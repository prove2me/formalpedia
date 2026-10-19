-- Prove2me | solution 1 for HunterPDE.Compactness.compact_embedding_C0
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-18T17:05:12.102346+00:00
-- url     : https://prove2.me/submissions/99ea2fd5-9f46-4fb8-ab5b-94a19ea473ae

import Theorems.Thm_HunterPDE_Sobolev_weak_morrey_representative
import Theorems.Thm_ZeroAtInftyContinuousMap_isCompact_closure_of_common_support
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open MeasureTheory HunterPDE Set Filter
open scoped ENNReal NNReal ZeroAtInfty Topology

theorem solution {n : ℕ} (hn : 1 ≤ n) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (p : ℝ) (hnp : (n : ℝ) < p)
    (F : Set (EuclideanSpace ℝ (Fin n) → ℝ))
    (hFD : ∀ f ∈ F, ∀ i : Fin n, ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      Shared.HasWeakDeriv Set.univ (Pi.single i 1) f g ∧ MemLp g (ENNReal.ofReal p) volume)
    (hFsupp : ∀ f ∈ F, ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧ K ⊆ Ω ∧
      ∀ᵐ x ∂volume, x ∉ K → f x = 0)
    (hFb : ∃ C : ℝ≥0, ∀ f ∈ F,
      eLpNorm (Shared.weakGradNorm Set.univ f) (ENNReal.ofReal p) volume ≤ (C : ℝ≥0∞)) :
    (∀ f ∈ F, ∃ u : C₀(EuclideanSpace ℝ (Fin n), ℝ), (u : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] f) ∧
      IsCompact (closure {u : C₀(EuclideanSpace ℝ (Fin n), ℝ) |
        ∃ f ∈ F, (u : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume] f}) := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨R, hR, hΩR⟩ := hΩb.exists_pos_norm_le
  obtain ⟨z : E, hz⟩ := NormedSpace.exists_lt_norm ℝ E R
  let K : Set E := Metric.closedBall 0 R
  have hK : IsCompact K := isCompact_closedBall 0 R
  have hΩK : Ω ⊆ K := fun x hx => by simpa [K, dist_zero_right] using hΩR x hx
  have hzK : z ∉ K := by simpa [K, dist_zero_right] using hz.not_ge
  obtain ⟨A, hA⟩ := Sobolev.weak_morrey_representative hn p hnp
  obtain ⟨C, hC⟩ := hFb
  let B : ℝ := (A : ℝ) * (C : ℝ)
  let α : ℝ := 1 - (n : ℝ) / p
  have hp : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hnp
  have hα : 0 < α := sub_pos.mpr ((div_lt_one hp).mpr hnp)
  have hB : 0 ≤ B := mul_nonneg A.coe_nonneg C.coe_nonneg
  have hex : ∀ f ∈ F, ∃ u : C₀(E, ℝ), (u : E → ℝ) =ᵐ[volume] f ∧
      (∀ x ∉ K, u x = 0) ∧
      ∀ x y, dist (u x) (u y) ≤ B * dist x y ^ α := by
    intro f hf
    obtain ⟨u, hu, hueq, hinc⟩ := hA f (hFD f hf) C (hC f hf)
    obtain ⟨L, hL, hLΩ, hfL⟩ := hFsupp f hf
    have hu0 : ∀ x ∉ K, u x = 0 := by
      have hae : u =ᵐ[volume.restrict Kᶜ] (fun _ => (0 : ℝ)) := by
        apply (ae_restrict_iff' hK.isClosed.measurableSet.compl).mpr
        filter_upwards [hueq, hfL] with x hx hfx hxK
        exact hx.trans (hfx (fun hxL => hxK (hΩK (hLΩ hxL))))
      exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae hK.isClosed.isOpen_compl
        hu.continuousOn continuous_const.continuousOn
    let v : C₀(E, ℝ) :=
      { toFun := u
        continuous_toFun := hu
        zero_at_infty' := by
          apply Tendsto.congr' (f₁ := fun _ : E => (0 : ℝ)) _ tendsto_const_nhds
          filter_upwards [hK.compl_mem_cocompact] with x hx
          exact (hu0 x hx).symm }
    exact ⟨v, hueq, hu0, hinc⟩
  let S : Set C₀(E, ℝ) := {u | ∃ f ∈ F, (u : E → ℝ) =ᵐ[volume] f}
  have hprop : ∀ u ∈ S, (∀ x ∉ K, u x = 0) ∧
      ∀ x y, dist (u x) (u y) ≤ B * dist x y ^ α := by
    rintro u ⟨f, hf, hueq⟩
    obtain ⟨v, hveq, hv0, hvinc⟩ := hex f hf
    have huv : (u : E → ℝ) = v := MeasureTheory.Measure.eq_of_ae_eq (hueq.trans hveq.symm)
      u.continuous v.continuous
    simpa only [huv] using And.intro hv0 hvinc
  refine ⟨fun f hf => ?_, ?_⟩
  · obtain ⟨u, hu, _⟩ := hex f hf
    exact ⟨u, hu⟩
  · apply ZeroAtInftyContinuousMap.isCompact_closure_of_common_support S K hK
      (fun u hu => (hprop u hu).1) (B * (R + ‖z‖) ^ α)
    · intro u hu x
      by_cases hx : x ∈ K
      · have hdist : dist x z ≤ R + ‖z‖ := by
          calc
            dist x z ≤ ‖x‖ + ‖z‖ := dist_le_norm_add_norm x z
            _ ≤ R + ‖z‖ := by
              have hxn : ‖x‖ ≤ R := by simpa [K, dist_zero_right] using hx
              linarith
        calc
          |u x| = dist (u x) (u z) := by rw [(hprop u hu).1 z hzK, Real.dist_eq, sub_zero]
          _ ≤ B * dist x z ^ α := (hprop u hu).2 x z
          _ ≤ B * (R + ‖z‖) ^ α := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow dist_nonneg hdist hα.le) hB
      · rw [(hprop u hu).1 x hx, abs_zero]
        positivity
    · intro x
      rw [Metric.equicontinuousAt_iff_right]
      intro ε hε
      have ht : Tendsto (fun y : E => B * dist x y ^ α) (𝓝 x) (𝓝 0) := by
        have hc : Continuous (fun y : E => B * dist x y ^ α) :=
          continuous_const.mul ((Real.continuous_rpow_const hα.le).comp
            (continuous_const.dist continuous_id))
        simpa [Real.zero_rpow (ne_of_gt hα)] using hc.tendsto x
      filter_upwards [ht.eventually (gt_mem_nhds hε)] with y hy
      intro u
      exact lt_of_le_of_lt ((hprop u.1 u.2).2 x y) hy
