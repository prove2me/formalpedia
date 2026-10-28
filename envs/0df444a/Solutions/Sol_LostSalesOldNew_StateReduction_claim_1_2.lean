-- Prove2me | solution 2 for LostSalesOldNew.StateReduction.claim_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T08:26:45.489241+00:00
-- url     : https://prove2.me/submissions/d6ad29e0-f87c-42aa-b42f-fd8bedb1f44b

import Mathlib
import Definitions.Def_LostSalesOldNew_StateReduction_Model
import Theorems.Thm_LostSalesOldNew_StateReduction_Xs_invariant
import Theorems.Thm_LostSalesOldNew_StateReduction_reaches_Xs

-- carved verbatim out of submission 40974d7e-4016-41d1-bcdc-5217230ac4dd, lines 200-295

section
set_option autoImplicit false
open LostSalesOldNew.StateReduction MeasureTheory ProbabilityTheory Filter

theorem solution {L : ℕ} (hL : 0 < L) (s : Fin (L + 1) → ℝ) (hs : IsLevelVector s)
    (z : (Fin L → ℝ) → ℝ) (hz : z ∈ Zs s)
    (D : Measure ℝ) (hD : IsDemand D) (hDpos : 0 < D (Set.Ioi 0))
    (x : Fin L → ℝ) (hx : ∀ i, 0 ≤ x i) :
    haveI := hD.isProb
    ∀ᵐ ds ∂(Measure.infinitePi (fun _ : ℕ => D)),
      ∃ T : ℕ, ∀ t, T ≤ t → traj z x ds t ∈ Xs s := by
  haveI := hD.isProb
  set μ : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => D) with hμ
  -- nonnegativity of the demands
  have hnn : ∀ᵐ ds ∂μ, ∀ t, 0 ≤ ds t := by
    rw [ae_all_iff]
    intro t
    rw [ae_iff]
    have h1 : {ds : ℕ → ℝ | ¬ 0 ≤ ds t} = (fun ds : ℕ → ℝ => ds t) ⁻¹' (Set.Iio 0) := by
      ext ds; simp
    rw [h1]
    have := (measurePreserving_eval_infinitePi (fun _ : ℕ => D) t).measure_preimage
      (measurableSet_Iio (a := (0 : ℝ))).nullMeasurableSet
    rw [show (Set.Iio (0:ℝ)) = Set.Iio 0 from rfl] at this
    simpa [hμ, hD.nonneg] using this
  -- divergence of the cumulative demand
  have hdiv : ∀ᵐ ds ∂μ, Tendsto (fun n => ∑ t ∈ Finset.range n, ds t) atTop atTop := by
    set g : ℝ → ℝ := fun y => min (max y 0) 1 with hg
    have hgm : Measurable g := (measurable_id.max measurable_const).min measurable_const
    have hg0 : ∀ y, 0 ≤ g y := fun y => le_min (le_max_right _ _) zero_le_one
    have hg1 : ∀ y, g y ≤ 1 := fun y => min_le_right _ _
    have hgle : ∀ y, 0 ≤ y → g y ≤ y := by
      intro y hy
      simp only [hg, max_eq_left hy]
      exact min_le_left _ _
    have hind : iIndepFun (fun (i : ℕ) (ω : ℕ → ℝ) => g (ω i)) μ :=
      iIndepFun_infinitePi (P := fun _ : ℕ => D) (X := fun _ => g) (fun _ => hgm)
    have hmeas : ∀ i : ℕ, Measurable (fun ω : ℕ → ℝ => g (ω i)) :=
      fun i => hgm.comp (measurable_pi_apply i)
    have hint : Integrable (fun ω : ℕ → ℝ => g (ω 0)) μ := by
      refine Integrable.of_bound (hmeas 0).aestronglyMeasurable 1 ?_
      refine Filter.Eventually.of_forall (fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 _)]
      exact hg1 _
    have hindep : Pairwise (Function.onFun (fun f h => f ⟂ᵢ[μ] h) (fun (n : ℕ) (ω : ℕ → ℝ) => g (ω n))) :=
      fun i j hij => hind.indepFun hij
    have hmap : ∀ i : ℕ, μ.map (fun ω : ℕ → ℝ => g (ω i)) = D.map g := by
      intro i
      have : (fun ω : ℕ → ℝ => g (ω i)) = g ∘ (fun ω : ℕ → ℝ => ω i) := rfl
      rw [this, ← Measure.map_map hgm (measurable_pi_apply i), hμ, Measure.infinitePi_map_eval]
    have hident : ∀ i, IdentDistrib (fun ω : ℕ → ℝ => g (ω i)) (fun ω : ℕ → ℝ => g (ω 0)) μ μ :=
      fun i => ⟨(hmeas i).aemeasurable, (hmeas 0).aemeasurable, by rw [hmap i, hmap 0]⟩
    have hlaw := strong_law_ae (μ := μ) (fun (n : ℕ) (ω : ℕ → ℝ) => g (ω n)) hint hindep hident
    have hE : 0 < ∫ ω, g (ω 0) ∂μ := by
      have h1 : ∫ ω, g (ω 0) ∂μ = ∫ y, g y ∂D := by
        rw [← integral_map (φ := fun ω : ℕ → ℝ => ω 0) (measurable_pi_apply 0).aemeasurable
          hgm.aestronglyMeasurable, hμ, Measure.infinitePi_map_eval]
      rw [h1]
      have hgi : Integrable g D :=
        Integrable.of_bound hgm.aestronglyMeasurable 1
          (Filter.Eventually.of_forall (fun y => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hg0 _)]; exact hg1 _))
      rw [integral_pos_iff_support_of_nonneg hg0 hgi]
      have hsupp : Function.support g = Set.Ioi 0 := by
        ext y
        simp only [Function.mem_support, Set.mem_Ioi]
        by_cases hy : 0 < y
        · have : 0 < g y := lt_min (lt_of_lt_of_le hy (le_max_left _ _)) one_pos
          simp [this.ne', hy]
        · have : g y = 0 := by
            simp only [hg, max_eq_right (not_lt.1 hy)]
            simp
          simp [this, hy]
      rw [hsupp]
      exact hDpos
    set m := ∫ ω, g (ω 0) ∂μ with hm
    filter_upwards [hlaw, hnn] with ds hds' hds0
    have hev := (tendsto_order.1 hds').1 (m / 2) (by linarith)
    have hlin : Tendsto (fun n : ℕ => (n : ℝ) * (m / 2)) atTop atTop :=
      Tendsto.atTop_mul_const (by positivity) tendsto_natCast_atTop_atTop
    refine tendsto_atTop_mono' atTop ?_ hlin
    filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
    have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
    have h1 : m / 2 < (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, g (ds i) := by
      simpa [smul_eq_mul] using hn
    have h2 : (n : ℝ) * (m / 2) ≤ ∑ i ∈ Finset.range n, g (ds i) := by
      have := mul_lt_mul_of_pos_left h1 hn0'
      rw [← mul_assoc, mul_inv_cancel₀ hn0'.ne', one_mul] at this
      exact this.le
    refine h2.trans ?_
    exact Finset.sum_le_sum (fun i _ => hgle _ (hds0 i))
  filter_upwards [hnn, hdiv] with ds hds hdv
  obtain ⟨t0, ht0⟩ := LostSalesOldNew.StateReduction.reaches_Xs hL s hs z hz x hx ds hds hdv
  refine ⟨t0, ?_⟩
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact ht0
  | succ t _ ih =>
    exact LostSalesOldNew.StateReduction.Xs_invariant hL s hs z hz _ ih (ds t) (hds t)

end
