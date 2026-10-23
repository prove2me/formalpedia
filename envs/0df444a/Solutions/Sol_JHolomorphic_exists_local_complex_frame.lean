-- Prove2me | solution 1 for JHolomorphic.exists_local_complex_frame
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T11:34:35.249177+00:00
-- url     : https://prove2.me/submissions/ebc237fb-82a4-47f6-925f-ae4b03f22d30

import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Theorems.Thm_JHolomorphic_exists_bijective_clm_I_smul_eq
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Calculus.FDeriv.CompCLM



namespace JHolomorphic

open Metric Filter Topology Set
open scoped ContDiff

/-- A smooth family of complex structures on a `2n`-dimensional space admits, near `0`, a smooth
family of real-linear isomorphisms `ℂⁿ → E` carrying `i` to `J̄(z)`, with smooth inverses. -/
theorem exists_local_frame_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (n : ℕ) (hn : Module.finrank ℝ E = 2 * n) (Jbar : ℂ → E →L[ℝ] E)
    (hJbar : ContDiffOn ℝ ∞ Jbar (ball 0 1))
    (hJbar2 : ∀ z ∈ ball (0 : ℂ) 1, (Jbar z).comp (Jbar z) = -ContinuousLinearMap.id ℝ E) :
    ∃ ρ > (0 : ℝ), ρ ≤ 1 ∧ ∃ Ψ : ℂ → EuclideanSpace ℂ (Fin n) →L[ℝ] E,
      ∃ Ψi : ℂ → E →L[ℝ] EuclideanSpace ℂ (Fin n),
        ContDiffOn ℝ ∞ Ψ (ball 0 ρ) ∧ ContDiffOn ℝ ∞ Ψi (ball 0 ρ) ∧
        ∀ z ∈ ball (0 : ℂ) ρ, (∀ v, Ψi z (Ψ z v) = v) ∧ (∀ x, Ψ z (Ψi z x) = x) ∧
          ∀ w, Ψ z (Complex.I • w) = Jbar z (Ψ z w) := by
  have h01 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  obtain ⟨T, hTb, hTI⟩ := exists_bijective_clm_I_smul_eq n hn (Jbar 0) (hJbar2 0 h01)
  let Te : EuclideanSpace ℂ (Fin n) ≃L[ℝ] E :=
    (LinearEquiv.ofBijective (T : EuclideanSpace ℂ (Fin n) →ₗ[ℝ] E) hTb).toContinuousLinearEquiv
  have hTe : ∀ v, Te v = T v := fun _ => rfl
  let P : ℂ → E →L[ℝ] E := fun z => (2⁻¹ : ℝ) • (1 - Jbar z * Jbar 0)
  have hPd : ContDiffOn ℝ ∞ P (ball 0 1) :=
    (contDiffOn_const.sub (hJbar.mul contDiffOn_const)).const_smul _
  have hJ0 : Jbar 0 * Jbar 0 = -1 := hJbar2 0 h01
  have hP0 : P 0 = 1 := by
    simp only [P, hJ0, sub_neg_eq_add]
    rw [← two_smul ℝ (1 : E →L[ℝ] E), smul_smul]; norm_num
  have hU : IsOpen {x : E →L[ℝ] E | IsUnit x} := Units.isOpen
  have hnhds : P ⁻¹' {x | IsUnit x} ∩ ball 0 1 ∈ 𝓝 (0 : ℂ) := by
    refine inter_mem ?_ (ball_mem_nhds _ one_pos)
    have hc : ContinuousAt P 0 := hPd.continuousOn.continuousAt (ball_mem_nhds _ one_pos)
    exact hc.preimage_mem_nhds (hU.mem_nhds (by rw [hP0]; exact isUnit_one))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 hnhds
  have hδ1 : ball (0 : ℂ) (min δ 1) ⊆ P ⁻¹' {x | IsUnit x} ∩ ball 0 1 :=
    (ball_subset_ball (min_le_left _ _)).trans hδsub
  refine ⟨min δ 1, lt_min hδ one_pos, min_le_right _ _, fun z => (P z).comp T,
    fun z => (Te.symm : E →L[ℝ] EuclideanSpace ℂ (Fin n)).comp (Ring.inverse (P z)),
    ?_, ?_, ?_⟩
  · exact (hPd.mono fun z hz => (hδ1 hz).2).clm_comp contDiffOn_const
  · refine contDiffOn_const.clm_comp ?_
    intro z hz
    obtain ⟨u, hu⟩ := (hδ1 hz).1
    have h1 : ContDiffAt ℝ ∞ Ring.inverse (P z) := by
      rw [← hu]; exact contDiffAt_ringInverse ℝ u
    exact (h1.comp z ((hPd.contDiffAt (isOpen_ball.mem_nhds (hδ1 hz).2)))).contDiffWithinAt
  · intro z hz
    have hu : IsUnit (P z) := (hδ1 hz).1
    have hz1 : z ∈ ball (0 : ℂ) 1 := (hδ1 hz).2
    refine ⟨fun v => ?_, fun x => ?_, fun w => ?_⟩
    · simp only [ContinuousLinearMap.comp_apply]
      have : Ring.inverse (P z) (P z (T v)) = T v := by
        rw [← ContinuousLinearMap.mul_apply, Ring.inverse_mul_cancel _ hu]; rfl
      rw [this, ← hTe, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
    · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
      rw [← hTe, ContinuousLinearEquiv.apply_symm_apply, ← ContinuousLinearMap.mul_apply,
        Ring.mul_inverse_cancel _ hu]; rfl
    · have hJz : Jbar z * Jbar z = -1 := hJbar2 z hz1
      simp only [ContinuousLinearMap.comp_apply, hTI, P, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.mul_apply,
        map_smul, map_sub]
      have e1 : Jbar 0 (Jbar 0 (T w)) = -T w := by
        rw [← ContinuousLinearMap.mul_apply, hJ0]; rfl
      have e2 : Jbar z (Jbar z (Jbar 0 (T w))) = -Jbar 0 (T w) := by
        rw [← ContinuousLinearMap.mul_apply, hJz]; rfl
      rw [e1, e2, map_neg]
      congr 1
      abel

end JHolomorphic

open JHolomorphic

open Metric Filter Topology Set
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (n : ℕ) (hn : Module.finrank ℝ E = 2 * n) (Jbar : ℂ → E →L[ℝ] E)
    (hJbar : ContDiffOn ℝ ∞ Jbar (ball 0 1))
    (hJbar2 : ∀ z ∈ ball (0 : ℂ) 1, (Jbar z).comp (Jbar z) = -ContinuousLinearMap.id ℝ E) :
    ∃ ρ > (0 : ℝ), ρ ≤ 1 ∧ ∃ Ψ : ℂ → EuclideanSpace ℂ (Fin n) →L[ℝ] E,
      ∃ Ψi : ℂ → E →L[ℝ] EuclideanSpace ℂ (Fin n),
        ContDiffOn ℝ ∞ Ψ (ball 0 ρ) ∧ ContDiffOn ℝ ∞ Ψi (ball 0 ρ) ∧
        ∀ z ∈ ball (0 : ℂ) ρ, (∀ v, Ψi z (Ψ z v) = v) ∧ (∀ x, Ψ z (Ψi z x) = x) ∧
          ∀ w, Ψ z (Complex.I • w) = Jbar z (Ψ z w) :=
  exists_local_frame_aux n hn Jbar hJbar hJbar2
