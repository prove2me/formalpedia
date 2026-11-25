-- Prove2me | solution 1 for GlobalTheory.AffinePoints.exists_isOpen_fderiv_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:59:50.616994+00:00
-- url     : https://prove2.me/submissions/518d42c6-8cf4-4d7b-89e0-2f4ee2e155d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasAlgebraicChartsOfIsStandardSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Theorems.Thm_P2M_GlobalTheory_AffinePoints_fderiv_apply_eval__3bb27b96ffd8

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set MvPolynomial MeasureTheory Module
open scoped Manifold ContDiff
variable {A : Type} [CommRing A] [Algebra ℂ A] {d : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} {φ : E → (A →ₐ[ℂ] ℂ)}
namespace GlobalTheory.AffinePoints
theorem _root_.solution {R : Type*} [CommRing R] (g : R →+* A) {a : A}
    (ha : g.IsIntegralElem a) (hU : IsOpen U) (hne : U.Nonempty)
    (hφ : ∀ a, DifferentiableOn ℂ (fun z => φ z a) U) :
    ∃ V ⊆ U, IsOpen V ∧ V.Nonempty ∧ ∀ z ∈ V, ∀ v,
      (∀ r, fderiv ℂ (fun z => φ z (g r)) z v = 0) → fderiv ℂ (fun z => φ z a) z v = 0 := by
  obtain ⟨h, hm, hh⟩ := ha
  let c : ℕ → A := fun k => (Polynomial.derivative^[k] h).eval₂ g a
  obtain ⟨k, hk, z₀, hz₀, hk'⟩ : ∃ k, (∀ z ∈ U, φ z (c k) = 0) ∧ ∃ z ∈ U, φ z (c (k + 1)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ k, ∀ z ∈ U, φ z (c k) = 0 := by
      intro k
      induction k with
      | zero => intro z _; simp [c, hh]
      | succ k ih => exact hcon k ih
    obtain ⟨z, hz⟩ := hne
    have h1 := hall h.natDegree z hz
    have h2 : Polynomial.derivative^[h.natDegree] h = Polynomial.C (h.natDegree.factorial : R) := by
      rw [Polynomial.eq_C_of_natDegree_le_zero (p := Polynomial.derivative^[h.natDegree] h)
        ((Polynomial.natDegree_iterate_derivative h _).trans (by simp)),
        Polynomial.coeff_iterate_derivative, zero_add, Nat.descFactorial_self,
        hm.coeff_natDegree, nsmul_eq_mul, mul_one]
    simp [c, h2, Nat.factorial_ne_zero] at h1
  refine ⟨U ∩ (fun z => φ z (c (k + 1))) ⁻¹' {0}ᶜ, inter_subset_left,
    (hφ _).continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton, ⟨z₀, hz₀, hk'⟩,
    fun z hz v hv => ?_⟩
  have h1 := fderiv_apply_eval₂ g (fun a => (hφ a).differentiableAt (hU.mem_nhds hz.1)) v hv a
    (Polynomial.derivative^[k] h)
  have h2 : (fun z => φ z (c k)) =ᶠ[𝓝 z] fun _ => 0 := by
    filter_upwards [hU.mem_nhds hz.1] with w hw using hk w hw
  rw [← Function.iterate_succ_apply' Polynomial.derivative] at h1
  rw [show (fun z => φ z ((Polynomial.derivative^[k] h).eval₂ g a)) = fun z => φ z (c k) from rfl,
    h2.fderiv_eq] at h1
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.zero_apply] at h1
  exact (mul_eq_zero.1 h1.symm).resolve_left hz.2
end GlobalTheory.AffinePoints
