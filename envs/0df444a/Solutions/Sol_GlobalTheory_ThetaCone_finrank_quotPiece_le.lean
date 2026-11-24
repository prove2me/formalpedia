-- Prove2me | solution 1 for GlobalTheory.ThetaCone.finrank_quotPiece_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:30:01.187122+00:00
-- url     : https://prove2.me/submissions/06e6929a-5715-42e0-9cf8-eb530eabbb85

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ThetaConeIdealIsPrimeAndRingKrullDimLe
import Theorems.Thm_GlobalTheory_ThetaCone_eval_mul_of_isHomogeneous
import Theorems.Thm_GlobalTheory_quotPiece_natCast


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.ThetaCone
open MvPolynomial Filter Topology Module ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
attribute [local instance] MvPolynomial.gradedAlgebra
variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
omit [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.ThetaCone
theorem _root_.solution [Finite ι] {φ : ι → E → ℂ} {I : Ideal (MvPolynomial ι ℂ)}
    (hI : ∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : E), eval (fun c => t * φ c z) F = 0) {d B : ℕ}
    (hB : ∀ (r : ℕ) (F : Fin r → MvPolynomial ι ℂ), (∀ k, (F k).IsHomogeneous d) →
      LinearIndependent ℂ (fun k z => eval (fun c => φ c z) (F k)) → r ≤ B) :
    finrank ℂ (quotPiece I d) ≤ B := by
  classical
  by_cases hfin : FiniteDimensional ℂ (quotPiece I d)
  swap
  · rw [Module.finrank_of_not_finite hfin]
    exact Nat.zero_le _
  let b := Module.finBasis ℂ (quotPiece I d)

  have hlift : ∀ x ∈ quotPiece I d, ∃ p ∈ homogeneousSubmodule ι ℂ d,
      (Ideal.Quotient.mkₐ ℂ I).toLinearMap p = x := by
    intro x hx
    rw [quotPiece_natCast] at hx
    exact Submodule.mem_map.mp hx
  have hmem : ∀ k, ∃ p ∈ homogeneousSubmodule ι ℂ d,
      (Ideal.Quotient.mkₐ ℂ I).toLinearMap p = (b k : MvPolynomial ι ℂ ⧸ I) :=
    fun k => hlift _ (b k).2
  choose F hFd hFb using hmem
  refine hB _ F (fun k => (mem_homogeneousSubmodule d (F k)).mp (hFd k)) ?_
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have hhom : (∑ k, a k • F k).IsHomogeneous d := (mem_homogeneousSubmodule d _).mp
    (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hFd k))
  have hG : ∑ k, a k • F k ∈ I := by
    refine (hI _).mpr fun t z => ?_
    rw [eval_mul_of_isHomogeneous (fun c => φ c z) t hhom]
    have hz := congrFun ha z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hz
    rw [map_sum]
    simp only [smul_eval]
    rw [hz, mul_zero]
  have h0 : ∑ k, a k • b k = 0 := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero]
    simp_rw [← hFb, ← map_smul, ← map_sum]
    simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hG
  exact (Fintype.linearIndependent_iff.mp b.linearIndependent) a h0
end GlobalTheory.ThetaCone
