-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EichlerTransf.isUnit_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:01:34.930228+00:00
-- url     : https://prove2.me/submissions/99c546a0-af54-4af0-9a45-f90f7ac8b56f

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExtendByZeroApplyOfNe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EichlerTransf
open scoped ComplexOrder
variable {n m : ℕ}
namespace GlobalTheory.CompanionTheory.EichlerTransf
theorem _root_.solution (a : Matrix (Fin n) (Fin m) ℂ) (b : Matrix (Fin m) (Fin n) ℂ)
    (P : Matrix (Fin m) (Fin m) ℂ) (hPh : Pᴴ = P) (hPP : P * P = P) (hb : b * a = P) :
    IsUnit (aᴴ * a + (1 - P)) := by
  have hQ : (1 - P)ᴴ * (1 - P) = 1 - P := by
    rw [conjTranspose_sub, conjTranspose_one, hPh]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP]
    abel
  have hB : aᴴ * a + (1 - P) = (fromRows a (1 - P))ᴴ * fromRows a (1 - P) := by
    rw [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows, hQ]
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h0
  obtain ⟨v, hv, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  rw [hB, Matrix.conjTranspose_mul_self_mulVec_eq_zero, fromRows_mulVec] at hz
  have h1 : a *ᵥ v = 0 := by
    ext k; simpa using congrFun hz (Sum.inl k)
  have h2 : (1 - P) *ᵥ v = 0 := by
    ext k; simpa using congrFun hz (Sum.inr k)
  have h3 : P *ᵥ v = 0 := by
    rw [← hb, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]
  apply hv
  rw [Matrix.sub_mulVec, h3, Matrix.one_mulVec, sub_zero] at h2
  exact h2
end GlobalTheory.CompanionTheory.EichlerTransf
