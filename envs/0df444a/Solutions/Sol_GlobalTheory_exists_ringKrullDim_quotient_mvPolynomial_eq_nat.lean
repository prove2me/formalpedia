-- Prove2me | solution 1 for GlobalTheory.exists_ringKrullDim_quotient_mvPolynomial_eq_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:20.26918+00:00
-- url     : https://prove2.me/submissions/8e566ab4-57b5-4a78-ac01-bb86d143f9f3

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {σ : Type*} [Finite σ] {k : Type*} [Field k]
namespace GlobalTheory
theorem _root_.solution {I : Ideal (MvPolynomial σ k)}
    (hI : I ≠ ⊤) : ∃ δ : ℕ, ringKrullDim (MvPolynomial σ k ⧸ I) = δ := by
  haveI := Ideal.Quotient.nontrivial_iff.mpr hI
  have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial σ k ⧸ I)
  have h1 := ringKrullDim_quotient_le I
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
    zero_add] at h1
  generalize ringKrullDim (MvPolynomial σ k ⧸ I) = x at h0 h1
  induction x with
  | bot => simp at h0
  | coe x =>
    induction x with
    | top => exact absurd h1 (not_le.mpr (by exact_mod_cast ENat.coe_lt_top _))
    | coe n => exact ⟨n, rfl⟩
end GlobalTheory
