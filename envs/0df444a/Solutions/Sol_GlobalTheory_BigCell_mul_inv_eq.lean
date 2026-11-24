-- Prove2me | solution 1 for GlobalTheory.BigCell.mul_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:01:31.265882+00:00
-- url     : https://prove2.me/submissions/01796f77-fb23-4718-bd2a-f08241e360d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BigCellFactorisationDoubledUnitaryGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM
open scoped Matrix
open Matrix
open GlobalTheory GlobalTheory.BigCell
variable {R : Type} [CommRing R] {β : Type} [Fintype β] [DecidableEq β]
variable [Invertible (2 : R)]
variable (f : R →+* R) (J : Matrix β β R) (K G : Matrix (β ⊕ β) (β ⊕ β) R) (Δ N : Matrix (β ⊕ β) β R)
  (Δt Nt : Matrix β (β ⊕ β) R) (D' : Matrix β β R)
namespace GlobalTheory.BigCell
theorem _root_.solution (hNtΔ : Nt * Δ = 0) (x : Matrix β β R) :
    (1 + ⅟(2 : R) • (Δ * x * Nt)) * (1 - ⅟(2 : R) • (Δ * x * Nt)) = 1 ∧
    (1 - ⅟(2 : R) • (Δ * x * Nt)) * (1 + ⅟(2 : R) • (Δ * x * Nt)) = 1 := by
  have hM : (Δ * x * Nt) * (Δ * x * Nt) = 0 := by
    simp only [Matrix.mul_assoc]
    rw [show Nt * (Δ * (x * Nt)) = 0 by rw [← Matrix.mul_assoc, hNtΔ, Matrix.zero_mul]]
    simp
  constructor
  · simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hM, smul_zero]
    abel
  · simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hM, smul_zero]
    abel
end GlobalTheory.BigCell
