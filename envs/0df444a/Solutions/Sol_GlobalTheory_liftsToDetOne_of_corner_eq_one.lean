-- Prove2me | solution 1 for GlobalTheory.liftsToDetOne_of_corner_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:17:16.38199+00:00
-- url     : https://prove2.me/submissions/6df06ca6-b84a-42f7-812e-a1b122168d33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_LiftsToDetOne_mul
import Theorems.Thm_GlobalTheory_LiftsToDetOne_upper
import Theorems.Thm_GlobalTheory_LiftsToDetOne_lower
import Theorems.Thm_GlobalTheory_LiftsToDetOne_block
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open Matrix Module Function
open private exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot from
  Mathlib.LinearAlgebra.SymplecticGroup
open GlobalTheory
variable {S R : Type*} [CommRing S] [CommRing R] {f : S →+* R}
  {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
namespace GlobalTheory
theorem _root_.solution (hf : Surjective f)
    (ih : ∀ D : Matrix m m R, D.det = 1 → LiftsToDetOne f D)
    {A : Matrix (Unit ⊕ m) (Unit ⊕ m) R} (hA : A.det = 1) (h1 : A (.inl ()) (.inl ()) = 1) :
    LiftsToDetOne f A := by
  have ha : A.toBlocks₁₁ = 1 := by
    ext ⟨⟩ ⟨⟩
    simpa [toBlocks₁₁] using h1
  have hdec : A = fromBlocks 1 0 A.toBlocks₂₁ 1 *
      fromBlocks 1 0 0 (A.toBlocks₂₂ - A.toBlocks₂₁ * A.toBlocks₁₂) *
        fromBlocks 1 A.toBlocks₁₂ 0 1 := by
    conv_lhs => rw [← A.fromBlocks_toBlocks, ha]
    simp [fromBlocks_multiply]
  have hD : (A.toBlocks₂₂ - A.toBlocks₂₁ * A.toBlocks₁₂).det = 1 := by
    rw [hdec] at hA
    simpa only [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, det_one, one_mul,
      mul_one] using hA
  rw [hdec]
  exact ((LiftsToDetOne.lower hf _).mul (ih _ hD).block).mul (LiftsToDetOne.upper hf _)
end GlobalTheory
