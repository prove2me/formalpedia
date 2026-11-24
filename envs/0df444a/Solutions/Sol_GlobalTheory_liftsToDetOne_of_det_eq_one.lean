-- Prove2me | solution 1 for GlobalTheory.liftsToDetOne_of_det_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:31:28.253521+00:00
-- url     : https://prove2.me/submissions/cb858fc8-3c58-4d55-b1b0-6529bf7a50ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_LiftsToDetOne_one
import Theorems.Thm_GlobalTheory_LiftsToDetOne_det_eq
import Theorems.Thm_GlobalTheory_LiftsToDetOne_of_mul_left
import Theorems.Thm_GlobalTheory_LiftsToDetOne_of_reindex
import Theorems.Thm_GlobalTheory_LiftsToDetOne_upper
import Theorems.Thm_GlobalTheory_exists_isUnit_corner
import Theorems.Thm_GlobalTheory_liftsToDetOne_of_isUnit_corner
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_reindex
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
theorem _root_.solution [Finite (MaximalSpectrum R)] (hf : Surjective f)
    {A : Matrix n n R} (hA : A.det = 1) : LiftsToDetOne f A := by
  have key : ∀ (k : ℕ) (A : Matrix (Fin k) (Fin k) R), A.det = 1 → LiftsToDetOne f A := by
    intro k
    induction k with
    | zero => intro A _; rw [Subsingleton.elim A 1]; exact .one
    | succ k ih =>
      intro A hA
      let e : Fin (k + 1) ≃ Unit ⊕ Fin k := Fintype.equivOfCardEq (by simp [add_comm])
      refine .of_reindex e ?_
      have hA' : (reindex e e A).det = 1 := by simpa using hA
      obtain ⟨t, ht⟩ := exists_isUnit_corner (A := reindex e e A) (by simp [hA])
      refine (LiftsToDetOne.upper hf t).of_mul_left (liftsToDetOne_of_isUnit_corner hf ih ?_ ht)
      rw [det_mul, hA', (LiftsToDetOne.upper hf t).det_eq, one_mul]
  exact .of_reindex (Fintype.equivFin n) (key _ _ (by simpa using hA))
end GlobalTheory
