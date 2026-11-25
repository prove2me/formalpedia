-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.llRank_permGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:32:34.274479+00:00
-- url     : https://prove2.me/submissions/086ddfbb-9aac-446d-b96e-c2e0921bf524

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_mul_permGL_apply
import Theorems.Thm_GroundTheory_Automorphic_permGL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (w : Equiv.Perm (Fin n)) (i j : Fin n) :
    llRank i j (permGL F w) = (Finset.univ.filter fun r : Fin n => i ≤ r ∧ w⁻¹ r ≤ j).card := by
  classical
  have hW : IsUnit ((permGL F w⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  unfold llRank
  rw [← rank_mul_eq_left_of_isUnit_det _ _ hW]
  have e : rowsFrom i * (permGL F w : Matrix (Fin n) (Fin n) F) * colsTo j *
      (permGL F w⁻¹ : Matrix (Fin n) (Fin n) F) =
      diagonal fun r => if i ≤ r ∧ w⁻¹ r ≤ j then (1 : F) else 0 := by
    ext r c
    rw [mul_permGL_apply]
    simp only [rowsFrom, colsTo]
    rw [mul_diagonal, diagonal_mul, permGL_apply, diagonal_apply]
    have hwc : w (w⁻¹ c) = c := by rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
    rw [hwc]
    by_cases hrc : r = c
    · subst hrc
      by_cases h1 : i ≤ r <;> simp [h1]
    · simp [hrc]
  rw [e, rank_diagonal, Fintype.card_subtype]
  congr 1
  ext r
  simp
end GroundTheory.Automorphic.Whittaker
