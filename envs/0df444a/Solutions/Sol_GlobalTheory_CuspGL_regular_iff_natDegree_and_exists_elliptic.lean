-- Prove2me | solution 1 for GlobalTheory.CuspGL.regular_iff_natDegree_and_exists_elliptic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:25:08.173557+00:00
-- url     : https://prove2.me/submissions/2e76bce3-9ed1-4683-8a24-64ec777dbb99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RegularIffNatDegreeAndExistsEllipticGL
import Theorems.Thm_GlobalTheory_CuspGL_pow_card_pow_eq_iff_natDegree_minpoly_dvd
import Theorems.Thm_GlobalTheory_CuspGL_exists_GL_charpoly_eq_minpoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution :
    ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 0 < n → ∀ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, ((∀ e : ℕ, 0 < e → e < n → α ^ Nat.card F ^ e ≠ α) ↔ (minpoly F α).natDegree = n) ∧ ((minpoly F α).natDegree = n → ∃ x : GL (Fin n) F, Matrix.charpoly (x : Matrix (Fin n) (Fin n) F) = minpoly F α) := by
  intro F _ _ n hn α hα
  have hα' : α ^ (Nat.card F ^ n - 1) = 1 := hα
  have hx : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have hq : 1 < Nat.card F ^ n := Nat.one_lt_pow hn.ne' Finite.one_lt_card
  have h0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.sub_ne_zero_of_lt hq)] at hα'
    exact zero_ne_one hα'
  have hfix : α ^ Nat.card F ^ n = α := by
    have hsplit : Nat.card F ^ n = (Nat.card F ^ n - 1) + 1 := (Nat.sub_add_cancel hq.le).symm
    rw [hsplit, pow_succ, hα', one_mul]
  have hdvd := (pow_card_pow_eq_iff_natDegree_minpoly_dvd F α n).1 hfix
  have hdpos : 0 < (minpoly F α).natDegree := minpoly.natDegree_pos hx
  refine ⟨⟨fun h => ?_, fun h e he1 he2 heq => ?_⟩,
    fun h => exists_GL_charpoly_eq_minpoly F (AlgebraicClosure F) α hx h0 n h⟩
  · by_contra hne
    have hlt : (minpoly F α).natDegree < n := lt_of_le_of_ne (Nat.le_of_dvd hn hdvd) hne
    exact h _ hdpos hlt ((pow_card_pow_eq_iff_natDegree_minpoly_dvd F α _).2 dvd_rfl)
  · have hd := (pow_card_pow_eq_iff_natDegree_minpoly_dvd F α e).1 heq
    rw [h] at hd
    exact absurd (Nat.le_of_dvd he1 hd) (not_le.2 he2)
end GlobalTheory.CuspGL
