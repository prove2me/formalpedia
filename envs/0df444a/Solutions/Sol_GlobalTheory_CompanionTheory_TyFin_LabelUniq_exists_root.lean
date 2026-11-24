-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.LabelUniq.exists_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:44:16.318855+00:00
-- url     : https://prove2.me/submissions/95f39208-55e5-471f-bc84-79b4a162610c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OrthogonalIntVectorsNotAgreeOnRegular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RegularIffNatDegreeAndExistsEllipticGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InnerProductRootPowerSumEqOfFrobeniusModEq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalLabelUnique
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_LabelUniq_pow_card_pow_self
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_LabelUniq_regular_iff_degree
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_LabelUniq_gen_primitive
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_LabelUniq_card_pow_sub_one_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.LabelUniq
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
namespace GlobalTheory.CompanionTheory.TyFin.LabelUniq
theorem _root_.solution (C : LabelConv K) {d : ℕ} (hd : 0 < d) {P : K[X]} (hm : P.Monic)
    (hi : Irreducible P) (hX : P ≠ X) (hdeg : P.natDegree = d) :
    ∃ (x : AlgebraicClosure K) (s : ℕ), aeval x P = 0 ∧ minpoly K x = P ∧ C.gen d ^ s = x ∧
      ∀ e, 0 < e → e < d → ¬ s * Fintype.card K ^ e ≡ s [MOD Fintype.card K ^ d - 1] := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) P (Polynomial.degree_pos_of_irreducible hi).ne'
  have hmin : minpoly K x = P := (minpoly.eq_of_irreducible_of_monic hi hx hm).symm
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hX (by rw [← hmin, minpoly.zero])
  have hdeg' : (minpoly K x).natDegree = d := by rw [hmin, hdeg]
  have hxq : x ^ Fintype.card K ^ d = x := pow_card_pow_self x hdeg'
  have hpos := card_pow_sub_one_pos (K := K) hd
  have hx1 : x ^ (Fintype.card K ^ d - 1) = 1 := by
    have h1 : x ^ (Fintype.card K ^ d - 1) * x = 1 * x := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), hxq, one_mul]
    exact mul_right_cancel₀ hx0 h1
  haveI : NeZero (Fintype.card K ^ d - 1) := ⟨hpos.ne'⟩
  have hord : orderOf (C.gen d) = Fintype.card K ^ d - 1 := C.gen_order d hd
  have hfin : IsOfFinOrder (C.gen d) := orderOf_pos_iff.mp (by rw [hord]; exact hpos)
  have hmodq : ∀ a b : ℕ, C.gen d ^ a = C.gen d ^ b ↔ a ≡ b [MOD Fintype.card K ^ d - 1] := by
    intro a b
    rw [← hord]
    exact hfin.pow_eq_pow_iff_modEq
  obtain ⟨s, -, hs⟩ := (gen_primitive C hd).eq_pow_of_pow_eq_one hx1
  refine ⟨x, s, hx, hmin, hs, ?_⟩
  intro e he hed hmod
  apply ((regular_iff_degree hd x hx1).1.mpr hdeg') e he hed
  rw [← hs, ← pow_mul]
  exact (hmodq _ _).mpr hmod
end GlobalTheory.CompanionTheory.TyFin.LabelUniq
