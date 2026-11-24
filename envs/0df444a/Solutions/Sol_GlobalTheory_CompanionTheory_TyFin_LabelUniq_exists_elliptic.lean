-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.LabelUniq.exists_elliptic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:44:15.463528+00:00
-- url     : https://prove2.me/submissions/057ebc4b-4709-4721-9935-d30333cd7dd5

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OrthogonalIntVectorsNotAgreeOnRegular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RegularIffNatDegreeAndExistsEllipticGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InnerProductRootPowerSumEqOfFrobeniusModEq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalLabelUnique
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
theorem _root_.solution (C : LabelConv K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (hd : 0 < Fintype.card ι) (j : ℕ)
    (hj : ∀ e, 0 < e → e < Fintype.card ι →
      ¬ j * Fintype.card K ^ e ≡ j [MOD Fintype.card K ^ Fintype.card ι - 1]) :
    ∃ γ : GL ι K, Irreducible (Matrix.charpoly (γ : Matrix ι ι K)) ∧
      aeval (C.gen (Fintype.card ι) ^ j) (Matrix.charpoly (γ : Matrix ι ι K)) = 0 := by
  have hprim := gen_primitive C hd
  have hα1 : (C.gen (Fintype.card ι) ^ j) ^ (Fintype.card K ^ Fintype.card ι - 1) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
  have hpos := card_pow_sub_one_pos (K := K) hd
  have hord : orderOf (C.gen (Fintype.card ι)) = Fintype.card K ^ Fintype.card ι - 1 := C.gen_order _ hd
  have hfin : IsOfFinOrder (C.gen (Fintype.card ι)) := orderOf_pos_iff.mp (by rw [hord]; exact hpos)
  have hreg : ∀ e : ℕ, 0 < e → e < Fintype.card ι →
      (C.gen (Fintype.card ι) ^ j) ^ Fintype.card K ^ e ≠ C.gen (Fintype.card ι) ^ j := by
    intro e he hed heq
    apply hj e he hed
    rw [← pow_mul] at heq
    rw [← hord]
    exact hfin.pow_eq_pow_iff_modEq.mp heq
  obtain ⟨hiff, hex⟩ := regular_iff_degree hd (C.gen (Fintype.card ι) ^ j) hα1
  obtain ⟨x, hx⟩ := hex (hiff.mp hreg)
  have hMchar : (Matrix.reindex (Fintype.equivFin ι).symm (Fintype.equivFin ι).symm
      (x : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) K)).charpoly =
      minpoly K (C.gen (Fintype.card ι) ^ j) := by
    rw [Matrix.charpoly_reindex, hx]
  have hMu : IsUnit (Matrix.reindex (Fintype.equivFin ι).symm (Fintype.equivFin ι).symm
      (x : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) K)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, ← Matrix.isUnit_iff_isUnit_det]
    exact x.isUnit
  refine ⟨hMu.unit, ?_, ?_⟩
  · rw [IsUnit.unit_spec, hMchar]
    exact minpoly.irreducible (Algebra.IsIntegral.isIntegral _)
  · rw [IsUnit.unit_spec, hMchar]
    exact minpoly.aeval K _
end GlobalTheory.CompanionTheory.TyFin.LabelUniq
