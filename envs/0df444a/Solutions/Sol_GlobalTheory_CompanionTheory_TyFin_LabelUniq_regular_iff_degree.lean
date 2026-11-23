-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.LabelUniq.regular_iff_degree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:31.95938+00:00
-- url     : https://prove2.me/submissions/e2b8fe9e-0acc-463a-b1a0-7e58823d75b4

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OrthogonalIntVectorsNotAgreeOnRegular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RegularIffNatDegreeAndExistsEllipticGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InnerProductRootPowerSumEqOfFrobeniusModEq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalLabelUnique
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_LabelUniq_pow_card_pow_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory
namespace GlobalTheory.CompanionTheory.TyFin.LabelUniq
section Field
variable {K : Type} [Field K] [Fintype K]
end Field
end GlobalTheory.CompanionTheory.TyFin.LabelUniq
namespace GlobalTheory.CompanionTheory.TyFin.LabelUniq
section Label
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
private theorem regular_iff_degree_lemma (α : AlgebraicClosure K) {e : ℕ} (he : 0 < e)
    (h : α ^ Fintype.card K ^ e = α) : (minpoly K α).natDegree ≤ e := by
  classical
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hexp : ∀ n (f : K[X]), f ^ (Fintype.card K ^ n) = expand K (Fintype.card K ^ n) f := by
    intro n
    induction n with
    | zero => intro f; simp
    | succ n ih =>
      intro f
      rw [pow_succ, pow_mul, ih, ← FiniteField.expand_card, ← Polynomial.expand_mul, Nat.mul_comm]
  have hg : (IntermediateField.AdjoinSimple.gen K α) ^ Fintype.card K ^ e = IntermediateField.AdjoinSimple.gen K α :=
    Subtype.ext (by simpa using h)
  have hfix' : ∀ y : IntermediateField.adjoin K {α}, y ^ Fintype.card K ^ e = y := by
    intro y
    obtain ⟨f, -, rfl⟩ := (IntermediateField.adjoin.powerBasis hint).exists_eq_aeval y
    rw [IntermediateField.adjoin.powerBasis_gen, ← map_pow, hexp, Polynomial.expand_aeval, hg]
  have hfix : ∀ y : IntermediateField.adjoin K {α}, (y : AlgebraicClosure K) ^ Fintype.card K ^ e = y := by
    intro y
    simpa using congrArg (fun z : IntermediateField.adjoin K {α} => (z : AlgebraicClosure K)) (hfix' y)
  haveI : FiniteDimensional K (IntermediateField.adjoin K {α}) :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite (IntermediateField.adjoin K {α}) := Module.finite_of_finite K
  letI : Fintype (IntermediateField.adjoin K {α}) := Fintype.ofFinite _
  have hcard : Fintype.card (IntermediateField.adjoin K {α}) = Fintype.card K ^ (minpoly K α).natDegree := by
    rw [Module.card_fintype (Module.finBasis K (IntermediateField.adjoin K {α})), Fintype.card_fin,
      IntermediateField.adjoin.finrank hint]
  have hqe : 1 < Fintype.card K ^ e := Nat.one_lt_pow he.ne' hq
  have hdeg : (X ^ (Fintype.card K ^ e) - X : (AlgebraicClosure K)[X]).natDegree = Fintype.card K ^ e := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hqe]
  have hF0 : (X ^ (Fintype.card K ^ e) - X : (AlgebraicClosure K)[X]) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hdeg
    omega
  have hle : Fintype.card (IntermediateField.adjoin K {α}) ≤ Fintype.card K ^ e := by
    calc Fintype.card (IntermediateField.adjoin K {α})
        = (Finset.univ.image (fun y : IntermediateField.adjoin K {α} => (y : AlgebraicClosure K))).card := by
          rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ]
      _ ≤ (X ^ (Fintype.card K ^ e) - X : (AlgebraicClosure K)[X]).roots.toFinset.card := by
          apply Finset.card_le_card
          intro z hz
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
          obtain ⟨y, rfl⟩ := hz
          rw [Multiset.mem_toFinset, Polynomial.mem_roots hF0, Polynomial.IsRoot, Polynomial.eval_sub,
            Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]
          exact hfix y
      _ ≤ (X ^ (Fintype.card K ^ e) - X : (AlgebraicClosure K)[X]).roots.card := Multiset.toFinset_card_le _
      _ ≤ (X ^ (Fintype.card K ^ e) - X : (AlgebraicClosure K)[X]).natDegree := Polynomial.card_roots' _
      _ = Fintype.card K ^ e := hdeg
  rw [hcard] at hle
  by_contra hlt
  rw [not_le] at hlt
  have := Nat.pow_lt_pow_right hq hlt
  omega
end Label
end GlobalTheory.CompanionTheory.TyFin.LabelUniq
end

set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.LabelUniq
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
namespace GlobalTheory.CompanionTheory.TyFin.LabelUniq
theorem _root_.solution {d : ℕ} (hd : 0 < d) (α : AlgebraicClosure K)
    (hα : α ^ (Fintype.card K ^ d - 1) = 1) :
    ((∀ e : ℕ, 0 < e → e < d → α ^ Fintype.card K ^ e ≠ α) ↔ (minpoly K α).natDegree = d) ∧
      ((minpoly K α).natDegree = d →
        ∃ x : GL (Fin d) K, Matrix.charpoly (x : Matrix (Fin d) (Fin d) K) = minpoly K α) := by
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hM : 0 < Fintype.card K ^ d - 1 := by
    have := Nat.le_self_pow hd.ne' (Fintype.card K)
    omega
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hα
    exact zero_ne_one hα
  have hαd : α ^ Fintype.card K ^ d = α := by
    have e : Fintype.card K ^ d = (Fintype.card K ^ d - 1) + 1 := by omega
    rw [e, pow_succ, hα, one_mul]
  have hle := regular_iff_degree_lemma α hd hαd
  have hpos : 0 < (minpoly K α).natDegree := minpoly.natDegree_pos hint
  have hm := pow_card_pow_self α (d := (minpoly K α).natDegree) rfl
  refine ⟨⟨fun h => ?_, fun h e he hed heq => ?_⟩, fun h => ?_⟩
  · by_contra hne
    exact h _ hpos (lt_of_le_of_ne hle hne) hm
  · have := regular_iff_degree_lemma α he heq
    omega
  · have hdim : (IntermediateField.adjoin.powerBasis hint).dim = d := by
      rw [IntermediateField.adjoin.powerBasis_dim, h]
    have hchar : (Matrix.reindex (finCongr hdim) (finCongr hdim)
        (Algebra.leftMulMatrix (IntermediateField.adjoin.powerBasis hint).basis
          (IntermediateField.adjoin.powerBasis hint).gen)).charpoly = minpoly K α := by
      rw [Matrix.charpoly_reindex, charpoly_leftMulMatrix, IntermediateField.adjoin.powerBasis_gen,
        IntermediateField.minpoly_gen]
    haveI : FiniteDimensional K (IntermediateField.adjoin K {α}) :=
      IntermediateField.adjoin.finiteDimensional hint
    have hdet : (Matrix.reindex (finCongr hdim) (finCongr hdim)
        (Algebra.leftMulMatrix (IntermediateField.adjoin.powerBasis hint).basis
          (IntermediateField.adjoin.powerBasis hint).gen)).det ≠ 0 := by
      rw [Matrix.det_reindex_self, ← Algebra.norm_eq_matrix_det, Ne, Algebra.norm_eq_zero_iff,
        IntermediateField.adjoin.powerBasis_gen]
      intro h0
      apply hα0
      simpa using congrArg (fun y : IntermediateField.adjoin K {α} => (y : AlgebraicClosure K)) h0
    have hu := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    exact ⟨hu.unit, by rw [IsUnit.unit_spec]; exact hchar⟩
end GlobalTheory.CompanionTheory.TyFin.LabelUniq
