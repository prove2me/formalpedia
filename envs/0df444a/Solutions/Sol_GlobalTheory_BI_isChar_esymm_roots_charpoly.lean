-- Prove2me | solution 1 for GlobalTheory.BI.isChar_esymm_roots_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:09:55.032374+00:00
-- url     : https://prove2.me/submissions/a8f43bd3-5255-4cd7-84ae-c7aee0a1c3b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterOverSubfieldOfRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_IsCharacterEsymmRootsCharpoly
import Theorems.Thm_GlobalTheory_BI_isChar_and_isIrrChar_of_rep
import Theorems.Thm_GlobalTheory_IsLogBounded_compoundMatrix
import Theorems.Thm_GlobalTheory_IsLogBounded_det
import Theorems.Thm_GlobalTheory_range_subsetEnum
import Theorems.Thm_GlobalTheory_subsetEnum_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI
open Polynomial in
private lemma det_submatrix_subsetEnum_eq_det_submatrix_val {n j : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (S : Set.powersetCard (Fin n) j) :
    (A.submatrix (_root_.GlobalTheory.subsetEnum S) (_root_.GlobalTheory.subsetEnum S)).det =
      (A.submatrix (Subtype.val : {x // x ∈ S.1} → Fin n) Subtype.val).det := by
  have hmem : ∀ i, _root_.GlobalTheory.subsetEnum S i ∈ S.1 := fun i => by
    have : _root_.GlobalTheory.subsetEnum S i ∈ Set.range (_root_.GlobalTheory.subsetEnum S) :=
      ⟨i, rfl⟩
    rw [_root_.GlobalTheory.range_subsetEnum] at this
    exact_mod_cast this
  let σ : Fin j ≃ {x // x ∈ S.1} := Equiv.ofBijective
    (fun i => ⟨_root_.GlobalTheory.subsetEnum S i, hmem i⟩)
    ⟨fun a b hab => _root_.GlobalTheory.subsetEnum_injective S (congrArg Subtype.val hab),
      fun x => by
        have hx : x.1 ∈ ((S.1 : Finset (Fin n)) : Set (Fin n)) := x.2
        rw [← _root_.GlobalTheory.range_subsetEnum] at hx
        obtain ⟨i, hi⟩ := hx
        exact ⟨i, Subtype.ext hi⟩⟩
  have hsub : A.submatrix (_root_.GlobalTheory.subsetEnum S) (_root_.GlobalTheory.subsetEnum S) =
      (A.submatrix (Subtype.val : {x // x ∈ S.1} → Fin n) Subtype.val).submatrix σ σ := rfl
  rw [hsub, Matrix.det_submatrix_equiv_self]
open Polynomial in
private lemma trace_compoundMatrix_eq_sum_principal_minors {n : ℕ} (j : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (_root_.GlobalTheory.compoundMatrix j A).trace = ∑ s ∈ Finset.powersetCard j Finset.univ,
      (A.submatrix (Subtype.val : s → Fin n) Subtype.val).det := by
  rw [Finset.sum_subtype (p := fun s : Finset (Fin n) => s ∈ Set.powersetCard (Fin n) j) _
    (fun s => by simp [Finset.mem_powersetCard, Set.powersetCard])]
  unfold _root_.GlobalTheory.compoundMatrix
  simp only [Matrix.trace, Matrix.diag, Matrix.of_apply]
  exact Finset.sum_congr rfl fun S _ => det_submatrix_subsetEnum_eq_det_submatrix_val A S
open Polynomial in
private lemma esymm_roots_charpoly_eq_sum_principal_minors {n : ℕ} (j : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) :
    M.charpoly.roots.esymm j = ∑ s ∈ Finset.powersetCard j Finset.univ,
      (M.submatrix (Subtype.val : s → Fin n) Subtype.val).det := by
  have hdeg : M.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hcard : M.charpoly.roots.card = M.charpoly.natDegree :=
    splits_iff_card_roots.mp (IsAlgClosed.splits _)
  rcases le_or_gt j n with hj | hj
  · have h1 := coeff_eq_esymm_roots_of_card hcard (k := n - j) (by omega)
    have h2 := M.charpoly_coeff_eq_sum_minors j (by simp [hj])
    rw [hdeg, Nat.sub_sub_self hj, M.charpoly_monic.leadingCoeff, one_mul] at h1
    rw [Fintype.card_fin, h1] at h2
    exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) h2
  · rw [Finset.powersetCard_eq_empty.mpr (by simp [hj]), Finset.sum_empty, Multiset.esymm,
      Multiset.powersetCard_eq_empty _ (by omega)]
    simp
end GlobalTheory.BI
end
end

set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
noncomputable section
open GlobalTheory GlobalTheory.BI
open Polynomial
namespace GlobalTheory.BI
namespace _root_.GlobalTheory.BI
theorem _root_.solution :
    ∀ (G : Type) [Group G] (n j : ℕ) (ρ : G →* GL (Fin n) ℂ), _root_.GlobalTheory.BI.IsChar ℂ ℂ
      (fun g => (Matrix.charpoly (ρ g : Matrix (Fin n) (Fin n) ℂ)).roots.esymm j) := by
  intro G _ n j ρ
  have h := (_root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep ℂ ℂ G _ (_root_.GlobalTheory.BI.compoundRep j ρ)).1
  have heq : (fun g => (Matrix.charpoly (ρ g : Matrix (Fin n) (Fin n) ℂ)).roots.esymm j) =
      fun g => algebraMap ℂ ℂ ((_root_.GlobalTheory.BI.compoundRep j ρ).character g) := by
    funext g
    rw [Algebra.algebraMap_self, RingHom.id_apply]
    change _ = LinearMap.trace ℂ _
      (Matrix.toLin' (_root_.GlobalTheory.compoundMatrix j (ρ g : Matrix (Fin n) (Fin n) ℂ)))
    rw [Matrix.trace_toLin'_eq, trace_compoundMatrix_eq_sum_principal_minors, esymm_roots_charpoly_eq_sum_principal_minors]
  rw [heq]
  exact h
end _root_.GlobalTheory.BI
end GlobalTheory.BI
