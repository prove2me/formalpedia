-- Prove2me | solution 1 for GlobalTheory.exists_isUnit_det_mul_eq_neg_of_linearIndependent_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:37:17.936199+00:00
-- url     : https://prove2.me/submissions/3db3a160-54f0-41a9-a0b9-a336d8068348

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsLinearIndependentSumElimOfFinrankEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsUnimodularMulEqNegOfIndependentModMaximal
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_neg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_neg
import Theorems.Thm_GlobalTheory_exists_linearIndependent_sumElim_of_finrank_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTAgree_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R : Type} [CommRing R]
    [IsLocalRing R] (n n0 : ℕ) (Φ : Fin n → Fin n0 → R)
    (h : LinearIndependent (IsLocalRing.ResidueField R)
      (fun (c : Fin n0) (b : Fin n) => IsLocalRing.residue R (Φ b c))) :
    n0 ≤ n ∧ ∃ Y : Matrix (Fin n) (Fin n) R, IsUnit Y.det ∧
      ∀ (b : Fin n) (c : Fin n0), ∑ b', Y b b' * Φ b' c = if b.val = c.val then -1 else 0 := by
  have hle : n0 ≤ n := by simpa using h.fintype_card_le_finrank
  refine ⟨hle, ?_⟩
  obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le hle
  obtain ⟨w, hw⟩ := exists_linearIndependent_sumElim_of_finrank_eq (n' := n') (by simp) _ h
  choose s hs using IsLocalRing.residue_surjective (R := R)
  let M : Matrix (Fin (n0 + n')) (Fin (n0 + n')) R := Matrix.of fun i j =>
    Sum.elim (Φ i) (fun j' => s (w j' i)) (finSumFinEquiv.symm j)
  have hcol : (M.map (IsLocalRing.residue R)).col =
      Sum.elim (fun (c : Fin n0) (b : Fin (n0 + n')) => IsLocalRing.residue R (Φ b c)) w ∘
        finSumFinEquiv.symm := by
    funext j i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rcases j with j | j
    · simp [M, Matrix.col]
    · simp [M, Matrix.col, hs]
  have hu : IsUnit (M.map (IsLocalRing.residue R)) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit, hcol]
    exact hw.comp _ finSumFinEquiv.symm.injective
  have hdet : IsUnit M.det := by
    rw [Matrix.isUnit_iff_isUnit_det] at hu
    have : (M.map (IsLocalRing.residue R)).det = IsLocalRing.residue R M.det :=
      (RingHom.map_det (IsLocalRing.residue R) M).symm
    rw [this] at hu
    exact (isUnit_map_iff (IsLocalRing.residue R) _).mp hu
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hdet
  refine ⟨-M⁻¹, ?_, ?_⟩
  · rw [← Matrix.isUnit_iff_isUnit_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det M hdet)).neg
  · intro b c
    have hij : ∑ b', M⁻¹ b b' * Φ b' c = (M⁻¹ * M) b (Fin.castAdd n' c) := by
      simp [M, Matrix.mul_apply]
    simp only [Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [hij, hinv, Matrix.one_apply]
    by_cases hbc : b.val = c.val
    · rw [if_pos hbc, if_pos (Fin.ext hbc)]
    · rw [if_neg hbc, if_neg (fun e => hbc (by rw [e]; rfl)), neg_zero]
end GlobalTheory
