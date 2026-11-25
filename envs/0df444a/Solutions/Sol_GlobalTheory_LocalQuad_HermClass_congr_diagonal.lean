-- Prove2me | solution 1 for GlobalTheory.LocalQuad.HermClass.congr_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:12:42.71414+00:00
-- url     : https://prove2.me/submissions/6f6d960e-4740-4a35-8dfe-ced2257ff491

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroCoordNeZero
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_trans
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_symm
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_det
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_congr_diagonal_of_tail
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_exists_represent
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_posCount_succ
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_posIndex_diagonal_map
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_posIndex_of_congr
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_exists_sign_iff
import Theorems.Thm_GlobalTheory_HermDiag_exists_congr_diagonal_herm_col_eq
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_Published_Landherr_size_one
import Theorems.Thm_GlobalTheory_Published_Landherr_size_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Inertia.negIndex_neg
attribute [local simp] GlobalTheory.Inertia.posIndex_neg



set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.LocalQuad
open GlobalTheory.LocalQuad.HermClass
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.LocalQuad.HermClass
theorem _root_.solution (H : Isotropy) (r : ℕ) : ∀ g g' : Fin r → E,
    (∀ i, cc (g i) = g i) → (∀ i, cc (g' i) = g' i) → (∀ i, g i ≠ 0) → (∀ i, g' i ≠ 0) →
    (∀ τ : E →+* ℂ, posCount τ g = posCount τ g') →
    (∃ x : E, ∏ i, g i = x * cc x * ∏ i, g' i) →
    Congr (IsCMField.complexConj E : E →+* E) (Matrix.diagonal g) (Matrix.diagonal g') := by
  induction r with
  | zero =>
    intro g g' _ _ _ _ _ _
    exact GlobalTheory.Published.Landherr.size_zero _ _
  | succ r ih =>
    intro g g' hg hg' h0 h0' hs ⟨x, hx⟩
    have hp : ∏ i, g i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => h0 i
    have hp' : ∏ i, g' i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => h0' i
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · refine GlobalTheory.Published.Landherr.size_one _ _ (by rwa [Matrix.det_diagonal])
        (by rwa [Matrix.det_diagonal]) ⟨x, ?_⟩
      rw [Matrix.det_diagonal, Matrix.det_diagonal, hx, mul_div_cancel_right₀ _ hp']
    obtain ⟨z, hz⟩ := exists_represent H (by omega) hg h0 (hg' 0) (h0' 0)
      fun τ => exists_sign_iff τ (hs τ) 0
    have hG : ∀ a b, cc (Matrix.diagonal g a b) = Matrix.diagonal g b a := by
      intro a b
      by_cases hab : a = b
      · subst hab
        simpa using hg a
      · simp [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab), cc]
    obtain ⟨P, k, hP, hPk, hk, hk0, -, hk1⟩ :=
      GlobalTheory.HermDiag.exists_congr_diagonal_herm_col_eq hG (x := z) (hz ▸ h0' 0) 0
    have hk0 := hk0 (by rwa [Matrix.det_diagonal])
    have hc : Congr (IsCMField.complexConj E : E →+* E) (Matrix.diagonal g) (Matrix.diagonal k) :=
      ⟨P, hP, hPk.symm⟩
    have hk2 : k 0 = g' 0 := hk1.trans hz
    refine hc.trans (congr_diagonal_of_tail hk2 (ih _ _ (fun i => hk _) (fun i => hg' _)
      (fun i => hk0 _) (fun i => h0' _) (fun τ => ?_) ?_))
    · have h1 := posIndex_of_congr τ hc
      rw [posIndex_diagonal_map, posIndex_diagonal_map, hs τ, posCount_succ, posCount_succ τ g',
        hk2] at h1
      exact Nat.add_left_cancel h1
    · obtain ⟨y, -, hy⟩ := hc.det
      rw [Matrix.det_diagonal, Matrix.det_diagonal, hx, Fin.prod_univ_succ, Fin.prod_univ_succ,
        hk2] at hy
      refine ⟨y * x, mul_left_cancel₀ (h0' 0) ?_⟩
      rw [hy]
      simp only [cc, map_mul, RingHom.coe_coe]
      ring
end GlobalTheory.LocalQuad.HermClass
