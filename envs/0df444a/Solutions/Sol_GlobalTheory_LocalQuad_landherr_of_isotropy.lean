-- Prove2me | solution 1 for GlobalTheory.LocalQuad.landherr_of_isotropy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:01:32.231723+00:00
-- url     : https://prove2.me/submissions/5db1e149-18cd-4939-acb8-9d883e2f2003

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroCoordNeZero
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_trans
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_symm
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_det
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_posIndex_diagonal_map
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_posIndex_of_congr
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_congr_diagonal
import Theorems.Thm_GlobalTheory_HermDiag_exists_congr_diagonal_herm
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_congr
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
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
open HermClass
namespace GlobalTheory.LocalQuad
theorem _root_.solution
    (H : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] (a : ι → F),
      5 ≤ Fintype.card ι → (∀ i, a i ≠ 0) → (∀ σ : F →+* ℝ, ∃ i j, σ (a i) < 0 ∧ 0 < σ (a j)) →
      ∃ x : ι → F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0) :
    GlobalTheory.Published.Landherr := by
  intro E _ _ _ r G G' hG hG' hd hd' hs ⟨x, hx⟩
  obtain ⟨P, g, hP, hPg, hg, hg0⟩ := GlobalTheory.HermDiag.exists_congr_diagonal_herm hG
  obtain ⟨P', g', hP', hPg', hg', hg0'⟩ := GlobalTheory.HermDiag.exists_congr_diagonal_herm hG'
  have hc : Congr (IsCMField.complexConj E : E →+* E) G (Matrix.diagonal g) := ⟨P, hP, hPg.symm⟩
  have hc' : Congr (IsCMField.complexConj E : E →+* E) G' (Matrix.diagonal g') :=
    ⟨P', hP', hPg'.symm⟩
  refine (hc.trans (congr_diagonal H r g g' hg hg' (hg0 hd) (hg0' hd') (fun τ => ?_) ?_)).trans
    hc'.symm
  · obtain ⟨Q, hQ, h⟩ := hs τ
    rw [← posIndex_diagonal_map, ← posIndex_diagonal_map, posIndex_of_congr τ hc,
      posIndex_of_congr τ hc', h, GlobalTheory.Inertia.posIndex_congr _ hQ]
  · obtain ⟨y, -, hy⟩ := hc.det
    obtain ⟨y', -, hy'⟩ := hc'.symm.det
    rw [div_eq_iff hd'] at hx
    rw [Matrix.det_diagonal] at hy hy'
    refine ⟨y * x * y', ?_⟩
    rw [hy, hx, hy']
    simp only [cc, map_mul, RingHom.coe_coe]
    ring
end GlobalTheory.LocalQuad
