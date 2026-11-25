-- Prove2me | solution 1 for GlobalTheory.Inertia.gram_eq_sgn_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:56:12.694945+00:00
-- url     : https://prove2.me/submissions/015ba301-797d-405b-8acb-b48a15b3d63f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_congr_sgn_iff
import Theorems.Thm_GlobalTheory_Inertia_isHermitian_map
import Theorems.Thm_GlobalTheory_Inertia_det_map_ne_zero
import Theorems.Thm_GlobalTheory_Inertia_gram_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Inertia.posIndex_neg
attribute [local simp] GlobalTheory.Inertia.negIndex_neg

set_option autoImplicit false
open GlobalTheory GlobalTheory.Inertia
open Module Matrix ReciprocityTheory.ChartRestriction.G
open scoped ComplexConjugate
open NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.Inertia
theorem _root_.solution (τ : E →+* ℂ) {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, FD.cc (G a b) = G b a) (hG0 : G.det ≠ 0) (p : ℕ) :
    (p ≤ r ∧ ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧
      FD.gram τ G P = diagonal fun a : Fin r => ((FD.sgn p a : ℝ) : ℂ)) ↔
      p = posIndex (G.map τ) := by
  simp only [gram_eq]
  exact congr_sgn_iff (isHermitian_map τ hG) (det_map_ne_zero τ hG0) p
end GlobalTheory.Inertia
