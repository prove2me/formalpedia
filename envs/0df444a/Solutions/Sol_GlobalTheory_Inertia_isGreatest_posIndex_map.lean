-- Prove2me | solution 1 for GlobalTheory.Inertia.isGreatest_posIndex_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:56:17.988613+00:00
-- url     : https://prove2.me/submissions/996d01b0-b23e-4be0-bb22-1080b65a631e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_isGreatest_posIndex
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_hermC_eq_dotProduct
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
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.Inertia
theorem _root_.solution (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) :
    IsGreatest {d | ∃ W : Submodule ℂ (Fin r → ℂ), finrank ℂ W = d ∧
      ∀ x ∈ W, x ≠ 0 → 0 < (FD.hermC τ G x x).re} (posIndex (G.map τ)) := by
  simp only [hermC_eq_dotProduct]
  exact isGreatest_posIndex _
end GlobalTheory.Inertia
