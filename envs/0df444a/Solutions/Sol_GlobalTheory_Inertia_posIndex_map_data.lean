-- Prove2me | solution 1 for GlobalTheory.Inertia.posIndex_map_data
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:59:03.964965+00:00
-- url     : https://prove2.me/submissions/4ff9d3cc-3738-4f55-9ebe-ee3ee898208d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_gram_eq_sgn_iff
import Theorems.Thm_GlobalTheory_Inertia_posIndex_map_conjugate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Inertia
open Module Matrix ReciprocityTheory.ChartRestriction.G
open scoped ComplexConjugate
open NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace GlobalTheory.Inertia
theorem _root_.solution (X : FD.Data E r) (τ : E →+* ℂ) : posIndex (X.Gm.map τ) = X.p0 := by
  have key : ∀ σ ∈ X.Ψ, posIndex (X.Gm.map σ) = X.p0 := fun σ hσ =>
    ((gram_eq_sgn_iff σ X.Gm_herm X.Gm_det X.p0).1 ⟨X.p0_le, X.signature ⟨σ, hσ⟩⟩).symm
  by_cases h : τ ∈ X.Ψ
  · exact key τ h
  · rw [← posIndex_map_conjugate τ X.Gm_herm]
    refine key _ ?_
    by_contra h'
    exact h ((X.cmType τ).2 h')
end GlobalTheory.Inertia
