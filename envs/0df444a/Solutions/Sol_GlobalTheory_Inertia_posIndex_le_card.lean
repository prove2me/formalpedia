-- Prove2me | solution 1 for GlobalTheory.Inertia.posIndex_le_card
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T02:25:45.838438+00:00
-- url     : https://prove2.me/submissions/d5202303-3c09-47cc-857f-cb8d4292306b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
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
variable {n m : Type*} [Fintype n] [Fintype m]


theorem solution (G : Matrix n n ℂ) : posIndex G ≤ Fintype.card n := by
  classical
  apply csSup_le'
  intro d hd
  obtain ⟨W,rfl,_⟩ := hd
  simpa using Submodule.finrank_le W
