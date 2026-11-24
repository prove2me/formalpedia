-- Prove2me | solution 1 for GlobalTheory.Inertia.posIndex_le
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T03:18:41.487154+00:00
-- url     : https://prove2.me/submissions/63325da7-b8d6-44b9-93d0-89fb7e6706e7

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
variable {r s : ℕ}


theorem solution (G : Matrix (Fin r) (Fin r) ℂ) : posIndex G ≤ r := by
  classical
  apply csSup_le'; intro d hd; obtain ⟨W,rfl,_⟩ := hd
  simpa using Submodule.finrank_le W
