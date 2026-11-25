-- Prove2me | solution 1 for GlobalTheory.Inertia.negIndex_le_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:57:23.465012+00:00
-- url     : https://prove2.me/submissions/292ae38f-ac17-4687-a8ae-aa16f527f27a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_posIndex_le_card

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
namespace GlobalTheory.Inertia
theorem _root_.solution (G : Matrix n n ℂ) : negIndex G ≤ Fintype.card n :=
  posIndex_le_card _
end GlobalTheory.Inertia
