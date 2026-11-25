-- Prove2me | solution 1 for GlobalTheory.HermDiag.coe_complexConj_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:46:33.455243+00:00
-- url     : https://prove2.me/submissions/e8ca6720-84cf-4760-b115-c1b5c02bbcf7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermDiag
open Module Matrix
open NumberField ReciprocityTheory.ChartRestriction.G
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.HermDiag
theorem _root_.solution :
    ⇑((IsCMField.complexConj E : E →+* E)) = FD.cc := rfl
end GlobalTheory.HermDiag
