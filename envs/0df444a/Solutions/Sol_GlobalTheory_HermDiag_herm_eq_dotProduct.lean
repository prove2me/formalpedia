-- Prove2me | solution 1 for GlobalTheory.HermDiag.herm_eq_dotProduct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:28.430815+00:00
-- url     : https://prove2.me/submissions/566556f7-31b0-4a84-b7b3-2d7411eba31b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Theorems.Thm_GlobalTheory_HermDiag_dotProduct_mulVec_comp_eq_sum

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
theorem _root_.solution (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    FD.herm G x y = x ⬝ᵥ G *ᵥ (FD.cc ∘ y) :=
  (dotProduct_mulVec_comp_eq_sum FD.cc G x y).symm
end GlobalTheory.HermDiag
