-- Prove2me | solution 1 for GlobalTheory.FamFree.zero_add_nsmul_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:14:13.030821+00:00
-- url     : https://prove2.me/submissions/48ea958d-dc4b-461c-b236-3426302d84c9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
import Theorems.Thm_GlobalTheory_FamFree_zero_add_nsmul
import Theorems.Thm_GlobalTheory_FamFree_zero_of_eq_add_nsmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FamFree
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.FamFree
theorem _root_.solution (hG : GlobalFnsSt) {k : ℕ} (s : Fam D F k) (α mu : D.X) :
    (∀ j, (s.s (α + k • mu)).f j = 0) ↔ ∀ j, (s.s α).f j = 0 :=
  ⟨zero_of_eq_add_nsmul hG s ⟨-mu, by rw [smul_neg, add_neg_cancel_right]⟩, zero_add_nsmul hG s α mu⟩
end GlobalTheory.FamFree
