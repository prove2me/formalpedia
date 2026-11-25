-- Prove2me | solution 1 for GlobalTheory.FamFree.eq_of_eq_add_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:52:18.125614+00:00
-- url     : https://prove2.me/submissions/11566baa-5982-4751-91e1-a0b79fe8f2dd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
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
theorem _root_.solution (hG : GlobalFnsSt) {k : ℕ} (s t : Fam D F k) {α β : D.X} (hβ : ∃ mu, α + k • mu = β)
    (h : s.s α = t.s α) : s.s β = t.s β := by
  have h0 := zero_of_eq_add_nsmul hG (s + -t) hβ (fun j => by rw [add_f, neg_f, h, add_neg_cancel])
  refine SecOps.sec_ext fun j => ?_
  have := h0 j
  rw [add_f, neg_f, add_neg_eq_zero] at this
  exact this
end GlobalTheory.FamFree
