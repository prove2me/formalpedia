-- Prove2me | solution 1 for GlobalTheory.FamFree.mk_eq_mk_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:14.1693+00:00
-- url     : https://prove2.me/submissions/1761bf90-1b58-4b18-a2de-e123e32beb94

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps

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
theorem _root_.solution {k : ℕ} (α β : D.X) :
    (QuotientAddGroup.mk α : D.X ⧸ multiples D k) = QuotientAddGroup.mk β ↔ ∃ mu, α + k • mu = β := by
  rw [QuotientAddGroup.eq]
  constructor
  · rintro ⟨mu, h⟩
    exact ⟨mu, by rw [show k • mu = -α + β from h, add_neg_cancel_left]⟩
  · rintro ⟨mu, rfl⟩
    exact ⟨mu, by rw [neg_add_cancel_left]; rfl⟩
end GlobalTheory.FamFree
