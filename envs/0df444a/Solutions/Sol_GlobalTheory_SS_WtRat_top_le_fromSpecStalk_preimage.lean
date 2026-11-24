-- Prove2me | solution 1 for GlobalTheory.SS.WtRat.top_le_fromSpecStalk_preimage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:23:15.474806+00:00
-- url     : https://prove2.me/submissions/e8ac9f12-686a-46fb-8ecc-881bddc8374b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGenericFunctionFieldPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WtRat
variable {Y : Scheme.{0}}
namespace GlobalTheory.SS.WtRat
theorem _root_.solution (x : Y) {V : Y.Opens} (hx : x ∈ V) :
    ⊤ ≤ Y.fromSpecStalk x ⁻¹ᵁ V := by
  intro y _
  have : Y.fromSpecStalk x y ∈ Set.range (Y.fromSpecStalk x) := ⟨y, rfl⟩
  rw [Scheme.range_fromSpecStalk] at this
  exact this.mem_open V.isOpen hx
end GlobalTheory.SS.WtRat
