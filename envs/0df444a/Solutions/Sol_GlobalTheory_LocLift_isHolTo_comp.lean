-- Prove2me | solution 1 for GlobalTheory.LocLift.isHolTo_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:20.144686+00:00
-- url     : https://prove2.me/submissions/cffa1478-4580-4bed-adef-451c1bb0fa6e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearEquivLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open Filter Topology
open GlobalTheory GlobalTheory.LocLift
noncomputable section
variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  {X Y : Scheme.{0}}
namespace GlobalTheory.LocLift
theorem _root_.solution {B : Set V} {y : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) {C : Set W} (hC : IsOpen C) {β : W → V}
    (hβ : DifferentiableOn ℂ β C) (hm : Set.MapsTo β C B) : IsHolTo C (fun w => y (β w)) := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  refine ⟨?_, h2.comp (hβ.mono fun w hw => hw.1) fun w hw => ⟨hm hw.1, hw.2⟩⟩
  have := hβ.continuousOn.isOpen_inter_preimage hC h1
  convert this using 1
  ext w
  exact ⟨fun hw => ⟨hw.1, hm hw.1, hw.2⟩, fun hw => ⟨hw.1, hw.2.2⟩⟩
end GlobalTheory.LocLift
