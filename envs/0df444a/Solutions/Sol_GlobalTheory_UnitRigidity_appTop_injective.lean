-- Prove2me | solution 1 for GlobalTheory.UnitRigidity.appTop_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:36:15.158984+00:00
-- url     : https://prove2.me/submissions/45457730-d2ad-43f3-9a7a-88a2c4de64cc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitOnProductEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfIsPullbackOfSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.UnitRigidity
open scoped TensorProduct
namespace GlobalTheory.UnitRigidity
theorem _root_.solution {U X : Scheme.{0}} [IsIntegral X] [Nonempty U] (m : U ⟶ X)
    [IsOpenImmersion m] : Function.Injective m.appTop.hom := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  by_contra h
  rw [← basicOpen_eq_bot_iff] at h
  obtain ⟨_, hx, x, rfl⟩ := nonempty_preirreducible_inter (X.basicOpen v).isOpen
    m.isOpenEmbedding.isOpen_range (TopologicalSpace.Opens.ne_bot_iff_nonempty _ |>.mp h)
    (Set.range_nonempty _)
  have hx' : x ∈ m ⁻¹ᵁ X.basicOpen v := hx
  rw [Scheme.preimage_basicOpen_top, hv, Scheme.basicOpen_zero] at hx'
  exact hx'
end GlobalTheory.UnitRigidity
