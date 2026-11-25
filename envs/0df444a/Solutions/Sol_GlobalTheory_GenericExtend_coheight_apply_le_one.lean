-- Prove2me | solution 1 for GlobalTheory.GenericExtend.coheight_apply_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:05:17.901064+00:00
-- url     : https://prove2.me/submissions/fd84b909-ebc5-45a5-82fa-b1e86eee23dd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLineBundleGeneratorExtendingDensePart
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed


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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.GenericExtend
namespace GlobalTheory.GenericExtend
theorem _root_.solution {X Y : Scheme.{0}} (p : Y ⟶ X) [Flat p] {y : Y}
    (h : Order.coheight y ≤ 1) : Order.coheight (p y) ≤ 1 := by
  refine (Order.coheight_le_coe_iff (n := 1)).2 fun x₁ hx₁ ↦ ?_
  obtain ⟨y₁, hy₁, rfl⟩ := Flat.generalizingMap p (show x₁ ⤳ p y from hx₁.le)
  have hlt : y < y₁ := lt_of_le_not_ge hy₁ fun h' ↦
    hx₁.not_ge (show p y ⤳ p y₁ from (show y ⤳ y₁ from h').map p.continuous)
  have h0 := (Order.coheight_le_coe_iff (n := 1)).1 h y₁ hlt
  rw [Nat.cast_one, ENat.lt_one_iff_eq_zero, Order.coheight_eq_zero] at h0 ⊢
  intro x₂ hx₂
  obtain ⟨y₂, hy₂, rfl⟩ := Flat.generalizingMap p (show x₂ ⤳ p y₁ from hx₂)
  exact (show y₁ ⤳ y₂ from h0 hy₂).map p.continuous
end GlobalTheory.GenericExtend
