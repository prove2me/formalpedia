-- Prove2me | solution 1 for GlobalTheory.GmPoints.evalOne_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:34:54.750042+00:00
-- url     : https://prove2.me/submissions/a97d893d-f831-46b1-9b2d-52339a6ea071

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.GmPoints
variable {O : Type} [CommRing O] {R : Type} [CommRing R] [Algebra O R]
namespace GlobalTheory.GmPoints
theorem _root_.solution {M : Type} [Group M] :
    Function.Bijective (fun f : Multiplicative (ULift.{0} ℤ) →* M =>
      f (Multiplicative.ofAdd (ULift.up 1))) := by
  have h : ∀ n : ℤ, (Multiplicative.ofAdd (ULift.up n) : Multiplicative (ULift.{0} ℤ)) =
      (Multiplicative.ofAdd (ULift.up 1)) ^ n := by
    intro n
    rw [← ofAdd_zsmul]
    congr 1
    ext
    simp
  constructor
  · intro f g hfg
    ext ⟨n⟩
    have := h n
    change f (Multiplicative.ofAdd (ULift.up n)) = g (Multiplicative.ofAdd (ULift.up n))
    rw [this, map_zpow, map_zpow]
    exact congrArg (· ^ n) hfg
  · intro m
    exact ⟨{ toFun := fun x => m ^ x.toAdd.down
             map_one' := zpow_zero m
             map_mul' := fun x y => zpow_add m _ _ }, zpow_one m⟩
end GlobalTheory.GmPoints
