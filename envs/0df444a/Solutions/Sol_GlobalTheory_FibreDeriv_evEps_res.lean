-- Prove2me | solution 1 for GlobalTheory.FibreDeriv.evEps_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:04:45.424422+00:00
-- url     : https://prove2.me/submissions/955a7f82-0f29-46d6-9424-abc5d202dd3e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDerivAt0OfIsPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology
open GlobalTheory
open GlobalTheory.FibreDeriv
variable {g : ℕ} {X Y : Scheme.{0}}
namespace GlobalTheory.FibreDeriv
theorem _root_.solution (v : Sp (DualNumber ℂ) ⟶ X) {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) (hV : ⊤ ≤ v ⁻¹ᵁ V)
    (hU : ⊤ ≤ v ⁻¹ᵁ U) : evEps v V hV (resG X h f) = evEps v U hU f := by
  simp only [evEps, CommRingCat.hom_comp, RingHom.comp_apply]
  congr 1
  change (v.appLE V ⊤ hV).hom ((X.presheaf.map (homOfLE h).op).hom f) = _
  rw [← CommRingCat.comp_apply (X.presheaf.map _), Scheme.Hom.map_appLE]
end GlobalTheory.FibreDeriv
