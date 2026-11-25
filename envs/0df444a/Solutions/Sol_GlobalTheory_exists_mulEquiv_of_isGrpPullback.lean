-- Prove2me | solution 1 for GlobalTheory.exists_mulEquiv_of_isGrpPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:52:10.316385+00:00
-- url     : https://prove2.me/submissions/d2074cdf-76e7-4ded-adf3-f39ed3986ad9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulEquivOfIsGrpPullback

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
open GlobalTheory
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
namespace GlobalTheory
theorem _root_.solution (h : IsGrpPullback G' G f φ) {X : Scheme.{0}} (a : X ⟶ S') (b : X ⟶ S)
    (hb : b = a ≫ f) :
    ∃ e : (Over.mk a ⟶ G') ≃* (Over.mk b ⟶ G), ∀ x, (e x).left = x.left ≫ φ := by
  subst hb
  let ρ : (Over.mk a ⟶ G') →* (Over.mk (a ≫ f) ⟶ G) :=
    MonoidHom.mk' (pushPt h.1.w) fun x y => Over.OverMorphism.ext (h.2 (Over.mk a) x y _ _ rfl rfl).symm
  have hρ : ∀ x, (ρ x).left = x.left ≫ φ := fun _ => rfl
  refine ⟨MulEquiv.ofBijective ρ ⟨fun x y hxy => ?_, fun y => ?_⟩, hρ⟩
  · refine Over.OverMorphism.ext (h.1.hom_ext ?_ ((Over.w x).trans (Over.w y).symm))
    exact (hρ x).symm.trans ((congrArg (fun z => z.left) hxy).trans (hρ y))
  · exact ⟨Over.homMk (h.1.lift y.left a (Over.w y)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext ((hρ _).trans (h.1.lift_fst _ _ _))⟩
end GlobalTheory
