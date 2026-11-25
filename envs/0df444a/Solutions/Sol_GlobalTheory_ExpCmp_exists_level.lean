-- Prove2me | solution 1 for GlobalTheory.ExpCmp.exists_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:27:21.324626+00:00
-- url     : https://prove2.me/submissions/5f347f3c-fbec-49ba-b0a1-21a69f83e35b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_MatchingSectionsExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitMapSnd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
noncomputable section
open GlobalTheory GlobalTheory.ExpCmp
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ExpTrans GlobalTheory.UnitSec
variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]
omit [IsDomain R] [IsDomain V]
namespace GlobalTheory.ExpCmp
theorem _root_.solution {I : Ideal R} {I' : Ideal V} {φ : R →+* V} (hI : I.map φ ≤ I')
    {G : Over (Spec (CommRingCat.of R))} {G' : Over (Spec (CommRingCat.of V))} {F : G'.left ⟶ G.left}
    (hF : F ≫ G.hom = G'.hom ≫ spMap φ) (e : ℕ) :
    ∃ m : (thickObj V I' e G').left ⟶ (thickObj R I e G).left,
      m ≫ (fstG I e G).left = (fstG I' e G').left ≫ F := by
  have hle : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ :=
    Ideal.map_le_iff_le_comap.1 (by rw [Ideal.map_pow]; exact Ideal.pow_right_mono hI _)
  refine ⟨pullback.lift ((fstG I' e G').left ≫ F)
    (pullback.snd G'.hom (thick V I' e) ≫ spMap (Ideal.quotientMap (I' ^ (e + 1)) φ hle)) ?_, pullback.lift_fst _ _ _⟩
  have e2 : (fstG I' e G').left ≫ G'.hom = pullback.snd G'.hom (thick _ I' e) ≫ thick _ I' e := pullback.condition
  rw [Category.assoc, hF, ← Category.assoc, e2, Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  rfl
end GlobalTheory.ExpCmp
