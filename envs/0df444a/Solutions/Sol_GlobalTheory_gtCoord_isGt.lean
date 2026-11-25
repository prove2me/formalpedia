-- Prove2me | solution 1 for GlobalTheory.gtCoord_isGt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:36:16.913436+00:00
-- url     : https://prove2.me/submissions/f92fcdc1-1650-4637-be7a-6143853859bb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAbelianSchemeThick
import Theorems.Thm_GlobalTheory_CoordToExt_exists_iso
import Theorems.Thm_GlobalTheory_CoordToExt_exists_rig
import Theorems.Thm_GlobalTheory_CoordToExt_isGt_of_units
import Theorems.Thm_GlobalTheory_CoordToExt_bundle_add
import Theorems.Thm_GlobalTheory_CoordToExt_bundle_zero
import Theorems.Thm_GlobalTheory_CoordToExt_bundle_primitive
import Theorems.Thm_GlobalTheory_CoordToExt_isAbelianScheme_thick
import Theorems.Thm_GlobalTheory_CoordToExt_coordUnit_trans
import Theorems.Thm_GlobalTheory_CoordToExt_coordUnit_weight
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_WeightPf_O__comp_24bcd133e28a
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_isLB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open CoordToExt
namespace GlobalTheory
theorem _root_.solution : Geo.Tor.GtCoordToGtSt := by
  rintro R _ _ I D e G _ _ ⟨g⟩
  have := g.q_hom
  have he : eSec (thickObj R I e G) ≫ g.q.left = eSec (thickObj R I e D.P.A) :=
    congrArg (fun f => f.left) (IsMonHom.one_hom g.q)
  choose ρ hρ hρ' using fun χ => exists_rig g.q.left _ _ he (bundle I D e χ) (coordUnit g χ) (coordUnit_trans g χ)
  let E : SplitExt (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    { B := thickObj R I e D.P.A
      isAbelian := isAbelianScheme_thick I D e
      X := D.X
      O := fun χ => ⟨bundle I D e χ, ρ χ, DVR.linComb_isLB _ D.P.isLB _ _, hρ χ⟩
      addIso := bundle_add I D e
      zeroTriv := bundle_zero I D e
      primitive := bundle_primitive I D e }
  refine ⟨E, Iso.refl _, AddEquiv.refl _, inferInstanceAs (IsMonHom (𝟙 (thickObj R I e D.P.A))), fun χ => ?_, ?_⟩
  · refine exists_iso D.P.isLB (funext fun k => ?_) Oε
    refine Eq.trans ?_ (WeightPf.Oφ_comp ((Over.map (thick R I e)).map (𝟙 (thickObj R I e D.P.A)) ≫ D.prBe I e) (𝟙 _) χ k).symm
    rw [Category.comp_id]
    exact congrArg (D.Oφ · χ k) (((congrArg (· ≫ _) ((Over.map (thick R I e)).map_id _)).trans (Category.id_comp _)).symm)
  · exact isGt_of_units E g.q g.i g.q_hom g.i_hom g.q_flat g.q_surj g.q_affine g.isKernel (coordUnit g)
      (coordUnit_trans g) (coordUnit_weight g) hρ'
end GlobalTheory
