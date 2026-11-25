-- Prove2me | solution 1 for GlobalTheory.UT.SymFrame.GRep.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:59:14.877537+00:00
-- url     : https://prove2.me/submissions/68c9e2c2-3d7f-4c06-931d-fd13c03b621c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UnivIdentity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_powGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.SymFrame
variable {S X : Scheme.{0}} (L : LB X) (Y : Over S)
variable {L Y}
namespace GlobalTheory.UT.SymFrame
namespace GRep
theorem _root_.solution {P v} (h : GRep L Y P v) (n : ℕ) :
    GRep L Y (fun U _ h => P U h ^ n) (fun T r z J => v T r z J ^ n) := by
  obtain ⟨K, _, φ, ε, s, hs, hP, hv⟩ := h
  refine ⟨K, inferInstance, _, _, GeneratorPullback.powGen L _ _ s n, powGen_isGen _ _ _ _ hs n,
    fun U _ h => ?_, fun T r z J hJ => (map_pow _ _ _).trans (congrArg (· ^ n) (hv T r z J hJ))⟩
  show _ = P U h ^ n
  rw [← hP U h, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun k _ => by rw [mul_comm, zpow_mul, zpow_natCast]
end GRep
end GlobalTheory.UT.SymFrame
