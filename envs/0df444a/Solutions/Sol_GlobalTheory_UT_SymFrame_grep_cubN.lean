-- Prove2me | solution 1 for GlobalTheory.UT.SymFrame.grep_cubN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:50:39.154087+00:00
-- url     : https://prove2.me/submissions/ef1e9a75-7551-4674-9472-96e9f7ccd178

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UnivIdentity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_cubN


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
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {Y : Over (Spec (CommRingCat.of R))}
namespace GlobalTheory.UT.SymFrame
theorem _root_.solution (m x : Y ⟶ D.P.A) (k : ℕ) :
    GRep D.P.L Y (fun _ _ h => h (m ^ k * x).left * (h (m ^ k).left)⁻¹ * (h x.left)⁻¹ * h (1 : Y ⟶ D.P.A).left *
        (h (m * x).left ^ k)⁻¹ * h m.left ^ k * h x.left ^ k * (h (1 : Y ⟶ D.P.A).left ^ k)⁻¹)
      (fun _ r z J => cubN (cubV D.cub z J) k 1 (r ≫ m) (r ≫ x)) := by
  obtain ⟨t, ht, vt⟩ := exists_cubN D.cub 1 m x k
  refine ⟨_, inferInstance, _, _, t, ht, fun U _ h => ?_, fun T r z J hJ => ?_⟩
  · rw [Fin.prod_univ_eight]
    simp
  · rw [vt T r z J hJ, MonObj.comp_one]
end GlobalTheory.UT.SymFrame
