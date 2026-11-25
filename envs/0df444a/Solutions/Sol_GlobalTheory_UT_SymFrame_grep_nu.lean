-- Prove2me | solution 1 for GlobalTheory.UT.SymFrame.grep_nu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:10:00.133824+00:00
-- url     : https://prove2.me/submissions/1339d882-81df-4428-b52d-a4de728fd4d9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UnivIdentity
import Theorems.Thm_GlobalTheory_UT_SymFrame_GRep_congr
import Theorems.Thm_GlobalTheory_UT_SymFrame_grep_gen
import Theorems.Thm_GlobalTheory_UT_SymFrame_left_pow
import Theorems.Thm_GlobalTheory_UT_SymFrame_left_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


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
theorem _root_.solution {n : ℕ} (ν : LB.Gen (nuLB D n)) (hν : ν.IsGen) (x : Y ⟶ D.P.A) :
    GRep D.P.L Y (fun _ _ h => h (x ^ n * x).left * (h (x ^ n).left)⁻¹ * h x.left ^ (-(2 * (n : ℤ) + 1)) *
      h (1 : Y ⟶ D.P.A).left ^ (2 * (n : ℤ) + 1)) (fun _ r z J => val ν (r ≫ x).left z J) :=
  (grep_gen ν hν x.left).congr (fun _ _ h => by
    rw [Fin.prod_univ_four]
    show h (x.left ≫ (𝟙 D.P.A ^ (n + 1)).left) ^ (1 : ℤ) * h (x.left ≫ (𝟙 D.P.A ^ n).left) ^ (-1 : ℤ) *
      h (x.left ≫ 𝟙 _) ^ (-(2 * (n : ℤ) + 1)) * h (x.left ≫ (1 : D.P.A ⟶ D.P.A).left) ^ (2 * (n : ℤ) + 1) = _
    rw [Category.comp_id, left_pow, left_pow, left_one, zpow_neg_one, zpow_one, pow_succ]) (fun _ _ _ _ _ => rfl)
end GlobalTheory.UT.SymFrame
