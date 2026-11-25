-- Prove2me | solution 1 for GlobalTheory.UT.SymFrame.grep_kap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:10:00.115856+00:00
-- url     : https://prove2.me/submissions/1bebfc0f-1c05-41a1-bb4e-c6085a63440c

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
theorem _root_.solution {n : ℕ} (κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1)) (hκ : κ.IsGen) (x : Y ⟶ D.P.A) :
    GRep D.P.L Y (fun _ _ h => h x.left ^ ((n : ℤ) ^ 2) * (h (x ^ n).left)⁻¹ * h (1 : Y ⟶ D.P.A).left ^ (1 - (n : ℤ) ^ 2))
      (fun _ r z J => val κ (r ≫ x).left z J) :=
  (grep_gen κ hκ x.left).congr (fun _ _ h => by
    rw [Fin.prod_univ_three]
    show h (x.left ≫ 𝟙 _) ^ ((n ^ 2 : ℕ) : ℤ) * h (x.left ≫ (𝟙 D.P.A ^ n).left) ^ (-((1 : ℕ) : ℤ)) *
      h (x.left ≫ (1 : D.P.A ⟶ D.P.A).left) ^ (((1 : ℕ) : ℤ) - ((n ^ 2 : ℕ) : ℤ)) = _
    rw [Category.comp_id, left_pow, left_one, Nat.cast_pow, Nat.cast_one, zpow_neg_one]) (fun _ _ _ _ _ => rfl)
end GlobalTheory.UT.SymFrame
