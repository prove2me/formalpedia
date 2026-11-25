-- Prove2me | solution 1 for GlobalTheory.UT.SymFrame.exists_kap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:45:44.495583+00:00
-- url     : https://prove2.me/submissions/7917488d-af66-482a-9c39-8a703c197092

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UnivIdentity
import Theorems.Thm_GlobalTheory_UT_SymFrame_GRep_mul
import Theorems.Thm_GlobalTheory_UT_SymFrame_GRep_inv
import Theorems.Thm_GlobalTheory_UT_SymFrame_GRep_congr
import Theorems.Thm_GlobalTheory_UT_SymFrame_grep_gen
import Theorems.Thm_GlobalTheory_UT_SymFrame_GRep_normd
import Theorems.Thm_GlobalTheory_UT_SymFrame_left_pow
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
theorem _root_.solution [IsNoetherianRing R] (hM : MulPullSt) (n : ℕ) :
    ∃ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1), Normd κ := by
  obtain ⟨α, hα⟩ := hM _ D.P n
  have ra : ∀ x : D.P.A ⟶ D.P.A, GRep D.P.L D.P.A (fun _ _ h => h x.left ^ ((n : ℤ) ^ 2) * (h (x ^ n).left)⁻¹)
      (fun _ r z J => val α (r ≫ x).left z J) := fun x => (grep_gen α hα x.left).congr (fun _ _ h => by
    rw [Fin.prod_univ_two]
    show h (x.left ≫ 𝟙 _) ^ ((n : ℤ) ^ 2) * h (x.left ≫ (𝟙 D.P.A ^ n).left) ^ (-1 : ℤ) = _
    rw [Category.comp_id, left_pow, zpow_neg_one]) (fun _ _ _ _ _ => rfl)
  obtain ⟨s, hs, -⟩ := ((ra (𝟙 _)).mul (ra 1).inv).normd
    ![𝟙 _, (𝟙 D.P.A ^ n).left, (1 : D.P.A ⟶ D.P.A).left] ![((n ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ) - ((n ^ 2 : ℕ) : ℤ)]
    (fun U _ h => by
      rw [Fin.prod_univ_three, one_pow]
      apply Additive.ofMul.injective
      simp [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (fun y J hJ => by
      beta_reduce
      rw [Category.comp_id, MonObj.comp_one, mul_inv_cancel])
  exact ⟨s, hs⟩
end GlobalTheory.UT.SymFrame
