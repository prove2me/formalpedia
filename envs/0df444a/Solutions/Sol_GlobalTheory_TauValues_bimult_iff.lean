-- Prove2me | solution 1 for GlobalTheory.TauValues.bimult_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:48:02.066475+00:00
-- url     : https://prove2.me/submissions/1aa4a8ac-5f5a-4d78-b609-2536d539e9d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CorrOfValFieldExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultPsiEvenOverExtensionField
import Theorems.Thm_GlobalTheory_TauValues_val_tau
import Theorems.Thm_GlobalTheory_TauValues_comp_cT
import Theorems.Thm_GlobalTheory_TauValues_val_rigK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory GlobalTheory.TauValues
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
namespace GlobalTheory.TauValues
theorem _root_.solution {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) {z : T.left} {J} (hJ : Good D.P.L z J)
    (a b m : D.X) :
    val (D.psi (a + b + m)) κ.left z J * val (D.psi a) κ.left z J * val (D.psi b) κ.left z J *
        val (D.psi m) κ.left z J * rigV D z J * cubV D.cub z J (cT D T a) (cT D T b) (cT D T m) =
      val (D.psi (a + b)) κ.left z J * val (D.psi (a + m)) κ.left z J * val (D.psi (b + m)) κ.left z J ↔
    val (LB.mulGen D.P.L _ _ _ _ (D.tau (a + b) m)
        (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a b m))) κ.left z J =
      val (LB.mulGen D.P.L _ _ _ _ (D.tau a m) (D.tau b m)) κ.left z J := by
  have c : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a b m)) κ.left z J =
      cubV D.cub z J (cT D T a) (cT D T b) (cT D T m) := by
    refine (val_cub D.cub κ hJ (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b) (toUnit (TK R) ≫ D.c m)).trans ?_
    rw [comp_cT, comp_cT, comp_cT]
  have l := (val_mul hJ (D.tau (a + b) m)
    (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (D.pt3 a b m)) κ.left).trans
    (congrArg₂ (· * ·) (val_tau D κ.left hJ _ _) c)
  have r := (val_mul hJ (D.tau a m) (D.tau b m) κ.left).trans
    (congrArg₂ (· * ·) (val_tau D κ.left hJ _ _) (val_tau D κ.left hJ _ _))
  rw [val_rigK D κ hJ] at l r
  rw [l, r]
  constructor <;> intro h <;> apply Additive.ofMul.injective <;> have e := congrArg Additive.ofMul h <;>
    simp only [ofMul_mul, ofMul_inv] at e ⊢ <;> linear_combination (norm := abel) e
end GlobalTheory.TauValues
