-- Prove2me | solution 1 for GlobalTheory.ThetaSplit.exists_gen_lbPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:32:59.647028+00:00
-- url     : https://prove2.me/submissions/406f3949-c7c0-47bc-8a0f-5ecdb1f738cd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LbPowDescendsOfIsotropic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.ThetaSplit
variable {X Y : Scheme.{0}} {L : LB X}
namespace GlobalTheory.ThetaSplit
theorem _root_.solution (n : ℕ) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε ε' : K → ℤ}
    (hε : ∀ k, ε' k = n * ε k) (t : LB.Gen (LB.LinComb L φ ε')) (ht : t.IsGen) (b : Γ(Y, ⊤)ˣ) :
    ∃ t' : LB.Gen (LB.LinComb (lbPow L n) φ ε), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good (lbPow L n) z J →
        val t' r z J = val t r z (fun χ => J χ PUnit.unit) * gm r z ⊤ b := by
  have le : ∀ j : K → (lbPow L n).ι, LB.wchart (lbPow L n) φ j ≤ LB.wchart L φ (fun k => j k PUnit.unit) :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Set.mem_iInter.1 hy k) PUnit.unit
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → (lbPow L n).ι), r z ∈ LB.wchart (lbPow L n) φ j →
      gm r z (LB.wchart (lbPow L n) φ j) (res (le j) (t.s _) * res le_top b) =
        gm r z (LB.wchart L φ (fun k => j k PUnit.unit)) (t.s _) * gm r z ⊤ b := fun Z r z j hz =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hz _) (gm_res r z _ hz _))
  refine ⟨⟨fun j => res (le j) (t.s _) * res le_top b⟩, fun i j => unit_ext fun y hy => ?_,
    fun Z r z J hJ => key Z r z _ (hJ.mem φ r)⟩
  refine ((gm_res (𝟙 Y) y _ hy _).trans (key _ _ y i hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb (lbPow L n) φ ε (𝟙 Y) y i j hy.1 hy.2)
      ((gm_res (𝟙 Y) y _ hy _).trans (key _ _ y j hy.2)))).symm)
  rw [gen_trans ht (𝟙 Y) y (le i hy.1) (le j hy.2), _root_.mul_assoc]
  refine congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_)
  have e := gm_linComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => (n : ℤ)) (𝟙 Y ≫ φ k) y (i k) (j k)
    (Set.mem_iInter.1 hy.1 k) (Set.mem_iInter.1 hy.2 k)
  rw [Fintype.prod_unique, Category.comp_id] at e
  rw [hε, zpow_mul]
  exact congrArg (· ^ ε k) e.symm
end GlobalTheory.ThetaSplit
