-- Prove2me | solution 1 for GlobalTheory.WeightGen.HasGen.exists_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:30:25.461808+00:00
-- url     : https://prove2.me/submissions/b7c526d1-30ed-4775-9448-e52c38c84e82

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyGtCoordOfIsGt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


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
open GlobalTheory GlobalTheory.WeightGen
variable {P G B : Scheme.{0}} (q : G ⟶ B) (a p : P ⟶ G)
variable {q a p}
namespace GlobalTheory.WeightGen
namespace HasGen
theorem _root_.solution {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
    {φ : K → (B ⟶ X)} {ε : K → ℤ} {c : GermFn P} (h : a ≫ q = p ≫ q)
    (H : HasGen q a p (LB.LinComb L φ ε) c) (φ' : K → (G ⟶ X)) (ε' : K → ℤ)
    (hφ : ∀ k, φ' k = q ≫ φ k) (hε : ∀ k, ε' k = -ε k) (hL : L.IsLB) :
    ∃ t : LB.Gen (LB.LinComb L φ' ε'), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ P) (z : Z) (J),
      Good L z J → val t (r ≫ a) z J = c Z r z * val t (r ≫ p) z J := by
  obtain rfl : φ' = fun k => q ≫ φ k := funext hφ
  obtain rfl : ε' = fun k => -ε k := funext hε
  obtain ⟨s, s₁, s₂⟩ := H
  have le : ∀ j : K → L.ι, LB.wchart L (fun k => q ≫ φ k) j ≤ q ⁻¹ᵁ LB.wchart L φ j :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  refine ⟨⟨fun j => res (le j) (s j)⟩, fun j j' => unit_ext fun y hy => ?_, fun Z r z J hJ => ?_⟩
  · refine ((gm_res _ y _ hy _).trans (gm_res (𝟙 G) y (le j) hy.1 _)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) (gm_linComb L _ _ (𝟙 G) y j j' hy.1 hy.2)
        ((gm_res _ y _ hy _).trans (gm_res (𝟙 G) y (le j') hy.2 _)))).symm)
    have e := (s₁ _ (𝟙 G) y j j' (le j hy.1) (le j' hy.2)).trans (congrArg (· * _)
      (gm_linComb L φ ε (𝟙 G ≫ q) y j j' (le j hy.1) (le j' hy.2)))
    refine (inv_mul_cancel_left _ _).symm.trans (congrArg₂ (· * ·) ?_ e.symm)
    refine (DVR.prod_neg _ _ ?_).symm
    simp only [Category.assoc]
  · have m := hJ.mem (fun k => q ≫ φ k) (r ≫ p)
    have m' := hJ.mem (fun k => q ≫ φ k) (r ≫ a)
    have e : ∀ k, J ((r ≫ a) ≫ q ≫ φ k) = J ((r ≫ p) ≫ q ≫ φ k) := fun k => by
      rw [Category.assoc, Category.assoc, reassoc_of% h]
    rw [funext e] at m'
    rw [val_of _ (r ≫ a) z J _ e]
    exact (gm_res _ z (le _) m' _).trans ((s₂ Z r z _ (le _ m)).trans
      (congrArg _ (gm_res _ z (le _) m _).symm))
end HasGen
end GlobalTheory.WeightGen
