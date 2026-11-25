-- Prove2me | solution 1 for GlobalTheory.Exist.CubicalExtension.pmaps_of_tri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:11:23.319218+00:00
-- url     : https://prove2.me/submissions/13a1d57f-b1c1-44bb-9799-d2a98a3f2b31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SabMapOfIsoOfExtendGen
import Theorems.Thm_GlobalTheory_Exist_CubicalExtension_unit_ext_of_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_pw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pt_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Exist GlobalTheory.Exist.CubicalExtension
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X X' X'' A : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}
namespace GlobalTheory.Exist.CubicalExtension
theorem _root_.solution {w : LB.Iso L' (L.pull F)} {w' : LB.Iso L'' (L'.pull F')} {w'' : LB.Iso L'' (L.pull (F' ≫ F))}
    {K : Type} [Fintype K] {Y Y' Y'' : Scheme.{0}} {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X')} {φ'' : K → (Y'' ⟶ X'')}
    {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L' φ' ε)}
    {t'' : LB.Gen (LB.LinComb L'' φ'' ε)} {h : Y' ⟶ Y} {h' : Y'' ⟶ Y'} (T : Tri w w' w'') (hL'' : L''.IsLB)
    (hc : ∀ k, φ' k ≫ F = h ≫ φ k) (hc' : ∀ k, φ'' k ≫ F' = h' ≫ φ' k) (H' : PMaps w' φ'' φ' ε t'' t' h')
    (H'' : PMaps w'' φ'' φ ε t'' t (h' ≫ h)) (l : A ⟶ Y'') (hl : ∀ V, Function.Injective ((l ≫ h').app V)) :
    PMaps w φ' φ ε t' t h := by
  intro Z r z p q hp hq
  obtain ⟨u, hu⟩ := exists_pw w φ' ε p q
  have le : LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q ≤ h ⁻¹ᵁ LB.wchart L φ p := fun y hy =>
    Set.mem_iInter.2 fun k => by
      show φ k (h y) ∈ L.U (p k)
      rw [pt_eq hc]; exact Set.mem_iInter.1 hy.1 k
  have v₁ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z), r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
      gm r z _ (res le (pullU h _ (t.s p))) = gm (r ≫ h) z (LB.wchart L φ p) (t.s p) := fun Z r z hz =>
    (gm_res r z le hz _).trans (gm_pull r h z _ (le hz) _)
  have v₂ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z), r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
      gm r z _ (u * res inf_le_right (t'.s q)) = pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (t'.s q) :=
    fun Z r z hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) (hu Z r z hz) (gm_res r z _ hz _))
  have e : res le (pullU h _ (t.s p)) = u * res inf_le_right (t'.s q) :=
    unit_ext_of_injective (l ≫ h') (hl _) fun y hy => by
      choose k hk using fun k => exists_chart hL'' (φ'' k (l y))
      have a₁ : ∀ k, F (F' (φ'' k (l y))) ∈ L.U (p k) := fun k => by
        rw [← pt_eq hc']; exact Set.mem_iInter.1 hy.1 k
      have a₂ : ∀ k, F' (φ'' k (l y)) ∈ L'.U (q k) := fun k => by
        rw [← pt_eq hc']; exact Set.mem_iInter.1 hy.2 k
      rw [v₁ _ _ _ hy, v₂ _ _ _ hy, Category.assoc, H'' _ l y p k a₁ hk, H' _ l y q k a₂ hk,
        T.prod hc' _ l y p q k a₁ a₂ hk, _root_.mul_assoc]
      rfl
  have hz : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q :=
    ⟨Set.mem_iInter.2 hp, Set.mem_iInter.2 hq⟩
  exact (v₁ Z r z hz).symm.trans ((congrArg (gm r z _) e).trans (v₂ Z r z hz))
end GlobalTheory.Exist.CubicalExtension
