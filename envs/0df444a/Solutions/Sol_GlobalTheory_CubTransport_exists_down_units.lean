-- Prove2me | solution 1 for GlobalTheory.CubTransport.exists_down_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:36:54.37479+00:00
-- url     : https://prove2.me/submissions/eaf5ea0d-2fdb-4edf-b732-719ac067e391

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubicalSymmetryTransport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_pw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_glue_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_of_gm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pw_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_trF_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CubTransport
open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
namespace GlobalTheory.CubTransport
theorem _root_.solution {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y ⟶ X')} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
        r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
        gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) =
          pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have glue : ∀ q : K → L'.ι, ∃ s : Γ(Y, LB.wchart L' φ' q)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p,
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
      gm r z _ s = (pw w φ' ε r z p q)⁻¹ * gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) := by
    intro q
    have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p,
        r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
        gm r z _ ((u p q)⁻¹ * res inf_le_left (t.s p)) =
          (pw w φ' ε r z p q)⁻¹ * gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) :=
      fun Z r z p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans
        (congrArg (·⁻¹) (hu p q _ _ z hz))) (gm_res _ z _ hz _))
    obtain ⟨s, hs⟩ := glue_unit _ (fun p => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q)
      (fun _ => inf_le_right)
      (fun y hy => by
        choose p hp using fun k => exists_chart hL (F (φ' k y))
        exact Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp, hy⟩) (fun p => (u p q)⁻¹ * res inf_le_left (t.s p))
      (fun p p' y hy => by
        rw [hv _ _ y p hy.1, hv _ _ y p' hy.2, pw_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.2.1 hy.1.2 hy.1.2,
          trF_self hL' _ ε (𝟙 Y) y hy.1.2, gen_trans ht (𝟙 Y) y hy.1.1 hy.2.1, inv_one, _root_.mul_one, mul_inv,
          _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun Z r z p h₁ h₂ => ?_⟩
    have hz : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
    exact (gm_res _ z inf_le_right hz s).symm.trans ((congrArg (gm _ z _) (hs p)).trans (hv Z r z p hz))
  choose s hs using glue
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_, fun Z r z p q h₁ h₂ => ?_⟩
  · choose p hp using fun k => exists_chart hL (F (φ' k y))
    have m : y ∈ LB.wchart L (fun k => φ' k ≫ F) p := Set.mem_iInter.2 hp
    refine (hs j _ (𝟙 Y) y p m hj).trans (Eq.trans ?_ (congrArg _ (hs j' _ (𝟙 Y) y p m hj')).symm)
    rw [pw_trans hw φ' ε (𝟙 Y) y m m hj hj', trF_self hL _ ε (𝟙 Y) y m, _root_.one_mul, mul_inv, inv_inv,
      _root_.mul_assoc]
  · exact (mul_inv_cancel_left _ _).symm.trans (congrArg (pw w φ' ε r z p q * ·) (hs q Z r z p h₁ h₂).symm)
end GlobalTheory.CubTransport
