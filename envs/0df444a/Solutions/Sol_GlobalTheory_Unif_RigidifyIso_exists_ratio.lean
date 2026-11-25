-- Prove2me | solution 1 for GlobalTheory.Unif.RigidifyIso.exists_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:57:28.064067+00:00
-- url     : https://prove2.me/submissions/5bda9f12-627f-47f2-9214-804d16cbf0f5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsRigidifiedIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_pw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_glue_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pw_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Unif GlobalTheory.Unif.RigidifyIso
open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.Unif.RigidifyIso
theorem _root_.solution {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (f : Y' ⟶ Y) (hφ : ∀ k, φ' k ≫ F = f ≫ φ k) (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ c : Γ(Y', ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
      gm (r ≫ f) z (LB.wchart L φ p) (t.s p) =
        gm r z ⊤ c * (pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q)) := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have le : ∀ p, LB.wchart L (fun k => φ' k ≫ F) p ≤ f ⁻¹ᵁ LB.wchart L φ p := fun p y hy =>
    Set.mem_iInter.2 fun k => (congrArg (fun g : Y' ⟶ X => g y ∈ L.U (p k)) (hφ k)).mp (Set.mem_iInter.1 hy k)
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) p q,
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
      gm r z _ (res (inf_le_left.trans (le p)) (pullU f _ (t.s p)) * (u p q * res inf_le_right (a.s q))⁻¹) =
        gm (r ≫ f) z (LB.wchart L φ p) (t.s p) * (pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q))⁻¹ :=
    fun Z r z p q hz => (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res r z _ hz _).trans (gm_pull r f z _ (le p hz.1) _))
      ((map_inv _ _).trans (congrArg (·⁻¹) ((map_mul _ _ _).trans
        (congrArg₂ (· * ·) (hu p q Z r z hz) (gm_res r z _ hz _))))))
  obtain ⟨c, hc⟩ := glue_unit (⊤ : Y'.Opens)
    (fun i : (K → L.ι) × (K → L'.ι) => LB.wchart L (fun k => φ' k ≫ F) i.1 ⊓ LB.wchart L' φ' i.2) (fun _ => le_top)
    (fun y _ => by
      choose p hp using fun k => exists_chart hL (F (φ' k y))
      choose q hq using fun k => exists_chart hL' (φ' k y)
      exact Opens.mem_iSup.2 ⟨(p, q), Set.mem_iInter.2 hp, Set.mem_iInter.2 hq⟩)
    (fun i => res (inf_le_left.trans (le i.1)) (pullU f _ (t.s i.1)) * (u i.1 i.2 * res inf_le_right (a.s i.2))⁻¹)
    (fun i i' y hy => by
      have e : trF φ ε (𝟙 Y' ≫ f) y i.1 i'.1 = trF (fun k => φ' k ≫ F) ε (𝟙 Y') y i.1 i'.1 := by
        simp only [trF, hφ, Category.assoc]
      rw [hv _ _ y _ _ hy.1, hv _ _ y _ _ hy.2, pw_trans hw φ' ε (𝟙 Y') y hy.1.1 hy.2.1 hy.1.2 hy.2.2,
        gen_trans ha (𝟙 Y') y hy.1.2 hy.2.2, gen_trans ht (𝟙 Y' ≫ f) y (le _ hy.1.1) (le _ hy.2.1), e]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  refine ⟨c, fun Z r z p q h₁ h₂ => ?_⟩
  have hz : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
  have e := (gm_res r z le_top hz c).symm.trans ((congrArg (gm r z _) (hc (p, q))).trans (hv Z r z p q hz))
  rw [e, inv_mul_cancel_right]
end GlobalTheory.Unif.RigidifyIso
