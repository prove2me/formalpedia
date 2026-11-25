-- Prove2me | solution 1 for GlobalTheory.RigidIsoCube.pmaps_of_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:47:46.794831+00:00
-- url     : https://prove2.me/submissions/f88dfcf4-d7a4-47ee-a273-74b881da675b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RigidifiedIsoRespectsCubeAndSymmetry
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_up
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gen_unique


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
open GlobalTheory GlobalTheory.RigidIsoCube
namespace GlobalTheory.RigidIsoCube
theorem _root_.solution {X X' Y S₀ : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y ⟶ X')}
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) (t : LB.Gen (LB.LinComb L φ ε))
    (ht : t.IsGen) (hψ : ∀ k, φ' k ≫ F = φ k) (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _)
    (hp : Function.Surjective p.appTop.hom)
    (h : ∀ (y : S₀) J J', Good L y J → Good L' y J' → val t e y J =
      (∏ k, gw w (e ≫ φ' k) y (J ((e ≫ φ' k) ≫ F)) (J' (e ≫ φ' k)) ^ ε k) * val a e y J') :
    PMaps w φ' φ ε a t (𝟙 Y) := by
  obtain rfl : φ = fun k => φ' k ≫ F := funext fun k => (hψ k).symm
  obtain ⟨t₁, ht₁, hv⟩ := exists_up hw hL hL' a ha
  have key := gen_unique hL p e he hp ht ht₁ (fun y J hJ => by
    choose J' hJ' using fun ψ : S₀ ⟶ X' => exists_chart hL' (ψ y)
    have v := hv _ e y _ _ (Good.mem hJ _ e) (Good.mem hJ' _ e)
    refine (h y J J' hJ hJ').trans (Eq.trans (congrArg₂ (· * ·) ?_ rfl) v.symm)
    simp only [pw, Category.assoc])
  intro Z r z i q hi hq
  rw [Category.comp_id]
  have hi' : r z ∈ LB.wchart L (fun k => φ' k ≫ F) i := Set.mem_iInter.2 hi
  choose J hJ using fun ψ : Z ⟶ X => exists_chart hL (ψ z)
  exact ((gen_trans ht r z hi' (Good.mem hJ _ r)).trans ((congrArg _ (key Z r z J hJ)).trans
    (gen_trans ht₁ r z hi' (Good.mem hJ _ r)).symm)).trans (hv Z r z i q hi' (Set.mem_iInter.2 hq))
end GlobalTheory.RigidIsoCube
