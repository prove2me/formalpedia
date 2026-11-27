-- Prove2me | solution 1 for GlobalTheory.UU.polarisation_extends
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:36:03.766527+00:00
-- url     : https://prove2.me/submissions/0cb5902a-a80f-4847-b192-c18a8eec8ca0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenOfChartPull
import Theorems.Thm_GlobalTheory_UU_exists_gen_of_chartPull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pull_isLB


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory GlobalTheory.UU
namespace GlobalTheory.UU
theorem _root_.solution : Laws → (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (gen : (Over.pullback (jK V)).obj G ≅ A.A), IsMonHom gen.hom → ∃ L : RigLB G, LBIso (A.L.pull gen.hom.left) (L.L.pull (pullback.fst G.hom (jK V)))) := by
  intro hL V _ _ _ A G _ _ hG gen hgen
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have := hG.geomConnected
  obtain ⟨t, ht⟩ := A.rigid
  have e₁ : eSec ((Over.pullback (jK V)).obj G) ≫ gen.hom.left = eSec A.A := by
    unfold eSec
    rw [← Over.comp_left, IsMonHom.one_hom]
  have e₂ : eSec ((Over.pullback (jK V)).obj G) ≫ jA V (FractionRing V) G = eK V (FractionRing V) G := by
    unfold eSec eK eSec
    simp
    rw [pullback.lift_fst, ← Category.assoc, ← pullback.condition, Category.comp_id]
  obtain ⟨ρ, hρ⟩ := exists_gen_of_chartPull
    (chartPullLinComb A.L gen.hom.left (K := PUnit) (fun _ => eSec ((Over.pullback (jK V)).obj G))
      (fun _ => eSec A.A) (fun _ => 1) (𝟙 _) (fun _ => e₁.trans (Category.id_comp _).symm)) t ht
  obtain ⟨L, φ, hφ⟩ := hL.extend V (FractionRing V) G _ e₂ (A.L.pull gen.hom.left) (pull_isLB A.isLB _) ρ hρ
  exact ⟨L, LBIso.symm ⟨φ, hφ⟩⟩
end GlobalTheory.UU
