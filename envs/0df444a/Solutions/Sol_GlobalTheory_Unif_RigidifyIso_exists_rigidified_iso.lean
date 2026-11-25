-- Prove2me | solution 1 for GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:35:23.840936+00:00
-- url     : https://prove2.me/submissions/91a8901b-d5ad-4cfd-8ccd-a1a8dbfeefc7

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
import Theorems.Thm_GlobalTheory_Unif_RigidifyIso_exists_ratio
import Theorems.Thm_GlobalTheory_Unif_RigidifyIso_exists_scaled
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_maps_iff


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
theorem _root_.solution : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (Ψ : G'.left ⟶ G.left) (he : eSec G' ≫ Ψ = f ≫ eSec G) (L : RigLB G) (L' : RigLB G'), (∃ w : LB.Iso L'.L (L.L.pull Ψ), w.IsGen) → ∃ w : LB.Iso L'.L (L.L.pull Ψ), w.IsGen ∧ LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig (rigPullOf Ψ f he L.L L.rig) := by
  rintro S S' f G _ _ G' _ _ Ψ he L L' ⟨w, hw⟩
  have hw := (isGen_iff w).1 hw
  obtain ⟨c, hc⟩ := exists_ratio (K := PUnit) (φ' := fun _ => eSec G') (φ := fun _ => eSec G) (ε := fun _ => 1)
    hw L.isLB L'.isLB f (fun _ => he) L'.rig L'.rigGen L.rig L.rigGen
  obtain ⟨w', hw'⟩ := exists_scaled (B := (𝟙_ (Over S')).left) w G'.hom c
  have hs : eSec G' ≫ (show G'.left ⟶ (𝟙_ (Over S')).left from G'.hom) = 𝟙 _ := Over.w η[G']
  refine ⟨w', (isGen_iff w').2 fun Y r y j j' k k' hj hj' hk hk' => ?_,
    (maps_iff w' _ (fun _ => eSec G) _ L'.rig L.rig f _ (rigPull_le Ψ f he L.L) (fun _ => rfl)).2
      fun Z r z p q hp hq => ?_⟩
  · rw [hw' Y r y j k hj hk, hw' Y r y j' k' hj' hk', hw Y r y j j' k k' hj hj' hk hk', mul_left_comm]
  · refine (hc Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)).trans ?_
    rw [← _root_.mul_assoc]
    refine congrArg₂ (· * ·) ?_ rfl
    rw [pw, Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one,
      hw' Z (r ≫ eSec G') z _ _ (hp _) (hq _), Category.assoc]
    exact congrArg (fun g => gm g z ⊤ c * _) ((congrArg (r ≫ ·) hs).trans (Category.comp_id r)).symm
end GlobalTheory.Unif.RigidifyIso
