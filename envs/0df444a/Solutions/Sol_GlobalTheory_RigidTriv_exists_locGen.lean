-- Prove2me | solution 1 for GlobalTheory.RigidTriv.exists_locGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:56:36.550876+00:00
-- url     : https://prove2.me/submissions/87639d26-3a1c-4ce6-8fa9-e399368b1c60

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenOfRigid
import Theorems.Thm_GlobalTheory_RigidTriv_gm_stalk
import Theorems.Thm_GlobalTheory_RigidTriv_pull_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_ext_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
noncomputable section
namespace GlobalTheory.RigidTriv
variable {X Y Z : Scheme.{0}}
private lemma gm_id_val_eq_germ (W : Z.Opens) (z : Z) (hz : z ∈ W) (u : Γ(Z, W)ˣ) :
    Units.val (gm (𝟙 Z) z W u) = (Z.presheaf.germ W z hz).hom u.1 := by
  simp [gm, hz, pullU]
  rfl
private lemma gm_res_lemma_4 {U V : Y.Opens} (hVU : V ≤ U) (y : Y) (hy : y ∈ V) (a : Γ(Y, U)ˣ) :
    gm (𝟙 Y) y V (Units.map (Y.presheaf.map (homOfLE hVU).op).hom.toMonoidHom a) = gm (𝟙 Y) y U a := by
  ext1
  rw [gm_id_val_eq_germ V y hy, gm_id_val_eq_germ U y (hVU hy)]
  exact TopCat.Presheaf.germ_res_apply ..
end GlobalTheory.RigidTriv
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
noncomputable section
open GlobalTheory GlobalTheory.RigidTriv
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.RigidTriv
theorem _root_.solution {N : LB Y} (W : Y.Opens) {t : (N.pull W.ι).Gen} (ht : t.IsGen) :
    ∃ s, LocGen N W s := by
  choose b hb using fun i => exists_ext_unit W.ι ((N.pull W.ι).U fun _ => i) (t.s fun _ => i)
  have hle : ∀ i, W ⊓ N.U i ≤ W.ι ''ᵁ ((N.pull W.ι).U fun _ => i) := fun i y hy =>
    (Scheme.Opens.mem_ι_image_iff (x := ⟨y, hy.1⟩)).2 (Set.mem_iInter.2 fun _ => hy.2)
  have key : ∀ (y : Y) (hyW : y ∈ W) (i j : N.ι) (hi : y ∈ N.U i) (hj : y ∈ N.U j),
      gm (𝟙 Y) y _ (b i) = gm (𝟙 Y) y (N.U i ⊓ N.U j) (N.g i j) * gm (𝟙 Y) y _ (b j) := by
    intro y hyW i j hi hj
    obtain ⟨z0, rfl⟩ : ∃ z0 : W.toScheme, W.ι z0 = y := ⟨⟨y, hyW⟩, rfl⟩
    have hz0i : z0 ∈ (N.pull W.ι).U fun _ => i := Set.mem_iInter.2 fun _ => hi
    have hz0j : z0 ∈ (N.pull W.ι).U fun _ => j := Set.mem_iInter.2 fun _ => hj
    have P := pull_gen ht z0 i j hi hj
    rw [← hb i W.toScheme (𝟙 _) z0 hz0i, ← hb j W.toScheme (𝟙 _) z0 hz0j, Category.id_comp,
      gm_stalk W.ι z0 _ (hle i ⟨hyW, hi⟩), gm_stalk W.ι z0 _ (hle j ⟨hyW, hj⟩),
      gm_stalk W.ι z0 _ (show W.ι z0 ∈ N.U i ⊓ N.U j from ⟨hi, hj⟩), ← map_mul] at P
    exact Units.map_injective (fun a c h => (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap z0)).1 h) P
  refine ⟨fun i => Units.map (Y.presheaf.map (homOfLE (hle i)).op).hom.toMonoidHom (b i), ?_⟩
  intro Z f z i j hW hi hj
  rw [gm_stalk f z _ (show f z ∈ W ⊓ N.U i from ⟨hW, hi⟩), gm_stalk f z _ (show f z ∈ N.U i ⊓ N.U j from ⟨hi, hj⟩),
    gm_stalk f z _ (show f z ∈ W ⊓ N.U j from ⟨hW, hj⟩), ← map_mul, gm_res_lemma_4 (hle i) _ ⟨hW, hi⟩,
    gm_res_lemma_4 (hle j) _ ⟨hW, hj⟩, key (f z) hW i j hi hj]
end GlobalTheory.RigidTriv
