-- Prove2me | solution 1 for GlobalTheory.GenIsoRatio.ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:27:06.655545+00:00
-- url     : https://prove2.me/submissions/41dc94ac-2422-46e4-aee2-60f0eac9e5a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RigidifiedPartialLineBundleIsoCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlobalUnitRatioGenericLineBundleIsos
import Theorems.Thm_GlobalTheory_GenIsoRatio_gm_pullU_res
import Theorems.Thm_P2M_GlobalTheory_GenIsoRatio_gm_pull_g__f1a988516116
import Theorems.Thm_GlobalTheory_PartialCocycle_gm_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_glue_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.GenIsoRatio
namespace GlobalTheory.GenIsoRatio
theorem _root_.solution : ∀ (X Y : Scheme.{0}) (β : Y ⟶ X) (P M : LB X) (N : LB Y), P.IsLB → M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull β) N) (w₁ : LB.Iso (P.pull β) N) (v : LB.Iso P M), w.IsGen → w₁.IsGen → v.IsGen → ∃ u : Γ(Y, ⊤)ˣ, ∀ (n : N.ι) (i : P.ι) (m : M.ι) (hle : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ β ⁻¹ᵁ (M.U m ⊓ P.U i)), GlobalTheory.AbLaw.rs _ (inf_le_left : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ N.U n ⊓ (P.pull β).U (fun _ => i)) (w₁.s (n, fun _ => i)).val = GlobalTheory.AbLaw.rs _ (le_top : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ ⊤) (u : Γ(Y, ⊤)) * (β.appLE (M.U m ⊓ P.U i) _ hle).hom (v.s (m, i)).val * GlobalTheory.AbLaw.rs _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right : N.U n ⊓ (P.pull β).U (fun _ => i) ⊓ (M.pull β).U (fun _ => m) ≤ N.U n ⊓ (M.pull β).U (fun _ => m)) (w.s (n, fun _ => m)).val := by
  intro X Y β P M N hP hM hN w w₁ v hw hw₁ hv
  let W : N.ι × P.ι × M.ι → Y.Opens := fun j =>
    N.U j.1 ⊓ (P.pull β).U (fun _ => j.2.1) ⊓ (M.pull β).U (fun _ => j.2.2)
  have l₁ : ∀ j, W j ≤ N.U j.1 ⊓ (P.pull β).U (fun _ => j.2.1) := fun j => inf_le_left
  have l₂ : ∀ j, W j ≤ N.U j.1 ⊓ (M.pull β).U (fun _ => j.2.2) := fun j =>
    le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have l₃ : ∀ j, W j ≤ β ⁻¹ᵁ (M.U j.2.2 ⊓ P.U j.2.1) := fun j y hy =>
    ⟨mem_pull.1 hy.2, mem_pull.1 hy.1.2⟩
  let r : ∀ j, Γ(Y, W j)ˣ := fun j =>
    res (l₁ j) (w₁.s (j.1, fun _ => j.2.1)) * (res (l₃ j) (pullU β _ (v.s (j.2.2, j.2.1))))⁻¹ *
      (res (l₂ j) (w.s (j.1, fun _ => j.2.2)))⁻¹
  have k : ∀ j (y : Y), y ∈ W j → gm (𝟙 Y) y (W j) (r j) =
      gm (𝟙 Y) y (N.U j.1 ⊓ (P.pull β).U (fun _ => j.2.1)) (w₁.s (j.1, fun _ => j.2.1)) *
        (gm β y (M.U j.2.2 ⊓ P.U j.2.1) (v.s (j.2.2, j.2.1)))⁻¹ *
        (gm (𝟙 Y) y (N.U j.1 ⊓ (M.pull β).U (fun _ => j.2.2)) (w.s (j.1, fun _ => j.2.2)))⁻¹ := by
    intro j y hy
    simp only [r, map_mul, map_inv]
    erw [gm_res (𝟙 Y) y (l₁ j) hy, gm_res (𝟙 Y) y (l₂ j) hy, gm_pullU_res β _ (l₃ j) y hy]
  obtain ⟨u, hu⟩ := glue_unit (⊤ : Y.Opens) W (fun _ => le_top)
    (fun y _ => by
      obtain ⟨n, hn⟩ := exists_chart hN y
      obtain ⟨i, hi⟩ := exists_chart hP (β y)
      obtain ⟨m, hm⟩ := exists_chart hM (β y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(n, i, m), ⟨hn, mem_pull.2 hi⟩, mem_pull.2 hm⟩) r
    (fun j j' y hy => by
      have hi := mem_pull.1 hy.1.1.2
      have hi' := mem_pull.1 hy.2.1.2
      have hm := mem_pull.1 hy.1.2
      have hm' := mem_pull.1 hy.2.2
      rw [k j y hy.1, k j' y hy.2,
        GlobalTheory.PartialCocycle.gm_iso hw₁ (𝟙 Y) y j.1 j'.1 (fun _ => j.2.1) (fun _ => j'.2.1) hy.1.1.1 hy.2.1.1
          hy.1.1.2 hy.2.1.2,
        GlobalTheory.PartialCocycle.gm_iso hw (𝟙 Y) y j.1 j'.1 (fun _ => j.2.2) (fun _ => j'.2.2) hy.1.1.1 hy.2.1.1
          hy.1.2 hy.2.2,
        GlobalTheory.PartialCocycle.gm_iso hv β y j.2.2 j'.2.2 j.2.1 j'.2.1 hm hm' hi hi',
        gm_pull_g' β P y _ _ hi hi', gm_pull_g' β M y _ _ hm hm']
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  refine ⟨u, fun n i m hle => ?_⟩
  have e : res (l₁ (n, i, m)) (w₁.s (n, fun _ => i)) =
      res (le_top : W (n, i, m) ≤ ⊤) u * res hle (pullU β _ (v.s (m, i))) * res (l₂ (n, i, m)) (w.s (n, fun _ => m)) := by
    change _ = _ * res (l₃ (n, i, m)) (pullU β _ (v.s (m, i))) * _
    rw [hu (n, i, m)]
    simp only [r]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  exact congrArg Units.val e
end GlobalTheory.GenIsoRatio
