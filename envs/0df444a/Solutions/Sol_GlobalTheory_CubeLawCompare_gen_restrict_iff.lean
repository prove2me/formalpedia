-- Prove2me | solution 1 for GlobalTheory.CubeLawCompare.gen_restrict_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:07.908955+00:00
-- url     : https://prove2.me/submissions/8dee783b-12b2-414e-9577-cf0acd503dbe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_RigidityTranslation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LocallyTrivialOfIsoPull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_ext_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CubeLawCompare
variable {Y T : Scheme.{0}}
namespace GlobalTheory.CubeLawCompare
theorem _root_.solution (M : LB Y) (W : Y.Opens) :
    (∃ c : LB.Gen (M.pull W.ι), c.IsGen) ↔ ∃ d, IsGenOn M W d := by
  constructor
  · rintro ⟨c, hc⟩
    choose b hb using fun j : M.ι =>
      exists_ext_unit W.ι ((M.pull W.ι).U fun _ => j) (c.s fun _ => j)
    have le : ∀ j, W ⊓ M.U j ≤ W.ι ''ᵁ ((M.pull W.ι).U fun _ => j) :=
      fun j y hy => ⟨⟨y, hy.1⟩, mem_pull.2 hy.2, rfl⟩
    refine ⟨fun j => res (le j) (b j), fun j j' y hW hj hj' => ?_⟩
    let z : W.toScheme := ⟨y, hW⟩
    have hz : W.ι z ∈ W ⊓ M.U j ⊓ M.U j' := ⟨⟨hW, hj⟩, hj'⟩
    have l₁ : W ⊓ M.U j ⊓ M.U j' ≤ W ⊓ M.U j := inf_le_left
    have l₂ : W ⊓ M.U j ⊓ M.U j' ≤ M.U j ⊓ M.U j' := fun _ h => ⟨h.1.2, h.2⟩
    have l₃ : W ⊓ M.U j ⊓ M.U j' ≤ W ⊓ M.U j' := fun _ h => ⟨h.1.1, h.2⟩
    have v : ∀ i (hi : y ∈ M.U i), gm W.ι z (W ⊓ M.U i) (res (le i) (b i)) =
        gm (𝟙 _) z ((M.pull W.ι).U fun _ => i) (c.s fun _ => i) := fun i hi => by
      have h := hb i _ (𝟙 _) z (mem_pull.2 hi)
      rw [Category.id_comp] at h
      exact (gm_res W.ι z (le i) ⟨hW, hi⟩ _).trans h
    have m : (𝟙 W.toScheme : _ ⟶ _) z ∈ ((M.pull W.ι).U fun _ => j) ⊓ ((M.pull W.ι).U fun _ => j') :=
      ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
    have e := (gm_res (𝟙 _) z _ m _).symm.trans ((congrArg (gm (𝟙 _) z _) (hc (fun _ => j) (fun _ => j'))).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull_g M W.ι (𝟙 _) z _ _ m.1 m.2) (gm_res (𝟙 _) z _ m _))))
    rw [Category.id_comp] at e
    have key := gm_inj W.ι z hz hz (a := res l₁ (res (le j) (b j)))
      (b := res l₂ (M.g j j') * res l₃ (res (le j') (b j'))) (by
        rw [map_mul, gm_res W.ι z l₁ hz, gm_res W.ι z l₂ hz, gm_res W.ι z l₃ hz, v j hj, v j' hj']
        exact e)
    rw [map_mul, gm_res (𝟙 Y) (W.ι z) l₁ hz, gm_res (𝟙 Y) (W.ι z) l₂ hz, gm_res (𝟙 Y) (W.ι z) l₃ hz] at key
    exact key
  · rintro ⟨d, hd⟩
    have le : ∀ J : PUnit → M.ι, (M.pull W.ι).U J ≤ W.ι ⁻¹ᵁ (W ⊓ M.U (J PUnit.unit)) :=
      fun J z hz => ⟨z.2, mem_pull.1 hz⟩
    refine ⟨⟨fun J => res (le J) (pullU W.ι _ (d (J PUnit.unit)))⟩, fun J J' => ?_⟩
    have e : res (inf_le_left : W ⊓ M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit) ≤ _) (d (J PUnit.unit)) =
        res (show W ⊓ M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit) ≤
            M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit) from fun _ h => ⟨h.1.2, h.2⟩)
          (M.g (J PUnit.unit) (J' PUnit.unit)) *
        res (show W ⊓ M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit) ≤
            W ⊓ M.U (J' PUnit.unit) from fun _ h => ⟨h.1.1, h.2⟩)
          (d (J' PUnit.unit)) := unit_ext fun y hy => by
      rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy]
      exact hd _ _ y hy.1.1 hy.1.2 hy.2
    refine unit_ext fun z hz => ?_
    have hz' : W.ι z ∈ W ⊓ M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit) :=
      ⟨⟨z.2, mem_pull.1 hz.1⟩, mem_pull.1 hz.2⟩
    have e' := congrArg (gm W.ι z _) e
    rw [map_mul, gm_res _ z _ hz', gm_res _ z _ hz', gm_res _ z _ hz'] at e'
    have v : ∀ I : PUnit → M.ι, z ∈ (M.pull W.ι).U I →
        gm (𝟙 _) z ((M.pull W.ι).U I) (res (le I) (pullU W.ι _ (d (I PUnit.unit)))) =
          gm W.ι z (W ⊓ M.U (I PUnit.unit)) (d (I PUnit.unit)) := fun I hI =>
      (gm_res (𝟙 _) z (le I) hI _).trans ((gm_pull (𝟙 _) W.ι z _ (le I hI) _).trans
        (by rw [Category.id_comp]))
    refine ((gm_res (𝟙 _) z _ hz _).trans (v J hz.1)).trans (e'.trans (Eq.symm ?_))
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_pull_g M W.ι (𝟙 _) z J J' hz.1 hz.2).trans ?_)
      ((gm_res (𝟙 _) z _ hz _).trans (v J' hz.2)))
    rw [Category.id_comp]
end GlobalTheory.CubeLawCompare
