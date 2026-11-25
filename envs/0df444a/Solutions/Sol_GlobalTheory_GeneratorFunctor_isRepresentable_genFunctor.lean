-- Prove2me | solution 1 for GlobalTheory.GeneratorFunctor.isRepresentable_genFunctor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:16:18.698709+00:00
-- url     : https://prove2.me/submissions/faf35552-1a92-417e-ba3b-74b3e427c5e3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InverseBundleGeneratorPointOfChartUnitsSections
import Theorems.Thm_GlobalTheory_GeneratorFunctor_isRepresentable_of_charts
import Theorems.Thm_GlobalTheory_GeneratorFunctor_exists_torus
import Theorems.Thm_GlobalTheory_GeneratorFunctor_Pt_congr
import Theorems.Thm_GlobalTheory_GeneratorFunctor_genFunctor_map
import Theorems.Thm_GlobalTheory_GeneratorFunctor_isSheaf_genFunctor
import Theorems.Thm_GlobalTheory_GeneratorFunctor_Pt_inverseBundleGeneratorPoint_ofChartUnits_sections
import Theorems.Thm_GlobalTheory_GeneratorFunctor_Pt_ext_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_mem_of_cover


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
open GlobalTheory
open GlobalTheory.GeneratorFunctor
open Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
variable {B : Scheme.{0}} {κ : Type} (N : κ → LB B)
variable {N}
namespace GlobalTheory.GeneratorFunctor
theorem _root_.solution [Fintype κ] (hN : ∀ k, (N k).IsLB) :
    (genFunctor N).IsRepresentable := by
  let U : (∀ k, (N k).ι) → B.Opens := fun j =>
    ⟨⋂ k, ((N k).U (j k) : Set B), isOpen_iInter_of_finite fun k => ((N k).U (j k)).isOpen⟩
  have hU : ∀ j k, U j ≤ (N k).U (j k) := fun j k _ hy => Set.mem_iInter.1 hy k
  choose T p t hex hun using fun j => exists_torus (U j).toScheme κ
  have hb : ∀ j k, ⊤ ≤ (p j ≫ (U j).ι) ⁻¹ᵁ (N k).U (j k) := fun j k z _ =>
    hU j k (p j z).2
  let x : ∀ j, Pt N (T j) := fun j => Pt.ofChart hN (p j ≫ (U j).ι) j (hb j) (t j)
  have hx : ∀ j (Z : Scheme.{0}) (g : Z ⟶ T j) k,
      ⊤ ≤ 𝟙 Z ⁻¹ᵁ (Pt.map g (x j)).b ⁻¹ᵁ (N k).U (j k) := fun j Z g k z _ =>
    hU j k (p j (g z)).2
  have hxs : ∀ j (Z : Scheme.{0}) (g : Z ⟶ T j) k,
      (pb (𝟙 Z) _ ⊤ (hx j Z g k) ((Pt.map g (x j)).s k (j k))).val =
        g.appTop.hom (t j k).val := fun j Z g k =>
    (congrArg Units.val (pb_id_comp _ _ _ _ _ _ _)).trans (Pt.inverseBundleGeneratorPoint_ofChartUnits_sections hN _ j (hb j) (t j) k g _)
  refine isRepresentable_of_charts (genFunctor N) isSheaf_genFunctor T x
    (fun j Z (y : Pt N Z) => y.b ⁻¹ᵁ U j) ?_ ?_ ?_
  · intro j Z (y : Pt N Z) Z' a
    simp only [genFunctor_map]
    constructor
    · intro h
      let c := IsOpenImmersion.lift (U j).ι (a ≫ y.b) (by
        rintro _ ⟨z, rfl⟩
        exact ⟨⟨_, h ⟨z, rfl⟩⟩, rfl⟩)
      have hc : c ≫ (U j).ι = a ≫ y.b := IsOpenImmersion.lift_fac _ _ _
      have hy : ∀ k, ⊤ ≤ 𝟙 Z' ⁻¹ᵁ (Pt.map a y).b ⁻¹ᵁ (N k).U (j k) := fun k z _ =>
        hU j k (h ⟨z, rfl⟩)
      obtain ⟨g, hg, hg'⟩ := hex j Z' c fun k => pb (𝟙 Z') _ ⊤ (hy k) ((Pt.map a y).s k (j k))
      refine ⟨g, Pt.ext_chart ?_ j (hx j Z' g) hy fun k => Units.ext ((hxs j Z' g k).trans (hg' k))⟩
      change g ≫ p j ≫ (U j).ι = a ≫ y.b
      rw [← hc, ← hg, Category.assoc]
    · rintro ⟨g, hg⟩ _ ⟨z, rfl⟩
      have e : g ≫ p j ≫ (U j).ι = a ≫ y.b := congrArg Pt.b hg
      change (a ≫ y.b) z ∈ U j
      rw [← e]
      exact (p j (g z)).2
  · intro j Z g g' h
    replace h : Pt.map g (x j) = Pt.map g' (x j) := h
    refine hun j Z g g' ?_ fun k => ?_
    · have e : g ≫ p j ≫ (U j).ι = g' ≫ p j ≫ (U j).ι := congrArg Pt.b h
      rw [← cancel_mono (U j).ι, Category.assoc, Category.assoc, e]
    · rw [← hxs, ← hxs]
      exact congrArg Units.val (Pt.congr h k (j k) _ _ _ _)
  · intro Z (y : Pt N Z) z
    choose j hj using fun k => LB.mem_of_cover (hN k) (y.b z)
    exact ⟨j, Set.mem_iInter.2 hj⟩
end GlobalTheory.GeneratorFunctor
