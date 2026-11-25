-- Prove2me | solution 1 for GlobalTheory.GeneratorFunctor.isSheaf_genFunctor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:39:30.499618+00:00
-- url     : https://prove2.me/submissions/8a377ecb-c6c6-41e4-a705-6a545eda8143

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InverseBundleGeneratorPointOfChartUnitsSections
import Theorems.Thm_GlobalTheory_GeneratorFunctor_cover_ext
import Theorems.Thm_GlobalTheory_GeneratorFunctor_cover_glue
import Theorems.Thm_GlobalTheory_GeneratorFunctor_Pt_congr

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
theorem _root_.solution : Presieve.IsSheaf Scheme.zariskiTopology (genFunctor N) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y S hS
  obtain ⟨(𝒰 : Scheme.OpenCover Y), rfl⟩ := Scheme.exists_cover_of_mem_pretopology hS
  rw [Presieve.isSheafFor_arrows_iff]
  intro (x : ∀ j, Pt N (𝒰.X j)) hx
  replace hx : ∀ i j (Z : Scheme.{0}) (a : Z ⟶ 𝒰.X i) (a' : Z ⟶ 𝒰.X j),
      a ≫ 𝒰.f i = a' ≫ 𝒰.f j → Pt.map a (x i) = Pt.map a' (x j) := hx
  let b : Y ⟶ B := 𝒰.glueMorphisms (fun j => (x j).b) fun i j =>
    congrArg Pt.b (hx i j _ _ _ pullback.condition)
  have hb : ∀ j, 𝒰.f j ≫ b = (x j).b := fun j => 𝒰.ι_glueMorphisms _ _ j
  have hle : ∀ j (U : B.Opens), 𝒰.f j ⁻¹ᵁ b ⁻¹ᵁ U ≤ 𝟙 (𝒰.X j) ⁻¹ᵁ (x j).b ⁻¹ᵁ U := fun j U => by
    rw [← hb]; exact le_rfl
  have hs : ∀ k i, ∃ s : Γ(Y, b ⁻¹ᵁ (N k).U i)ˣ, ∀ j, pb (𝒰.f j) _ _ le_rfl s =
      pb (𝟙 _) _ _ (hle j _) ((x j).s k i) := fun k i => by
    refine cover_glue 𝒰 _ _ fun j j' Z a a' e h h' => ?_
    have := Pt.congr (hx j j' Z a a' e) k i (𝟙 Z) ⊤ (h.trans (a.preimage_mono (hle j _)))
      (h'.trans (a'.preimage_mono (hle j' _)))
    rw [pb_comp_id, pb_comp_id]
    exact (pb_id_comp _ _ _ _ _ _ _).symm.trans (this.trans (pb_id_comp _ _ _ _ _ _ _))
  choose s hs using hs
  have hs' : ∀ k i j (W : (𝒰.X j).Opens) (h : W ≤ 𝒰.f j ⁻¹ᵁ b ⁻¹ᵁ (N k).U i),
      pb (𝒰.f j) _ W h (s k i) = pb (𝟙 _) _ W (h.trans (hle j _)) ((x j).s k i) := by
    intro k i j W h
    have := congrArg (pb (𝟙 _) (𝒰.f j ⁻¹ᵁ b ⁻¹ᵁ (N k).U i) W h) (hs k i j)
    rwa [pb_id_comp, pb_id_comp] at this
  let y : Pt N Y := ⟨b, s, fun k i i' W h h' => cover_ext 𝒰 _ _ _ fun j => by
    rw [map_mul, pb_comp_id, pb_comp_id, pb_pb, hs', hs', pb_congr (hb j)]
    exact (x j).compat k i i' _ _ _⟩
  refine ⟨y, fun j => ?_, fun (y' : Pt N Y) hy' => ?_⟩
  · exact Pt.ext' (hb j) fun k i => hs k i j
  · replace hy' : ∀ j, Pt.map (𝒰.f j) y' = x j := hy'
    have e : y'.b = b := 𝒰.hom_ext _ _ fun j => (congrArg Pt.b (hy' j)).trans (hb j).symm
    refine Pt.ext' e fun k i => cover_ext 𝒰 _ _ _ fun j => ?_
    rw [pb_comp_id]
    refine Eq.trans ?_ (hs' k i j _ _).symm
    exact (pb_id_comp _ _ _ _ _ _ _).symm.trans (Pt.congr (hy' j) k i (𝟙 _) _ le_rfl _)
end GlobalTheory.GeneratorFunctor
