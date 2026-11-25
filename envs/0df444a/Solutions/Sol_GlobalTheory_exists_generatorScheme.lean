-- Prove2me | solution 1 for GlobalTheory.exists_generatorScheme
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:14:35.852028+00:00
-- url     : https://prove2.me/submissions/cf78e4e4-9f3c-4db4-ab94-641a27d6c363

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InverseBundleGeneratorPointOfChartUnitsSections
import Theorems.Thm_GlobalTheory_GeneratorFunctor_Pt_congr
import Theorems.Thm_GlobalTheory_GeneratorFunctor_isRepresentable_genFunctor

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
set_option backward.isDefEq.respectTransparency false
open GeneratorFunctor Opposite
namespace GlobalTheory
theorem _root_.solution : ∀ (B : Scheme.{0}) (κ : Type) [Fintype κ] (N : κ → LB B), (∀ k, (N k).IsLB) → ∃ (G : Scheme.{0}) (q : G ⟶ B) (u : ∀ k (i : (N k).ι), Γ(G, q ⁻¹ᵁ (N k).U i)ˣ), (∀ k i i', res (Scheme.Hom.preimage_mono q (inf_le_right : (N k).U i ⊓ (N k).U i' ≤ (N k).U i')) (u k i') = pullU q _ ((N k).g i i') * res (Scheme.Hom.preimage_mono q (inf_le_left : (N k).U i ⊓ (N k).U i' ≤ (N k).U i)) (u k i)) ∧ ∀ (Z : Scheme.{0}) (b : Z ⟶ B) (s : ∀ k (i : (N k).ι), Γ(Z, b ⁻¹ᵁ (N k).U i)ˣ), (∀ k i i', res (Scheme.Hom.preimage_mono b (inf_le_right : (N k).U i ⊓ (N k).U i' ≤ (N k).U i')) (s k i') = pullU b _ ((N k).g i i') * res (Scheme.Hom.preimage_mono b (inf_le_left : (N k).U i ⊓ (N k).U i' ≤ (N k).U i)) (s k i)) → ∃! g : Z ⟶ G, ∃ hg : g ≫ q = b, ∀ k i, (g.appLE (q ⁻¹ᵁ (N k).U i) (b ⁻¹ᵁ (N k).U i) (by rw [← hg]; exact le_rfl)).hom (u k i).val = (s k i).val := by
  intro B κ _ N hN
  obtain ⟨G, ⟨e⟩⟩ := (isRepresentable_genFunctor hN).has_representation
  let x : Pt N G := e.homEquiv (𝟙 G)
  have he : ∀ {Z : Scheme.{0}} (g : Z ⟶ G), e.homEquiv g = Pt.map g x := fun g => by
    rw [e.homEquiv_eq]; rfl
  refine ⟨G, x.b, x.s, fun k i i' => ?_, fun Z b s hs => ?_⟩
  · rw [res_eq_pb, res_eq_pb, pullU_eq_pb]
    exact x.compat k i i' _ inf_le_left inf_le_right
  · let y : Pt N Z := ⟨b, s, fun k i i' W h h' => by
      have := congrArg (pb (𝟙 Z) (b ⁻¹ᵁ ((N k).U i ⊓ (N k).U i')) W (le_inf h h')) (hs k i i')
      rwa [map_mul, res_eq_pb, res_eq_pb, pullU_eq_pb, pb_id_comp, pb_id_comp, pb_id_comp] at this⟩
    have key : ∀ g : Z ⟶ G, (∃ hg : g ≫ x.b = b, ∀ k i, (g.appLE (x.b ⁻¹ᵁ (N k).U i)
        (b ⁻¹ᵁ (N k).U i) (by rw [← hg]; exact le_rfl)).hom (x.s k i).val = (s k i).val) ↔
        e.homEquiv g = y := fun g => by
      rw [he]
      constructor
      · rintro ⟨hg, h⟩
        refine (Pt.ext' (x := y) (y := Pt.map g x) hg.symm fun k i => ?_).symm
        exact (Units.ext (h k i).symm).trans (pb_id_comp _ _ _ _ _ _ _).symm
      · intro h
        have hg : g ≫ x.b = b := congrArg Pt.b h
        refine ⟨hg, fun k i => ?_⟩
        have := Pt.congr h k i (𝟙 Z) (b ⁻¹ᵁ (N k).U i) (by rw [← hg]; exact le_rfl) le_rfl
        exact congrArg Units.val
          ((pb_id_comp _ _ _ _ _ _ _).symm.trans (this.trans (pb_id _ _)))
    refine ⟨e.homEquiv.symm y, (key _).2 (e.homEquiv.apply_symm_apply y), fun g hg => ?_⟩
    rw [← (key g).1 hg, Equiv.symm_apply_apply]
end GlobalTheory
