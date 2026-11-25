-- Prove2me | solution 1 for GlobalTheory.generatorScheme_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:46:33.476978+00:00
-- url     : https://prove2.me/submissions/5fb1c65b-14cd-47fd-a187-6d6cee892c38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties
import Theorems.Thm_GlobalTheory_GenScheme_prop_of_torus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_torus_dim


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
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (B : Scheme.{0}) (κ : Type) [Fintype κ] (N : κ → LB B), (∀ k, (N k).IsLB) → ∀ (G : Scheme.{0}) (q : G ⟶ B) (u : ∀ k (i : (N k).ι), Γ(G, q ⁻¹ᵁ (N k).U i)ˣ), ((∀ k i i', res (Scheme.Hom.preimage_mono q (inf_le_right : (N k).U i ⊓ (N k).U i' ≤ (N k).U i')) (u k i') = pullU q _ ((N k).g i i') * res (Scheme.Hom.preimage_mono q (inf_le_left : (N k).U i ⊓ (N k).U i' ≤ (N k).U i)) (u k i)) ∧ ∀ (Z : Scheme.{0}) (b : Z ⟶ B) (s : ∀ k (i : (N k).ι), Γ(Z, b ⁻¹ᵁ (N k).U i)ˣ), (∀ k i i', res (Scheme.Hom.preimage_mono b (inf_le_right : (N k).U i ⊓ (N k).U i' ≤ (N k).U i')) (s k i') = pullU b _ ((N k).g i i') * res (Scheme.Hom.preimage_mono b (inf_le_left : (N k).U i ⊓ (N k).U i' ≤ (N k).U i)) (s k i)) → ∃! g : Z ⟶ G, ∃ hg : g ≫ q = b, ∀ k i, (g.appLE (q ⁻¹ᵁ (N k).U i) (b ⁻¹ᵁ (N k).U i) (by rw [← hg]; exact le_rfl)).hom (u k i).val = (s k i).val) → IsAffineHom q ∧ Smooth q ∧ Surjective q ∧ IsSeparated q ∧ GeometricallyConnected q := by
  intro B κ _ N hN G q u ⟨hu, hU⟩
  have hc : GeometricallyConnected q := by
    have : IsZariskiLocalAtTarget @GeometricallyConnected := by
      rw [GeometricallyConnected.eq_geometrically]; infer_instance
    exact GenScheme.prop_of_torus @GeometricallyConnected (fun V => inferInstance) hN hu hU
  have : IsZariskiLocalAtTarget @IsAffineHom :=
    HasAffineProperty.instIsZariskiLocalAtTarget (P := @IsAffineHom)
  have : IsZariskiLocalAtTarget @Smooth := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth)
  have ha : IsAffineHom q := GenScheme.prop_of_torus @IsAffineHom (fun V => inferInstance) hN hu hU
  refine ⟨ha, GenScheme.prop_of_torus @Smooth (fun V => ?_) hN hu hU, inferInstance, inferInstance, hc⟩
  have := H1.torus_dim V (κ →₀ ℤ)
  exact SmoothOfRelativeDimension.smooth (Module.finrank ℤ (κ →₀ ℤ)) _
end GlobalTheory
