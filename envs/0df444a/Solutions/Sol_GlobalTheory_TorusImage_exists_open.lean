-- Prove2me | solution 1 for GlobalTheory.TorusImage.exists_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:56:08.838594+00:00
-- url     : https://prove2.me/submissions/3a8c9f13-5c99-4064-8600-9ab8628a953d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRatioOfWeightSumsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTorusStableGoodOpenOfWeightUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusImageFactorQuotientGoodOpen
import Theorems.Thm_GlobalTheory_TorusImage_exists_finset_ext
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_P2M_GlobalTheory_T_exists_ratio_of_weight_sums__fe61bd6e41f2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.TorusImage
namespace GlobalTheory.TorusImage
theorem _root_.solution (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (hG : SmConn G)
    [IrreducibleSpace G.left] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (i : splitTorus (Sp k) X ⟶ G) (hi : IsMonHom i) :
    ∃ U : G.left.Opens, (U : Set G.left).Nonempty ∧ ∀ (Y : Over (Sp k)) (t : Y ⟶ splitTorus (Sp k) X) (g : Y ⟶ G),
      (∀ χ ∈ weights i, SplitTorus.val t χ = 1) → ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ U → ⊤ ≤ g.left ⁻¹ᵁ U →
      (t ≫ i) * g = g := by
  have := hG.2.1
  obtain ⟨x⟩ : Nonempty G.left := inferInstance
  obtain ⟨W, hW, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := G.left) (U := ⊤) (x := x) trivial
  obtain ⟨s, hs⟩ := exists_finset_ext G hW
  have one : ∀ f : Γ(G.left, W), ∃ U : G.left.Opens, (U : Set G.left).Nonempty ∧
      ∀ (Y : Over (Sp k)) (t : Y ⟶ splitTorus (Sp k) X) (g : Y ⟶ G),
      (∀ χ ∈ weights i, SplitTorus.val t χ = 1) → ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ U → ⊤ ≤ g.left ⁻¹ᵁ U →
      ∀ h₁ h₂, (((t ≫ i) * g).left.appLE W ⊤ h₁).hom f = (g.left.appLE W ⊤ h₂).hom f := by
    intro f
    obtain ⟨U, hU, n, a, b, χ, hne, hw, hb, e⟩ := GlobalTheory.T.exists_ratio_of_weight_sums' k G hG X i hi W f ⟨x, hx⟩
    refine ⟨U, hne, fun Y t g ht k₁ k₂ h₁ h₂ => ?_⟩
    have key : ∀ (c : Γ(G.left, U)) (ψ : X), Wt i U c ψ → (c = 0 ∨ IsUnit c) →
        (((t ≫ i) * g).left.appLE U ⊤ k₁).hom c = (g.left.appLE U ⊤ k₂).hom c := by
      rintro c ψ hc (rfl | hu)
      · rw [map_zero, map_zero]
      · rw [hc Y t g k₁ k₂, appTop_charUnit, ht ψ ⟨U, c, hne, hu, hc⟩, _root_.one_mul]
    have ea : (((t ≫ i) * g).left.appLE U ⊤ k₁).hom (∑ j, a j) = (g.left.appLE U ⊤ k₂).hom (∑ j, a j) := by
      rw [map_sum, map_sum]
      exact Finset.sum_congr rfl fun j _ => key _ _ (hw j).1 (hw j).2.2.1
    have eb : (((t ≫ i) * g).left.appLE U ⊤ k₁).hom (∑ j, b j) = (g.left.appLE U ⊤ k₂).hom (∑ j, b j) := by
      rw [map_sum, map_sum]
      exact Finset.sum_congr rfl fun j _ => key _ _ (hw j).2.1 (hw j).2.2.2
    rw [← e, map_mul, map_mul, eb, appLE_res _ hU k₁ h₁, appLE_res _ hU k₂ h₂] at ea
    exact (hb.map (g.left.appLE U ⊤ k₂).hom).mul_right_cancel ea
  choose V hV hV' using one
  have fin : ∀ s : Finset Γ(G.left, W), ∃ U : G.left.Opens, (U : Set G.left).Nonempty ∧ U ≤ W ∧ ∀ f ∈ s, U ≤ V f := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨W, ⟨x, hx⟩, le_rfl, by simp⟩
    | insert f s _ ih =>
      obtain ⟨U, h1, h2, h3⟩ := ih
      refine ⟨U ⊓ V f, nonempty_preirreducible_inter U.2 (V f).2 h1 (hV f), inf_le_left.trans h2, fun f' hf' => ?_⟩
      rcases Finset.mem_insert.1 hf' with rfl | hf'
      · exact inf_le_right
      · exact inf_le_left.trans (h3 f' hf')
  obtain ⟨U, h1, h2, h3⟩ := fin s
  refine ⟨U, h1, fun Y t g ht k₁ k₂ => hs Y _ _ (k₁.trans fun _ hy => h2 hy) (k₂.trans fun _ hy => h2 hy) fun f hf => ?_⟩
  exact hV' f Y t g ht (k₁.trans fun _ hy => h3 f hf hy) (k₂.trans fun _ hy => h3 f hf hy) _ _
end GlobalTheory.TorusImage
