-- Prove2me | solution 1 for GlobalTheory.Models.Cpt.Above.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:02:35.613795+00:00
-- url     : https://prove2.me/submissions/772fc364-a55f-487c-a2d8-e4b709d5069d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GenericPartDenseProOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueLiftOfDensePart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_OpenImmersionCompStructureEqGeneric
import Theorems.Thm_GlobalTheory_Models_Cpt_openImmersion_comp_structure_eq_generic
import Theorems.Thm_GlobalTheory_existsUnique_lift_of_densePart
import Theorems.Thm_GlobalTheory_genericPart_dense_proOpen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_projProper
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pullCubCancel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sabCancel

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
open GlobalTheory.Models
namespace GlobalTheory.Models
private theorem spMap_comp_moduli_spaces {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (g : A →+* B) (g' : B →+* D) :
    spMap (g'.comp g) = spMap g' ≫ spMap g := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl
end GlobalTheory.Models
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory GlobalTheory.Models
namespace GlobalTheory.Models
namespace Cpt.Above
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (U'' : Scheme.{0}) (F'' O'' : Type) [Field F''] [CommRing O''] (c'' : U'' ⟶ Sp F'') (t'' : SAB H U'') (β'' : O'' →+* F'') (C : Cpt c t β) (C' : Cpt c' t' β') (C'' : Cpt c'' t'' β'') (b : O →+* O') (b' : O' →+* O'') (k' : F' →+* F'') (r : U' ⟶ U) (ν : SABMap t' t r) (a : C'.Above C b r ν) (r' : U'' ⟶ U') (ν' : SABMap t'' t' r') (f : C''.X ⟶ C.X) (mu : SABMap C''.t C.t f) (hf : f ≫ C.s = C''.s ≫ spMap (b'.comp b)), IsDedFrac β'' → β''.comp b' = k'.comp β' → r' ≫ c' = c'' ≫ spMap k' → C''.j ≫ f = r' ≫ r ≫ C.j → C''.m.φ ≫ mu.φ = ν'.φ ≫ ν.φ ≫ C.m.φ → ∃ (h : C''.X ⟶ C'.X) (mu' : SABMap C''.t C'.t h) (hh : h ≫ C'.s = C''.s ≫ spMap b'), h ≫ a.π = f ∧ mu'.φ ≫ a.mu.φ = mu.φ ∧ C''.j ≫ h = r' ≫ C'.j ∧ C''.m.φ ≫ mu'.φ = ν'.φ ≫ C'.m.φ ∧ (IsFinite (pullback.lift f C''.s hf) → IsFinite (pullback.lift h C''.s hh)) := by
  intro E _ _ _ H U F O _ _ c t β U' F' O' _ _ c' t' β' U'' F'' O'' _ _ c'' t'' β'' C C' C'' b b' k' r ν a r' ν' f mu hf
    hD hβ hc hj hφ
  obtain ⟨⟨hdom, hDed⟩, -, hFrac⟩ := hD
  let _ : Algebra O'' F'' := β''.toAlgebra
  have := hdom
  have : IsDedekindDomain O'' := hDed
  have : IsFractionRing O'' F'' := hFrac
  obtain ⟨hN, -, -, hPre, hFl, hDom, hQC⟩ := GlobalTheory.genericPart_dense_proOpen O'' F'' C''.X U'' C''.s C''.jQ C''.flat
    C''.proj C''.jQ_open C''.jQ_dense
  have : IsLocallyNoetherian C''.X := hN

  have hbase : f ≫ C.s = (C''.s ≫ spMap b') ≫ spMap b := by
    rw [hf, Category.assoc, spMap_comp_moduli_spaces]
  have hq : IsIntegralHom (pullback.lift a.π C'.s a.π_over) := by
    have := a.fin
    infer_instance
  have hsq : (r' ≫ C'.j) ≫ pullback.lift a.π C'.s a.π_over = C''.j ≫ pullback.lift f (C''.s ≫ spMap b') hbase := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, a.j_comm, hj]
    · simp only [Category.assoc, pullback.lift_snd]
      rw [Cpt.openImmersion_comp_structure_eq_generic C', ← Category.assoc r', hc, Category.assoc, ← spMap_comp_moduli_spaces, ← hβ,
        spMap_comp_moduli_spaces, ← Category.assoc C''.j, Cpt.openImmersion_comp_structure_eq_generic C'', Category.assoc]
  obtain ⟨h, ⟨h1, h2⟩, -⟩ := GlobalTheory.existsUnique_lift_of_densePart C''.X U'' (pullback C.s (spMap b)) C'.X C''.j C''.normal
    hPre hFl hDom hQC _ _ _ hq hsq
  have hπ : h ≫ a.π = f := by
    simpa only [Category.assoc, pullback.lift_fst] using congrArg (· ≫ pullback.fst _ _) h2
  have hh : h ≫ C'.s = C''.s ≫ spMap b' := by
    simpa only [Category.assoc, pullback.lift_snd] using congrArg (· ≫ pullback.snd _ _) h2
  clear h2 hsq hbase
  subst hπ
  obtain ⟨mu', hmu'⟩ := sabCancel pullCubCancel E H C.X C'.X C''.X C.t C'.t C''.t a.π h a.mu mu
  refine ⟨h, mu', hh, rfl, hmu'.symm, h1, ?_, ?_⟩
  · apply a.mu.2.1.hom_ext
    · rw [Category.assoc, Category.assoc]
      erw [← hmu', hφ, a.φ_comm]
    · have w1 := mu'.2.1.w
      have w2 := C''.m.2.1.w
      have w3 := ν'.2.1.w
      have w4 := C'.m.2.1.w
      have h1' : C''.jQ ≫ pullback.fst _ _ ≫ h = r' ≫ C'.jQ ≫ pullback.fst _ _ := by
        simpa only [Cpt.j, Category.assoc] using h1
      simp only [Category.assoc] at w1 w2 w3 w4 ⊢
      erw [w1, reassoc_of% w2, h1', w4, reassoc_of% w3]
  · intro hfin
    have : IsProper C'.s := projProper O' C'.X C'.s C'.proj
    let p : pullback C'.s (spMap b') ⟶ pullback C.s (spMap (b'.comp b)) :=
      pullback.lift (pullback.fst _ _ ≫ a.π) (pullback.snd _ _) (by
        rw [Category.assoc, a.π_over, ← Category.assoc, pullback.condition, Category.assoc, spMap_comp_moduli_spaces])
    have hp : pullback.lift h C''.s hh ≫ p = pullback.lift (h ≫ a.π) C''.s hf := by
      apply pullback.hom_ext
      · simp only [p, Category.assoc]
        rw [pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst]
      · simp only [p, Category.assoc]
        rw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
    have : IsSeparated p := by
      have e : p ≫ pullback.snd C.s (spMap (b'.comp b)) = pullback.snd C'.s (spMap b') := pullback.lift_snd _ _ _
      have : IsSeparated (p ≫ pullback.snd C.s (spMap (b'.comp b))) := by
        rw [e]
        infer_instance
      exact IsSeparated.of_comp p (pullback.snd C.s (spMap (b'.comp b)))
    rw [← hp] at hfin
    exact IsFinite.of_comp _ p
end Cpt.Above
end GlobalTheory.Models
