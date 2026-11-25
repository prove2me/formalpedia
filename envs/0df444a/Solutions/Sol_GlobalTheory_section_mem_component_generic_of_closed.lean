-- Prove2me | solution 1 for GlobalTheory.section_mem_component_generic_of_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:09:51.133138+00:00
-- url     : https://prove2.me/submissions/8fe1aac2-a12a-4533-bfe1-7fcf1feb9274

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenConnectedComponentOfIsLocallyNoetherianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmoothGenericFibreClosurePartitionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionMemComponentGenericOfClosedValuation
import Theorems.Thm_GlobalTheory_separated_of_isOpen_component_subtype
import Theorems.Thm_GlobalTheory_isOpen_component_fibre_subtype
import Theorems.Thm_GlobalTheory_T_disjoint_closure_and_union_eq_univ_of_genericFibre_partition


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (e σ : Spec (CommRingCat.of V) ⟶ X), Smooth f → e ≫ f = 𝟙 _ → σ ≫ f = 𝟙 _ → σ (IsLocalRing.closedPoint V) ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} → σ (⊥ : PrimeSpectrum V) ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  intro V _ _ _ X f e σ hf he hσ hm
  have hfe : ∀ p : (Spec (CommRingCat.of V) : Scheme.{0}), f (e p) = p := fun p => by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  have hfσ : ∀ p : (Spec (CommRingCat.of V) : Scheme.{0}), f (σ p) = p := fun p => by
    rw [← Scheme.Hom.comp_apply, hσ]; rfl
  let g₀ : (Spec (CommRingCat.of V) : Scheme.{0}) := (⊥ : PrimeSpectrum V)
  let m : (Spec (CommRingCat.of V) : Scheme.{0}) := IsLocalRing.closedPoint V
  change σ m ∈ connectedComponentIn (f ⁻¹' {f (σ m)}) (e (f (σ m))) at hm
  change σ g₀ ∈ connectedComponentIn (f ⁻¹' {f (σ g₀)}) (e (f (σ g₀)))
  rw [hfσ] at hm ⊢
  have hsp : g₀ ⤳ m := IsLocalRing.specializes_closedPoint (R := V) ⊥
  have ha : e g₀ ∈ f ⁻¹' {g₀} := hfe g₀
  obtain ⟨h1, h2⟩ := separated_of_isOpen_component_subtype (f ⁻¹' {g₀}) (e g₀) ha
    (isOpen_component_fibre_subtype f g₀ ⟨e g₀, ha⟩)
  obtain ⟨hd, hu⟩ := GlobalTheory.T.disjoint_closure_and_union_eq_univ_of_genericFibre_partition V X f hf (connectedComponentIn (f ⁻¹' {g₀}) (e g₀))
    (f ⁻¹' {g₀} \ connectedComponentIn (f ⁻¹' {g₀}) (e g₀))
    (Set.union_diff_cancel (connectedComponentIn_subset _ _)) h1 h2
  by_contra hne
  have hσ' : σ m ∈ closure (f ⁻¹' {g₀} \ connectedComponentIn (f ⁻¹' {g₀}) (e g₀)) :=
    (hsp.map σ.continuous).mem_closed isClosed_closure (subset_closure ⟨hfσ g₀, hne⟩)
  have he' : e m ∈ closure (connectedComponentIn (f ⁻¹' {g₀}) (e g₀)) :=
    (hsp.map e.continuous).mem_closed isClosed_closure
      (subset_closure (mem_connectedComponentIn ha))
  have hclopen : IsClopen (closure (connectedComponentIn (f ⁻¹' {g₀}) (e g₀))) := by
    refine ⟨isClosed_closure, ?_⟩
    have : closure (connectedComponentIn (f ⁻¹' {g₀}) (e g₀))
        = (closure (f ⁻¹' {g₀} \ connectedComponentIn (f ⁻¹' {g₀}) (e g₀)))ᶜ :=
      (IsCompl.eq_compl ⟨hd, codisjoint_iff.2 hu⟩)
    rw [this]
    exact isClosed_closure.isOpen_compl
  have hsub := (isPreconnected_connectedComponentIn (x := e m) (F := f ⁻¹' {m})).subset_isClopen
    hclopen ⟨e m, mem_connectedComponentIn (hfe m), he'⟩
  exact Set.disjoint_left.1 hd (hsub hm) hσ'
end GlobalTheory
