-- Prove2me | solution 1 for GlobalTheory.IdCompOpen.isOpen_sectionComponents_of_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:38:30.587611+00:00
-- url     : https://prove2.me/submissions/dc5a2bf3-be6e-4051-be7a-ca28aa8a419c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOpenNbhdSectionFibreIsPreirreducibleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenSndImageMulMemOpenGroupSchemeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemUnitComponentMulMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemIdentityComponentsOfMulInvStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenOfStableUnderGeneralizationOfLocallyClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StableUnderGeneralizationSectionComponentsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenIdentityComponentsSmoothGroupScheme
import Theorems.Thm_GlobalTheory_T_exists_open_nbhd_section_fiber_isPreirreducible
import Theorems.Thm_GlobalTheory_T_isOpen_of_stableUnderGeneralization_of_local_pieces
import Theorems.Thm_GlobalTheory_T_stableUnderGeneralization_section_connectedComponentIn


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
open GlobalTheory GlobalTheory.IdCompOpen
namespace GlobalTheory.IdCompOpen
theorem _root_.solution (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X)
    (hf : Smooth f) (he : e ≫ f = 𝟙 _) (O : X.Opens → Set X) (hO : ∀ U, IsOpen (O U))
    (h1 : ∀ (U : X.Opens) (y : X), e (f y) ∈ U →
      y ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} → y ∈ O U)
    (h2 : ∀ (U : X.Opens) (y : X),
      (∀ z ∈ U, f z = f y → z ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))}) →
      y ∈ O U → y ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))}) :
    IsOpen {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  classical
  have hfe : ∀ t : S, f (e t) = t := fun t => by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  refine GlobalTheory.T.isOpen_of_stableUnderGeneralization_of_local_pieces X _ (GlobalTheory.T.stableUnderGeneralization_section_connectedComponentIn X S f e hf he) ?_
  intro x hx
  obtain ⟨U, V₀, V, I, hV, hs, hU, hI, hirr⟩ := GlobalTheory.T.exists_open_nbhd_section_fiber_isPreirreducible X S f e hf he (f x)
  refine ⟨⟨O U, hO U⟩ ⊓ f ⁻¹ᵁ (V₀ ⊓ e ⁻¹ᵁ U), f ⁻¹ᵁ V, I.image (fun c => f.app V c), ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact hV hy.2.1
  · exact ⟨h1 U x hU hx, hs, hU⟩
  · intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hc
    rw [← Scheme.preimage_basicOpen]
    exact hI d hd
  · intro y hy hJ
    have hpre := hirr (f y) hy.2.1 (fun c hc => by
      have := hJ _ (Finset.mem_image_of_mem _ hc)
      rw [← Scheme.preimage_basicOpen] at this
      exact this)
    refine h2 U y ?_ hy.1
    intro z hz hzy
    have hsub := hpre.isPreconnected.subset_connectedComponentIn
      (x := e (f y)) (F := f ⁻¹' {f y}) ⟨hy.2.2, hfe _⟩ Set.inter_subset_right
    show z ∈ connectedComponentIn (f ⁻¹' {f z}) (e (f z))
    rw [hzy]
    exact hsub ⟨hz, hzy⟩
end GlobalTheory.IdCompOpen
