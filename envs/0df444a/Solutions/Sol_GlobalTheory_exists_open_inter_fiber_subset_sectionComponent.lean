-- Prove2me | solution 1 for GlobalTheory.exists_open_inter_fiber_subset_sectionComponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:24:56.481278+00:00
-- url     : https://prove2.me/submissions/09d0b2ac-948c-49db-bc1f-1f7043cbcfe0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionComponentsPreimageOfIsPullbackStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenConnectedComponentOfIsLocallyNoetherianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComponentInFibreIffOfIsPullbackStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenIsIrreducibleComponentOfRationalPointSmootStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineChartPreirreducibleFiber
import Theorems.Thm_GlobalTheory_RatPointConn_of_isPullback
import Theorems.Thm_GlobalTheory_T_mem_connectedComponentIn_fibre_iff_of_isPullback
import Theorems.Thm_P2M_GlobalTheory_T_isOpen_connectedComponent_of_isLocallyNoetherian__f7bb4608baf5


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
theorem _root_.solution (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X)
    (hf : Smooth f) (he : e ≫ f = 𝟙 _) (s : S) :
    ∃ W₁ : X.Opens, e s ∈ W₁ ∧ ∀ x : X, x ∈ W₁ → f x = s →
      x ∈ connectedComponentIn (f ⁻¹' {s}) (e s) := by
  have hes : f (e s) = s := by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  have hrange : Set.range (f.fiberι s) = f ⁻¹' {s} := f.range_fiberι s
  obtain ⟨y₀, hy₀⟩ : e s ∈ Set.range (f.fiberι s) := by rw [hrange]; exact hes
  have hpb : IsPullback (f.fiberι s) (f.fiberToSpecResidueField s) f (S.fromSpecResidueField s) :=
    IsPullback.of_hasPullback _ _
  have hft : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
    MorphismProperty.of_isPullback hpb inferInstance
  have hN : IsLocallyNoetherian (f.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)
  have hopen := GlobalTheory.T.isOpen_connectedComponent_of_isLocallyNoetherian' _ hN y₀
  obtain ⟨U, hU, hUe⟩ := (f.fiberι s).isEmbedding.isInducing.isOpen_iff.mp hopen
  refine ⟨⟨U, hU⟩, ?_, ?_⟩
  · change e s ∈ U
    rw [← hy₀]
    have : y₀ ∈ connectedComponent y₀ := mem_connectedComponent
    rw [← hUe] at this
    exact this
  · intro x hx hxs
    obtain ⟨y, rfl⟩ : x ∈ Set.range (f.fiberι s) := by rw [hrange]; exact hxs
    refine (GlobalTheory.T.mem_connectedComponentIn_fibre_iff_of_isPullback X S f e s _ _ _ y₀ hpb hy₀ y).mpr ?_
    rw [← hUe]
    exact hx
end GlobalTheory
