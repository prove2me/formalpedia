-- Prove2me | solution 1 for GlobalTheory.Shintani.denseRange_realEmbeddings
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:10:04.366621+00:00
-- url     : https://prove2.me/submissions/f6b00832-ec2b-4462-a98e-e11d3d81ba83

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsSimplicial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DenseRangeRealEmbeddings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField GlobalTheory.Shintani MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.Shintani
namespace GlobalTheory.Shintani
theorem _root_.solution :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F],
      DenseRange (fun (x : F) (σ : F →+* ℝ) => σ x) := by
  intro F _ _ _
  have h1 := NumberField.InfiniteAdeleRing.denseRange_algebraMap F
  let E : ∀ w : InfinitePlace F, w.Completion → ℝ := fun w z =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w) z
  have hs : Function.Surjective (Pi.map E) := by
    intro y
    refine ⟨fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm (y w), ?_⟩
    funext w
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).apply_symm_apply (y w)
  have hc : Continuous (Pi.map E) := by
    refine continuous_pi fun w => ?_
    have : (E w) = InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal w) := by
      funext z; exact InfinitePlace.Completion.ringEquivRealOfIsReal_apply _ z
    change Continuous fun a : (∀ v : InfinitePlace F, v.Completion) => E w (a w)
    rw [this]
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
      (IsTotallyReal.isReal w)).continuous.comp (continuous_apply w)
  have h2 := hs.denseRange.comp h1 hc
  let g : (F →+* ℝ) → InfinitePlace F := fun σ => InfinitePlace.mk (Complex.ofRealHom.comp σ)
  have hreal : ∀ σ : F →+* ℝ, ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    intro σ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp [ComplexEmbedding.conjugate_coe_eq]
  have hemb : ∀ σ : F →+* ℝ, (g σ).embedding = Complex.ofRealHom.comp σ := fun σ =>
    InfinitePlace.embedding_mk_eq_of_isReal (hreal σ)
  have hg : Function.Injective g := by
    intro σ τ h
    have := hemb σ
    rw [h, hemb τ] at this
    ext x
    have h3 := congrArg (fun f : F →+* ℂ => f x) this
    simp only [RingHom.comp_apply, Complex.ofRealHom_eq_coe, Complex.ofReal_inj] at h3
    exact h3.symm
  have hval : ∀ (x : F) (σ : F →+* ℝ), Pi.map E (algebraMap F (InfiniteAdeleRing F) x) (g σ) = σ x := by
    intro x σ
    change E (g σ) (algebraMap F (InfiniteAdeleRing F) x (g σ)) = σ x
    rw [InfiniteAdeleRing.algebraMap_apply]
    have e1 := InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe (IsTotallyReal.isReal (g σ))
      ((WithAbs.equiv (g σ).1).symm x)
    have e2 := InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal (g σ)) x
    apply Complex.ofReal_injective
    simp only [E, InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
    have e3 : ((InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal (g σ)))
        { toCompletion := ↑(WithAbs.toAbs (g σ).1 x) } : ℂ) = (g σ).embedding x := by
      rw [← e2]
      simp only [RingEquiv.apply_symm_apply, WithAbs.equiv_symm_apply, WithAbs.equiv_apply] at e1
      exact congrArg _ e1
    rw [e3, hemb σ]
    rfl

  let P : (InfinitePlace F → ℝ) → ((F →+* ℝ) → ℝ) := fun y σ => y (g σ)
  have hPs : Function.Surjective P := fun z => ⟨Function.extend g z 0, funext fun σ => hg.extend_apply z 0 σ⟩
  have hPc : Continuous P := continuous_pi fun σ => continuous_apply (g σ)
  convert hPs.denseRange.comp h2 hPc using 1
  funext x σ
  exact (hval x σ).symm
end GlobalTheory.Shintani
