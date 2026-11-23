-- Prove2me | solution 1 for GlobalTheory.CMTransference.sumElim_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:02.049997+00:00
-- url     : https://prove2.me/submissions/ee03d6b3-787c-4c98-ae04-3e73fd1f85c2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoveringRadiusStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BabaiCovering
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_CmApproximationTransference

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CMTransference
open NumberField Matrix Module Submodule ReciprocityTheory.MultiplicativeHeights ComplexConjugate
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {σ : ι → K →+* ℂ}
omit [NumberField K] [Fintype ι]
namespace GlobalTheory.CMTransference
theorem _root_.solution (hσ : Function.Injective σ)
    (hcm : ∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ) :
    Function.Bijective (Sum.elim σ fun i => ComplexEmbedding.conjugate (σ i)) := by
  have hcc : ∀ τ : K →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
    fun τ => by ext x; simp
  constructor
  · rintro (i | i) (j | j) h
    · exact congrArg _ (hσ h)
    · exact absurd ⟨i, h⟩ ((hcm (σ j)).1 ⟨j, rfl⟩)
    · exact absurd ⟨j, h.symm⟩ ((hcm (σ i)).1 ⟨i, rfl⟩)
    · have h' := congrArg ComplexEmbedding.conjugate h
      simp only [Sum.elim_inr, hcc] at h'
      exact congrArg _ (hσ h')
  · intro τ
    by_cases h : ∃ i, σ i = τ
    · obtain ⟨i, hi⟩ := h
      exact ⟨Sum.inl i, hi⟩
    · rw [hcm, not_not] at h
      obtain ⟨i, hi⟩ := h
      exact ⟨Sum.inr i, by simp only [Sum.elim_inr, hi, hcc]⟩
end GlobalTheory.CMTransference
