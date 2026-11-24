-- Prove2me | solution 1 for GlobalTheory.SW.ThetaProd.fromBlocks_mem_siegel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:29:34.05588+00:00
-- url     : https://prove2.me/submissions/0953d2ee-495e-46c5-a4f4-475cb706023b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaMulConjEqBlockTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ThetaProd
namespace GlobalTheory.SW.ThetaProd
theorem _root_.solution {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {τ₁ : Matrix ι₁ ι₁ ℂ} {τ₂ : Matrix ι₂ ι₂ ℂ} (h₁ : τ₁ ∈ Siegel ι₁) (h₂ : τ₂ ∈ Siegel ι₂) :
    Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj)) ∈ Siegel (ι₁ ⊕ ι₂) := by
  refine ⟨Matrix.IsSymm.fromBlocks h₁.1 (by simp) (h₂.1.map _).neg, ?_⟩
  have e : (Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj))).map Complex.im =
      Matrix.fromBlocks (τ₁.map Complex.im) 0 0 (τ₂.map Complex.im) := by
    ext (i | i) (j | j) <;> simp
  rw [e]
  refine Matrix.posDef_iff_dotProduct_mulVec.2
    ⟨Matrix.IsHermitian.fromBlocks h₁.2.isHermitian (by simp) h₂.2.isHermitian, fun x hx => ?_⟩
  obtain ⟨u, v, rfl⟩ : ∃ u v, x = Sum.elim u v :=
    ⟨x ∘ Sum.inl, x ∘ Sum.inr, (Sum.elim_comp_inl_inr x).symm⟩
  rw [star_trivial, fromBlocks_mulVec, sumElim_dotProduct_sumElim]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, add_zero, zero_add]
  have a := h₁.2.posSemidef.dotProduct_mulVec_nonneg u
  have b := h₂.2.posSemidef.dotProduct_mulVec_nonneg v
  rw [star_trivial] at a b
  by_cases hu : u = 0
  · have hv : v ≠ 0 := by
      rintro rfl
      apply hx
      rw [hu]
      ext (i | i) <;> rfl
    have := h₂.2.dotProduct_mulVec_pos hv
    rw [star_trivial] at this
    linarith
  · have := h₁.2.dotProduct_mulVec_pos hu
    rw [star_trivial] at this
    linarith
end GlobalTheory.SW.ThetaProd
