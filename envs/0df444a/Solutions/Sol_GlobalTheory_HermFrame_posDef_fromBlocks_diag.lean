-- Prove2me | solution 1 for GlobalTheory.HermFrame.posDef_fromBlocks_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:46:24.496566+00:00
-- url     : https://prove2.me/submissions/691a0e59-12fc-45c5-8f01-f992d4ad8671

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OpNormLeOpNormBlockDiagonal
import Theorems.Thm_GlobalTheory_HermFrame_form_fromBlocks_diag
import Theorems.Thm_GlobalTheory_HermFrame_form_self
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m l m' l' : Type*}
variable [Fintype m] [Fintype l] [Fintype m'] [Fintype l']
namespace GlobalTheory.HermFrame
theorem _root_.solution {A₁ : Matrix m m ℂ} {A₂ : Matrix l l ℂ} (h₁ : A₁.PosDef)
    (h₂ : A₂.PosDef) : (fromBlocks A₁ 0 0 A₂).PosDef := by
  refine posDef_iff.2 ⟨IsHermitian.fromBlocks h₁.isHermitian (by simp) h₂.isHermitian,
    fun v hv => ?_⟩
  rw [← Sum.elim_comp_inl_inr v] at hv ⊢
  rw [form_fromBlocks_diag, form_self h₁.posSemidef, form_self h₂.posSemidef, ← ofReal_add,
    zero_lt_real]
  by_cases h : v ∘ Sum.inl = 0
  · have h' : v ∘ Sum.inr ≠ 0 := fun h' => hv (by rw [h, h']; simp)
    have := gnorm_pos h₂ h'
    positivity
  · have := gnorm_pos h₁ h
    positivity
end GlobalTheory.HermFrame
