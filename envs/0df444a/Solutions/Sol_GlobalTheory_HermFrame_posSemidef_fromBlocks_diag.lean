-- Prove2me | solution 1 for GlobalTheory.HermFrame.posSemidef_fromBlocks_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:46:33.497834+00:00
-- url     : https://prove2.me/submissions/824f8e94-d13b-410e-9dca-0a150959cbea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OpNormLeOpNormBlockDiagonal
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
theorem _root_.solution {A₁ : Matrix m m ℂ} {A₂ : Matrix l l ℂ} (h₁ : A₁.PosSemidef)
    (h₂ : A₂.PosSemidef) : (fromBlocks A₁ 0 0 A₂).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg
    (IsHermitian.fromBlocks h₁.isHermitian (by simp) h₂.isHermitian) fun x => ?_
  have h : star x ⬝ᵥ (fromBlocks A₁ 0 0 A₂ *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (A₁ *ᵥ (x ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (A₂ *ᵥ (x ∘ Sum.inr)) := by
    simp [dotProduct, mulVec, Fintype.sum_sum_type]
  rw [h]
  exact add_nonneg (h₁.dotProduct_mulVec_nonneg _) (h₂.dotProduct_mulVec_nonneg _)
end GlobalTheory.HermFrame
