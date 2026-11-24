-- Prove2me | solution 1 for GlobalTheory.HermFrame.form_fromBlocks_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:46:26.908706+00:00
-- url     : https://prove2.me/submissions/6cf72987-4e6a-4bb3-aff9-7fb9aa4a227b

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
theorem _root_.solution (A₁ : Matrix m m ℂ) (A₂ : Matrix l l ℂ) (u u' : m → ℂ)
    (w w' : l → ℂ) : form (fromBlocks A₁ 0 0 A₂) (Sum.elim u w) (Sum.elim u' w') =
      form A₁ u u' + form A₂ w w' := by
  simp [form_eq_sum, Fintype.sum_sum_type]
end GlobalTheory.HermFrame
