-- Prove2me | solution 1 for GlobalTheory.HermFrame.det_firstGram_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:48:53.605853+00:00
-- url     : https://prove2.me/submissions/dbe347d3-08fb-4901-b693-c7249371ee41

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EventuallyDifferentiableAtOfContDiffAtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LeTwoMulOfForallScale
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
import Theorems.Thm_GlobalTheory_HermFrame_det_eq_det_subGram_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero

set_option autoImplicit false
open Matrix Complex ComplexConjugate
open scoped ComplexOrder MatrixOrder
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
variable {N : ℕ}
namespace GlobalTheory.HermFrame
theorem _root_.solution (H : Matrix (Fin N) (Fin N) ℂ) (i : Fin N)
    (hu : IsUnit (firstGram i.2.le H).det) :
    (firstGram (k := i + 1) i.2 H).det = (firstGram i.2.le H).det * gradedGram H i () () := by
  have h := det_eq_det_subGram_mul (H := stepGram H i) hu
  rw [det_unique (quotGram _)] at h
  rw [← det_submatrix_equiv_self
    ((Equiv.sumCongr (Equiv.refl _) (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv)]
  refine Eq.trans ?_ h
  congr 1
  ext (a | a) (b | b) <;> rfl
end GlobalTheory.HermFrame
