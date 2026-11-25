-- Prove2me | solution 1 for GroundTheory.Global.mixedTraceForm_separatingLeft
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:09:48.993923+00:00
-- url     : https://prove2.me/submissions/472d8024-f04d-4543-9a46-d355675729e3

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TracePairing
import Theorems.Thm_P2M_GroundTheory_Global_mixedTraceForm_apply__be78fc251b6f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical ComplexConjugate RealInnerProductSpace FourierTransform Real
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution : (mixedTraceForm K).SeparatingLeft := by
  intro x hx
  have h := hx (x.1, fun w => conj (x.2 w))
  rw [mixedTraceForm_apply'] at h
  simp only [Complex.mul_conj, Complex.ofReal_re] at h
  have h1 : 0 ≤ ∑ w, x.1 w * x.1 w := Finset.sum_nonneg fun w _ => mul_self_nonneg _
  have h2 : 0 ≤ ∑ w, 2 * Complex.normSq (x.2 w) :=
    Finset.sum_nonneg fun w _ => mul_nonneg zero_le_two (Complex.normSq_nonneg _)
  have e1 : ∑ w, x.1 w * x.1 w = 0 := by linarith
  have e2 : ∑ w, 2 * Complex.normSq (x.2 w) = 0 := by linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun w _ => mul_self_nonneg _)] at e1
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun w _ => mul_nonneg zero_le_two (Complex.normSq_nonneg _))] at e2
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · simpa using e1 w (Finset.mem_univ _)
  · simpa using e2 w (Finset.mem_univ _)
end GroundTheory.Global
