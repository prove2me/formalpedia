-- Prove2me | solution 1 for GlobalTheory.SmoothForms.PermWord.trace_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:06:44.508619+00:00
-- url     : https://prove2.me/submissions/f8dcb0bf-c6df-4ffa-9b37-3977bd38ad49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorter
import Theorems.Thm_GlobalTheory_SmoothForms_PermWord_trace_path

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
noncomputable section
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.PermWord
variable {S : Type} [CommRing S] {n : ℕ}
namespace GlobalTheory.SmoothForms.PermWord
theorem _root_.solution [Algebra ℂ S] (X : Fin n → Fin n → S) (k : ℕ) :
    ((Matrix.of X) ^ (k + 1)).trace = gelfA X k := by
  rw [pow_succ', trace_path, gelfA]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [List.prod_ofFn, Fin.prod_univ_castSucc, mul_comm]
  simp [Fin.coeSucc_eq_succ]
end GlobalTheory.SmoothForms.PermWord
