-- Prove2me | solution 1 for GlobalTheory.Nef.OrdCalc.nrm_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:02:52.9919+00:00
-- url     : https://prove2.me/submissions/544c2b06-24f8-44d6-957f-6fb40230a186

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceOrderCalculus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option autoImplicit false
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.OrdCalc
variable {k F : Type} [Field k] [Field F] [Algebra k F]
namespace GlobalTheory.Nef.OrdCalc
theorem _root_.solution (v : Place k F) (n : ℕ) (x : Fin n → F) (hx : x ≠ 0) :
    ∃ i, x i ≠ 0 ∧ nrm v x = v.1 (x i) ∧ ordVec v x = ord v (x i) ∧ ∀ j, v.1 (x j) ≤ v.1 (x i) := by
  obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hx
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨i0, Finset.mem_univ _⟩ (fun i => v.1 (x i))
  have hle : ∀ j, v.1 (x j) ≤ v.1 (x i) := fun j => by
    rw [← hi]; exact Finset.le_sup (f := fun i => v.1 (x i)) (Finset.mem_univ j)
  refine ⟨i, ?_, hi, ?_, hle⟩
  · intro h0
    have := hle i0
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at this
    exact hi0 this
  · unfold ordVec ord nrm; rw [hi]
end GlobalTheory.Nef.OrdCalc
