-- Prove2me | solution 1 for GlobalTheory.SumSmulAeEq.coeFn_sum_smul_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:58:41.911417+00:00
-- url     : https://prove2.me/submissions/7e9ca113-f9c3-4bc9-b691-6edc0e25556c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CoeFnSumSmulAeEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SumSmulAeEq
open MeasureTheory
namespace GlobalTheory.SumSmulAeEq
theorem _root_.solution {X ι : Type} [MeasurableSpace X] (μ : Measure X) (s : Finset ι)
    (c : ι → ℂ) (y : ι → Lp ℂ (2 : ENNReal) μ) (F : ι → X → ℂ)
    (h : ∀ i, (y i : X → ℂ) =ᵐ[μ] F i) :
    ((∑ i ∈ s, c i • y i : Lp ℂ (2 : ENNReal) μ) : X → ℂ) =ᵐ[μ]
      fun x => ∑ i ∈ s, c i * F i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 μ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (c a • y a) (∑ i ∈ s, c i • y i), Lp.coeFn_smul (c a) (y a),
      h a, ih] with x h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, h4, Finset.sum_insert ha, Pi.smul_apply, h3, smul_eq_mul]
end GlobalTheory.SumSmulAeEq
