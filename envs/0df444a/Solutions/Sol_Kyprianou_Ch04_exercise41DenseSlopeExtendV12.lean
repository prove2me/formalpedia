-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41DenseSlopeExtendV12
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:54:29.751854+00:00
-- url     : https://prove2.me/submissions/0b765cd1-cbfc-4349-984c-8a6a1795a937

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41DenseRightHitV4
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    (x : NNReal → ℝ) (q : ℕ → NNReal) (hq : DenseRange q)
    (hR : ∀ u, ContinuousWithinAt x (Ici u) u)
    (c : ℝ) (δ : NNReal)
    (h : ∀ k, 0 < q k → q k < δ → c * (q k : ℝ) ≤ x (q k)) :
    ∀ u : NNReal, 0 < u → u < δ → c * (u : ℝ) ≤ x u := by
  intro u hu hδ
  by_contra hn
  let f : NNReal → ℝ := fun v => x v - c * (v : ℝ)
  have hf : f u < 0 := sub_neg.mpr (lt_of_not_ge hn)
  have hF : ContinuousWithinAt (fun v => f v - f u) (Ici u) u := by
    have hc : Continuous (fun v : NNReal => c * (v : ℝ)) := by fun_prop
    exact ((hR u).sub hc.continuousAt.continuousWithinAt).sub continuousWithinAt_const
  obtain ⟨k,huk,hk,hv⟩ := exercise41DenseRightHitV4
    (fun v => f v - f u) q hq u (δ : ℝ) (-f u) (by exact_mod_cast hδ)
    (by linarith) hF (sub_self _)
  have hqδ : q k < δ := by exact_mod_cast hk
  have hq0 := hu.trans_le huk
  have hfk : 0 ≤ f (q k) := sub_nonneg.mpr (h k hq0 hqδ)
  have H := (abs_lt.mp hv).2
  linarith
