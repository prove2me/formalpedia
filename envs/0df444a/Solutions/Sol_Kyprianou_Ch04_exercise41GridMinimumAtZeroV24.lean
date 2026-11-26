-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41GridMinimumAtZeroV24
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:09:08.898664+00:00
-- url     : https://prove2.me/submissions/d84086ab-6d61-4ab6-b153-929f01de0cb9

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41DenseRightHitV4
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    (x : NNReal → ℝ) (q : ℕ → NNReal) (hq : DenseRange q)
    (r s h : NNReal) (hrs : r ≤ s) (hsh : s < r+h)
    (hR : ∀ t, ContinuousWithinAt x (Ici t) t)
    (hMin : ∀ u ∈ Icc r (r+h), 0 ≤ x u) (hz : x s = 0) :
    x r + (⨅ k : ℕ, (x (r + min (q k) h) - x r)) = 0 := by
  let f (k : ℕ) := x (r + min (q k) h) - x r
  have hl (k : ℕ) : -x r ≤ f k := by
    have H := hMin (r+min (q k) h) ⟨by simp,add_le_add_right (min_le_right _ _) r⟩
    dsimp [f]
    linarith
  have hb : BddBelow (range f) := ⟨-x r,by rintro _ ⟨k,rfl⟩; exact hl k⟩
  have hge : -x r ≤ ⨅ k, f k := le_ciInf hl
  have hle : (⨅ k, f k) ≤ -x r := by
    by_contra! hn
    let y : NNReal → ℝ := fun u => x (r+u)
    let e : ℝ := (⨅ k, f k) + x r
    have he : 0 < e := by dsimp [e]; linarith
    have hv : s-r < h := (tsub_lt_iff_left hrs).mpr hsh
    have hr : ContinuousWithinAt y (Ici (s-r)) (s-r) := by
      apply (hR (r+(s-r))).comp
      · exact continuousWithinAt_const.add continuousWithinAt_id
      · intro u hu
        change r+(s-r) ≤ r+u
        exact add_le_add_right (show s-r ≤ u from hu) r
    have hy : y (s-r) = 0 := by dsimp [y]; rw [add_tsub_cancel_of_le hrs,hz]
    obtain ⟨k,_,hk,hsmall⟩ := exercise41DenseRightHitV4 y q hq (s-r) (h : ℝ) e
      (by exact_mod_cast hv) he hr hy
    have hkh : q k < h := by exact_mod_cast hk
    have hf : f k < -x r + e := by
      dsimp [f]
      rw [min_eq_left hkh.le]
      change |x (r+q k)| < e at hsmall
      linarith [(abs_lt.mp hsmall).2]
    have H := ciInf_le hb k
    dsimp [e] at hf
    linarith
  change x r + (⨅ k, f k) = 0
  linarith
