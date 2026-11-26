-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41NoLocalMinimumFromNullWindowsV25
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:35:39.621139+00:00
-- url     : https://prove2.me/submissions/03220945-2d1b-4820-8e32-75b8dc8a496c

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41WindowStartGeometryV25
import Theorems.Thm_Kyprianou_Ch04_exercise41GridMinimumAtZeroV24
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    (x : NNReal → ℝ) (q : ℕ → NNReal) (hq : DenseRange q)
    (hR : ∀ t, ContinuousWithinAt x (Ici t) t)
    (hNull : ∀ j : ℕ, volume {r : ℝ | 0 ≤ r ∧ x r.toNNReal +
      (⨅ k : ℕ, (x (r.toNNReal+min (q k) (q j)) - x r.toNNReal)) = 0} = 0) :
    ∀ s : NNReal, 0 < s → x s = 0 →
      ¬ (∃ e : NNReal, 0 < e ∧ ∀ u ∈ Icc (s-e) (s+e), 0 ≤ x u) := by
  intro s hs hz hmin
  obtain ⟨e,he,hE⟩ := hmin
  have hm : 0 < min e s := lt_min he hs
  obtain ⟨y,hy,⟨j,rfl⟩⟩ := hq.inter_open_nonempty (Ioo 0 (min e s)) isOpen_Ioo
    (nonempty_Ioo.mpr hm)
  have hpos : 0 < q j := hy.1
  have hhe : q j < e := hy.2.trans_le (min_le_left _ _)
  have hhs : q j < s := hy.2.trans_le (min_le_right _ _)
  have hN : volume (Ioo ((s : ℝ)-(q j : ℝ)) (s : ℝ)) = 0 := by
    apply measure_mono_null _ (hNull j)
    intro r hr
    obtain ⟨hr0,hrs,hsh,hsub⟩ := exercise41WindowStartGeometryV25 s e (q j) hs hpos hhe hhs r hr
    exact ⟨hr0,exercise41GridMinimumAtZeroV24 x q hq r.toNNReal s (q j) hrs hsh hR
      (fun u hu => hE u (hsub hu)) hz⟩
  rw [Real.volume_Ioo,ENNReal.ofReal_eq_zero] at hN
  have hp : (0 : ℝ) < (q j : ℝ) := by exact_mod_cast hpos
  linarith
