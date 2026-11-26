-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45FiniteLargeMarkLimitV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:22:56.834302+00:00
-- url     : https://prove2.me/submissions/a8bcd0b9-8cc2-414c-b096-ffa65a145860

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise45NonnegativeTimeExtensionV2
open MeasureTheory Filter Set Topology
open scoped MeasureTheory NNReal ENNReal Classical Topology
set_option autoImplicit false
theorem solution
(R : Measure (ℝ × ℝ)) (t : NNReal) (S : Finset NNReal) (j : NNReal → ℝ)
    (hS : ∀ r ∈ S, 0 < r)
    (hR : R.restrict (Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1/2 < |x|}) =
      ∑ r ∈ S, Measure.dirac ((r : ℝ),j r))
    (L : ℕ → NNReal → ℝ) (Y : NNReal → ℝ) (g : ℝ → ℝ → ℝ)
    (hg : ContinuousOn (fun z : ℝ × ℝ => g z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hConv : ∀ s : NNReal, 0 < s → Tendsto (fun n => L n s) atTop (nhds (Y s))) :
    Tendsto (fun n => ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
      z.2 * g z.1 (L n z.1.toNNReal) ∂ R) atTop
      (nhds (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
        z.2 * g z.1 (Y z.1.toNNReal) ∂ R)) := by
  let A : Set (ℝ × ℝ) := Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1/2 < |x|}
  let B : Set (ℝ × ℝ) := Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}
  have hBA : B ⊆ A := fun z hz => ⟨hz.1,lt_of_lt_of_le (show (1/2 : ℝ) < 1 by norm_num) hz.2⟩
  have hBM : MeasurableSet B := measurableSet_Icc.prod (measurableSet_le measurable_const measurable_id.abs)
  have hμ : R.restrict B = (∑ r ∈ S, Measure.dirac ((r : ℝ),j r)).restrict B := by
    rw [← hR,Measure.restrict_restrict_of_subset hBA]
  have hlim : Tendsto (fun n => ∫ z in B, z.2 * g z.1 (L n z.1.toNNReal) ∂ R)
      atTop (nhds (∫ z in B, z.2 * g z.1 (Y z.1.toNNReal) ∂ R)) := by
    have hEq (g : ℝ × ℝ → ℝ) : (∫ z in B, g z ∂ R) =
        ∑ r ∈ S, B.indicator g ((r : ℝ),j r) := by
      rw [hμ,← integral_indicator hBM,integral_finsetSum_measure]
      · simp_rw [integral_dirac]
      · intro r hr
        exact integrable_dirac (by simp)
    simp_rw [hEq]
    apply tendsto_finset_sum
    intro r hr
    have hp := hS r hr
    let z : ℝ × ℝ := ((r : ℝ),j r)
    change Tendsto (fun n => B.indicator (fun z => z.2 * g z.1 (L n z.1.toNNReal)) z)
      atTop (nhds (B.indicator (fun z => z.2 * g z.1 (Y z.1.toNNReal)) z))
    by_cases hz : z ∈ B
    · simp only [Set.indicator_of_mem hz]
      have h := hConv r hp
      have hc := Kyprianou.Ch04.exercise45NonnegativeTimeExtensionV2 g hg
      have hpairs : Tendsto (fun n => ((r : ℝ),L n r)) atTop (nhds ((r : ℝ),Y r)) :=
        tendsto_const_nhds.prodMk_nhds h
      have hh := (hc.continuousAt.tendsto.comp hpairs)
      simpa [z,max_eq_left r.coe_nonneg] using ((tendsto_const_nhds (x := j r)).mul hh)
    · simp only [Set.indicator_of_notMem hz]
      exact tendsto_const_nhds
  exact hlim
