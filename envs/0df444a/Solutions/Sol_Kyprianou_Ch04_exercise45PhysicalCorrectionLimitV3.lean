-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45PhysicalCorrectionLimitV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:20:04.615795+00:00
-- url     : https://prove2.me/submissions/3610529a-969a-4bfb-adac-c517a231d5b4

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise45ClosedWindowPositiveTimeV2
import Theorems.Thm_Kyprianou_Ch04_exercise45FullSquareEnergyV2
import Theorems.Thm_Kyprianou_Ch04_exercise45CorrectionDCTV2
open MeasureTheory Filter Set Topology
open scoped MeasureTheory NNReal ENNReal Classical Topology
set_option autoImplicit false
theorem solution
(R : Measure (ℝ × ℝ)) (t : NNReal) (hzero : R ({0} ×ˢ (univ : Set ℝ)) = 0)
    (hEn : Integrable (fun z : ℝ × ℝ => min (1 : ℝ) (z.2^2))
      (R.restrict (Ioc (0 : ℝ) (t : ℝ) ×ˢ univ)))
    (S : Finset NNReal) (j : NNReal → ℝ)
    (hR : R.restrict (Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1/2 < |x|}) =
      ∑ r ∈ S, Measure.dirac ((r : ℝ),j r))
    (f g : ℝ → ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hf : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hg : ContinuousOn (fun z : ℝ × ℝ => g z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hb : ∀ s x z : ℝ, 0 ≤ s → |f s (x+z)-f s x-z*g s x| ≤ K*z^2)
    (L : ℕ → NNReal → ℝ) (Y : NNReal → ℝ)
    (hL : ∀ n, Measurable (L n)) (hY : Measurable Y)
    (hConv : ∀ s : NNReal, 0 < s → Tendsto (fun n => L n s) atTop (nhds (Y s)))
    (e : ℕ → ℝ) (he : Tendsto e atTop (nhds 0)) :
    Tendsto (fun n => ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | e n < |x|},
      f z.1 (L n z.1.toNNReal+z.2)-f z.1 (L n z.1.toNNReal)-
        z.2*g z.1 (L n z.1.toNNReal) ∂ R)
      atTop (nhds (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ univ,
        f z.1 (Y z.1.toNNReal+z.2)-f z.1 (Y z.1.toNNReal)-
        z.2*g z.1 (Y z.1.toNNReal) ∂ R)) := by
  let A : Set (ℝ × ℝ) := Icc (0 : ℝ) (t : ℝ) ×ˢ univ
  let μ := R.restrict A
  have hμ : μ = R.restrict (Ioc (0 : ℝ) (t : ℝ) ×ˢ univ) :=
    Kyprianou.Ch04.exercise45ClosedWindowPositiveTimeV2 R hzero t
  have hpos : ∀ᵐ z : ℝ × ℝ ∂μ, 0 < z.1 := by
    rw [hμ]
    filter_upwards [ae_restrict_mem (μ := R) (measurableSet_Ioc.prod MeasurableSet.univ :
      MeasurableSet (Ioc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ)))] with z hz
    exact hz.1.1
  have hlarge : Integrable (fun z : ℝ × ℝ => z.2^2)
      (μ.restrict {z : ℝ × ℝ | 1/2 < |z.2|}) := by
    have hB : MeasurableSet {z : ℝ × ℝ | 1/2 < |z.2|} :=
      measurableSet_lt measurable_const measurable_snd.abs
    rw [show μ.restrict {z : ℝ × ℝ | 1/2 < |z.2|} =
      R.restrict (Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1/2 < |x|}) by
        dsimp [μ,A]; rw [Measure.restrict_restrict hB]; congr 1; ext z; simp [and_comm],
      hR]
    exact integrable_finsetSum_measure.mpr fun r hr => integrable_dirac (by simp)
  have hfull := Kyprianou.Ch04.exercise45FullSquareEnergyV2 μ (hμ.symm ▸ hEn) hlarge
  have hd := Kyprianou.Ch04.exercise45CorrectionDCTV2 μ hpos hfull f g K hK
    hf hg hb L Y hL hY hConv e he
  apply hd.congr
  intro n
  congr 1
  dsimp [μ,A]
  rw [Measure.restrict_restrict (measurableSet_lt measurable_const measurable_snd.abs)]
  congr 1
  ext z
  simp [and_comm]
