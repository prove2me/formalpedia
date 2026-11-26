-- Prove2me | solution 1 for Kyprianou.Ch04.finiteWindowWeightedL2V1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T22:50:02.427015+00:00
-- url     : https://prove2.me/submissions/971df056-94e9-4763-a850-38f952f91c40

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_prmFiniteIntensityCountRealL2V1
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A measurable bounded-kernel compensated finite-window integral is square integrable. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν) (B : Set ℝ)
    (hB : MeasurableSet B) (hfin : ν B < ⊤) (T : NNReal)
    (K : ℝ) (hK : 0 ≤ K) (g : ℝ → ℝ → Ω → ℝ)
    (hg : ∀ s x ω, 0 ≤ s → x ∈ B → |g s x ω| ≤ K)
    (M : Ω → ℝ) (hM : AEStronglyMeasurable M P)
    (hrep : ∀ ω, M ω =
      (∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ B, g z.1 z.2 ω ∂(N.N ω)) -
      ∫ s in Icc (0 : ℝ) (T : ℝ), (∫ x in B, g s x ω ∂ν) ∂volume) :
    MemLp M 2 P := by
  let R : Set (ℝ × ℝ) := Icc (0 : ℝ) (T : ℝ) ×ˢ B
  have hR : MeasurableSet R := measurableSet_Icc.prod hB
  have hRf : referenceIntensity ν R ≠ ⊤ := by
    dsimp [R]
    rw [referenceIntensity, Measure.prod_prod, Measure.restrict_apply measurableSet_Icc]
    rw [inter_eq_left.mpr (show Icc (0 : ℝ) (T : ℝ) ⊆ Ici 0 from fun x hx => hx.1)]
    rw [Real.volume_Icc, sub_zero]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne
  have hcount := Kyprianou.Ch02.prmFiniteIntensityCountRealL2V1 P ν N R hR hRf
  have hdom : MemLp (fun ω => K * (N.N ω R).toReal + K * (ν B).toReal * (T : ℝ)) 2 P :=
    (hcount.const_mul K).add (memLp_const _)
  apply hdom.mono' hM
  filter_upwards [N.integer_valued hR hRf] with ω hω
  obtain ⟨n, hn⟩ := hω
  have hraw : |∫ z in R, g z.1 z.2 ω ∂(N.N ω)| ≤ K * (N.N ω R).toReal := by
    haveI : IsFiniteMeasure ((N.N ω).restrict R) := isFiniteMeasure_restrict.mpr
      (by rw [hn]; exact ENNReal.natCast_ne_top n)
    simpa only [Real.norm_eq_abs, measureReal_def, Measure.restrict_apply_univ] using
      (norm_integral_le_of_norm_le_const (μ := (N.N ω).restrict R)
        (f := fun z : ℝ × ℝ => g z.1 z.2 ω)
        ((ae_restrict_mem hR).mono (fun z hz => by rw [Real.norm_eq_abs]; exact hg z.1 z.2 ω hz.1.1 hz.2)))
  haveI : IsFiniteMeasure (ν.restrict B) := isFiniteMeasure_restrict.mpr hfin.ne
  have hinner (s : ℝ) (hs : 0 ≤ s) : |∫ x in B, g s x ω ∂ν| ≤ K * (ν B).toReal := by
    simpa only [Real.norm_eq_abs, measureReal_def, Measure.restrict_apply_univ] using
      (norm_integral_le_of_norm_le_const (μ := ν.restrict B) (f := fun x => g s x ω)
        ((ae_restrict_mem hB).mono (fun x hx => by rw [Real.norm_eq_abs]; exact hg s x ω hs hx)))
  have hcomp : |∫ s in Icc (0 : ℝ) (T : ℝ), (∫ x in B, g s x ω ∂ν) ∂volume| ≤
      K * (ν B).toReal * (T : ℝ) := by
    have h := norm_integral_le_of_norm_le_const
      (μ := volume.restrict (Icc (0 : ℝ) (T : ℝ)))
      (f := fun s => ∫ x in B, g s x ω ∂ν)
      ((ae_restrict_mem measurableSet_Icc).mono (fun s hs => by rw [Real.norm_eq_abs]; exact hinner s hs.1))
    simpa only [Real.norm_eq_abs, measureReal_def, Measure.restrict_apply_univ,
      Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal T.coe_nonneg] using h
  rw [Real.norm_eq_abs, hrep]
  exact (abs_sub _ _).trans (add_le_add hraw hcomp)
