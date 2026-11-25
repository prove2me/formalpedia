-- Prove2me | solution 1 for Kyprianou.Ch04.klsGeneralRegionVarianceBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:45:31.618372+00:00
-- url     : https://prove2.me/submissions/f85e269d-a596-4861-a8a0-779c480a84e7

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_compensatedGeneralRegionMartingaleCh02V3
import Theorems.Thm_Kyprianou_Ch02_realMarkSimpleL2ApproxV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteIntensityWindowSimpleMarkIntegralTendstoV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteMarkTimeRectIntensityFiniteV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteSimpleMarkRawIntegralL2V1
import Theorems.Thm_Kyprianou_Ch04_l2IntegralLimitV1
import Theorems.Thm_Kyprianou_Ch04_l2SquareIntegralLimitV1
import Theorems.Thm_Kyprianou_Ch04_klsSimpleCenteredMomentV1
import Theorems.Thm_Kyprianou_Ch04_l2FatouSquareLimitV1
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- The centred real marked Poisson integral has second moment bounded by its intensity energy. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν) (B : Set ℝ)
    (hB : MeasurableSet B) (hfinite : ν B < ⊤)
    (hsecond : MemLp (fun x : ℝ => x) 2 (ν.restrict B)) (t : ℝ≥0) :
    let D := fun ω => (∫ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ B, z.2 ∂(N.N ω)) -
        (t : ℝ) * ∫ x in B, x ∂ν
    Integrable (fun ω => (D ω)^2) P ∧
      (∫ ω, (D ω)^2 ∂P) ≤ (t : ℝ) * ∫ x in B, x^2 ∂ν := by
  dsimp only
  letI : IsFiniteMeasure (ν.restrict B) := isFiniteMeasure_restrict.mpr hfinite.ne
  obtain ⟨g,hg,hg2⟩ := Kyprianou.Ch02.realMarkSimpleL2ApproxV1 ν B hsecond
  have hgLp (n : ℕ) : MemLp (fun x => g n x) 2 (ν.restrict B) := by
    classical
    apply MemLp.of_bound (g n).measurable.aestronglyMeasurable
      (∑ r ∈ (g n).range, ‖r‖)
    exact Eventually.of_forall fun x => Finset.single_le_sum
      (fun r _ => norm_nonneg r) ((g n).mem_range_self x)
  have hm := (Kyprianou.Ch04.l2IntegralLimitV1 (ν.restrict B)
    (fun n x => g n x) (fun x => x) hgLp hsecond hg2).const_mul (t : ℝ)
  have hs := (Kyprianou.Ch04.l2SquareIntegralLimitV1 (ν.restrict B)
    (fun n x => g n x) (fun x => x) hgLp hsecond hg2).const_mul (t : ℝ)
  let R := Ioc (0 : ℝ) (t : ℝ) ×ˢ B
  have hR : MeasurableSet R := measurableSet_Ioc.prod hB
  have hRfin : referenceIntensity ν R ≠ ⊤ :=
    Kyprianou.Ch02.prmFiniteMarkTimeRectIntensityFiniteV1 ν B hB hfinite 0 t
  let D : Ω → ℝ := fun ω => (∫ z in R, z.2 ∂(N.N ω)) -
      (t : ℝ) * ∫ x in B, x ∂ν
  let f : ℕ → Ω → ℝ := fun n ω => (∫ z in R, g n z.2 ∂(N.N ω)) -
      (t : ℝ) * ∫ x in B, g n x ∂ν
  have hD : MemLp D 2 P := by
    obtain ⟨F, hF, hM, hLp⟩ := Kyprianou.compensatedGeneralRegionMartingaleCh02V3
      P ν N B hB hfinite (hsecond.integrable (by norm_num))
    exact hLp hsecond t
  have hf (n : ℕ) : MemLp (f n) 2 P :=
    (Kyprianou.Ch02.prmFiniteSimpleMarkRawIntegralL2V1 P ν N R hR hRfin (g n)).sub
      (memLp_const _)
  let Z : ℕ → Ω → ℝ := fun n => (hf n).aestronglyMeasurable.mk (f n)
  have hZ (n : ℕ) : Measurable (Z n) :=
    (hf n).aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have he (n : ℕ) : f n =ᵐ[P] Z n := (hf n).aestronglyMeasurable.ae_eq_mk
  have he2 (n : ℕ) : (fun ω => (f n ω)^2) =ᵐ[P] fun ω => (Z n ω)^2 := by
    filter_upwards [he n] with ω hω
    rw [hω]
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Z n ω) atTop (𝓝 (D ω)) := by
    filter_upwards [ae_all_iff.mpr he,
      Kyprianou.Ch02.prmFiniteIntensityWindowSimpleMarkIntegralTendstoV1
        P ν N R hR hRfin g hg] with ω hω hconv
    have hc : Tendsto (fun n => f n ω) atTop (𝓝 (D ω)) := hconv.sub hm
    exact hc.congr (fun n => hω n)
  have hmoment (n : ℕ) : (∫ ω, (Z n ω)^2 ∂P) =
      (t : ℝ) * ∫ x in B, (g n x)^2 ∂ν :=
    (integral_congr_ae (he2 n).symm).trans
      (Kyprianou.Ch04.klsSimpleCenteredMomentV1 P ν N B hB hfinite (g n) t).2
  have hlimit : Tendsto (fun n => ∫ ω, (Z n ω)^2 ∂P) atTop
      (𝓝 ((t : ℝ) * ∫ x in B, x^2 ∂ν)) := hs.congr (fun n => (hmoment n).symm)
  exact ⟨hD.integrable_sq, Kyprianou.Ch04.l2FatouSquareLimitV1 P Z D _
    (mul_nonneg t.coe_nonneg (integral_nonneg fun x => sq_nonneg x)) hZ
    (fun n => (hf n).integrable_sq.congr (he2 n)) hD.integrable_sq hlim hlimit⟩
