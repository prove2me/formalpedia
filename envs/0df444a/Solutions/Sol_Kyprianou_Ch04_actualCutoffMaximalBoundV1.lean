-- Prove2me | solution 1 for Kyprianou.Ch04.actualCutoffMaximalBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:48:43.73689+00:00
-- url     : https://prove2.me/submissions/9e5e19f9-7fd4-488b-ab1c-0613b493168e

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionMarkedIntegrableAllTimesAEV1
import Theorems.Thm_Kyprianou_Ch04_pathJumpMeasureZeroTimeV1
import Theorems.Thm_Kyprianou_Ch04_zeroTimeRestrictionIccIocV1
import Theorems.Thm_Kyprianou_Ch04_actualCutoffDifferenceBandV1
import Theorems.Thm_Kyprianou_Ch04_klsGeneralRegionMaximalBoundV1
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Actual nested cutoff difference maximal square bound. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (hν : IsLevyMeasure ν) (N : PoissonRandomMeasure.{0,0,0} P ν)
    (X Xleft X2 U V : NNReal → Ω → ℝ) (η ε : ℝ)
    (hη : 0 < η) (hηε : η < ε) (hε : ε < 1)
    (hN : ∀ᵐ ω ∂P, N.N ω = Kyprianou.Ch04.pathJumpMeasure X Xleft ω)
    (hU : ∀ t ω, U t ω = X2 t ω +
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | η < |x| ∧ |x| < 1},
        z.2 ∂(N.N ω)) - (t : ℝ) *
      (∫ x in {x : ℝ | η < |x| ∧ |x| < 1}, x ∂ν))
    (hV : ∀ t ω, V t ω = X2 t ω +
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | ε < |x| ∧ |x| < 1},
        z.2 ∂(N.N ω)) - (t : ℝ) *
      (∫ x in {x : ℝ | ε < |x| ∧ |x| < 1}, x ∂ν))
    (T : NNReal) (hT : 0 < T) :
    Integrable (fun ω => sSup ((fun t : NNReal => |U t ω - V t ω|^2) '' Iic T)) P ∧
      (∫ ω, sSup ((fun t : NNReal => |U t ω - V t ω|^2) '' Iic T) ∂P) ≤
        4 * (T : ℝ) * (∫⁻ z in {z : ℝ | |z| ≤ ε}, ENNReal.ofReal (z^2) ∂ν).toReal := by
  let B : Set ℝ := {z | η < |z| ∧ |z| ≤ ε}
  let C : Set ℝ := {z | |z| ≤ ε}
  have hB : MeasurableSet B := (measurableSet_lt measurable_const measurable_id.abs).inter
    (measurableSet_le measurable_id.abs measurable_const)
  have hfin : ν B < ⊤ := (measure_mono (show B ⊆ {z | η ≤ |z|} from
    fun z hz => hz.1.le)).trans_lt (hν.measure_setOf_abs_ge_lt_top hη)
  have : IsFiniteMeasure (ν.restrict B) := isFiniteMeasure_restrict.mpr hfin.ne
  have hsecond : MemLp (fun z : ℝ => z) 2 (ν.restrict B) := by
    apply MemLp.of_bound measurable_id.aestronglyMeasurable 1
    filter_upwards [ae_restrict_mem hB] with z hz
    rw [Real.norm_eq_abs]
    exact hz.2.trans hε.le
  let D : NNReal → Ω → ℝ := fun t ω =>
    (∫ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ B, z.2 ∂(N.N ω)) -
      (t : ℝ) * ∫ x in B, x ∂ν
  have hm := Kyprianou.Ch04.klsGeneralRegionMaximalBoundV1 P ν N B hB hfin hsecond T hT
  have he := Kyprianou.Ch04.actualCutoffDifferenceBandV1
    P ν hν N X Xleft X2 U V η ε hη hηε hε hN hU hV
  have heq : (fun ω => sSup ((fun t : NNReal => |D t ω|^2) '' Iic T)) =ᵐ[P]
      fun ω => sSup ((fun t : NNReal => |U t ω - V t ω|^2) '' Iic T) := by
    filter_upwards [he] with ω hω
    have hfun : (fun t : NNReal => |D t ω|^2) = fun t => |U t ω - V t ω|^2 := by
      funext t
      rw [hω t]
    rw [hfun]
  have hC : MeasurableSet C := measurableSet_le measurable_id.abs measurable_const
  have hCfin : (∫⁻ z in C, ENNReal.ofReal (z^2) ∂ν) < ⊤ := by
    have h : (∫⁻ z in C, ENNReal.ofReal (z^2) ∂ν) =
        ∫⁻ z in C, ENNReal.ofReal (min 1 (z^2)) ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hC] with z hz
      rw [min_eq_right]
      have hz' : |z| < 1 := hz.trans_lt hε
      nlinarith [sq_abs z, abs_nonneg z]
    rw [h]
    exact (lintegral_mono' Measure.restrict_le_self le_rfl).trans_lt hν.2
  have henergy : (∫ x in B, x^2 ∂ν) ≤
      (∫⁻ z in C, ENNReal.ofReal (z^2) ∂ν).toReal := by
    have hnn : 0 ≤ ∫ x in B, x^2 ∂ν := integral_nonneg fun _ => sq_nonneg _
    have hb := ofReal_integral_eq_lintegral_ofReal hsecond.integrable_sq
      (Eventually.of_forall fun z => sq_nonneg z)
    have hle : (∫⁻ z in B, ENNReal.ofReal (z^2) ∂ν) ≤
        ∫⁻ z in C, ENNReal.ofReal (z^2) ∂ν :=
      lintegral_mono' (Measure.restrict_mono (fun z hz => hz.2) le_rfl) le_rfl
    rw [← hb] at hle
    simpa [ENNReal.toReal_ofReal hnn] using ENNReal.toReal_mono hCfin.ne hle
  refine ⟨hm.1.congr heq,?_⟩
  rw [← integral_congr_ae heq]
  exact hm.2.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
