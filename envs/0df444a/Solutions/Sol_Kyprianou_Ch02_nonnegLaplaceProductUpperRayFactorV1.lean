-- Prove2me | solution 1 for Kyprianou.Ch02.nonnegLaplaceProductUpperRayFactorV1
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T02:49:13.20182+00:00
-- url     : https://prove2.me/submissions/279b60f5-f697-40e3-b89f-415e67ce47db

import Theorems.Thm_Kyprianou_Ch02_nonnegRVLawEqOfLaplaceV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter Set Real
open scoped NNReal ENNReal Topology ProbabilityTheory
set_option autoImplicit false
set_option linter.unusedVariables false

/-!
Joint Laplace product ⇒ restricted upper-ray ENNReal Laplace factor.

Esscher-tilt `Q := P.tilted (-β • B)`. Factorisation + `integral_exp_tilted`
make the Laplace of `A` tilt-invariant, so `nonnegRVLawEqOfLaplaceV1` yields
`P.map A = Q.map A`. Evaluating the ray `{A > a}` and rewriting via
`tilted_apply_eq_ofReal_integral'` gives the required ENNReal factorisation.
-/

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : Ω → ℝ) (hmA : Measurable A) (hmB : Measurable B)
    (hnA : ∀ ω, 0 ≤ A ω) (hnB : ∀ ω, 0 ≤ B ω)
    (h : ∀ u v : ℝ, 0 < u → 0 < v →
      (∫ ω, Real.exp (-(u * A ω + v * B ω)) ∂P) =
      (∫ ω, Real.exp (-(u * A ω)) ∂P) * (∫ ω, Real.exp (-(v * B ω)) ∂P))
    (a β : ℝ) (ha : 0 ≤ a) (hβ : 0 < β) :
    (∫⁻ ω in A ⁻¹' Set.Ioi a,
        ENNReal.ofReal (Real.exp (-(β * B ω))) ∂P) =
      P (A ⁻¹' Set.Ioi a) *
        (∫⁻ ω, ENNReal.ofReal (Real.exp (-(β * B ω))) ∂P) := by
  -- Esscher tilt by -β B
  let f : Ω → ℝ := fun ω => -(β * B ω)
  have hf_meas : Measurable f := by fun_prop
  have hf_int : Integrable (fun ω => Real.exp (f ω)) P := by
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun ω => ?_)
    have hmul : 0 ≤ β * B ω := mul_nonneg hβ.le (hnB ω)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by simp [f, hmul])
  have hZpos : 0 < ∫ ω, Real.exp (f ω) ∂P := integral_exp_pos hf_int
  let Z : ℝ := ∫ ω, Real.exp (f ω) ∂P
  have hZ_ne : Z ≠ 0 := ne_of_gt hZpos
  let Q : Measure Ω := P.tilted f
  haveI hQ : IsProbabilityMeasure Q := isProbabilityMeasure_tilted hf_int
  -- Laplace of A is tilt-invariant
  have hLap (u : ℝ) (hu : 0 < u) :
      (∫ ω, Real.exp (-(u * A ω)) ∂Q) = ∫ ω, Real.exp (-(u * A ω)) ∂P := by
    have htilt := integral_exp_tilted (μ := P) f (fun ω => -(u * A ω))
    -- htilt: ∫ exp(-uA) dQ = ∫ exp(f-uA) / ∫ exp(f)
    dsimp [Q]
    rw [htilt]
    have hfac := h u β hu hβ
    have hsum :
        (∫ ω, Real.exp ((f + fun ω => -(u * A ω)) ω) ∂P) =
          ∫ ω, Real.exp (-(u * A ω + β * B ω)) ∂P := by
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      simp [f, Pi.add_apply, add_comm, add_left_comm, add_assoc]
    have hfB : (∫ ω, Real.exp (f ω) ∂P) = ∫ ω, Real.exp (-(β * B ω)) ∂P := rfl
    rw [hsum, hfac, hfB]
    -- (X * Y) / Y = X
    have hY : ∫ ω, Real.exp (-(β * B ω)) ∂P ≠ 0 := by
      simpa [hfB] using hZ_ne
    exact mul_div_cancel_right₀ _ hY
  -- Laws of A agree
  have hlaw : P.map A = Q.map A :=
    Kyprianou.Ch02.nonnegRVLawEqOfLaplaceV1 P Q A A hmA hmA hnA hnA fun s hs =>
      (hLap s hs).symm
  -- Ray probabilities agree
  have hAset : MeasurableSet (A ⁻¹' Ioi a) := hmA measurableSet_Ioi
  have hQeq : Q (A ⁻¹' Ioi a) = P (A ⁻¹' Ioi a) := by
    have := congrArg (fun μ : Measure ℝ => μ (Ioi a)) hlaw
    simpa [Measure.map_apply hmA measurableSet_Ioi] using this.symm
  -- Pull constant denominator out of the tilted ray measure
  have hQform :
      Q (A ⁻¹' Ioi a) =
        ENNReal.ofReal ((∫ ω in A ⁻¹' Ioi a, Real.exp (f ω) ∂P) / Z) := by
    have hraw := tilted_apply_eq_ofReal_integral' (μ := P) f hAset
    -- raw integrates (exp(f)/∫exp(f)) pointwise
    have hpull :
        (∫ ω in A ⁻¹' Ioi a, Real.exp (f ω) / Z ∂P) =
          (∫ ω in A ⁻¹' Ioi a, Real.exp (f ω) ∂P) / Z := by
      simp [div_eq_inv_mul, ← integral_const_mul]
    -- identify Z with ∫ exp(f)
    have hZdef : Z = ∫ ω, Real.exp (f ω) ∂P := rfl
    -- rewrite hraw's denominator
    have hraw' :
        Q (A ⁻¹' Ioi a) =
          ENNReal.ofReal (∫ ω in A ⁻¹' Ioi a, Real.exp (f ω) / Z ∂P) := by
      simpa [Q, hZdef] using hraw
    rw [hraw', hpull]
  -- Convert: ∫_ray exp(f) = P(ray).toReal * Z
  have hfactor_real :
      (∫ ω in A ⁻¹' Ioi a, Real.exp (f ω) ∂P) =
        (P (A ⁻¹' Ioi a)).toReal * Z := by
    have hpos : 0 ≤ ∫ ω in A ⁻¹' Ioi a, Real.exp (f ω) ∂P :=
      integral_nonneg fun _ => (Real.exp_pos _).le
    have hof :
        ENNReal.ofReal ((∫ ω in A ⁻¹' Ioi a, Real.exp (f ω) ∂P) / Z) =
          P (A ⁻¹' Ioi a) := by
      rw [← hQform, hQeq]
    have hdiv :
        (∫ ω in A ⁻¹' Ioi a, Real.exp (f ω) ∂P) / Z =
          (P (A ⁻¹' Ioi a)).toReal := by
      have hnn : 0 ≤ (∫ ω in A ⁻¹' Ioi a, Real.exp (f ω) ∂P) / Z :=
        div_nonneg hpos hZpos.le
      calc
        (∫ ω in A ⁻¹' Ioi a, Real.exp (f ω) ∂P) / Z
            = (ENNReal.ofReal
                ((∫ ω in A ⁻¹' Ioi a, Real.exp (f ω) ∂P) / Z)).toReal :=
              (ENNReal.toReal_ofReal hnn).symm
        _ = (P (A ⁻¹' Ioi a)).toReal := by rw [hof]
    have := congrArg (fun x : ℝ => x * Z) hdiv
    simpa [div_mul_cancel₀ _ hZ_ne] using this
  -- ENNReal form
  have hLray :
      (∫⁻ ω in A ⁻¹' Ioi a, ENNReal.ofReal (Real.exp (f ω)) ∂P) =
        ENNReal.ofReal (∫ ω in A ⁻¹' Ioi a, Real.exp (f ω) ∂P) := by
    refine (ofReal_integral_eq_lintegral_ofReal ?_ ?_).symm
    · exact hf_int.integrableOn
    · exact ae_restrict_of_ae (ae_of_all _ fun _ => (Real.exp_pos _).le)
  have hLall :
      (∫⁻ ω, ENNReal.ofReal (Real.exp (f ω)) ∂P) =
        ENNReal.ofReal Z := by
    refine (ofReal_integral_eq_lintegral_ofReal hf_int
      (ae_of_all _ fun _ => (Real.exp_pos _).le)).symm
  rw [hLray, hLall, hfactor_real]
  -- ofReal(P.toReal * Z) = P * ofReal Z
  have : ENNReal.ofReal ((P (A ⁻¹' Ioi a)).toReal * Z) =
      P (A ⁻¹' Ioi a) * ENNReal.ofReal Z := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  simpa [f] using this
