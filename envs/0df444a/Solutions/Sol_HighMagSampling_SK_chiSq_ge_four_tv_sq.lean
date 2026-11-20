-- Prove2me | solution 1 for HighMagSampling.SK.chiSq_ge_four_tv_sq
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T15:02:29.318489+00:00
-- url     : https://prove2.me/submissions/9d60dba4-9b2b-4298-a60f-1ddfa7132d15

import Mathlib
import Definitions.Def_PolySampIso_Divergences

open MeasureTheory
open scoped ENNReal

/-- Cauchy–Schwarz for real integrals, via Hölder with `p = q = 2`. -/
lemma cs_abs {Ω : Type*} [MeasurableSpace Ω] {π : Measure Ω} {h g : Ω → ℝ}
    (hh : MemLp h 2 π) (hg : MemLp g 2 π) :
    |∫ x, h x * g x ∂π| ≤ Real.sqrt (∫ x, h x ^ 2 ∂π) * Real.sqrt (∫ x, g x ^ 2 ∂π) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hh' : MemLp (fun x => |h x|) (ENNReal.ofReal 2) π := by
    rw [ENNReal.ofReal_ofNat]; exact hh.abs
  have hg' : MemLp (fun x => |g x|) (ENNReal.ofReal 2) π := by
    rw [ENNReal.ofReal_ofNat]; exact hg.abs
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (ae_of_all _ (fun x => abs_nonneg (h x)))
    (ae_of_all _ (fun x => abs_nonneg (g x))) hh' hg'
  have e1 : ∀ f : Ω → ℝ, (∫ x, |f x| ^ (2 : ℝ) ∂π) = ∫ x, f x ^ 2 ∂π := fun f => by
    congr 1; funext x; rw [Real.rpow_two, sq_abs]
  rw [e1, e1, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hH
  calc |∫ x, h x * g x ∂π| ≤ ∫ x, |h x * g x| ∂π := abs_integral_le_integral_abs
    _ = ∫ x, |h x| * |g x| ∂π := by congr 1; funext x; exact abs_mul _ _
    _ ≤ _ := hH

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ π : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure π] :
    ENNReal.ofReal (4 * PolySampIso.tvDist μ π ^ 2) ≤ PolySampIso.chiSq μ π := by
  classical
  by_cases hac : μ ≪ π
  swap
  · simp [PolySampIso.chiSq, hac]
  set f : Ω → ℝ := fun x => (μ.rnDeriv π x).toReal with hf
  set g : Ω → ℝ := fun x => f x - 1 with hg
  have hchi : PolySampIso.chiSq μ π = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂π := by
    simp [PolySampIso.chiSq, hac, hg, hf]
  rw [hchi]
  set C := ∫⁻ x, ‖g x‖ₑ ^ 2 ∂π with hC
  by_cases hCt : C = ⊤
  · rw [hCt]; exact le_top
  have hfm : Measurable f := (Measure.measurable_rnDeriv μ π).ennreal_toReal
  have hgm : AEStronglyMeasurable g π := (hfm.sub_const 1).aestronglyMeasurable
  have hgsq : ∀ x, ENNReal.ofReal (g x ^ 2) = ‖g x‖ₑ ^ 2 := by
    intro x
    rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg _), ← Real.enorm_eq_ofReal_abs]
  have hint2 : Integrable (fun x => g x ^ 2) π := by
    refine ⟨hgm.pow 2, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x => sq_nonneg _))]
    simp_rw [hgsq]; exact lt_top_iff_ne_top.mpr hCt
  have hgL2 : MemLp g 2 π := (memLp_two_iff_integrable_sq hgm).mpr hint2
  have hG : ∫ x, g x ^ 2 ∂π = C.toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun x => sq_nonneg _)) (hgm.pow 2)]
    simp_rw [hgsq]
    rfl
  have hfint : Integrable f π := Measure.integrable_toReal_rnDeriv
  have hf1 : ∫ x, f x ∂π = 1 := by
    rw [hf, Measure.integral_toReal_rnDeriv hac, probReal_univ]
  -- bound for each set
  have hB : ∀ B : {B : Set Ω // MeasurableSet B},
      |μ.real B.1 - π.real B.1| ≤ Real.sqrt (C.toReal) / 2 := by
    rintro ⟨B, hBm⟩
    set c := π.real B with hc
    set h : Ω → ℝ := fun x => B.indicator (fun _ => (1 : ℝ)) x - c with hh
    have hhm : Measurable h := (measurable_const.indicator hBm).sub_const c
    have hhb : ∀ x, |h x| ≤ 1 := by
      intro x
      have hc0 : 0 ≤ c := measureReal_nonneg
      have hc1 : c ≤ 1 := by rw [hc]; exact measureReal_le_one
      by_cases hx : x ∈ B <;> simp [hh, hx, abs_le] <;> constructor <;> linarith
    have hhL2 : MemLp h 2 π :=
      MemLp.of_bound hhm.aestronglyMeasurable 1 (ae_of_all _ (fun x => by simpa using hhb x))
    -- the covariance identity
    have hcov : ∫ x, h x * g x ∂π = μ.real B - c := by
      have hgint : Integrable g π := hfint.sub (integrable_const 1)
      have e : (fun x => h x * g x) = fun x => B.indicator g x - c * g x := by
        funext x; by_cases hx : x ∈ B <;> simp [hh, hx] <;> ring
      rw [e, integral_sub (hgint.indicator hBm) (hgint.const_mul c), integral_indicator hBm,
        integral_const_mul, hg, integral_sub hfint (integrable_const 1), hf1,
        integral_sub hfint.integrableOn (integrable_const 1).integrableOn,
        Measure.setIntegral_toReal_rnDeriv hac B]
      simp [hc, measureReal_restrict_apply_univ]
    -- variance of the indicator
    have hvar : ∫ x, h x ^ 2 ∂π = c * (1 - c) := by
      have e : (fun x => h x ^ 2) = fun x => (1 - 2 * c) * B.indicator (fun _ => (1 : ℝ)) x + c ^ 2 := by
        funext x; by_cases hx : x ∈ B <;> simp [hh, hx] <;> ring
      rw [e, integral_add ((integrable_const _).indicator hBm |>.const_mul _) (integrable_const _),
        integral_const_mul, integral_indicator hBm, integral_const, integral_const]
      simp [hc, measureReal_restrict_apply_univ]; ring
    have hq : Real.sqrt (c * (1 - c)) ≤ 1 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; nlinarith [sq_nonneg (c - 1 / 2)]
    have := cs_abs hhL2 hgL2
    rw [hcov, hvar, hG] at this
    calc |μ.real B - π.real B| ≤ Real.sqrt (c * (1 - c)) * Real.sqrt C.toReal := this
      _ ≤ 1 / 2 * Real.sqrt C.toReal := by gcongr
      _ = _ := by ring
  have hTV : PolySampIso.tvDist μ π ≤ Real.sqrt (C.toReal) / 2 := by
    unfold PolySampIso.tvDist
    have : Nonempty {B : Set Ω // MeasurableSet B} := ⟨⟨∅, MeasurableSet.empty⟩⟩
    exact ciSup_le hB
  have hTV0 : 0 ≤ PolySampIso.tvDist μ π := by
    unfold PolySampIso.tvDist
    refine le_trans (abs_nonneg (μ.real (∅ : Set Ω) - π.real ∅)) ?_
    exact le_ciSup (f := fun B : {B : Set Ω // MeasurableSet B} => |μ.real B.1 - π.real B.1|)
      ⟨Real.sqrt (C.toReal) / 2, by rintro _ ⟨B, rfl⟩; exact hB B⟩ ⟨∅, MeasurableSet.empty⟩
  rw [← ENNReal.ofReal_toReal hCt]
  refine ENNReal.ofReal_le_ofReal ?_
  have hs := Real.sq_sqrt (ENNReal.toReal_nonneg (a := C))
  nlinarith [Real.sqrt_nonneg C.toReal]
