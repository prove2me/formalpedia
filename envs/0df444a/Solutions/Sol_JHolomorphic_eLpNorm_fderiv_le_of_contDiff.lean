-- Prove2me | solution 1 for JHolomorphic.eLpNorm_fderiv_le_of_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T17:31:16.130284+00:00
-- url     : https://prove2.me/submissions/1368d37e-8da0-4b26-8c42-c1cfe812fdc0

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_DbarRegularity_cauchyRiemann_lp_complex
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality



namespace JHolomorphic

open MeasureTheory

/-- For `1 < p < ∞` and a complex structure `J₀` on the finite-dimensional real space `E` there is
`C` such that every `C¹` map `g : ℂ → E` with compact support satisfies
`‖g_s‖_p + ‖g_t‖_p ≤ C ‖g_s + J₀ g_t‖_p`. -/
theorem eLpNorm_fderiv_le_of_contDiff_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (p : ℝ) (hp : 1 < p) (J₀ : E →L[ℝ] E)
    (hJ₀ : J₀.comp J₀ = -ContinuousLinearMap.id ℝ E) :
    ∃ C : ℝ, ∀ g : ℂ → E, ContDiff ℝ 1 g → HasCompactSupport g →
      eLpNorm (fun z => fderiv ℝ g z 1) (ENNReal.ofReal p) volume +
          eLpNorm (fun z => fderiv ℝ g z Complex.I) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C *
          eLpNorm (fun z => fderiv ℝ g z 1 + J₀ (fderiv ℝ g z Complex.I)) (ENNReal.ofReal p)
            volume := by
  have hJalg : ∀ (ℓ : E →L[ℝ] ℝ) (w : E),
      ((ℓ w : ℂ) - Complex.I * (ℓ (J₀ w) : ℂ)) * Complex.I + 0 =
        (ℓ (J₀ w) : ℂ) - Complex.I * (ℓ (J₀ (J₀ w)) : ℂ) := by
    intro ℓ w
    have h : J₀ (J₀ w) = -w := by
      simpa using congrArg (fun T : E →L[ℝ] E => T w) hJ₀
    rw [h, map_neg]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  obtain ⟨A, hA⟩ := DbarRegularity.cauchyRiemann_lp_complex p hp
  set q := ENNReal.ofReal p with hq
  have hq1 : 1 ≤ q := by rw [hq]; exact ENNReal.one_le_ofReal.2 hp.le
  let b := Module.finBasis ℝ E
  let ℓ : Fin (Module.finrank ℝ E) → E →L[ℝ] ℝ := fun i =>
    LinearMap.toContinuousLinearMap (b.coord i)
  let L : Fin (Module.finrank ℝ E) → E →L[ℝ] ℂ := fun i =>
    Complex.ofRealCLM.comp (ℓ i) - Complex.I • Complex.ofRealCLM.comp ((ℓ i).comp J₀)
  have hL : ∀ i w, L i w = (ℓ i w : ℂ) - Complex.I * (ℓ i (J₀ w) : ℂ) := by
    intro i w; simp [L]
  have hLJ : ∀ i w, L i (J₀ w) = Complex.I * L i w := by
    intro i w
    rw [hL, hL]
    have := hJalg (ℓ i) w
    rw [add_zero] at this
    rw [← this]; ring
  have hre : ∀ i w, |ℓ i w| ≤ ‖L i w‖ := by
    intro i w
    have : (L i w).re = ℓ i w := by rw [hL]; simp
    rw [← this]; exact Complex.abs_re_le_norm _
  have hnorm : ∀ w : E, ‖w‖ ≤ ∑ i, ‖b i‖ * ‖L i w‖ := by
    intro w
    calc ‖w‖ = ‖∑ i, b.repr w i • b i‖ := by rw [b.sum_repr]
      _ ≤ ∑ i, ‖b.repr w i • b i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖b i‖ * ‖L i w‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, mul_comm]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have : b.repr w i = ℓ i w := by simp [ℓ]
        rw [this, Real.norm_eq_abs]; exact hre i w
  refine ⟨∑ i, ‖b i‖ * (A * ‖L i‖), fun g hg hgc => ?_⟩
  have hdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hcd : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  -- derivatives of the scalar components
  have hfd : ∀ i z, fderiv ℝ (fun x => L i (g x)) z = (L i).comp (fderiv ℝ g z) := by
    intro i z
    exact ((L i).hasFDerivAt.comp z (hdiff z).hasFDerivAt).fderiv
  -- the scalar estimate for each component
  have hcomp : ∀ i, eLpNorm (fun z => L i (fderiv ℝ g z 1)) q volume +
      eLpNorm (fun z => L i (fderiv ℝ g z Complex.I)) q volume ≤
      (A : ENNReal) * (‖L i‖ₑ *
        eLpNorm (fun z => fderiv ℝ g z 1 + J₀ (fderiv ℝ g z Complex.I)) q volume) := by
    intro i
    have h1 := hA (fun x => L i (g x)) ((L i).contDiff.comp hg)
      (hgc.comp_left (map_zero (L i)))
    simp only [hfd, ContinuousLinearMap.comp_apply] at h1
    refine h1.trans ?_
    gcongr ?_ * ?_
    rfl
    have hdb : DbarRegularity.dbar (fun x => L i (g x)) =
        fun z => L i (fderiv ℝ g z 1 + J₀ (fderiv ℝ g z Complex.I)) := by
      funext z
      simp only [DbarRegularity.dbar, hfd, ContinuousLinearMap.comp_apply, map_add, hLJ,
        smul_eq_mul]
    rw [hdb]
    refine (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
      (Filter.Eventually.of_forall fun z => (L i).le_opNNNorm _) q).trans ?_
    rw [ENNReal.smul_def, smul_eq_mul]
    rfl
  -- reduce the `E`-valued norms to the components
  have hred : ∀ v : ℂ, eLpNorm (fun z => fderiv ℝ g z v) q volume ≤
      ∑ i, ‖b i‖ₑ * eLpNorm (fun z => L i (fderiv ℝ g z v)) q volume := by
    intro v
    have hmeas : ∀ i, AEStronglyMeasurable
        (‖b i‖ • fun z => ‖L i (fderiv ℝ g z v)‖) volume := fun i =>
      ((continuous_const.smul ((L i).continuous.comp
        (hcd.clm_apply continuous_const)).norm)).aestronglyMeasurable
    calc eLpNorm (fun z => fderiv ℝ g z v) q volume
        ≤ eLpNorm (∑ i, ‖b i‖ • fun z => ‖L i (fderiv ℝ g z v)‖) q volume := by
          refine eLpNorm_mono fun z => ?_
          rw [Finset.sum_apply, Real.norm_eq_abs, abs_of_nonneg
            (Finset.sum_nonneg fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; positivity)]
          simpa using hnorm (fderiv ℝ g z v)
      _ ≤ ∑ i, eLpNorm (‖b i‖ • fun z => ‖L i (fderiv ℝ g z v)‖) q volume :=
          eLpNorm_sum_le (fun i _ => hmeas i) hq1
      _ = ∑ i, ‖b i‖ₑ * eLpNorm (fun z => L i (fderiv ℝ g z v)) q volume := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [eLpNorm_const_smul, eLpNorm_norm, enorm_norm]
  calc _ ≤ ∑ i, ‖b i‖ₑ * eLpNorm (fun z => L i (fderiv ℝ g z 1)) q volume +
        ∑ i, ‖b i‖ₑ * eLpNorm (fun z => L i (fderiv ℝ g z Complex.I)) q volume :=
        add_le_add (hred 1) (hred Complex.I)
    _ = ∑ i, ‖b i‖ₑ * (eLpNorm (fun z => L i (fderiv ℝ g z 1)) q volume +
        eLpNorm (fun z => L i (fderiv ℝ g z Complex.I)) q volume) := by
        rw [← Finset.sum_add_distrib]; simp_rw [mul_add]
    _ ≤ ∑ i, ‖b i‖ₑ * ((A : ENNReal) * (‖L i‖ₑ *
        eLpNorm (fun z => fderiv ℝ g z 1 + J₀ (fderiv ℝ g z Complex.I)) q volume)) :=
        Finset.sum_le_sum fun i _ => by gcongr; exact hcomp i
    _ = ENNReal.ofReal (∑ i, ‖b i‖ * (A * ‖L i‖)) *
        eLpNorm (fun z => fderiv ℝ g z 1 + J₀ (fderiv ℝ g z Complex.I)) q volume := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity), Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul A.coe_nonneg,
          ofReal_norm, ofReal_norm, ENNReal.ofReal_coe_nnreal]
        ring

end JHolomorphic

open JHolomorphic

open MeasureTheory

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (p : ℝ) (hp : 1 < p) (J₀ : E →L[ℝ] E)
    (hJ₀ : J₀.comp J₀ = -ContinuousLinearMap.id ℝ E) :
    ∃ C : ℝ, ∀ g : ℂ → E, ContDiff ℝ 1 g → HasCompactSupport g →
      eLpNorm (fun z => fderiv ℝ g z 1) (ENNReal.ofReal p) volume +
          eLpNorm (fun z => fderiv ℝ g z Complex.I) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C *
          eLpNorm (fun z => fderiv ℝ g z 1 + J₀ (fderiv ℝ g z Complex.I)) (ENNReal.ofReal p)
            volume :=
  JHolomorphic.eLpNorm_fderiv_le_of_contDiff_aux p hp J₀ hJ₀
