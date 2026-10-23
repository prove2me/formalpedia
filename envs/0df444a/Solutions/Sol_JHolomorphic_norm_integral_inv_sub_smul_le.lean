-- Prove2me | solution 1 for JHolomorphic.norm_integral_inv_sub_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T08:48:17.664872+00:00
-- url     : https://prove2.me/submissions/d1578027-35cc-41ee-b72f-1b663524397c

import Definitions.Def_JHolomorphic_Setting
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Complex.Basic



namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal

/-- `w ↦ w⁻¹` restricted to a disc lies in `L^q` for `1 ≤ q < 2`. -/
theorem memLp_indicator_ball_inv {q : ℝ} (hq1 : 1 ≤ q) (hq2 : q < 2) (r : ℝ) :
    MemLp ((ball (0 : ℂ) r).indicator fun w : ℂ => w⁻¹) (ENNReal.ofReal q) volume := by
  have hq0 : 0 < q := by linarith
  rw [memLp_indicator_iff_restrict measurableSet_ball]
  have hmeas : AEStronglyMeasurable (fun w : ℂ => w⁻¹) (volume.restrict (ball 0 r)) :=
    (measurable_inv.aestronglyMeasurable)
  rw [← integrable_norm_rpow_iff hmeas (by simpa using hq0) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq0.le]
  show IntegrableOn (fun w : ℂ => ‖w⁻¹‖ ^ q) (ball 0 r) volume
  simp_rw [norm_inv]
  rw [integrableOn_fun_norm_addHaar volume (f := fun y : ℝ => y⁻¹ ^ q), Complex.finrank_real_complex]
  rcases le_or_gt r 0 with hr | hr
  · rw [Ioo_eq_empty (by linarith)]; exact integrableOn_empty
  refine ((intervalIntegral.integrableOn_Ioo_rpow_iff (s := 1 - q) hr).2 (by linarith)).congr_fun
    (fun y hy => ?_) measurableSet_Ioo
  have hy0 : 0 < y := hy.1
  simp only [smul_eq_mul, pow_one]
  rw [Real.inv_rpow hy0.le, ← Real.rpow_neg hy0.le, Real.rpow_sub hy0, Real.rpow_one,
    Real.rpow_neg hy0.le, div_eq_mul_inv]
  norm_num

set_option maxHeartbeats 400000 in
/-- Sup bound for the Cauchy kernel against compactly supported `L^p` data, `p > 2`. -/
theorem norm_integral_inv_sub_smul_le_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p R : ℝ) (hp : 2 < p) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℂ → E, MemLp g (ENNReal.ofReal p) volume →
      Function.support g ⊆ ball 0 R → ∀ z ∈ ball (0 : ℂ) R,
        Integrable (fun ζ => (z - ζ)⁻¹ • g ζ) ∧
        ‖∫ ζ, (z - ζ)⁻¹ • g ζ‖ ≤ C * (eLpNorm g (ENNReal.ofReal p) volume).toReal := by
  set q : ℝ := p / (p - 1) with hqdef
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent (by linarith)
  have hq1 : 1 ≤ q := by rw [hqdef, le_div_iff₀ (by linarith)]; linarith
  have hq2 : q < 2 := by
    rw [hqdef, div_lt_iff₀ (by linarith)]; linarith
  haveI : ENNReal.HolderTriple (ENNReal.ofReal q) (ENNReal.ofReal p) 1 :=
    ⟨by rw [inv_one, add_comm]; exact hpq.inv_add_inv_ennreal⟩
  obtain ⟨k0, hk0def⟩ : ∃ k0 : ℂ → ℂ, k0 = (ball (0 : ℂ) (2 * R)).indicator fun w : ℂ => w⁻¹ :=
    ⟨_, rfl⟩
  have hk0 : MemLp k0 (ENNReal.ofReal q) volume := hk0def ▸ memLp_indicator_ball_inv hq1 hq2 _
  refine ⟨(eLpNorm k0 (ENNReal.ofReal q) volume).toReal, ENNReal.toReal_nonneg,
    fun g hg hsupp z hz => ?_⟩
  have hmp : MeasurePreserving (fun ζ : ℂ => z - ζ) volume volume :=
    Measure.measurePreserving_sub_left volume z
  obtain ⟨k1, hk1def⟩ : ∃ k1 : ℂ → ℂ, k1 = fun ζ => k0 (z - ζ) := ⟨_, rfl⟩
  have hk1 : MemLp k1 (ENNReal.ofReal q) volume := hk1def ▸ hk0.comp_measurePreserving hmp
  have hk1n : eLpNorm k1 (ENNReal.ofReal q) volume = eLpNorm k0 (ENNReal.ofReal q) volume :=
    hk1def ▸ eLpNorm_comp_measurePreserving hk0.1 hmp
  have hF : (fun ζ => (z - ζ)⁻¹ • g ζ) = k1 • g := by
    funext ζ
    by_cases hζ : ζ ∈ Function.support g
    · have hζR := mem_ball_zero_iff.1 (hsupp hζ)
      have hzR := mem_ball_zero_iff.1 hz
      have : z - ζ ∈ ball (0 : ℂ) (2 * R) := by
        rw [mem_ball_zero_iff]
        calc ‖z - ζ‖ ≤ ‖z‖ + ‖ζ‖ := norm_sub_le _ _
          _ < 2 * R := by linarith
      rw [hk1def]; show _ = k0 (z - ζ) • g ζ
      rw [hk0def, indicator_of_mem this]
    · rw [Function.notMem_support] at hζ
      simp [hζ]
  have hmem : MemLp (k1 • g) 1 volume := hg.smul hk1
  refine ⟨by rw [hF]; exact memLp_one_iff_integrable.1 hmem, ?_⟩
  have hle : ‖∫ ζ, (z - ζ)⁻¹ • g ζ‖ₑ ≤
      eLpNorm k0 (ENNReal.ofReal q) volume * eLpNorm g (ENNReal.ofReal p) volume := by
    calc ‖∫ ζ, (z - ζ)⁻¹ • g ζ‖ₑ ≤ ∫⁻ ζ, ‖(z - ζ)⁻¹ • g ζ‖ₑ := enorm_integral_le_lintegral_enorm _
      _ = eLpNorm (k1 • g) 1 volume := by rw [eLpNorm_one_eq_lintegral_enorm, ← hF]
      _ ≤ eLpNorm k1 (ENNReal.ofReal q) volume * eLpNorm g (ENNReal.ofReal p) volume :=
          eLpNorm_smul_le_mul_eLpNorm hg.1 hk1.1
      _ = _ := by rw [hk1n]
  have hfin : eLpNorm k0 (ENNReal.ofReal q) volume * eLpNorm g (ENNReal.ofReal p) volume ≠ ⊤ :=
    ENNReal.mul_ne_top hk0.eLpNorm_ne_top hg.eLpNorm_ne_top
  rw [← ENNReal.toReal_mul, ← toReal_enorm]
  exact ENNReal.toReal_mono hfin hle

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (p R : ℝ) (hp : 2 < p) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℂ → E, MemLp g (ENNReal.ofReal p) volume →
      Function.support g ⊆ ball 0 R → ∀ z ∈ ball (0 : ℂ) R,
        Integrable (fun ζ => (z - ζ)⁻¹ • g ζ) ∧
        ‖∫ ζ, (z - ζ)⁻¹ • g ζ‖ ≤ C * (eLpNorm g (ENNReal.ofReal p) volume).toReal :=
  norm_integral_inv_sub_smul_le_aux p R hp hR
