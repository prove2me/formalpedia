-- Prove2me | solution 1 for GuthMaynard.Affine.Sig_small_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T00:14:11.309743+00:00
-- url     : https://prove2.me/submissions/29a4f306-2cbe-42d2-b371-08ce6dc8102a

import Mathlib
import Definitions.Def_GuthMaynard
import Definitions.Def_GuthMaynardAffine
section
namespace GuthMaynard.Affine
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal


end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartT
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal

end GuthMaynard.Affine.PartT
end

section
namespace GuthMaynard.Affine
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartT
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal

end GuthMaynard.Affine.PartT
end

section
namespace GuthMaynard.Affine
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartT
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal

end GuthMaynard.Affine.PartT
end

section
namespace GuthMaynard.Affine
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
/-! ## Fixed objects -/


























theorem β_nonneg (x : ℝ) : 0 ≤ β x := βb.nonneg

theorem β_eq_one {x : ℝ} (hx : |x| ≤ 1) : β x = 1 :=
  βb.one_of_mem_closedBall (by rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact hx)

theorem adm_continuous {C : ℝ} {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hf : Adm C c T f) :
    Continuous f :=
  hf.smooth.continuous

theorem adm_hasCompactSupport {C : ℝ} {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hf : Adm C c T f) :
    HasCompactSupport f :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport f)
    (closure_minimal hf.supp isClosed_Icc)

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

theorem card_dyadic_le {M : ℝ} (hM : 0 ≤ M) : ((dyadic M).card : ℝ) ≤ M + 1 := by
  simp only [dyadic, Int.card_Ioc]
  have h1 : (⌊2 * M⌋ : ℝ) ≤ 2 * M := Int.floor_le _
  have h2 : M - 1 < (⌊M⌋ : ℝ) := Int.sub_one_lt_floor _
  rcases le_or_gt (⌊2 * M⌋ - ⌊M⌋) 0 with h | h
  · rw [Int.toNat_of_nonpos h]; simp; linarith
  · have : (((⌊2 * M⌋ - ⌊M⌋).toNat : ℤ) : ℝ) = (⌊2 * M⌋ : ℝ) - ⌊M⌋ := by
      rw [Int.toNat_of_nonneg h.le]; push_cast; ring
    rw [← Int.cast_natCast, this]
    linarith

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias card_dyadic_le := GuthMaynard.Affine.PartB.card_dyadic_le

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

/-- A bump, as a Schwartz function. -/
noncomputable def bumpS (b : ContDiffBump (0 : ℝ)) : SchwartzMap ℝ ℂ :=
  (b.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp b.contDiff)

theorem fourier_bump_decay (b : ContDiffBump (0 : ℝ)) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, ‖𝓕 (fun x => (b x : ℂ)) y‖ * (1 + |y|) ^ k ≤ B := by
  set F := 𝓕 (bumpS b) with hF
  refine ⟨2 ^ (k, 0).1 * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) F,
    by positivity, fun y => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl F y
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  have e : F y = 𝓕 (fun x => (b x : ℂ)) y := rfl
  rw [mul_comm, ← e]
  exact h

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias fourier_bump_decay := GuthMaynard.Affine.PartB.fourier_bump_decay

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
/-- The Fourier transform of `t ↦ b(t/L) e(tx)` at `j`. -/
theorem fourier_dilate_char (b : ContDiffBump (0 : ℝ)) (L : ℝ) (hL : 0 < L) (x w : ℝ) :
    𝓕 (fun t : ℝ => (b (t / L) : ℂ) * ee (t * x)) w =
      (L : ℂ) * 𝓕 (fun t => (b t : ℂ)) (L * (w - x)) := by
  simp_rw [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  set H : ℝ → ℂ := fun s => Complex.exp (↑(-2 * Real.pi * s * (L * (w - x))) * Complex.I) *
    (b s : ℂ) with hH
  have e : (fun t : ℝ => Complex.exp (↑(-2 * Real.pi * t * w) * Complex.I) *
      ((b (t / L) : ℂ) * ee (t * x))) = fun t => H (t / L) := by
    funext t
    simp only [hH, ee]
    rw [mul_left_comm, mul_comm (b (t / L) : ℂ), ← mul_assoc, ← Complex.exp_add]
    congr 2
    have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    push_cast; field_simp; ring
  rw [e, Measure.integral_comp_div H L, abs_of_pos hL, Complex.real_smul]

theorem poisson_bump (b : ContDiffBump (0 : ℝ)) (L : ℝ) (hL : 0 < L) (N : ℤ)
    (hN : b.rOut * L ≤ N) (x : ℝ) :
    ∑ m ∈ Finset.Icc (-N) N, (b (m / L) : ℂ) * ee (m * x) =
      ∑' j : ℤ, (L : ℂ) * 𝓕 (fun t => (b t : ℂ)) (L * (j - x)) := by
  set f : ℝ → ℂ := fun t => (b (t / L) : ℂ) * ee (t * x) with hf
  have hfc : ContDiff ℝ (⊤ : ℕ∞) f := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (b (t / L) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (b.contDiff.comp (contDiff_id.div_const L))
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => ee (t * x)) := by
      unfold ee
      exact Complex.contDiff_exp.comp (contDiff_const.mul
        (Complex.ofRealCLM.contDiff.comp (contDiff_id.mul contDiff_const)))
    exact h1.mul h2
  have hzero : ∀ t : ℝ, b.rOut * L ≤ |t| → f t = 0 := by
    intro t ht
    have : b (t / L) = 0 := by
      refine b.zero_of_le_dist ?_
      rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hL, le_div_iff₀ hL]; exact ht
    simp [hf, this]
  have hfs : HasCompactSupport f := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (b.rOut * L)) fun t ht => ?_
    apply hzero
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at ht
    exact ht.le
  set fS : SchwartzMap ℝ ℂ := hfs.toSchwartzMap hfc
  have hP := SchwartzMap.tsum_eq_tsum_fourier fS 0
  simp only [zero_add, AddCircle.coe_zero, fourier_eval_zero, mul_one, SchwartzMap.fourier_coe]
    at hP
  have hfS : (fS : ℝ → ℂ) = f := rfl
  rw [hfS] at hP
  have hL1 : ∑' n : ℤ, f n = ∑ m ∈ Finset.Icc (-N) N, (b (m / L) : ℂ) * ee (m * x) := by
    rw [tsum_eq_sum (s := Finset.Icc (-N) N)]
    intro m hm
    apply hzero
    simp only [Finset.mem_Icc, not_and_or, not_le] at hm
    have : (N : ℝ) < |(m : ℝ)| := by
      rcases hm with h | h
      · have : (m : ℝ) < -N := by exact_mod_cast h
        rw [abs_of_neg (by linarith [hN, mul_nonneg b.rOut_pos.le hL.le])]; linarith
      · have : (N : ℝ) < m := by exact_mod_cast h
        rw [abs_of_pos (by linarith [hN, mul_nonneg b.rOut_pos.le hL.le])]; exact this
    linarith
  rw [← hL1, hP]
  exact tsum_congr fun j => fourier_dilate_char b L hL x j

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias poisson_bump := GuthMaynard.Affine.PartB.poisson_bump

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

/-! ### Large `M`: Lipschitz bound, mass lower bound, Riemann sums -/

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

theorem β_continuous : Continuous β := βb.continuous

theorem β_le_one (x : ℝ) : β x ≤ 1 := βb.le_one

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace
theorem smooth_nonneg {T : ℝ} (hT : 0 ≤ T) {f : ℝ → ℝ} (hf : ∀ u, 0 ≤ f u) (x : ℝ) :
    0 ≤ smooth T f x :=
  mul_nonneg hT (integral_nonneg fun y => mul_nonneg (β_nonneg _) (hf y))

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias smooth_nonneg := GuthMaynard.Affine.PartS.smooth_nonneg

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace
theorem smooth_ge (T : ℝ) (hT : 0 < T) (f : ℝ → ℝ) (hf : Continuous f) (hcs : HasCompactSupport f)
    (hnn : ∀ u, 0 ≤ f u) (x : ℝ) :
    T * ∫ y in Set.Icc (x - 1 / T) (x + 1 / T), f y ≤ smooth T f x := by
  unfold smooth
  gcongr
  have hint : Integrable (fun y => β (T * (x - y)) * f y) := by
    refine (hf.integrable_of_hasCompactSupport hcs).bdd_mul (c := 1)
      (β_continuous.comp (by fun_prop)).aestronglyMeasurable ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (β_nonneg _)]; exact β_le_one _
  calc ∫ y in Set.Icc (x - 1 / T) (x + 1 / T), f y
      = ∫ y in Set.Icc (x - 1 / T) (x + 1 / T), β (T * (x - y)) * f y := by
        refine setIntegral_congr_fun measurableSet_Icc fun y hy => ?_
        rw [β_eq_one, one_mul]
        have h1 : |x - y| ≤ 1 / T := abs_le.2 ⟨by linarith [hy.2], by linarith [hy.1]⟩
        rw [abs_mul, abs_of_pos hT]
        calc T * |x - y| ≤ T * (1 / T) := by gcongr
          _ = 1 := by field_simp
    _ ≤ ∫ y, β (T * (x - y)) * f y :=
        setIntegral_le_integral hint (Filter.Eventually.of_forall fun y =>
          mul_nonneg (β_nonneg _) (hnn y))

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias smooth_ge := GuthMaynard.Affine.PartS.smooth_ge

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartR
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartR
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartZ
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
theorem mem_dyadic {M : ℝ} {m : ℤ} (h : m ∈ dyadic M) : M < m ∧ (m : ℝ) ≤ 2 * M := by
  simp only [dyadic, Finset.mem_Ioc] at h
  exact ⟨Int.floor_lt.1 h.1, Int.le_floor.1 h.2⟩

theorem norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  rw [Complex.norm_exp]
  simp

/-- `t(n) = (1 + |n|)⁻²`. -/
noncomputable def tt (n : ℤ) : ℝ := 1 / (1 + |(n : ℝ)|) ^ 2

theorem tt_nonneg (n : ℤ) : 0 ≤ tt n := by unfold tt; positivity

theorem summable_tt : Summable tt := by
  have hs := (Real.summable_one_div_int_add_rpow (1 / 2) 2).2 one_lt_two
  refine Summable.of_nonneg_of_le tt_nonneg (fun n => ?_) hs
  unfold tt
  have h1 : |(n : ℝ) + 1 / 2| ≤ 1 + |(n : ℝ)| := by
    calc |(n : ℝ) + 1 / 2| ≤ |(n : ℝ)| + |1 / 2| := abs_add_le _ _
      _ ≤ 1 + |(n : ℝ)| := by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; linarith
  have h2 : 0 < |(n : ℝ) + 1 / 2| := by
    rw [abs_pos]
    intro h
    have : (n : ℝ) * 2 = -1 := by linarith
    have h3 : (n * 2 : ℤ) = -1 := by exact_mod_cast this
    omega
  rw [Real.rpow_two]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ h2.le h1 2)

theorem tt_shift_le (x : ℝ) (j : ℤ) : 1 / (1 + |(j : ℝ) - x|) ^ 2 ≤ 4 * tt (j - ⌊x⌋) := by
  unfold tt
  have h0 : 0 ≤ x - ⌊x⌋ := Int.fract_nonneg x
  have h1 : x - ⌊x⌋ < 1 := Int.fract_lt_one x
  have hle : 1 + |((j - ⌊x⌋ : ℤ) : ℝ)| ≤ 2 * (1 + |(j : ℝ) - x|) := by
    push_cast
    have : |(j : ℝ) - ⌊x⌋| ≤ |(j : ℝ) - x| + |x - ⌊x⌋| := by
      have := abs_add_le ((j : ℝ) - x) (x - ⌊x⌋); ring_nf at this ⊢; linarith
    rw [abs_of_nonneg h0] at this
    linarith [abs_nonneg ((j : ℝ) - x)]
  have hp : 0 < 1 + |((j - ⌊x⌋ : ℤ) : ℝ)| := by positivity
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  nlinarith [pow_le_pow_left₀ hp.le hle 2]

theorem summable_tt_shift (n₀ : ℤ) : Summable (fun j : ℤ => tt (j - n₀)) := by
  have h := (Equiv.subRight n₀).summable_iff (f := tt)
  have e : (tt ∘ ⇑(Equiv.subRight n₀)) = fun j : ℤ => tt (j - n₀) := by
    funext j; simp only [Function.comp_apply, Equiv.subRight_apply]
  rw [e] at h
  exact h.2 summable_tt

theorem tsum_tt_shift (n₀ : ℤ) : ∑' j : ℤ, tt (j - n₀) = ∑' n : ℤ, tt n := by
  have h := (Equiv.subRight n₀).tsum_eq tt
  simp only [Equiv.subRight_apply] at h
  exact h

/-- The `Z`-kernel `L B (1 + L|y|)^{-k}` is dominated by a shifted `4 L B t`. -/
theorem kern_le (L B : ℝ) (hL : 1 ≤ L) (hB : 0 ≤ B) (k : ℕ) (hk : 2 ≤ k) (x : ℝ) (j : ℤ) :
    L * B / (1 + L * |(j : ℝ) - x|) ^ k ≤ L * B * (4 * tt (j - ⌊x⌋)) := by
  have h1 : 1 + |(j : ℝ) - x| ≤ 1 + L * |(j : ℝ) - x| := by
    nlinarith [abs_nonneg ((j : ℝ) - x)]
  have h0 : (1 : ℝ) ≤ 1 + |(j : ℝ) - x| := by linarith [abs_nonneg ((j : ℝ) - x)]
  have h2 : (1 + |(j : ℝ) - x|) ^ 2 ≤ (1 + L * |(j : ℝ) - x|) ^ k :=
    (pow_le_pow_right₀ h0 hk).trans (pow_le_pow_left₀ (by linarith) h1 k)
  have h3 : L * B / (1 + L * |(j : ℝ) - x|) ^ k ≤ L * B * (1 / (1 + |(j : ℝ) - x|) ^ 2) := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) h2
  exact h3.trans (mul_le_mul_of_nonneg_left (tt_shift_le x j) (by positivity))

theorem summable_kern (L B : ℝ) (hL : 1 ≤ L) (hB : 0 ≤ B) (k : ℕ) (hk : 2 ≤ k) (x : ℝ) :
    Summable (fun j : ℤ => L * B / (1 + L * |(j : ℝ) - x|) ^ k) :=
  Summable.of_nonneg_of_le (fun j => by
      have : 0 ≤ 1 + L * |(j : ℝ) - x| := by
        have := abs_nonneg ((j : ℝ) - x); nlinarith
      positivity)
    (kern_le L B hL hB k hk x) (((summable_tt_shift ⌊x⌋).mul_left 4).mul_left _)

/-- Poisson for `Z`: `Z(Δ) = ∑_j L β̂(L(j + Δ))`. -/
theorem norm_Zfun_le (k : ℕ) (hk : 2 ≤ k) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ L : ℝ, 1 ≤ L → ∀ Δ : ℝ,
      ‖Zfun L Δ‖ ≤ ∑' j : ℤ, L * B / (1 + L * |(j : ℝ) + Δ|) ^ k := by
  obtain ⟨B, hB0, hB⟩ := fourier_bump_decay βb k
  refine ⟨B, hB0, fun L hL Δ => ?_⟩
  have hL0 : 0 < L := by linarith
  set bh : ℝ → ℂ := fun y => 𝓕 (fun t => (βb t : ℂ)) y with hbh
  have hZ : Zfun L Δ = ∑' j : ℤ, (L : ℂ) * bh (L * (j - -Δ)) := by
    have hN : βb.rOut * L ≤ (⌈2 * L⌉ : ℝ) := Int.le_ceil _
    rw [← poisson_bump βb L hL0 ⌈2 * L⌉ hN (-Δ)]
    unfold Zfun
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_neg]; rfl
  have hbound : ∀ j : ℤ, ‖(L : ℂ) * bh (L * (j - -Δ))‖ ≤
      L * B / (1 + L * |(j : ℝ) - -Δ|) ^ k := by
    intro j
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL0]
    have hb := hB (L * (j - -Δ))
    have hay : |L * ((j : ℝ) - -Δ)| = L * |(j : ℝ) - -Δ| := by rw [abs_mul, abs_of_pos hL0]
    rw [hay] at hb
    have hpos : 0 < (1 + L * |(j : ℝ) - -Δ|) ^ k := by positivity
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left ((le_div_iff₀ hpos).2 hb) hL0.le
  have hgs := summable_kern L B hL hB0 k hk (-Δ)
  have hns : Summable (fun j : ℤ => ‖(L : ℂ) * bh (L * (j - -Δ))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hgs
  rw [hZ]
  calc ‖∑' j : ℤ, (L : ℂ) * bh (L * (j - -Δ))‖
      ≤ ∑' j : ℤ, ‖(L : ℂ) * bh (L * (j - -Δ))‖ := norm_tsum_le_tsum_norm hns
    _ ≤ ∑' j : ℤ, L * B / (1 + L * |(j : ℝ) - -Δ|) ^ k := hns.tsum_le_tsum hbound hgs
    _ = ∑' j : ℤ, L * B / (1 + L * |(j : ℝ) + Δ|) ^ k := by simp_rw [sub_neg_eq_add]

end GuthMaynard.Affine.PartZ
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartR
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartR
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartR
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartR
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal


end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartZ
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

theorem dyadic_pos {M : ℝ} (hM : 0 ≤ M) {m : ℤ} (h : m ∈ dyadic M) : (0 : ℝ) < m := by
  have := (mem_dyadic h).1; linarith

theorem Hfun_continuous (C M₂ : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    Continuous (Hfun C M₂ g) := by
  unfold Hfun
  refine continuous_finsetSum _ fun m₂ _ => continuous_finsetSum _ fun m₂' _ =>
    continuous_finsetSum _ fun j _ => ?_
  exact hg.comp (by fun_prop)

theorem Hfun_nonneg (C M₂ : ℝ) {g : ℝ → ℝ} (hg : ∀ u, 0 ≤ g u) (u : ℝ) : 0 ≤ Hfun C M₂ g u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hg _

/-- Far terms of the `Z`-kernel: if `L|y| ≥ Q`, `Q^m ≥ T`, `L ≤ 2TQ`, the term is
`≤ 8 B t(j - ⌊x⌋)`. -/
theorem kern_far (L B Q T : ℝ) (hL : 1 ≤ L) (hB : 0 ≤ B) (hQ : 1 ≤ Q) (m : ℕ)
    (hQT : T ≤ Q ^ m) (hLTQ : L ≤ 2 * T * Q) (x : ℝ) (j : ℤ) (hfar : Q ≤ L * |(j : ℝ) - x|) :
    L * B / (1 + L * |(j : ℝ) - x|) ^ (m + 3) ≤ 8 * B * tt (j - ⌊x⌋) := by
  set y := |(j : ℝ) - x| with hy
  have hy0 : 0 ≤ y := abs_nonneg _
  set D := 1 + L * y with hD
  have hD1 : Q ≤ D := by linarith
  have hQ0 : 0 < Q := by linarith
  have hDp : 0 < D := by linarith
  have hDy : 1 + y ≤ D := by nlinarith
  have h1 : T * Q ≤ D ^ (m + 1) := by
    rw [pow_succ]
    exact mul_le_mul (hQT.trans (pow_le_pow_left₀ hQ0.le hD1 m)) hD1 hQ0.le (by positivity)
  have h2 : T * Q * (1 + y) ^ 2 ≤ D ^ (m + 3) := by
    rw [show m + 3 = (m + 1) + 2 by ring, pow_add]
    exact mul_le_mul h1 (pow_le_pow_left₀ (by positivity) hDy 2) (by positivity) (by positivity)
  have h3 : L * B / D ^ (m + 3) ≤ 2 * B * (1 / (1 + y) ^ 2) := by
    rw [div_le_iff₀ (by positivity)]
    have hy2 : 0 < (1 + y) ^ 2 := by positivity
    have e : 2 * B * (1 / (1 + y) ^ 2) * (T * Q * (1 + y) ^ 2) = 2 * B * (T * Q) := by
      field_simp
    calc L * B ≤ 2 * B * (T * Q) := by nlinarith
      _ = 2 * B * (1 / (1 + y) ^ 2) * (T * Q * (1 + y) ^ 2) := e.symm
      _ ≤ 2 * B * (1 / (1 + y) ^ 2) * D ^ (m + 3) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  calc L * B / D ^ (m + 3) ≤ 2 * B * (1 / (1 + y) ^ 2) := h3
    _ ≤ 2 * B * (4 * tt (j - ⌊x⌋)) := mul_le_mul_of_nonneg_left (tt_shift_le x j) (by positivity)
    _ = 8 * B * tt (j - ⌊x⌋) := by ring

/-- Pointwise bound of the `Z`-kernel sum, for `u, u'` in the support. -/
theorem tsum_kern_le (C L B Q T M₂ : ℝ) (hC : 1 ≤ C) (hL : 1 ≤ L) (hB : 0 ≤ B) (hQ : 1 ≤ Q)
    (hT1 : 1 ≤ T) (m : ℕ) (hQT : T ≤ Q ^ m) (hM₂ : 1 / 2 ≤ M₂) (hLM : L * M₂ = T * Q)
    {m₂ m₂' : ℤ} (hm₂ : m₂ ∈ dyadic M₂) (hm₂' : m₂' ∈ dyadic M₂) {u u' : ℝ}
    (hu : u ∈ Set.Icc (1 / C) C) (hu' : u' ∈ Set.Icc (1 / C) C) :
    ∑' j : ℤ, L * B / (1 + L * |(j : ℝ) + (m₂ * u - m₂' * u')|) ^ (m + 3) ≤
      (∑ j ∈ Finset.Icc (-⌊8 * C * M₂⌋) ⌊8 * C * M₂⌋,
          (Set.Icc ((m₂ * u + j) / m₂' - 1 / T) ((m₂ * u + j) / m₂' + 1 / T)).indicator
            (fun _ => L * B) u') +
        8 * B * ∑' n : ℤ, tt n := by
  have hT : 0 < T := by linarith
  set Δ := (m₂ : ℝ) * u - m₂' * u' with hΔ
  set N := ⌊8 * C * M₂⌋ with hN
  set S := Finset.Icc (-N) N with hS
  have hM₂0 : 0 < M₂ := by linarith
  have hC0 : 0 < C := by linarith
  obtain ⟨h21, h22⟩ := mem_dyadic hm₂
  obtain ⟨h21', h22'⟩ := mem_dyadic hm₂'
  have hm₂'0 : (0 : ℝ) < m₂' := by linarith
  have hLTQ : L ≤ 2 * T * Q := by
    have : 0 ≤ T * Q := by positivity
    nlinarith
  set I : ℤ → Set ℝ := fun j => Set.Icc ((m₂ * u + j) / m₂' - 1 / T) ((m₂ * u + j) / m₂' + 1 / T)
    with hI
  set a : ℤ → ℝ := fun j => if j ∈ S then (I j).indicator (fun _ => L * B) u' else 0 with ha
  set b : ℤ → ℝ := fun j => 8 * B * tt (j - ⌊-Δ⌋) with hb
  have hkern : ∀ j : ℤ, L * B / (1 + L * |(j : ℝ) + Δ|) ^ (m + 3) ≤ a j + b j := by
    intro j
    have hjΔ : |(j : ℝ) + Δ| = |(j : ℝ) - -Δ| := by rw [sub_neg_eq_add]
    have hb0 : 0 ≤ b j := by have := tt_nonneg (j - ⌊-Δ⌋); simp only [hb]; positivity
    have hden : 0 < (1 + L * |(j : ℝ) + Δ|) ^ (m + 3) := by positivity
    by_cases hnear : j ∈ S ∧ u' ∈ I j
    · have haj : a j = L * B := by
        simp only [ha, if_pos hnear.1, Set.indicator_of_mem hnear.2]
      rw [haj]
      have h1 : (1 : ℝ) ≤ (1 + L * |(j : ℝ) + Δ|) ^ (m + 3) :=
        one_le_pow₀ (by have := abs_nonneg ((j : ℝ) + Δ); nlinarith)
      have : L * B / (1 + L * |(j : ℝ) + Δ|) ^ (m + 3) ≤ L * B :=
        div_le_self (by positivity) h1
      linarith
    · have ha0 : 0 ≤ a j := by
        simp only [ha]; split_ifs
        · exact Set.indicator_nonneg (fun _ _ => by positivity) _
        · exact le_rfl
      have hfar : Q ≤ L * |(j : ℝ) - -Δ| := by
        rw [← hjΔ]
        by_cases hjS : j ∈ S
        · have hnI : u' ∉ I j := fun h => hnear ⟨hjS, h⟩
          simp only [hI, Set.mem_Icc, not_and_or, not_le] at hnI
          -- `|j + Δ| = m₂' |x_j - u'|` with `|x_j - u'| > 1/T`
          have e : (j : ℝ) + Δ = m₂' * ((m₂ * u + j) / m₂' - u') := by
            rw [hΔ]; field_simp; ring
          have hx : 1 / T < |(m₂ * u + j) / m₂' - u'| := by
            rcases hnI with h | h
            · linarith [le_abs_self ((m₂ * u + j) / m₂' - u')]
            · linarith [neg_le_abs ((m₂ * u + j) / m₂' - u')]
          rw [e, abs_mul, abs_of_pos hm₂'0]
          have h1 : M₂ * (1 / T) ≤ m₂' * |(m₂ * u + j) / m₂' - u'| :=
            mul_le_mul h21'.le hx.le (by positivity) hm₂'0.le
          have h2 : L * (M₂ * (1 / T)) = Q := by
            rw [← mul_assoc, hLM]; field_simp
          rw [← h2]
          exact mul_le_mul_of_nonneg_left h1 (by linarith)
        · -- `|j| > 8 C M₂ ≥ |Δ| + M₂`
          have hΔb : |Δ| ≤ 2 * C * M₂ := by
            have p1 : 0 ≤ (m₂ : ℝ) * u := mul_nonneg (by linarith) (le_trans (by positivity) hu.1)
            have p2 : (m₂ : ℝ) * u ≤ 2 * C * M₂ := by nlinarith [hu.1, hu.2]
            have p3 : 0 ≤ (m₂' : ℝ) * u' := mul_nonneg (by linarith) (le_trans (by positivity) hu'.1)
            have p4 : (m₂' : ℝ) * u' ≤ 2 * C * M₂ := by nlinarith [hu'.1, hu'.2]
            rw [hΔ, abs_le]; constructor <;> linarith
          have hjbig : 8 * C * M₂ < |(j : ℝ)| := by
            simp only [hS, Finset.mem_Icc, not_and_or, not_le] at hjS
            have hfl := Int.lt_floor_add_one (8 * C * M₂)
            rw [← hN] at hfl
            have hN0 : (0 : ℝ) ≤ N := by
              rw [hN]; exact_mod_cast Int.floor_nonneg.2 (by positivity)
            rcases hjS with h | h
            · have : (j : ℝ) + 1 ≤ -(N : ℝ) := by exact_mod_cast (show j + 1 ≤ -N by omega)
              rw [abs_of_neg (by linarith)]; linarith
            · have : (N : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (show N + 1 ≤ j by omega)
              rw [abs_of_pos (by linarith)]; linarith
          have hjd : M₂ ≤ |(j : ℝ) + Δ| := by
            have := abs_add_le ((j : ℝ) + Δ) (-Δ)
            rw [add_neg_cancel_right, abs_neg] at this
            nlinarith
          have h3 : T * Q ≤ L * |(j : ℝ) + Δ| := by
            rw [← hLM]; exact mul_le_mul_of_nonneg_left hjd (by linarith)
          nlinarith
      have := kern_far L B Q T hL hB hQ m hQT hLTQ (-Δ) j hfar
      rw [hjΔ]
      linarith
  have hks : Summable (fun j : ℤ => L * B / (1 + L * |(j : ℝ) + Δ|) ^ (m + 3)) := by
    have := summable_kern L B hL hB (m + 3) (by omega) (-Δ)
    simpa only [sub_neg_eq_add] using this
  have has : Summable a := summable_of_ne_finset_zero (s := S) fun j hj => if_neg hj
  have hbs : Summable b := (summable_tt_shift _).mul_left _
  have hta : ∑' j : ℤ, a j = ∑ j ∈ S, (I j).indicator (fun _ => L * B) u' := by
    rw [tsum_eq_sum (s := S) fun j hj => if_neg hj]
    exact Finset.sum_congr rfl fun j hj => if_pos hj
  have htb : ∑' j : ℤ, b j = 8 * B * ∑' n : ℤ, tt n := by
    rw [hb, tsum_mul_left, tsum_tt_shift]
  calc ∑' j : ℤ, L * B / (1 + L * |(j : ℝ) + Δ|) ^ (m + 3)
      ≤ ∑' j : ℤ, (a j + b j) := hks.tsum_le_tsum hkern (has.add hbs)
    _ = _ := by rw [has.tsum_add hbs, hta, htb]

/-- The `u'`-integral against `|Z|` (brief, *Bounding `Σ`*): the terms `|j| ≤ 8CM₂` give
`(A T^η/M₂) g((m₂u + j)/m₂')` plus `Q^{-k}` tails, the terms `|j| > 8CM₂` give `O(∫ f)`. -/
theorem integral_f_Zfun_le (C : ℝ) (c : ℕ → ℝ → ℝ) (hC : 1 ≤ C) (η : ℝ) (hη : 0 < η) :
    ∃ A T₁ : ℝ, 0 ≤ A ∧ ∀ T : ℝ, T₁ ≤ T → ∀ f : ℝ → ℝ, Adm C c T f →
      ∀ M₂ : ℝ, 1 / 2 ≤ M₂ → 1 ≤ T ^ (1 + η) / M₂ →
      ∀ m₂ ∈ dyadic M₂, ∀ m₂' ∈ dyadic M₂, ∀ u ∈ Set.Icc (1 / C) C,
        ∫ u', f u' * ‖Zfun (T ^ (1 + η) / M₂) (m₂ * u - m₂' * u')‖ ≤
          A * T ^ η / M₂ * (∑ j ∈ Finset.Icc (-⌊8 * C * M₂⌋) ⌊8 * C * M₂⌋,
            smooth T f ((m₂ * u + j) / m₂')) + A * ∫ u', f u' := by
  obtain ⟨B, hB0, hB⟩ := norm_Zfun_le (⌈1 / η⌉₊ + 3) (by omega)
  set m := ⌈1 / η⌉₊ with hm
  set S₀ := ∑' n : ℤ, tt n with hS₀
  have hS₀0 : 0 ≤ S₀ := tsum_nonneg tt_nonneg
  refine ⟨B + 8 * B * S₀, 1, by positivity, ?_⟩
  intro T hT1 f hf M₂ hM₂ hL1 m₂ hm₂ m₂' hm₂' u hu
  have hT : 0 < T := by linarith
  set Q := T ^ η with hQdef
  have hQ : 1 ≤ Q := Real.one_le_rpow hT1 hη.le
  have hQT : T ≤ Q ^ m := by
    rw [hQdef, ← Real.rpow_natCast, ← Real.rpow_mul hT.le]
    conv_lhs => rw [← Real.rpow_one T]
    refine Real.rpow_le_rpow_of_exponent_le hT1 ?_
    have h1 : 1 / η ≤ (m : ℝ) := Nat.le_ceil (1 / η)
    calc (1 : ℝ) = η * (1 / η) := by field_simp
      _ ≤ η * m := mul_le_mul_of_nonneg_left h1 hη.le
  have hM₂0 : 0 < M₂ := by linarith
  set L := T ^ (1 + η) / M₂ with hLdef
  have hLM : L * M₂ = T * Q := by
    rw [hLdef, div_mul_cancel₀ _ hM₂0.ne', Real.rpow_add hT, Real.rpow_one]
  have hLT : L = T * Q / M₂ := by rw [← hLM]; field_simp
  have hfc := adm_continuous hf
  have hfcs := adm_hasCompactSupport hf
  have hfi : Integrable f := hfc.integrable_of_hasCompactSupport hfcs
  set S := Finset.Icc (-⌊8 * C * M₂⌋) ⌊8 * C * M₂⌋ with hS
  set I : ℤ → Set ℝ := fun j =>
    Set.Icc ((m₂ * u + j) / m₂' - 1 / T) ((m₂ * u + j) / m₂' + 1 / T) with hI
  set R : ℝ → ℝ := fun u' => L * B * (∑ j ∈ S, (I j).indicator f u') + 8 * B * S₀ * f u' with hR
  have hInd : ∀ j, Integrable ((I j).indicator f) := fun j =>
    hfi.indicator (show MeasurableSet (I j) from measurableSet_Icc)
  have hRi : Integrable R :=
    ((integrable_finsetSum _ fun j _ => hInd j).const_mul _).add (hfi.const_mul _)
  have hL0 : 0 ≤ L := by linarith
  have hR0 : ∀ u', 0 ≤ R u' := fun u' => by
    have h1 : 0 ≤ ∑ j ∈ S, (I j).indicator f u' :=
      Finset.sum_nonneg fun j _ => Set.indicator_nonneg (fun y _ => hf.nonneg y) _
    have h2 := hf.nonneg u'
    simp only [hR]; positivity
  have hpt : ∀ u', f u' * ‖Zfun L (m₂ * u - m₂' * u')‖ ≤ R u' := by
    intro u'
    by_cases h0 : f u' = 0
    · rw [h0, zero_mul]; exact hR0 u'
    have hu' : u' ∈ Set.Icc (1 / C) C := hf.supp h0
    have hk := tsum_kern_le C L B Q T M₂ hC hL1 hB0 hQ hT1 m hQT hM₂ hLM hm₂ hm₂' hu hu'
    have hz := hB L hL1 (m₂ * u - m₂' * u')
    calc f u' * ‖Zfun L (m₂ * u - m₂' * u')‖
        ≤ f u' * ((∑ j ∈ S, (I j).indicator (fun _ => L * B) u') + 8 * B * S₀) :=
          mul_le_mul_of_nonneg_left (hz.trans hk) (hf.nonneg u')
      _ = R u' := by
          simp only [hR, mul_add, Finset.mul_sum]
          congr 1
          · refine Finset.sum_congr rfl fun j _ => ?_
            simp only [Set.indicator_apply]
            split_ifs <;> ring
          · ring
  have hint : ∫ u', f u' * ‖Zfun L (m₂ * u - m₂' * u')‖ ≤ ∫ u', R u' :=
    integral_mono_of_nonneg (ae_of_all _ fun u' => mul_nonneg (hf.nonneg u') (norm_nonneg _))
      hRi (ae_of_all _ hpt)
  have hRint : ∫ u', R u' = L * B * (∑ j ∈ S, ∫ y in I j, f y) + 8 * B * S₀ * ∫ u', f u' := by
    simp only [hR]
    rw [integral_add ((integrable_finsetSum _ fun j _ => hInd j).const_mul _)
      (hfi.const_mul _), integral_const_mul, integral_const_mul,
      integral_finsetSum _ fun j _ => hInd j]
    rw [Finset.sum_congr rfl fun j _ =>
      MeasureTheory.integral_indicator (f := f) (μ := volume)
        (show MeasurableSet (I j) from measurableSet_Icc)]
  have hsg : ∀ j ∈ S, ∫ y in I j, f y ≤ smooth T f ((m₂ * u + j) / m₂') / T := by
    intro j _
    rw [le_div_iff₀ hT, mul_comm]
    have := smooth_ge T hT f hfc hfcs hf.nonneg ((m₂ * u + j) / m₂')
    simpa only [hI] using this
  have hg0 : 0 ≤ ∑ j ∈ S, smooth T f ((m₂ * u + j) / m₂') :=
    Finset.sum_nonneg fun j _ => smooth_nonneg hT.le hf.nonneg _
  have hIf : 0 ≤ ∫ u', f u' := integral_nonneg hf.nonneg
  have hsum : ∑ j ∈ S, ∫ y in I j, f y ≤ (∑ j ∈ S, smooth T f ((m₂ * u + j) / m₂')) / T := by
    rw [Finset.sum_div]; exact Finset.sum_le_sum hsg
  have hLBT : L * B * ((∑ j ∈ S, smooth T f ((m₂ * u + j) / m₂')) / T) =
      B * Q / M₂ * ∑ j ∈ S, smooth T f ((m₂ * u + j) / m₂') := by
    rw [hLT]; field_simp
  calc ∫ u', f u' * ‖Zfun L (m₂ * u - m₂' * u')‖ ≤ ∫ u', R u' := hint
    _ = L * B * (∑ j ∈ S, ∫ y in I j, f y) + 8 * B * S₀ * ∫ u', f u' := hRint
    _ ≤ L * B * ((∑ j ∈ S, smooth T f ((m₂ * u + j) / m₂')) / T) + 8 * B * S₀ * ∫ u', f u' :=
        by linarith [mul_le_mul_of_nonneg_left hsum (mul_nonneg hL0 hB0)]
    _ = B * Q / M₂ * ∑ j ∈ S, smooth T f ((m₂ * u + j) / m₂') + 8 * B * S₀ * ∫ u', f u' := by
        rw [hLBT]
    _ ≤ (B + 8 * B * S₀) * Q / M₂ * ∑ j ∈ S, smooth T f ((m₂ * u + j) / m₂') +
          (B + 8 * B * S₀) * ∫ u', f u' := by
        have hQM : 0 ≤ Q / M₂ := by positivity
        have e1 : B * Q / M₂ = B * (Q / M₂) := by ring
        have e2 : (B + 8 * B * S₀) * Q / M₂ = (B + 8 * B * S₀) * (Q / M₂) := by ring
        rw [e1, e2]
        have h8 : 0 ≤ 8 * B * S₀ := by positivity
        gcongr
        · linarith
        · linarith

theorem β_continuous : Continuous β := βb.continuous

theorem β_le_one (x : ℝ) : β x ≤ 1 := βb.le_one

theorem β_integrable : Integrable β := βb.integrable

theorem βdiv_integrable {Q : ℝ} (hQ : 0 < Q) : Integrable (fun τ => β (τ / Q)) :=
  β_integrable.comp_div hQ.ne'

theorem integral_βdiv {Q : ℝ} (hQ : 0 < Q) : ∫ τ, β (τ / Q) = Q * βint := by
  rw [Measure.integral_comp_div (fun y => β y) Q, abs_of_pos hQ, smul_eq_mul]; rfl

theorem continuous_ee : Continuous ee := by unfold ee; fun_prop

theorem ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  unfold ee; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem conj_ee (x : ℝ) : (starRingEnd ℂ) (ee x) = ee (-x) := by
  unfold ee; rw [← Complex.exp_conj]; congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast; ring

theorem fhat_eq (f : ℝ → ℝ) (ξ : ℝ) : fhat f ξ = ∫ u, ee (-(u * ξ)) * (f u : ℂ) := by
  unfold fhat
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr 1; funext u
  rw [smul_eq_mul]; unfold ee; congr 2; push_cast; ring

theorem fhat_continuous {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    Continuous (fhat f) := by
  have hFi : Integrable (fun u => (f u : ℂ)) := (hf.integrable_of_hasCompactSupport hcs).ofReal
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hFi

theorem Γfun_continuous (M₂ : ℝ) {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    Continuous (Γfun M₂ f) := by
  unfold Γfun
  exact continuous_finsetSum _ fun m₂ _ =>
    continuous_const.mul ((fhat_continuous hf hcs).comp (continuous_const.mul continuous_id))

theorem fhat_mul_conj (f : ℝ → ℝ) (a b : ℝ) :
    fhat f a * (starRingEnd ℂ) (fhat f b) =
      ∫ p : ℝ × ℝ, ((f p.1 * f p.2 : ℝ) : ℂ) * ee (-(p.1 * a - p.2 * b))
        ∂(volume.prod volume) := by
  rw [fhat_eq, fhat_eq, ← integral_conj, ← integral_prod_mul]
  congr 1; funext p
  rw [map_mul, conj_ee, Complex.conj_ofReal,
    show -(p.1 * a - p.2 * b) = -(p.1 * a) + -(-(p.2 * b)) by ring, ee_add]
  push_cast; ring

theorem normSq_Γ (M₂ : ℝ) (f : ℝ → ℝ) (y : ℝ) :
    ((‖Γfun M₂ f y‖ ^ 2 : ℝ) : ℂ) = ∑ m₂ ∈ dyadic M₂, ∑ m₂' ∈ dyadic M₂,
      (((m₂ : ℝ) * m₂' : ℝ) : ℂ) * ∫ p : ℝ × ℝ, ((f p.1 * f p.2 : ℝ) : ℂ) *
        ee (-(y * (m₂ * p.1 - m₂' * p.2))) ∂(volume.prod volume) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  unfold Γfun
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m₂ _ => Finset.sum_congr rfl fun m₂' _ => ?_
  rw [map_mul, map_intCast,
    show (m₂ : ℂ) * fhat f (m₂ * y) * ((m₂' : ℂ) * (starRingEnd ℂ) (fhat f (m₂' * y))) =
      ((m₂ : ℂ) * m₂') * (fhat f (m₂ * y) * (starRingEnd ℂ) (fhat f (m₂' * y))) by ring,
    fhat_mul_conj]
  push_cast
  congr 2; funext p; congr 3; ring

/-- `Φ(w) = ∫ β(τ/Q) e(-τw/M₃) dτ`, the `τ`-integral. -/
noncomputable def Φ (Q M₃ w : ℝ) : ℂ := ∫ τ, (β (τ / Q) : ℂ) * ee (-(τ / M₃ * w))

theorem norm_Φ_le {Q : ℝ} (hQ : 0 < Q) (M₃ w : ℝ) : ‖Φ Q M₃ w‖ ≤ Q * βint := by
  unfold Φ
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  rw [← integral_βdiv hQ]
  congr 1; funext τ
  rw [norm_mul, norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (β_nonneg _)]

/-- The integrand of the `τ`- and `(u, u')`-integrals. -/
noncomputable def Fz (f : ℝ → ℝ) (Q M₃ a m₂ m₂' : ℝ) (z : ℝ × (ℝ × ℝ)) : ℂ :=
  (β (z.1 / Q) : ℂ) * (((f z.2.1 * f z.2.2 : ℝ) : ℂ) *
    ee (-((a + z.1 / M₃) * (m₂ * z.2.1 - m₂' * z.2.2))))

theorem integrable_Fz {f : ℝ → ℝ} (hf : Continuous f) (hfi : Integrable f) (hnn : ∀ u, 0 ≤ f u)
    {Q : ℝ} (hQ : 0 < Q) (M₃ a m₂ m₂' : ℝ) :
    Integrable (Fz f Q M₃ a m₂ m₂') (volume.prod (volume.prod volume)) := by
  have hg : Integrable (fun z : ℝ × (ℝ × ℝ) => β (z.1 / Q) * (f z.2.1 * f z.2.2))
      (volume.prod (volume.prod volume)) :=
    (βdiv_integrable hQ).mul_prod (hfi.mul_prod hfi)
  refine hg.mono' ?_ (ae_of_all _ fun z => ?_)
  · have : Continuous (Fz f Q M₃ a m₂ m₂') := by
      unfold Fz
      have := continuous_ee
      have := β_continuous
      fun_prop
    exact this.aestronglyMeasurable
  · unfold Fz
    rw [norm_mul, norm_mul, norm_ee, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (β_nonneg _),
      abs_of_nonneg (mul_nonneg (hnn _) (hnn _))]

theorem tau_inner (f : ℝ → ℝ) (Q M₃ a m₂ m₂' : ℝ) (p : ℝ × ℝ) :
    ∫ τ, Fz f Q M₃ a m₂ m₂' (τ, p) =
      ((f p.1 * f p.2 : ℝ) : ℂ) * ee (-(a * (m₂ * p.1 - m₂' * p.2))) *
        Φ Q M₃ (m₂ * p.1 - m₂' * p.2) := by
  unfold Fz Φ
  rw [← integral_const_mul]
  congr 1; funext τ
  rw [show -((a + τ / M₃) * (m₂ * p.1 - m₂' * p.2)) =
    -(a * (m₂ * p.1 - m₂' * p.2)) + -(τ / M₃ * (m₂ * p.1 - m₂' * p.2)) by ring, ee_add]
  ring

theorem tau_swap {f : ℝ → ℝ} (hf : Continuous f) (hfi : Integrable f) (hnn : ∀ u, 0 ≤ f u)
    {Q : ℝ} (hQ : 0 < Q) (M₃ a m₂ m₂' : ℝ) :
    ∫ τ, ∫ p : ℝ × ℝ, Fz f Q M₃ a m₂ m₂' (τ, p) ∂(volume.prod volume) =
      ∫ p : ℝ × ℝ, ((f p.1 * f p.2 : ℝ) : ℂ) * ee (-(a * (m₂ * p.1 - m₂' * p.2))) *
        Φ Q M₃ (m₂ * p.1 - m₂' * p.2) ∂(volume.prod volume) := by
  rw [integral_integral_swap (f := fun τ p => Fz f Q M₃ a m₂ m₂' (τ, p))
    (integrable_Fz hf hfi hnn hQ M₃ a m₂ m₂')]
  exact integral_congr_ae (ae_of_all _ fun p => tau_inner f Q M₃ a m₂ m₂' p)

/-- The `τ`-integral of `β(τ/Q)|Γ(a + τ/M₃)|²`, expanded. -/
theorem V_eq {f : ℝ → ℝ} (hf : Continuous f) (hfi : Integrable f) (hnn : ∀ u, 0 ≤ f u)
    {Q : ℝ} (hQ : 0 < Q) (M₂ M₃ a : ℝ) :
    ((∫ τ, β (τ / Q) * ‖Γfun M₂ f (a + τ / M₃)‖ ^ 2 : ℝ) : ℂ) =
      ∑ m₂ ∈ dyadic M₂, ∑ m₂' ∈ dyadic M₂, (((m₂ : ℝ) * m₂' : ℝ) : ℂ) *
        ∫ p : ℝ × ℝ, ((f p.1 * f p.2 : ℝ) : ℂ) * ee (-(a * (m₂ * p.1 - m₂' * p.2))) *
          Φ Q M₃ (m₂ * p.1 - m₂' * p.2) ∂(volume.prod volume) := by
  have hpt : ∀ τ : ℝ, ((β (τ / Q) * ‖Γfun M₂ f (a + τ / M₃)‖ ^ 2 : ℝ) : ℂ) =
      ∑ m₂ ∈ dyadic M₂, ∑ m₂' ∈ dyadic M₂, (((m₂ : ℝ) * m₂' : ℝ) : ℂ) *
        ∫ p : ℝ × ℝ, Fz f Q M₃ a m₂ m₂' (τ, p) ∂(volume.prod volume) := by
    intro τ
    rw [Complex.ofReal_mul, normSq_Γ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m₂ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m₂' _ => ?_
    simp only [Fz]
    rw [integral_const_mul]
    ring
  rw [← integral_complex_ofReal, integral_congr_ae (ae_of_all _ hpt)]
  rw [integral_finsetSum]
  swap
  · intro m₂ _
    exact integrable_finsetSum _ fun m₂' _ =>
      ((integrable_Fz hf hfi hnn hQ M₃ a m₂ m₂').integral_prod_left).const_mul _
  refine Finset.sum_congr rfl fun m₂ _ => ?_
  rw [integral_finsetSum]
  swap
  · intro m₂' _
    exact ((integrable_Fz hf hfi hnn hQ M₃ a m₂ m₂').integral_prod_left).const_mul _
  refine Finset.sum_congr rfl fun m₂' _ => ?_
  rw [integral_const_mul, tau_swap hf hfi hnn hQ]

theorem integrable_G {f : ℝ → ℝ} (hf : Continuous f) (hfi : Integrable f) (hnn : ∀ u, 0 ≤ f u)
    {Q : ℝ} (hQ : 0 < Q) (M₃ a m₂ m₂' : ℝ) :
    Integrable (fun p : ℝ × ℝ => ((f p.1 * f p.2 : ℝ) : ℂ) * ee (-(a * (m₂ * p.1 - m₂' * p.2))) *
      Φ Q M₃ (m₂ * p.1 - m₂' * p.2)) (volume.prod volume) := by
  have h := (integrable_Fz hf hfi hnn hQ M₃ a m₂ m₂').integral_prod_right
  refine h.congr (ae_of_all _ fun p => ?_)
  exact tau_inner f Q M₃ a m₂ m₂' p

/-- The weighted `ℓ`-sum of the `τ`-integrals, expanded: the `ℓ`-sum is `Z`. -/
theorem sum_V_eq {f : ℝ → ℝ} (hf : Continuous f) (hfi : Integrable f) (hnn : ∀ u, 0 ≤ f u)
    {Q : ℝ} (hQ : 0 < Q) (L M₂ M₃ : ℝ) :
    ((∑ ℓ ∈ Finset.Icc (-⌈2 * L⌉) ⌈2 * L⌉,
        β (ℓ / L) * ∫ τ, β (τ / Q) * ‖Γfun M₂ f (ℓ + τ / M₃)‖ ^ 2 : ℝ) : ℂ) =
      ∑ m₂ ∈ dyadic M₂, ∑ m₂' ∈ dyadic M₂, (((m₂ : ℝ) * m₂' : ℝ) : ℂ) *
        ∫ p : ℝ × ℝ, ((f p.1 * f p.2 : ℝ) : ℂ) * Φ Q M₃ (m₂ * p.1 - m₂' * p.2) *
          Zfun L (m₂ * p.1 - m₂' * p.2) ∂(volume.prod volume) := by
  set S := Finset.Icc (-⌈2 * L⌉) ⌈2 * L⌉ with hS
  set G : ℤ → ℤ → ℤ → ℝ × ℝ → ℂ := fun ℓ m₂ m₂' p =>
    ((f p.1 * f p.2 : ℝ) : ℂ) * ee (-((ℓ : ℝ) * (m₂ * p.1 - m₂' * p.2))) *
      Φ Q M₃ (m₂ * p.1 - m₂' * p.2) with hG
  have hpair : ∀ m₂ m₂' : ℤ, ∑ ℓ ∈ S, (β (ℓ / L) : ℂ) * ((((m₂ : ℝ) * m₂' : ℝ) : ℂ) *
      ∫ p : ℝ × ℝ, G ℓ m₂ m₂' p ∂(volume.prod volume)) =
      (((m₂ : ℝ) * m₂' : ℝ) : ℂ) * ∫ p : ℝ × ℝ, ((f p.1 * f p.2 : ℝ) : ℂ) *
        Φ Q M₃ (m₂ * p.1 - m₂' * p.2) * Zfun L (m₂ * p.1 - m₂' * p.2) ∂(volume.prod volume) := by
    intro m₂ m₂'
    have e1 : ∑ ℓ ∈ S, (β (ℓ / L) : ℂ) * ((((m₂ : ℝ) * m₂' : ℝ) : ℂ) *
        ∫ p : ℝ × ℝ, G ℓ m₂ m₂' p ∂(volume.prod volume)) =
        (((m₂ : ℝ) * m₂' : ℝ) : ℂ) * ∑ ℓ ∈ S,
          ∫ p : ℝ × ℝ, (β (ℓ / L) : ℂ) * G ℓ m₂ m₂' p ∂(volume.prod volume) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [integral_const_mul]; ring
    rw [e1, ← integral_finsetSum]
    swap
    · intro ℓ _
      exact (integrable_G hf hfi hnn hQ M₃ ℓ m₂ m₂').const_mul _
    congr 1
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [hG, Zfun, Finset.mul_sum]
    rw [← hS]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    ring
  calc ((∑ ℓ ∈ S, β (ℓ / L) * ∫ τ, β (τ / Q) * ‖Γfun M₂ f (ℓ + τ / M₃)‖ ^ 2 : ℝ) : ℂ)
      = ∑ ℓ ∈ S, ∑ m₂ ∈ dyadic M₂, ∑ m₂' ∈ dyadic M₂, (β (ℓ / L) : ℂ) *
          ((((m₂ : ℝ) * m₂' : ℝ) : ℂ) * ∫ p : ℝ × ℝ, G ℓ m₂ m₂' p ∂(volume.prod volume)) := by
        rw [Complex.ofReal_sum]
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [Complex.ofReal_mul, V_eq hf hfi hnn hQ, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m₂ _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ m₂ ∈ dyadic M₂, ∑ ℓ ∈ S, ∑ m₂' ∈ dyadic M₂, (β (ℓ / L) : ℂ) *
          ((((m₂ : ℝ) * m₂' : ℝ) : ℂ) * ∫ p : ℝ × ℝ, G ℓ m₂ m₂' p ∂(volume.prod volume)) :=
        Finset.sum_comm
    _ = ∑ m₂ ∈ dyadic M₂, ∑ m₂' ∈ dyadic M₂, ∑ ℓ ∈ S, (β (ℓ / L) : ℂ) *
          ((((m₂ : ℝ) * m₂' : ℝ) : ℂ) * ∫ p : ℝ × ℝ, G ℓ m₂ m₂' p ∂(volume.prod volume)) :=
        Finset.sum_congr rfl fun m₂ _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun m₂ _ => Finset.sum_congr rfl fun m₂' _ => hpair m₂ m₂'

theorem continuous_Zfun (L : ℝ) : Continuous (Zfun L) := by
  unfold Zfun
  exact continuous_finsetSum _ fun ℓ _ =>
    continuous_const.mul (continuous_ee.comp (by fun_prop))

theorem norm_Zfun_le_card (L Δ : ℝ) :
    ‖Zfun L Δ‖ ≤ ((Finset.Icc (-⌈2 * L⌉) ⌈2 * L⌉).card : ℝ) := by
  unfold Zfun
  refine (norm_sum_le _ _).trans ?_
  rw [← nsmul_one, ← Finset.sum_const]
  refine Finset.sum_le_sum fun ℓ _ => ?_
  rw [norm_mul, norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (β_nonneg _)]
  exact β_le_one _

theorem integrable_ffZ {f : ℝ → ℝ} (hf : Continuous f) (hfi : Integrable f)
    (hnn : ∀ u, 0 ≤ f u) (L m₂ m₂' : ℝ) :
    Integrable (fun p : ℝ × ℝ => f p.1 * f p.2 * ‖Zfun L (m₂ * p.1 - m₂' * p.2)‖)
      (volume.prod volume) := by
  refine ((hfi.mul_prod hfi).mul_const ((Finset.Icc (-⌈2 * L⌉) ⌈2 * L⌉).card : ℝ)).mono' ?_
    (ae_of_all _ fun p => ?_)
  · have := continuous_Zfun L
    exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
      f p.1 * f p.2 * ‖Zfun L (m₂ * p.1 - m₂' * p.2)‖).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by have := hnn p.1; have := hnn p.2; positivity)]
    exact mul_le_mul_of_nonneg_left (norm_Zfun_le_card _ _) (mul_nonneg (hnn _) (hnn _))

/-- The real inequality behind `SigSmall_le_majorant`. -/
theorem majorant_real {f : ℝ → ℝ} (hf : Continuous f) (hfi : Integrable f) (hnn : ∀ u, 0 ≤ f u)
    {Q : ℝ} (hQ : 0 < Q) (L M₂ M₃ : ℝ) (hM₂ : 0 ≤ M₂) :
    ∑ ℓ ∈ Finset.Icc (-⌈2 * L⌉) ⌈2 * L⌉,
        β (ℓ / L) * ∫ τ, β (τ / Q) * ‖Γfun M₂ f (ℓ + τ / M₃)‖ ^ 2 ≤
      Q * βint * ∑ m₂ ∈ dyadic M₂, ∑ m₂' ∈ dyadic M₂,
        ((m₂ : ℝ) * m₂') * ∫ u, ∫ u', f u * f u' * ‖Zfun L (m₂ * u - m₂' * u')‖ := by
  set X := ∑ ℓ ∈ Finset.Icc (-⌈2 * L⌉) ⌈2 * L⌉,
    β (ℓ / L) * ∫ τ, β (τ / Q) * ‖Γfun M₂ f (ℓ + τ / M₃)‖ ^ 2 with hX
  have hβint : 0 ≤ βint := integral_nonneg β_nonneg
  have hcpos : ∀ m₂ ∈ dyadic M₂, ∀ m₂' ∈ dyadic M₂, (0 : ℝ) ≤ (m₂ : ℝ) * m₂' :=
    fun m₂ h₂ m₂' h₂' => mul_nonneg (dyadic_pos hM₂ h₂).le (dyadic_pos hM₂ h₂').le
  calc X ≤ ‖(X : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self _
    _ = ‖∑ m₂ ∈ dyadic M₂, ∑ m₂' ∈ dyadic M₂, (((m₂ : ℝ) * m₂' : ℝ) : ℂ) *
          ∫ p : ℝ × ℝ, ((f p.1 * f p.2 : ℝ) : ℂ) * Φ Q M₃ (m₂ * p.1 - m₂' * p.2) *
            Zfun L (m₂ * p.1 - m₂' * p.2) ∂(volume.prod volume)‖ := by
        rw [hX, sum_V_eq hf hfi hnn hQ]
    _ ≤ ∑ m₂ ∈ dyadic M₂, ∑ m₂' ∈ dyadic M₂, ((m₂ : ℝ) * m₂') *
          (Q * βint * ∫ u, ∫ u', f u * f u' * ‖Zfun L (m₂ * u - m₂' * u')‖) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m₂ h₂ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m₂' h₂' => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hcpos m₂ h₂ m₂' h₂')]
        refine mul_le_mul_of_nonneg_left ?_ (hcpos m₂ h₂ m₂' h₂')
        rw [← integral_prod _ (integrable_ffZ hf hfi hnn L m₂ m₂'), ← integral_const_mul]
        refine (norm_integral_le_integral_norm _).trans ?_
        refine integral_mono_of_nonneg (ae_of_all _ fun p => norm_nonneg _)
          ((integrable_ffZ hf hfi hnn L m₂ m₂').const_mul _) (ae_of_all _ fun p => ?_)
        have hff : 0 ≤ f p.1 * f p.2 := mul_nonneg (hnn _) (hnn _)
        simp only
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hff]
        have := norm_Φ_le hQ M₃ (m₂ * p.1 - m₂' * p.2)
        have hz := norm_nonneg (Zfun L (m₂ * p.1 - m₂' * p.2))
        calc f p.1 * f p.2 * ‖Φ Q M₃ (m₂ * p.1 - m₂' * p.2)‖ * ‖Zfun L (m₂ * p.1 - m₂' * p.2)‖
            ≤ f p.1 * f p.2 * (Q * βint) * ‖Zfun L (m₂ * p.1 - m₂' * p.2)‖ := by gcongr
          _ = Q * βint * (f p.1 * f p.2 * ‖Zfun L (m₂ * p.1 - m₂' * p.2)‖) := by ring
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m₂ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m₂' _ => ?_
        ring

theorem βdiv_hasCompactSupport {Q : ℝ} (hQ : 0 < Q) : HasCompactSupport (fun τ : ℝ => β (τ / Q)) := by
  have h := (βb.hasCompactSupport : HasCompactSupport β).comp_smul (inv_ne_zero hQ.ne')
  have e : (fun τ : ℝ => β (τ / Q)) = fun x => β (Q⁻¹ • x) := by
    funext x; rw [smul_eq_mul, div_eq_inv_mul]
  rw [e]; exact h

theorem integrable_Vint {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f)
    {Q : ℝ} (hQ : 0 < Q) (M₂ M₃ a : ℝ) :
    Integrable (fun τ => β (τ / Q) * ‖Γfun M₂ f (a + τ / M₃)‖ ^ 2) := by
  have hc : Continuous (fun τ => β (τ / Q) * ‖Γfun M₂ f (a + τ / M₃)‖ ^ 2) := by
    have := Γfun_continuous M₂ hf hcs
    have := β_continuous
    fun_prop
  exact hc.integrable_of_hasCompactSupport (βdiv_hasCompactSupport hQ).mul_right

theorem SigTerm_le {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f)
    {Q : ℝ} (hQ : 0 < Q) (M₂ M₃ : ℝ) (ℓ : ℤ) :
    SigTerm Q M₂ M₃ f ℓ ≤
      ENNReal.ofReal (∫ τ, β (τ / Q) * ‖Γfun M₂ f (ℓ + τ / M₃)‖ ^ 2) := by
  have hint := integrable_Vint hf hcs hQ M₂ M₃ (ℓ : ℝ)
  have hc : Continuous (fun τ => β (τ / Q) * ‖Γfun M₂ f (ℓ + τ / M₃)‖ ^ 2) := by
    have := Γfun_continuous M₂ hf hcs
    have := β_continuous
    fun_prop
  unfold SigTerm
  rw [ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun τ => mul_nonneg (β_nonneg _) (sq_nonneg _))]
  refine le_trans (setLIntegral_mono hc.measurable.ennreal_ofReal fun τ hτ => le_of_eq ?_)
    (setLIntegral_le_lintegral _ _)
  have h1 : β (τ / Q) = 1 := by
    apply β_eq_one
    rw [abs_div, abs_of_pos hQ, div_le_one hQ]; exact hτ.1
  rw [h1, one_mul, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- Majorize `Σ_small` by `∑_ℓ β(ℓ/L) ∫ β(τ/Q) |Γ(ℓ + τ/M₃)|² dτ`, expand `|Γ|²`, do the
`τ`-integral (`Q β̂(QΔ/M₃)`, `≤ Q ‖β‖₁`) and the `ℓ`-sum (`Z(Δ)`), `Δ = m₂u - m₂'u'`. -/
theorem SigSmall_le_majorant (L Q M₂ M₃ : ℝ) (hL : 0 < L) (hQ : 0 < Q) (hM₂ : 0 ≤ M₂)
    (hM₃ : 0 < M₃) (f : ℝ → ℝ) (hf : Continuous f) (hcs : HasCompactSupport f)
    (hnn : ∀ u, 0 ≤ f u) :
    SigSmall L Q M₂ M₃ f ≤ ENNReal.ofReal (Q * βint * ∑ m₂ ∈ dyadic M₂, ∑ m₂' ∈ dyadic M₂,
      ((m₂ : ℝ) * m₂') * ∫ u, ∫ u', f u * f u' * ‖Zfun L (m₂ * u - m₂' * u')‖) := by
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hcs
  set S := Finset.Icc (-⌈2 * L⌉) ⌈2 * L⌉ with hS
  set V : ℤ → ℝ := fun ℓ => ∫ τ, β (τ / Q) * ‖Γfun M₂ f (ℓ + τ / M₃)‖ ^ 2 with hV
  have hV0 : ∀ ℓ, 0 ≤ V ℓ := fun ℓ =>
    integral_nonneg fun τ => mul_nonneg (β_nonneg _) (sq_nonneg _)
  refine le_trans ?_ (ENNReal.ofReal_le_ofReal (majorant_real hf hfi hnn hQ L M₂ M₃ hM₂))
  rw [ENNReal.ofReal_sum_of_nonneg fun ℓ _ => mul_nonneg (β_nonneg _) (hV0 ℓ)]
  unfold SigSmall
  have hts : ∑' ℓ : ℤ, (if ℓ ∈ S then ENNReal.ofReal (β (ℓ / L) * V ℓ) else 0) =
      ∑ ℓ ∈ S, ENNReal.ofReal (β (ℓ / L) * V ℓ) := by
    rw [tsum_eq_sum (s := S) fun ℓ hℓ => if_neg hℓ]
    exact Finset.sum_congr rfl fun ℓ hℓ => if_pos hℓ
  rw [← hS, ← hts]
  refine ENNReal.tsum_le_tsum fun ℓ => ?_
  by_cases h : ℓ ≠ 0 ∧ |(ℓ : ℝ)| ≤ L
  · rw [if_pos h]
    have hℓS : ℓ ∈ S := by
      have hc := Int.le_ceil (2 * L)
      have h2 := abs_le.1 h.2
      rw [hS, Finset.mem_Icc]
      constructor
      · have : -(⌈2 * L⌉ : ℝ) ≤ (ℓ : ℝ) := by linarith
        exact_mod_cast this
      · have : (ℓ : ℝ) ≤ (⌈2 * L⌉ : ℝ) := by linarith
        exact_mod_cast this
    rw [if_pos hℓS]
    have h1 : β (ℓ / L) = 1 := by
      apply β_eq_one
      rw [abs_div, abs_of_pos hL, div_le_one hL]; exact h.2
    rw [h1, one_mul]
    exact SigTerm_le hf hcs hQ M₂ M₃ ℓ
  · rw [if_neg h]; exact zero_le

end GuthMaynard.Affine.PartZ
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartZ
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
/-- `βT T z = T β(T z)` (from `P91PartS`). -/
noncomputable def βT (T : ℝ) (z : ℝ) : ℝ := T * β (T * z)

theorem smooth_eq_conv (T : ℝ) (f : ℝ → ℝ) :
    smooth T f = convolution f (βT T) (ContinuousLinearMap.mul ℝ ℝ) volume := by
  ext x
  simp only [smooth, convolution_def, ContinuousLinearMap.mul_apply', βT, ← integral_const_mul]
  congr 1; ext y; ring

theorem smooth_continuous (T : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (smooth T f) := by
  rcases eq_or_ne T 0 with rfl | hT
  · have : smooth 0 f = fun _ => 0 := by ext x; simp [smooth]
    rw [this]; exact continuous_const
  rw [smooth_eq_conv]
  have hcsg : HasCompactSupport (βT T) := by
    have : HasCompactSupport (fun z : ℝ => β (T * z)) := by
      have h := (βb.hasCompactSupport : HasCompactSupport β).comp_smul hT
      have e : (fun z : ℝ => β (T * z)) = fun x => β (T • x) := by
        funext x; rw [smul_eq_mul]
      rw [e]; exact h
    exact this.mul_left
  have hg : ContDiff ℝ (⊤ : ℕ∞) (βT T) :=
    contDiff_const.mul ((βb.contDiff (n := (⊤ : ℕ∞))).comp (contDiff_const.mul contDiff_id))
  exact (hcsg.contDiff_convolution_right _ (hf.locallyIntegrable) hg).continuous

theorem Sig_small_le (C : ℝ) (c : ℕ → ℝ → ℝ) (hC : 1 ≤ C) (η : ℝ) (hη : 0 < η) :
    ∃ A T₁ : ℝ, 0 ≤ A ∧ ∀ T : ℝ, T₁ ≤ T → ∀ f : ℝ → ℝ, Adm C c T f →
      ∀ M M₁ M₂ M₃ : ℝ, Regime T M M₁ M₂ M₃ →
        SigSmall (T ^ (1 + η) / M₂) (T ^ η) M₂ M₃ f ≤
          ENNReal.ofReal (A * (T ^ η) ^ 2 * M₂ * (∫ u, f u * Hfun C M₂ (smooth T f) u) +
            A * T ^ η * M ^ 4 * (∫ u, f u) ^ 2) := by
  obtain ⟨AZ, TZ, hAZ, hZ⟩ := integral_f_Zfun_le C c hC η hη
  have hβint : 0 ≤ βint := integral_nonneg β_nonneg
  refine ⟨40 * βint * AZ, max TZ 1, by positivity, ?_⟩
  intro T hT f hf M M₁ M₂ M₃ hr
  have hTZ : TZ ≤ T := le_of_max_le_left hT
  have hT1 : 1 ≤ T := le_of_max_le_right hT
  have hT0 : 0 < T := by linarith
  have hM₂ : 1 / 2 ≤ M₂ := hr.h₂
  have hM₂0 : 0 < M₂ := by linarith
  have hM₂M : M₂ < M := hr.h₂M
  have hM₃ : 0 < M₃ := by linarith [hr.h₃]
  set Q := T ^ η with hQdef
  have hQ0 : 0 < Q := Real.rpow_pos_of_pos hT0 η
  set L := T ^ (1 + η) / M₂ with hLdef
  have hL0 : 0 < L := by positivity
  have hfc := adm_continuous hf
  have hfcs := adm_hasCompactSupport hf
  have hfi : Integrable f := hfc.integrable_of_hasCompactSupport hfcs
  set I := ∫ u, f u with hI
  have hI0 : 0 ≤ I := integral_nonneg hf.nonneg
  set g := smooth T f with hg
  have hgc : Continuous g := smooth_continuous T hfc
  have hg0 : ∀ x, 0 ≤ g x := smooth_nonneg hT0.le hf.nonneg
  set Sj := Finset.Icc (-⌊8 * C * M₂⌋) ⌊8 * C * M₂⌋ with hSj
  set H := Hfun C M₂ g with hH
  have hHc : Continuous H := Hfun_continuous C M₂ hgc
  have hFH0 : 0 ≤ ∫ u, f u * H u :=
    integral_nonneg fun u => mul_nonneg (hf.nonneg u) (Hfun_nonneg C M₂ hg0 u)
  have hM4 : M₂ ^ 4 ≤ M ^ 4 := pow_le_pow_left₀ hM₂0.le hM₂M.le 4
  have hRHS0 : 0 ≤ 40 * βint * AZ * Q ^ 2 * M₂ * (∫ u, f u * H u) +
      40 * βint * AZ * Q * M ^ 4 * I ^ 2 := by positivity
  -- the case `L < 1`
  by_cases hL1 : L < 1
  · have hz : ∀ ℓ : ℤ, ¬(ℓ ≠ 0 ∧ |(ℓ : ℝ)| ≤ L) := by
      rintro ℓ ⟨h0, h1⟩
      have : (1 : ℤ) ≤ |ℓ| := Int.one_le_abs h0
      have : (1 : ℝ) ≤ |(ℓ : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast this
      linarith
    have : SigSmall L Q M₂ M₃ f = 0 := by
      unfold SigSmall
      simp only [if_neg (hz _), tsum_zero]
    rw [this]; exact zero_le
  push Not at hL1
  -- the majorant
  refine (SigSmall_le_majorant L Q M₂ M₃ hL0 hQ0 hM₂0.le hM₃ f hfc hfcs hf.nonneg).trans
    (ENNReal.ofReal_le_ofReal ?_)
  set K : ℤ → ℤ → ℝ := fun m₂ m₂' => ∫ u, f u * ∑ j ∈ Sj, g ((m₂ * u + j) / m₂') with hK
  have hK0 : ∀ m₂ m₂', 0 ≤ K m₂ m₂' := fun m₂ m₂' =>
    integral_nonneg fun u => mul_nonneg (hf.nonneg u) (Finset.sum_nonneg fun j _ => hg0 _)
  have hKint : ∀ m₂ m₂' : ℤ, Integrable (fun u => f u * ∑ j ∈ Sj, g ((m₂ * u + j) / m₂')) :=
    fun m₂ m₂' => (hfc.mul (continuous_finsetSum _ fun j _ => hgc.comp (by fun_prop)))
      |>.integrable_of_hasCompactSupport hfcs.mul_right
  -- one pair
  have hW : ∀ m₂ ∈ dyadic M₂, ∀ m₂' ∈ dyadic M₂,
      ∫ u, ∫ u', f u * f u' * ‖Zfun L (m₂ * u - m₂' * u')‖ ≤
        AZ * Q / M₂ * K m₂ m₂' + AZ * I * I := by
    intro m₂ hm₂ m₂' hm₂'
    have e : ∀ u, ∫ u', f u * f u' * ‖Zfun L (m₂ * u - m₂' * u')‖ =
        f u * ∫ u', f u' * ‖Zfun L (m₂ * u - m₂' * u')‖ := by
      intro u; rw [← integral_const_mul]; congr 1; funext u'; ring
    simp_rw [e]
    have hRi : Integrable (fun u => AZ * Q / M₂ * (f u * ∑ j ∈ Sj, g ((m₂ * u + j) / m₂')) +
        AZ * I * f u) := ((hKint m₂ m₂').const_mul _).add (hfi.const_mul _)
    calc ∫ u, f u * ∫ u', f u' * ‖Zfun L (m₂ * u - m₂' * u')‖
        ≤ ∫ u, (AZ * Q / M₂ * (f u * ∑ j ∈ Sj, g ((m₂ * u + j) / m₂')) + AZ * I * f u) := by
          refine integral_mono_of_nonneg (ae_of_all _ fun u => mul_nonneg (hf.nonneg u)
            (integral_nonneg fun u' => mul_nonneg (hf.nonneg u') (norm_nonneg _))) hRi
            (ae_of_all _ fun u => ?_)
          by_cases h0 : f u = 0
          · simp only [h0, zero_mul, mul_zero, zero_add, le_refl]
          have hu : u ∈ Set.Icc (1 / C) C := hf.supp h0
          have := hZ T hTZ f hf M₂ hM₂ hL1 m₂ hm₂ m₂' hm₂' u hu
          calc f u * ∫ u', f u' * ‖Zfun L (m₂ * u - m₂' * u')‖
              ≤ f u * (AZ * Q / M₂ * (∑ j ∈ Sj, g ((m₂ * u + j) / m₂')) + AZ * I) :=
                mul_le_mul_of_nonneg_left this (hf.nonneg u)
            _ = _ := by ring
      _ = AZ * Q / M₂ * K m₂ m₂' + AZ * I * I := by
          rw [integral_add ((hKint m₂ m₂').const_mul _) (hfi.const_mul _), integral_const_mul,
            integral_const_mul]
  -- `∑∑ K = ∫ f H`
  have hKH : ∑ m₂ ∈ dyadic M₂, ∑ m₂' ∈ dyadic M₂, K m₂ m₂' = ∫ u, f u * H u := by
    simp only [hK, hH, Hfun, Finset.mul_sum]
    rw [integral_finsetSum]
    swap
    · intro m₂ _
      exact integrable_finsetSum _ fun m₂' _ => by
        have := hKint m₂ m₂'; simpa only [Finset.mul_sum] using this
    refine Finset.sum_congr rfl fun m₂ _ => ?_
    rw [integral_finsetSum]
    · intro m₂' _
      have := hKint m₂ m₂'; simpa only [Finset.mul_sum] using this
  -- arithmetic
  have hcard : ((dyadic M₂).card : ℝ) ≤ 3 * M₂ := (card_dyadic_le hM₂0.le).trans (by linarith)
  have hterm : ∀ m₂ ∈ dyadic M₂, ∀ m₂' ∈ dyadic M₂,
      ((m₂ : ℝ) * m₂') * ∫ u, ∫ u', f u * f u' * ‖Zfun L (m₂ * u - m₂' * u')‖ ≤
        4 * AZ * Q * M₂ * K m₂ m₂' + 4 * M₂ ^ 2 * AZ * I ^ 2 := by
    intro m₂ hm₂ m₂' hm₂'
    obtain ⟨a1, a2⟩ := mem_dyadic hm₂
    obtain ⟨b1, b2⟩ := mem_dyadic hm₂'
    have hc0 : 0 ≤ (m₂ : ℝ) * m₂' := by nlinarith
    have hc4 : (m₂ : ℝ) * m₂' ≤ 4 * M₂ ^ 2 := by nlinarith
    have hX0 : 0 ≤ AZ * Q / M₂ * K m₂ m₂' + AZ * I * I := by
      have := hK0 m₂ m₂'; positivity
    calc ((m₂ : ℝ) * m₂') * ∫ u, ∫ u', f u * f u' * ‖Zfun L (m₂ * u - m₂' * u')‖
        ≤ ((m₂ : ℝ) * m₂') * (AZ * Q / M₂ * K m₂ m₂' + AZ * I * I) :=
          mul_le_mul_of_nonneg_left (hW m₂ hm₂ m₂' hm₂') hc0
      _ ≤ 4 * M₂ ^ 2 * (AZ * Q / M₂ * K m₂ m₂' + AZ * I * I) :=
          mul_le_mul_of_nonneg_right hc4 hX0
      _ = 4 * AZ * Q * M₂ * K m₂ m₂' + 4 * M₂ ^ 2 * AZ * I ^ 2 := by
          field_simp
  have hsum : ∑ m₂ ∈ dyadic M₂, ∑ m₂' ∈ dyadic M₂,
      ((m₂ : ℝ) * m₂') * ∫ u, ∫ u', f u * f u' * ‖Zfun L (m₂ * u - m₂' * u')‖ ≤
        4 * AZ * Q * M₂ * (∫ u, f u * H u) + 36 * AZ * M₂ ^ 4 * I ^ 2 := by
    calc _ ≤ ∑ m₂ ∈ dyadic M₂, ∑ m₂' ∈ dyadic M₂,
          (4 * AZ * Q * M₂ * K m₂ m₂' + 4 * M₂ ^ 2 * AZ * I ^ 2) :=
          Finset.sum_le_sum fun m₂ hm₂ => Finset.sum_le_sum fun m₂' hm₂' => hterm m₂ hm₂ m₂' hm₂'
      _ = 4 * AZ * Q * M₂ * (∑ m₂ ∈ dyadic M₂, ∑ m₂' ∈ dyadic M₂, K m₂ m₂') +
          ((dyadic M₂).card : ℝ) * ((dyadic M₂).card : ℝ) * (4 * M₂ ^ 2 * AZ * I ^ 2) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
          ring
      _ ≤ 4 * AZ * Q * M₂ * (∫ u, f u * H u) + 36 * AZ * M₂ ^ 4 * I ^ 2 := by
          rw [hKH]
          have hc0 : (0 : ℝ) ≤ (dyadic M₂).card := Nat.cast_nonneg _
          have hcc : ((dyadic M₂).card : ℝ) * (dyadic M₂).card ≤ 9 * M₂ ^ 2 := by nlinarith
          have hY : 0 ≤ 4 * M₂ ^ 2 * AZ * I ^ 2 := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hcc hY]
  have hQβ : 0 ≤ Q * βint := by positivity
  calc Q * βint * ∑ m₂ ∈ dyadic M₂, ∑ m₂' ∈ dyadic M₂,
        ((m₂ : ℝ) * m₂') * ∫ u, ∫ u', f u * f u' * ‖Zfun L (m₂ * u - m₂' * u')‖
      ≤ Q * βint * (4 * AZ * Q * M₂ * (∫ u, f u * H u) + 36 * AZ * M₂ ^ 4 * I ^ 2) :=
        mul_le_mul_of_nonneg_left hsum hQβ
    _ ≤ 40 * βint * AZ * Q ^ 2 * M₂ * (∫ u, f u * H u) +
        40 * βint * AZ * Q * M ^ 4 * I ^ 2 := by
        have h1 : 0 ≤ βint * AZ * Q ^ 2 * M₂ * (∫ u, f u * H u) := by positivity
        have h2 : 0 ≤ βint * AZ * Q * I ^ 2 := by positivity
        have h3 := mul_le_mul_of_nonneg_left hM4 h2
        have hM40 : 0 ≤ M₂ ^ 4 := by positivity
        nlinarith

end GuthMaynard.Affine.PartZ
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

alias Sig_small_le_dev := GuthMaynard.Affine.PartZ.Sig_small_le
end GuthMaynard.Affine
end


theorem solution : type_of% @GuthMaynard.Affine.Sig_small_le_dev := @GuthMaynard.Affine.Sig_small_le_dev
