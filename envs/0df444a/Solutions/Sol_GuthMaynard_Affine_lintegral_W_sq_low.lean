-- Prove2me | solution 1 for GuthMaynard.Affine.lintegral_W_sq_low
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T00:14:14.937582+00:00
-- url     : https://prove2.me/submissions/35dac6e2-5bd9-415d-9141-05fff9e4667a

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


























theorem ψ₁_nonneg (K x : ℝ) : 0 ≤ ψ₁ K x := (ψb K).nonneg

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

theorem norm_fourier_bump_le (b : ContDiffBump (0 : ℝ)) (y : ℝ) :
    ‖𝓕 (fun x => (b x : ℂ)) y‖ ≤ ∫ x, b x := by
  rw [Real.fourier_real_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext u
  rw [Circle.norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg b.nonneg]

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias norm_fourier_bump_le := GuthMaynard.Affine.PartB.norm_fourier_bump_le

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
theorem card_D₁_le {M₁ : ℝ} (h : 1 / 2 ≤ M₁) : ((D₁ M₁).card : ℝ) ≤ 6 * M₁ := by
  have h1 : (D₁ M₁).card ≤ (dyadic M₁).card + (dyadic M₁).card := by
    unfold D₁
    refine (Finset.card_union_le _ _).trans ?_
    rw [Finset.card_map]
  have h2 := card_dyadic_le (M := M₁) (by linarith)
  have h3 : ((D₁ M₁).card : ℝ) ≤ (dyadic M₁).card + (dyadic M₁).card := by exact_mod_cast h1
  linarith

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias card_D₁_le := GuthMaynard.Affine.PartB.card_D₁_le

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
theorem mem_dyadic {M : ℝ} {m : ℤ} (h : m ∈ dyadic M) : M < m ∧ (m : ℝ) ≤ 2 * M := by
  simp only [dyadic, Finset.mem_Ioc] at h
  exact ⟨Int.floor_lt.1 h.1, Int.le_floor.1 h.2⟩

theorem dyadic_eq_empty {M : ℝ} (h0 : 0 < M) (h : M < 1 / 2) : dyadic M = ∅ := by
  ext m
  simp only [Finset.notMem_empty, iff_false]
  intro hm
  obtain ⟨h1, h2⟩ := mem_dyadic hm
  have : (m : ℝ) < 1 := by linarith
  have : (0 : ℝ) < m := by linarith
  have h3 : m < 1 := by exact_mod_cast ‹(m : ℝ) < 1›
  have h4 : 0 < m := by exact_mod_cast this
  omega

theorem card_dyadic_le {M : ℝ} (h0 : 0 < M) : ((dyadic M).card : ℝ) ≤ 3 * M := by
  by_cases hM : M < 1 / 2
  · rw [dyadic_eq_empty h0 hM]; simp; linarith
  push Not at hM
  simp only [dyadic, Int.card_Ioc]
  have h1 : (⌊2 * M⌋ : ℝ) ≤ 2 * M := Int.floor_le _
  have h2 : M - 1 < (⌊M⌋ : ℝ) := Int.sub_one_lt_floor _
  rcases le_or_gt (⌊2 * M⌋ - ⌊M⌋) 0 with h | h
  · rw [Int.toNat_of_nonpos h]; simp; linarith
  · have : (((⌊2 * M⌋ - ⌊M⌋).toNat : ℤ) : ℝ) = (⌊2 * M⌋ : ℝ) - ⌊M⌋ := by
      rw [Int.toNat_of_nonneg h.le]; push_cast; ring
    rw [← Int.cast_natCast, this]
    linarith

theorem mem_D₁ {M₁ : ℝ} {m : ℤ} (h : m ∈ D₁ M₁) : M₁ < |(m : ℝ)| ∧ |(m : ℝ)| ≤ 2 * M₁ := by
  simp only [D₁, Finset.mem_union, Finset.mem_map, Equiv.coe_toEmbedding, Equiv.neg_apply] at h
  rcases h with h | ⟨n, hn, rfl⟩
  · obtain ⟨h1, h2⟩ := mem_dyadic h
    have : (0 : ℝ) ≤ m := by
      by_contra hc; push Not at hc
      have := lt_trans h1 hc
      have hM : 0 ≤ M₁ ∨ M₁ < 0 := le_or_gt 0 M₁
      rcases hM with hM | hM <;> linarith
    rw [abs_of_nonneg this]; exact ⟨h1, h2⟩
  · obtain ⟨h1, h2⟩ := mem_dyadic hn
    push_cast
    rw [abs_neg]
    by_cases hn0 : (0 : ℝ) ≤ n
    · rw [abs_of_nonneg hn0]; exact ⟨h1, h2⟩
    · push Not at hn0
      rw [abs_of_neg hn0]; constructor <;> linarith

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

theorem norm_fhat_le (f : ℝ → ℝ) (hnn : ∀ u, 0 ≤ f u) (ξ : ℝ) : ‖fhat f ξ‖ ≤ ∫ u, f u := by
  unfold fhat
  rw [Real.fourier_real_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext u
  rw [Circle.norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hnn u)]

theorem norm_Ffun_le {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 1 / 2 ≤ M₂) {f : ℝ → ℝ}
    (hf : Continuous f) (hcs : HasCompactSupport f) (hnn : ∀ u, 0 ≤ f u) {m₁ : ℤ}
    (hm₁ : m₁ ∈ D₁ M₁) (ξ : ℝ) :
    ‖Ffun M₂ f m₁ ξ‖ ≤ 6 * M₂ ^ 2 / M₁ * ∫ u, f u := by
  have hI : 0 ≤ ∫ u, f u := integral_nonneg hnn
  obtain ⟨hm1, -⟩ := mem_D₁ hm₁
  have hm0 : 0 < |(m₁ : ℝ)| := hM₁.trans hm1
  have hM₂0 : 0 < M₂ := by linarith
  unfold Ffun
  refine (norm_sum_le _ _).trans ?_
  calc ∑ m₂ ∈ dyadic M₂, ‖(((m₂ : ℝ) / |(m₁ : ℝ)| : ℝ) : ℂ) * fhat f (ξ * m₂ / m₁)‖
      ≤ ∑ m₂ ∈ dyadic M₂, 2 * M₂ / M₁ * ∫ u, f u := by
        refine Finset.sum_le_sum fun m₂ hm₂ => ?_
        obtain ⟨h1, h2⟩ := mem_dyadic hm₂
        have hm₂0 : (0 : ℝ) ≤ m₂ := by linarith
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        refine mul_le_mul ?_ (norm_fhat_le f hnn _) (norm_nonneg _) (by positivity)
        rw [div_le_div_iff₀ hm0 hM₁]
        nlinarith
    _ = (dyadic M₂).card * (2 * M₂ / M₁ * ∫ u, f u) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 3 * M₂ * (2 * M₂ / M₁ * ∫ u, f u) :=
        mul_le_mul_of_nonneg_right (card_dyadic_le hM₂0) (by positivity)
    _ = 6 * M₂ ^ 2 / M₁ * ∫ u, f u := by ring

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias norm_Ffun_le := GuthMaynard.Affine.PartG.norm_Ffun_le

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
theorem norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  rw [Complex.norm_exp]
  simp

theorem ψ₁_le_one (K x : ℝ) : ψ₁ K x ≤ 1 := (ψb K).le_one

theorem NK_le (K M₃ : ℝ) : (NK K M₃ : ℝ) ≤ (|K| + 2) * M₃ + 1 :=
  (Int.ceil_lt_add_one _).le

theorem NK_nonneg (K M₃ : ℝ) (h : 0 ≤ M₃) : 0 ≤ NK K M₃ :=
  Int.ceil_nonneg (by positivity)

theorem norm_Pfun_le_const (K : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ M₃ : ℝ, 1 ≤ M₃ → ∀ x : ℝ, ‖Pfun K M₃ x‖ ≤ A * M₃ := by
  refine ⟨2 * |K| + 7, by positivity, fun M₃ hM₃ x => ?_⟩
  unfold Pfun
  refine (norm_sum_le _ _).trans ?_
  have hN := NK_le K M₃
  have hN0 := NK_nonneg K M₃ (by linarith)
  calc ∑ m₃ ∈ Finset.Icc (-NK K M₃) (NK K M₃), ‖(ψ₁ K (m₃ / M₃) : ℂ) * ee (m₃ * x)‖
      ≤ ∑ m₃ ∈ Finset.Icc (-NK K M₃) (NK K M₃), (1 : ℝ) := by
        refine Finset.sum_le_sum fun m₃ _ => ?_
        rw [norm_mul, norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (ψ₁_nonneg _ _)]
        exact ψ₁_le_one _ _
    _ = 2 * (NK K M₃ : ℝ) + 1 := by
        rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul, mul_one, ← Int.cast_natCast,
          Int.toNat_of_nonneg (by omega)]
        push_cast; ring
    _ ≤ (2 * |K| + 7) * M₃ := by nlinarith [abs_nonneg K]

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
theorem mem_nearSet {x r : ℝ} {j : ℤ} : j ∈ nearSet x r ↔ |(j : ℝ) - x| ≤ r := by
  simp only [nearSet, Finset.mem_Icc, Int.ceil_le, Int.le_floor, abs_le]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

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

theorem norm_Pfun_le (K : ℝ) (k : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ M₃ : ℝ, 1 ≤ M₃ → ∀ Q : ℝ, 1 ≤ Q → ∀ x : ℝ,
      ‖Pfun K M₃ x‖ ≤ M₃ * B₀ K * (nearSet x (Q / M₃)).card + A * M₃ / Q ^ k := by
  obtain ⟨B, hB0, hB⟩ := fourier_bump_decay (ψb K) (k + 2)
  set S₀ := ∑' n : ℤ, tt n with hS₀
  have hS₀0 : 0 ≤ S₀ := tsum_nonneg tt_nonneg
  refine ⟨4 * B * S₀, by positivity, fun M₃ hM₃ Q hQ x => ?_⟩
  have hM₃0 : 0 < M₃ := by linarith
  have hQ0 : 0 < Q := by linarith
  set bh : ℝ → ℂ := fun y => 𝓕 (fun t => ((ψb K) t : ℂ)) y with hbh
  have hP : Pfun K M₃ x = ∑' j : ℤ, (M₃ : ℂ) * bh (M₃ * (j - x)) := by
    have hN : (ψb K).rOut * M₃ ≤ (NK K M₃ : ℝ) := Int.le_ceil _
    exact poisson_bump (ψb K) M₃ hM₃0 (NK K M₃) hN x
  set s := nearSet x (Q / M₃) with hs
  set g : ℤ → ℝ := fun j => (if j ∈ s then M₃ * B₀ K else 0) +
    M₃ * B / Q ^ k * (4 * tt (j - ⌊x⌋)) with hg
  have hB₀ : 0 ≤ B₀ K := by
    unfold B₀; exact integral_nonneg fun _ => ψ₁_nonneg _ _
  have hbound : ∀ j : ℤ, ‖(M₃ : ℂ) * bh (M₃ * (j - x))‖ ≤ g j := by
    intro j
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM₃0]
    have hsec : 0 ≤ M₃ * B / Q ^ k * (4 * tt (j - ⌊x⌋)) := by
      have := tt_nonneg (j - ⌊x⌋); positivity
    by_cases hj : j ∈ s
    · simp only [hg, if_pos hj]
      have : ‖bh (M₃ * (j - x))‖ ≤ B₀ K := norm_fourier_bump_le (ψb K) _
      nlinarith
    · simp only [hg, if_neg hj, zero_add]
      rw [hs, mem_nearSet] at hj
      push Not at hj
      set y := M₃ * ((j : ℝ) - x) with hy
      have hay : |y| = M₃ * |(j : ℝ) - x| := by rw [hy, abs_mul, abs_of_pos hM₃0]
      have hyQ : Q < |y| := by
        rw [hay]; rwa [div_lt_iff₀' hM₃0] at hj
      have hy1 : 1 + |(j : ℝ) - x| ≤ 1 + |y| := by
        rw [hay]; nlinarith [abs_nonneg ((j : ℝ) - x)]
      have hb := hB y
      have hpos : 0 < (1 + |y|) ^ (k + 2) := by positivity
      have hbh : ‖bh y‖ ≤ B / (1 + |y|) ^ (k + 2) := by
        rw [le_div_iff₀ hpos]; exact hb
      have hd : B / (1 + |y|) ^ (k + 2) ≤ B / Q ^ k * (1 / (1 + |(j : ℝ) - x|) ^ 2) := by
        rw [div_mul_div_comm, mul_one]
        refine div_le_div_of_nonneg_left hB0 (by positivity) ?_
        rw [pow_add]
        exact mul_le_mul (pow_le_pow_left₀ hQ0.le (by linarith) k)
          (pow_le_pow_left₀ (by positivity) hy1 2) (by positivity) (by positivity)
      have ht := tt_shift_le x j
      calc M₃ * ‖bh y‖ ≤ M₃ * (B / Q ^ k * (1 / (1 + |(j : ℝ) - x|) ^ 2)) :=
            mul_le_mul_of_nonneg_left (hbh.trans hd) hM₃0.le
        _ ≤ M₃ * (B / Q ^ k * (4 * tt (j - ⌊x⌋))) := by gcongr
        _ = M₃ * B / Q ^ k * (4 * tt (j - ⌊x⌋)) := by ring
  have hsum1 : Summable (fun j : ℤ => if j ∈ s then M₃ * B₀ K else 0) :=
    summable_of_ne_finset_zero (s := s) fun j hj => if_neg hj
  have hsum2 : Summable (fun j : ℤ => M₃ * B / Q ^ k * (4 * tt (j - ⌊x⌋))) :=
    ((summable_tt_shift ⌊x⌋).mul_left 4).mul_left _
  have hgs : Summable g := hsum1.add hsum2
  have hns : Summable (fun j : ℤ => ‖(M₃ : ℂ) * bh (M₃ * (j - x))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hgs
  have htsum1 : ∑' j : ℤ, (if j ∈ s then M₃ * B₀ K else 0) = M₃ * B₀ K * s.card := by
    rw [tsum_eq_sum (s := s) fun j hj => if_neg hj, Finset.sum_congr rfl fun j hj => if_pos hj,
      Finset.sum_const, nsmul_eq_mul]
    ring
  have htsum2 : ∑' j : ℤ, M₃ * B / Q ^ k * (4 * tt (j - ⌊x⌋)) = 4 * B * S₀ * M₃ / Q ^ k := by
    rw [tsum_mul_left, tsum_mul_left, tsum_tt_shift]
    ring
  rw [hP]
  calc ‖∑' j : ℤ, (M₃ : ℂ) * bh (M₃ * (j - x))‖
      ≤ ∑' j : ℤ, ‖(M₃ : ℂ) * bh (M₃ * (j - x))‖ := norm_tsum_le_tsum_norm hns
    _ ≤ ∑' j : ℤ, g j := hns.tsum_le_tsum hbound hgs
    _ = M₃ * B₀ K * s.card + 4 * B * S₀ * M₃ / Q ^ k := by
        rw [hg, hsum1.tsum_add hsum2, htsum1, htsum2]

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias norm_Pfun_le := GuthMaynard.Affine.PartG.norm_Pfun_le

alias norm_Pfun_le_const := GuthMaynard.Affine.PartG.norm_Pfun_le_const

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
theorem sum_D₁_le {M₁ : ℝ} (h : 1 / 2 ≤ M₁) (g : ℤ → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hg : ∀ m ∈ D₁ M₁, g m ≤ b) : ∑ m ∈ D₁ M₁, g m ≤ 6 * M₁ * b :=
  (Finset.sum_le_card_nsmul _ _ _ hg).trans (by
    rw [nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (card_D₁_le h) hb)

theorem lintegral_W_sq_low (C : ℝ) (c : ℕ → ℝ → ℝ) (K : ℝ) (hC : 1 ≤ C) (hK : 0 < K)
    (η : ℝ) (hη : 0 < η) :
    ∃ A T₁ : ℝ, 0 ≤ A ∧ ∀ T : ℝ, T₁ ≤ T → ∀ f : ℝ → ℝ, Adm C c T f →
      ∀ M M₁ M₂ M₃ : ℝ, Regime T M M₁ M₂ M₃ →
        ∫⁻ ξ in {ξ : ℝ | |ξ| ≤ T ^ 20}, ENNReal.ofReal (Wfun K M₁ M₂ M₃ f ξ ^ 2) ≤
          ENNReal.ofReal (A * (T ^ η) ^ 3 * M ^ 6 * (∫ u, f u) ^ 2) +
            2 * ∫⁻ ξ in regII T η M₁ M₃, ENNReal.ofReal (Wnear K M₁ M₂ M₃ (T ^ η) f ξ ^ 2) := by
  obtain ⟨AP, hAP, hP⟩ := norm_Pfun_le_const K
  set k : ℕ := ⌈10 / η⌉₊ with hk
  obtain ⟨Ak, hAk, hPk⟩ := norm_Pfun_le K k
  have hηk : 10 ≤ η * k := by
    have := Nat.le_ceil (10 / η)
    rw [← hk, div_le_iff₀ hη] at this
    linarith
  refine ⟨20736 * (AP ^ 2 + Ak ^ 2), 1, by positivity, ?_⟩
  intro T hT f hf M M₁ M₂ M₃ hr
  have hT0 : 0 < T := by linarith
  have hM : 0 < M := by linarith [hr.h₁, hr.h₁M]
  have hM₁0 : 0 < M₁ := by linarith [hr.h₁]
  have hM₂0 : 0 < M₂ := by linarith [hr.h₂]
  have hM₃ : 0 < M₃ := by linarith [hr.h₃]
  have hQ : 1 ≤ T ^ η := Real.one_le_rpow hT hη.le
  have hQk : T ^ 10 ≤ (T ^ η) ^ k := by
    rw [← Real.rpow_natCast (T ^ η), ← Real.rpow_mul hT0.le, ← Real.rpow_natCast T]
    exact Real.rpow_le_rpow_of_exponent_le hT (by push_cast; linarith)
  have hI0 : 0 ≤ ∫ u, f u := integral_nonneg hf.nonneg
  have hfc := adm_continuous hf
  have hfcs := adm_hasCompactSupport hf
  have hFb : ∀ m₁ ∈ D₁ M₁, ∀ ξ, ‖Ffun M₂ f m₁ ξ‖ ≤ 6 * M₂ ^ 2 / M₁ * ∫ u, f u :=
    fun m₁ hm ξ => norm_Ffun_le hM₁0 hr.h₂ hfc hfcs hf.nonneg hm ξ
  set Q := T ^ η with hQdef
  set I := ∫ u, f u with hIdef
  have hQ0 : 0 < Q := by linarith
  have hQk0 : 0 < Q ^ k := by positivity
  set WI := 36 * AP * M₃ * M₂ ^ 2 * I with hWI
  set WF := 36 * Ak * M₃ * M₂ ^ 2 * I / Q ^ k with hWF
  have hW0 : ∀ ξ, 0 ≤ Wfun K M₁ M₂ M₃ f ξ := fun ξ =>
    Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hWI_le : ∀ ξ, Wfun K M₁ M₂ M₃ f ξ ≤ WI := by
    intro ξ
    unfold Wfun
    refine (sum_D₁_le hr.h₁ _ (b := AP * M₃ * (6 * M₂ ^ 2 / M₁ * I)) (by positivity)
      fun m₁ hm => mul_le_mul (hP M₃ hr.h₃ _) (hFb m₁ hm ξ) (norm_nonneg _)
        (by positivity)).trans (le_of_eq ?_)
    rw [hWI]; field_simp; ring
  have hWF_le : ∀ ξ, Wfun K M₁ M₂ M₃ f ξ ≤ Wnear K M₁ M₂ M₃ Q f ξ + WF := by
    intro ξ
    unfold Wfun Wnear
    calc ∑ m₁ ∈ D₁ M₁, ‖Pfun K M₃ (ξ / m₁)‖ * ‖Ffun M₂ f m₁ ξ‖
        ≤ ∑ m₁ ∈ D₁ M₁, (M₃ * B₀ K * ((nearSet (ξ / m₁) (Q / M₃)).card : ℝ) +
            Ak * M₃ / Q ^ k) * ‖Ffun M₂ f m₁ ξ‖ :=
          Finset.sum_le_sum fun m₁ _ =>
            mul_le_mul_of_nonneg_right (hPk M₃ hr.h₃ Q hQ _) (norm_nonneg _)
      _ = ∑ m₁ ∈ D₁ M₁, M₃ * B₀ K * ((nearSet (ξ / m₁) (Q / M₃)).card : ℝ) *
            ‖Ffun M₂ f m₁ ξ‖ + ∑ m₁ ∈ D₁ M₁, Ak * M₃ / Q ^ k * ‖Ffun M₂ f m₁ ξ‖ := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ _ := by
          gcongr
          refine (sum_D₁_le hr.h₁ _ (b := Ak * M₃ / Q ^ k * (6 * M₂ ^ 2 / M₁ * I))
            (by positivity) fun m₁ hm => mul_le_mul_of_nonneg_left (hFb m₁ hm ξ)
              (by positivity)).trans (le_of_eq ?_)
          rw [hWF]; field_simp; ring
  set R := 4 * Q * M₁ / M₃ with hR
  have hball : ∀ r : ℝ, {ξ : ℝ | |ξ| ≤ r} = Metric.closedBall 0 r := by
    intro r; ext ξ; simp
  have hsub : {ξ : ℝ | |ξ| ≤ T ^ 20} ⊆ {ξ : ℝ | |ξ| ≤ R} ∪ regII T η M₁ M₃ := by
    intro ξ hξ
    by_cases h : |ξ| ≤ R
    · exact Or.inl h
    · exact Or.inr ⟨lt_of_not_ge h, hξ⟩
  have hIreg : ∫⁻ ξ in {ξ : ℝ | |ξ| ≤ R}, ENNReal.ofReal (Wfun K M₁ M₂ M₃ f ξ ^ 2) ≤
      ENNReal.ofReal (WI ^ 2 * (2 * R)) := by
    calc _ ≤ ∫⁻ ξ in {ξ : ℝ | |ξ| ≤ R}, ENNReal.ofReal (WI ^ 2) :=
          lintegral_mono fun ξ =>
            ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hW0 ξ) (hWI_le ξ) 2)
      _ = ENNReal.ofReal (WI ^ 2) * ENNReal.ofReal (2 * R) := by
          rw [setLIntegral_const, hball, Real.volume_closedBall]
      _ = ENNReal.ofReal (WI ^ 2 * (2 * R)) := (ENNReal.ofReal_mul (sq_nonneg _)).symm
  have hIIreg : ∫⁻ ξ in regII T η M₁ M₃, ENNReal.ofReal (Wfun K M₁ M₂ M₃ f ξ ^ 2) ≤
      (2 * ∫⁻ ξ in regII T η M₁ M₃, ENNReal.ofReal (Wnear K M₁ M₂ M₃ Q f ξ ^ 2)) +
        ENNReal.ofReal (2 * WF ^ 2 * (2 * T ^ 20)) := by
    calc _ ≤ ∫⁻ ξ in regII T η M₁ M₃, (2 * ENNReal.ofReal (Wnear K M₁ M₂ M₃ Q f ξ ^ 2) +
            ENNReal.ofReal (2 * WF ^ 2)) := by
          refine lintegral_mono fun ξ => ?_
          have h1 := hWF_le ξ
          have h0 := hW0 ξ
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          nlinarith [sq_nonneg (Wnear K M₁ M₂ M₃ Q f ξ - WF)]
      _ = (2 * ∫⁻ ξ in regII T η M₁ M₃, ENNReal.ofReal (Wnear K M₁ M₂ M₃ Q f ξ ^ 2)) +
            ENNReal.ofReal (2 * WF ^ 2) * volume (regII T η M₁ M₃) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by norm_num),
            setLIntegral_const]
      _ ≤ _ := by
          refine add_le_add le_rfl ?_
          rw [ENNReal.ofReal_mul (p := 2 * WF ^ 2) (q := 2 * T ^ 20) (by positivity)]
          refine mul_le_mul' (le_refl (ENNReal.ofReal (2 * WF ^ 2))) ?_
          rw [← Real.volume_closedBall, ← hball]
          exact measure_mono fun ξ hξ => hξ.2
  have hreal : WI ^ 2 * (2 * R) + 2 * WF ^ 2 * (2 * T ^ 20) ≤
      20736 * (AP ^ 2 + Ak ^ 2) * Q ^ 3 * M ^ 6 * I ^ 2 := by
    have e1 : WI ^ 2 * (2 * R) =
        (10368 * AP ^ 2 * Q * I ^ 2) * (M₁ * M₃ * M₂ ^ 4) := by
      rw [hWI, hR]; field_simp; ring
    have e2 : 2 * WF ^ 2 * (2 * T ^ 20) =
        (5184 * Ak ^ 2 * I ^ 2) * (M₃ ^ 2 * M₂ ^ 4) * (T ^ 20 / (Q ^ k) ^ 2) := by
      rw [hWF]; field_simp; ring
    have hr1 : T ^ 20 / (Q ^ k) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      calc T ^ 20 = (T ^ 10) ^ 2 := by ring
        _ ≤ (Q ^ k) ^ 2 := pow_le_pow_left₀ (by positivity) hQk 2
    have hm1 : M₁ * M₃ * M₂ ^ 4 ≤ M * (2 * M) * M ^ 4 := by
      gcongr
      · exact hr.h₁M.le
      · exact hr.h₃M
      · exact hr.h₂M.le
    have hm2 : M₃ ^ 2 * M₂ ^ 4 ≤ (2 * M) ^ 2 * M ^ 4 := by
      gcongr
      · exact hr.h₃M
      · exact hr.h₂M.le
    have hQ3 : Q ≤ Q ^ 3 := le_self_pow₀ hQ (by norm_num)
    have hQ3' : 1 ≤ Q ^ 3 := one_le_pow₀ hQ
    rw [e1, e2]
    calc (10368 * AP ^ 2 * Q * I ^ 2) * (M₁ * M₃ * M₂ ^ 4) +
          (5184 * Ak ^ 2 * I ^ 2) * (M₃ ^ 2 * M₂ ^ 4) * (T ^ 20 / (Q ^ k) ^ 2)
        ≤ (10368 * AP ^ 2 * Q ^ 3 * I ^ 2) * (M * (2 * M) * M ^ 4) +
          (5184 * Ak ^ 2 * I ^ 2) * ((2 * M) ^ 2 * M ^ 4) * Q ^ 3 := by
          have t1 : (10368 * AP ^ 2 * Q * I ^ 2) * (M₁ * M₃ * M₂ ^ 4) ≤
              (10368 * AP ^ 2 * Q ^ 3 * I ^ 2) * (M * (2 * M) * M ^ 4) :=
            mul_le_mul (by gcongr) hm1 (by positivity) (by positivity)
          have t2 : (5184 * Ak ^ 2 * I ^ 2) * (M₃ ^ 2 * M₂ ^ 4) * (T ^ 20 / (Q ^ k) ^ 2) ≤
              (5184 * Ak ^ 2 * I ^ 2) * ((2 * M) ^ 2 * M ^ 4) * Q ^ 3 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hm2 (by positivity)) (hr1.trans hQ3')
              (by positivity) (by positivity)
          exact add_le_add t1 t2
      _ = 20736 * (AP ^ 2 + Ak ^ 2) * Q ^ 3 * M ^ 6 * I ^ 2 := by ring
  calc ∫⁻ ξ in {ξ : ℝ | |ξ| ≤ T ^ 20}, ENNReal.ofReal (Wfun K M₁ M₂ M₃ f ξ ^ 2)
      ≤ ∫⁻ ξ in {ξ : ℝ | |ξ| ≤ R} ∪ regII T η M₁ M₃,
          ENNReal.ofReal (Wfun K M₁ M₂ M₃ f ξ ^ 2) := lintegral_mono_set hsub
    _ ≤ (∫⁻ ξ in {ξ : ℝ | |ξ| ≤ R}, ENNReal.ofReal (Wfun K M₁ M₂ M₃ f ξ ^ 2)) +
          ∫⁻ ξ in regII T η M₁ M₃, ENNReal.ofReal (Wfun K M₁ M₂ M₃ f ξ ^ 2) :=
        lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal (WI ^ 2 * (2 * R)) +
          ((2 * ∫⁻ ξ in regII T η M₁ M₃, ENNReal.ofReal (Wnear K M₁ M₂ M₃ Q f ξ ^ 2)) +
            ENNReal.ofReal (2 * WF ^ 2 * (2 * T ^ 20))) := add_le_add hIreg hIIreg
    _ = ENNReal.ofReal (WI ^ 2 * (2 * R) + 2 * WF ^ 2 * (2 * T ^ 20)) +
          2 * ∫⁻ ξ in regII T η M₁ M₃, ENNReal.ofReal (Wnear K M₁ M₂ M₃ Q f ξ ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]; ring
    _ ≤ _ := by
        gcongr

end GuthMaynard.Affine.PartR
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias lintegral_W_sq_low_dev := GuthMaynard.Affine.PartR.lintegral_W_sq_low


end GuthMaynard.Affine
end


theorem solution : type_of% @GuthMaynard.Affine.lintegral_W_sq_low_dev := @GuthMaynard.Affine.lintegral_W_sq_low_dev
