-- Prove2me | solution 1 for GuthMaynard.Affine.iteration
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T00:14:19.705449+00:00
-- url     : https://prove2.me/submissions/8a64fa77-8b9c-400e-b221-aaa0e9cbc85c

import Mathlib
import Definitions.Def_GuthMaynard
import Definitions.Def_GuthMaynardAffine
import Theorems.Thm_GuthMaynard_Affine_Sig_large_le
import Theorems.Thm_GuthMaynard_Affine_Sig_small_le
import Theorems.Thm_GuthMaynard_Affine_integral_mul_Hfun_le
import Theorems.Thm_GuthMaynard_Affine_lintegral_W_sq_III
import Theorems.Thm_GuthMaynard_Affine_lintegral_W_sq_low
import Theorems.Thm_GuthMaynard_Affine_lintegral_Wnear_sq_le_Sig

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

theorem ψ₁_nonneg (K x : ℝ) : 0 ≤ ψ₁ K x := (ψb K).nonneg

theorem ψ₁_eq_one {K x : ℝ} (hx : |x| ≤ |K| + 1) : ψ₁ K x = 1 :=
  (ψb K).one_of_mem_closedBall (by rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact hx)

theorem adm_continuous {C : ℝ} {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hf : Adm C c T f) :
    Continuous f :=
  hf.smooth.continuous

theorem adm_hasCompactSupport {C : ℝ} {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hf : Adm C c T f) :
    HasCompactSupport f :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport f)
    (closure_minimal hf.supp isClosed_Icc)

theorem gsum_nonneg {K M₁ M₂ M₃ : ℝ} {f : ℝ → ℝ} (hf : ∀ u, 0 ≤ f u) (u : ℝ) :
    0 ≤ gsum K M₁ M₂ M₃ f u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hf _

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
theorem βint_pos : 0 < βint := by
  have h1 : ∫ x in Set.Icc (-1 : ℝ) 1, β x = 2 := by
    rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ => (1 : ℝ)) (fun x hx =>
      β_eq_one (abs_le.2 ⟨hx.1, hx.2⟩))]
    simp [Measure.real]; norm_num
  have h2 : ∫ x in Set.Icc (-1 : ℝ) 1, β x ≤ βint :=
    setIntegral_le_integral βb.integrable (Filter.Eventually.of_forall β_nonneg)
  linarith

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias βint_pos := GuthMaynard.Affine.PartB.βint_pos

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
theorem mem_dyadic_bounds {M : ℝ} {m : ℤ} (h : m ∈ dyadic M) : M < m ∧ (m : ℝ) ≤ 2 * M := by
  simp only [dyadic, Finset.mem_Ioc] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · have : ⌊M⌋ + 1 ≤ m := h1
    have h3 : M < (⌊M⌋ : ℝ) + 1 := Int.lt_floor_add_one M
    have : ((⌊M⌋ + 1 : ℤ) : ℝ) ≤ m := by exact_mod_cast this
    push_cast at this; linarith
  · have : (m : ℝ) ≤ (⌊2 * M⌋ : ℝ) := by exact_mod_cast h2
    linarith [Int.floor_le (2 * M)]

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
theorem half_le_of_dyadic_nonempty {M : ℝ} (h : (dyadic M).Nonempty) : 1 / 2 ≤ M := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨h1, h2⟩ := mem_dyadic_bounds hm
  have hm0 : (0 : ℝ) < m := by linarith
  have : (1 : ℤ) ≤ m := by exact_mod_cast hm0
  have : (1 : ℝ) ≤ m := by exact_mod_cast this
  linarith

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias half_le_of_dyadic_nonempty := GuthMaynard.Affine.PartB.half_le_of_dyadic_nonempty

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

end GuthMaynard.Affine.PartB
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
noncomputable def prof (a b R : ℝ) (t : ℝ) : ℝ := if t ≤ R then a else b / t ^ 2

theorem prof_nonneg {a b R : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (t : ℝ) : 0 ≤ prof a b R t := by
  unfold prof; split_ifs <;> positivity

theorem integrable_prof_abs {a b R : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hR : 0 < R) :
    Integrable (fun ξ : ℝ => prof a b R |ξ|) := by
  have hm : Measurable (fun ξ : ℝ => prof a b R |ξ|) := by
    unfold prof
    exact Measurable.ite (measurableSet_le measurable_abs measurable_const) measurable_const
      (measurable_const.div ((measurable_abs).pow_const 2))
  refine Integrable.mono' ((integrable_inv_one_add_sq.comp_div hR.ne').const_mul
    (2 * (a + b / R ^ 2))) hm.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (prof_nonneg ha hb _)]
  have hq : 0 < 1 + (ξ / R) ^ 2 := by positivity
  unfold prof
  split_ifs with h
  · have : (ξ / R) ^ 2 ≤ 1 := by
      rw [div_pow, div_le_one (by positivity), ← sq_abs ξ]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [← div_eq_mul_inv, le_div_iff₀ hq]
    have : 0 ≤ b / R ^ 2 := by positivity
    nlinarith
  · push Not at h
    have hξ : R ^ 2 < ξ ^ 2 := by rw [← sq_abs ξ]; exact pow_lt_pow_left₀ h hR.le two_ne_zero
    have hξ0 : 0 < ξ ^ 2 := by linarith [sq_nonneg R, pow_pos hR 2]
    rw [sq_abs, ← div_eq_mul_inv, le_div_iff₀ hq, div_pow]
    rw [div_mul_eq_mul_div, div_le_iff₀ hξ0]
    have hR2 : 0 < R ^ 2 := by positivity
    set q := ξ ^ 2 / R ^ 2 with hqdef
    have hxq : ξ ^ 2 = q * R ^ 2 := by rw [hqdef]; field_simp
    have e1 : 2 * (a + b / R ^ 2) * ξ ^ 2 = 2 * a * ξ ^ 2 + 2 * b * q := by
      rw [hxq]; field_simp
    rw [e1]
    have h1 : 1 ≤ q := by rw [hqdef, le_div_iff₀ hR2]; linarith
    have : 0 ≤ 2 * a * ξ ^ 2 := by positivity
    nlinarith

theorem integral_prof_abs {a b R : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hR : 0 < R) :
    ∫ ξ : ℝ, prof a b R |ξ| = 2 * (a * R + b / R) := by
  rw [integral_comp_abs (f := prof a b R)]
  congr 1
  have hI1 : IntegrableOn (prof a b R) (Set.Ioc 0 R) := by
    refine (integrableOn_const (C := a) (by simp)).congr_fun (fun t ht => ?_) measurableSet_Ioc
    simp [prof, ht.2]
  have hrp : Set.EqOn (prof a b R) (fun t => b * t ^ (-2 : ℝ)) (Set.Ioi R) := by
    intro t ht
    have ht' : ¬ t ≤ R := not_le.2 ht
    have tpos : 0 < t := hR.trans ht
    simp only [prof, ht', if_false]
    rw [Real.rpow_neg tpos.le, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      div_eq_mul_inv]
  have hI2' : IntegrableOn (fun t : ℝ => b * t ^ (-2 : ℝ)) (Set.Ioi R) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR).const_mul b
  have hI2 : IntegrableOn (prof a b R) (Set.Ioi R) :=
    hI2'.congr_fun hrp.symm measurableSet_Ioi
  rw [← Set.Ioc_union_Ioi_eq_Ioi hR.le, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi hI1 hI2]
  rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => a) (fun t ht => by simp [prof, ht.2]),
    setIntegral_congr_fun measurableSet_Ioi hrp, integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR]
  simp only [setIntegral_const, Measure.real, Real.volume_Ioc, sub_zero,
    ENNReal.toReal_ofReal hR.le, smul_eq_mul]
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  field_simp

theorem ae_ne_zero : ∀ᵐ ξ : ℝ ∂volume, ξ ≠ 0 := by
  rw [ae_iff]; simp

theorem cont_hcs {C : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hsupp : Function.support f ⊆ Set.Icc (1 / C) C) : HasCompactSupport f :=
  HasCompactSupport.intro isCompact_Icc fun x hx => by
    by_contra h; exact hx (hsupp h)

/-- Fourier inversion, pointwise. -/
theorem inversion {F : ℝ → ℂ} (hc : Continuous F) (hi : Integrable F) (hi' : Integrable (𝓕 F))
    (x : ℝ) : F x = ∫ ξ, 𝐞 (ξ * x) • 𝓕 F ξ := by
  have := congrFun (hc.fourierInv_fourier_eq hi hi') x
  rw [← this, Real.fourierInv_eq]
  simp [mul_comm]

/-! ### Large `M`: Lipschitz bound, mass lower bound, Riemann sums -/
theorem decay_le {C : ℝ} {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hf : Adm C c T f) (hT : 0 < T)
    (j : ℕ) (ξ : ℝ) (hξ : ξ ≠ 0) :
    ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ≤ |c j 1| * T ^ (j + 1) * (⨆ u, f u) / |ξ| ^ j := by
  have hS : 0 ≤ ⨆ u, f u := Real.iSup_nonneg hf.nonneg
  refine (hf.decay j 1 one_pos ξ hξ).trans ?_
  calc c j 1 * T ^ (1 : ℝ) * (T / |ξ|) ^ j * (⨆ u, f u)
      = c j 1 * T ^ (j + 1) * (⨆ u, f u) / |ξ| ^ j := by
        rw [Real.rpow_one, div_pow, pow_succ]; field_simp
    _ ≤ |c j 1| * T ^ (j + 1) * (⨆ u, f u) / |ξ| ^ j := by
        gcongr; exact le_abs_self _

theorem fourier_integrable {C : ℝ} {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hf : Adm C c T f)
    (hT : 0 < T) : Integrable (𝓕 (fun u => (f u : ℂ))) := by
  have hcont : Continuous f := hf.smooth.continuous
  have hS : 0 ≤ ⨆ u, f u := Real.iSup_nonneg hf.nonneg
  have hFi : Integrable (fun u => (f u : ℂ)) :=
    (hcont.integrable_of_hasCompactSupport (cont_hcs hcont hf.supp)).ofReal
  have hFFc : Continuous (𝓕 (fun u => (f u : ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hFi
  have ha : 0 ≤ |c 0 1| * T * ⨆ u, f u := by positivity
  have hb : 0 ≤ |c 2 1| * T ^ 3 * ⨆ u, f u := by positivity
  refine (integrable_prof_abs ha hb hT).mono' hFFc.aestronglyMeasurable ?_
  filter_upwards [ae_ne_zero] with ξ hξ
  unfold prof
  split_ifs with h
  · have := decay_le hf hT 0 ξ hξ
    simpa using this
  · exact decay_le hf hT 2 ξ hξ

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
/-- The dilated bump `T β(T z)`. -/
noncomputable def βT (T : ℝ) (z : ℝ) : ℝ := T * β (T * z)

theorem smooth_eq_conv (T : ℝ) (f : ℝ → ℝ) :
    smooth T f = f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] βT T := by
  ext x
  simp only [smooth, convolution_def, ContinuousLinearMap.mul_apply', βT, ← integral_const_mul]
  congr 1; ext y; ring

theorem β_continuous : Continuous β := βb.continuous

theorem β_le_one (x : ℝ) : β x ≤ 1 := βb.le_one

theorem β_eq_zero {x : ℝ} (hx : 2 ≤ |x|) : β x = 0 := by
  by_contra h
  have : x ∈ Function.support β := h
  rw [show Function.support β = Function.support βb from rfl, βb.support_eq] at this
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at this
  exact absurd this (not_lt.2 (by simpa [βb] using hx))

theorem β_hasCompactSupport : HasCompactSupport β := βb.hasCompactSupport

theorem β_integrable : Integrable β := βb.integrable

theorem βT_integrable (T : ℝ) : Integrable (βT T) := by
  rcases eq_or_ne T 0 with rfl | hT
  · have : βT 0 = fun _ => 0 := by ext z; simp [βT]
    rw [this]; exact integrable_zero _ _ _
  exact (β_integrable.comp_mul_left' hT).const_mul T

theorem integral_βT {T : ℝ} (hT : 0 < T) : ∫ z, βT T z = βint := by
  simp only [βT, integral_const_mul, Measure.integral_comp_mul_left (fun z => β z), βint]
  rw [abs_of_pos (inv_pos.2 hT), smul_eq_mul]; field_simp

theorem βT_hasCompactSupport {T : ℝ} (hT : T ≠ 0) : HasCompactSupport (βT T) := by
  have : HasCompactSupport (fun z : ℝ => β (T * z)) := by
    simpa [smul_eq_mul] using β_hasCompactSupport.comp_smul hT
  exact this.mul_left

theorem smooth_contDiff (T : ℝ) (f : ℝ → ℝ) (hf : Continuous f) (hcs : HasCompactSupport f) :
    ContDiff ℝ (⊤ : ℕ∞) (smooth T f) := by
  rcases eq_or_ne T 0 with rfl | hT
  · have : smooth 0 f = fun _ => 0 := by ext x; simp [smooth]
    rw [this]; exact contDiff_const
  rw [smooth_eq_conv]
  have hcsg : HasCompactSupport (βT T) := by
    have : HasCompactSupport (fun z : ℝ => β (T * z)) := by
      simpa [smul_eq_mul] using β_hasCompactSupport.comp_smul hT
    exact this.mul_left
  have hg : ContDiff ℝ (⊤ : ℕ∞) (βT T) :=
    contDiff_const.mul ((βb.contDiff (n := (⊤ : ℕ∞))).comp (contDiff_const.mul contDiff_id))
  exact hcsg.contDiff_convolution_right _ (hf.locallyIntegrable) hg

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias smooth_contDiff := GuthMaynard.Affine.PartS.smooth_contDiff

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
theorem smooth_support (C : ℝ) (hC : 1 ≤ C) (T : ℝ) (hT : 4 * C ≤ T) (f : ℝ → ℝ)
    (hfs : Function.support f ⊆ Set.Icc (1 / C) C) :
    Function.support (smooth T f) ⊆ Set.Icc (1 / (2 * C)) (2 * C) := by
  intro x hx
  by_contra hxI
  apply hx
  have hC0 : 0 < C := by linarith
  have hT0 : 0 < T := by linarith
  have h0 : ∀ y, β (T * (x - y)) * f y = 0 := by
    intro y
    by_cases hy : f y = 0
    · simp [hy]
    have hyI := hfs hy
    rw [β_eq_zero, zero_mul]
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hxI
    rcases hxI with h | h
    · -- x < 1/(2C) ≤ y - 1/(2C)
      have h1 : 1 / C = 1 / (2 * C) + 1 / (2 * C) := by field_simp; ring
      have h2 : 1 / (2 * C) ≤ y - x := by linarith [hyI.1]
      have h3 : 0 < 1 / (2 * C) := by positivity
      rw [abs_mul, abs_of_pos hT0, abs_sub_comm, abs_of_pos (by linarith)]
      calc (2 : ℝ) = 4 * C * (1 / (2 * C)) := by field_simp; ring
        _ ≤ T * (y - x) := by gcongr
    · have h2 : C ≤ x - y := by linarith [hyI.2]
      rw [abs_mul, abs_of_pos hT0, abs_of_pos (by linarith)]
      nlinarith
  simp [smooth, h0]

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias smooth_support := GuthMaynard.Affine.PartS.smooth_support

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

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace
theorem βint_pos' : 0 < βint := by
  have h1 : ∫ x in Set.Icc (-1 : ℝ) 1, β x = 2 := by
    rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ => (1 : ℝ)) (fun x hx =>
      β_eq_one (abs_le.2 ⟨hx.1, hx.2⟩))]
    simp [Measure.real]; norm_num
  have h2 : ∫ x in Set.Icc (-1 : ℝ) 1, β x ≤ βint :=
    setIntegral_le_integral β_integrable (Filter.Eventually.of_forall β_nonneg)
  linarith

theorem βT_nonneg {T : ℝ} (hT : 0 ≤ T) (z : ℝ) : 0 ≤ βT T z := mul_nonneg hT (β_nonneg _)

theorem βT_le {T : ℝ} (hT : 0 ≤ T) (z : ℝ) : βT T z ≤ T := by
  unfold βT; nlinarith [β_le_one (T * z)]

theorem βT_continuous (T : ℝ) : Continuous (βT T) := by
  unfold βT; exact continuous_const.mul (β_continuous.comp (continuous_const.mul continuous_id))

theorem smooth_apply (T : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    smooth T f x = ∫ y, f y * βT T (x - y) := by
  rw [smooth_eq_conv, convolution_def]; rfl

theorem integral_smooth (T : ℝ) (hT : 0 < T) (f : ℝ → ℝ) (hf : Continuous f)
    (hcs : HasCompactSupport f) :
    ∫ u, smooth T f u = βint * ∫ u, f u := by
  rw [smooth_eq_conv, integral_convolution (ContinuousLinearMap.mul ℝ ℝ)
    (hf.integrable_of_hasCompactSupport hcs) (βT_integrable T), integral_βT hT]
  simp [mul_comm]

theorem norm_fourier_le (g : ℝ → ℂ) (ξ : ℝ) : ‖𝓕 g ξ‖ ≤ ∫ x, ‖g x‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

/-- `𝓕 g(ξ) = 𝓕 f(ξ) β̂(ξ/T)`, hence `‖𝓕 g‖ ≤ ‖β‖₁ ‖𝓕 f‖`. -/
theorem norm_fourier_smooth_le (T : ℝ) (hT : 0 < T) (f : ℝ → ℝ) (hf : Continuous f)
    (hcs : HasCompactSupport f) (ξ : ℝ) :
    ‖𝓕 (fun u => (smooth T f u : ℂ)) ξ‖ ≤ βint * ‖𝓕 (fun u => (f u : ℂ)) ξ‖ := by
  have hfi : Integrable (fun u => (f u : ℂ)) := (hf.integrable_of_hasCompactSupport hcs).ofReal
  have hbi : Integrable (fun u => (βT T u : ℂ)) := (βT_integrable T).ofReal
  have heq : (fun u => (smooth T f u : ℂ)) =
      (fun u => (f u : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] (fun u => (βT T u : ℂ)) := by
    ext x
    rw [smooth_apply, convolution_def, ← integral_complex_ofReal]
    simp
  rw [heq, Real.fourier_mul_convolution_eq hfi hbi, norm_mul, mul_comm]
  gcongr
  refine (norm_fourier_le _ ξ).trans (le_of_eq ?_)
  rw [← integral_βT hT]
  congr 1; ext z
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (βT_nonneg hT.le z)]

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias norm_fourier_smooth_le := GuthMaynard.Affine.PartS.norm_fourier_smooth_le

alias integral_smooth := GuthMaynard.Affine.PartS.integral_smooth

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace
/-- Cauchy–Schwarz against a nonnegative weight. -/
theorem sq_integral_mul_le {w g : ℝ → ℝ} (hw : ∀ y, 0 ≤ w y) (h1 : Integrable w)
    (h2 : Integrable (fun y => g y * w y)) (h3 : Integrable (fun y => g y ^ 2 * w y))
    (hW : 0 < ∫ y, w y) :
    (∫ y, g y * w y) ^ 2 ≤ (∫ y, w y) * ∫ y, g y ^ 2 * w y := by
  set A := ∫ y, g y * w y
  set W := ∫ y, w y
  set B := ∫ y, g y ^ 2 * w y
  have key : ∀ t : ℝ, 0 ≤ B - 2 * t * A + t ^ 2 * W := by
    intro t
    have e : ∫ y, (g y - t) ^ 2 * w y = B - 2 * t * A + t ^ 2 * W := by
      have : (fun y => (g y - t) ^ 2 * w y) =
          fun y => g y ^ 2 * w y - (2 * t) * (g y * w y) + t ^ 2 * w y := by
        ext y; ring
      have i1 : Integrable (fun y => g y ^ 2 * w y - 2 * t * (g y * w y)) := h3.sub (h2.const_mul _)
      have i2 : Integrable (fun y => t ^ 2 * w y) := h1.const_mul _
      have i3 : Integrable (fun y => 2 * t * (g y * w y)) := h2.const_mul _
      rw [this, integral_add i1 i2, integral_sub h3 i3, integral_const_mul, integral_const_mul]
    rw [← e]
    exact integral_nonneg fun y => mul_nonneg (sq_nonneg _) (hw y)
  have := key (A / W)
  have e2 : B - 2 * (A / W) * A + (A / W) ^ 2 * W = B - A ^ 2 / W := by
    field_simp; ring
  rw [e2, sub_nonneg, div_le_iff₀ hW] at this
  linarith

theorem integral_smooth_sq_le (T : ℝ) (hT : 0 < T) (f : ℝ → ℝ) (hf : Continuous f)
    (hcs : HasCompactSupport f) :
    ∫ u, smooth T f u ^ 2 ≤ βint ^ 2 * ∫ u, f u ^ 2 := by
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hcs
  have hcs2 : HasCompactSupport (fun u => f u ^ 2) :=
    hcs.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)
  have hf2i : Integrable (fun u => f u ^ 2) :=
    (hf.pow 2).integrable_of_hasCompactSupport hcs2
  have hwm : ∀ x, Integrable (fun y => βT T (x - y)) := fun x => (βT_integrable T).comp_sub_left x
  have hbd : ∀ x, ∀ᵐ y ∂(volume : Measure ℝ), ‖βT T (x - y)‖ ≤ T := fun x =>
    Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (βT_nonneg hT.le _)]; exact βT_le hT.le _
  have hmeas : ∀ x, AEStronglyMeasurable (fun y => βT T (x - y)) volume := fun x =>
    ((βT_continuous T).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hpt : ∀ x, smooth T f x ^ 2 ≤ βint * ((fun u => f u ^ 2) ⋆[ContinuousLinearMap.mul ℝ ℝ,
      volume] βT T) x := by
    intro x
    rw [smooth_apply, convolution_def]
    simp only [ContinuousLinearMap.mul_apply']
    have hW : ∫ y, βT T (x - y) = βint := by
      rw [integral_sub_left_eq_self (fun y => βT T y), integral_βT hT]
    rw [← hW]
    exact sq_integral_mul_le (fun y => βT_nonneg hT.le _) (hwm x)
      (hfi.mul_bdd (hmeas x) (hbd x)) (hf2i.mul_bdd (hmeas x) (hbd x)) (hW ▸ βint_pos')
  have hcsg : HasCompactSupport (βT T) := βT_hasCompactSupport hT.ne'
  have hsc : HasCompactSupport (smooth T f) := by
    rw [smooth_eq_conv]; exact hcs.convolution _ hcsg
  have hsc2 : HasCompactSupport (fun u => smooth T f u ^ 2) :=
    hsc.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)
  have hsi : Integrable (fun u => smooth T f u ^ 2) :=
    ((smooth_contDiff T f hf hcs).continuous.pow 2).integrable_of_hasCompactSupport hsc2
  have hci := (hf2i.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) (βT_integrable T)).const_mul
    βint
  refine (integral_mono hsi hci hpt).trans (le_of_eq ?_)
  have hc := integral_convolution (μ := volume) (ν := volume) (ContinuousLinearMap.mul ℝ ℝ) hf2i
    (βT_integrable T)
  rw [integral_βT hT, ContinuousLinearMap.mul_apply'] at hc
  rw [integral_const_mul, hc]
  ring

/-- `β` as a complex function. -/
noncomputable def βc (x : ℝ) : ℂ := (β x : ℂ)

theorem βc_hasCompactSupport : HasCompactSupport βc :=
  β_hasCompactSupport.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)

theorem βc_contDiff : ContDiff ℝ (⊤ : ℕ∞) βc :=
  Complex.ofRealCLM.contDiff.comp (βb.contDiff (n := (⊤ : ℕ∞)))

/-- `β` as a Schwartz function. -/
noncomputable def βS : 𝓢(ℝ, ℂ) := βc_hasCompactSupport.toSchwartzMap βc_contDiff

/-- `ψ = 𝓕⁻¹ β`. -/
noncomputable def ψS : 𝓢(ℝ, ℂ) := 𝓕⁻ βS

theorem ψS_apply (s : ℝ) : ψS s = ∫ v : ℝ, 𝐞 (v * s) • βc v := by
  rw [ψS, SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  simp [βS, mul_comm]

theorem norm_ψS_le (s : ℝ) : ‖ψS s‖ ≤ βint := by
  rw [ψS_apply]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  unfold βint; congr 1; ext v
  rw [Circle.norm_smul, βc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (β_nonneg _)]

/-- The dilated inverse transform: `∫ e(ξt) β(ξ/X) dξ = X ψ(Xt)`. -/
theorem integral_e_βc_div {X : ℝ} (hX : 0 < X) (t : ℝ) :
    ∫ ξ : ℝ, 𝐞 (ξ * t) • βc (ξ / X) = (X : ℂ) * ψS (X * t) := by
  have h := Measure.integral_comp_mul_left (fun ξ : ℝ => 𝐞 (ξ * t) • βc (ξ / X)) X
  rw [abs_of_pos (inv_pos.2 hX)] at h
  have h2 : ∫ ξ : ℝ, 𝐞 (ξ * t) • βc (ξ / X) = (X : ℂ) * ∫ η : ℝ, 𝐞 (X * η * t) • βc (X * η / X) := by
    rw [h, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hX.ne',
      Complex.ofReal_one, one_mul]
  rw [h2, ψS_apply]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  simp only
  rw [mul_div_cancel_left₀ _ hX.ne']
  congr 2; ring

theorem βc_continuous : Continuous βc := Complex.continuous_ofReal.comp β_continuous

/-- Fubini: `∫ e(ξx) β(ξ/X) 𝓕f(ξ) dξ = ∫ X ψ(X(x-y)) f(y) dy`. -/
theorem integral_e_βc_fourier (f : ℝ → ℝ) (hf : Continuous f) (hcs : HasCompactSupport f)
    {X : ℝ} (hX : 0 < X) (x : ℝ) :
    ∫ ξ : ℝ, 𝐞 (ξ * x) • (βc (ξ / X) * 𝓕 (fun u => (f u : ℂ)) ξ) =
      ∫ y, (X : ℂ) * ψS (X * (x - y)) * (f y : ℂ) := by
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hcs
  have step1 : ∀ ξ : ℝ, 𝐞 (ξ * x) • (βc (ξ / X) * 𝓕 (fun u => (f u : ℂ)) ξ) =
      ∫ y, (𝐞 (ξ * (x - y)) • βc (ξ / X)) * (f y : ℂ) := by
    intro ξ
    simp only [Real.fourier_real_eq, Circle.smul_def, smul_eq_mul]
    rw [← integral_const_mul, ← integral_const_mul]
    congr 1; ext y
    rw [show ξ * (x - y) = ξ * x + -(y * ξ) by ring, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  simp_rw [step1]
  have hint : Integrable (Function.uncurry fun (ξ : ℝ) (y : ℝ) =>
      (𝐞 (ξ * (x - y)) • βc (ξ / X)) * (f y : ℂ)) (volume.prod volume) := by
    have hdom : Integrable (fun z : ℝ × ℝ => β (z.1 / X) * |f z.2|) (volume.prod volume) :=
      (β_integrable.comp_div hX.ne').mul_prod hfi.abs
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      show Continuous fun z : ℝ × ℝ => (𝐞 (z.1 * (x - z.2)) • βc (z.1 / X)) * (f z.2 : ℂ)
      refine Continuous.mul ?_ (Complex.continuous_ofReal.comp (hf.comp continuous_snd))
      refine Continuous.smul ?_ (βc_continuous.comp (continuous_fst.div_const _))
      have h1 : Continuous fun z : ℝ × ℝ => 𝐞 (z.1 * (x - z.2)) :=
        Real.continuous_fourierChar.comp (continuous_fst.mul (continuous_const.sub continuous_snd))
      exact continuous_subtype_val.comp h1
    · simp only [Function.uncurry, norm_mul, Circle.norm_smul, βc, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (β_nonneg _)]
      rfl
  rw [integral_integral_swap hint]
  congr 1; ext y
  rw [integral_mul_const, integral_e_βc_div hX]

theorem fourier_integrable_of_smooth (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcs : HasCompactSupport f) : Integrable (𝓕 (fun u => (f u : ℂ))) := by
  have hcsF : HasCompactSupport (fun u => (f u : ℂ)) :=
    hcs.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun u => (f u : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have := (𝓕 (hcsF.toSchwartzMap hcd)).integrable (μ := volume)
  rwa [SchwartzMap.fourier_coe] at this

/-- Ingredient for `local_mass`: `φ₀ = 𝓕⁻¹ β` (real, as `β` is even) has `φ̂₀ = β`, so
`f - f ∗ φ_X` has Fourier transform `𝓕f · (1 - β(·/X))`, which vanishes on `|ξ| ≤ X` and has
modulus `≤ ‖𝓕f‖`; Fourier inversion gives the bound. -/
theorem exists_phi0 :
    ∃ φ₀ : ℝ → ℝ, Continuous φ₀ ∧ Integrable φ₀ ∧ (∃ B : ℝ, ∀ x, |φ₀ x| ≤ B) ∧
      ∀ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → ∀ X : ℝ, 0 < X → ∀ x : ℝ,
        |f x - ∫ y, X * φ₀ (X * (x - y)) * f y| ≤
          ∫ ξ in {ξ : ℝ | X < |ξ|}, ‖𝓕 (fun u => (f u : ℂ)) ξ‖ := by
  refine ⟨fun s => (ψS s).re, Complex.continuous_re.comp ψS.continuous,
    (ψS.integrable (μ := volume)).re, ⟨βint, fun s => (Complex.abs_re_le_norm _).trans
      (norm_ψS_le s)⟩, fun f hf hcs X hX x => ?_⟩
  have hcont : Continuous f := hf.continuous
  set F : ℝ → ℂ := fun u => (f u : ℂ) with hFdef
  have hFc : Continuous F := Complex.continuous_ofReal.comp hcont
  have hFi : Integrable F := (hcont.integrable_of_hasCompactSupport hcs).ofReal
  have hFFi : Integrable (𝓕 F) := fourier_integrable_of_smooth f hf hcs
  have hFFc : Continuous (𝓕 F) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hFi
  -- the convolution integrand
  set g : ℝ → ℂ := fun y => (X : ℂ) * ψS (X * (x - y)) * F y with hgdef
  have hgi : Integrable g := by
    have hm : AEStronglyMeasurable (fun y => (X : ℂ) * ψS (X * (x - y))) volume :=
      (continuous_const.mul (ψS.continuous.comp (continuous_const.mul
        (continuous_const.sub continuous_id)))).aestronglyMeasurable
    refine (hFi.bdd_mul (c := X * βint) hm (Filter.Eventually.of_forall fun y => ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX]
    gcongr; exact norm_ψS_le _
  have hre : ∫ y, X * (ψS (X * (x - y))).re * f y = (∫ y, g y).re := by
    rw [show (∫ y, g y).re = RCLike.re (∫ y, g y) from rfl, ← integral_re hgi]
    congr 1; ext y
    simp [g, F, Complex.re_ofReal_mul, Complex.re_mul_ofReal]
  rw [hre]
  have hFx : F x = ∫ ξ, 𝐞 (ξ * x) • 𝓕 F ξ := inversion hFc hFi hFFi x
  have hZ := integral_e_βc_fourier f hcont hcs hX x
  -- integrability of the two Fourier-side integrands
  have hi1 : Integrable (fun ξ : ℝ => 𝐞 (ξ * x) • 𝓕 F ξ) := by
    refine hFFi.norm.mono' (Continuous.aestronglyMeasurable ?_)
      (Filter.Eventually.of_forall fun ξ => by rw [Circle.norm_smul])
    exact (Real.continuous_fourierChar.comp (continuous_id.mul continuous_const)).smul hFFc
  have hi2 : Integrable (fun ξ : ℝ => 𝐞 (ξ * x) • (βc (ξ / X) * 𝓕 F ξ)) := by
    refine hFFi.norm.mono' (Continuous.aestronglyMeasurable ?_)
      (Filter.Eventually.of_forall fun ξ => ?_)
    · exact (Real.continuous_fourierChar.comp (continuous_id.mul continuous_const)).smul
        ((βc_continuous.comp (continuous_id.div_const _)).mul hFFc)
    · rw [Circle.norm_smul, norm_mul, βc, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (β_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (β_le_one _)
  have hdiff : F x - ∫ y, g y =
      ∫ ξ, (𝐞 (ξ * x) • 𝓕 F ξ - 𝐞 (ξ * x) • (βc (ξ / X) * 𝓕 F ξ)) := by
    rw [integral_sub hi1 hi2, ← hFx, hZ]
  have hmeasS : MeasurableSet {ξ : ℝ | X < |ξ|} := measurableSet_lt measurable_const measurable_abs
  have hbound : ‖F x - ∫ y, g y‖ ≤ ∫ ξ in {ξ : ℝ | X < |ξ|}, ‖𝓕 F ξ‖ := by
    rw [hdiff, ← integral_indicator hmeasS]
    refine norm_integral_le_of_norm_le (hFFi.norm.indicator hmeasS)
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [← smul_sub, Circle.norm_smul,
      show 𝓕 F ξ - βc (ξ / X) * 𝓕 F ξ = ((1 - β (ξ / X) : ℝ) : ℂ) * 𝓕 F ξ by
        simp [βc]; ring, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hξ : X < |ξ|
    · rw [Set.indicator_of_mem (show ξ ∈ {ξ : ℝ | X < |ξ|} from hξ)]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      rw [abs_le]; constructor <;> linarith [β_nonneg (ξ / X), β_le_one (ξ / X)]
    · rw [Set.indicator_of_notMem (show ξ ∉ {ξ : ℝ | X < |ξ|} from hξ)]
      rw [β_eq_one, sub_self, abs_zero, zero_mul]
      rw [abs_div, abs_of_pos hX, div_le_one hX]; exact not_lt.1 hξ
  have hreal : |f x - (∫ y, g y).re| = |(F x - ∫ y, g y).re| := by simp [F]
  rw [hreal]
  exact (Complex.abs_re_le_norm _).trans hbound

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
/-- The Fourier tail beyond `X`, from the decay with `j = M + 2`. -/
theorem tail_le {C : ℝ} {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hf : Adm C c T f) (hT : 0 < T)
    (M : ℕ) {X : ℝ} (hX : 0 < X) :
    ∫ ξ in {ξ : ℝ | X < |ξ|}, ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ≤
      2 * (|c (M + 2) 1| * T ^ (M + 2 + 1) * (⨆ u, f u)) / X ^ (M + 1) := by
  set S := ⨆ u, f u
  have hS : 0 ≤ S := Real.iSup_nonneg hf.nonneg
  set a := |c (M + 2) 1| * T ^ (M + 2 + 1) * S
  have ha : 0 ≤ a := by positivity
  set b := a / X ^ M
  have hb : 0 ≤ b := by positivity
  have hmeas : MeasurableSet {ξ : ℝ | X < |ξ|} := measurableSet_lt measurable_const measurable_abs
  have hpi := integrable_prof_abs (le_refl (0 : ℝ)) hb hX
  have h1 : ∫ ξ in {ξ : ℝ | X < |ξ|}, ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ≤
      ∫ ξ in {ξ : ℝ | X < |ξ|}, prof 0 b X |ξ| := by
    refine setIntegral_mono_on (fourier_integrable hf hT).norm.integrableOn hpi.integrableOn hmeas
      fun ξ hξ => ?_
    have hξ' : X < |ξ| := hξ
    have hξ0 : ξ ≠ 0 := by
      intro h; rw [h, abs_zero] at hξ'; linarith
    have hpos : 0 < |ξ| := abs_pos.2 hξ0
    refine (decay_le hf hT (M + 2) ξ hξ0).trans ?_
    simp only [prof, not_le.2 hξ', if_false]
    rw [div_div]
    refine div_le_div_of_nonneg_left ha (by positivity) ?_
    rw [pow_add]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hX.le hξ'.le M) (by positivity)
  have h2 : ∫ ξ in {ξ : ℝ | X < |ξ|}, prof 0 b X |ξ| ≤ ∫ ξ, prof 0 b X |ξ| :=
    setIntegral_le_integral hpi (Filter.Eventually.of_forall fun ξ =>
      prof_nonneg (le_refl 0) hb _)
  rw [integral_prof_abs (le_refl (0 : ℝ)) hb hX] at h2
  refine (h1.trans h2).trans (le_of_eq ?_)
  simp only [b]
  rw [pow_succ]
  field_simp
  ring

theorem smooth_hasCompactSupport {T : ℝ} (hT : 0 < T) {f : ℝ → ℝ} (hcs : HasCompactSupport f) :
    HasCompactSupport (smooth T f) := by
  rw [smooth_eq_conv]; exact hcs.convolution _ (βT_hasCompactSupport hT.ne')

/-- The local-mass bound for one `η'`, with its own threshold. -/
theorem local_mass_core (C : ℝ) (c : ℕ → ℝ → ℝ) (η' : ℝ) (hη' : 0 < η') :
    ∃ D T₂ : ℝ, 0 ≤ D ∧ 1 ≤ T₂ ∧ ∀ T : ℝ, T₂ ≤ T → ∀ f : ℝ → ℝ, Adm C c T f →
      (⨆ u, f u) ≤ D * T ^ η' * ⨆ u, smooth T f u := by
  obtain ⟨φ₀, hφc, hφi, ⟨B, hB⟩, hmain⟩ := exists_phi0
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  -- the tail of `φ₀`
  have ht := intervalIntegral_tendsto_integral hφi.abs Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
  obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.1
    (ht.eventually (lt_mem_nhds (show (∫ w, |φ₀ w|) - 1 / 4 < ∫ w, |φ₀ w| by linarith)))
  set M : ℕ := ⌈3 / η'⌉₊
  have hM : 3 ≤ η' * ((M : ℝ) + 1) := by
    have : 3 / η' ≤ M := Nat.le_ceil _
    rw [div_le_iff₀ hη'] at this
    nlinarith
  set K := |c (M + 2) 1|
  refine ⟨2 * B, max (max 1 (8 * K)) ((max 1 R₀) ^ η'⁻¹), by positivity,
    le_trans (le_max_left _ _) (le_max_left _ _), fun T hT f hf => ?_⟩
  have hT1 : 1 ≤ T := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hT)
  have hTK : 8 * K ≤ T := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hT)
  have hTR : (max 1 R₀) ^ η'⁻¹ ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : 0 < T := by linarith
  have hcont : Continuous f := hf.smooth.continuous
  have hcs : HasCompactSupport f := adm_hasCompactSupport hf
  have hfi : Integrable f := hcont.integrable_of_hasCompactSupport hcs
  set S := ⨆ u, f u with hSdef
  have hS : 0 ≤ S := Real.iSup_nonneg hf.nonneg
  have hbdd : BddAbove (Set.range f) := hcont.bddAbove_range_of_hasCompactSupport hcs
  have hfS : ∀ y, f y ≤ S := fun y => le_ciSup hbdd y
  obtain ⟨x₀, hx₀⟩ := hcont.exists_forall_ge_of_hasCompactSupport hcs
  have hSx : S = f x₀ := le_antisymm (ciSup_le hx₀) (hfS x₀)
  -- `G = sup g`
  set G := ⨆ u, smooth T f u with hGdef
  have hsc := smooth_contDiff T f hcont hcs
  have hGx : smooth T f x₀ ≤ G :=
    le_ciSup (hsc.continuous.bddAbove_range_of_hasCompactSupport
      (smooth_hasCompactSupport hT0 hcs)) x₀
  -- scales
  set Q := T ^ η' with hQdef
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hT1 hη'.le
  have hQ0 : 0 < Q := by linarith
  have hQR : R₀ ≤ Q := by
    have h1 : ((max 1 R₀) ^ η'⁻¹) ^ η' ≤ T ^ η' :=
      Real.rpow_le_rpow (by positivity) hTR hη'.le
    rw [Real.rpow_inv_rpow (by positivity) hη'.ne'] at h1
    exact le_trans (le_max_right _ _) h1
  set X := T * Q with hXdef
  have hX : 0 < X := by positivity
  -- Fourier tail `≤ S/4`
  have htail : ∫ ξ in {ξ : ℝ | X < |ξ|}, ‖𝓕 (fun u => (f u : ℂ)) ξ‖ ≤ S / 4 := by
    refine (tail_le hf hT0 M hX).trans ?_
    have hQM : T ^ 3 ≤ Q ^ (M + 1) := by
      rw [hQdef, ← Real.rpow_mul_natCast hT0.le, ← Real.rpow_natCast T 3]
      exact Real.rpow_le_rpow_of_exponent_le hT1 (by push_cast; linarith)
    have hXM : T ^ (M + 4) ≤ X ^ (M + 1) := by
      rw [hXdef, mul_pow, show M + 4 = (M + 1) + 3 by ring, pow_add]
      gcongr
    have hK : 0 ≤ K := abs_nonneg _
    rw [div_le_iff₀ (by positivity)]
    calc 2 * (K * T ^ (M + 2 + 1) * S) = 2 * K * S * T ^ (M + 3) := by ring
      _ ≤ T / 4 * S * T ^ (M + 3) := by gcongr; linarith
      _ = S / 4 * T ^ (M + 4) := by ring
      _ ≤ S / 4 * X ^ (M + 1) := by gcongr
  have hmn := hmain f hf.smooth hcs X hX x₀
  set I := ∫ y, X * φ₀ (X * (x₀ - y)) * f y with hIdef
  have hSI : S ≤ I + S / 4 := by
    have := (abs_le.1 (hmn.trans htail)).2
    rw [← hSx] at this; linarith
  -- the tail function of `φ₀`
  set h : ℝ → ℝ := Set.indicator (Set.Icc (-Q) Q)ᶜ (fun w => |φ₀ w|) with hhdef
  have hh_nn : ∀ w, 0 ≤ h w := fun w => Set.indicator_nonneg (fun w _ => abs_nonneg (φ₀ w)) w
  have hh_int : Integrable h := hφi.abs.indicator measurableSet_Icc.compl
  have hh_tail : ∫ w, h w ≤ 1 / 4 := by
    rw [hhdef, integral_indicator measurableSet_Icc.compl]
    have h1 := integral_add_compl (measurableSet_Icc (a := -Q) (b := Q)) hφi.abs
    have h2 := hR₀ Q hQR
    simp only [id] at h2
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc] at h2
    linarith
  -- integrability
  have hφm : AEStronglyMeasurable (fun y => φ₀ (X * (x₀ - y))) volume :=
    (hφc.comp (continuous_const.mul (continuous_const.sub continuous_id))).aestronglyMeasurable
  have i_a : Integrable (fun y => X * φ₀ (X * (x₀ - y)) * f y) := by
    refine hfi.bdd_mul (c := X * B) (hφm.const_mul X) (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hX]
    gcongr; exact hB _
  have i_b : Integrable (fun y => X * |φ₀ (X * (x₀ - y))| * f y) := by
    refine hfi.bdd_mul (c := X * B) (hφm.norm.const_mul X) (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hX, abs_abs]
    gcongr; exact hB _
  have i_c : Integrable (fun y => X * B * Set.indicator (Set.Icc (x₀ - 1 / T) (x₀ + 1 / T)) f y) :=
    (hfi.indicator measurableSet_Icc).const_mul _
  have i_d : Integrable (fun y => S * (X * h (X * (x₀ - y)))) :=
    (((hh_int.comp_mul_left' hX.ne').comp_sub_left x₀).const_mul X).const_mul S
  have hIb : I ≤ ∫ y, X * |φ₀ (X * (x₀ - y))| * f y :=
    integral_mono i_a i_b fun y => mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_abs_self _) hX.le) (hf.nonneg y)
  have hsplit : ∀ y, X * |φ₀ (X * (x₀ - y))| * f y ≤
      X * B * Set.indicator (Set.Icc (x₀ - 1 / T) (x₀ + 1 / T)) f y +
        S * (X * h (X * (x₀ - y))) := by
    intro y
    have hfy := hf.nonneg y
    by_cases hy : y ∈ Set.Icc (x₀ - 1 / T) (x₀ + 1 / T)
    · rw [Set.indicator_of_mem hy]
      have : 0 ≤ S * (X * h (X * (x₀ - y))) := by have := hh_nn (X * (x₀ - y)); positivity
      have : X * |φ₀ (X * (x₀ - y))| * f y ≤ X * B * f y := by gcongr; exact hB _
      linarith
    · rw [Set.indicator_of_notMem hy, mul_zero, zero_add]
      have hfar : 1 / T < |x₀ - y| := by
        by_contra hc; push Not at hc
        exact hy ⟨by linarith [(abs_le.1 hc).2], by linarith [(abs_le.1 hc).1]⟩
      have hout : X * (x₀ - y) ∈ (Set.Icc (-Q) Q)ᶜ := by
        intro hin
        have h1 : |X * (x₀ - y)| ≤ Q := abs_le.2 ⟨hin.1, hin.2⟩
        rw [abs_mul, abs_of_pos hX] at h1
        have h2 : X * (1 / T) < X * |x₀ - y| := mul_lt_mul_of_pos_left hfar hX
        have h3 : X * (1 / T) = Q := by rw [hXdef]; field_simp
        linarith
      rw [hhdef, Set.indicator_of_mem hout]
      calc X * |φ₀ (X * (x₀ - y))| * f y ≤ X * |φ₀ (X * (x₀ - y))| * S := by
            gcongr; exact hfS y
        _ = S * (X * |φ₀ (X * (x₀ - y))|) := by ring
  have hsub : ∫ y, h (X * (x₀ - y)) = X⁻¹ * ∫ w, h w := by
    rw [integral_sub_left_eq_self (fun y => h (X * y)) volume x₀, Measure.integral_comp_mul_left,
      abs_of_pos (inv_pos.2 hX), smul_eq_mul]
  have hInt : ∫ y, (X * B * Set.indicator (Set.Icc (x₀ - 1 / T) (x₀ + 1 / T)) f y +
      S * (X * h (X * (x₀ - y)))) =
      X * B * (∫ y in Set.Icc (x₀ - 1 / T) (x₀ + 1 / T), f y) + S * ∫ w, h w := by
    rw [integral_add i_c i_d, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_indicator measurableSet_Icc, hsub, ← mul_assoc X X⁻¹, mul_inv_cancel₀ hX.ne',
      one_mul]
  have hJ : ∫ y, X * |φ₀ (X * (x₀ - y))| * f y ≤
      X * B * (∫ y in Set.Icc (x₀ - 1 / T) (x₀ + 1 / T), f y) + S * ∫ w, h w :=
    (integral_mono i_b (i_c.add i_d) hsplit).trans (le_of_eq hInt)
  have hnear : X * B * ∫ y in Set.Icc (x₀ - 1 / T) (x₀ + 1 / T), f y ≤ B * Q * G := by
    have h1 := smooth_ge T hT0 f hcont hcs hf.nonneg x₀
    calc X * B * ∫ y in Set.Icc (x₀ - 1 / T) (x₀ + 1 / T), f y
        = B * Q * (T * ∫ y in Set.Icc (x₀ - 1 / T) (x₀ + 1 / T), f y) := by rw [hXdef]; ring
      _ ≤ B * Q * G := by gcongr; exact h1.trans hGx
  have hSh : S * ∫ w, h w ≤ S / 4 := by nlinarith
  have : S ≤ B * Q * G + S / 2 := by linarith
  linarith

/-- Local mass (brief, *Local mass*; use `exists_phi0` with `X = T^{1+η'}`, the decay with
`ε = 1` and large `j`, the tail `∫_{|w| > T^{η'}} |φ₀| → 0`, `smooth_ge` at a maximum point), in the uniform form: one threshold `T₀` for every `η'`
(for `T₀ ≤ T ≤ T₂(η')` use the `η' = 1` bound and `T ≤ T₂(η')^{1-η'} T^{η'}`). -/
theorem local_mass (C : ℝ) (c : ℕ → ℝ → ℝ) (hC : 1 ≤ C) :
    ∃ T₀ : ℝ, ∀ η' : ℝ, 0 < η' → ∃ D : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Adm C c T f →
      (⨆ u, f u) ≤ D * T ^ η' * ⨆ u, smooth T f u := by
  obtain ⟨D₁, T₁, hD₁, hT₁, h₁⟩ := local_mass_core C c 1 one_pos
  refine ⟨T₁, fun η' hη' => ?_⟩
  obtain ⟨D₂, T₂, hD₂, hT₂, h₂⟩ := local_mass_core C c η' hη'
  refine ⟨max D₂ (D₁ * T₂), fun T hT f hf => ?_⟩
  have hT1 : 1 ≤ T := hT₁.trans hT
  have hT0 : 0 < T := by linarith
  have hG : 0 ≤ ⨆ u, smooth T f u := Real.iSup_nonneg fun u => smooth_nonneg hT0.le hf.nonneg u
  have hQ : 1 ≤ T ^ η' := Real.one_le_rpow hT1 hη'.le
  by_cases hTT : T₂ ≤ T
  · refine (h₂ T hTT f hf).trans ?_
    gcongr; exact le_max_left _ _
  · push Not at hTT
    refine (h₁ T hT f hf).trans ?_
    rw [Real.rpow_one]
    have : D₁ * T ≤ max D₂ (D₁ * T₂) * T ^ η' := by
      calc D₁ * T ≤ D₁ * T₂ := by gcongr
        _ ≤ D₁ * T₂ * T ^ η' := le_mul_of_one_le_right (by positivity) hQ
        _ ≤ max D₂ (D₁ * T₂) * T ^ η' := by gcongr; exact le_max_right _ _
    gcongr

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias local_mass := GuthMaynard.Affine.PartS.local_mass

alias integral_smooth_sq_le := GuthMaynard.Affine.PartS.integral_smooth_sq_le

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
theorem mem_dyadic {M : ℝ} {m : ℤ} (h : m ∈ dyadic M) : M < m ∧ (m : ℝ) ≤ 2 * M := by
  simp only [dyadic, Finset.mem_Ioc] at h
  exact ⟨Int.floor_lt.1 h.1, Int.le_floor.1 h.2⟩

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

theorem gsum_le_Gfun {K M₁ M₂ M₃ M₃' : ℝ} (hK : 0 < K) (hM₃ : 0 < M₃) (hM₃' : M₃ ≤ M₃')
    {f : ℝ → ℝ} (hf : ∀ u, 0 ≤ f u) (u : ℝ) :
    gsum K M₁ M₂ M₃ f u ≤ Gfun K M₁ M₂ M₃' f u := by
  have hM₃'0 : 0 < M₃' := lt_of_lt_of_le hM₃ hM₃'
  have hKM : K * M₃ ≤ (|K| + 2) * M₃' := by
    rw [abs_of_pos hK]; nlinarith
  have hsub : Finset.Icc (-⌊K * M₃⌋) ⌊K * M₃⌋ ⊆ Finset.Icc (-NK K M₃') (NK K M₃') := by
    have : ⌊K * M₃⌋ ≤ NK K M₃' := by
      unfold NK
      exact (Int.floor_le_ceil _).trans (Int.ceil_mono hKM)
    intro m hm
    simp only [Finset.mem_Icc] at hm ⊢
    constructor <;> omega
  unfold gsum Gfun
  refine Finset.sum_le_sum fun m₁ _ => Finset.sum_le_sum fun m₂ _ => ?_
  calc ∑ m₃ ∈ Finset.Icc (-⌊K * M₃⌋) ⌊K * M₃⌋, f ((m₁ * u + m₃) / m₂)
      = ∑ m₃ ∈ Finset.Icc (-⌊K * M₃⌋) ⌊K * M₃⌋, ψ₁ K (m₃ / M₃') * f ((m₁ * u + m₃) / m₂) := by
        refine Finset.sum_congr rfl fun m₃ hm₃ => ?_
        rw [ψ₁_eq_one, one_mul]
        simp only [Finset.mem_Icc] at hm₃
        have h1 : (m₃ : ℝ) ≤ K * M₃ := by
          have : (m₃ : ℝ) ≤ (⌊K * M₃⌋ : ℝ) := by exact_mod_cast hm₃.2
          linarith [Int.floor_le (K * M₃)]
        have h2 : -(K * M₃) ≤ (m₃ : ℝ) := by
          have : (-(⌊K * M₃⌋ : ℝ)) ≤ (m₃ : ℝ) := by exact_mod_cast hm₃.1
          linarith [Int.floor_le (K * M₃)]
        rw [abs_div, abs_of_pos hM₃'0, div_le_iff₀ hM₃'0, abs_of_pos hK, abs_le]
        constructor <;> nlinarith
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun m₃ _ _ =>
        mul_nonneg (ψ₁_nonneg _ _) (hf _)

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias gsum_le_Gfun := GuthMaynard.Affine.PartG.gsum_le_Gfun

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
theorem Gfun_contDiff (K M₁ M₂ M₃ : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (Gfun K M₁ M₂ M₃ f) := by
  unfold Gfun
  refine ContDiff.sum fun m₁ _ => ContDiff.sum fun m₂ _ => ContDiff.sum fun m₃ _ => ?_
  exact contDiff_const.mul (hf.comp (by fun_prop))

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias Gfun_contDiff := GuthMaynard.Affine.PartG.Gfun_contDiff

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
theorem hcs_term {f : ℝ → ℝ} (hcs : HasCompactSupport f) {a b c : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) :
    HasCompactSupport (fun u => f ((a * u + b) / c)) := by
  have e : (fun u => f ((a * u + b) / c)) =
      f ∘ (Homeomorph.addRight (b / c)) ∘ (Homeomorph.mulLeft₀ (a / c) (div_ne_zero ha hc)) := by
    funext u; simp only [Function.comp, Homeomorph.coe_addRight, Homeomorph.coe_mulLeft₀]
    congr 1; field_simp
  rw [e, ← Function.comp_assoc]
  exact (hcs.comp_homeomorph _).comp_homeomorph _

theorem Gfun_hasCompactSupport (K M₁ M₂ M₃ : ℝ) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (f : ℝ → ℝ)
    (hcs : HasCompactSupport f) : HasCompactSupport (Gfun K M₁ M₂ M₃ f) := by
  have e : Gfun K M₁ M₂ M₃ f = ∑ m₁ ∈ D₁ M₁, ∑ m₂ ∈ dyadic M₂,
      ∑ m₃ ∈ Finset.Icc (-NK K M₃) (NK K M₃),
        fun u : ℝ => ψ₁ K (m₃ / M₃) * f ((m₁ * u + m₃) / m₂) := by
    funext u; simp only [Gfun, Finset.sum_apply]
  rw [e]
  refine HasCompactSupport.finset_sum fun m₁ hm₁ => HasCompactSupport.finset_sum fun m₂ hm₂ =>
    HasCompactSupport.finset_sum fun m₃ _ => ?_
  have h1 : (m₁ : ℝ) ≠ 0 := by
    have := (mem_D₁ hm₁).1; intro h; rw [h, abs_zero] at this; linarith
  have h2 : (m₂ : ℝ) ≠ 0 := by
    have := (mem_dyadic hm₂).1; intro h; rw [h] at this; linarith
  exact (hcs_term hcs h1 h2).mul_left

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias Gfun_hasCompactSupport := GuthMaynard.Affine.PartG.Gfun_hasCompactSupport

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
theorem plancherel (h : ℝ → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hcs : HasCompactSupport h) :
    ∫⁻ u, ENNReal.ofReal (h u ^ 2) = ∫⁻ ξ, ‖𝓕 (fun u => (h u : ℂ)) ξ‖ₑ ^ 2 := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun u => (h u : ℂ)) := Complex.ofRealCLM.contDiff.comp hh
  have hcs' : HasCompactSupport (fun u => (h u : ℂ)) := hcs.comp_left Complex.ofReal_zero
  obtain ⟨F, hF⟩ : ∃ F : SchwartzMap ℝ ℂ, (F : ℝ → ℂ) = fun u => (h u : ℂ) :=
    ⟨hcs'.toSchwartzMap hc, rfl⟩
  have hP := SchwartzMap.integral_norm_sq_fourier F
  rw [SchwartzMap.fourier_coe, hF] at hP
  have hint1 : Integrable (fun ξ => ‖𝓕 F ξ‖ ^ 2) :=
    ((𝓕 F).memLp 2 volume).integrable_norm_pow (by norm_num)
  rw [SchwartzMap.fourier_coe, hF] at hint1
  have hint2 : Integrable (fun u => h u ^ 2) := by
    have e : (fun u => h u ^ 2) = h * h := by funext u; simp [sq]
    rw [e]
    exact (hh.continuous.mul hh.continuous).integrable_of_hasCompactSupport (hcs.mul_left)
  rw [← ofReal_integral_eq_lintegral_ofReal hint2 (ae_of_all _ fun u => sq_nonneg _)]
  have : (fun ξ => ‖𝓕 (fun u => (h u : ℂ)) ξ‖ₑ ^ 2) =
      fun ξ => ENNReal.ofReal (‖𝓕 (fun u => (h u : ℂ)) ξ‖ ^ 2) := by
    funext ξ; rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [this, ← ofReal_integral_eq_lintegral_ofReal hint1 (ae_of_all _ fun u => by positivity), hP]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias plancherel := GuthMaynard.Affine.PartG.plancherel

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

theorem integral_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E)
    (a b c : ℝ) (hc : c ≠ 0) :
    ∫ u, g ((a * u + b) / c) = |c / a| • ∫ u, g u := by
  have e : (fun u => g ((a * u + b) / c)) = fun u => (fun y => g (y + b / c)) ((a / c) * u) := by
    funext u; congr 1; field_simp
  rw [e, Measure.integral_comp_mul_left (fun y => g (y + b / c)) (a / c),
    integral_add_right_eq_self, inv_div]

theorem fourier_finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℂ)
    (hF : ∀ i ∈ s, Integrable (F i)) (ξ : ℝ) :
    𝓕 (fun u => ∑ i ∈ s, F i u) ξ = ∑ i ∈ s, 𝓕 (F i) ξ := by
  simp_rw [Real.fourier_real_eq, Finset.smul_sum]
  rw [integral_finsetSum]
  intro i hi
  have := (Real.fourierIntegral_convergent_iff (μ := volume) ξ).2 (hF i hi)
  simpa [mul_comm] using this

theorem fourier_term (f : ℝ → ℝ) (k a b c : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) (ξ : ℝ) :
    𝓕 (fun u => (k : ℂ) * (f ((a * u + b) / c) : ℂ)) ξ =
      (k : ℂ) * ((|c / a| : ℝ) : ℂ) * ee (b * (ξ / a)) * fhat f (ξ * c / a) := by
  unfold fhat
  simp_rw [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  set G : ℝ → ℂ := fun v => (k : ℂ) * (ee (b * (ξ / a)) *
    (Complex.exp (↑(-2 * Real.pi * v * (ξ * c / a)) * Complex.I) * (f v : ℂ))) with hG
  have e : (fun u => Complex.exp (↑(-2 * Real.pi * u * ξ) * Complex.I) *
      ((k : ℂ) * (f ((a * u + b) / c) : ℂ))) = fun u => G ((a * u + b) / c) := by
    funext u
    simp only [hG, ee]
    rw [mul_left_comm, ← mul_assoc (Complex.exp (2 * ↑Real.pi * Complex.I * _)), ← Complex.exp_add]
    congr 3
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    push_cast; field_simp; ring
  rw [e, integral_affine G a b c hc]
  simp only [hG]
  rw [integral_const_mul, integral_const_mul, Complex.real_smul]
  ring

theorem integrable_term {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f)
    (k a b c : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) :
    Integrable (fun u => (k : ℂ) * (f ((a * u + b) / c) : ℂ)) := by
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
  exact ((hcs_term hcs ha hc).comp_left Complex.ofReal_zero).mul_left

theorem fourier_Gfun (K M₁ M₂ M₃ : ℝ) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (f : ℝ → ℝ)
    (hf : Continuous f) (hcs : HasCompactSupport f) (ξ : ℝ) :
    𝓕 (fun u => (Gfun K M₁ M₂ M₃ f u : ℂ)) ξ = ∑ m₁ ∈ D₁ M₁, Pfun K M₃ (ξ / m₁) * Ffun M₂ f m₁ ξ := by
  have h1 : ∀ m₁ ∈ D₁ M₁, (m₁ : ℝ) ≠ 0 := by
    intro m₁ hm₁ h
    have := (mem_D₁ hm₁).1; rw [h, abs_zero] at this; linarith
  have h2 : ∀ m₂ ∈ dyadic M₂, (0 : ℝ) < m₂ := fun m₂ hm₂ => by
    have := (mem_dyadic hm₂).1; linarith
  have e : (fun u => (Gfun K M₁ M₂ M₃ f u : ℂ)) = fun u => ∑ m₁ ∈ D₁ M₁, ∑ m₂ ∈ dyadic M₂,
      ∑ m₃ ∈ Finset.Icc (-NK K M₃) (NK K M₃),
        (ψ₁ K (m₃ / M₃) : ℂ) * (f ((m₁ * u + m₃) / m₂) : ℂ) := by
    funext u; simp only [Gfun]; push_cast; rfl
  rw [e, fourier_finset_sum]
  swap
  · intro m₁ hm₁
    refine integrable_finsetSum _ fun m₂ hm₂ => integrable_finsetSum _ fun m₃ _ => ?_
    exact integrable_term hf hcs _ _ _ _ (h1 m₁ hm₁) (h2 m₂ hm₂).ne'
  refine Finset.sum_congr rfl fun m₁ hm₁ => ?_
  rw [fourier_finset_sum]
  swap
  · intro m₂ hm₂
    refine integrable_finsetSum _ fun m₃ _ => ?_
    exact integrable_term hf hcs _ _ _ _ (h1 m₁ hm₁) (h2 m₂ hm₂).ne'
  unfold Pfun Ffun
  rw [Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m₂ hm₂ => ?_
  rw [fourier_finset_sum]
  swap
  · intro m₃ _
    exact integrable_term hf hcs _ _ _ _ (h1 m₁ hm₁) (h2 m₂ hm₂).ne'
  refine Finset.sum_congr rfl fun m₃ _ => ?_
  rw [fourier_term f _ _ _ _ (h1 m₁ hm₁) (h2 m₂ hm₂).ne', abs_div, abs_of_pos (h2 m₂ hm₂)]
  ring

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias fourier_Gfun := GuthMaynard.Affine.PartG.fourier_Gfun

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

end GuthMaynard.Affine.PartZ
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal



/-- `∫ gsum² ≤ ∫ G² = ∫ |Ĝ|² ≤ ∫ W²`. -/
theorem lintegral_gsum_sq_le_W (K M₁ M₂ M₃ M₃' : ℝ) (hK : 0 < K) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hM₃ : 0 < M₃) (hM₃' : M₃ ≤ M₃') (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hnn : ∀ u, 0 ≤ f u) (hcs : HasCompactSupport f) :
    ∫⁻ u, ENNReal.ofReal (gsum K M₁ M₂ M₃ f u ^ 2) ≤
      ∫⁻ ξ, ENNReal.ofReal (Wfun K M₁ M₂ M₃' f ξ ^ 2) := by
  calc ∫⁻ u, ENNReal.ofReal (gsum K M₁ M₂ M₃ f u ^ 2)
      ≤ ∫⁻ u, ENNReal.ofReal (Gfun K M₁ M₂ M₃' f u ^ 2) :=
        lintegral_mono fun u => ENNReal.ofReal_le_ofReal
          (pow_le_pow_left₀ (gsum_nonneg hnn u) (gsum_le_Gfun hK hM₃ hM₃' hnn u) 2)
    _ = ∫⁻ ξ, ‖𝓕 (fun u => (Gfun K M₁ M₂ M₃' f u : ℂ)) ξ‖ₑ ^ 2 :=
        plancherel _ (Gfun_contDiff K M₁ M₂ M₃' f hf)
          (Gfun_hasCompactSupport K M₁ M₂ M₃' hM₁ hM₂ f hcs)
    _ ≤ ∫⁻ ξ, ENNReal.ofReal (Wfun K M₁ M₂ M₃' f ξ ^ 2) := by
        refine lintegral_mono fun ξ => ?_
        rw [fourier_Gfun K M₁ M₂ M₃' hM₁ hM₂ f hf.continuous hcs ξ, ← ofReal_norm,
          ← ENNReal.ofReal_pow (norm_nonneg _)]
        refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun m₁ _ => norm_mul_le _ _)

theorem Sig_le_large_add_small (L Q M₂ M₃ : ℝ) (f : ℝ → ℝ) :
    Sig Q M₂ M₃ f ≤ SigLarge L Q M₂ M₃ f + SigSmall L Q M₂ M₃ f := by
  unfold Sig SigLarge SigSmall
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun ℓ => ?_
  by_cases h0 : ℓ = 0
  · simp [h0]
  · by_cases hL : L < |(ℓ : ℝ)|
    · simp [h0, hL]
    · simp [h0, hL, le_of_not_gt hL]

/-- The smoothing is in the class `Adm (2C) c' T` (from the smoothing stubs and `local_mass`). -/
theorem smooth_adm (C : ℝ) (c : ℕ → ℝ → ℝ) (hC : 1 ≤ C) :
    ∃ (c' : ℕ → ℝ → ℝ) (T₂ : ℝ), ∀ T : ℝ, T₂ ≤ T → ∀ f : ℝ → ℝ, Adm C c T f →
      Adm (2 * C) c' T (smooth T f) := by
  obtain ⟨T₀, hloc⟩ := local_mass C c hC
  choose! D hD using hloc
  refine ⟨fun j ε => βint * max (c j (ε / 2)) 0 * D (ε / 2), max (max T₀ (4 * C)) 1, ?_⟩
  intro T hT f hf
  have hT0 : 0 < T := lt_of_lt_of_le one_pos (le_of_max_le_right hT)
  have hTT₀ : T₀ ≤ T := le_trans (le_max_left _ _) (le_of_max_le_left hT)
  have hT4 : 4 * C ≤ T := le_trans (le_max_right _ _) (le_of_max_le_left hT)
  have hfc := adm_continuous hf
  have hfcs := adm_hasCompactSupport hf
  refine ⟨smooth_contDiff T f hfc hfcs, smooth_nonneg hT0.le hf.nonneg,
    smooth_support C hC T hT4 f hf.supp, ?_⟩
  intro j ε hε ξ hξ
  have hε2 : 0 < ε / 2 := by positivity
  have h1 := norm_fourier_smooth_le T hT0 f hfc hfcs ξ
  have h2 := hf.decay j (ε / 2) hε2 ξ hξ
  have h3 := hD (ε / 2) hε2 T hTT₀ f hf
  have hSf : 0 ≤ ⨆ u, f u := Real.iSup_nonneg hf.nonneg
  have hβ : 0 ≤ βint := βint_pos.le
  have hpow : T ^ ε = T ^ (ε / 2) * T ^ (ε / 2) := by
    rw [← Real.rpow_add hT0]; congr 1; ring
  have hX : 0 ≤ T ^ (ε / 2) * (T / |ξ|) ^ j := by positivity
  calc ‖𝓕 (fun u => (smooth T f u : ℂ)) ξ‖
      ≤ βint * ‖𝓕 (fun u => (f u : ℂ)) ξ‖ := h1
    _ ≤ βint * (max (c j (ε / 2)) 0 * (T ^ (ε / 2) * (T / |ξ|) ^ j) * ⨆ u, f u) := by
        refine mul_le_mul_of_nonneg_left (h2.trans ?_) hβ
        rw [mul_assoc (c j (ε / 2))]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hX) hSf
    _ ≤ βint * (max (c j (ε / 2)) 0 * (T ^ (ε / 2) * (T / |ξ|) ^ j) *
          (D (ε / 2) * T ^ (ε / 2) * ⨆ u, smooth T f u)) := by
        gcongr
    _ = βint * max (c j (ε / 2)) 0 * D (ε / 2) * T ^ ε * (T / |ξ|) ^ j *
          ⨆ u, smooth T f u := by
        rw [hpow]; ring

/-- `Σ ≤ A Q² M₂ ‖f‖₂ J(g)^{1/2} + A Q M⁴ (∫ f)²`. -/
theorem Sig_le_J (C : ℝ) (c : ℕ → ℝ → ℝ) (hC : 1 ≤ C) (η : ℝ) (hη : 0 < η) :
    ∃ A T₁ : ℝ, 0 ≤ A ∧ ∀ T : ℝ, T₁ ≤ T → ∀ f : ℝ → ℝ, Adm C c T f →
      ∀ M M₁ M₂ M₃ : ℝ, Regime T M M₁ M₂ M₃ →
        Sig (T ^ η) M₂ M₃ f ≤ ENNReal.ofReal (A * (T ^ η) ^ 2 * M₂ *
          (√(∫ u, f u ^ 2) * √((J M (8 * C) (smooth T f)).toReal)) +
            A * T ^ η * M ^ 4 * (∫ u, f u) ^ 2) := by
  obtain ⟨AL, TL, hAL, hL⟩ := Sig_large_le C c hC η hη
  obtain ⟨AS, TS, hAS, hS⟩ := Sig_small_le C c hC η hη
  obtain ⟨c', T₂, hadm⟩ := smooth_adm C c hC
  refine ⟨AL + AS, max (max TL TS) (max T₂ 1), by positivity, ?_⟩
  intro T hT f hf M M₁ M₂ M₃ hr
  have hTL : TL ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTS : TS ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT2 : T₂ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT1 : 1 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hg := hadm T hT2 f hf
  have hM₂ : M₂ ∈ Set.Ioo 0 M := ⟨by linarith [hr.h₂], hr.h₂M⟩
  have hFH := integral_mul_Hfun_le C hC M M₂ hM₂ f (smooth T f) (adm_continuous hf) hf.supp
    (adm_continuous hg) hg.nonneg hg.supp
  have hQ : 1 ≤ T ^ η := Real.one_le_rpow hT1 hη.le
  have hM₂0 : 0 ≤ M₂ := by linarith [hr.h₂]
  have hI : 0 ≤ (∫ u, f u) ^ 2 := sq_nonneg _
  have hM4 : 0 ≤ M ^ 4 := by have := hr.h₂M; positivity
  set s := √(∫ u, f u ^ 2) * √((J M (8 * C) (smooth T f)).toReal) with hs
  have hs0 : 0 ≤ s := by positivity
  calc Sig (T ^ η) M₂ M₃ f
      ≤ SigLarge (T ^ (1 + η) / M₂) (T ^ η) M₂ M₃ f +
          SigSmall (T ^ (1 + η) / M₂) (T ^ η) M₂ M₃ f := Sig_le_large_add_small _ _ _ _ _
    _ ≤ ENNReal.ofReal (AL * M ^ 4 * (∫ u, f u) ^ 2) +
          ENNReal.ofReal (AS * (T ^ η) ^ 2 * M₂ * s + AS * T ^ η * M ^ 4 * (∫ u, f u) ^ 2) := by
        refine add_le_add (hL T hTL f hf M M₁ M₂ M₃ hr)
          ((hS T hTS f hf M M₁ M₂ M₃ hr).trans (ENNReal.ofReal_le_ofReal ?_))
        have : 0 ≤ AS * (T ^ η) ^ 2 * M₂ := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hFH this]
    _ = ENNReal.ofReal (AL * M ^ 4 * (∫ u, f u) ^ 2 +
          (AS * (T ^ η) ^ 2 * M₂ * s + AS * T ^ η * M ^ 4 * (∫ u, f u) ^ 2)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : AL * M ^ 4 * (∫ u, f u) ^ 2 ≤ AL * T ^ η * M ^ 4 * (∫ u, f u) ^ 2 := by
          have : 0 ≤ AL * M ^ 4 * (∫ u, f u) ^ 2 := by positivity
          nlinarith
        have h2 : AS * (T ^ η) ^ 2 * M₂ * s ≤ (AL + AS) * (T ^ η) ^ 2 * M₂ * s := by
          have : 0 ≤ (T ^ η) ^ 2 * M₂ * s := by positivity
          nlinarith
        nlinarith

/-- The final real inequality of the assembly. -/
theorem final_arith {A₅ A₆ A₇ A₈ Q M M₂ P s : ℝ} (hA₅ : 0 ≤ A₅) (hA₆ : 0 ≤ A₆) (hA₇ : 0 ≤ A₇)
    (hA₈ : 0 ≤ A₈) (hQ : 1 ≤ Q) (hM : 1 / 2 ≤ M) (_hM₂ : 0 ≤ M₂) (hM₂M : M₂ ≤ M) (I : ℝ)
    (hP : P = M ^ 6 * I ^ 2) (hs : 0 ≤ s) :
    A₆ * Q ^ 3 * M ^ 6 * I ^ 2 + 2 * (A₇ * Q ^ 2 * M * (A₈ * Q ^ 2 * M₂ * s +
      A₈ * Q * M ^ 4 * I ^ 2)) + A₅ * M ^ 6 * I ^ 2 ≤
      (A₆ + A₅ + 6 * A₇ * A₈) * Q ^ 4 * (P + M ^ 2 * s) := by
  subst hP
  have hQ3 : Q ^ 3 ≤ Q ^ 4 := pow_le_pow_right₀ hQ (by norm_num)
  have hQ4 : 1 ≤ Q ^ 4 := one_le_pow₀ hQ
  have hM0 : 0 ≤ M := by linarith
  have hP0 : 0 ≤ M ^ 6 * I ^ 2 := by positivity
  have hM5 : M ^ 5 ≤ 2 * M ^ 6 := by
    have : M ^ 5 * 1 ≤ M ^ 5 * (2 * M) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have ha : A₆ * Q ^ 3 * M ^ 6 * I ^ 2 ≤ A₆ * Q ^ 4 * (M ^ 6 * I ^ 2) := by
    have := mul_le_mul_of_nonneg_right hQ3 (mul_nonneg hA₆ hP0); nlinarith
  have hb : A₅ * M ^ 6 * I ^ 2 ≤ A₅ * Q ^ 4 * (M ^ 6 * I ^ 2) := by
    have := mul_le_mul_of_nonneg_right hQ4 (mul_nonneg hA₅ hP0); nlinarith
  have hc : 2 * (A₇ * Q ^ 2 * M * (A₈ * Q ^ 2 * M₂ * s)) ≤ 2 * A₇ * A₈ * Q ^ 4 * (M ^ 2 * s) := by
    have hMM : M * M₂ ≤ M ^ 2 := by nlinarith
    have hk : 0 ≤ 2 * A₇ * A₈ * Q ^ 4 * s := by positivity
    have := mul_le_mul_of_nonneg_left hMM hk
    nlinarith
  have hd : 2 * (A₇ * Q ^ 2 * M * (A₈ * Q * M ^ 4 * I ^ 2)) ≤
      4 * A₇ * A₈ * Q ^ 4 * (M ^ 6 * I ^ 2) := by
    have hk : 0 ≤ 2 * A₇ * A₈ * I ^ 2 := by positivity
    have h1 : Q ^ 3 * M ^ 5 ≤ Q ^ 4 * (2 * M ^ 6) :=
      mul_le_mul hQ3 hM5 (by positivity) (by positivity)
    have := mul_le_mul_of_nonneg_left h1 hk
    nlinarith
  have hMs : 0 ≤ M ^ 2 * s := by positivity
  have he : 0 ≤ (A₆ + A₅ + 4 * A₇ * A₈) * Q ^ 4 * (M ^ 2 * s) := by positivity
  have hf : 0 ≤ 2 * A₇ * A₈ * Q ^ 4 * (M ^ 6 * I ^ 2) := by positivity
  nlinarith

/-- The `J`-bound of Lemma 9.2 for `M ≤ T⁶`, with `T^{4η}` in place of `T^η`. -/
theorem main_bound (C : ℝ) (c : ℕ → ℝ → ℝ) (K : ℝ) (hC : 1 ≤ C) (hK : 0 < K) (η : ℝ)
    (hη : 0 < η) :
    ∃ A T₁ : ℝ, 0 ≤ A ∧ 1 ≤ T₁ ∧ ∀ T : ℝ, T₁ ≤ T → ∀ f : ℝ → ℝ, Adm C c T f →
      ∀ M : ℝ, 0 < M → M ≤ T ^ 6 →
      ∀ M₁ M₂ M₃ : ℝ, M₁ ∈ Set.Ioo 0 M → M₂ ∈ Set.Ioo 0 M → M₃ ∈ Set.Ioo 0 M →
      ∫⁻ u : ℝ, ENNReal.ofReal (gsum K M₁ M₂ M₃ f u ^ 2) ≤
        ENNReal.ofReal (A * (T ^ η) ^ 4 * (M ^ 6 * (∫ u, f u) ^ 2 +
          Real.sqrt (M ^ 4 * (∫ u, f u ^ 2) * (J M (8 * C) (smooth T f)).toReal))) := by
  obtain ⟨A₅, T₅, hA₅, h5⟩ := lintegral_W_sq_III C c K hC hK
  obtain ⟨A₆, T₆, hA₆, h6⟩ := lintegral_W_sq_low C c K hC hK η hη
  obtain ⟨A₇, T₇, hA₇, h7⟩ := lintegral_Wnear_sq_le_Sig C c K hC hK η hη
  obtain ⟨A₈, T₈, hA₈, h8⟩ := Sig_le_J C c hC η hη
  refine ⟨A₆ + A₅ + 6 * A₇ * A₈, max (max (max T₅ T₆) (max T₇ T₈)) 1, by positivity,
    le_max_right _ _, ?_⟩
  intro T hT f hf M hM hMT M₁ M₂ M₃ h₁ h₂ h₃
  have hT' := le_of_max_le_left hT
  have hT5 : T₅ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT'
  have hT6 : T₆ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT'
  have hT7 : T₇ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT'
  have hT8 : T₈ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT'
  have hT1 : 1 ≤ T := le_of_max_le_right hT
  -- empty dyadic ranges
  by_cases hne : (dyadic M₁).Nonempty ∧ (dyadic M₂).Nonempty
  swap
  · have h0 : ∀ u, gsum K M₁ M₂ M₃ f u = 0 := by
      intro u
      rcases not_and_or.mp hne with h | h
      · rw [Finset.not_nonempty_iff_eq_empty] at h
        simp [gsum, h]
      · rw [Finset.not_nonempty_iff_eq_empty] at h
        simp [gsum, h]
    simp [h0]
  obtain ⟨hn₁, hn₂⟩ := hne
  have hM₁h := half_le_of_dyadic_nonempty hn₁
  have hM₂h := half_le_of_dyadic_nonempty hn₂
  set M₃' := max M₃ 1 with hM₃'
  have hr : Regime T M M₁ M₂ M₃' :=
    ⟨hM₁h, h₁.2, hM₂h, h₂.2, le_max_right _ _,
      max_le (by linarith [h₃.2]) (by linarith [h₁.2]), hMT⟩
  have hW := lintegral_gsum_sq_le_W K M₁ M₂ M₃ M₃' hK h₁.1 h₂.1 h₃.1 (le_max_left _ _) f
    hf.smooth hf.nonneg (adm_hasCompactSupport hf)
  have hmeas : MeasurableSet {ξ : ℝ | |ξ| ≤ T ^ 20} :=
    measurableSet_le continuous_abs.measurable measurable_const
  have hcompl : {ξ : ℝ | |ξ| ≤ T ^ 20}ᶜ = {ξ : ℝ | T ^ 20 < |ξ|} := by
    ext ξ; simp
  have hsplit := lintegral_add_compl (μ := volume) (fun ξ => ENNReal.ofReal (Wfun K M₁ M₂ M₃' f ξ ^ 2)) hmeas
  rw [hcompl] at hsplit
  set Q := T ^ η with hQdef
  have hQ : 1 ≤ Q := Real.one_le_rpow hT1 hη.le
  set I := ∫ u, f u with hI
  set Jr := (J M (8 * C) (smooth T f)).toReal with hJr
  set s := √(∫ u, f u ^ 2) * √Jr with hs
  have hs0 : 0 ≤ s := by positivity
  have hM2 : 1 / 2 ≤ M := by linarith [h₁.2]
  have hlow := h6 T hT6 f hf M M₁ M₂ M₃' hr
  have hnear := h7 T hT7 f hf M M₁ M₂ M₃' hr
  have hsig := h8 T hT8 f hf M M₁ M₂ M₃' hr
  have hIII := h5 T hT5 f hf M M₁ M₂ M₃' hr
  have hb0 : 0 ≤ A₇ * Q ^ 2 * M := by positivity
  have hc0 : 0 ≤ A₈ * Q ^ 2 * M₂ * s + A₈ * Q * M ^ 4 * I ^ 2 := by
    have : 0 ≤ M₂ := by linarith
    positivity
  have hsqrt : Real.sqrt (M ^ 4 * (∫ u, f u ^ 2) * Jr) = M ^ 2 * s := by
    have hM4 : M ^ 4 = (M ^ 2) ^ 2 := by ring
    rw [hs, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), hM4,
      Real.sqrt_sq (by positivity)]
    ring
  calc ∫⁻ u : ℝ, ENNReal.ofReal (gsum K M₁ M₂ M₃ f u ^ 2)
      ≤ ∫⁻ ξ, ENNReal.ofReal (Wfun K M₁ M₂ M₃' f ξ ^ 2) := hW
    _ = (∫⁻ ξ in {ξ : ℝ | |ξ| ≤ T ^ 20}, ENNReal.ofReal (Wfun K M₁ M₂ M₃' f ξ ^ 2)) +
          ∫⁻ ξ in {ξ : ℝ | T ^ 20 < |ξ|}, ENNReal.ofReal (Wfun K M₁ M₂ M₃' f ξ ^ 2) :=
        hsplit.symm
    _ ≤ (ENNReal.ofReal (A₆ * Q ^ 3 * M ^ 6 * I ^ 2) +
          2 * (ENNReal.ofReal (A₇ * Q ^ 2 * M) *
            ENNReal.ofReal (A₈ * Q ^ 2 * M₂ * s + A₈ * Q * M ^ 4 * I ^ 2))) +
          ENNReal.ofReal (A₅ * M ^ 6 * I ^ 2) := by
        refine add_le_add (hlow.trans (add_le_add le_rfl ?_)) hIII
        gcongr
        exact hnear.trans (by gcongr)
    _ = ENNReal.ofReal (A₆ * Q ^ 3 * M ^ 6 * I ^ 2 +
          2 * (A₇ * Q ^ 2 * M * (A₈ * Q ^ 2 * M₂ * s + A₈ * Q * M ^ 4 * I ^ 2)) +
          A₅ * M ^ 6 * I ^ 2) := by
        rw [← ENNReal.ofReal_mul hb0, ← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
          (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((A₆ + A₅ + 6 * A₇ * A₈) * Q ^ 4 * (M ^ 6 * I ^ 2 +
          Real.sqrt (M ^ 4 * (∫ u, f u ^ 2) * Jr))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hsqrt]
        exact final_arith hA₅ hA₆ hA₇ hA₈ hQ hM2 (by linarith) h₂.2.le I rfl hs0

/-- Lemma 9.2 (iterative bound for `J`), for `M ≤ T⁶`, with the smoothing `f̃` (which does not
depend on `M`) in the class with doubled support constant. -/
theorem iteration_dev (C : ℝ) (c : ℕ → ℝ → ℝ) (K : ℝ) (hC : 1 ≤ C) (hK : 0 < K) (η : ℝ) (hη : 0 < η) :
    ∃ (A T₁ : ℝ) (c' : ℕ → ℝ → ℝ), ∀ T : ℝ, T₁ ≤ T → ∀ f : ℝ → ℝ, Adm C c T f →
      ∃ g : ℝ → ℝ, Adm (2 * C) c' T g ∧ (∫ u, g u) ≤ A * ∫ u, f u ∧
        (∫ u, g u ^ 2) ≤ A * ∫ u, f u ^ 2 ∧
        ∀ M : ℝ, 0 < M → M ≤ T ^ 6 →
        ∀ M₁ M₂ M₃ : ℝ, M₁ ∈ Set.Ioo 0 M → M₂ ∈ Set.Ioo 0 M → M₃ ∈ Set.Ioo 0 M →
        ∫⁻ u : ℝ, ENNReal.ofReal (gsum K M₁ M₂ M₃ f u ^ 2) ≤
          ENNReal.ofReal (A * T ^ η * (M ^ 6 * (∫ u, f u) ^ 2 +
            Real.sqrt (M ^ 4 * (∫ u, f u ^ 2) * (J M (8 * C) g).toReal))) := by
  obtain ⟨A, T₁, hA, hT₁, hmain⟩ := main_bound C c K hC hK (η / 4) (by positivity)
  obtain ⟨c', T₂, hadm⟩ := smooth_adm C c hC
  refine ⟨max A (max βint (βint ^ 2)), max T₁ T₂, c', ?_⟩
  intro T hT f hf
  have hT1 : T₁ ≤ T := le_of_max_le_left hT
  have hT2 : T₂ ≤ T := le_of_max_le_right hT
  have hT0 : 0 < T := by linarith
  have hfc := adm_continuous hf
  have hfcs := adm_hasCompactSupport hf
  refine ⟨smooth T f, hadm T hT2 f hf, ?_, ?_, ?_⟩
  · rw [integral_smooth T hT0 f hfc hfcs]
    exact mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_right _ _))
      (integral_nonneg hf.nonneg)
  · exact (integral_smooth_sq_le T hT0 f hfc hfcs).trans
      (mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_right _ _))
        (integral_nonneg fun u => sq_nonneg (f u)))
  · intro M hM hMT M₁ M₂ M₃ h₁ h₂ h₃
    refine (hmain T hT1 f hf M hM hMT M₁ M₂ M₃ h₁ h₂ h₃).trans (ENNReal.ofReal_le_ofReal ?_)
    have hpow : (T ^ (η / 4)) ^ 4 = T ^ η := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; norm_num
    rw [hpow]
    have hX : 0 ≤ M ^ 6 * (∫ u, f u) ^ 2 +
        Real.sqrt (M ^ 4 * (∫ u, f u ^ 2) * (J M (8 * C) (smooth T f)).toReal) := by
      positivity
    have hTη : 0 ≤ T ^ η := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hTη) hX

end GuthMaynard.Affine
end


theorem solution : type_of% @GuthMaynard.Affine.iteration_dev := @GuthMaynard.Affine.iteration_dev
