-- Prove2me | solution 1 for GuthMaynard.Affine.Sig_large_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T00:14:17.106289+00:00
-- url     : https://prove2.me/submissions/46b35a83-ff84-4f82-b69d-1712d5c974b7

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

theorem norm_e_sub_le (ξ x y : ℝ) :
    ‖((𝐞 (ξ * x) : ℂ) - 𝐞 (ξ * y))‖ ≤ 2 * Real.pi * (|ξ| * |x - y|) := by
  have e1 : (𝐞 (ξ * x) : ℂ) = 𝐞 (ξ * y) * 𝐞 (ξ * (x - y)) := by
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]; congr 2; ring
  rw [e1, ← mul_sub_one, norm_mul, Circle.norm_coe, one_mul, Real.fourierChar_apply, mul_comm]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans (le_of_eq ?_)
  rw [Real.norm_eq_abs]
  simp only [abs_mul, abs_two, abs_of_pos Real.pi_pos]

/-- The Lipschitz bound `|f x - f y| ≤ 4π(|c 0 1| + |c 3 1|) T³ S |x - y|`. -/
theorem lipschitz {C : ℝ} {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hf : Adm C c T f) (hT : 0 < T)
    (x y : ℝ) : |f x - f y| ≤
      4 * Real.pi * (|c 0 1| + |c 3 1|) * T ^ 3 * (⨆ u, f u) * |x - y| := by
  have hcont : Continuous f := hf.smooth.continuous
  set S := ⨆ u, f u
  have hS : 0 ≤ S := Real.iSup_nonneg hf.nonneg
  set F : ℝ → ℂ := fun u => (f u : ℂ) with hF
  have hFc : Continuous F := continuous_ofReal.comp hcont
  have hFi : Integrable F :=
    (hcont.integrable_of_hasCompactSupport (cont_hcs hcont hf.supp)).ofReal
  have hFFc : Continuous (𝓕 F) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hFi
  have hint := fourier_integrable hf hT
  have hie : ∀ z : ℝ, Integrable (fun ξ : ℝ => 𝐞 (ξ * z) • 𝓕 F ξ) := by
    intro z
    refine hint.norm.mono' (Continuous.aestronglyMeasurable ?_)
      (Filter.Eventually.of_forall fun ξ => by rw [Circle.norm_smul])
    exact (Real.continuous_fourierChar.comp (continuous_id.mul continuous_const)).smul hFFc
  have ha : 0 ≤ |c 0 1| * T ^ 2 * S := by positivity
  have hb : 0 ≤ |c 3 1| * T ^ 4 * S := by positivity
  have hgi := (integrable_prof_abs ha hb hT).const_mul (2 * Real.pi * |x - y|)
  have hdiff : F x - F y = ∫ ξ, (𝐞 (ξ * x) • 𝓕 F ξ - 𝐞 (ξ * y) • 𝓕 F ξ) := by
    rw [integral_sub (hie x) (hie y), ← inversion hFc hFi hint, ← inversion hFc hFi hint]
  have hnorm : ‖F x - F y‖ ≤ ∫ ξ, 2 * Real.pi * |x - y| * prof (|c 0 1| * T ^ 2 * S)
      (|c 3 1| * T ^ 4 * S) T |ξ| := by
    rw [hdiff]
    refine norm_integral_le_of_norm_le hgi ?_
    filter_upwards [ae_ne_zero] with ξ hξ
    rw [Circle.smul_def, Circle.smul_def, ← sub_smul, norm_smul]
    have hbd : |ξ| * ‖𝓕 F ξ‖ ≤ prof (|c 0 1| * T ^ 2 * S) (|c 3 1| * T ^ 4 * S) T |ξ| := by
      unfold prof
      split_ifs with h
      · have := decay_le hf hT 0 ξ hξ
        simp only [zero_add, pow_one, pow_zero, div_one] at this
        calc |ξ| * ‖𝓕 F ξ‖ ≤ T * (|c 0 1| * T * S) := by
              gcongr
          _ = |c 0 1| * T ^ 2 * S := by ring
      · have := decay_le hf hT 3 ξ hξ
        have hξ0 : 0 < |ξ| := abs_pos.2 hξ
        calc |ξ| * ‖𝓕 F ξ‖ ≤ |ξ| * (|c 3 1| * T ^ (3 + 1) * S / |ξ| ^ 3) := by gcongr
          _ = |c 3 1| * T ^ 4 * S / |ξ| ^ 2 := by field_simp; ring
    calc ‖(𝐞 (ξ * x) : ℂ) - 𝐞 (ξ * y)‖ * ‖𝓕 F ξ‖
        ≤ 2 * Real.pi * (|ξ| * |x - y|) * ‖𝓕 F ξ‖ := by gcongr; exact norm_e_sub_le ξ x y
      _ = 2 * Real.pi * |x - y| * (|ξ| * ‖𝓕 F ξ‖) := by ring
      _ ≤ _ := by gcongr
  rw [integral_const_mul, integral_prof_abs ha hb hT] at hnorm
  have hFxy : |f x - f y| = ‖F x - F y‖ := by
    simp only [F, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hFxy]
  refine hnorm.trans (le_of_eq ?_)
  field_simp
  ring

/-- Mass lower bound: `S ≤ 2 Λ ∫ f` given a Lipschitz bound with constant `Λ S`. -/
theorem sup_le_mass {C : ℝ} {f : ℝ → ℝ} (hcont : Continuous f) (hnn : ∀ u, 0 ≤ f u)
    (hsupp : Function.support f ⊆ Set.Icc (1 / C) C) {Λ : ℝ} (hΛ : 0 < Λ)
    (hlip : ∀ x y, |f x - f y| ≤ Λ * (⨆ u, f u) * |x - y|) :
    (⨆ u, f u) ≤ 2 * Λ * ∫ u, f u := by
  set S := ⨆ u, f u
  have hcs := cont_hcs hcont hsupp
  have hint : Integrable f := hcont.integrable_of_hasCompactSupport hcs
  obtain ⟨x₀, hx₀⟩ := hcont.exists_forall_ge_of_hasCompactSupport hcs
  have hSx : S ≤ f x₀ := ciSup_le hx₀
  set r := 1 / (2 * Λ) with hr
  have hr0 : 0 < r := by positivity
  have hlow : ∀ y ∈ Set.Icc (x₀ - r) (x₀ + r), S / 2 ≤ f y := by
    intro y hy
    have h1 := hlip x₀ y
    have h2 : |x₀ - y| ≤ r := by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
    have h3 : Λ * S * |x₀ - y| ≤ Λ * S * r := by
      have : 0 ≤ Λ * S := mul_nonneg hΛ.le (Real.iSup_nonneg hnn)
      gcongr
    have h4 : Λ * S * r = S / 2 := by rw [hr]; field_simp
    have := (abs_le.1 h1).2
    linarith
  have h1 := setIntegral_ge_of_const_le (μ := volume) measurableSet_Icc
    (by simp) hlow hint.integrableOn
  have h2 : ∫ u in Set.Icc (x₀ - r) (x₀ + r), f u ≤ ∫ u, f u :=
    setIntegral_le_integral hint (Filter.Eventually.of_forall hnn)
  rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul] at h1
  have h5 : (x₀ + r - (x₀ - r)) * (S / 2) = S / (2 * Λ) := by rw [hr]; field_simp; ring
  rw [h5] at h1
  have := le_trans h1 h2
  rw [div_le_iff₀ (by positivity)] at this
  linarith

/-- Lower bound for the mass (brief, `lintegral_gsum_sq_le_of_large` (a), (b)):
`f` is `O(T³ S)`-Lipschitz, so `S ≤ A₀ T³ ∫ f`. -/
theorem sup_le_lower (C : ℝ) (c : ℕ → ℝ → ℝ) (hC : 1 ≤ C) :
    ∃ A₀ : ℝ, 0 ≤ A₀ ∧ ∀ T : ℝ, 0 < T → ∀ f : ℝ → ℝ, Adm C c T f →
      (⨆ u, f u) ≤ A₀ * T ^ 3 * ∫ u, f u := by
  refine ⟨8 * Real.pi * (|c 0 1| + |c 3 1| + 1), by positivity, fun T hT f hf => ?_⟩
  have hS : 0 ≤ ⨆ u, f u := Real.iSup_nonneg hf.nonneg
  have hΛ : 0 < 4 * Real.pi * (|c 0 1| + |c 3 1| + 1) * T ^ 3 := by positivity
  have h := sup_le_mass hf.smooth.continuous hf.nonneg hf.supp hΛ (fun x y => by
    refine (lipschitz hf hT x y).trans ?_
    gcongr 4 * Real.pi * ?_ * T ^ 3 * (⨆ u, f u) * |x - y|
    linarith)
  calc (⨆ u, f u) ≤ 2 * (4 * Real.pi * (|c 0 1| + |c 3 1| + 1) * T ^ 3) * ∫ u, f u := h
    _ = 8 * Real.pi * (|c 0 1| + |c 3 1| + 1) * T ^ 3 * ∫ u, f u := by ring

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias sup_le_lower := GuthMaynard.Affine.PartS.sup_le_lower

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

/-- Pointwise bound for `Γ` on the range of `SigTerm ℓ`, `|ℓ| > TQ/M₂`. -/
theorem norm_Γ_large {C : ℝ} {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hf : Adm C c T f)
    (hT : 0 < T) (n : ℕ) {Q M₂ M₃ : ℝ} (hQ : 0 < Q) (hM₂ : 1 / 2 ≤ M₂) (hM₃ : 0 < M₃) {ℓ : ℤ}
    (hℓ : T * Q / M₂ < |(ℓ : ℝ)|) {τ : ℝ} (hτ : |τ| ≤ Q) (hy : 2 * Q / M₃ ≤ |(ℓ : ℝ) + τ / M₃|) :
    ‖Γfun M₂ f (ℓ + τ / M₃)‖ ≤ 6 * (3 / 2) ^ (n + 2) * |c (n + 2) 1| * T ^ 2 * (⨆ u, f u) *
      M₂ * (1 / Q) ^ (n + 1) * (1 / |(ℓ : ℝ)|) := by
  set y := (ℓ : ℝ) + τ / M₃ with hydef
  set S := ⨆ u, f u with hSdef
  have hS0 : 0 ≤ S := Real.iSup_nonneg hf.nonneg
  have hM₂0 : 0 < M₂ := by linarith
  have hℓ0 : 0 < |(ℓ : ℝ)| := lt_of_le_of_lt (by positivity) hℓ
  have hτM : |τ / M₃| ≤ Q / M₃ := by
    rw [abs_div, abs_of_pos hM₃]; exact div_le_div_of_nonneg_right hτ hM₃.le
  have hy2 : 2 * |(ℓ : ℝ)| / 3 ≤ |y| := by
    have e : (ℓ : ℝ) = y - τ / M₃ := by rw [hydef]; ring
    have h1 : |(ℓ : ℝ)| ≤ |y| + |τ / M₃| := by rw [e]; exact abs_sub _ _
    have h2 : Q / M₃ ≤ |y| / 2 := by
      have : 2 * Q / M₃ = 2 * (Q / M₃) := by ring
      linarith
    linarith
  set ρ := T / (M₂ * |(ℓ : ℝ)|) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρQ : ρ ≤ 1 / Q := by
    rw [hρ, div_le_div_iff₀ (by positivity) hQ, one_mul]
    rw [div_lt_iff₀ hM₂0] at hℓ
    linarith
  set c' := |c (n + 2) 1| with hc'
  set X := c' * T * ((3 / 2) ^ (n + 2) * (1 / Q) ^ (n + 1) * ρ) * S with hX
  have hterm : ∀ m₂ ∈ dyadic M₂, ‖(m₂ : ℂ) * fhat f (m₂ * y)‖ ≤ 2 * M₂ * X := by
    intro m₂ hm₂
    obtain ⟨h1, h2⟩ := mem_dyadic hm₂
    have hm0 : (0 : ℝ) < m₂ := by linarith
    have hmy : M₂ * (2 * |(ℓ : ℝ)| / 3) ≤ |(m₂ : ℝ) * y| := by
      rw [abs_mul, abs_of_pos hm0]
      exact mul_le_mul h1.le hy2 (by positivity) hm0.le
    have hmy0 : 0 < |(m₂ : ℝ) * y| := lt_of_lt_of_le (by positivity) hmy
    have hratio : T / |(m₂ : ℝ) * y| ≤ 3 / 2 * ρ := by
      calc T / |(m₂ : ℝ) * y| ≤ T / (M₂ * (2 * |(ℓ : ℝ)| / 3)) :=
            div_le_div_of_nonneg_left hT.le (by positivity) hmy
        _ = 3 / 2 * ρ := by rw [hρ]; field_simp
    have hpow : (T / |(m₂ : ℝ) * y|) ^ (n + 2) ≤ (3 / 2) ^ (n + 2) * (1 / Q) ^ (n + 1) * ρ := by
      calc (T / |(m₂ : ℝ) * y|) ^ (n + 2) ≤ (3 / 2 * ρ) ^ (n + 2) :=
            pow_le_pow_left₀ (by positivity) hratio _
        _ = (3 / 2) ^ (n + 2) * ρ ^ (n + 1) * ρ := by ring
        _ ≤ (3 / 2) ^ (n + 2) * (1 / Q) ^ (n + 1) * ρ := by
            gcongr
    have hdec := hf.decay (n + 2) 1 one_pos (m₂ * y) (abs_pos.1 hmy0)
    rw [Real.rpow_one] at hdec
    have hfh : ‖fhat f (m₂ * y)‖ ≤ X := by
      unfold fhat
      refine hdec.trans ?_
      rw [hX]
      have hcc : c (n + 2) 1 ≤ c' := le_abs_self _
      have hA : 0 ≤ (T / |(m₂ : ℝ) * y|) ^ (n + 2) := by positivity
      calc c (n + 2) 1 * T * (T / |(m₂ : ℝ) * y|) ^ (n + 2) * S
          ≤ c' * T * (T / |(m₂ : ℝ) * y|) ^ (n + 2) * S := by gcongr
        _ ≤ c' * T * ((3 / 2) ^ (n + 2) * (1 / Q) ^ (n + 1) * ρ) * S := by gcongr
    rw [norm_mul, Complex.norm_intCast, abs_of_pos hm0]
    exact mul_le_mul h2 hfh (norm_nonneg _) (by positivity)
  have hX0 : 0 ≤ X := by positivity
  have hcard : ((dyadic M₂).card : ℝ) ≤ 3 * M₂ := (card_dyadic_le hM₂0.le).trans (by linarith)
  unfold Γfun
  calc ‖∑ m₂ ∈ dyadic M₂, (m₂ : ℂ) * fhat f (m₂ * y)‖
      ≤ ∑ m₂ ∈ dyadic M₂, 2 * M₂ * X := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = ((dyadic M₂).card : ℝ) * (2 * M₂ * X) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 3 * M₂ * (2 * M₂ * X) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by rw [hX, hρ]; field_simp; ring

/-- `Σ_large` (`|ℓ| > L₀ = T^{1+η}/M₂`): `|m₂ y| ≥ M₂|ℓ|/3`, decay with large `j`, then
`sup_le_lower`. -/
theorem Sig_large_le (C : ℝ) (c : ℕ → ℝ → ℝ) (hC : 1 ≤ C) (η : ℝ) (hη : 0 < η) :
    ∃ A T₁ : ℝ, 0 ≤ A ∧ ∀ T : ℝ, T₁ ≤ T → ∀ f : ℝ → ℝ, Adm C c T f →
      ∀ M M₁ M₂ M₃ : ℝ, Regime T M M₁ M₂ M₃ →
        SigLarge (T ^ (1 + η) / M₂) (T ^ η) M₂ M₃ f ≤
          ENNReal.ofReal (A * M ^ 4 * (∫ u, f u) ^ 2) := by
  obtain ⟨A₀, hA₀, hlow⟩ := sup_le_lower C c hC
  set n := ⌈10 / η⌉₊ with hn
  set G₀ := 6 * (3 / 2) ^ (n + 2) * |c (n + 2) 1| with hG₀
  have hG₀0 : 0 ≤ G₀ := by positivity
  set S₁ := ∑' ℓ : ℤ, 1 / (ℓ : ℝ) ^ 2 with hS₁
  have hS₁s : Summable (fun ℓ : ℤ => 1 / (ℓ : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.2 one_lt_two
  have hS₁0 : 0 ≤ S₁ := tsum_nonneg fun ℓ => by positivity
  refine ⟨8 * G₀ ^ 2 * A₀ ^ 2 * S₁, 1, by positivity, ?_⟩
  intro T hT1 f hf M M₁ M₂ M₃ hr
  have hT0 : 0 < T := by linarith
  set Q := T ^ η with hQdef
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hT1 hη.le
  have hQ0 : 0 < Q := by linarith
  have hQn : T ^ 10 ≤ Q ^ n := by
    have e1 : Q ^ n = T ^ (η * n) := by
      rw [hQdef, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
    have e2 : T ^ 10 = T ^ ((10 : ℕ) : ℝ) := (Real.rpow_natCast T 10).symm
    rw [e1, e2]
    refine Real.rpow_le_rpow_of_exponent_le hT1 ?_
    have h1 : 10 / η ≤ (n : ℝ) := Nat.le_ceil _
    have e : ((10 : ℕ) : ℝ) = η * (10 / η) := by push_cast; field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left h1 hη.le
  have hM₂ : 1 / 2 ≤ M₂ := hr.h₂
  have hM₂0 : 0 < M₂ := by linarith
  have hM₃ : 0 < M₃ := by linarith [hr.h₃]
  have hMM : M₂ ^ 2 ≤ 4 * M ^ 4 := by
    have h1 : M₂ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hM₂0.le hr.h₂M.le 2
    have h2 : 1 / 4 ≤ M ^ 2 := by nlinarith [hr.h₂M]
    nlinarith
  set S := ⨆ u, f u with hSdef
  have hS0 : 0 ≤ S := Real.iSup_nonneg hf.nonneg
  set I := ∫ u, f u with hI
  have hSI : S ≤ A₀ * T ^ 3 * I := hlow T hT0 f hf
  have hL₀ : T ^ (1 + η) / M₂ = T * Q / M₂ := by rw [Real.rpow_add hT0, Real.rpow_one]
  set P := (1 / Q) ^ (n + 1) with hP
  have hPQ : T ^ 10 * (P ^ 2 * Q) ≤ 1 := by
    have e : P ^ 2 * Q = (1 / Q) ^ n * (1 / Q) ^ (n + 1) := by
      calc P ^ 2 * Q = (1 / Q) ^ n * (1 / Q) ^ (n + 1) * ((1 / Q) * Q) := by rw [hP]; ring
        _ = (1 / Q) ^ n * (1 / Q) ^ (n + 1) := by rw [one_div_mul_cancel hQ0.ne', mul_one]
    have h1 : (1 / Q) ^ (n + 1) ≤ 1 := pow_le_one₀ (by positivity) (by
      rw [div_le_one hQ0]; exact hQ1)
    have h2 : T ^ 10 * (1 / Q) ^ n ≤ 1 := by
      rw [one_div_pow, mul_one_div, div_le_one (by positivity)]; exact hQn
    rw [e]
    have h3 : 0 ≤ T ^ 10 * (1 / Q) ^ n := by positivity
    nlinarith
  set B₁ := 8 * G₀ ^ 2 * A₀ ^ 2 * M ^ 4 * I ^ 2 with hB₁
  have hterm : ∀ ℓ : ℤ, (if ℓ ≠ 0 ∧ T ^ (1 + η) / M₂ < |(ℓ : ℝ)| then SigTerm Q M₂ M₃ f ℓ
      else 0) ≤ ENNReal.ofReal (B₁ * (1 / (ℓ : ℝ) ^ 2)) := by
    intro ℓ
    split_ifs with h
    swap
    · exact zero_le
    have hℓ : T * Q / M₂ < |(ℓ : ℝ)| := by rw [← hL₀]; exact h.2
    set b := G₀ * T ^ 2 * S * M₂ * P * (1 / |(ℓ : ℝ)|) with hb
    unfold SigTerm
    calc ∫⁻ τ in {τ : ℝ | |τ| ≤ Q ∧ 2 * Q / M₃ ≤ |(ℓ : ℝ) + τ / M₃|},
          ‖Γfun M₂ f (ℓ + τ / M₃)‖ₑ ^ 2
        ≤ ∫⁻ τ in {τ : ℝ | |τ| ≤ Q ∧ 2 * Q / M₃ ≤ |(ℓ : ℝ) + τ / M₃|},
          ENNReal.ofReal (b ^ 2) := by
          refine setLIntegral_mono measurable_const fun τ hτ => ?_
          rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _)
            (norm_Γ_large hf hT0 n hQ0 hM₂ hM₃ hℓ hτ.1 hτ.2) 2)
      _ = ENNReal.ofReal (b ^ 2) *
          volume {τ : ℝ | |τ| ≤ Q ∧ 2 * Q / M₃ ≤ |(ℓ : ℝ) + τ / M₃|} := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (b ^ 2) * volume (Set.Icc (-Q) Q) := by
          gcongr
          intro τ hτ
          exact abs_le.1 hτ.1
      _ = ENNReal.ofReal (b ^ 2 * (2 * Q)) := by
          rw [Real.volume_Icc, ← ENNReal.ofReal_mul (sq_nonneg b)]
          congr 2; ring
      _ ≤ ENNReal.ofReal (B₁ * (1 / (ℓ : ℝ) ^ 2)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hl : (1 / |(ℓ : ℝ)|) ^ 2 = 1 / (ℓ : ℝ) ^ 2 := by rw [div_pow, sq_abs, one_pow]
          have hl0 : 0 ≤ 1 / (ℓ : ℝ) ^ 2 := by positivity
          have e : b ^ 2 * (2 * Q) =
              2 * G₀ ^ 2 * M₂ ^ 2 * (1 / (ℓ : ℝ) ^ 2) * (S ^ 2 * T ^ 4 * (P ^ 2 * Q)) := by
            rw [hb, ← hl]; ring
          have hS2 : S ^ 2 ≤ (A₀ * T ^ 3 * I) ^ 2 := pow_le_pow_left₀ hS0 hSI 2
          have hk : S ^ 2 * T ^ 4 * (P ^ 2 * Q) ≤ A₀ ^ 2 * I ^ 2 := by
            have hPQ0 : 0 ≤ T ^ 4 * (P ^ 2 * Q) := by positivity
            calc S ^ 2 * T ^ 4 * (P ^ 2 * Q) = S ^ 2 * (T ^ 4 * (P ^ 2 * Q)) := by ring
              _ ≤ (A₀ * T ^ 3 * I) ^ 2 * (T ^ 4 * (P ^ 2 * Q)) :=
                  mul_le_mul_of_nonneg_right hS2 hPQ0
              _ = A₀ ^ 2 * I ^ 2 * (T ^ 10 * (P ^ 2 * Q)) := by ring
              _ ≤ A₀ ^ 2 * I ^ 2 * 1 := mul_le_mul_of_nonneg_left hPQ (by positivity)
              _ = A₀ ^ 2 * I ^ 2 := mul_one _
          rw [e, hB₁]
          have h0 : 0 ≤ 2 * G₀ ^ 2 * M₂ ^ 2 * (1 / (ℓ : ℝ) ^ 2) := by positivity
          calc 2 * G₀ ^ 2 * M₂ ^ 2 * (1 / (ℓ : ℝ) ^ 2) * (S ^ 2 * T ^ 4 * (P ^ 2 * Q))
              ≤ 2 * G₀ ^ 2 * M₂ ^ 2 * (1 / (ℓ : ℝ) ^ 2) * (A₀ ^ 2 * I ^ 2) :=
                mul_le_mul_of_nonneg_left hk h0
            _ = 2 * G₀ ^ 2 * A₀ ^ 2 * I ^ 2 * (1 / (ℓ : ℝ) ^ 2) * M₂ ^ 2 := by ring
            _ ≤ 2 * G₀ ^ 2 * A₀ ^ 2 * I ^ 2 * (1 / (ℓ : ℝ) ^ 2) * (4 * M ^ 4) :=
                mul_le_mul_of_nonneg_left hMM (by positivity)
            _ = 8 * G₀ ^ 2 * A₀ ^ 2 * M ^ 4 * I ^ 2 * (1 / (ℓ : ℝ) ^ 2) := by ring
  have hB₁0 : 0 ≤ B₁ := by positivity
  calc SigLarge (T ^ (1 + η) / M₂) Q M₂ M₃ f
      ≤ ∑' ℓ : ℤ, ENNReal.ofReal (B₁ * (1 / (ℓ : ℝ) ^ 2)) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' ℓ : ℤ, B₁ * (1 / (ℓ : ℝ) ^ 2)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun ℓ => by positivity) (hS₁s.mul_left _)).symm
    _ = ENNReal.ofReal (8 * G₀ ^ 2 * A₀ ^ 2 * S₁ * M ^ 4 * I ^ 2) := by
        rw [tsum_mul_left, hB₁, ← hS₁]; ring_nf

end GuthMaynard.Affine.PartZ
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias Sig_large_le_dev := GuthMaynard.Affine.PartZ.Sig_large_le
end GuthMaynard.Affine
end


theorem solution : type_of% @GuthMaynard.Affine.Sig_large_le_dev := @GuthMaynard.Affine.Sig_large_le_dev
