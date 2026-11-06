-- Prove2me | solution 1 for GuthMaynard.Affine.lintegral_W_sq_III
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T00:14:14.937301+00:00
-- url     : https://prove2.me/submissions/92ede377-5332-45d5-8ebc-a86063082b23

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

alias mem_dyadic_bounds := GuthMaynard.Affine.PartB.mem_dyadic_bounds

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
theorem abs_of_mem_D₁ {M₁ : ℝ} {m : ℤ} (h : m ∈ D₁ M₁) : M₁ < |(m : ℝ)| ∧ |(m : ℝ)| ≤ 2 * M₁ := by
  simp only [D₁, Finset.mem_union, Finset.mem_map, Equiv.coe_toEmbedding, Equiv.neg_apply] at h
  rcases h with h | ⟨n, hn, rfl⟩
  · obtain ⟨h1, h2⟩ := mem_dyadic_bounds h
    have hM := half_le_of_dyadic_nonempty ⟨m, h⟩
    rw [abs_of_nonneg (by linarith)]; exact ⟨h1, h2⟩
  · obtain ⟨h1, h2⟩ := mem_dyadic_bounds hn
    have hM := half_le_of_dyadic_nonempty ⟨n, hn⟩
    push_cast
    rw [abs_neg, abs_of_nonneg (by linarith)]; exact ⟨h1, h2⟩

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias abs_of_mem_D₁ := GuthMaynard.Affine.PartB.abs_of_mem_D₁

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

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

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

/-- Pointwise bound for `W` used in region III. -/
theorem W_le_III {C : ℝ} {c : ℕ → ℝ → ℝ} {K T : ℝ} (hT : 0 < T) {f : ℝ → ℝ}
    (hf : Adm C c T f) {M M₁ M₂ M₃ AP : ℝ} (hr : Regime T M M₁ M₂ M₃) (hAP : 0 ≤ AP)
    (hP : ∀ x, ‖Pfun K M₃ x‖ ≤ AP * M₃) {ξ : ℝ} (hξ : ξ ≠ 0) :
    Wfun K M₁ M₂ M₃ f ξ ≤ 6 * M * (AP * M₃ * (3 * M * (4 * M *
      (|c 3 1| * T * (2 * M * T / |ξ|) ^ 3 * ⨆ u, f u)))) := by
  have hM₁0 : 0 < M₁ := by linarith [hr.h₁]
  have hM : 0 < M := by linarith [hr.h₁, hr.h₁M]
  have hM₃ : 0 < M₃ := by linarith [hr.h₃]
  have hS : 0 ≤ ⨆ u, f u := Real.iSup_nonneg hf.nonneg
  have hξ0 : 0 < |ξ| := abs_pos.2 hξ
  set D := |c 3 1| * T * (2 * M * T / |ξ|) ^ 3 * ⨆ u, f u with hD
  have hD0 : 0 ≤ D := by positivity
  have hF : ∀ m₁ ∈ D₁ M₁, ‖Ffun M₂ f m₁ ξ‖ ≤ 3 * M * (4 * M * D) := by
    intro m₁ hm
    obtain ⟨hlo, hhi⟩ := abs_of_mem_D₁ hm
    have hm1 : 0 < |(m₁ : ℝ)| := by linarith
    have hm0 : (m₁ : ℝ) ≠ 0 := abs_pos.1 hm1
    have hterm : ∀ m₂ ∈ dyadic M₂,
        ‖(((m₂ : ℝ) / |(m₁ : ℝ)| : ℝ) : ℂ) * fhat f (ξ * m₂ / m₁)‖ ≤ 4 * M * D := by
      intro m₂ hm₂
      obtain ⟨h2lo, h2hi⟩ := mem_dyadic_bounds hm₂
      have hm₂0 : (0 : ℝ) < m₂ := by linarith [hr.h₂]
      have hm₂1 : (1 : ℝ) ≤ m₂ := by
        have : (0 : ℤ) < m₂ := by exact_mod_cast hm₂0
        exact_mod_cast this
      have hη : ξ * m₂ / m₁ ≠ 0 := div_ne_zero (mul_ne_zero hξ hm₂0.ne') hm0
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have hratio : (m₂ : ℝ) / |(m₁ : ℝ)| ≤ 4 * M := by
        rw [div_le_iff₀ hm1]
        nlinarith [hr.h₂M, hr.h₁, hr.h₁M]
      have hfh : ‖fhat f (ξ * m₂ / m₁)‖ ≤ D := by
        have hdec := hf.decay 3 1 one_pos _ hη
        rw [Real.rpow_one] at hdec
        have habs : |ξ * m₂ / m₁| = |ξ| * m₂ / |(m₁ : ℝ)| := by
          rw [abs_div, abs_mul, abs_of_pos hm₂0]
        have hlow : |ξ| / (2 * M) ≤ |ξ * m₂ / m₁| := by
          rw [habs, div_le_div_iff₀ (by positivity) hm1]
          have h1 : |(m₁ : ℝ)| ≤ 2 * M * m₂ := by nlinarith [hr.h₁M]
          nlinarith
        have hTη : T / |ξ * m₂ / m₁| ≤ 2 * M * T / |ξ| := by
          calc T / |ξ * m₂ / m₁| ≤ T / (|ξ| / (2 * M)) :=
                div_le_div_of_nonneg_left hT.le (by positivity) hlow
            _ = 2 * M * T / |ξ| := by field_simp
        calc ‖fhat f (ξ * m₂ / m₁)‖ ≤ c 3 1 * T * (T / |ξ * m₂ / m₁|) ^ 3 * ⨆ u, f u := hdec
          _ ≤ |c 3 1| * T * (T / |ξ * m₂ / m₁|) ^ 3 * ⨆ u, f u := by
              gcongr; exact le_abs_self _
          _ ≤ D := by rw [hD]; gcongr
      exact mul_le_mul hratio hfh (norm_nonneg _) (by positivity)
    unfold Ffun
    calc _ ≤ ∑ m₂ ∈ dyadic M₂, ‖(((m₂ : ℝ) / |(m₁ : ℝ)| : ℝ) : ℂ) * fhat f (ξ * m₂ / m₁)‖ :=
          norm_sum_le _ _
      _ ≤ (dyadic M₂).card • (4 * M * D) := Finset.sum_le_card_nsmul _ _ _ hterm
      _ ≤ 3 * M * (4 * M * D) := by
          rw [nsmul_eq_mul]
          have hc := card_dyadic_le (show 0 ≤ M₂ by linarith [hr.h₂])
          gcongr
          linarith [hr.h₂M, hr.h₂]
  unfold Wfun
  calc ∑ m₁ ∈ D₁ M₁, ‖Pfun K M₃ (ξ / m₁)‖ * ‖Ffun M₂ f m₁ ξ‖
      ≤ ∑ m₁ ∈ D₁ M₁, AP * M₃ * (3 * M * (4 * M * D)) :=
        Finset.sum_le_sum fun m₁ hm => mul_le_mul (hP _) (hF m₁ hm) (norm_nonneg _) (by positivity)
    _ = (D₁ M₁).card * (AP * M₃ * (3 * M * (4 * M * D))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 6 * M * (AP * M₃ * (3 * M * (4 * M * D))) := by
        gcongr
        exact (card_D₁_le hr.h₁).trans (by linarith [hr.h₁M])

theorem lintegral_W_sq_III (C : ℝ) (c : ℕ → ℝ → ℝ) (K : ℝ) (hC : 1 ≤ C) (hK : 0 < K) :
    ∃ A T₁ : ℝ, 0 ≤ A ∧ ∀ T : ℝ, T₁ ≤ T → ∀ f : ℝ → ℝ, Adm C c T f →
      ∀ M M₁ M₂ M₃ : ℝ, Regime T M M₁ M₂ M₃ →
        ∫⁻ ξ in {ξ : ℝ | T ^ 20 < |ξ|}, ENNReal.ofReal (Wfun K M₁ M₂ M₃ f ξ ^ 2) ≤
          ENNReal.ofReal (A * M ^ 6 * (∫ u, f u) ^ 2) := by
  obtain ⟨AP, hAP, hP⟩ := norm_Pfun_le_const K
  obtain ⟨A₀, hA₀, hlow⟩ := sup_le_lower C c hC
  set B := 1152 * AP * |c 3 1| * A₀ with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨2 * Real.pi * B ^ 2, 1, by positivity, ?_⟩
  intro T hT f hf M M₁ M₂ M₃ hr
  have hT0 : 0 < T := by linarith
  have hM : 0 < M := by linarith [hr.h₁, hr.h₁M]
  have hM₃ : 0 < M₃ := by linarith [hr.h₃]
  have hS0 : 0 ≤ ⨆ u, f u := Real.iSup_nonneg hf.nonneg
  have hSI : (⨆ u, f u) ≤ A₀ * T ^ 3 * ∫ u, f u := hlow T hT0 f hf
  have hI0 : 0 ≤ ∫ u, f u := integral_nonneg hf.nonneg
  set I := ∫ u, f u with hIdef
  set S := ⨆ u, f u with hSdef
  have hpt : ∀ ξ ∈ {ξ : ℝ | T ^ 20 < |ξ|}, ENNReal.ofReal (Wfun K M₁ M₂ M₃ f ξ ^ 2) ≤
      ENNReal.ofReal (2 * B ^ 2 * M ^ 6 * I ^ 2) * ENNReal.ofReal ((1 + ξ ^ 2)⁻¹) := by
    intro ξ hξ
    have hξ' : T ^ 20 < |ξ| := hξ
    have hT20 : 1 ≤ T ^ 20 := one_le_pow₀ hT
    set x := |ξ| with hx
    have hx1 : 1 < x := by linarith
    have hx0 : 0 < x := by linarith
    have hξ0 : ξ ≠ 0 := fun h => by rw [h, abs_zero] at hx; linarith
    have hW := W_le_III (K := K) hT0 hf hr hAP (hP M₃ hr.h₃) hξ0
    have hW0 : 0 ≤ Wfun K M₁ M₂ M₃ f ξ :=
      Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [← hx] at hW
    have hW2 : Wfun K M₁ M₂ M₃ f ξ ≤ B * M ^ 7 * T ^ 7 * I / x ^ 3 := by
      refine hW.trans ?_
      have e : 6 * M * (AP * M₃ * (3 * M * (4 * M * (|c 3 1| * T * (2 * M * T / x) ^ 3 * S)))) =
          576 * AP * |c 3 1| * M₃ * M ^ 6 * T ^ 4 * S / x ^ 3 := by
        field_simp; ring
      rw [e]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      calc 576 * AP * |c 3 1| * M₃ * M ^ 6 * T ^ 4 * S
          ≤ 576 * AP * |c 3 1| * (2 * M) * M ^ 6 * T ^ 4 * (A₀ * T ^ 3 * I) := by
            gcongr; exact hr.h₃M
        _ = B * M ^ 7 * T ^ 7 * I := by rw [hB]; ring
    have hsq : ξ ^ 2 = x ^ 2 := (sq_abs ξ).symm
    rw [hsq]
    have hM8 : M ^ 8 ≤ T ^ 48 := by
      calc M ^ 8 ≤ (T ^ 6) ^ 8 := pow_le_pow_left₀ hM.le hr.hMT 8
        _ = T ^ 48 := by ring
    have hT62 : T ^ 62 ≤ x ^ 4 := by
      calc T ^ 62 ≤ T ^ 80 := pow_le_pow_right₀ hT (by norm_num)
        _ = (T ^ 20) ^ 4 := by ring
        _ ≤ x ^ 4 := pow_le_pow_left₀ (by positivity) hξ'.le 4
    have hkey : M ^ 8 * T ^ 14 * (1 + x ^ 2) ≤ 2 * x ^ 6 := by
      have h1 : 1 + x ^ 2 ≤ 2 * x ^ 2 := by nlinarith
      calc M ^ 8 * T ^ 14 * (1 + x ^ 2) ≤ T ^ 48 * T ^ 14 * (2 * x ^ 2) := by gcongr
        _ = T ^ 62 * (2 * x ^ 2) := by ring
        _ ≤ x ^ 4 * (2 * x ^ 2) := by gcongr
        _ = 2 * x ^ 6 := by ring
    calc Wfun K M₁ M₂ M₃ f ξ ^ 2 ≤ (B * M ^ 7 * T ^ 7 * I / x ^ 3) ^ 2 :=
          pow_le_pow_left₀ hW0 hW2 2
      _ = (B ^ 2 * M ^ 6 * I ^ 2) * (M ^ 8 * T ^ 14 / x ^ 6) := by field_simp
      _ ≤ (B ^ 2 * M ^ 6 * I ^ 2) * (2 / (1 + x ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          linarith
      _ = 2 * B ^ 2 * M ^ 6 * I ^ 2 * (1 + x ^ 2)⁻¹ := by ring
  have hmeas : MeasurableSet {ξ : ℝ | T ^ 20 < |ξ|} :=
    measurableSet_lt measurable_const measurable_abs
  have hpi : ∫⁻ ξ : ℝ, ENNReal.ofReal ((1 + ξ ^ 2)⁻¹) = ENNReal.ofReal Real.pi := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal integrable_inv_one_add_sq
      (ae_of_all _ fun x => by positivity), integral_univ_inv_one_add_sq]
  calc ∫⁻ ξ in {ξ : ℝ | T ^ 20 < |ξ|}, ENNReal.ofReal (Wfun K M₁ M₂ M₃ f ξ ^ 2)
      ≤ ∫⁻ ξ in {ξ : ℝ | T ^ 20 < |ξ|}, ENNReal.ofReal (2 * B ^ 2 * M ^ 6 * I ^ 2) *
          ENNReal.ofReal ((1 + ξ ^ 2)⁻¹) := setLIntegral_mono' hmeas hpt
    _ ≤ ∫⁻ ξ, ENNReal.ofReal (2 * B ^ 2 * M ^ 6 * I ^ 2) * ENNReal.ofReal ((1 + ξ ^ 2)⁻¹) :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (2 * B ^ 2 * M ^ 6 * I ^ 2) * ENNReal.ofReal Real.pi := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hpi]
    _ = ENNReal.ofReal (2 * Real.pi * B ^ 2 * M ^ 6 * I ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

end GuthMaynard.Affine.PartR
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias lintegral_W_sq_III_dev := GuthMaynard.Affine.PartR.lintegral_W_sq_III

end GuthMaynard.Affine
end


theorem solution : type_of% @GuthMaynard.Affine.lintegral_W_sq_III_dev := @GuthMaynard.Affine.lintegral_W_sq_III_dev
