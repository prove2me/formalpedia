-- Prove2me | solution 1 for HryniewiczCriterion.exists_strip_center
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T10:17:13.315601+00:00
-- url     : https://prove2.me/submissions/98df2053-bc87-42cd-8af8-e1cb1ea2001e

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Log

open HryniewiczCriterion
open MeasureTheory Set Complex

/-!
# Strip coordinates for a punctured disk

A centre `c` off the (null) lines through pairs of punctures; each puncture `z` lies on the ray
from `c` to the boundary point `∂(s_z)`, at height `λ_z = 1 / t_z ∈ (0,1)` where `t_z > 1` is the
positive root of `|c + t (z - c)|² = 1`. The positive root is unique (product of roots `< 0`).
-/


noncomputable section

namespace HryniewiczCriterion

lemma rg_cp_surj (w : Plane) (hw : w 0 ^ 2 + w 1 ^ 2 = 1) : ∃ s, circlePoint s = w := by
  set z : ℂ := (w 0 : ℂ) + (w 1 : ℂ) * I
  have hzre : z.re = w 0 := by simp [z]
  have hzim : z.im = w 1 := by simp [z]
  have hzn : ‖z‖ = 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [normSq_apply, hzre, hzim] at h
    nlinarith [norm_nonneg z]
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hzn; norm_num at hzn
  refine ⟨arg z / (2 * Real.pi), ?_⟩
  have h2 : 2 * Real.pi * (arg z / (2 * Real.pi)) = arg z := by field_simp
  ext i; fin_cases i
  · simp only [circlePoint, h2]
    simp [Complex.cos_arg hz0, hzn, hzre]
  · simp only [circlePoint, h2]
    simp [Complex.sin_arg, hzn, hzim]

lemma rg_cp_inj {s s' : ℝ} (h : circlePoint s = circlePoint s') : ∃ n : ℤ, s = s' + n := by
  have h0 : Real.cos (2 * Real.pi * s) = Real.cos (2 * Real.pi * s') := by
    simpa [circlePoint] using congrFun h 0
  have h1 : Real.sin (2 * Real.pi * s) = Real.sin (2 * Real.pi * s') := by
    simpa [circlePoint] using congrFun h 1
  have he : Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * I) =
      Complex.exp (((2 * Real.pi * s' : ℝ) : ℂ) * I) := by
    apply Complex.ext
    · rw [exp_ofReal_mul_I_re, exp_ofReal_mul_I_re, h0]
    · rw [exp_ofReal_mul_I_im, exp_ofReal_mul_I_im, h1]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 he
  refine ⟨n, ?_⟩
  have him := congrArg Complex.im hn
  simp at him
  have hp := Real.pi_pos
  have : 2 * Real.pi * s = 2 * Real.pi * (s' + n) := by linarith
  exact mul_left_cancel₀ (by positivity) this

lemma rg_cp_int (s : ℝ) (n : ℤ) : circlePoint (s + n) = circlePoint s := by
  have h : 2 * Real.pi * (s + n) = 2 * Real.pi * s + n * (2 * Real.pi) := by ring
  ext i; fin_cases i
  · simp only [circlePoint, h]; simp [Real.cos_add_int_mul_two_pi]
  · simp only [circlePoint, h]; simp [Real.sin_add_int_mul_two_pi]

lemma rg_cp_sq (s : ℝ) : circlePoint s 0 ^ 2 + circlePoint s 1 ^ 2 = 1 := by
  simp [circlePoint, Real.cos_sq_add_sin_sq]

lemma rg_plane_ext {u v : Plane} (h0 : u 0 = v 0) (h1 : u 1 = v 1) : u = v := by
  ext i; fin_cases i <;> assumption

lemma rg_line_null (z w : Plane) : volume (range fun t : ℝ => z + t • (w - z)) = 0 := by
  let S : Submodule ℝ Plane := LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1)
  have hS : (S : Set Plane) = {p : Plane | p 1 = 0} := by
    ext p; simp [S]
  have hnull : volume {p : Plane | p 1 = 0} = 0 := by
    rw [← hS]
    refine Measure.addHaar_submodule volume S ?_
    intro htop
    have h : (Pi.single 1 1 : Plane) ∈ S := htop ▸ Submodule.mem_top
    simp [S] at h
  set F : Plane → Plane := fun p => z + p 0 • (w - z)
  have hsub : (range fun t : ℝ => z + t • (w - z)) ⊆ F '' {p : Plane | p 1 = 0} := by
    rintro _ ⟨t, rfl⟩
    exact ⟨![t, 0], by simp, by simp [F]⟩
  have hF : DifferentiableOn ℝ F {p : Plane | p 1 = 0} :=
    (by fun_prop : Differentiable ℝ F).differentiableOn
  exact measure_mono_null hsub (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    volume hF hnull)

/-- The ray from `c` through `z` meets the circle once, beyond `z`. -/
lemma rg_ray {c z : Plane} (hc : c ∈ openUnitDisk) (hz : z ∈ openUnitDisk) (hcz : c ≠ z) :
    ∃ l s : ℝ, 0 < l ∧ l < 1 ∧ z = c + l • (circlePoint s - c) ∧
      ∀ μ s' : ℝ, 0 ≤ μ → c + μ • (circlePoint s' - c) = z → μ = l ∧ ∃ n : ℤ, s' = s + n := by
  have hc' : c 0 ^ 2 + c 1 ^ 2 < 1 := hc
  have hz' : z 0 ^ 2 + z 1 ^ 2 < 1 := hz
  set d0 := z 0 - c 0
  set d1 := z 1 - c 1
  set A := d0 ^ 2 + d1 ^ 2
  set B := c 0 * d0 + c 1 * d1
  set C := c 0 ^ 2 + c 1 ^ 2 - 1
  have hA : 0 < A := by
    rcases (show d0 ≠ 0 ∨ d1 ≠ 0 by
      by_contra h; push_neg at h
      exact hcz (rg_plane_ext (by linarith [h.1]) (by linarith [h.2]))) with h | h
    · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; positivity
    · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; positivity
  have hC : C < 0 := by simp only [C]; linarith
  have hf1 : A + 2 * B + C < 0 := by
    have : z 0 = c 0 + d0 := by simp [d0]
    have : z 1 = c 1 + d1 := by simp [d1]
    simp only [A, B, C]; nlinarith
  set D := B ^ 2 - A * C
  have hD : 0 < D := by simp only [D]; nlinarith [sq_nonneg B, mul_neg_of_pos_of_neg hA hC]
  have hsq := Real.sq_sqrt hD.le
  have hsqrt : A + B < Real.sqrt D := by
    rcases lt_or_ge (A + B) 0 with h | h
    · linarith [Real.sqrt_nonneg D]
    · rw [Real.lt_sqrt h]; simp only [D]; nlinarith
  set v := (-B + Real.sqrt D) / A
  have hv1 : 1 < v := by rw [lt_div_iff₀ hA]; linarith
  have hfv : A * v ^ 2 + 2 * B * v + C = 0 := by
    simp only [v]; field_simp; ring_nf; rw [hsq]; simp only [D]; ring
  -- the boundary point
  set q : Plane := c + v • (z - c)
  have hq : q 0 ^ 2 + q 1 ^ 2 = 1 := by
    simp only [q, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    simp only [A, B, C, d0, d1] at hfv; nlinarith
  obtain ⟨s, hs⟩ := rg_cp_surj q hq
  have hv0 : 0 < v := by linarith
  refine ⟨1 / v, s, by positivity, by rw [div_lt_one hv0]; exact hv1, ?_, ?_⟩
  · rw [hs]; simp only [q]
    rw [add_sub_cancel_left, smul_smul, one_div_mul_cancel hv0.ne', one_smul, add_sub_cancel]
  · intro μ s' hμ he
    have hμ0 : μ ≠ 0 := by
      rintro rfl; apply hcz; simpa using he
    have hμpos : 0 < μ := lt_of_le_of_ne hμ (Ne.symm hμ0)
    set u := 1 / μ
    have hu0 : 0 < u := by positivity
    have hp0 : circlePoint s' 0 = c 0 + u * d0 := by
      have := congrFun he 0
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this
      simp only [u, d0]; rw [← this]; field_simp; ring
    have hp1 : circlePoint s' 1 = c 1 + u * d1 := by
      have := congrFun he 1
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this
      simp only [u, d1]; rw [← this]; field_simp; ring
    have hfu : A * u ^ 2 + 2 * B * u + C = 0 := by
      have := rg_cp_sq s'
      rw [hp0, hp1] at this
      simp only [A, B, C]; nlinarith
    have huv : u = v := by
      by_contra hne
      have h1 : A * (u + v) + 2 * B = 0 := by
        have : (u - v) * (A * (u + v) + 2 * B) = 0 := by linear_combination hfu - hfv
        rcases mul_eq_zero.1 this with h | h
        · exact absurd (sub_eq_zero.1 h) hne
        · exact h
      have : A * (u * v) = C := by linear_combination u * h1 - hfu
      linarith [mul_pos hA (mul_pos hu0 hv0)]
    refine ⟨?_, ?_⟩
    · rw [← huv]; simp only [u]; field_simp
    · apply rg_cp_inj
      rw [hs]
      apply rg_plane_ext
      · rw [hp0, huv]; simp [q, d0]
      · rw [hp1, huv]; simp [q, d1]

theorem exists_strip_center' (Z : Finset Plane) (hZ : ∀ z ∈ Z, z ∈ openUnitDisk) :
    ∃ c : Plane, c ∈ openUnitDisk ∧ ∃ lam sp : Plane → ℝ, ∀ z ∈ Z,
      0 < lam z ∧ lam z < 1 ∧ z = c + lam z • (circlePoint (sp z) - c) ∧
      (∀ μ s : ℝ, 0 ≤ μ → c + μ • (circlePoint s - c) = z → μ = lam z ∧ ∃ n : ℤ, s = sp z + n) ∧
      (∀ w ∈ Z, w ≠ z → ∀ n : ℤ, sp w ≠ sp z + n) := by
  classical
  set B : Set Plane := ⋃ z ∈ (Z : Set Plane), ⋃ w ∈ (Z : Set Plane),
    range fun t : ℝ => z + t • (w - z)
  have hB : volume B = 0 :=
    (measure_biUnion_null_iff Z.countable_toSet).2 fun z _ =>
      (measure_biUnion_null_iff Z.countable_toSet).2 fun w _ => rg_line_null z w
  have hDopen : IsOpen openUnitDisk := isOpen_lt (by fun_prop) continuous_const
  have hDpos : volume openUnitDisk ≠ 0 :=
    (hDopen.measure_pos volume ⟨0, show (0 : Plane) 0 ^ 2 + (0 : Plane) 1 ^ 2 < 1 by simp⟩).ne'
  obtain ⟨c, hcD, hcB⟩ : (openUnitDisk \ B).Nonempty :=
    nonempty_of_measure_ne_zero (by rwa [measure_diff_null hB])
  have hline : ∀ z ∈ Z, ∀ w ∈ Z, ∀ t : ℝ, c ≠ z + t • (w - z) := by
    intro z hz w hw t h
    exact hcB (mem_iUnion₂.2 ⟨z, hz, mem_iUnion₂.2 ⟨w, hw, t, h.symm⟩⟩)
  have hcz : ∀ z ∈ Z, c ≠ z := fun z hz h => hline z hz z hz 0 (by simp [h])
  choose! lam sp hpos hlt heq huniq using fun z (hz : z ∈ Z) => rg_ray hcD (hZ z hz) (hcz z hz)
  refine ⟨c, hcD, lam, sp, fun z hz => ⟨hpos z hz, hlt z hz, heq z hz, huniq z hz, ?_⟩⟩
  intro w hw hwz n hn
  have hq : circlePoint (sp w) = circlePoint (sp z) := by rw [hn, rg_cp_int]
  have hz' := heq z hz
  have hw' := heq w hw
  rw [hq] at hw'
  set q := circlePoint (sp z)
  have hl : lam z ≠ lam w := by
    intro h; apply hwz; rw [hw', hz', h]
  apply hline z hz w hw (lam z / (lam z - lam w))
  have hne : lam z - lam w ≠ 0 := sub_ne_zero.2 hl
  have key : lam z / (lam z - lam w) * (lam w - lam z) = -lam z := by field_simp; ring
  set t := lam z / (lam z - lam w)
  have hz0 := congrFun hz' 0
  have hz1 := congrFun hz' 1
  have hw0 := congrFun hw' 0
  have hw1 := congrFun hw' 1
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hz0 hz1 hw0 hw1
  apply rg_plane_ext
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linear_combination (t - 1) * hz0 - t * hw0 - (q 0 - c 0) * key
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linear_combination (t - 1) * hz1 - t * hw1 - (q 1 - c 1) * key

end HryniewiczCriterion

open HryniewiczCriterion

theorem solution (Z : Finset Plane) (hZ : ∀ z ∈ Z, z ∈ openUnitDisk) :
    ∃ c : Plane, c ∈ openUnitDisk ∧ ∃ lam sp : Plane → ℝ, ∀ z ∈ Z,
      0 < lam z ∧ lam z < 1 ∧ z = c + lam z • (circlePoint (sp z) - c) ∧
      (∀ μ s : ℝ, 0 ≤ μ → c + μ • (circlePoint s - c) = z → μ = lam z ∧ ∃ n : ℤ, s = sp z + n) ∧
      (∀ w ∈ Z, w ≠ z → ∀ n : ℤ, sp w ≠ sp z + n) :=
  HryniewiczCriterion.exists_strip_center' Z hZ
