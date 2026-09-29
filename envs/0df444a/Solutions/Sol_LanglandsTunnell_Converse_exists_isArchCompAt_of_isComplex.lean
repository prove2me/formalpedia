-- Prove2me | solution 1 for LanglandsTunnell.Converse.exists_isArchCompAt_of_isComplex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/15c95084-dc35-59be-a30c-abec18c8e773

import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_exists_isArchCompAt_of_isComplex

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal

open LanglandsTunnell.Converse

section

open Complex

section OneParam

variable {φ : ℝ → ℂˣ} (hφ : Continuous fun t => ((φ t : ℂˣ) : ℂ))
  (hadd : ∀ s t, φ (s + t) = φ s * φ t)
include hadd

private theorem aux_map_zero_eq_one : φ 0 = 1 := by
  have h : φ 0 * φ 0 = φ 0 * 1 := by rw [mul_one, ← hadd, add_zero]
  exact mul_left_cancel h

include hφ

private theorem aux_exists_norm_eq_exp : ∃ a : ℝ, ∀ t, ‖((φ t : ℂˣ) : ℂ)‖ = Real.exp (a * t) := by
  have hpos : ∀ t, 0 < ‖((φ t : ℂˣ) : ℂ)‖ := fun t => norm_pos_iff.mpr (φ t).ne_zero
  have h0 : φ 0 = 1 := aux_map_zero_eq_one hadd
  let L : ℝ →+ ℝ :=
    { toFun := fun t => Real.log ‖((φ t : ℂˣ) : ℂ)‖
      map_zero' := by simp only [h0, Units.val_one, norm_one, Real.log_one]
      map_add' := fun s t => by
        simp only [hadd, Units.val_mul, norm_mul]
        rw [Real.log_mul (hpos s).ne' (hpos t).ne'] }
  have hLt : ∀ t, L t = Real.log ‖((φ t : ℂˣ) : ℂ)‖ := fun t => rfl
  have hL : Continuous L := by
    show Continuous fun t => Real.log ‖((φ t : ℂˣ) : ℂ)‖
    exact (continuous_norm.comp hφ).log fun t => (hpos t).ne'
  have hlin : ∀ t, L t = t * L 1 := fun t => by
    have h := map_smul (L.toRealLinearMap hL) t (1 : ℝ)
    rw [AddMonoidHom.coe_toRealLinearMap] at h
    simpa only [smul_eq_mul, mul_one] using h
  refine ⟨L 1, fun t => ?_⟩
  rw [← Real.exp_log (hpos t), ← hLt, hlin t, mul_comm]

private theorem aux_exists_div_norm_eq_exp :
    ∃ b : ℝ, ∀ t, ((φ t : ℂˣ) : ℂ) / (‖((φ t : ℂˣ) : ℂ)‖ : ℂ) = exp ((b * t : ℝ) * I) := by
  have hne : ∀ t, ((φ t : ℂˣ) : ℂ) ≠ 0 := fun t => (φ t).ne_zero
  have hpos : ∀ t, 0 < ‖((φ t : ℂˣ) : ℂ)‖ := fun t => norm_pos_iff.mpr (hne t)
  have hnC : ∀ t, ((‖((φ t : ℂˣ) : ℂ)‖ : ℝ) : ℂ) ≠ 0 := fun t => by
    exact_mod_cast (hpos t).ne'
  have h0 : φ 0 = 1 := aux_map_zero_eq_one hadd

  have hmem : ∀ t, ((φ t : ℂˣ) : ℂ) / (‖((φ t : ℂˣ) : ℂ)‖ : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := fun t => by
    rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, norm_norm, div_self (hpos t).ne']
  let ψ : ℝ → Circle := fun t => ⟨((φ t : ℂˣ) : ℂ) / (‖((φ t : ℂˣ) : ℂ)‖ : ℂ), hmem t⟩
  have hψv : ∀ t, ((ψ t : Circle) : ℂ) = ((φ t : ℂˣ) : ℂ) / (‖((φ t : ℂˣ) : ℂ)‖ : ℂ) := fun t => rfl
  have hψc : Continuous ψ := by
    refine Continuous.subtype_mk ?_ _
    exact hφ.div (continuous_ofReal.comp (continuous_norm.comp hφ)) hnC
  have hψ0 : ψ 0 = 1 := by
    apply Circle.ext
    rw [hψv, h0, Units.val_one, norm_one, Complex.ofReal_one, div_one, Circle.coe_one]
  have hψmul : ∀ s t, ψ (s + t) = ψ s * ψ t := fun s t => by
    apply Circle.ext
    rw [Circle.coe_mul, hψv, hψv, hψv, hadd, Units.val_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm]
  let ψC : C(ℝ, Circle) := ⟨ψ, hψc⟩
  have hψC : ∀ t, ψC t = ψ t := fun t => rfl

  obtain ⟨F, ⟨hF0, hFl⟩, -⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts ψC 0 0 (by rw [hψC, hψ0, Circle.exp_zero])
  have hFt : ∀ x, Circle.exp (F x) = ψ x := fun x => by
    have := congrFun hFl x
    simp only [Function.comp_apply] at this
    exact this

  have hFadd : ∀ s t, F (s + t) = F s + F t := fun s t => by
    let fs : C(ℝ, Circle) := ⟨fun t => ψ (s + t), hψc.comp (continuous_const.add continuous_id)⟩
    have hfs : ∀ t, fs t = ψ (s + t) := fun t => rfl
    have hs : Circle.exp (F s) = fs 0 := by rw [hfs, add_zero, hFt]
    let G₁ : C(ℝ, ℝ) := ⟨fun t => F (s + t), F.continuous.comp (continuous_const.add continuous_id)⟩
    let G₂ : C(ℝ, ℝ) := ⟨fun t => F s + F t, continuous_const.add F.continuous⟩
    have hG₁ : ∀ t, G₁ t = F (s + t) := fun t => rfl
    have hG₂ : ∀ t, G₂ t = F s + F t := fun t => rfl
    have h1 : G₁ 0 = F s ∧ ⇑Circle.exp ∘ ⇑G₁ = ⇑fs := by
      refine ⟨by rw [hG₁, add_zero], funext fun t => ?_⟩
      simp only [Function.comp_apply]
      rw [hG₁, hfs, hFt]
    have h2 : G₂ 0 = F s ∧ ⇑Circle.exp ∘ ⇑G₂ = ⇑fs := by
      refine ⟨by rw [hG₂, hF0, add_zero], funext fun t => ?_⟩
      simp only [Function.comp_apply]
      rw [hG₂, hfs, Circle.exp_add, hFt, hFt, hψmul]
    have hG : G₁ = G₂ :=
      (Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts fs 0 (F s) hs).unique h1 h2
    have := DFunLike.congr_fun hG t
    rwa [hG₁, hG₂] at this

  let L : ℝ →+ ℝ := { toFun := F, map_zero' := hF0, map_add' := hFadd }
  have hLt : ∀ t, L t = F t := fun t => rfl
  have hlin : ∀ t, F t = t * F 1 := fun t => by
    have h := map_smul (L.toRealLinearMap F.continuous) t (1 : ℝ)
    rw [AddMonoidHom.coe_toRealLinearMap] at h
    simpa only [hLt, smul_eq_mul, mul_one] using h
  refine ⟨F 1, fun t => ?_⟩
  rw [← hψv, ← hFt t, Circle.coe_exp, hlin t, mul_comm t]

private theorem aux_exists_eq_exp_mul : ∃ c : ℂ, ∀ t : ℝ, ((φ t : ℂˣ) : ℂ) = exp (c * t) := by
  obtain ⟨a, ha⟩ := aux_exists_norm_eq_exp hφ hadd
  obtain ⟨b, hb⟩ := aux_exists_div_norm_eq_exp hφ hadd
  have hpos : ∀ t, 0 < ‖((φ t : ℂˣ) : ℂ)‖ := fun t => norm_pos_iff.mpr (φ t).ne_zero
  refine ⟨(a : ℂ) + (b : ℂ) * I, fun t => ?_⟩
  have hnC : ((‖((φ t : ℂˣ) : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hpos t).ne'
  have h1 : ((φ t : ℂˣ) : ℂ) = (‖((φ t : ℂˣ) : ℂ)‖ : ℂ) * (((φ t : ℂˣ) : ℂ) / (‖((φ t : ℂˣ) : ℂ)‖ : ℂ)) := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hnC]
  rw [h1, hb t, ha t, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end OneParam

private theorem aux_exists_circle_eq_zpow (χ : Circle →* ℂˣ) (hχ : Continuous fun z => ((χ z : ℂˣ) : ℂ)) :
    ∃ k : ℤ, ∀ z : Circle, ((χ z : ℂˣ) : ℂ) = (z : ℂ) ^ k := by
  let φ : ℝ → ℂˣ := fun t => χ (Circle.exp t)
  have hφv : ∀ t, φ t = χ (Circle.exp t) := fun t => rfl
  have hφ : Continuous fun t => ((φ t : ℂˣ) : ℂ) := hχ.comp Circle.exp.continuous
  have hadd : ∀ s t, φ (s + t) = φ s * φ t := fun s t => by
    rw [hφv, hφv, hφv, Circle.exp_add, map_mul]
  obtain ⟨c, hc⟩ := aux_exists_eq_exp_mul hφ hadd

  have h2π : exp (c * (2 * Real.pi : ℝ)) = 1 := by
    rw [← hc, hφv, Circle.exp_two_pi, map_one, Units.val_one]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h2π
  have hc' : c = n * I := by
    have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := by
      exact mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
    have : c * (2 * (Real.pi : ℂ)) = (n * I) * (2 * (Real.pi : ℂ)) := by
      rw [show (n : ℂ) * I * (2 * (Real.pi : ℂ)) = n * (2 * Real.pi * I) by ring, ← hn]
      push_cast
      ring
    exact mul_right_cancel₀ hπ this
  refine ⟨n, fun z => ?_⟩
  obtain ⟨θ, rfl⟩ := Circle.exp_surjective z
  rw [← hφv, hc, hc', Circle.coe_exp, ← Complex.exp_int_mul]
  congr 1
  ring

private theorem aux_exists_realUnits (χ : ℝˣ →* ℂˣ) (hχ : Continuous fun x => ((χ x : ℂˣ) : ℂ)) :
    ∃ u : ℂ, ∃ a : ZMod 2, ∀ x : ℝˣ, ((χ x : ℂˣ) : ℂ) =
      ((‖(x : ℝ)‖ : ℂ) ^ u) * (((x : ℝ) : ℂ) / (‖(x : ℝ)‖ : ℂ)) ^ ((a.val : ℕ) : ℤ) := by

  let e : ℝ → ℝˣ := fun t => Units.mk0 (Real.exp t) (Real.exp_pos t).ne'
  have hev : ∀ t, ((e t : ℝˣ) : ℝ) = Real.exp t := fun t => rfl
  have hec : Continuous e := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · show Continuous fun t => ((e t : ℝˣ) : ℝ)
      simp only [hev]
      exact Real.continuous_exp
    · show Continuous fun t => (((e t)⁻¹ : ℝˣ) : ℝ)
      simp only [Units.val_inv_eq_inv_val, hev]
      exact Real.continuous_exp.inv₀ fun t => (Real.exp_pos t).ne'
  let φ : ℝ → ℂˣ := fun t => χ (e t)
  have hφv : ∀ t, φ t = χ (e t) := fun t => rfl
  have hφ : Continuous fun t => ((φ t : ℂˣ) : ℂ) := hχ.comp hec
  have headd : ∀ s t, e (s + t) = e s * e t := fun s t =>
    Units.ext (by rw [Units.val_mul, hev, hev, hev, Real.exp_add])
  have hadd : ∀ s t, φ (s + t) = φ s * φ t := fun s t => by
    rw [hφv, hφv, hφv, headd, map_mul]
  obtain ⟨c, hc⟩ := aux_exists_eq_exp_mul hφ hadd
  have hposval : ∀ (r : ℝ) (hr : 0 < r),
      ((χ (Units.mk0 r hr.ne') : ℂˣ) : ℂ) = (r : ℂ) ^ c := fun r hr => by
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hre : Units.mk0 r hr.ne' = e (Real.log r) :=
      Units.ext (by rw [Units.val_mk0, hev, Real.exp_log hr])
    rw [hre, ← hφv, hc, cpow_def_of_ne_zero hr0, ← ofReal_log hr.le, mul_comm]

  have hsq : ((χ (-1) : ℂˣ) : ℂ) * ((χ (-1) : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, ← map_mul, neg_one_mul, neg_neg, map_one, Units.val_one]
  have hsign : ∃ a : ZMod 2, ((χ (-1) : ℂˣ) : ℂ) = (-1 : ℂ) ^ ((a.val : ℕ) : ℤ) := by
    rcases mul_self_eq_one_iff.mp hsq with h | h
    · exact ⟨0, by rw [h, show (0 : ZMod 2).val = 0 from rfl, Nat.cast_zero, zpow_zero]⟩
    · exact ⟨1, by rw [h, show (1 : ZMod 2).val = 1 from rfl, Nat.cast_one, zpow_one]⟩
  obtain ⟨a, ha⟩ := hsign
  refine ⟨c, a, fun x => ?_⟩
  have hx0 : (x : ℝ) ≠ 0 := x.ne_zero
  have hxC : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx0
  have hn : 0 < ‖(x : ℝ)‖ := norm_pos_iff.mpr hx0
  rcases lt_or_gt_of_ne hx0 with hlt | hgt
  · have hxe : x = -1 * Units.mk0 ‖(x : ℝ)‖ hn.ne' := Units.ext (by
      rw [Units.val_mul, Units.val_neg, Units.val_one, Units.val_mk0, Real.norm_eq_abs,
        abs_of_neg hlt]
      ring)
    have hq : ((x : ℝ) : ℂ) / (‖(x : ℝ)‖ : ℂ) = -1 := by
      rw [Real.norm_eq_abs, abs_of_neg hlt, ofReal_neg, div_neg, div_self hxC]
    rw [hq, ← ha]
    conv_lhs => rw [hxe]
    rw [map_mul, Units.val_mul, hposval _ hn, mul_comm]
  · have hxe : x = Units.mk0 ‖(x : ℝ)‖ hn.ne' :=
      Units.ext (by rw [Units.val_mk0, Real.norm_eq_abs, abs_of_pos hgt])
    have hq : ((x : ℝ) : ℂ) / (‖(x : ℝ)‖ : ℂ) = 1 := by
      rw [Real.norm_eq_abs, abs_of_pos hgt, div_self hxC]
    rw [hq, one_zpow, mul_one]
    conv_lhs => rw [hxe]
    exact hposval _ hn

private theorem aux_exists_complexUnits (χ : ℂˣ →* ℂˣ) (hχ : Continuous fun z => ((χ z : ℂˣ) : ℂ)) :
    ∃ u : ℂ, ∃ k : ℤ, ∀ z : ℂˣ, ((χ z : ℂˣ) : ℂ) =
      ((‖(z : ℂ)‖ : ℂ) ^ ((2 : ℂ) * u)) * ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ k := by

  have hexp0 : ∀ t, ((Real.exp t : ℝ) : ℂ) ≠ 0 := fun t => by exact_mod_cast (Real.exp_pos t).ne'
  let e : ℝ → ℂˣ := fun t => Units.mk0 ((Real.exp t : ℝ) : ℂ) (hexp0 t)
  have hev : ∀ t, ((e t : ℂˣ) : ℂ) = ((Real.exp t : ℝ) : ℂ) := fun t => rfl
  have hec : Continuous e := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · show Continuous fun t => ((e t : ℂˣ) : ℂ)
      simp only [hev]
      exact continuous_ofReal.comp Real.continuous_exp
    · show Continuous fun t => (((e t)⁻¹ : ℂˣ) : ℂ)
      simp only [Units.val_inv_eq_inv_val, hev]
      exact (continuous_ofReal.comp Real.continuous_exp).inv₀ hexp0
  let φ : ℝ → ℂˣ := fun t => χ (e t)
  have hφv : ∀ t, φ t = χ (e t) := fun t => rfl
  have hφ : Continuous fun t => ((φ t : ℂˣ) : ℂ) := hχ.comp hec
  have headd : ∀ s t, e (s + t) = e s * e t := fun s t =>
    Units.ext (by rw [Units.val_mul, hev, hev, hev, Real.exp_add, ofReal_mul])
  have hadd : ∀ s t, φ (s + t) = φ s * φ t := fun s t => by
    rw [hφv, hφv, hφv, headd, map_mul]
  obtain ⟨c, hc⟩ := aux_exists_eq_exp_mul hφ hadd
  have hposval : ∀ (r : ℝ) (hr : 0 < r) (hr' : (r : ℂ) ≠ 0),
      ((χ (Units.mk0 (r : ℂ) hr') : ℂˣ) : ℂ) = (r : ℂ) ^ c := fun r hr hr' => by
    have hre : Units.mk0 (r : ℂ) hr' = e (Real.log r) :=
      Units.ext (by rw [Units.val_mk0, hev, Real.exp_log hr])
    rw [hre, ← hφv, hc, cpow_def_of_ne_zero hr', ← ofReal_log hr.le, mul_comm]

  let χc : Circle →* ℂˣ := χ.comp Circle.toUnits
  have hχcv : ∀ ζ : Circle, χc ζ = χ (Circle.toUnits ζ) := fun ζ => rfl
  have htu : Continuous (Circle.toUnits : Circle → ℂˣ) := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · show Continuous fun ζ : Circle => ((Circle.toUnits ζ : ℂˣ) : ℂ)
      simp only [Circle.toUnits_apply, Units.val_mk0]
      exact continuous_subtype_val
    · show Continuous fun ζ : Circle => (((Circle.toUnits ζ)⁻¹ : ℂˣ) : ℂ)
      simp only [Units.val_inv_eq_inv_val, Circle.toUnits_apply, Units.val_mk0]
      exact continuous_subtype_val.inv₀ fun ζ => Circle.coe_ne_zero ζ
  have hχc : Continuous fun ζ => ((χc ζ : ℂˣ) : ℂ) := hχ.comp htu
  obtain ⟨k, hk⟩ := aux_exists_circle_eq_zpow χc hχc
  refine ⟨c / 2, k, fun z => ?_⟩
  have hz0 : (z : ℂ) ≠ 0 := z.ne_zero
  have hn : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr hz0
  have hnC : ((‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hmem : (z : ℂ) / (‖(z : ℂ)‖ : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, norm_norm, div_self hn.ne']
  let ζ : Circle := ⟨(z : ℂ) / (‖(z : ℂ)‖ : ℂ), hmem⟩
  have hζ : ((ζ : Circle) : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) := rfl
  have hze : z = Units.mk0 ((‖(z : ℂ)‖ : ℝ) : ℂ) hnC * Circle.toUnits ζ := Units.ext (by
    rw [Units.val_mul, Units.val_mk0, Circle.toUnits_apply, Units.val_mk0, hζ, ← mul_div_assoc,
      mul_div_cancel_left₀ _ hnC])
  have h2 : (2 : ℂ) * (c / 2) = c := by rw [two_mul, add_halves]
  rw [h2, ← hζ, ← hk ζ, hχcv]
  conv_lhs => rw [hze]
  rw [map_mul, Units.val_mul, hposval _ hn hnC]

end

section

open IsDedekindDomain NumberField NumberField.TateGlobal Complex

variable (K : Type) [Field K] [NumberField K]

private theorem aux_continuous_archUnitHom (w : InfinitePlace K) :
    Continuous (archUnitHom w : (w.Completion)ˣ → (AdeleRing (𝓞 K) K)ˣ) := by
  classical
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun x : (w.Completion)ˣ =>
      ((Function.update (1 : InfiniteAdeleRing K) w (x : w.Completion),
        (1 : FiniteAdeleRing (𝓞 K) K)) : AdeleRing (𝓞 K) K)
    exact (continuous_const.update w Units.continuous_val).prodMk continuous_const
  · show Continuous fun x : (w.Completion)ˣ =>
      ((Function.update (1 : InfiniteAdeleRing K) w ((x⁻¹ : (w.Completion)ˣ) : w.Completion),
        (1 : FiniteAdeleRing (𝓞 K) K)) : AdeleRing (𝓞 K) K)
    exact (continuous_const.update w Units.continuous_coe_inv).prodMk continuous_const

private theorem aux_continuous_archLocalChar (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : Continuous μ)
    (w : InfinitePlace K) : Continuous fun x : (w.Completion)ˣ => ((archLocalChar μ w x : ℂˣ) : ℂ) :=
  (Units.continuous_val.comp (hμ.comp (aux_continuous_archUnitHom K w))).congr fun _ => rfl

end

open Complex in

theorem solution (K : Type) [Field K] [NumberField K]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : Continuous μ) (w : InfinitePlace K) (hw : w.IsComplex) :
    ∃ u : ℂ, ∃ k : ℤ, IsArchCompAt K μ w u k := by
  let e : w.Completion ≃+* ℂ := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  have he : ∀ x, e x = InfinitePlace.Completion.extensionEmbedding w x :=
    InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply hw
  have hiso : Isometry (InfinitePlace.Completion.extensionEmbedding w) :=
    InfinitePlace.Completion.isometry_extensionEmbedding w
  have hsymm : Continuous e.symm := by
    refine (Isometry.of_dist_eq fun a b => ?_).continuous
    rw [← hiso.dist_eq (e.symm a) (e.symm b), ← he, ← he, e.apply_symm_apply, e.apply_symm_apply]
  let χ : ℂˣ →* ℂˣ := (archLocalChar μ w).comp (Units.map e.symm.toRingHom.toMonoidHom)
  have hχv : ∀ y : ℂˣ, ((χ y : ℂˣ) : ℂ) =
      ((archLocalChar μ w (Units.map e.symm.toRingHom.toMonoidHom y) : ℂˣ) : ℂ) := fun y => rfl
  have hmapc : Continuous (Units.map e.symm.toRingHom.toMonoidHom : ℂˣ → (w.Completion)ˣ) :=
    Continuous.units_map _ hsymm
  have hχ : Continuous fun y : ℂˣ => ((χ y : ℂˣ) : ℂ) :=
    (aux_continuous_archLocalChar K μ hμ w).comp hmapc
  obtain ⟨u, k, huk⟩ := aux_exists_complexUnits χ hχ
  refine ⟨u, k, ?_⟩
  intro x
  have hx : Units.map e.symm.toRingHom.toMonoidHom (Units.map e.toRingHom.toMonoidHom x) = x :=
    Units.ext (e.symm_apply_apply _)
  have hnorm : ‖((Units.map e.toRingHom.toMonoidHom x : ℂˣ) : ℂ)‖ = ‖(x : w.Completion)‖ := by
    show ‖e (x : w.Completion)‖ = ‖(x : w.Completion)‖
    rw [he]
    exact hiso.norm_map_of_map_zero (map_zero _) _
  have hemb : ((Units.map e.toRingHom.toMonoidHom x : ℂˣ) : ℂ) =
      InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) := by
    show e (x : w.Completion) = _
    rw [he]
  have hmult : (w.mult : ℂ) * u = 2 * u := by
    rw [show w.mult = 2 from InfinitePlace.mult_isComplex ⟨w, hw⟩, Nat.cast_ofNat]
  conv_lhs => rw [← hx, ← hχv, huk]
  rw [hnorm, hemb, hmult]

end S_LanglandsTunnell_Converse_exists_isArchCompAt_of_isComplex
end P2MW
export P2MW.S_LanglandsTunnell_Converse_exists_isArchCompAt_of_isComplex (solution)
