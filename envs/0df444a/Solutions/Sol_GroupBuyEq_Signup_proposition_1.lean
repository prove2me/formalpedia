-- Prove2me | solution 1 for GroupBuyEq.Signup.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T17:03:49.414152+00:00
-- url     : https://prove2.me/submissions/7e89b8cc-2203-4d1b-b3e7-6d6c02c98d8f

import Mathlib
import Definitions.Def_GroupBuyEq_Signup_Model

set_option autoImplicit false

open MeasureTheory Set

namespace GBQ

noncomputable def Phi (lam T : ℝ) (h g : ℝ → ℝ) (t : ℝ) : ℝ :=
  lam * ∫ s in t..T, Real.exp (-(lam * ∫ v in t..s, h v)) * h s * g s

theorem ii_of_bdd {u : ℝ → ℝ} {T C : ℝ} (hu : Measurable u) (hb : ∀ x ∈ Icc 0 T, |u x| ≤ C)
    {a b : ℝ} (ha : a ∈ Icc 0 T) (hb' : b ∈ Icc 0 T) : IntervalIntegrable u volume a b := by
  refine (intervalIntegrable_const (c := C)).mono_fun hu.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_uIoc).2 (Filter.Eventually.of_forall fun x hx => ?_)
  have hx' : x ∈ Icc 0 T := uIcc_subset_Icc ha hb' (uIoc_subset_uIcc hx)
  simp only [Real.norm_eq_abs]
  exact (hb x hx').trans (le_abs_self C)

theorem ii_glob {u : ℝ → ℝ} {C : ℝ} (hu : Measurable u) (hb : ∀ x, |u x| ≤ C) (a b : ℝ) :
    IntervalIntegrable u volume a b := by
  refine (intervalIntegrable_const (c := C)).mono_fun hu.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  simp only [Real.norm_eq_abs]
  exact (hb x).trans (le_abs_self C)

theorem ac_exp_prim (w : ℝ → ℝ) (C : NNReal) (hw : Measurable w) (hb : ∀ x, |w x| ≤ C) {T : ℝ}
    (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (fun t => Real.exp (∫ s in (0:ℝ)..t, w s)) 0 T := by
  have hii := ii_glob hw hb
  have hF : LipschitzWith C (fun t => ∫ s in (0:ℝ)..t, w s) := LipschitzWith.of_dist_le_mul
    fun x y => by
      simp only [Real.dist_eq]
      rw [intervalIntegral.integral_interval_sub_left (hii 0 x) (hii 0 y)]
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := y) (b := x) (C := C)
        (f := w) (fun z _ => by simpa [Real.norm_eq_abs] using hb z)
      simpa [Real.norm_eq_abs] using this
  have hmaps : MapsTo (fun t => ∫ s in (0:ℝ)..t, w s) (uIcc 0 T) (Icc (-(C * T)) (C * T)) := by
    intro x hx
    rw [uIcc_of_le hT] at hx
    have h1 := hF.dist_le_mul x 0
    simp only [Real.dist_eq, intervalIntegral.integral_same, sub_zero] at h1
    rw [abs_of_nonneg hx.1] at h1
    have h2 : (C : ℝ) * x ≤ C * T := mul_le_mul_of_nonneg_left hx.2 C.2
    exact abs_le.1 (h1.trans h2)
  have hexp : LipschitzOnWith (Real.toNNReal (Real.exp (C * T))) Real.exp
      (Icc (-(C * T)) (C * T)) :=
    (convex_Icc _ _).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) (fun x hx => by
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x),
          Real.coe_toNNReal _ (Real.exp_pos _).le]
        exact Real.exp_le_exp.2 hx.2)
  exact (hexp.comp hF.lipschitzOnWith hmaps).absolutelyContinuousOnInterval

theorem volterra_shift (lam T t : ℝ) (Q : ℝ → ℝ) :
    ∫ x in (0:ℝ)..(T - t), Q (t + x) * lam * Real.exp (-(lam * x)) =
      Real.exp (lam * t) * ∫ s in t..T, Q s * lam * Real.exp (-(lam * s)) := by
  have := intervalIntegral.integral_comp_add_left
    (fun s => Q s * lam * Real.exp (-(lam * (s - t)))) t (a := 0) (b := T - t)
  simp only [add_sub_cancel_left, add_zero, add_sub_cancel] at this
  rw [this, ← intervalIntegral.integral_const_mul]
  congr 1; funext s
  rw [show -(lam * (s - t)) = lam * t + -(lam * s) by ring, Real.exp_add]; ring

theorem phi_conv (lam T : ℝ) (h g : ℝ → ℝ) (hh : ∀ a b, IntervalIntegrable h volume a b)
    (t : ℝ) :
    Phi lam T h g t = lam * Real.exp (lam * ∫ v in (0:ℝ)..t, h v) *
      ∫ s in t..T, Real.exp (-(lam * ∫ v in (0:ℝ)..s, h v)) * h s * g s := by
  unfold Phi
  rw [mul_assoc]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [← intervalIntegral.integral_interval_sub_left (hh 0 s) (hh 0 t)]
  rw [show -(lam * ((∫ v in (0:ℝ)..s, h v) - ∫ v in (0:ℝ)..t, h v))
      = lam * (∫ v in (0:ℝ)..t, h v) + -(lam * ∫ v in (0:ℝ)..s, h v) by ring, Real.exp_add]
  ring

/-- Volterra form ⇒ explicit formula. -/
theorem char (lam T : ℝ) (hlam : 0 < lam) (hT : 0 ≤ T) (h g f : ℝ → ℝ)
    (hh : Measurable h) (h01 : ∀ x, 0 ≤ h x ∧ h x ≤ 1)
    (hg : Measurable g) (hgb : ∀ x ∈ Icc 0 T, |g x| ≤ 1)
    (hf : Measurable f) (hfb : ∀ x ∈ Icc 0 T, |f x| ≤ 1)
    (hV : ∀ t ∈ Icc 0 T, f t = ∫ x in (0:ℝ)..(T - t),
      (h (t + x) * g (t + x) + (1 - h (t + x)) * f (t + x)) * lam * Real.exp (-(lam * x))) :
    ∀ t ∈ Icc 0 T, f t = Phi lam T h g t := by
  have hhb : ∀ x, |h x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [(h01 x).1], (h01 x).2⟩
  have hhi : ∀ a b, IntervalIntegrable h volume a b := ii_glob hh hhb
  have hIc : Continuous (fun t => ∫ v in (0:ℝ)..t, h v) :=
    intervalIntegral.continuous_primitive hhi 0
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ → ℝ, Y = fun t => Real.exp (-(lam * ∫ v in (0:ℝ)..t, h v)) :=
    ⟨_, rfl⟩
  have hY' : ∀ s, Real.exp (-(lam * ∫ v in (0:ℝ)..s, h v)) = Y s := fun s => by rw [hYdef]
  have hYm : Measurable Y := by rw [hYdef]; exact (by fun_prop : Continuous _).measurable
  have hYb : ∀ x ∈ Icc 0 T, |Y x| ≤ 1 := by
    intro x hx
    rw [← hY', abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have := intervalIntegral.integral_nonneg (μ := volume) hx.1 (fun y _ => (h01 y).1)
    nlinarith
  obtain ⟨k, hkdef⟩ : ∃ k : ℝ → ℝ, k = fun s => Y s * h s * g s := ⟨_, rfl⟩
  have hkm : Measurable k := by rw [hkdef]; fun_prop
  have hkb : ∀ x ∈ Icc 0 T, |k x| ≤ 1 := by
    intro x hx
    rw [hkdef]; dsimp only; rw [abs_mul, abs_mul]
    have := hYb x hx; have := hhb x; have := hgb x hx
    calc |Y x| * |h x| * |g x| ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by ring
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ → ℝ,
      q = fun s => (h s * g s + (1 - h s) * f s) * lam * Real.exp (-(lam * s)) := ⟨_, rfl⟩
  have hqm : Measurable q := by rw [hqdef]; fun_prop
  have hqb : ∀ x ∈ Icc 0 T, |q x| ≤ lam := by
    intro x hx
    have e1 : |h x * g x + (1 - h x) * f x| ≤ 1 := by
      have := abs_le.1 (hgb x hx); have := abs_le.1 (hfb x hx); have := h01 x
      rw [abs_le]; constructor <;>
        nlinarith [mul_nonneg (h01 x).1 (by linarith : 0 ≤ 1 + g x),
          mul_nonneg (h01 x).1 (by linarith : 0 ≤ 1 - g x),
          mul_nonneg (by linarith : 0 ≤ 1 - h x) (by linarith : 0 ≤ 1 + f x),
          mul_nonneg (by linarith : 0 ≤ 1 - h x) (by linarith : 0 ≤ 1 - f x)]
    have e2 : Real.exp (-(lam * x)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hx.1])
    rw [hqdef]; dsimp only
    rw [abs_mul, abs_mul, abs_of_pos hlam, abs_of_pos (Real.exp_pos _)]
    calc |h x * g x + (1 - h x) * f x| * lam * Real.exp (-(lam * x)) ≤ 1 * lam * 1 := by
          gcongr
      _ = lam := by ring
  have m0 : (0:ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have mT : T ∈ Icc 0 T := ⟨hT, le_rfl⟩
  have hqi : IntervalIntegrable q volume 0 T := ii_of_bdd hqm hqb m0 mT
  have hki : IntervalIntegrable k volume 0 T := ii_of_bdd hkm hkb m0 mT
  have hwm : Measurable (fun s => lam * (1 - h s)) := by fun_prop
  have hwb : ∀ x, |(fun s => lam * (1 - h s)) x| ≤ (Real.toNNReal lam : ℝ) := by
    intro x; rw [Real.coe_toNNReal _ hlam.le, abs_le]; constructor <;> nlinarith [h01 x]
  have hXac := ac_exp_prim _ (Real.toNNReal lam) hwm hwb hT
  have hwi : IntervalIntegrable (fun s => lam * (1 - h s)) volume 0 T := ii_glob hwm hwb 0 T
  have hXY : ∀ x, Real.exp (∫ s in (0:ℝ)..x, lam * (1 - h s)) * Real.exp (-(lam * x)) = Y x := by
    intro x
    rw [← hY', ← Real.exp_add]; congr 1
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub intervalIntegrable_const (hhi 0 x)]
    simp; ring
  -- the Volterra relation in primitive form
  have hA : ∀ x ∈ Icc 0 T, -(∫ s in T..x, q s) = Real.exp (-(lam * x)) * f x := by
    intro x hx
    have hrel := hV x hx
    have hs := volterra_shift lam T x (fun s => h s * g s + (1 - h s) * f s)
    beta_reduce at hs
    rw [hs] at hrel
    rw [hrel, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul,
      intervalIntegral.integral_symm, neg_neg, hqdef]
  have hWac : AbsolutelyContinuousOnInterval (fun t => Real.exp (∫ s in (0:ℝ)..t, lam * (1 - h s))
      * (-∫ s in T..t, q s) + lam * ∫ s in T..t, k s) 0 T :=
    (hXac.fun_mul (hqi.absolutelyContinuousOnInterval_intervalIntegral right_mem_uIcc).neg).add
      ((hki.absolutelyContinuousOnInterval_intervalIntegral right_mem_uIcc).const_mul lam)
  have hder : ∀ᵐ x, x ∈ uIcc 0 T → HasDerivAt (fun t => Real.exp (∫ s in (0:ℝ)..t, lam * (1 - h s))
      * (-∫ s in T..t, q s) + lam * ∫ s in T..t, k s) 0 x := by
    filter_upwards [hqi.ae_hasDerivAt_integral, hki.ae_hasDerivAt_integral,
      hwi.ae_hasDerivAt_integral] with x h1 h2 h3 hx
    have dX := (h3 hx 0 left_mem_uIcc).exp
    have dA := (h1 hx T right_mem_uIcc).neg
    have dK := (h2 hx T right_mem_uIcc).const_mul lam
    have hx' : x ∈ Icc 0 T := by rwa [uIcc_of_le hT] at hx
    have hAx := hA x hx'
    have hXYx := hXY x
    have hqx : q x = (h x * g x + (1 - h x) * f x) * lam * Real.exp (-(lam * x)) := by
      rw [hqdef]
    have hkx : k x = Y x * h x * g x := by rw [hkdef]
    refine ((dX.mul dA).add dK).congr_deriv ?_
    beta_reduce
    simp only [Pi.neg_apply]
    rw [hqx, hkx]
    symm
    linear_combination (-(Real.exp (∫ s in (0:ℝ)..x, lam * (1 - h s)) * lam * (1 - h x))) * hAx
      + (lam * h x * g x) * hXYx
  obtain ⟨C, hC⟩ := hWac.const_of_ae_hasDerivAt_zero hder
  intro t ht
  have hCt := hC t (by rw [uIcc_of_le hT]; exact ht)
  have hCT := hC T right_mem_uIcc
  simp only [intervalIntegral.integral_same, neg_zero, mul_zero, add_zero] at hCT
  have hAt := hA t ht
  have hXYt := hXY t
  rw [phi_conv lam T h g hhi t]
  simp only [hY']
  have hk' : ∫ s in t..T, Y s * h s * g s = -∫ s in T..t, k s := by
    rw [intervalIntegral.integral_symm, hkdef]
  rw [hk']
  have hYI : Real.exp (lam * ∫ v in (0:ℝ)..t, h v) * Y t = 1 := by
    rw [← hY', ← Real.exp_add]; simp
  have hW := hCt.trans hCT.symm
  linear_combination (Real.exp (lam * ∫ v in (0:ℝ)..t, h v)) * hW
    - (Real.exp (lam * ∫ v in (0:ℝ)..t, h v)) * Real.exp (∫ s in (0:ℝ)..t, lam * (1 - h s)) * hAt
    - (Real.exp (lam * ∫ v in (0:ℝ)..t, h v)) * f t * hXYt - f t * hYI

/-- explicit formula ⇒ Volterra form. -/
theorem exist (lam T : ℝ) (hlam : 0 < lam) (hT : 0 ≤ T) (h g f : ℝ → ℝ)
    (hh : Measurable h) (h01 : ∀ x, 0 ≤ h x ∧ h x ≤ 1)
    (hg : Measurable g) (hgb : ∀ x ∈ Icc 0 T, |g x| ≤ 1)
    (hf : Measurable f) (hfb : ∀ x ∈ Icc 0 T, |f x| ≤ 1)
    (hfe : ∀ t ∈ Icc 0 T, f t = Phi lam T h g t) :
    ∀ t ∈ Icc 0 T, f t = ∫ x in (0:ℝ)..(T - t),
      (h (t + x) * g (t + x) + (1 - h (t + x)) * f (t + x)) * lam * Real.exp (-(lam * x)) := by
  have hhb : ∀ x, |h x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [(h01 x).1], (h01 x).2⟩
  have hhi : ∀ a b, IntervalIntegrable h volume a b := ii_glob hh hhb
  have hIc : Continuous (fun t => ∫ v in (0:ℝ)..t, h v) :=
    intervalIntegral.continuous_primitive hhi 0
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ → ℝ, Y = fun t => Real.exp (-(lam * ∫ v in (0:ℝ)..t, h v)) :=
    ⟨_, rfl⟩
  have hY' : ∀ s, Real.exp (-(lam * ∫ v in (0:ℝ)..s, h v)) = Y s := fun s => by rw [hYdef]
  have hYm : Measurable Y := by rw [hYdef]; exact (by fun_prop : Continuous _).measurable
  have hYb : ∀ x ∈ Icc 0 T, |Y x| ≤ 1 := by
    intro x hx
    rw [← hY', abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have := intervalIntegral.integral_nonneg (μ := volume) hx.1 (fun y _ => (h01 y).1)
    nlinarith
  obtain ⟨k, hkdef⟩ : ∃ k : ℝ → ℝ, k = fun s => Y s * h s * g s := ⟨_, rfl⟩
  have hkm : Measurable k := by rw [hkdef]; fun_prop
  have hkb : ∀ x ∈ Icc 0 T, |k x| ≤ 1 := by
    intro x hx
    rw [hkdef]; dsimp only; rw [abs_mul, abs_mul]
    have := hYb x hx; have := hhb x; have := hgb x hx
    calc |Y x| * |h x| * |g x| ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by ring
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ → ℝ,
      q = fun s => (h s * g s + (1 - h s) * f s) * lam * Real.exp (-(lam * s)) := ⟨_, rfl⟩
  have hqm : Measurable q := by rw [hqdef]; fun_prop
  have hqb : ∀ x ∈ Icc 0 T, |q x| ≤ lam := by
    intro x hx
    have e1 : |h x * g x + (1 - h x) * f x| ≤ 1 := by
      have := abs_le.1 (hgb x hx); have := abs_le.1 (hfb x hx); have := h01 x
      rw [abs_le]; constructor <;>
        nlinarith [mul_nonneg (h01 x).1 (by linarith : 0 ≤ 1 + g x),
          mul_nonneg (h01 x).1 (by linarith : 0 ≤ 1 - g x),
          mul_nonneg (by linarith : 0 ≤ 1 - h x) (by linarith : 0 ≤ 1 + f x),
          mul_nonneg (by linarith : 0 ≤ 1 - h x) (by linarith : 0 ≤ 1 - f x)]
    have e2 : Real.exp (-(lam * x)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hx.1])
    rw [hqdef]; dsimp only
    rw [abs_mul, abs_mul, abs_of_pos hlam, abs_of_pos (Real.exp_pos _)]
    calc |h x * g x + (1 - h x) * f x| * lam * Real.exp (-(lam * x)) ≤ 1 * lam * 1 := by
          gcongr
      _ = lam := by ring
  have m0 : (0:ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have mT : T ∈ Icc 0 T := ⟨hT, le_rfl⟩
  have hqi : IntervalIntegrable q volume 0 T := ii_of_bdd hqm hqb m0 mT
  have hki : IntervalIntegrable k volume 0 T := ii_of_bdd hkm hkb m0 mT
  have hwm : Measurable (fun s => lam * (h s - 1)) := by fun_prop
  have hwb : ∀ x, |(fun s => lam * (h s - 1)) x| ≤ (Real.toNNReal lam : ℝ) := by
    intro x; rw [Real.coe_toNNReal _ hlam.le, abs_le]; constructor <;> nlinarith [h01 x]
  have hZac := ac_exp_prim _ (Real.toNNReal lam) hwm hwb hT
  have hwi : IntervalIntegrable (fun s => lam * (h s - 1)) volume 0 T := ii_glob hwm hwb 0 T
  have hZY : ∀ x, Real.exp (∫ s in (0:ℝ)..x, lam * (h s - 1)) * Y x = Real.exp (-(lam * x)) := by
    intro x
    rw [← hY', ← Real.exp_add]; congr 1
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (hhi 0 x) intervalIntegrable_const]
    simp; ring
  have hZI : ∀ x, Real.exp (-(lam * x)) * Real.exp (lam * ∫ v in (0:ℝ)..x, h v)
      = Real.exp (∫ s in (0:ℝ)..x, lam * (h s - 1)) := by
    intro x
    rw [← Real.exp_add]; congr 1
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (hhi 0 x) intervalIntegrable_const]
    simp; ring
  have hr : ∀ x ∈ Icc 0 T, Real.exp (-(lam * x)) * f x
      = -lam * (Real.exp (∫ s in (0:ℝ)..x, lam * (h s - 1)) * ∫ s in T..x, k s) := by
    intro x hx
    rw [hfe x hx, phi_conv lam T h g hhi x]
    simp only [hY']
    have hk' : ∫ s in x..T, Y s * h s * g s = -∫ s in T..x, k s := by
      rw [intervalIntegral.integral_symm, hkdef]
    rw [hk', ← hZI x]; ring
  have hRac : AbsolutelyContinuousOnInterval (fun t => -lam * (Real.exp (∫ s in (0:ℝ)..t,
      lam * (h s - 1)) * ∫ s in T..t, k s) + ∫ s in T..t, q s) 0 T :=
    ((hZac.fun_mul (hki.absolutelyContinuousOnInterval_intervalIntegral right_mem_uIcc)).const_mul
      (-lam)).add (hqi.absolutelyContinuousOnInterval_intervalIntegral right_mem_uIcc)
  have hder : ∀ᵐ x, x ∈ uIcc 0 T → HasDerivAt (fun t => -lam * (Real.exp (∫ s in (0:ℝ)..t,
      lam * (h s - 1)) * ∫ s in T..t, k s) + ∫ s in T..t, q s) 0 x := by
    filter_upwards [hqi.ae_hasDerivAt_integral, hki.ae_hasDerivAt_integral,
      hwi.ae_hasDerivAt_integral] with x h1 h2 h3 hx
    have dZ := (h3 hx 0 left_mem_uIcc).exp
    have dK := h2 hx T right_mem_uIcc
    have dQ := h1 hx T right_mem_uIcc
    have hx' : x ∈ Icc 0 T := by rwa [uIcc_of_le hT] at hx
    have hrx := hr x hx'
    have hZYx := hZY x
    have hqx : q x = (h x * g x + (1 - h x) * f x) * lam * Real.exp (-(lam * x)) := by
      rw [hqdef]
    have hkx : k x = Y x * h x * g x := by rw [hkdef]
    refine (((dZ.mul dK).const_mul (-lam)).add dQ).congr_deriv ?_
    beta_reduce
    rw [hqx, hkx]
    linear_combination (lam * (1 - h x)) * hrx - (lam * h x * g x) * hZYx
  obtain ⟨C, hC⟩ := hRac.const_of_ae_hasDerivAt_zero hder
  intro t ht
  have hCt := hC t (by rw [uIcc_of_le hT]; exact ht)
  have hCT := hC T right_mem_uIcc
  beta_reduce at hCt hCT
  simp only [intervalIntegral.integral_same, mul_zero, add_zero] at hCT
  have hRt := hCt.trans hCT.symm
  have hrt := hr t ht
  have hs := volterra_shift lam T t (fun s => h s * g s + (1 - h s) * f s)
  beta_reduce at hs
  rw [hs]
  have hq' : ∫ s in t..T, (h s * g s + (1 - h s) * f s) * lam * Real.exp (-(lam * s))
      = -∫ s in T..t, q s := by
    rw [intervalIntegral.integral_symm, hqdef]
  rw [hq']
  have hee : Real.exp (lam * t) * Real.exp (-(lam * t)) = 1 := by rw [← Real.exp_add]; simp
  linear_combination (Real.exp (lam * t)) * hRt + (Real.exp (lam * t)) * hrt - f t * hee

/-- the explicit formula stays in `[0,1]`. -/
theorem phi_bound (lam T : ℝ) (hlam : 0 < lam) (hT : 0 ≤ T) (h g : ℝ → ℝ)
    (hh : Measurable h) (h01 : ∀ x, 0 ≤ h x ∧ h x ≤ 1)
    (hg : Measurable g) (hg01 : ∀ x ∈ Icc 0 T, 0 ≤ g x ∧ g x ≤ 1) :
    ∀ t ∈ Icc 0 T, 0 ≤ Phi lam T h g t ∧ Phi lam T h g t ≤ 1 := by
  have hgb : ∀ x ∈ Icc 0 T, |g x| ≤ 1 := fun x hx =>
    abs_le.2 ⟨by linarith [(hg01 x hx).1], (hg01 x hx).2⟩
  have hhb : ∀ x, |h x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [(h01 x).1], (h01 x).2⟩
  have hhi : ∀ a b, IntervalIntegrable h volume a b := ii_glob hh hhb
  have hIc : Continuous (fun t => ∫ v in (0:ℝ)..t, h v) :=
    intervalIntegral.continuous_primitive hhi 0
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ → ℝ, Y = fun t => Real.exp (-(lam * ∫ v in (0:ℝ)..t, h v)) :=
    ⟨_, rfl⟩
  have hY' : ∀ s, Real.exp (-(lam * ∫ v in (0:ℝ)..s, h v)) = Y s := fun s => by rw [hYdef]
  have hYm : Measurable Y := by rw [hYdef]; exact (by fun_prop : Continuous _).measurable
  have hYpos : ∀ x, 0 < Y x := fun x => by rw [← hY']; exact Real.exp_pos _
  have hYb : ∀ x ∈ Icc 0 T, |Y x| ≤ 1 := by
    intro x hx
    rw [← hY', abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have := intervalIntegral.integral_nonneg (μ := volume) hx.1 (fun y _ => (h01 y).1)
    nlinarith
  obtain ⟨k, hkdef⟩ : ∃ k : ℝ → ℝ, k = fun s => Y s * h s * g s := ⟨_, rfl⟩
  have hkm : Measurable k := by rw [hkdef]; fun_prop
  have hkb : ∀ x ∈ Icc 0 T, |k x| ≤ 1 := by
    intro x hx
    rw [hkdef]; dsimp only; rw [abs_mul, abs_mul]
    have := hYb x hx; have := hhb x; have := hgb x hx
    calc |Y x| * |h x| * |g x| ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by ring
  obtain ⟨j, hjdef⟩ : ∃ j : ℝ → ℝ, j = fun s => Y s * h s := ⟨_, rfl⟩
  have hjm : Measurable j := by rw [hjdef]; fun_prop
  have hjb : ∀ x ∈ Icc 0 T, |j x| ≤ 1 := by
    intro x hx
    rw [hjdef]; dsimp only; rw [abs_mul]
    have := hYb x hx; have := hhb x
    calc |Y x| * |h x| ≤ 1 * 1 := by gcongr
      _ = 1 := by ring
  have m0 : (0:ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have mT : T ∈ Icc 0 T := ⟨hT, le_rfl⟩
  have hji : IntervalIntegrable j volume 0 T := ii_of_bdd hjm hjb m0 mT
  have hwm : Measurable (fun s => -lam * h s) := by fun_prop
  have hwb : ∀ x, |(fun s => -lam * h s) x| ≤ (Real.toNNReal lam : ℝ) := by
    intro x; rw [Real.coe_toNNReal _ hlam.le, abs_le]; constructor <;> nlinarith [h01 x]
  have hYac0 := ac_exp_prim _ (Real.toNNReal lam) hwm hwb hT
  have hYe : ∀ x, Real.exp (∫ s in (0:ℝ)..x, -lam * h s) = Y x := by
    intro x; rw [← hY', intervalIntegral.integral_const_mul, neg_mul]
  have hwi : IntervalIntegrable (fun s => -lam * h s) volume 0 T := ii_glob hwm hwb 0 T
  have hUac : AbsolutelyContinuousOnInterval (fun t => Real.exp (∫ s in (0:ℝ)..t, -lam * h s)
      + lam * ∫ s in T..t, j s) 0 T :=
    hYac0.add ((hji.absolutelyContinuousOnInterval_intervalIntegral right_mem_uIcc).const_mul lam)
  have hder : ∀ᵐ x, x ∈ uIcc 0 T → HasDerivAt (fun t => Real.exp (∫ s in (0:ℝ)..t, -lam * h s)
      + lam * ∫ s in T..t, j s) 0 x := by
    filter_upwards [hji.ae_hasDerivAt_integral, hwi.ae_hasDerivAt_integral] with x h1 h2 hx
    have dY := (h2 hx 0 left_mem_uIcc).exp
    have dJ := (h1 hx T right_mem_uIcc).const_mul lam
    have hjx : j x = Y x * h x := by rw [hjdef]
    refine (dY.add dJ).congr_deriv ?_
    beta_reduce
    rw [hjx, hYe x]
    ring
  obtain ⟨C, hC⟩ := hUac.const_of_ae_hasDerivAt_zero hder
  intro t ht
  have hCt := hC t (by rw [uIcc_of_le hT]; exact ht)
  have hCT := hC T right_mem_uIcc
  beta_reduce at hCt hCT
  simp only [intervalIntegral.integral_same, mul_zero, add_zero] at hCT
  rw [hYe] at hCt hCT
  rw [phi_conv lam T h g hhi t]
  simp only [hY']
  have hYI : Real.exp (lam * ∫ v in (0:ℝ)..t, h v) * Y t = 1 := by
    rw [← hY', ← Real.exp_add]; simp
  have hEpos : 0 < Real.exp (lam * ∫ v in (0:ℝ)..t, h v) := Real.exp_pos _
  have hint_nonneg : 0 ≤ ∫ s in t..T, Y s * h s * g s :=
    intervalIntegral.integral_nonneg ht.2 (fun s hs =>
      mul_nonneg (mul_nonneg (hYpos s).le (h01 s).1) (hg01 s ⟨ht.1.trans hs.1, hs.2⟩).1)
  have hle : ∫ s in t..T, Y s * h s * g s ≤ ∫ s in t..T, j s := by
    apply intervalIntegral.integral_mono_on ht.2
    · have := ii_of_bdd hkm hkb ht mT
      rw [hkdef] at this; exact this
    · exact ii_of_bdd hjm hjb ht mT
    · intro s hs; rw [hjdef]; dsimp only
      have := hg01 s ⟨ht.1.trans hs.1, hs.2⟩
      nlinarith [mul_nonneg (hYpos s).le (h01 s).1]
  have key : lam * Real.exp (lam * ∫ v in (0:ℝ)..t, h v) * ∫ s in t..T, j s
      = 1 - Real.exp (lam * ∫ v in (0:ℝ)..t, h v) * Y T := by
    rw [intervalIntegral.integral_symm T t]
    linear_combination (-(Real.exp (lam * ∫ v in (0:ℝ)..t, h v))) * hCt
      + (Real.exp (lam * ∫ v in (0:ℝ)..t, h v)) * hCT + hYI
  have h1 : lam * Real.exp (lam * ∫ v in (0:ℝ)..t, h v) * ∫ s in t..T, Y s * h s * g s
      ≤ lam * Real.exp (lam * ∫ v in (0:ℝ)..t, h v) * ∫ s in t..T, j s :=
    mul_le_mul_of_nonneg_left hle (by positivity)
  have hYT := hYpos T
  constructor
  · exact mul_nonneg (mul_nonneg hlam.le hEpos.le) hint_nonneg
  · nlinarith [mul_pos hEpos hYT]

open GroupBuyEq.Signup

/-- threshold characterization of the sign-up rule -/
theorem V_iff (P : Params) (hd : 0 < P.d) (hδ : 0 < P.δ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (u : ℝ) : 0 ≤ V P a b u ↔ ubar P a b ≤ u := by
  unfold V ubar Params.p2 Params.p1
  set p0 := P.p0
  set δ := P.δ
  set d := P.d
  have k1 : ∀ x y : ℝ, x ≤ y → max x y = y := fun x y h => max_eq_right h
  have k2 : ∀ x y : ℝ, y ≤ x → max x y = x := fun x y h => max_eq_left h
  split_ifs with h1 h2
  · -- branch 1 : root in region II, b > 0
    have hb0 : 0 < b := by
      rcases eq_or_lt_of_le hb with h | h
      · rw [← h] at h1; nlinarith [h1.2]
      · exact h
    have hr : b * (p0 - 2 * δ - d * (1 - 1 / b)) = b * (p0 - 2 * δ) - b * d + d := by
      field_simp; ring
    set r := p0 - 2 * δ - d * (1 - 1 / b) with hrdef
    rcases le_or_gt u (p0 - δ - δ - d) with hu | hu
    · rw [k1 _ _ (by linarith), k1 _ _ (by linarith), k1 _ _ (by linarith)]
      constructor
      · intro h; nlinarith
      · intro h; nlinarith [mul_le_mul_of_nonneg_left h hb]
    rcases le_or_gt u (p0 - δ - d) with hu2 | hu2
    · rw [k1 _ _ (by linarith), k2 _ _ (by linarith), k1 _ _ (by linarith)]
      constructor
      · intro h; by_contra hc; push Not at hc; nlinarith [mul_lt_mul_of_pos_left hc hb0]
      · intro h; nlinarith [mul_le_mul_of_nonneg_left h hb]
    rcases le_or_gt u (p0 - d) with hu3 | hu3
    · rw [k2 _ _ (by linarith), k2 _ _ (by linarith), k1 _ _ (by linarith)]
      constructor
      · intro h; by_contra hc; push Not at hc; nlinarith [mul_lt_mul_of_pos_left hc hb0]
      · intro h; nlinarith [mul_le_mul_of_nonneg_left h hb, mul_le_mul_of_nonneg_left hu2.le ha]
    · rw [k2 _ _ (by linarith), k2 _ _ (by linarith), k2 _ _ (by linarith)]
      constructor
      · intro h; by_contra hc; push Not at hc; nlinarith [mul_lt_mul_of_pos_left hc hb0]
      · intro h; nlinarith [mul_le_mul_of_nonneg_left h hb, mul_le_mul_of_nonneg_left hu2.le ha]
  · -- branch 2 : root in region III
    have hab : 0 < a + b := by
      by_contra hc; push Not at hc
      have : a = 0 := by linarith
      have : b = 0 := by linarith
      subst_vars; nlinarith [h2.2]
    have hr : (a + b) * (p0 - d + (d - δ * (a + 2 * b)) / (a + b))
        = (a + b) * (p0 - d) + (d - δ * (a + 2 * b)) := by
      field_simp
    set r := p0 - d + (d - δ * (a + 2 * b)) / (a + b) with hrdef
    have hdb : δ * b < d := by
      by_contra hc; push Not at hc; exact h1 ⟨hd.le, hc⟩
    rcases le_or_gt u (p0 - δ - δ - d) with hu | hu
    · rw [k1 _ _ (by linarith), k1 _ _ (by linarith), k1 _ _ (by linarith)]
      constructor
      · intro h; nlinarith
      · intro h; by_contra _
        nlinarith [mul_le_mul_of_nonneg_left h hab.le]
    rcases le_or_gt u (p0 - δ - d) with hu2 | hu2
    · rw [k1 _ _ (by linarith), k2 _ _ (by linarith), k1 _ _ (by linarith)]
      constructor
      · intro h; nlinarith [mul_le_mul_of_nonneg_left hu2 hb]
      · intro h; nlinarith [mul_le_mul_of_nonneg_left h hab.le, mul_le_mul_of_nonneg_left hu2 ha]
    rcases le_or_gt u (p0 - d) with hu3 | hu3
    · rw [k2 _ _ (by linarith), k2 _ _ (by linarith), k1 _ _ (by linarith)]
      constructor
      · intro h; by_contra hc; push Not at hc; nlinarith [mul_lt_mul_of_pos_left hc hab]
      · intro h; nlinarith [mul_le_mul_of_nonneg_left h hab.le]
    · rw [k2 _ _ (by linarith), k2 _ _ (by linarith), k2 _ _ (by linarith)]
      constructor
      · intro h; by_contra hc; push Not at hc; nlinarith [mul_lt_mul_of_pos_left hc hab]
      · intro h; nlinarith [mul_le_mul_of_nonneg_left h hab.le, h2.2]
  · -- branch 3 : root in region IV
    have hdb : δ * b < d := by
      by_contra hc; push Not at hc; exact h1 ⟨hd.le, hc⟩
    have hd2 : δ * a + 2 * δ * b < d := by
      by_contra hc; push Not at hc; exact h2 ⟨hdb, hc⟩
    rcases le_or_gt u (p0 - δ - δ - d) with hu | hu
    · rw [k1 _ _ (by linarith), k1 _ _ (by linarith), k1 _ _ (by linarith)]
      constructor
      · intro h; nlinarith
      · intro h; nlinarith [mul_nonneg ha hδ.le, mul_nonneg hb hδ.le]
    rcases le_or_gt u (p0 - δ - d) with hu2 | hu2
    · rw [k1 _ _ (by linarith), k2 _ _ (by linarith), k1 _ _ (by linarith)]
      constructor
      · intro h; nlinarith [mul_le_mul_of_nonneg_left hu2 hb]
      · intro h; nlinarith [mul_nonneg ha hδ.le, mul_nonneg hb hδ.le]
    rcases le_or_gt u (p0 - d) with hu3 | hu3
    · rw [k2 _ _ (by linarith), k2 _ _ (by linarith), k1 _ _ (by linarith)]
      constructor
      · intro h; nlinarith [mul_le_mul_of_nonneg_left hu3 ha, mul_le_mul_of_nonneg_left hu3 hb]
      · intro h; nlinarith [mul_nonneg ha hδ.le, mul_nonneg hb hδ.le]
    · rw [k2 _ _ (by linarith), k2 _ _ (by linarith), k2 _ _ (by linarith)]
      constructor
      · intro h; nlinarith
      · intro h; nlinarith

/-- `H = 1 - cdf` -/
theorem H_eq (P : Params) (hd : 0 < P.d) (hδ : 0 < P.δ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (E : Profile) (k : ℕ) (t : ℝ)
    (ha : 0 ≤ E.pi1 (k + 1) t) (hb : 0 ≤ E.pi2 (k + 1) t) :
    H P μ E k t = 1 - ProbabilityTheory.cdf μ (ubar P (E.pi1 (k + 1) t) (E.pi2 (k + 1) t)) := by
  unfold H
  have hs : {u | 0 ≤ V P (E.pi1 (k + 1) t) (E.pi2 (k + 1) t) u}
      = Ici (ubar P (E.pi1 (k + 1) t) (E.pi2 (k + 1) t)) := by
    ext u; simp only [mem_setOf_eq, mem_Ici]; exact V_iff P hd hδ _ _ ha hb u
  rw [hs, ProbabilityTheory.cdf_eq_real, ← probReal_compl_eq_one_sub measurableSet_Iic,
    compl_Iic, measureReal_def, measure_congr Ioi_ae_eq_Ici]


open GroupBuyEq.Signup

theorem phi_congr (lam T : ℝ) (h h' g g' : ℝ → ℝ) (hh : ∀ x ∈ Icc 0 T, h x = h' x)
    (hg : ∀ x ∈ Icc 0 T, g x = g' x) :
    ∀ t ∈ Icc 0 T, Phi lam T h g t = Phi lam T h' g' t := by
  intro t ht
  unfold Phi
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc 0 T := uIcc_subset_Icc ht ⟨ht.1.trans ht.2, le_rfl⟩ hs
  dsimp only
  rw [intervalIntegral.integral_congr (g := h') (fun v hv => hh v (uIcc_subset_Icc ht hs' hv)),
    hh s hs', hg s hs']

theorem phi_contOn (lam T : ℝ) (hlam : 0 < lam) (hT : 0 ≤ T) (h g : ℝ → ℝ)
    (hh : Measurable h) (h01 : ∀ x, 0 ≤ h x ∧ h x ≤ 1)
    (hg : Measurable g) (hgb : ∀ x ∈ Icc 0 T, |g x| ≤ 1) :
    ContinuousOn (Phi lam T h g) (Icc 0 T) := by
  have hhb : ∀ x, |h x| ≤ 1 := fun x => abs_le.2 ⟨by linarith [(h01 x).1], (h01 x).2⟩
  have hhi : ∀ a b, IntervalIntegrable h volume a b := ii_glob hh hhb
  have hIc : Continuous (fun t => ∫ v in (0:ℝ)..t, h v) :=
    intervalIntegral.continuous_primitive hhi 0
  have hIm : Measurable (fun t => ∫ v in (0:ℝ)..t, h v) := hIc.measurable
  have hkm : Measurable (fun s => Real.exp (-(lam * ∫ v in (0:ℝ)..s, h v)) * h s * g s) := by
    fun_prop
  have hkb : ∀ x ∈ Icc 0 T, |Real.exp (-(lam * ∫ v in (0:ℝ)..x, h v)) * h x * g x| ≤ 1 := by
    intro x hx
    rw [abs_mul, abs_mul]
    have e1 : |Real.exp (-(lam * ∫ v in (0:ℝ)..x, h v))| ≤ 1 := by
      rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      have := intervalIntegral.integral_nonneg (μ := volume) hx.1 (fun y _ => (h01 y).1)
      nlinarith
    have := hhb x; have := hgb x hx
    calc |Real.exp (-(lam * ∫ v in (0:ℝ)..x, h v))| * |h x| * |g x| ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by ring
  have hki := ii_of_bdd hkm hkb (a := 0) (b := T) ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩
  have hc := (hki.absolutelyContinuousOnInterval_intervalIntegral (c := T) right_mem_uIcc).continuousOn
  rw [uIcc_of_le hT] at hc
  have heq : Phi lam T h g = fun t => lam * Real.exp (lam * ∫ v in (0:ℝ)..t, h v) *
      -(∫ s in T..t, Real.exp (-(lam * ∫ v in (0:ℝ)..s, h v)) * h s * g s) := by
    funext t; rw [phi_conv lam T h g hhi t, intervalIntegral.integral_symm T t]
  rw [heq]
  exact ContinuousOn.mul (Continuous.continuousOn (by fun_prop)) hc.neg

noncomputable def clip (T : ℝ) (φ : ℝ → ℝ) : ℝ → ℝ := fun t => if t ∈ Icc 0 T then φ t else 0

theorem clip_meas (T : ℝ) (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Icc 0 T)) :
    Measurable (clip T φ) :=
  ContinuousOn.measurable_piecewise hφ (continuousOn_const (c := (0:ℝ))) measurableSet_Icc

theorem clip_eq (T : ℝ) (φ : ℝ → ℝ) (t : ℝ) (ht : t ∈ Icc 0 T) : clip T φ t = φ t := by
  unfold clip; rw [if_pos ht]

noncomputable def Hf (P : Params) (μ : Measure ℝ) (a b : ℝ → ℝ) (t : ℝ) : ℝ :=
  (μ {u | 0 ≤ V P (a t) (b t) u}).toReal

theorem Hf_meas (P : Params) (μ : Measure ℝ) [IsProbabilityMeasure μ] (a b : ℝ → ℝ)
    (ha : Measurable a) (hb : Measurable b) : Measurable (Hf P μ a b) := by
  have hS : MeasurableSet {p : ℝ × ℝ | 0 ≤ V P (a p.1) (b p.1) p.2} := by
    apply measurableSet_le measurable_const
    unfold V; fun_prop
  exact (measurable_measure_prodMk_left hS).ennreal_toReal

theorem Hf_01 (P : Params) (μ : Measure ℝ) [IsProbabilityMeasure μ] (a b : ℝ → ℝ) (t : ℝ) :
    0 ≤ Hf P μ a b t ∧ Hf P μ a b t ≤ 1 := by
  unfold Hf
  exact ⟨ENNReal.toReal_nonneg,
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)⟩

theorem clip_spec (P : Params) (hT : 0 < P.T) (hlam : 0 < P.lam) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (a b g : ℝ → ℝ) (ha : Measurable a) (hb : Measurable b)
    (hg : Measurable g) (hg01 : ∀ x ∈ Icc 0 P.T, g x ∈ Icc (0:ℝ) 1) :
    Measurable (clip P.T (Phi P.lam P.T (Hf P μ a b) g)) ∧
    (∀ t ∈ Icc 0 P.T, clip P.T (Phi P.lam P.T (Hf P μ a b) g) t ∈ Icc (0:ℝ) 1) ∧
    ∀ t ∈ Icc 0 P.T, clip P.T (Phi P.lam P.T (Hf P μ a b) g) t =
      ∫ x in (0:ℝ)..(P.T - t), (Hf P μ a b (t + x) * g (t + x) + (1 - Hf P μ a b (t + x)) *
        clip P.T (Phi P.lam P.T (Hf P μ a b) g) (t + x)) * P.lam * Real.exp (-(P.lam * x)) := by
  have hHm := Hf_meas P μ a b ha hb
  have hH01 := Hf_01 P μ a b
  have hgb : ∀ x ∈ Icc 0 P.T, |g x| ≤ 1 := fun x hx =>
    abs_le.2 ⟨by linarith [(hg01 x hx).1], (hg01 x hx).2⟩
  have hcont := phi_contOn P.lam P.T hlam hT.le (Hf P μ a b) g hHm hH01 hg hgb
  have hfm := clip_meas P.T _ hcont
  have hfe : ∀ t ∈ Icc 0 P.T, clip P.T (Phi P.lam P.T (Hf P μ a b) g) t
      = Phi P.lam P.T (Hf P μ a b) g t := fun t ht => clip_eq _ _ t ht
  have hbd := phi_bound P.lam P.T hlam hT.le (Hf P μ a b) g hHm hH01 hg hg01
  refine ⟨hfm, fun t ht => by rw [hfe t ht]; exact hbd t ht, ?_⟩
  exact exist P.lam P.T hlam hT.le _ g _ hHm hH01 hg hgb hfm (fun x hx => by
    rw [hfe x hx]; exact abs_le.2 ⟨by linarith [(hbd x hx).1], (hbd x hx).2⟩) hfe

noncomputable def step (P : Params) (μ : Measure ℝ) (k : ℕ) (nx : (ℝ → ℝ) × (ℝ → ℝ)) :
    (ℝ → ℝ) × (ℝ → ℝ) :=
  (if P.M1 ≤ k then fun t => 1 - clip P.T (Phi P.lam P.T (Hf P μ nx.1 nx.2) nx.2) t
    else clip P.T (Phi P.lam P.T (Hf P μ nx.1 nx.2) nx.1),
   clip P.T (Phi P.lam P.T (Hf P μ nx.1 nx.2) nx.2))

noncomputable def lev (P : Params) (μ : Measure ℝ) (k : ℕ) : (ℝ → ℝ) × (ℝ → ℝ) :=
  if hk : P.M2 ≤ k then ((fun _ => 0), (fun _ => 1)) else step P μ k (lev P μ (k + 1))
termination_by P.M2 - k
decreasing_by omega

theorem lev_ge (P : Params) (μ : Measure ℝ) (k : ℕ) (hk : P.M2 ≤ k) :
    lev P μ k = ((fun _ => 0), (fun _ => 1)) := by
  rw [lev, dif_pos hk]

theorem lev_lt (P : Params) (μ : Measure ℝ) (k : ℕ) (hk : k < P.M2) :
    lev P μ k = step P μ k (lev P μ (k + 1)) := by
  rw [lev, dif_neg (by omega)]

theorem lev_inv (P : Params) (hT : 0 < P.T) (hlam : 0 < P.lam) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (k : ℕ) :
    Measurable (lev P μ k).1 ∧ Measurable (lev P μ k).2 ∧
      ∀ t ∈ Icc 0 P.T, (lev P μ k).1 t ∈ Icc (0:ℝ) 1 ∧ (lev P μ k).2 t ∈ Icc (0:ℝ) 1 := by
  have key : ∀ n k, P.M2 - k ≤ n → Measurable (lev P μ k).1 ∧ Measurable (lev P μ k).2 ∧
      ∀ t ∈ Icc 0 P.T, (lev P μ k).1 t ∈ Icc (0:ℝ) 1 ∧ (lev P μ k).2 t ∈ Icc (0:ℝ) 1 := by
    intro n
    induction n with
    | zero =>
      intro k hk
      rw [lev_ge P μ k (by omega)]
      refine ⟨measurable_const, measurable_const, fun t _ => ?_⟩
      simp
    | succ n ih =>
      intro k hk
      by_cases hk' : P.M2 ≤ k
      · exact ih k (by omega)
      push Not at hk'
      obtain ⟨ma, mb, bd⟩ := ih (k + 1) (by omega)
      have c2 := clip_spec P hT hlam μ _ _ _ ma mb mb (fun x hx => (bd x hx).2)
      have c1 := clip_spec P hT hlam μ _ _ _ ma mb ma (fun x hx => (bd x hx).1)
      rw [lev_lt P μ k hk']
      unfold step
      by_cases hm : P.M1 ≤ k
      · rw [if_pos hm]
        refine ⟨measurable_const.sub c2.1, c2.1, fun t ht => ⟨?_, c2.2.1 t ht⟩⟩
        have := c2.2.1 t ht
        exact ⟨by linarith [this.2], by linarith [this.1]⟩
      · rw [if_neg hm]
        exact ⟨c1.1, c2.1, fun t ht => ⟨c1.2.1 t ht, c2.2.1 t ht⟩⟩
  exact key _ k le_rfl

noncomputable def prof (P : Params) (μ : Measure ℝ) : Profile :=
  ⟨fun k => (lev P μ k).1, fun k => (lev P μ k).2⟩

theorem prof_pi1 (P : Params) (μ : Measure ℝ) : (prof P μ).pi1 = fun k => (lev P μ k).1 := rfl
theorem prof_pi2 (P : Params) (μ : Measure ℝ) : (prof P μ).pi2 = fun k => (lev P μ k).2 := rfl

theorem prof_eq (P : Params) (hP : P.Standing) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsEquilibrium P μ (prof P μ) := by
  obtain ⟨hT, hlam, -, hM12, -, -, -, -⟩ := hP
  have inv := lev_inv P hT hlam μ
  refine ⟨fun k => ⟨(inv k).1, (inv k).2.1⟩, fun k t ht => (inv k).2.2 t ht, ?_, ?_, ?_, ?_⟩
  · intro k hk t _
    simp [prof_pi1, prof_pi2, lev_ge P μ k hk]
  · intro k hm hk t _
    simp only [prof_pi1, prof_pi2, lev_lt P μ k hk, step, if_pos hm]
  · intro k hk t ht
    have hHk : H P μ (prof P μ) k = Hf P μ (lev P μ (k + 1)).1 (lev P μ (k + 1)).2 := rfl
    rw [hHk]
    simp only [prof_pi2]
    obtain ⟨ma, mb, bd⟩ := inv (k + 1)
    have c2 := clip_spec P hT hlam μ _ _ _ ma mb mb (fun x hx => (bd x hx).2)
    rw [lev_lt P μ k hk]
    exact c2.2.2 t ht
  · intro k hk t ht
    have hHk : H P μ (prof P μ) k = Hf P μ (lev P μ (k + 1)).1 (lev P μ (k + 1)).2 := rfl
    rw [hHk]
    simp only [prof_pi1]
    obtain ⟨ma, mb, bd⟩ := inv (k + 1)
    have c1 := clip_spec P hT hlam μ _ _ _ ma mb ma (fun x hx => (bd x hx).1)
    have hm : ¬ P.M1 ≤ k := by omega
    rw [lev_lt P μ k (by omega)]
    unfold step
    rw [if_neg hm]
    exact c1.2.2 t ht


end GBQ

open GroupBuyEq.Signup in
theorem solution (P : Params) (hP : P.Standing) (μ : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.NullSingletonClass μ] :
    (∃ E : Profile, IsEquilibrium P μ E) ∧
    (∀ E E' : Profile, IsEquilibrium P μ E → IsEquilibrium P μ E' → ∀ k : ℕ,
        Set.EqOn (E.pi1 k) (E'.pi1 k) (Set.Icc 0 P.T) ∧
          Set.EqOn (E.pi2 k) (E'.pi2 k) (Set.Icc 0 P.T)) ∧
    (∀ E : Profile, IsEquilibrium P μ E → ∀ k : ℕ, ∀ t ∈ Set.Icc 0 P.T,
        (∀ u : ℝ, 0 ≤ V P (E.pi1 (k + 1) t) (E.pi2 (k + 1) t) u ↔
            ubar P (E.pi1 (k + 1) t) (E.pi2 (k + 1) t) ≤ u) ∧
        H P μ E k t = 1 - ProbabilityTheory.cdf μ (ubar P (E.pi1 (k + 1) t) (E.pi2 (k + 1) t)) ∧
        (k < P.M2 → E.pi2 k t = P.lam * ∫ s in t..P.T,
            Real.exp (-(P.lam * ∫ v in t..s, H P μ E k v)) * H P μ E k s * E.pi2 (k + 1) s) ∧
        (k < P.M1 → E.pi1 k t = P.lam * ∫ s in t..P.T,
            Real.exp (-(P.lam * ∫ v in t..s, H P μ E k v)) * H P μ E k s * E.pi1 (k + 1) s)) := by
  have hP' := hP
  obtain ⟨hT, hlam, hM1, hM12, hd, hδ, hδp, hdp⟩ := hP
  have hHm : ∀ E : Profile, IsEquilibrium P μ E → ∀ k, Measurable (H P μ E k) := fun E hE k =>
    GBQ.Hf_meas P μ _ _ (hE.1 (k + 1)).1 (hE.1 (k + 1)).2
  have hH01 : ∀ (E : Profile) (k : ℕ) (x : ℝ), 0 ≤ H P μ E k x ∧ H P μ E k x ≤ 1 :=
    fun E k x => GBQ.Hf_01 P μ _ _ x
  have ab : ∀ x : ℝ, x ∈ Set.Icc (0:ℝ) 1 → |x| ≤ 1 := fun x hx =>
    abs_le.2 ⟨by linarith [hx.1], hx.2⟩
  have char2 : ∀ E : Profile, IsEquilibrium P μ E → ∀ k, k < P.M2 → ∀ t ∈ Set.Icc 0 P.T,
      E.pi2 k t = GBQ.Phi P.lam P.T (H P μ E k) (E.pi2 (k + 1)) t := by
    intro E hE k hk
    exact GBQ.char P.lam P.T hlam hT.le (H P μ E k) (E.pi2 (k + 1)) (E.pi2 k) (hHm E hE k)
      (hH01 E k) (hE.1 (k + 1)).2 (fun x hx => ab _ ((hE.2.1 (k + 1) x hx).2)) (hE.1 k).2
      (fun x hx => ab _ ((hE.2.1 k x hx).2)) (hE.2.2.2.2.1 k hk)
  have char1 : ∀ E : Profile, IsEquilibrium P μ E → ∀ k, k < P.M1 → ∀ t ∈ Set.Icc 0 P.T,
      E.pi1 k t = GBQ.Phi P.lam P.T (H P μ E k) (E.pi1 (k + 1)) t := by
    intro E hE k hk
    exact GBQ.char P.lam P.T hlam hT.le (H P μ E k) (E.pi1 (k + 1)) (E.pi1 k) (hHm E hE k)
      (hH01 E k) (hE.1 (k + 1)).1 (fun x hx => ab _ ((hE.2.1 (k + 1) x hx).1)) (hE.1 k).1
      (fun x hx => ab _ ((hE.2.1 k x hx).1)) (hE.2.2.2.2.2 k hk)
  refine ⟨⟨GBQ.prof P μ, GBQ.prof_eq P hP' μ⟩, ?_, ?_⟩
  · intro E E' hE hE'
    have key : ∀ n k, P.M2 - k ≤ n → Set.EqOn (E.pi1 k) (E'.pi1 k) (Set.Icc 0 P.T) ∧
        Set.EqOn (E.pi2 k) (E'.pi2 k) (Set.Icc 0 P.T) := by
      intro n
      induction n with
      | zero =>
        intro k hk
        have hk' : P.M2 ≤ k := by omega
        exact ⟨fun t ht => by rw [(hE.2.2.1 k hk' t ht).1, (hE'.2.2.1 k hk' t ht).1],
          fun t ht => by rw [(hE.2.2.1 k hk' t ht).2, (hE'.2.2.1 k hk' t ht).2]⟩
      | succ n ih =>
        intro k hk
        by_cases hk' : P.M2 ≤ k
        · exact ih k (by omega)
        push Not at hk'
        obtain ⟨e1, e2⟩ := ih (k + 1) (by omega)
        have hHe : ∀ x ∈ Set.Icc 0 P.T, H P μ E k x = H P μ E' k x := by
          intro x hx; unfold H; rw [e1 hx, e2 hx]
        have h2 : Set.EqOn (E.pi2 k) (E'.pi2 k) (Set.Icc 0 P.T) := fun t ht => by
          rw [char2 E hE k hk' t ht, char2 E' hE' k hk' t ht]
          exact GBQ.phi_congr _ _ _ _ _ _ hHe (fun x hx => e2 hx) t ht
        refine ⟨fun t ht => ?_, h2⟩
        by_cases hm : P.M1 ≤ k
        · rw [hE.2.2.2.1 k hm hk' t ht, hE'.2.2.2.1 k hm hk' t ht, h2 ht]
        · push Not at hm
          rw [char1 E hE k hm t ht, char1 E' hE' k hm t ht]
          exact GBQ.phi_congr _ _ _ _ _ _ hHe (fun x hx => e1 hx) t ht
    intro k
    exact key _ k le_rfl
  · intro E hE k t ht
    have hb := hE.2.1 (k + 1) t ht
    exact ⟨fun u => GBQ.V_iff P hd hδ _ _ hb.1.1 hb.2.1 u, GBQ.H_eq P hd hδ μ E k t hb.1.1 hb.2.1,
      fun hk => char2 E hE k hk t ht, fun hk => char1 E hE k hk t ht⟩

