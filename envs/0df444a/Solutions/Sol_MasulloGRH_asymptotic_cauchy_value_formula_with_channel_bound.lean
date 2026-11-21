-- Prove2me | solution 1 for MasulloGRH.asymptotic_cauchy_value_formula_with_channel_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T04:45:37.538732+00:00
-- url     : https://prove2.me/submissions/4968ccf0-18eb-46b5-8b19-04d9394a8bb0

import Theorems.Thm_ResidueTheoremOnRectangleWithSimplePole_prime
import Definitions.Def_MasulloGRH_MellinRpos
import Definitions.Def_ResidueCalcOnRectangles_defs
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open Set Filter MeasureTheory Complex Asymptotics
open scoped Topology Interval

namespace C11Cauchy
private theorem strip_line {F : ℂ → ℂ} {l r x B : ℝ} (hxl : l ≤ x) (hxr : x ≤ r)
    (hF : ∀ s : ℂ, l ≤ s.re → s.re ≤ r → DifferentiableAt ℂ F s)
    (hbound : ∀ s : ℂ, l ≤ s.re → s.re ≤ r → ‖F s‖ ≤ B/(1+s.im^2))
    (z : ℂ) (hz : x ≠ z.re) :
    MasulloGRH.VerticalLineIntegrable (fun s => F s/(s-z)) x := by
  let g (y : ℝ) := F (x+y*I)/((x:ℂ)+y*I-z)
  have hd (y : ℝ) : |x-z.re| ≤ ‖(x:ℂ)+y*I-z‖ := by
    simpa using abs_re_le_norm ((x:ℂ)+y*I-z)
  have hpos : 0 < |x-z.re| := abs_pos.mpr (sub_ne_zero.mpr hz)
  have hcont : Continuous g := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have h := hF ((x:ℂ)+y*I) (by simpa using hxl) (by simpa using hxr)
    unfold g
    let j (v : ℝ) : ℂ := (x:ℂ)+v*I
    have hj : Continuous j := by dsimp [j]; fun_prop
    have hnum : ContinuousAt (fun v => F (j v)) y := h.continuousAt.comp (f := j) hj.continuousAt
    have hden : ContinuousAt (fun v => j v-z) y := (hj.sub continuous_const).continuousAt
    apply hnum.div hden
    intro e
    apply hz
    simpa [j] using congrArg Complex.re (sub_eq_zero.mp e)
  have hmaj := (integrable_inv_one_add_sq.const_mul B).div_const |x-z.re|
  apply hmaj.mono' hcont.aestronglyMeasurable
  filter_upwards with y
  change ‖F _ / _‖ ≤ _
  rw [norm_div]
  calc
    _ ≤ ‖F ((x:ℂ)+y*I)‖ / |x-z.re| := div_le_div_of_nonneg_left (norm_nonneg _) hpos (hd y)
    _ ≤ (B/(1+y^2)) / |x-z.re| := by
      exact div_le_div_of_nonneg_right (by simpa using hbound ((x:ℂ)+y*I) (by simpa using hxl) (by simpa using hxr)) hpos.le
    _ = _ := by simp only [div_eq_mul_inv]

private theorem horizontal_decay {F : ℂ → ℂ} {l r B : ℝ} (hlr : l ≤ r) (_hB : 0 ≤ B)
    (hbound : ∀ s : ℂ, l ≤ s.re → s.re ≤ r → ‖F s‖ ≤ B/(1+s.im^2))
    (z : ℂ) {ι : Type*} {f : Filter ι} (height : ι → ℝ)
    (ht : Tendsto (fun n => |height n|) f atTop) :
    Tendsto (fun n => HIntegral (fun s => F s / (s-z)) l r (height n)) f (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hden := (tendsto_atTop_add_const_left _ 1 ((Filter.tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp ht))
  have hlim : Tendsto (fun n => B/(1+(height n)^2)*|r-l|) f (𝓝 0) := by
    have hden' : Tendsto (fun n => 1+(height n)^2) f atTop := by simpa [Function.comp_def] using hden
    simpa using (tendsto_const_nhds.div_atTop (a := B) hden').mul_const |r-l|
  apply squeeze_zero' (.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [ht.eventually_ge_atTop (|z.im|+1)] with n hn
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  rw [Set.uIoc_of_le hlr] at hx
  have hd : 1 ≤ ‖(x:ℂ)+(height n)*I-z‖ := by
    have h := abs_im_le_norm ((x:ℂ)+(height n)*I-z)
    simp only [sub_im, add_im, ofReal_im, zero_add, mul_I_im, ofReal_re] at h
    linarith [abs_sub_abs_le_abs_sub (height n) z.im]
  rw [norm_div]
  exact (div_le_self (norm_nonneg _) hd).trans (by simpa using hbound ((x:ℂ)+(height n)*I) (by simpa using hx.1.le) (by simpa using hx.2))

private theorem rect_neighborhood {l r T : ℝ} {z : ℂ} (hl : l < z.re) (hr : z.re < r)
    (ht : |z.im| < T) : Complex.Rectangle ⟨l,-T⟩ ⟨r,T⟩ ∈ 𝓝 z := by
  have h₁ : Icc l r ∈ 𝓝 z.re := Icc_mem_nhds hl hr
  have h₂ : Icc (-T) T ∈ 𝓝 z.im := Icc_mem_nhds (abs_lt.mp ht).1 (abs_lt.mp ht).2
  change (uIcc l r ×ℂ uIcc (-T) T) ∈ 𝓝 z
  rw [uIcc_of_le (hl.trans hr).le, uIcc_of_le (show -T ≤ T by linarith [abs_nonneg z.im])]
  exact inter_mem (continuous_re.continuousAt.preimage_mem_nhds h₁)
      (continuous_im.continuousAt.preimage_mem_nhds h₂)

private theorem strip_cauchy
    (hres : ∀ {f : ℂ → ℂ} {z w p A : ℂ},
      z.re ≤ w.re → z.im ≤ w.im → Complex.Rectangle z w ∈ 𝓝 p →
        HolomorphicOn f (Complex.Rectangle z w \ {p}) →
        (f - (fun s ↦ A / (s - p))) =O[𝓝[≠] p] (1 : ℂ → ℂ) →
        RectangleIntegral' f z w = A)
    {F : ℂ → ℂ} {l r B : ℝ} (hlr : l < r) (hB : 0 ≤ B)
    (hF : ∀ s : ℂ, l ≤ s.re → s.re ≤ r → DifferentiableAt ℂ F s)
    (hbound : ∀ s : ℂ, l ≤ s.re → s.re ≤ r → ‖F s‖ ≤ B/(1+s.im^2))
    {z : ℂ} (hlz : l ≠ z.re) (hrz : r ≠ z.re) :
    let g := fun s : ℂ => F s / (s-z)
    (1/(2*Real.pi*I)) * (MasulloGRH.verticalLineIntegral g r - MasulloGRH.verticalLineIntegral g l) =
      if l < z.re ∧ z.re < r then F z else 0 := by
  intro g
  let c : ℂ := 1/(2*Real.pi*I)
  let R (T : ℝ) := RectangleIntegral' g ⟨l,-T⟩ ⟨r,T⟩
  have rt : Tendsto (fun T : ℝ => T) atTop atTop := tendsto_id
  have hm : Tendsto (fun T : ℝ => -T) atTop atBot := tendsto_neg_atTop_atBot
  have hs : Tendsto (fun T : ℝ => |T|) atTop atTop := tendsto_abs_atTop_atTop
  have hbot := horizontal_decay hlr.le hB hbound z (fun T : ℝ => -T) (by simpa using hs)
  have htop := horizontal_decay hlr.le hB hbound z (fun T : ℝ => T) hs
  have hv (x : ℝ) (hxl : l ≤ x) (hxr : x ≤ r) (hxz : x ≠ z.re) :
      Tendsto (fun T : ℝ => VIntegral g x (-T) T) atTop (𝓝 (MasulloGRH.verticalLineIntegral g x)) :=
    (intervalIntegral_tendsto_integral (strip_line hxl hxr hF hbound z hxz) hm rt).const_mul I
  have hlim : Tendsto R atTop (𝓝 (c*(MasulloGRH.verticalLineIntegral g r - MasulloGRH.verticalLineIntegral g l))) := by
    simpa only [zero_sub, sub_zero, zero_add, smul_eq_mul, R, c, RectangleIntegral', RectangleIntegral]
      using (((hbot.sub htop).add (hv r hlr.le le_rfl hrz)).sub (hv l le_rfl hlr.le hlz)).const_mul c
  have hfixed : ∀ᶠ T : ℝ in atTop, R T = if l < z.re ∧ z.re < r then F z else 0 := by
    filter_upwards [eventually_gt_atTop |z.im|] with T hT
    have hTT : -T ≤ T := by linarith [abs_nonneg z.im]
    have hrect {s : ℂ} (hs : s ∈ Complex.Rectangle ⟨l,-T⟩ ⟨r,T⟩) :
        s.re ∈ Icc l r := by
      have h := hs.1
      simpa [Set.uIcc_of_le hlr.le] using h
    have hdiff {s : ℂ} (hs : s ∈ Complex.Rectangle ⟨l,-T⟩ ⟨r,T⟩) (hn : s ≠ z) :
        DifferentiableAt ℂ g s := (hF _ (hrect hs).1 (hrect hs).2).div
          (differentiableAt_id.sub_const z) (sub_ne_zero.mpr hn)
    split_ifs with h
    · obtain ⟨hl,hr⟩ := h
      apply hres hlr.le hTT (rect_neighborhood hl hr hT)
      · intro s hs
        exact (hdiff hs.1 (by simpa using hs.2)).differentiableWithinAt
      · have hf := (hF z hl.le hr.le).hasDerivAt.tendsto_slope.isBigO_one ℂ
        change (fun s : ℂ => F s/(s-z) - F z/(s-z)) =O[𝓝[≠] z] (fun _ => (1:ℂ))
        simpa only [slope_fun_def_field, sub_div] using hf
    · have hz : z ∉ Complex.Rectangle ⟨l,-T⟩ ⟨r,T⟩ := by
        intro hmem
        exact h ⟨lt_of_le_of_ne (hrect hmem).1 hlz, lt_of_le_of_ne (hrect hmem).2 hrz.symm⟩
      have hzero := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g ⟨l,-T⟩ ⟨r,T⟩
        (fun s hs => (hdiff hs (fun e => hz (e ▸ hs))).differentiableWithinAt)
      have hraw : RectangleIntegral g ⟨l,-T⟩ ⟨r,T⟩ = 0 := hzero
      simp [R,RectangleIntegral',hraw]
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hfixed.mono (fun _ h => h.symm)))

private theorem clip_bound {F : ℂ → ℂ} {S : Set ℂ} {C Y M : ℝ} (hC : 0 < C)
    (hhi : ∀ s ∈ S, Y ≤ |s.im| → ‖F s‖ ≤ C/|s.im|^2)
    (hlo : ∀ s ∈ S, |s.im| ≤ max Y 1 → ‖F s‖ ≤ M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ S, ‖F s‖ ≤ B/(1+s.im^2) := by
  let T := max Y 1
  let B := max (max M 0 * (1+T^2)) (2*C)
  have hB : 2*C ≤ B := le_max_right _ _
  refine ⟨B, by linarith, ?_⟩
  intro s hs
  apply (le_div_iff₀ (by positivity : 0 < 1+s.im^2)).2
  by_cases hy : |s.im| ≤ T
  · have hM : ‖F s‖ ≤ max M 0 := (hlo s hs hy).trans (le_max_left ..)
    have hsq : s.im^2 ≤ T^2 := by nlinarith [sq_abs s.im, mul_self_le_mul_self (abs_nonneg s.im) hy]
    exact (mul_le_mul hM (by linarith) (by positivity) (le_max_right M 0)).trans (le_max_left ..)
  · have h1 : 1 ≤ |s.im| := (le_max_right Y 1).trans (le_of_not_ge hy)
    have hsquare : 1 ≤ s.im^2 := by nlinarith [sq_abs s.im,mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1) h1]
    have htail := (le_div_iff₀ (by positivity : 0 < |s.im|^2)).mp (hhi s hs ((le_max_left Y 1).trans (le_of_not_ge hy)))
    rw [sq_abs] at htail
    nlinarith [mul_le_mul_of_nonneg_left hsquare (norm_nonneg (F s))]

private theorem abs_channel_of_strip {F : ℂ → ℂ} {a b ε : ℝ} (hε : 0 < ε) (hw : a+ε < b-ε)
    (hF : DifferentiableOn ℂ F (MasulloGRH.openStrip a b))
    (hdec : MasulloGRH.UniformlySchwartzOnStrip F a b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, a+ε ≤ s.re → s.re ≤ b-ε → ‖F s‖ ≤ B/(1+s.im^2) := by
  obtain ⟨C,hC,Y,hY⟩ := hdec ε hε hw 2 (by norm_num)
  let T := max Y 1
  let K := Icc (a+ε) (b-ε) ×ℂ Icc (-T) T
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hsub : K ⊆ MasulloGRH.openStrip a b := by
    intro s hs
    exact ⟨by linarith [hs.1.1], by linarith [hs.1.2]⟩
  obtain ⟨M,hM⟩ := hK.bddAbove_image (hF.continuousOn.norm.mono hsub)
  obtain ⟨B,hB,h⟩ := clip_bound (S := {s : ℂ | s.re ∈ Icc (a+ε) (b-ε)}) hC
    (fun s hs => hY s hs.1 hs.2) (fun s hs hIm => hM (mem_image_of_mem _ (show s ∈ K from ⟨hs, abs_le.mp hIm⟩)))
  exact ⟨B,hB, fun s hl hr => h s ⟨hl,hr⟩⟩

private theorem hardy_vanish {F : ℂ → ℂ} {d B : ℝ}
    (_hF : ∀ s : ℂ, s.re ≤ d → DifferentiableAt ℂ F s)
    (hbound : ∀ s : ℂ, s.re ≤ d → ‖F s‖ ≤ B/(1+s.im^2))
    (z : ℂ) : Tendsto (fun x : ℝ => MasulloGRH.verticalLineIntegral (fun s => F s/(s-z)) x) atBot (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hden : Tendsto (fun x : ℝ => z.re-x) atBot atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_left atBot z.re tendsto_neg_atBot_atTop
  have hlim := tendsto_const_nhds.div_atTop (a := ∫ y : ℝ, B*(1+y^2)⁻¹) hden
  apply squeeze_zero' (.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [eventually_lt_atBot z.re,eventually_le_atBot d] with x hx hxd
  have h := norm_integral_le_of_norm_le ((integrable_inv_one_add_sq.const_mul B).div_const (z.re-x))
    (.of_forall (fun y : ℝ => show ‖F ((x:ℂ)+y*I)/((x:ℂ)+y*I-z)‖ ≤ B*(1+y^2)⁻¹/(z.re-x) from by
      rw [norm_div]
      have hd : z.re-x ≤ ‖(x:ℂ)+y*I-z‖ := by
        have hr := abs_re_le_norm ((x:ℂ)+y*I-z)
        simp at hr
        linarith [neg_le_abs (x-z.re)]
      calc
        _ ≤ ‖F ((x:ℂ)+y*I)‖/(z.re-x) := div_le_div_of_nonneg_left (norm_nonneg _) (sub_pos.mpr hx) hd
        _ ≤ _ := div_le_div_of_nonneg_right (by simpa only [div_eq_mul_inv, add_im, ofReal_im, zero_add,mul_I_im,ofReal_re] using (hbound ((x:ℂ)+y*I) (by simpa using hxd))) (sub_pos.mpr hx).le))
  simpa [MasulloGRH.verticalLineIntegral, norm_mul,integral_div] using h
private theorem cauchy_pair
    (hres : ∀ {f : ℂ → ℂ} {z w p A : ℂ},
      z.re ≤ w.re → z.im ≤ w.im → Complex.Rectangle z w ∈ 𝓝 p →
        HolomorphicOn f (Complex.Rectangle z w \ {p}) →
        (f - (fun s ↦ A / (s - p))) =O[𝓝[≠] p] (1 : ℂ → ℂ) →
        RectangleIntegral' f z w = A) :
    (∀ (a b ε : ℝ) (F : ℂ → ℂ), 0 < ε → a+ε < b-ε →
      DifferentiableOn ℂ F (MasulloGRH.openStrip a b) →
      MasulloGRH.UniformlySchwartzOnStrip F a b → ∀ z : ℂ, z.re ≠ a+ε → z.re ≠ b-ε →
      let g := fun s : ℂ => F s/(s-z)
      MasulloGRH.VerticalLineIntegrable g (a+ε) ∧ MasulloGRH.VerticalLineIntegrable g (b-ε) ∧
      (1/(2*Real.pi*I))*(MasulloGRH.verticalLineIntegral g (b-ε) - MasulloGRH.verticalLineIntegral g (a+ε)) =
        if a+ε < z.re ∧ z.re < b-ε then F z else 0) ∧
    (∀ (b d : ℝ) (F : ℂ → ℂ), d < b → DifferentiableOn ℂ F {s : ℂ | s.re < b} →
      MasulloGRH.SchwartzOnLeftHalfPlane F b →
      (∀ Y : ℝ, ∃ M : ℝ, ∀ s : ℂ, s.re ≤ d → |s.im| ≤ Y → ‖F s‖ ≤ M) →
      ∀ z : ℂ, z.re ≠ d → let g := fun s : ℂ => F s/(s-z)
        MasulloGRH.VerticalLineIntegrable g d ∧
          (1/(2*Real.pi*I))*MasulloGRH.verticalLineIntegral g d = if z.re < d then F z else 0) := by
  constructor
  · intro a b ε F hε hw hF hS z hl hr g
    obtain ⟨B,hB,h⟩ := abs_channel_of_strip hε hw hF hS
    have hopen : IsOpen (MasulloGRH.openStrip a b) :=
      (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
    have hd (s : ℂ) (hl : a+ε ≤ s.re) (hr : s.re ≤ b-ε) : DifferentiableAt ℂ F s :=
      hF.differentiableAt (hopen.mem_nhds ⟨by linarith,by linarith⟩)
    exact ⟨strip_line le_rfl hw.le hd h z hl.symm,strip_line hw.le le_rfl hd h z hr.symm,
      strip_cauchy hres hw hB hd h hl.symm hr.symm⟩
  · intro b d F hd hF hS hchannel z hz g
    obtain ⟨C,hC,Y,hY⟩ := hS (b-d) (sub_pos.mpr hd) 2 (by norm_num)
    obtain ⟨M,hM⟩ := hchannel (max Y 1)
    obtain ⟨B,hB,hbound⟩ := clip_bound (S := {s : ℂ | s.re ≤ d}) hC
      (fun s hs => hY s (by simpa using hs)) (fun s hs => hM s hs)
    have hdiff (s : ℂ) (h : s.re ≤ d) : DifferentiableAt ℂ F s :=
      hF.differentiableAt ((isOpen_lt continuous_re continuous_const).mem_nhds (h.trans_lt hd))
    refine ⟨strip_line (l := d) (r := d) le_rfl le_rfl (fun s _ hr => hdiff s hr)
      (fun s _ hr => hbound s hr) z hz.symm, ?_⟩
    let c : ℂ := 1/(2*Real.pi*I)
    have hlim := (tendsto_const_nhds (x := MasulloGRH.verticalLineIntegral g d) |>.sub
      (hardy_vanish hdiff hbound z)).const_mul c
    have hid : ∀ᶠ x : ℝ in atBot, c*(MasulloGRH.verticalLineIntegral g d -
        MasulloGRH.verticalLineIntegral g x) = if z.re < d then F z else 0 := by
      filter_upwards [eventually_lt_atBot d,eventually_lt_atBot z.re] with x hxd hxz
      simpa [c,g,hxz] using strip_cauchy hres hxd hB (fun s _ hr => hdiff s hr)
        (fun s _ hr => hbound s hr) (z := z) hxz.ne hz.symm
    exact tendsto_nhds_unique (by simpa only [sub_zero] using hlim)
      (tendsto_const_nhds.congr' (hid.mono (fun _ h => h.symm)))
end C11Cauchy

theorem solution :
    (∀ (a b ε : ℝ) (F : ℂ → ℂ), 0 < ε → a+ε < b-ε →
      DifferentiableOn ℂ F (MasulloGRH.openStrip a b) →
      MasulloGRH.UniformlySchwartzOnStrip F a b → ∀ z : ℂ, z.re ≠ a+ε → z.re ≠ b-ε →
      let g := fun s : ℂ => F s/(s-z)
      MasulloGRH.VerticalLineIntegrable g (a+ε) ∧ MasulloGRH.VerticalLineIntegrable g (b-ε) ∧
      (1/(2*Real.pi*I))*(MasulloGRH.verticalLineIntegral g (b-ε) - MasulloGRH.verticalLineIntegral g (a+ε)) =
        if a+ε < z.re ∧ z.re < b-ε then F z else 0) ∧
    (∀ (b d : ℝ) (F : ℂ → ℂ), d < b → DifferentiableOn ℂ F {s : ℂ | s.re < b} →
      MasulloGRH.SchwartzOnLeftHalfPlane F b →
      (∀ Y : ℝ, ∃ M : ℝ, ∀ s : ℂ, s.re ≤ d → |s.im| ≤ Y → ‖F s‖ ≤ M) →
      ∀ z : ℂ, z.re ≠ d → let g := fun s : ℂ => F s/(s-z)
        MasulloGRH.VerticalLineIntegrable g d ∧
          (1/(2*Real.pi*I))*MasulloGRH.verticalLineIntegral g d = if z.re < d then F z else 0) := C11Cauchy.cauchy_pair (fun h₁ h₂ h₃ h₄ h₅ => ResidueTheoremOnRectangleWithSimplePole_prime h₁ h₂ h₃ h₄ h₅)
