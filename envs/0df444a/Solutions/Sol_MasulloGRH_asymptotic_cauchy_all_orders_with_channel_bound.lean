-- Prove2me | solution 1 for MasulloGRH.asymptotic_cauchy_all_orders_with_channel_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T04:51:42.168152+00:00
-- url     : https://prove2.me/submissions/1840d78d-729e-45e1-822d-68d5a4c606d1

import Theorems.Thm_MasulloGRH_asymptotic_cauchy_value_formula_with_channel_bound
import Definitions.Def_MasulloGRH_MellinRpos
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Tactic.NormNum

open MeasureTheory Set Filter Complex Asymptotics
open scoped Topology

private theorem cauchy_parameter_deriv (Φ : ℂ → ℂ) (d : ℝ) (hL : MasulloGRH.VerticalLineIntegrable Φ d)
    (n : ℕ) (z : ℂ) (hz : z.re ≠ d) :
    HasDerivAt (fun w : ℂ => MasulloGRH.verticalLineIntegral (fun s => Φ s / (s-w)^(n+1)) d)
      (((n+1:ℕ):ℂ) * MasulloGRH.verticalLineIntegral (fun s => Φ s / (s-z)^(n+2)) d) z := by
  let L (t : ℝ) : ℂ := d+t*I
  let G (w : ℂ) (t : ℝ) := Φ (L t)/(L t-w)^(n+1)
  let P (w : ℂ) (t : ℝ) := ((n+1:ℕ):ℂ)*Φ (L t)/(L t-w)^(n+2)
  let δ := |d-z.re|/2
  have hδ : 0 < δ := half_pos (abs_pos.mpr (sub_ne_zero.mpr hz.symm))
  let S := {w : ℂ | δ < |d-w.re|}
  have hs : S ∈ 𝓝 z := by
    have hopen : IsOpen S := isOpen_lt continuous_const (continuous_const.sub continuous_re).abs
    exact hopen.mem_nhds (show δ < |d-z.re| by exact half_lt_self (abs_pos.mpr (sub_ne_zero.mpr hz.symm)))
  have hLcont : Continuous L := by dsimp [L]; fun_prop
  have hbase : Integrable (fun t => Φ (L t)) := hL
  have hden (w : ℂ) (hw : w ∈ S) (t : ℝ) : δ < ‖L t-w‖ := by
    exact lt_of_lt_of_le hw (by simpa [L] using abs_re_le_norm (L t-w))
  have hmeas (w : ℂ) : AEStronglyMeasurable (G w) := (hbase.aestronglyMeasurable.aemeasurable.div
    (((hLcont.sub continuous_const).pow (n+1)).aemeasurable)).aestronglyMeasurable
  have hmP : AEStronglyMeasurable (P z) := ((hbase.aestronglyMeasurable.const_mul _).aemeasurable.div
    (((hLcont.sub continuous_const).pow (n+2)).aemeasurable)).aestronglyMeasurable
  have hmain : Integrable (G z) := by
    apply (hbase.norm.div_const (δ^(n+1))).mono' (hmeas z)
    filter_upwards with t
    simp only [G,norm_div,norm_pow]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (pow_le_pow_left₀ hδ.le ((hden z (mem_of_mem_nhds hs) t).le) _)
  have hdiff (w : ℂ) (hw : w ∈ S) (t : ℝ) : HasDerivAt (fun w => G w t) (P w t) w := by
    have hne : L t-w ≠ 0 := norm_pos_iff.mp (hδ.trans (hden w hw t))
    have h := (hasDerivAt_const w (Φ (L t))).div (((hasDerivAt_const w (L t)).sub (hasDerivAt_id w)).pow (n+1))
      (pow_ne_zero _ hne)
    apply h.congr_deriv
    dsimp [P]
    field_simp
    ring
  have hbound (w : ℂ) (hw : w ∈ S) (t : ℝ) :
      ‖P w t‖ ≤ (((n+1:ℕ):ℝ)*‖Φ (L t)‖) / δ^(n+2) := by
    simp only [P,norm_div,norm_mul,norm_pow,Complex.norm_natCast]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ hδ.le ((hden w hw t).le) _)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (.of_forall hmeas) hmain hmP (.of_forall (fun t w hw => hbound w hw t))
    ((hbase.norm.const_mul ((n+1:ℕ):ℝ)).div_const (δ^(n+2))) (.of_forall (fun t w hw => hdiff w hw t))
  apply (h.2.const_mul I).congr_deriv
  unfold MasulloGRH.verticalLineIntegral P L
  simp_rw [mul_div_assoc, integral_const_mul]
  ring

private theorem line_iter_int (F : ℂ → ℂ) (d : ℝ) (hL : MasulloGRH.VerticalLineIntegrable F d)
    (n : ℕ) (z : ℂ) (hz : z.re ≠ d) :
    MasulloGRH.VerticalLineIntegrable (fun s => F s/(s-z)^(n+1)) d := by
  let L (t : ℝ) : ℂ := d+t*I
  have ht : Continuous L := by dsimp [L];fun_prop
  have hf : Integrable (fun t => F (L t)) := hL
  apply (hf.norm.div_const (|d-z.re|^(n+1))).mono'
    ((hf.aestronglyMeasurable.aemeasurable.div (((ht.sub continuous_const).pow (n+1)).aemeasurable)).aestronglyMeasurable)
  filter_upwards with t
  have hpos := abs_pos.mpr (sub_ne_zero.mpr hz.symm)
  have hden : |d-z.re| ≤ ‖L t-z‖ := by simpa [L] using abs_re_le_norm (L t-z)
  change ‖F (L t)/(L t-z)^(n+1)‖ ≤ _
  rw [norm_div,norm_pow]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (pow_le_pow_left₀ hpos.le hden _)

private noncomputable def Vseq (F : ℂ → ℂ) (d : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ((n.factorial : ℂ)/(2*Real.pi*I)) * MasulloGRH.verticalLineIntegral (fun s => F s/(s-z)^(n+1)) d

private theorem Vseq_der (F : ℂ → ℂ) (d : ℝ) (hL : MasulloGRH.VerticalLineIntegrable F d)
    (n : ℕ) (z : ℂ) (hz : z.re ≠ d) : HasDerivAt (Vseq F d n) (Vseq F d (n+1) z) z := by
  apply ((cauchy_parameter_deriv F d hL n z hz).const_mul ((n.factorial : ℂ)/(2*Real.pi*I))).congr_deriv
  dsimp only [Vseq]
  rw [Nat.factorial_succ, Nat.cast_mul]
  ring

private theorem lift_local (G : ℕ → ℂ → ℂ) (F : ℂ → ℂ) (z : ℂ)
    (h₀ : G 0 =ᶠ[𝓝 z] F)
    (hstep : ∀ n, ∀ᶠ w in 𝓝 z, HasDerivAt (G n) (G (n+1) w) w) (n : ℕ) :
    G n z = iteratedDeriv n F z := by
  suffices e : G n =ᶠ[𝓝 z] iteratedDeriv n F by exact e.eq_of_nhds
  induction n with
  | zero => simpa using h₀
  | succ n ih =>
    rw [iteratedDeriv_succ]
    filter_upwards [hstep n, ih.deriv] with w hw he
    exact hw.deriv.symm.trans he

private theorem stable_side {z : ℂ} {d : ℝ} (hz : z.re ≠ d) :
    ∀ᶠ w in 𝓝 z, w.re ≠ d ∧ (w.re < d ↔ z.re < d) ∧ (d < w.re ↔ d < z.re) := by
  rcases lt_or_gt_of_ne hz with h | h
  · filter_upwards [continuous_re.continuousAt.eventually_lt_const h] with w hw
    exact ⟨hw.ne, iff_of_true hw h,iff_of_false (not_lt.mpr hw.le) (not_lt.mpr h.le)⟩
  · filter_upwards [continuous_re.continuousAt.eventually_const_lt h] with w hw
    exact ⟨hw.ne', iff_of_false (not_lt.mpr hw.le) (not_lt.mpr h.le), iff_of_true hw h⟩

private theorem line_integrable_on_strip (a b ε : ℝ) (F : ℂ → ℂ) (hε : 0 < ε) (hw : a+ε < b-ε)
    (hF : DifferentiableOn ℂ F (MasulloGRH.openStrip a b)) (hS : MasulloGRH.UniformlySchwartzOnStrip F a b)
    (d : ℝ) (had : a+ε ≤ d) (hdb : d ≤ b-ε) : MasulloGRH.VerticalLineIntegrable F d := by
  obtain ⟨C,hC,Y,hY⟩ := hS ε hε hw 2 (by norm_num)
  let line (y : ℝ) : ℂ := d+y*I
  have hcont : Continuous (fun y => F (line y)) := by
    refine hF.continuousOn.comp_continuous (by dsimp [line];fun_prop) ?_
    intro y
    exact ⟨by simpa [line] using (show a < d by linarith), by simpa [line] using (show d < b by linarith)⟩
  have ht (y : ℝ) (hy : max Y 1 ≤ |y|) : ‖F (line y)‖ ≤ (2*C)*‖(1+y^2)⁻¹‖ := by
    have hb := hY (line y) (by simpa [line] using had) (by simpa [line] using hdb) (by simpa [line] using (le_max_left Y 1).trans hy)
    calc
      _ ≤ C/y^2 := by simpa [line] using hb
      _ ≤ _ := by
        have hy1 := (le_max_right Y 1).trans hy
        have hy2 : 1 ≤ y^2 := by nlinarith [sq_abs y,mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1) hy1]
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← div_eq_mul_inv]
        apply (div_le_div_iff₀ (by positivity : 0 < y^2) (by positivity)).mpr
        nlinarith [mul_le_mul_of_nonneg_left hy2 hC.le]
  change Integrable (fun y => F (line y))
  apply hcont.locallyIntegrable.integrable_of_isBigO_atBot_atTop
    (g := fun y : ℝ => (1+y^2)⁻¹) (g' := fun y : ℝ => (1+y^2)⁻¹)
  · apply isBigO_iff.mpr
    refine ⟨2*C, ?_⟩
    filter_upwards [eventually_le_atBot (-max Y 1)] with y hy
    exact ht y (by linarith [neg_le_abs y])
  · exact integrable_inv_one_add_sq.integrableAtFilter _
  · apply isBigO_iff.mpr
    refine ⟨2*C, ?_⟩
    filter_upwards [eventually_ge_atTop (max Y 1)] with y hy
    exact ht y (by linarith [le_abs_self y])
  · exact integrable_inv_one_add_sq.integrableAtFilter _

open MasulloGRH
private theorem nf_cauchy_lineL1 (Φ : ℂ → ℂ) (b d : ℝ) (hd : d < b)
    (hc : ContinuousOn Φ {z : ℂ | z.re < b}) (hS : SchwartzOnLeftHalfPlane Φ b) :
    VerticalLineIntegrable Φ d := by
  let F : ℝ → ℂ := fun y => Φ (d+y*Complex.I)
  have hline : Continuous F := by
    apply hc.comp_continuous (f := fun y : ℝ => (d : ℂ) + y*Complex.I)
    · fun_prop
    · intro y
      simpa using hd
  obtain ⟨C,hC,Y,hY⟩ := hS (b-d) (sub_pos.mpr hd) 2 (by norm_num)
  have hB (y : ℝ) (hy : max Y 1 ≤ |y|) :
      ‖F y‖ ≤ (2*C) * ‖(1+y^2)⁻¹‖ := by
    have ht := hY ((d : ℂ)+y*Complex.I) (by simp) (by simpa using (le_max_left Y 1).trans hy)
    have hy1 := (le_max_right Y 1).trans hy
    change ‖Φ _‖ ≤ _
    calc
      _ ≤ C / y^2 := by simpa using ht
      _ ≤ _ := by
        have hy2 : 1 ≤ y^2 := by nlinarith [sq_abs y, mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1) hy1]
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← div_eq_mul_inv]
        apply (div_le_div_iff₀ (by positivity : 0 < y^2) (by positivity)).mpr
        nlinarith [mul_le_mul_of_nonneg_left hy2 hC.le]
  unfold VerticalLineIntegrable
  change Integrable F
  apply hline.locallyIntegrable.integrable_of_isBigO_atBot_atTop
    (g := fun y : ℝ => (1+y^2)⁻¹) (g' := fun y : ℝ => (1+y^2)⁻¹)
  · apply isBigO_iff.mpr
    refine ⟨2*C, ?_⟩
    filter_upwards [eventually_le_atBot (-max Y 1)] with y hy
    exact hB y (by linarith [neg_le_abs y])
  · exact integrable_inv_one_add_sq.integrableAtFilter _
  · apply isBigO_iff.mpr
    refine ⟨2*C, ?_⟩
    filter_upwards [eventually_ge_atTop (max Y 1)] with y hy
    exact hB y (hy.trans (le_abs_self _))
  · exact integrable_inv_one_add_sq.integrableAtFilter _

private theorem lift_two (Φ : ℂ → ℂ) {l r : ℝ} (hl : VerticalLineIntegrable Φ l)
    (hr : VerticalLineIntegrable Φ r)
    (hval : ∀ w : ℂ, w.re ≠ l → w.re ≠ r → Vseq Φ r 0 w - Vseq Φ l 0 w =
      if l < w.re ∧ w.re < r then Φ w else 0) (n : ℕ) (z : ℂ) (hzl : z.re ≠ l) (hzr : z.re ≠ r) :
    Vseq Φ r n z - Vseq Φ l n z = if l < z.re ∧ z.re < r then iteratedDeriv n Φ z else 0 := by
  let G (n : ℕ) (w : ℂ) := Vseq Φ r n w - Vseq Φ l n w
  let F (w : ℂ) := if l < z.re ∧ z.re < r then Φ w else 0
  have h0 : G 0 =ᶠ[𝓝 z] F := by
    filter_upwards [stable_side hzl,stable_side hzr] with w hw hv
    simpa [G,F,hw.2.2,hv.2.1] using hval w hw.1 hv.1
  have hd (n : ℕ) : ∀ᶠ w in 𝓝 z, HasDerivAt (G n) (G (n+1) w) w := by
    filter_upwards [stable_side hzl,stable_side hzr] with w hw hv
    exact (Vseq_der Φ r hr n w hv.1).sub (Vseq_der Φ l hl n w hw.1)
  have he := lift_local G F z h0 hd n
  by_cases h : l < z.re ∧ z.re < r
  · simpa [G,F,h] using he
  · simpa [G,F,h] using he

private theorem lift_one (Φ : ℂ → ℂ) {d : ℝ} (hv : VerticalLineIntegrable Φ d)
    (hval : ∀ w : ℂ, w.re ≠ d → Vseq Φ d 0 w = if w.re < d then Φ w else 0)
    (n : ℕ) (z : ℂ) (hz : z.re ≠ d) :
    Vseq Φ d n z = if z.re < d then iteratedDeriv n Φ z else 0 := by
  let F (w : ℂ) := if z.re < d then Φ w else 0
  have h0 : Vseq Φ d 0 =ᶠ[𝓝 z] F := by
    filter_upwards [stable_side hz] with w hw
    simpa [F,hw.2.1] using hval w hw.1
  have hd (n : ℕ) : ∀ᶠ w in 𝓝 z, HasDerivAt (Vseq Φ d n) (Vseq Φ d (n+1) w) w := by
    filter_upwards [stable_side hz] with w hw
    exact Vseq_der Φ d hv n w hw.1
  have he := lift_local (Vseq Φ d) F z h0 hd n
  by_cases h : z.re < d
  · simpa [F,h] using he
  · simpa [F,h] using he

theorem solution :
(∀ (a b ε : ℝ) (Φ : ℂ → ℂ), 0 < ε → a+ε < b-ε →
      DifferentiableOn ℂ Φ (MasulloGRH.openStrip a b) →
      MasulloGRH.UniformlySchwartzOnStrip Φ a b → ∀ (N : ℕ) (z : ℂ), z.re ≠ a+ε → z.re ≠ b-ε →
      let g := fun s : ℂ => Φ s/(s-z)^(N+1)
      MasulloGRH.VerticalLineIntegrable g (a+ε) ∧ MasulloGRH.VerticalLineIntegrable g (b-ε) ∧
      ((N.factorial:ℂ)/(2*Real.pi*I))*(MasulloGRH.verticalLineIntegral g (b-ε) -
        MasulloGRH.verticalLineIntegral g (a+ε)) =
        if a+ε < z.re ∧ z.re < b-ε then iteratedDeriv N Φ z else 0) ∧
    (∀ (b d : ℝ) (Φ : ℂ → ℂ), d < b → DifferentiableOn ℂ Φ {s : ℂ | s.re < b} →
      MasulloGRH.SchwartzOnLeftHalfPlane Φ b →
      (∀ Y : ℝ, ∃ M : ℝ, ∀ s : ℂ, s.re ≤ d → |s.im| ≤ Y → ‖Φ s‖ ≤ M) →
      ∀ (N : ℕ) (z : ℂ), z.re ≠ d → let g := fun s : ℂ => Φ s/(s-z)^(N+1)
        MasulloGRH.VerticalLineIntegrable g d ∧
          ((N.factorial:ℂ)/(2*Real.pi*I))*MasulloGRH.verticalLineIntegral g d =
            if z.re < d then iteratedDeriv N Φ z else 0) := by
  constructor
  · intro a b ε Φ hε hw hΦ hS N z hzl hzr g
    have hl := line_integrable_on_strip a b ε Φ hε hw hΦ hS (a+ε) le_rfl hw.le
    have hr := line_integrable_on_strip a b ε Φ hε hw hΦ hS (b-ε) hw.le le_rfl
    refine ⟨line_iter_int Φ _ hl N z hzl,line_iter_int Φ _ hr N z hzr,?_⟩
    have hval (w : ℂ) (hw₁ : w.re ≠ a+ε) (hw₂ : w.re ≠ b-ε) :=
      (MasulloGRH.asymptotic_cauchy_value_formula_with_channel_bound.1 a b ε Φ hε hw hΦ hS w hw₁ hw₂).2.2
    have h := lift_two Φ hl hr (fun w hw₁ hw₂ => by simpa [Vseq,mul_sub] using hval w hw₁ hw₂) N z hzl hzr
    simpa only [g,Vseq,mul_sub] using h
  · intro b d Φ hd hΦ hS hc N z hz g
    have hL := nf_cauchy_lineL1 Φ b d hd hΦ.continuousOn hS
    refine ⟨line_iter_int Φ d hL N z hz,?_⟩
    apply lift_one Φ hL _ N z hz
    intro w hw
    simpa [Vseq] using (MasulloGRH.asymptotic_cauchy_value_formula_with_channel_bound.2 b d Φ hd hΦ hS hc w hw).2
