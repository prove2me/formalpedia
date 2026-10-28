-- Prove2me | solution 2 for GraphonGames.Stability.theorem_3_20_stability
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:54:32.620011+00:00
-- url     : https://prove2.me/submissions/5098e090-f1c4-4686-bd15-ce50710e5bc2

import Mathlib
import Definitions.Def_GraphonGames_Stability_Setting
import Theorems.Thm_GraphonGames_Stability_lemma_3_7_best_response_lipschitz

-- carved verbatim out of submission 9a4f07ff-9348-4353-85c1-ef785fd88d7a, lines 488-586

section
open MeasureTheory
open scoped ENNReal
open GraphonGames
open GraphonGames.Stability

lemma l2_sq {A : Type*} [MeasurableSpace A] (μ : Measure A) (f : A → ℝ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] using
    (eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := f) (p := 2) (by norm_num))

lemma kernel_bound (w : I → I → ℝ) (hw : IsGraphon w) (g : I → ℝ)
    (hg : MemLp g 2 volume) :
    eLpNorm (graphonApply w g) 2 volume ≤
      eLpNorm (Function.uncurry w) 2 (volume : Measure (I × I)) * eLpNorm g 2 volume := by
  have hrow (x : I) : Measurable (w x) :=
    hw.1.comp (measurable_const.prodMk measurable_id)
  have hpoint (x : I) : ‖graphonApply w g x‖ₑ ≤
      eLpNorm (w x) 2 volume * eLpNorm g 2 volume := by
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume
      (Real.holderConjugate_iff.mpr (by norm_num : (1 : ℝ) < 2 ∧ (2 : ℝ)⁻¹ + 2⁻¹ = 1))
      (hrow x).enorm.aemeasurable hg.1.enorm
    simpa only [Pi.mul_apply, enorm_mul,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞), ENNReal.toReal_ofNat] using h
  have hsq : eLpNorm (graphonApply w g) 2 volume ^ 2 ≤
      (eLpNorm (Function.uncurry w) 2 (volume : Measure (I × I)) * eLpNorm g 2 volume) ^ 2 := by
    rw [l2_sq]
    calc
      (∫⁻ x, ‖graphonApply w g x‖ₑ ^ 2) ≤
          ∫⁻ x, (eLpNorm (w x) 2 volume * eLpNorm g 2 volume) ^ 2 :=
        lintegral_mono fun x => ENNReal.pow_le_pow_left (hpoint x)
      _ = (∫⁻ x, ∫⁻ y, ‖w x y‖ₑ ^ 2) * eLpNorm g 2 volume ^ 2 := by
        simp_rw [mul_pow, l2_sq (volume : Measure I) (w _)]
        exact lintegral_mul_const _ (hw.1.enorm.pow_const 2).lintegral_prod_right
      _ = (eLpNorm (Function.uncurry w) 2 (volume : Measure (I × I)) *
          eLpNorm g 2 volume) ^ 2 := by
        rw [mul_pow, l2_sq (volume : Measure (I × I)) (Function.uncurry w)]
        congr 1
        exact (lintegral_prod _ (hw.1.enorm.pow_const 2).aemeasurable).symm
  apply (ENNReal.rpow_le_rpow_iff (z := 2) (by norm_num)).mp
  simpa only [ENNReal.rpow_two] using hsq

lemma graphon_memLp (w : I → I → ℝ) (hw : IsGraphon w) (g : I → ℝ)
    (hg : MemLp g 2 volume) : MemLp (graphonApply w g) 2 volume := by
  refine ⟨?_, (kernel_bound w hw g hg).trans_lt (ENNReal.mul_lt_top hw.2.2.2 hg.2)⟩
  exact (hw.1.aestronglyMeasurable.mul (hg.comp_snd (volume : Measure I)).1).integral_prod_right'

lemma opNorm_finite (w : I → I → ℝ) (hw : IsGraphon w) : opNorm w < ∞ := by
  refine lt_of_le_of_lt ?_ hw.2.2.2
  apply iSup_le
  intro g
  apply iSup_le
  intro hg
  simpa only [hg.2, mul_one] using kernel_bound w hw g hg.1

lemma apply_smul (w : I → I → ℝ) (g : I → ℝ) (c : ℝ) :
    graphonApply w (c • g) = c • graphonApply w g := by
  funext x
  simp only [graphonApply, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (w x _ ) c, integral_const_mul]

lemma operator_bound (w : I → I → ℝ) (hw : IsGraphon w) (g : I → ℝ)
    (hg : MemLp g 2 volume) :
    eLpNorm (graphonApply w g) 2 volume ≤ opNorm w * eLpNorm g 2 volume := by
  by_cases h0 : eLpNorm g 2 volume = 0
  · simpa only [h0, mul_zero] using kernel_bound w hw g hg
  let r := (eLpNorm g 2 volume).toReal
  have hr : 0 < r := ENNReal.toReal_pos h0 hg.2.ne
  have he : ‖r⁻¹‖ₑ = (eLpNorm g 2 volume)⁻¹ := by
    rw [← ofReal_norm, Real.norm_of_nonneg (inv_nonneg.mpr hr.le),
      ENNReal.ofReal_inv_of_pos hr, ENNReal.ofReal_toReal hg.2.ne]
  have hunit : eLpNorm (r⁻¹ • g) 2 volume = 1 := by
    rw [eLpNorm_const_smul, he, ENNReal.inv_mul_cancel h0 hg.2.ne]
  have hb : eLpNorm (graphonApply w (r⁻¹ • g)) 2 volume ≤ opNorm w :=
    le_iSup_of_le (r⁻¹ • g) (le_iSup_of_le ⟨hg.const_smul _, hunit⟩ le_rfl)
  rw [apply_smul, eLpNorm_const_smul, he] at hb
  calc
    eLpNorm (graphonApply w g) 2 volume = eLpNorm g 2 volume *
        ((eLpNorm g 2 volume)⁻¹ * eLpNorm (graphonApply w g) 2 volume) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel h0 hg.2.ne, one_mul]
    _ ≤ eLpNorm g 2 volume * opNorm w := mul_le_mul_of_nonneg_left hb zero_le
    _ = _ := mul_comm _ _

lemma b_point (b : ℝ → ℝ → ℝ) (μ0 : Measure ℝ) (cα cz : ℝ)
    (h1 : GraphonGames.Existence.Asm1 b μ0 cα cz) (a z a' z' : ℝ) :
    |b a z - b a' z'| ≤ Real.sqrt cα * |a-a'| + Real.sqrt cz * |z-z'| := by
  have h := h1.2.2.1 a z a' z'
  have ha := Real.sq_sqrt h1.1
  have hz := Real.sq_sqrt h1.2.1
  have hsq1 : (Real.sqrt cα * |a-a'|)^2 = cα*(a-a')^2 := by
    rw [mul_pow, ha, sq_abs]
  have hsq2 : (Real.sqrt cz * |z-z'|)^2 = cz*(z-z')^2 := by
    rw [mul_pow, hz, sq_abs]
  have hn1 : 0 ≤ Real.sqrt cα * |a-a'| := by positivity
  have hn2 : 0 ≤ Real.sqrt cz * |z-z'| := by positivity
  have hab := sq_abs (b a z-b a' z')
  nlinarith [abs_nonneg (b a z-b a' z'), mul_nonneg hn1 hn2]

lemma b_lipschitz (b : ℝ → ℝ → ℝ) (μ0 : Measure ℝ) (cα cz : ℝ)
    (h1 : GraphonGames.Existence.Asm1 b μ0 cα cz) :
    LipschitzWith ⟨Real.sqrt cα + Real.sqrt cz, by positivity⟩ (Function.uncurry b) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  change |b p.1 p.2-b q.1 q.2| ≤ (Real.sqrt cα+Real.sqrt cz)*dist p q
  have ha : |p.1-q.1| ≤ dist p q := le_max_left _ _
  have hz : |p.2-q.2| ≤ dist p q := le_max_right _ _
  calc
    _ ≤ Real.sqrt cα*|p.1-q.1| + Real.sqrt cz*|p.2-q.2| := b_point b μ0 cα cz h1 _ _ _ _
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left ha (Real.sqrt_nonneg cα),
      mul_le_mul_of_nonneg_left hz (Real.sqrt_nonneg cz)]

lemma b_memLp (b : ℝ → ℝ → ℝ) (μ0 : Measure ℝ) (cα cz : ℝ)
    (h1 : GraphonGames.Existence.Asm1 b μ0 cα cz) (a z : I → ℝ)
    (ha : MemLp a 2 volume) (hz : MemLp z 2 volume) :
    MemLp (fun x => b (a x) (z x)) 2 volume := by
  have hp : MemLp (fun x => (a x,z x)) 2 volume := memLp_prod_iff.mpr ⟨ha,hz⟩
  have hl : LipschitzWith ⟨Real.sqrt cα+Real.sqrt cz, by positivity⟩
      (fun p : ℝ × ℝ => b p.1 p.2-b 0 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    simpa only [dist_sub_right, Function.uncurry] using (b_lipschitz b μ0 cα cz h1).dist_le_mul p q
  have hh := hl.comp_memLp (by simp) hp
  have hc : MemLp (fun _ : I => b 0 0) 2 volume := memLp_const _
  convert hh.add hc using 1
  ext x
  simp [Function.comp_def]

lemma b_difference_bound (b : ℝ → ℝ → ℝ) (μ0 : Measure ℝ) (cα cz : ℝ)
    (h1 : GraphonGames.Existence.Asm1 b μ0 cα cz) (a1 a2 z1 z2 : I → ℝ)
    (ha1 : MemLp a1 2 volume) (ha2 : MemLp a2 2 volume)
    (hz1 : MemLp z1 2 volume) (hz2 : MemLp z2 2 volume) :
    eLpNorm (fun x => b (a1 x) (z1 x)-b (a2 x) (z2 x)) 2 volume ≤
      ENNReal.ofReal (Real.sqrt cα) * eLpNorm (a1-a2) 2 volume +
      ENNReal.ofReal (Real.sqrt cz) * eLpNorm (z1-z2) 2 volume := by
  let A : I → ℝ := fun x => ‖(a1-a2) x‖
  let Z : I → ℝ := fun x => ‖(z1-z2) x‖
  have ha : MemLp A 2 volume := (ha1.sub ha2).norm
  have hz : MemLp Z 2 volume := (hz1.sub hz2).norm
  calc
    _ ≤ eLpNorm (Real.sqrt cα • A + Real.sqrt cz • Z) 2 volume := by
      apply eLpNorm_mono_ae
      filter_upwards [] with x
      have hn : 0 ≤ (Real.sqrt cα • A + Real.sqrt cz • Z) x := by
        dsimp [A,Z]; positivity
      rw [Real.norm_of_nonneg hn]
      exact b_point b μ0 cα cz h1 _ _ _ _
    _ ≤ eLpNorm (Real.sqrt cα • A) 2 volume + eLpNorm (Real.sqrt cz • Z) 2 volume :=
      eLpNorm_add_le (ha.const_smul _).1 (hz.const_smul _).1 (by norm_num)
    _ = _ := by
      simp only [eLpNorm_const_smul, A, Z, eLpNorm_norm, ← ofReal_norm,
        Real.norm_of_nonneg (Real.sqrt_nonneg _)]

end

section
open MeasureTheory
open scoped ENNReal
open GraphonGames.Stability
set_option autoImplicit false
open GraphonGames

lemma graphon_difference (w w' : I → I → ℝ) (hw : IsGraphon w) (hw' : IsGraphon w') :
    IsGraphon (w-w') := by
  exact ⟨hw.1.sub hw'.1,fun x y => by simp only [Pi.sub_apply,hw.2.1 x y,hw'.2.1 x y],
    hw.2.2.sub hw'.2.2⟩

end

section
open MeasureTheory
open scoped ENNReal
open GraphonGames.Stability
set_option autoImplicit false
open GraphonGames.Existence
variable {J : ℝ → ℝ → ℝ} {ℓc ℓJ : ℝ} (h4 : Asm4 J ℓc ℓJ)
include h4

lemma strongly_convex (z : ℝ) : StrongConvexOn Set.univ ℓc (fun a => J a z) := by
  refine ⟨convex_univ, ?_⟩
  intro a ha b hb u v hu hv huv
  have hv' : v = 1-u := by linarith
  have h := h4.2.2.2.1 a b z u hu (by linarith)
  simp only [smul_eq_mul, Real.norm_eq_abs]
  rw [hv']
  convert h using 1 <;> ring

lemma differentiable (z : ℝ) : Differentiable ℝ (fun a => J a z) :=
  (h4.2.2.1 z).differentiable (by norm_num)

lemma convex (z : ℝ) : ConvexOn ℝ Set.univ (fun a => J a z) :=
  ((strongly_convex h4 z).strictConvexOn h4.1).convexOn

lemma derivative_growth (z a b : ℝ) (hab : a ≤ b) :
    ℓc*(b-a) ≤ deriv (fun x => J x z) b - deriv (fun x => J x z) a := by
  let g : ℝ → ℝ := fun x => J x z - ℓc/2*x^2
  have hg : ConvexOn ℝ Set.univ g := by
    simpa only [Real.norm_eq_abs, sq_abs] using strongConvexOn_iff_convex.mp (strongly_convex h4 z)
  have hd (x : ℝ) : HasDerivAt g (deriv (fun x => J x z) x - ℓc*x) x := by
    have hq : HasDerivAt (fun y : ℝ => ℓc/2*y^2) (ℓc*x) x := by
      convert ((hasDerivAt_id x).pow 2).const_mul (ℓc/2) using 1 <;> norm_num <;> first | rfl | ring
    exact ((differentiable h4 z x).hasDerivAt).sub hq
  have hm := hg.monotoneOn_deriv (fun x _ => (hd x).differentiableAt)
  have hh := hm (Set.mem_univ a) (Set.mem_univ b) hab
  rw [(hd a).deriv, (hd b).deriv] at hh
  linarith

lemma exists_minimizer (z : ℝ) : ∃ a, ∀ b, J a z ≤ J b z := by
  let d := deriv (fun a => J a z) 0
  let R := (|d|+1)/ℓc
  have hc := h4.1
  have hR : 0 < R := div_pos (by positivity) hc
  have hRc : ℓc*R = |d|+1 := by dsimp [R]; field_simp
  have hlo := derivative_growth h4 z (-R) 0 (by linarith)
  have hhi := derivative_growth h4 z 0 R hR.le
  have hl : deriv (fun a => J a z) (-R) ≤ 0 := by
    have hab := le_abs_self d
    change d - deriv (fun a => J a z) (-R) ≥ ℓc * (0- -R) at hlo
    nlinarith
  have hu : 0 ≤ deriv (fun a => J a z) R := by
    have hab := neg_abs_le d
    change ℓc*(R-0) ≤ deriv (fun a => J a z) R-d at hhi
    nlinarith
  obtain ⟨a, _, ha⟩ := intermediate_value_Icc (show -R ≤ R by linarith)
    ((h4.2.2.1 z).continuous_deriv (by norm_num)).continuousOn (show (0:ℝ) ∈ Set.Icc _ _ from ⟨hl,hu⟩)
  refine ⟨a, fun b => ?_⟩
  rcases lt_trichotomy a b with hab | rfl | hba
  · have h := (convex h4 z).deriv_le_slope (Set.mem_univ a) (Set.mem_univ b) hab (differentiable h4 z a)
    rw [ha, slope_def_field] at h
    have hh := (le_div_iff₀ (sub_pos.mpr hab)).mp h
    linarith
  · rfl
  · have h := (convex h4 z).slope_le_deriv (Set.mem_univ b) (Set.mem_univ a) hba (differentiable h4 z a)
    rw [ha, slope_def_field] at h
    have hh := (div_le_iff₀ (sub_pos.mpr hba)).mp h
    linarith

noncomputable def response (J : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  Classical.epsilon (fun a => ∀ b, J a z ≤ J b z)

lemma response_min (z b : ℝ) : J (response J z) z ≤ J b z :=
  Classical.epsilon_spec (exists_minimizer h4 z) b

lemma response_unique (z a : ℝ) (ha : ∀ b, J a z ≤ J b z) : a = response J z := by
  exact ((strongly_convex h4 z).strictConvexOn h4.1).eq_of_isMinOn
    (fun b _ => ha b) (fun b _ => response_min h4 z b) (Set.mem_univ a) (Set.mem_univ _)

end

section
open MeasureTheory
open scoped ENNReal
open GraphonGames.Stability
set_option autoImplicit false
open GraphonGames

lemma mixed_aggregate_difference (b : ℝ → ℝ → ℝ) (μ0 : Measure ℝ) (cα cz : ℝ)
    (h1 : GraphonGames.Existence.Asm1 b μ0 cα cz)
    (w w' : I → I → ℝ) (hw : IsGraphon w) (hw' : IsGraphon w')
    (α α' z z' : I → ℝ) (hα : MemLp α 2 volume) (hα' : MemLp α' 2 volume)
    (hz : IsAggregate w b α z) (hz' : IsAggregate w' b α' z') :
    (z-z') =ᵐ[volume] graphonApply w (fun y => b (α y) (z y)-b (α' y) (z' y)) +
      graphonApply (w-w') (fun y => b (α' y) (z' y)) := by
  have hg := b_memLp b μ0 cα cz h1 α z hα hz.1
  have hh := b_memLp b μ0 cα cz h1 α' z' hα' hz'.1
  have hi1 := hw.2.2.integrable_mul (hg.comp_snd (volume : Measure I))
  have hi2 := hw.2.2.integrable_mul (hh.comp_snd (volume : Measure I))
  have hi3 := hw'.2.2.integrable_mul (hh.comp_snd (volume : Measure I))
  filter_upwards [hz.2,hz'.2,hi1.prod_right_ae,hi2.prod_right_ae,hi3.prod_right_ae]
    with x hx hx' h1i h2i h3i
  change z x-z' x = (∫y, w x y*(b (α y) (z y)-b (α' y) (z' y))) +
    ∫y, (w x y-w' x y)*b (α' y) (z' y)
  change Integrable (fun y => w x y*b (α y) (z y)) volume at h1i
  change Integrable (fun y => w x y*b (α' y) (z' y)) volume at h2i
  change Integrable (fun y => w' x y*b (α' y) (z' y)) volume at h3i
  rw [hx,hx']
  simp_rw [mul_sub,sub_mul]
  rw [integral_sub h1i h2i,integral_sub h2i h3i]
  ring

end

section
open MeasureTheory
open scoped ENNReal
open GraphonGames.Stability
set_option autoImplicit false

theorem solution
    (b : ℝ → ℝ → ℝ) (f : ℝ → ℝ → ℝ → ℝ)
    (μ0 : Measure ℝ) (cα cz ℓc ℓJ c0 : ℝ)
    (h1 : GraphonGames.Existence.Asm1 b μ0 cα cz)
    (h4 : GraphonGames.Existence.Asm4 (GraphonGames.Existence.cost b f μ0) ℓc ℓJ)
    (h5 : GraphonGames.Existence.Asm5 b c0)
    (w w' : I → I → ℝ) (hw : IsGraphon w) (hw' : IsGraphon w')
    (hW : Real.sqrt cz * (opNorm w).toReal < 1)
    (h17 : ℓJ / ℓc * (Real.sqrt cα * (opNorm w).toReal /
      (1 - Real.sqrt cz * (opNorm w).toReal)) < 1)
    (hW' : Real.sqrt cz * (opNorm w').toReal < 1)
    (α α' : I → ℝ) (hα : IsNash w b f μ0 α) (hα' : IsNash w' b f μ0 α') :
    eLpNorm (α - α') 2 volume ≤
      ENNReal.ofReal
        (c0 * ℓJ * (1 - Real.sqrt cz * (opNorm w).toReal) /
          ((1 - Real.sqrt cz * (opNorm w).toReal) *
            (ℓc * (1 - Real.sqrt cz * (opNorm w).toReal) -
              ℓJ * Real.sqrt cα * (opNorm w).toReal))) * opNorm (w - w') := by
  obtain ⟨hαL,z,hz,hmin⟩ := hα
  obtain ⟨hα'L,z',hz',hmin'⟩ := hα'
  let J := GraphonGames.Existence.cost b f μ0
  have haeq : α =ᵐ[volume] bestResponse J z := by
    filter_upwards [hmin] with x hx
    exact response_unique h4 (z x) (α x) hx
  have haeq' : α' =ᵐ[volume] bestResponse J z' := by
    filter_upwards [hmin'] with x hx
    exact response_unique h4 (z' x) (α' x) hx
  have hab : eLpNorm (α-α') 2 volume ≤
      ENNReal.ofReal (ℓJ/ℓc)*eLpNorm (z-z') 2 volume :=
    (eLpNorm_congr_ae (haeq.sub haeq')).le.trans
      (GraphonGames.Stability.lemma_3_7_best_response_lipschitz J ℓc ℓJ h4 z z' hz.1 hz'.1)
  have hww := graphon_difference w w' hw hw'
  have hg := b_memLp b μ0 cα cz h1 α z hαL hz.1
  have hh := b_memLp b μ0 cα cz h1 α' z' hα'L hz'.1
  have hbb := b_difference_bound b μ0 cα cz h1 α α' z z' hαL hα'L hz.1 hz'.1
  have hbc : eLpNorm (fun y => b (α' y) (z' y)) 2 volume ≤ ENNReal.ofReal c0 := by
    calc
      _ ≤ eLpNorm (fun _ : I => c0) 2 volume := by
        apply eLpNorm_mono_ae
        filter_upwards [] with y
        simpa only [Real.norm_eq_abs,abs_of_pos h5.1] using h5.2 (α' y) (z' y)
      _ = _ := by
        rw [eLpNorm_const' c0 (by norm_num) (by norm_num)]
        simp [Real.enorm_eq_ofReal h5.1.le]
  have hA := operator_bound w hw (fun y => b (α y) (z y)-b (α' y) (z' y)) (hg.sub hh)
  have hB := operator_bound (w-w') hww (fun y => b (α' y) (z' y)) hh
  have hsum := eLpNorm_add_le
    (graphon_memLp w hw _ (hg.sub hh)).1 (graphon_memLp (w-w') hww _ hh).1
    (by norm_num : (1:ℝ≥0∞)≤2)
  have he := eLpNorm_congr_ae (p:=2)
    (mixed_aggregate_difference b μ0 cα cz h1 w w' hw hw' α α' z z' hαL hα'L hz hz')
  have hm : eLpNorm (z-z') 2 volume ≤
      opNorm w*(ENNReal.ofReal (Real.sqrt cα)*eLpNorm (α-α') 2 volume +
        ENNReal.ofReal (Real.sqrt cz)*eLpNorm (z-z') 2 volume) +
      opNorm (w-w')*ENNReal.ofReal c0 :=
    he.le.trans (hsum.trans (add_le_add
      (hA.trans (mul_le_mul_of_nonneg_left hbb zero_le))
      (hB.trans (mul_le_mul_of_nonneg_left hbc zero_le))))
  have hAf := (hαL.sub hα'L).2.ne
  have hZf := (hz.1.sub hz'.1).2.ne
  have hN := (opNorm_finite w hw).ne
  have hD := (opNorm_finite (w-w') hww).ne
  have hmR := ENNReal.toReal_mono (by finiteness) hm
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hmR
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness)] at hmR
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg cα),
    ENNReal.toReal_ofReal (Real.sqrt_nonneg cz), ENNReal.toReal_ofReal h5.1.le] at hmR
  have hL : 0 ≤ ℓJ/ℓc := div_nonneg h4.2.1 h4.1.le
  have habR := ENNReal.toReal_mono (by finiteness) hab
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hL] at habR
  have hd : 0 < 1 - Real.sqrt cz*(opNorm w).toReal := by linarith
  have hdelta : 0 < ℓc*(1-Real.sqrt cz*(opNorm w).toReal) -
      ℓJ*Real.sqrt cα*(opNorm w).toReal := by
    rw [div_mul_div_comm] at h17
    have hh := (div_lt_one (mul_pos h4.1 hd)).mp h17
    nlinarith
  have habc : ℓc*(eLpNorm (α-α') 2 volume).toReal ≤
      ℓJ*(eLpNorm (z-z') 2 volume).toReal := by
    rw [div_mul_eq_mul_div] at habR
    have hh := (le_div_iff₀ h4.1).mp habR
    nlinarith
  have ht := mul_le_mul_of_nonneg_left habc hd.le
  have hs := mul_le_mul_of_nonneg_left hmR h4.2.1
  have hc : 0 ≤ c0*ℓJ*(1-Real.sqrt cz*(opNorm w).toReal) /
      ((1-Real.sqrt cz*(opNorm w).toReal)*
        (ℓc*(1-Real.sqrt cz*(opNorm w).toReal)-ℓJ*Real.sqrt cα*(opNorm w).toReal)) := by
    exact div_nonneg (mul_nonneg (mul_nonneg h5.1.le h4.2.1) hd.le) (mul_pos hd hdelta).le
  apply (ENNReal.toReal_le_toReal hAf (by finiteness)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]
  have hcancel : c0*ℓJ*(1-Real.sqrt cz*(opNorm w).toReal) /
      ((1-Real.sqrt cz*(opNorm w).toReal)*
        (ℓc*(1-Real.sqrt cz*(opNorm w).toReal)-ℓJ*Real.sqrt cα*(opNorm w).toReal)) =
      c0*ℓJ/(ℓc*(1-Real.sqrt cz*(opNorm w).toReal)-ℓJ*Real.sqrt cα*(opNorm w).toReal) := by
    field_simp
  rw [hcancel, div_mul_eq_mul_div, le_div_iff₀ hdelta]
  nlinarith

end
