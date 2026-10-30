-- Prove2me | solution 1 for LearnDoFrontier.TwoAction.thm3_root_count
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T03:00:34.936034+00:00
-- url     : https://prove2.me/submissions/3de31453-0777-416b-bd6d-0efd3aee49f6

import Mathlib
import Definitions.Def_LearnDoFrontier_TwoAction_Algebra
import Definitions.Def_LearnDoFrontier_TwoAction_Model

open Polynomial Complex Metric

namespace LDFRoot

noncomputable def lgd (q : ℂ[X]) (z : ℂ) : ℂ := (derivative q).eval z / q.eval z

noncomputable def Pm (s : Multiset ℂ) : ℂ[X] := (s.map (fun a => X - C a)).prod

lemma Pm_eval_ne (s : Multiset ℂ) (z : ℂ) (hz : z ∉ s) : (Pm s).eval z ≠ 0 := by
  unfold Pm
  rw [eval_multiset_prod]
  apply Multiset.prod_ne_zero
  intro h
  simp only [Multiset.map_map, Function.comp_def, eval_sub, eval_X, eval_C,
    Multiset.mem_map] at h
  obtain ⟨a, ha, h0⟩ := h
  rw [sub_eq_zero] at h0
  exact hz (h0 ▸ ha)

lemma lgd_Pm (s : Multiset ℂ) (z : ℂ) (hz : z ∉ s) :
    lgd (Pm s) z = (s.map (fun a => (z - a)⁻¹)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [lgd, Pm]
  | cons a t ih =>
    have hza : z ≠ a := fun h => hz (h ▸ Multiset.mem_cons_self a t)
    have hzt : z ∉ t := fun h => hz (Multiset.mem_cons_of_mem h)
    have ht := Pm_eval_ne t z hzt
    have hPm : Pm (a ::ₘ t) = (X - C a) * Pm t := by simp [Pm]
    rw [Multiset.map_cons, Multiset.sum_cons, ← ih hzt]
    unfold lgd
    rw [hPm, derivative_mul]
    simp only [derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, eval_add, eval_mul,
      eval_sub, eval_X, eval_C]
    have hza' : z - a ≠ 0 := sub_ne_zero.mpr hza
    field_simp

lemma lgd_eq (q : ℂ[X]) (hq : q ≠ 0) (z : ℂ) (hz : z ∉ q.roots) :
    lgd q z = (q.roots.map (fun a => (z - a)⁻¹)).sum := by
  have hsplit := C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := q))
  have hlc : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq
  rw [← lgd_Pm _ z hz]
  unfold lgd
  conv_lhs => rw [← hsplit]
  rw [derivative_C_mul, eval_mul, eval_mul, eval_C]
  unfold Pm
  rw [mul_div_mul_left _ _ hlc]

lemma circ_inv (a : ℂ) (ha : ‖a‖ ≠ 1) :
    (∮ z in C(0, 1), (z - a)⁻¹) = if ‖a‖ < 1 then 2 * Real.pi * I else 0 := by
  split_ifs with h
  · exact circleIntegral.integral_sub_inv_of_mem_ball (by simpa [mem_ball_zero_iff] using h)
  · have h' : 1 < ‖a‖ := lt_of_le_of_ne (not_lt.mp h) (Ne.symm ha)
    apply circleIntegral_eq_zero_of_differentiable_on_off_countable zero_le_one
      Set.countable_empty
    · apply ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
      intro z hz h0
      have h0' : z - a = 0 := h0
      rw [sub_eq_zero] at h0'
      rw [mem_closedBall_zero_iff, h0'] at hz
      linarith
    · intro z hz
      have hz1 : ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hz.1
      apply DifferentiableAt.inv (differentiableAt_id.sub (differentiableAt_const _))
      intro h0
      rw [sub_eq_zero] at h0
      rw [h0] at hz1
      linarith

lemma cont_inv (b : ℂ) (hb : ‖b‖ ≠ 1) : ContinuousOn (fun z : ℂ => (z - b)⁻¹) (sphere 0 1) := by
  apply ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
  intro z hz h0
  have h0' : z - b = 0 := h0
  rw [sub_eq_zero] at h0'
  rw [mem_sphere_zero_iff_norm, h0'] at hz
  exact hb hz

lemma circ_sum (s : Multiset ℂ) (hs : ∀ a ∈ s, ‖a‖ ≠ 1) :
    CircleIntegrable (fun z => (s.map (fun a => (z - a)⁻¹)).sum) 0 1 ∧
    (∮ z in C(0, 1), (s.map (fun a => (z - a)⁻¹)).sum) =
      2 * Real.pi * I * ((s.filter (fun a => ‖a‖ < 1)).card : ℂ) := by
  induction s using Multiset.induction_on with
  | empty => simp [circleIntegral]
  | cons a t ih =>
    have ha : ‖a‖ ≠ 1 := hs a (Multiset.mem_cons_self a t)
    have ht : ∀ b ∈ t, ‖b‖ ≠ 1 := fun b hb => hs b (Multiset.mem_cons_of_mem hb)
    obtain ⟨hint2, heq⟩ := ih ht
    have hint1 : CircleIntegrable (fun z : ℂ => (z - a)⁻¹) 0 1 :=
      ContinuousOn.circleIntegrable' (by rw [abs_one]; exact cont_inv a ha)
    simp only [Multiset.map_cons, Multiset.sum_cons]
    refine ⟨hint1.add hint2, ?_⟩
    rw [circleIntegral.integral_add hint1 hint2, heq, circ_inv a ha, Multiset.filter_cons]
    split_ifs with h <;> simp <;> ring


theorem arg_principle (q : ℂ[X]) (hq : q ≠ 0) (hc : ∀ z : ℂ, ‖z‖ = 1 → q.eval z ≠ 0) :
    (∮ z in C(0, 1), lgd q z) =
      2 * Real.pi * I * ((q.roots.filter (fun a => ‖a‖ < 1)).card : ℂ) := by
  have hr : ∀ a ∈ q.roots, ‖a‖ ≠ 1 := by
    intro a ha h1
    exact hc a h1 ((mem_roots hq).mp ha)
  rw [circleIntegral.integral_congr zero_le_one (g := fun z => (q.roots.map (fun a => (z - a)⁻¹)).sum)]
  · exact (circ_sum q.roots hr).2
  · intro z hz
    apply lgd_eq q hq z
    intro hzr
    exact hr z hzr (by simpa using hz)

noncomputable def Qs (A B : ℝ) (N nb : ℕ) (s : ℝ) : ℂ[X] :=
  C (s : ℂ) * X ^ N - C (A : ℂ) * X ^ nb + C (B : ℂ)

lemma Qs_eval (A B : ℝ) (N nb : ℕ) (s : ℝ) (z : ℂ) :
    (Qs A B N nb s).eval z = s * z ^ N - A * z ^ nb + B := by
  simp [Qs]

lemma Qs_deval (A B : ℝ) (N nb : ℕ) (s : ℝ) (z : ℂ) :
    (derivative (Qs A B N nb s)).eval z = s * N * z ^ (N - 1) - A * nb * z ^ (nb - 1) := by
  simp [Qs, derivative_X_pow]; ring

lemma Qs_ne (A B : ℝ) (N nb : ℕ) (hB : 0 ≤ B) (hAB : B + 1 < A) (s : ℝ) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) (z : ℂ) (hz : ‖z‖ = 1) : (Qs A B N nb s).eval z ≠ 0 := by
  rw [Qs_eval]
  intro h
  have h1 : (A : ℂ) * z ^ nb = s * z ^ N + B := by linear_combination -h
  have h2 : ‖(A : ℂ) * z ^ nb‖ = A := by
    rw [norm_mul, norm_pow, hz, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
  have h3 : ‖(s : ℂ) * z ^ N + B‖ ≤ s + B := by
    calc ‖(s : ℂ) * z ^ N + B‖ ≤ ‖(s : ℂ) * z ^ N‖ + ‖(B : ℂ)‖ := norm_add_le _ _
      _ = s + B := by
        rw [norm_mul, norm_pow, hz, one_pow, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hs0, abs_of_nonneg hB]
  rw [h1] at h2
  linarith

lemma Qs_ne_zero (A B : ℝ) (N nb : ℕ) (hB : 0 ≤ B) (hAB : B + 1 < A) (s : ℝ) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : Qs A B N nb s ≠ 0 := by
  intro h
  have := Qs_ne A B N nb hB hAB s hs0 hs1 1 (by simp)
  rw [h] at this
  simp at this

noncomputable def clamp (s : ℝ) : ℝ := max 0 (min s 1)
lemma clamp_nonneg (s : ℝ) : 0 ≤ clamp s := le_max_left _ _
lemma clamp_le (s : ℝ) : clamp s ≤ 1 := max_le zero_le_one (min_le_right _ _)
lemma clamp_cont : Continuous clamp := continuous_const.max (continuous_id.min continuous_const)
lemma clamp_of (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1) : clamp s = s := by
  simp [clamp, h0, h1]

lemma J_cont (A B : ℝ) (N nb : ℕ) (hB : 0 ≤ B) (hAB : B + 1 < A) :
    Continuous (fun s : ℝ => ∮ z in C(0, 1), lgd (Qs A B N nb (clamp s)) z) := by
  unfold circleIntegral
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have hfun : Function.uncurry (fun (s : ℝ) (θ : ℝ) =>
      deriv (circleMap 0 1) θ • lgd (Qs A B N nb (clamp s)) (circleMap 0 1 θ)) =
      fun p : ℝ × ℝ => (circleMap 0 1 p.2 * I) *
        (((clamp p.1 : ℝ) : ℂ) * N * (circleMap 0 1 p.2) ^ (N - 1) - A * nb * (circleMap 0 1 p.2) ^ (nb - 1)) /
        (((clamp p.1 : ℝ) : ℂ) * (circleMap 0 1 p.2) ^ N - A * (circleMap 0 1 p.2) ^ nb + B) := by
    funext p
    simp only [Function.uncurry, deriv_circleMap, smul_eq_mul, lgd, Qs_eval, Qs_deval]
    ring
  rw [hfun]
  have hc := clamp_cont
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro p
    have := Qs_ne A B N nb hB hAB (clamp p.1) (clamp_nonneg _) (clamp_le _) (circleMap 0 1 p.2)
      (by simp)
    rwa [Qs_eval] at this


lemma count_const (A B : ℝ) (N nb : ℕ) (hB : 0 ≤ B) (hAB : B + 1 < A) :
    ((Qs A B N nb 0).roots.filter (fun a => ‖a‖ < 1)).card =
      ((Qs A B N nb 1).roots.filter (fun a => ‖a‖ < 1)).card := by
  set k : ℝ → ℕ := fun s => ((Qs A B N nb (clamp s)).roots.filter (fun a => ‖a‖ < 1)).card
  have hJ : ∀ s, (∮ z in C(0, 1), lgd (Qs A B N nb (clamp s)) z) = 2 * Real.pi * I * (k s : ℂ) :=
    fun s => arg_principle _ (Qs_ne_zero A B N nb hB hAB _ (clamp_nonneg s) (clamp_le s))
      (Qs_ne A B N nb hB hAB _ (clamp_nonneg s) (clamp_le s))
  set r : ℝ → ℝ := fun s => ((∮ z in C(0, 1), lgd (Qs A B N nb (clamp s)) z) /
    (2 * Real.pi * I)).re
  have hr : ∀ s, r s = k s := by
    intro s
    simp only [r, hJ]
    have : (2 * Real.pi * I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, I_ne_zero]
    rw [mul_div_cancel_left₀ _ this]
    simp
  have hrc : Continuous r :=
    Complex.continuous_re.comp ((J_cont A B N nb hB hAB).div_const _)
  have k0 : k 0 = ((Qs A B N nb 0).roots.filter (fun a => ‖a‖ < 1)).card := by
    simp only [k, clamp_of 0 le_rfl zero_le_one]
  have k1 : k 1 = ((Qs A B N nb 1).roots.filter (fun a => ‖a‖ < 1)).card := by
    simp only [k, clamp_of 1 zero_le_one le_rfl]
  rw [← k0, ← k1]
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmem : ((k 0 : ℝ) + 1 / 2) ∈ Set.Icc (r 0) (r 1) := by
      rw [hr, hr]
      have : ((k 0 : ℝ) + 1) ≤ k 1 := by exact_mod_cast hlt
      constructor <;> linarith
    obtain ⟨s, _, hs⟩ := intermediate_value_Icc zero_le_one hrc.continuousOn hmem
    rw [hr] at hs
    have : (2 * k s : ℝ) = 2 * k 0 + 1 := by linarith
    have : 2 * k s = 2 * k 0 + 1 := by exact_mod_cast this
    omega
  · have hmem : ((k 1 : ℝ) + 1 / 2) ∈ Set.Icc (r 1) (r 0) := by
      rw [hr, hr]
      have : ((k 1 : ℝ) + 1) ≤ k 0 := by exact_mod_cast hgt
      constructor <;> linarith
    obtain ⟨s, _, hs⟩ := intermediate_value_Icc' zero_le_one hrc.continuousOn hmem
    rw [hr] at hs
    have : (2 * k s : ℝ) = 2 * k 1 + 1 := by linarith
    have : 2 * k s = 2 * k 1 + 1 := by exact_mod_cast this
    omega

lemma count_zero (A B : ℝ) (N nb : ℕ) (hnb : 0 < nb) (hB : 0 ≤ B) (hAB : B + 1 < A) :
    ((Qs A B N nb 0).roots.filter (fun a => ‖a‖ < 1)).card = nb := by
  have hA : (A : ℂ) ≠ 0 := by
    have : A ≠ 0 := by linarith
    exact_mod_cast this
  have hQ : Qs A B N nb 0 = C (B : ℂ) - C (A : ℂ) * X ^ nb := by
    simp [Qs]; ring
  have hdeg : (Qs A B N nb 0).natDegree = nb := by
    rw [hQ, natDegree_sub_eq_right_of_natDegree_lt] <;> rw [natDegree_C_mul_X_pow _ _ hA]
    rw [natDegree_C]; exact hnb
  have hne : Qs A B N nb 0 ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hdeg; omega
  rw [Multiset.filter_eq_self.mpr, IsAlgClosed.card_roots_eq_natDegree, hdeg]
  intro a ha
  have h0 := (mem_roots hne).mp ha
  rw [IsRoot, Qs_eval] at h0
  push_cast at h0
  have h1 : (A : ℂ) * a ^ nb = B := by linear_combination -h0
  have h2 : A * ‖a‖ ^ nb = B := by
    have := congrArg norm h1
    rwa [norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (by linarith), abs_of_nonneg hB] at this
  by_contra hge
  push Not at hge
  have : 1 ≤ ‖a‖ ^ nb := one_le_pow₀ hge
  nlinarith

end LDFRoot

open LearnDoFrontier.TwoAction in
theorem LDFRoot.sum_mult (f : ℂ[X]) :
    ∑ z ∈ Zunit f, mult f z = (f.roots.filter (fun a => ‖a‖ < 1)).card := by
  unfold Zunit mult
  rw [← Multiset.toFinset_filter, ← Multiset.toFinset_sum_count_eq]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Multiset.mem_toFinset, Multiset.mem_filter] at hz
  rw [Multiset.count_filter_of_pos (p := fun a : ℂ => ‖a‖ < 1) hz.2, count_roots]

open LearnDoFrontier.TwoAction in
theorem LDFRoot.root_count (n nbar : ℕ) (_hn : 0 < n) (hnbar : 0 < nbar) (δ p : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    let f : ℂ[X] := X ^ (n + nbar) - C ((δ⁻¹ * p⁻¹ : ℝ) : ℂ) * X ^ nbar + C ((p⁻¹ * (1 - p) : ℝ) : ℂ)
    ∑ z ∈ Zunit f, mult f z = nbar := by
  intro f
  have hB : 0 ≤ p⁻¹ * (1 - p) := mul_nonneg (inv_nonneg.mpr hp0.le) (by linarith)
  have hAB : p⁻¹ * (1 - p) + 1 < δ⁻¹ * p⁻¹ := by
    have e : p⁻¹ * (1 - p) + 1 = p⁻¹ := by field_simp; ring
    rw [e]
    have : 1 < δ⁻¹ := one_lt_inv_iff₀.mpr ⟨hδ0, hδ1⟩
    have hp' : 0 < p⁻¹ := inv_pos.mpr hp0
    nlinarith
  have hf : f = LDFRoot.Qs (δ⁻¹ * p⁻¹) (p⁻¹ * (1 - p)) (n + nbar) nbar 1 := by
    simp [f, LDFRoot.Qs]
  rw [LDFRoot.sum_mult, hf, ← LDFRoot.count_const _ _ _ _ hB hAB,
    LDFRoot.count_zero _ _ _ _ hnbar hB hAB]

open LearnDoFrontier.TwoAction in
theorem solution (n nbar : ℕ) (hn : 0 < n) (hnbar : 0 < nbar) (δ p : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    let f : ℂ[X] := X ^ (n + nbar) - C ((δ⁻¹ * p⁻¹ : ℝ) : ℂ) * X ^ nbar + C ((p⁻¹ * (1 - p) : ℝ) : ℂ)
    ∑ z ∈ Zunit f, mult f z = nbar :=
  LDFRoot.root_count n nbar hn hnbar δ p hδ0 hδ1 hp0 hp1
