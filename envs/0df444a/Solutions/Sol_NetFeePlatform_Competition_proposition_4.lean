-- Prove2me | solution 1 for NetFeePlatform.Competition.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T00:46:57.766303+00:00
-- url     : https://prove2.me/submissions/c47b3113-db0e-4dcf-a9fc-ad81f08ffc2f

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting

set_option autoImplicit false

namespace P4Aux

/-- Logit share of a platform whose fee exceeds the rival's by `d`. -/
noncomputable def nn (d : ℝ) : ℝ := 1 / (1 + Real.exp d)

lemma nn_pos (d : ℝ) : 0 < nn d := by unfold nn; positivity

lemma nn_lt_one (d : ℝ) : nn d < 1 := by
  unfold nn
  rw [div_lt_one (by positivity)]
  linarith [Real.exp_pos d]

lemma nn_neg (d : ℝ) : nn (-d) = 1 - nn d := by
  unfold nn
  have h1 := Real.exp_pos d
  rw [Real.exp_neg]
  field_simp
  ring

lemma nn_strictAnti {x y : ℝ} (h : x < y) : nn y < nn x := by
  unfold nn
  apply one_div_lt_one_div_of_lt (by positivity)
  linarith [Real.exp_lt_exp.mpr h]

lemma neg_of_nn_gt_half {d : ℝ} (h : 1 / 2 < nn d) : d < 0 := by
  by_contra hc
  replace hc : 0 ≤ d := not_lt.mp hc
  have h1 := Real.one_le_exp hc
  unfold nn at h
  rw [lt_div_iff₀ (by positivity)] at h
  linarith

lemma continuous_nn : Continuous nn := by
  unfold nn
  exact continuous_const.div (continuous_const.add Real.continuous_exp)
    (fun x => by positivity)

/-- Profit of the deviating platform as a function of its own fee `s`, rival fee `a`. -/
noncomputable def P (g B a s : ℝ) : ℝ := (s + g * nn (s - a) + B) * nn (s - a)

/-- First-order expression: `P' = n (1 - n) H`. -/
noncomputable def H (g B a s : ℝ) : ℝ :=
  1 + Real.exp (a - s) - 2 * g * nn (s - a) - s - B

lemma hasDerivAt_nn (a s : ℝ) :
    HasDerivAt (fun x => nn (x - a))
      (-(Real.exp (s - a)) / (1 + Real.exp (s - a)) ^ 2) s := by
  have h1 : HasDerivAt (fun x => 1 + Real.exp (x - a)) (Real.exp (s - a)) s := by
    have := ((hasDerivAt_id s).sub_const a).exp
    simpa using this.const_add 1
  have h2 := h1.inv (by positivity)
  simp only [nn, one_div]
  exact h2

lemma hasDerivAt_P (g B a s : ℝ) :
    HasDerivAt (P g B a) (nn (s - a) * (1 - nn (s - a)) * H g B a s) s := by
  have hn := hasDerivAt_nn a s
  have h1 : HasDerivAt (fun x => (x + g * nn (x - a) + B) * nn (x - a))
      ((1 + g * (-(Real.exp (s - a)) / (1 + Real.exp (s - a)) ^ 2)) * nn (s - a)
        + (s + g * nn (s - a) + B) * (-(Real.exp (s - a)) / (1 + Real.exp (s - a)) ^ 2)) s :=
    (((hasDerivAt_id' s).add (hn.const_mul g)).add_const B).mul hn
  refine h1.congr_deriv ?_
  have hE := Real.exp_pos (s - a)
  have hinv : Real.exp (a - s) = (Real.exp (s - a))⁻¹ := by
    rw [← Real.exp_neg, neg_sub]
  simp only [H, nn, hinv]
  field_simp
  ring

lemma hasDerivAt_H (g B a s : ℝ) :
    HasDerivAt (H g B a)
      (-Real.exp (a - s) - 2 * g * (-(Real.exp (s - a)) / (1 + Real.exp (s - a)) ^ 2) - 1) s := by
  have hn := hasDerivAt_nn a s
  have he : HasDerivAt (fun x => Real.exp (a - x)) (-Real.exp (a - s)) s := by
    have := ((hasDerivAt_id s).const_sub a).exp
    simpa using this
  have h1 : HasDerivAt (fun x => 1 + Real.exp (a - x) - 2 * g * nn (x - a) - x - B)
      (-Real.exp (a - s) - 2 * g * (-(Real.exp (s - a)) / (1 + Real.exp (s - a)) ^ 2) - 1) s :=
    ((((he.const_add 1).sub (hn.const_mul (2 * g))).sub (hasDerivAt_id' s)).sub_const B)
  exact h1

lemma H_deriv_nonpos (g a s : ℝ) (hg : g ≤ 27 / 8) :
    -Real.exp (a - s) - 2 * g * (-(Real.exp (s - a)) / (1 + Real.exp (s - a)) ^ 2) - 1 ≤ 0 := by
  set E := Real.exp (s - a) with hEdef
  have hE : 0 < E := Real.exp_pos _
  have hinv : Real.exp (a - s) = E⁻¹ := by
    rw [hEdef, ← Real.exp_neg, neg_sub]
  rw [hinv]
  have key : 2 * g * E ^ 2 ≤ (1 + E) ^ 3 := by
    have h0 : 0 ≤ (E - 2) ^ 2 * (E + 1 / 4) := mul_nonneg (sq_nonneg _) (by linarith)
    have h2 : 2 * g * E ^ 2 ≤ 27 / 4 * E ^ 2 := by nlinarith [sq_nonneg E]
    nlinarith
  have hfrac : 2 * g * E / (1 + E) ^ 2 ≤ 1 + E⁻¹ := by
    rw [div_le_iff₀ (by positivity)]
    have : (1 + E⁻¹) * (1 + E) ^ 2 = (1 + E) ^ 3 / E := by
      field_simp
      ring
    rw [this, le_div_iff₀ hE]
    nlinarith
  have : -(2 * g * (-E / (1 + E) ^ 2)) = 2 * g * E / (1 + E) ^ 2 := by ring
  linarith

lemma br (g B a s0 : ℝ) (hg : g ≤ 27 / 8) (hfoc : H g B a s0 = 0) (s : ℝ) :
    P g B a s ≤ P g B a s0 := by
  have hP : ∀ x, HasDerivAt (P g B a) (nn (x - a) * (1 - nn (x - a)) * H g B a x) x :=
    fun x => hasDerivAt_P g B a x
  have hH : Antitone (H g B a) := by
    apply antitone_of_deriv_nonpos (fun x => (hasDerivAt_H g B a x).differentiableAt)
    intro x
    rw [(hasDerivAt_H g B a x).deriv]
    exact H_deriv_nonpos g a x hg
  have hPd : Differentiable ℝ (P g B a) := fun x => (hP x).differentiableAt
  have hpos : ∀ x, 0 < nn (x - a) * (1 - nn (x - a)) := fun x =>
    mul_pos (nn_pos _) (by linarith [nn_lt_one (x - a)])
  rcases le_total s s0 with h | h
  · have hm : MonotoneOn (P g B a) (Set.Iic s0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Iic s0) hPd.continuous.continuousOn
        hPd.differentiableOn
      intro x hx
      rw [interior_Iic] at hx
      rw [(hP x).deriv]
      have : 0 ≤ H g B a x := by rw [← hfoc]; exact hH (le_of_lt hx)
      exact mul_nonneg (hpos x).le this
    exact hm (Set.mem_Iic.mpr h) (Set.mem_Iic.mpr le_rfl) h
  · have hm : AntitoneOn (P g B a) (Set.Ici s0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici s0) hPd.continuous.continuousOn
        hPd.differentiableOn
      intro x hx
      rw [interior_Ici] at hx
      rw [(hP x).deriv]
      have : H g B a x ≤ 0 := by rw [← hfoc]; exact hH (le_of_lt hx)
      exact mul_nonpos_of_nonneg_of_nonpos (hpos x).le this
    exact hm (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h) h

lemma foc (g B a s0 : ℝ) (hmax : ∀ s, P g B a s ≤ P g B a s0) : H g B a s0 = 0 := by
  have hlm : IsLocalMax (P g B a) s0 := Filter.Eventually.of_forall hmax
  have h0 := hlm.hasDerivAt_eq_zero (hasDerivAt_P g B a s0)
  have hp : 0 < nn (s0 - a) * (1 - nn (s0 - a)) :=
    mul_pos (nn_pos _) (by linarith [nn_lt_one (s0 - a)])
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd h hp.ne'
  · exact h

open NetFeePlatform.Competition

/-- Total weight of the rivals of platform `j`. -/
noncomputable def R {J : ℕ} (t : Fin J → ℝ) (j : Fin J) : ℝ :=
  ∑ k ∈ Finset.univ.erase j, Real.exp (-t k)

lemma R_pos {J : ℕ} (t : Fin J → ℝ) (j : Fin J) (hne : (Finset.univ.erase j).Nonempty) :
    0 < R t j :=
  Finset.sum_pos (fun k _ => Real.exp_pos _) hne

lemma sum_split {J : ℕ} (t : Fin J → ℝ) (j : Fin J) :
    ∑ k, Real.exp (-t k) = Real.exp (-t j) + R t j := by
  unfold R
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]

lemma R_update {J : ℕ} (t : Fin J → ℝ) (j : Fin J) (s : ℝ) :
    R (Function.update t j s) j = R t j := by
  unfold R
  apply Finset.sum_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

lemma demand_nn {J : ℕ} (t : Fin J → ℝ) (j : Fin J) (hR : 0 < R t j) :
    demand 0 t j = nn (t j - (-Real.log (R t j))) := by
  unfold demand nn
  rw [sum_split, zero_add, sub_neg_eq_add, Real.exp_add, Real.exp_log hR, Real.exp_neg]
  have h1 := Real.exp_pos (t j)
  field_simp

lemma profit_update4 {J : ℕ} (c γ : ℝ) (t : Fin J → ℝ) (j : Fin J) (hR : 0 < R t j) (s : ℝ) :
    profit 0 c γ 0 (Function.update t j s) j = P γ (-c) (-Real.log (R t j)) s := by
  have hR' : 0 < R (Function.update t j s) j := by rwa [R_update]
  unfold profit
  rw [demand_nn _ j hR', R_update, Function.update_self]
  unfold P
  ring

lemma profit_self {J : ℕ} (c γ : ℝ) (t : Fin J → ℝ) (j : Fin J) (hR : 0 < R t j) :
    profit 0 c γ 0 t j = P γ (-c) (-Real.log (R t j)) (t j) := by
  have := profit_update4 c γ t j hR (t j)
  rwa [Function.update_eq_self] at this

lemma H_eq {J : ℕ} (c γ : ℝ) (t : Fin J → ℝ) (j : Fin J) (hR : 0 < R t j) :
    H γ (-c) (-Real.log (R t j)) (t j)
      = 1 / (1 - demand 0 t j) - 2 * γ * demand 0 t j - t j + c := by
  have hd : 1 + Real.exp (-Real.log (R t j) - t j) = 1 / (1 - demand 0 t j) := by
    unfold demand
    rw [sum_split, zero_add, Real.exp_sub, Real.exp_neg, Real.exp_log hR, Real.exp_neg]
    have h1 := Real.exp_pos (t j)
    field_simp
    ring
  unfold H
  rw [hd, ← demand_nn t j hR]
  ring

lemma foc_of_eq {J : ℕ} (c γ : ℝ) (t : Fin J → ℝ) (hR : ∀ j, 0 < R t j)
    (h : IsEquilibrium 0 c γ 0 t) (j : Fin J) :
    t j - c = 1 / (1 - demand 0 t j) - 2 * γ * demand 0 t j := by
  have hmax : ∀ s, P γ (-c) (-Real.log (R t j)) s ≤ P γ (-c) (-Real.log (R t j)) (t j) := by
    intro s
    have := h j s
    rwa [profit_update4 c γ t j (hR j) s, profit_self c γ t j (hR j)] at this
  have := foc _ _ _ _ hmax
  rw [H_eq c γ t j (hR j)] at this
  linarith

lemma eq_of_foc {J : ℕ} (c γ : ℝ) (hγ : γ ≤ 27 / 8) (t : Fin J → ℝ) (hR : ∀ j, 0 < R t j)
    (hf : ∀ j, t j - c = 1 / (1 - demand 0 t j) - 2 * γ * demand 0 t j) :
    IsEquilibrium 0 c γ 0 t := by
  intro j s
  rw [profit_update4 c γ t j (hR j) s, profit_self c γ t j (hR j)]
  apply br _ _ _ _ hγ
  rw [H_eq c γ t j (hR j)]
  linarith [hf j]

lemma demand_ratio {J : ℕ} (t : Fin J → ℝ) (k k' : Fin J) :
    demand 0 t k / demand 0 t k' = Real.exp (t k' - t k) := by
  have hpos : 0 < 0 + ∑ i, Real.exp (-t i) := by
    rw [zero_add]
    exact Finset.sum_pos (fun i _ => Real.exp_pos _) ⟨k, Finset.mem_univ _⟩
  unfold demand
  rw [div_div_div_cancel_right₀ (ne_of_gt hpos), ← Real.exp_sub]
  congr 1
  ring

noncomputable def Φ (γ x : ℝ) : ℝ :=
  Real.log (x / (1 - x)) + 1 / (1 - x) - 1 / x - 2 * γ * (2 * x - 1)

noncomputable def Ψ (γ x : ℝ) : ℝ :=
  2 / (1 + x) - 1 / (1 - x) + γ * (3 * x - 1) - Real.log (2 * x / (1 - x))

lemma duo_share (c γ : ℝ) (t : Fin 2 → ℝ) (hR : ∀ j, 0 < R t j) (h : IsEquilibrium 0 c γ 0 t)
    (k k' : Fin 2) (hsum : demand 0 t k + demand 0 t k' = 1) :
    Φ γ (demand 0 t k) = 0 := by
  have h1 := foc_of_eq c γ t hR h k
  have h2 := foc_of_eq c γ t hR h k'
  have hk' : demand 0 t k' = 1 - demand 0 t k := by linarith
  have hr := demand_ratio t k k'
  rw [hk'] at hr h2
  have hl : Real.log (demand 0 t k / (1 - demand 0 t k)) = t k' - t k := by
    rw [hr, Real.log_exp]
  unfold Φ
  rw [hl, show (1 : ℝ) - (1 - demand 0 t k) = demand 0 t k by ring] at *
  linarith

lemma log_ratio_ge (x : ℝ) (hx1 : 1 / 2 ≤ x) (hx2 : x < 1) :
    2 * (2 * x - 1) + 2 * (2 * x - 1) ^ 3 / 3 ≤ Real.log (x / (1 - x)) := by
  set y := 2 * x - 1 with hy
  have hy0 : 0 ≤ y := by linarith
  have hyabs : |y| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one hyabs
  have hle := sum_le_hasSum (Finset.range 2)
    (fun i _ => mul_nonneg (by positivity) (pow_nonneg hy0 _)) hs
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hle
  have e1 : Real.log (1 + y) = Real.log 2 + Real.log x := by
    rw [show 1 + y = 2 * x by rw [hy]; ring, Real.log_mul (by norm_num) (by linarith)]
  have e2 : Real.log (1 - y) = Real.log 2 + Real.log (1 - x) := by
    rw [show 1 - y = 2 * (1 - x) by rw [hy]; ring, Real.log_mul (by norm_num) (by linarith)]
  rw [Real.log_div (by linarith) (by linarith)]
  norm_num at hle
  linarith

lemma duo_bound (γ x : ℝ) (hγ : γ ≤ 27 / 8) (hx1 : 1 / 2 < x) (hx2 : x < 1) (hΦ : Φ γ x = 0) :
    x < 7 / 10 ∧ 1 + (2 * x - 1) ^ 2 / 3 + 1 / (2 * x * (1 - x)) ≤ γ := by
  have hL := log_ratio_ge x hx1.le hx2
  have h3 : 1 / (1 - x) - 1 / x = (2 * x - 1) / (x * (1 - x)) := by
    have : 1 - x ≠ 0 := by linarith
    have : x ≠ 0 := by linarith
    field_simp
    ring
  unfold Φ at hΦ
  have hy : 0 < 2 * x - 1 := by linarith
  have hxx : 0 < x * (1 - x) := mul_pos (by linarith) (by linarith)
  have key : 2 * (2 * x - 1) * (1 + (2 * x - 1) ^ 2 / 3 + 1 / (2 * x * (1 - x)))
      ≤ 2 * (2 * x - 1) * γ := by
    have e : 2 * (2 * x - 1) * (1 + (2 * x - 1) ^ 2 / 3 + 1 / (2 * x * (1 - x)))
        = 2 * (2 * x - 1) + 2 * (2 * x - 1) ^ 3 / 3 + (2 * x - 1) / (x * (1 - x)) := by
      field_simp
    rw [e]
    nlinarith
  have hg := le_of_mul_le_mul_left key (by linarith)
  refine ⟨?_, hg⟩
  by_contra hc
  push Not at hc
  have hxx2 : x * (1 - x) ≤ 21 / 100 := by nlinarith
  have : 100 / 42 ≤ 1 / (2 * x * (1 - x)) := by
    rw [le_div_iff₀ (by nlinarith)]
    nlinarith
  nlinarith [sq_nonneg (2 * x - 1)]

lemma D_pos (γ x : ℝ) (hx1 : 1 / 2 < x) (hx7 : x < 7 / 10)
    (hγ : 1 + (2 * x - 1) ^ 2 / 3 + 1 / (2 * x * (1 - x)) ≤ γ) :
    Real.log 2 < 2 / (1 + x) - 1 / x + γ * (1 - x) := by
  have hl := Real.log_two_lt_d9
  have h1x : 0 < 1 - x := by linarith
  have hg : (1 - x) * (1 + (2 * x - 1) ^ 2 / 3) + 1 / (2 * x) ≤ γ * (1 - x) := by
    have e : (1 - x) * (1 + (2 * x - 1) ^ 2 / 3 + 1 / (2 * x * (1 - x)))
        = (1 - x) * (1 + (2 * x - 1) ^ 2 / 3) + 1 / (2 * x) := by
      field_simp
    rw [← e, mul_comm γ]
    exact mul_le_mul_of_nonneg_left hγ h1x.le
  have hq : 7 / 10 < 2 / (1 + x) - 1 / x + ((1 - x) * (1 + (2 * x - 1) ^ 2 / 3) + 1 / (2 * x)) := by
    have hx0 : 0 < x := by linarith
    rw [show 2 / (1 + x) - 1 / x + ((1 - x) * (1 + (2 * x - 1) ^ 2 / 3) + 1 / (2 * x))
        = (4 * x - (1 + x) + 2 * x * (1 + x) * ((1 - x) * (1 + (2 * x - 1) ^ 2 / 3)))
          / (2 * x * (1 + x)) by field_simp; ring]
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [mul_pos (sub_pos.mpr hx1) (sub_pos.mpr hx7), mul_pos hx0 hx0,
      mul_pos (mul_pos (sub_pos.mpr hx1) (sub_pos.mpr hx7)) hx0]
  norm_num at hl
  linarith

lemma Φ_cont (γ : ℝ) : ContinuousOn (Φ γ) (Set.Icc (1 / 2) (4 / 5)) := by
  intro x hx
  have h0 : x ≠ 0 := (by linarith [hx.1] : (0 : ℝ) < x).ne'
  have h1 : 1 - x ≠ 0 := (by linarith [hx.2] : (0 : ℝ) < 1 - x).ne'
  have h2 : x / (1 - x) ≠ 0 := div_ne_zero h0 h1
  apply ContinuousAt.continuousWithinAt
  unfold Φ
  fun_prop (disch := assumption)

lemma Ψ_cont (γ a b : ℝ) (ha : 0 < a) (hb : b < 1) : ContinuousOn (Ψ γ) (Set.Icc a b) := by
  intro x hx
  have h0 : 2 * x ≠ 0 := (by linarith [hx.1] : (0 : ℝ) < 2 * x).ne'
  have h1 : 1 - x ≠ 0 := (by linarith [hx.2] : (0 : ℝ) < 1 - x).ne'
  have h3 : 1 + x ≠ 0 := (by linarith [hx.1] : (0 : ℝ) < 1 + x).ne'
  have h2 : 2 * x / (1 - x) ≠ 0 := div_ne_zero h0 h1
  apply ContinuousAt.continuousWithinAt
  unfold Ψ
  fun_prop (disch := assumption)

lemma real_core (γ : ℝ) (hlo : 2 * Real.log 2 + 4 / 3 < γ) (hhi : γ ≤ 27 / 8) :
    ∃ x3 : ℝ, 1 / 2 < x3 ∧ x3 < 1 ∧ Ψ γ x3 = 0 ∧
      ∀ x : ℝ, 0 < x → x < 1 → Φ γ x = 0 → x < x3 := by
  set S := Set.Icc (1 / 2 : ℝ) (4 / 5) ∩ Φ γ ⁻¹' {0} with hSdef
  have hSc : IsClosed S :=
    (Φ_cont γ).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hSk : IsCompact S := isCompact_Icc.of_isClosed_subset hSc Set.inter_subset_left
  have hhalf : (1 / 2 : ℝ) ∈ S := by
    refine ⟨⟨le_rfl, by norm_num⟩, ?_⟩
    show Φ γ (1 / 2) = 0
    unfold Φ
    rw [show (1 / 2 : ℝ) / (1 - 1 / 2) = 1 by norm_num, Real.log_one]
    ring
  have hm : sSup S ∈ S := hSk.sSup_mem ⟨_, hhalf⟩
  have hbdd : BddAbove S := hSk.bddAbove
  set m := sSup S with hmdef
  have hm1 : 1 / 2 ≤ m := hm.1.1
  have hm2 : m ≤ 4 / 5 := hm.1.2
  have hΦm : Φ γ m = 0 := hm.2
  have hΨm : 0 < Ψ γ m := by
    rcases eq_or_lt_of_le hm1 with h | h
    · rw [← h]
      unfold Ψ
      rw [show (2 : ℝ) * (1 / 2) / (1 - 1 / 2) = 2 by norm_num]
      have : 2 / (1 + 1 / 2) - 1 / (1 - 1 / 2) + γ * (3 * (1 / 2) - 1) - Real.log 2
          = γ / 2 - 2 / 3 - Real.log 2 := by ring
      rw [this]
      linarith
    · obtain ⟨h7, hg⟩ := duo_bound γ m hhi h (by linarith) hΦm
      have hD := D_pos γ m h h7 hg
      have hx0 : 0 < m := by linarith
      have h1m : 0 < 1 - m := by linarith
      have hlog : Real.log (2 * m / (1 - m)) = Real.log 2 + Real.log (m / (1 - m)) := by
        rw [mul_div_assoc, Real.log_mul (by norm_num) (div_pos hx0 h1m).ne']
      unfold Φ at hΦm
      unfold Ψ
      rw [hlog]
      linarith
  have hΨ9 : Ψ γ (9 / 10) < 0 := by
    have hpos : 0 < Real.log 18 := Real.log_pos (by norm_num)
    unfold Ψ
    rw [show (2 : ℝ) * (9 / 10) / (1 - 9 / 10) = 18 by norm_num]
    norm_num
    linarith
  have hm9 : m ≤ 9 / 10 := by linarith
  have hcΨ : ContinuousOn (Ψ γ) (Set.Icc m (9 / 10)) := Ψ_cont γ m (9 / 10) (by linarith) (by norm_num)
  obtain ⟨x3, hx3, hx3e⟩ := intermediate_value_Icc' hm9 hcΨ ⟨hΨ9.le, hΨm.le⟩
  have hne : x3 ≠ m := by
    intro h
    rw [h] at hx3e
    linarith
  have hlt : m < x3 := lt_of_le_of_ne hx3.1 (Ne.symm hne)
  refine ⟨x3, by linarith, by linarith [hx3.2], hx3e, ?_⟩
  intro x hx0 hx1 hΦx
  by_cases hx : x ≤ 1 / 2
  · linarith
  · push Not at hx
    have h7 := (duo_bound γ x hhi hx hx1 hΦx).1
    have hxS : x ∈ S := ⟨⟨hx.le, by linarith⟩, hΦx⟩
    have := le_csSup hbdd hxS
    linarith

lemma tri_eq (c γ x : ℝ) (hγ : γ ≤ 27 / 8) (hx0 : 0 < x) (hx1 : x < 1) (hΨ : Ψ γ x = 0)
    (hR3 : ∀ (t : Fin 3 → ℝ) (j : Fin 3), 0 < R t j) :
    ∃ t : Fin 3 → ℝ, IsEquilibrium 0 c γ 0 t ∧ demand 0 t 0 = x := by
  set tb := c + 1 / (1 - x) - 2 * γ * x with htb
  set ts := c + 2 / (1 + x) - γ * (1 - x) with hts
  have h1x : 0 < 1 - x := by linarith
  have hq : 0 < 2 * x / (1 - x) := div_pos (by linarith) h1x
  have hrel : -tb = -ts + Real.log (2 * x / (1 - x)) := by
    unfold Ψ at hΨ
    rw [htb, hts]
    linarith
  have hE : Real.exp (-tb) = Real.exp (-ts) * (2 * x / (1 - x)) := by
    rw [hrel, Real.exp_add, Real.exp_log hq]
  have hEs := Real.exp_pos (-ts)
  have hsum : ∑ k, Real.exp (-(![tb, ts, ts] : Fin 3 → ℝ) k)
      = Real.exp (-ts) * (2 * x / (1 - x)) + Real.exp (-ts) + Real.exp (-ts) := by
    rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [hE]
  have hd0 : demand 0 (![tb, ts, ts] : Fin 3 → ℝ) 0 = x := by
    unfold demand
    rw [hsum, zero_add]
    simp only [Matrix.cons_val_zero]
    rw [hE, div_eq_iff (by positivity)]
    field_simp
    ring
  have hds : ∀ j : Fin 3, j ≠ 0 → demand 0 (![tb, ts, ts] : Fin 3 → ℝ) j = (1 - x) / 2 := by
    intro j hj
    have hj' : (![tb, ts, ts] : Fin 3 → ℝ) j = ts := by
      fin_cases j
      · exact absurd rfl hj
      · rfl
      · rfl
    unfold demand
    rw [hsum, zero_add, hj', div_eq_iff (by positivity)]
    field_simp
    ring
  refine ⟨![tb, ts, ts], ?_, hd0⟩
  apply eq_of_foc c γ hγ _ (hR3 _)
  intro j
  by_cases hj : j = 0
  · subst hj
    rw [hd0]
    show tb - c = _
    rw [htb]
    ring
  · rw [hds j hj]
    have hj' : (![tb, ts, ts] : Fin 3 → ℝ) j = ts := by
      fin_cases j
      · exact absurd rfl hj
      · rfl
      · rfl
    rw [hj', hts, show (1 : ℝ) - (1 - x) / 2 = (1 + x) / 2 by ring, one_div_div]
    ring

lemma demand_const2 (a : ℝ) (j : Fin 2) : demand 0 (fun _ : Fin 2 => a) j = 1 / 2 := by
  unfold demand
  rw [Fin.sum_univ_two, zero_add, div_eq_iff (by positivity)]
  ring

lemma demand_sum2 (t : Fin 2 → ℝ) : demand 0 t 0 + demand 0 t 1 = 1 := by
  unfold demand
  rw [Fin.sum_univ_two, zero_add, ← add_div, div_self (by positivity)]

end P4Aux

open NetFeePlatform.Competition in
theorem solution (c γ : ℝ) (hlo : 2 * Real.log 2 + 4 / 3 < γ) (hhi : γ ≤ 27 / 8) :
    (∃ t₂ : Fin 2 → ℝ, IsEquilibrium 0 c γ 0 t₂) ∧
    ∃ t₃ : Fin 3 → ℝ, IsEquilibrium 0 c γ 0 t₃ ∧ ∃ i : Fin 3,
      ∀ t₂ : Fin 2 → ℝ, IsEquilibrium 0 c γ 0 t₂ →
        ∀ k : Fin 2, demand 0 t₂ k < demand 0 t₃ i := by
  have hR2 : ∀ (t : Fin 2 → ℝ) (j : Fin 2), 0 < P4Aux.R t j := fun t j =>
    P4Aux.R_pos t j (by fin_cases j <;> decide)
  have hR3 : ∀ (t : Fin 3 → ℝ) (j : Fin 3), 0 < P4Aux.R t j := fun t j =>
    P4Aux.R_pos t j (by fin_cases j <;> decide)
  obtain ⟨x3, hx3a, hx3b, hΨ, hbig⟩ := P4Aux.real_core γ hlo hhi
  obtain ⟨t3, ht3, hd⟩ := P4Aux.tri_eq c γ x3 hhi (by linarith) hx3b hΨ hR3
  refine ⟨⟨fun _ => c + 2 - γ, ?_⟩, t3, ht3, 0, ?_⟩
  · apply P4Aux.eq_of_foc c γ hhi _ (hR2 _)
    intro j
    show c + 2 - γ - c = 1 / (1 - demand 0 (fun _ : Fin 2 => c + 2 - γ) j)
      - 2 * γ * demand 0 (fun _ : Fin 2 => c + 2 - γ) j
    rw [P4Aux.demand_const2, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    ring
  · intro t2 ht2 k
    rw [hd]
    have hsum := P4Aux.demand_sum2 t2
    have hk' : ∃ k' : Fin 2, demand 0 t2 k + demand 0 t2 k' = 1 := by
      fin_cases k
      · exact ⟨1, hsum⟩
      · exact ⟨0, show demand 0 t2 1 + demand 0 t2 0 = 1 by linarith⟩
    obtain ⟨k', hk'⟩ := hk'
    have hΦ := P4Aux.duo_share c γ t2 (hR2 t2) ht2 k k' hk'
    have hpos : 0 < demand 0 t2 k := by
      rw [P4Aux.demand_nn t2 k (hR2 t2 k)]
      exact P4Aux.nn_pos _
    have hlt : demand 0 t2 k < 1 := by
      rw [P4Aux.demand_nn t2 k (hR2 t2 k)]
      exact P4Aux.nn_lt_one _
    exact hbig _ hpos hlt hΦ
