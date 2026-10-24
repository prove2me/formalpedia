-- Prove2me | solution 1 for NetFeePlatform.InteropDominance.proposition_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T06:49:57.695+00:00
-- url     : https://prove2.me/submissions/29f5ef79-6bac-4d36-a337-42888935269a

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting

set_option autoImplicit false

namespace P6Aux

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

lemma sum_erase_eq (f : Fin 2 → ℝ) (j k : Fin 2) (hjk : j ≠ k) :
    ∑ i ∈ Finset.univ.erase j, f i = f k := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), Fin.sum_univ_two]
  fin_cases j <;> fin_cases k <;> simp_all

open NetFeePlatform.Competition in
lemma demand_eq (t : Fin 2 → ℝ) (j k : Fin 2) (hjk : j ≠ k) :
    demand 0 t j = nn (t j - t k) := by
  have hsum : ∑ i, Real.exp (-t i) = Real.exp (-t j) + Real.exp (-t k) := by
    rw [Fin.sum_univ_two]
    fin_cases j <;> fin_cases k <;> simp_all <;> ring
  unfold demand nn
  rw [hsum, zero_add]
  have hj := Real.exp_pos (-t j)
  have hk := Real.exp_pos (-t k)
  rw [show t j - t k = (-t k) - (-t j) by ring, Real.exp_sub]
  field_simp

open NetFeePlatform.Competition in
lemma profit_P (c γ lam : ℝ) (t : Fin 2 → ℝ) (j k : Fin 2) (hjk : j ≠ k) :
    profit 0 c γ lam t j = P (γ * (1 - lam)) (lam * γ - c) (t k) (t j) := by
  unfold profit P
  rw [sum_erase_eq _ j k hjk, demand_eq t j k hjk, demand_eq t k j (Ne.symm hjk),
    show t k - t j = -(t j - t k) by ring, nn_neg]
  ring

open NetFeePlatform.Competition in
lemma profit_update (c γ lam : ℝ) (t : Fin 2 → ℝ) (j k : Fin 2) (hjk : j ≠ k) (s : ℝ) :
    profit 0 c γ lam (Function.update t j s) j = P (γ * (1 - lam)) (lam * γ - c) (t k) s := by
  rw [profit_P c γ lam _ j k hjk, Function.update_self, Function.update_of_ne (Ne.symm hjk)]

/-- Difference of the two first-order conditions, as a function of the fee gap `d`. -/
noncomputable def G (g d : ℝ) : ℝ :=
  Real.exp (-d) - Real.exp d - d - 2 * g * (nn d - nn (-d))

lemma continuous_G (g : ℝ) : Continuous (G g) := by
  unfold G
  have h1 : Continuous fun d : ℝ => nn d - nn (-d) :=
    continuous_nn.sub (continuous_nn.comp continuous_neg)
  exact (((Real.continuous_exp.comp continuous_neg).sub Real.continuous_exp).sub
    continuous_id).sub (continuous_const.mul h1)

open NetFeePlatform.Competition in
lemma main (c γ lamLo lamHi : ℝ) (hγ : 0 < γ) (hlt : lamLo < lamHi) (hhi : lamHi ≤ 1)
    (hreg : γ * (1 - lamLo) ≤ 27 / 8)
    (t : Fin 2 → ℝ) (ht : IsEquilibrium 0 c γ lamHi t) (j k : Fin 2) (hjk : j ≠ k)
    (hall : ∀ i : Fin 2, i = j ∨ i = k)
    (hdom : 1 / 2 < demand 0 t j) :
    ∃ t' : Fin 2 → ℝ, IsEquilibrium 0 c γ lamLo t' ∧ demand 0 t j < demand 0 t' j := by
  -- first-order conditions of the high-interoperability equilibrium
  have hfj : H (γ * (1 - lamHi)) (lamHi * γ - c) (t k) (t j) = 0 := by
    apply foc
    intro s
    have := ht j s
    rwa [profit_update c γ lamHi t j k hjk, profit_P c γ lamHi t j k hjk] at this
  have hfk : H (γ * (1 - lamHi)) (lamHi * γ - c) (t j) (t k) = 0 := by
    apply foc
    intro s
    have := ht k s
    rwa [profit_update c γ lamHi t k j (Ne.symm hjk),
      profit_P c γ lamHi t k j (Ne.symm hjk)] at this
  obtain ⟨d, hd⟩ : ∃ d, d = t j - t k := ⟨_, rfl⟩
  have hGH : G (γ * (1 - lamHi)) d = 0 := by
    unfold H at hfj hfk
    unfold G
    rw [show t k - t j = -(t j - t k) by ring] at hfj hfk
    rw [← hd] at hfj hfk
    linarith
  rw [demand_eq t j k hjk, ← hd] at hdom
  have hdneg : d < 0 := neg_of_nn_gt_half hdom
  have hgap : 0 < nn d - nn (-d) := by
    have := nn_strictAnti (show d < -d by linarith)
    linarith
  obtain ⟨gL, hgL⟩ : ∃ g, g = γ * (1 - lamLo) := ⟨_, rfl⟩
  obtain ⟨BL, hBL⟩ : ∃ B, B = lamLo * γ - c := ⟨_, rfl⟩
  have hgL0 : 0 ≤ gL := by rw [hgL]; nlinarith
  have hreg' : gL ≤ 27 / 8 := by rw [hgL]; exact hreg
  have hGL : G gL d < 0 := by
    have e1 : G gL d = G (γ * (1 - lamHi)) d - 2 * (γ * (lamHi - lamLo)) * (nn d - nn (-d)) := by
      unfold G; rw [hgL]; ring
    have : 0 < 2 * (γ * (lamHi - lamLo)) * (nn d - nn (-d)) := by
      have : 0 < γ * (lamHi - lamLo) := mul_pos hγ (by linarith)
      positivity
    linarith
  -- a far-left point where G is positive
  obtain ⟨D, hD⟩ : ∃ D, D = d - 2 * gL - 2 := ⟨_, rfl⟩
  have hGD : 0 < G gL D := by
    unfold G
    have e1 := Real.add_one_le_exp (-D)
    have e2 : Real.exp D ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have e3 : nn D - nn (-D) ≤ 1 := by linarith [nn_lt_one D, nn_pos (-D)]
    have e4 : gL * (nn D - nn (-D)) ≤ gL := by nlinarith
    nlinarith
  have hDd : D ≤ d := by linarith
  have hivt := intermediate_value_Icc' hDd (continuous_G gL).continuousOn
  obtain ⟨d', hd'mem, hd'0⟩ := hivt (show (0 : ℝ) ∈ Set.Icc (G gL d) (G gL D) from
    ⟨hGL.le, hGD.le⟩)
  have hd'lt : d' < d := by
    rcases lt_or_eq_of_le hd'mem.2 with h | h
    · exact h
    · rw [h] at hd'0; linarith
  -- the low-interoperability equilibrium
  obtain ⟨Tj, hTj⟩ : ∃ x, x = 1 + Real.exp (-d') - 2 * gL * nn d' - BL := ⟨_, rfl⟩
  obtain ⟨Tk, hTk⟩ : ∃ x, x = 1 + Real.exp d' - 2 * gL * nn (-d') - BL := ⟨_, rfl⟩
  have hdiff : Tj - Tk = d' := by
    unfold G at hd'0
    rw [hTj, hTk]; linarith
  let t' : Fin 2 → ℝ := fun i => if i = j then Tj else Tk
  have htj : t' j = Tj := if_pos rfl
  have htk : t' k = Tk := if_neg (Ne.symm hjk)
  refine ⟨t', ?_, ?_⟩
  · intro i s
    rcases hall i with h | h
    · rw [h, profit_update c γ lamLo t' j k hjk, profit_P c γ lamLo t' j k hjk, ← hgL, ← hBL]
      apply br gL BL (t' k) (t' j) hreg' _ s
      unfold H
      rw [htj, htk, show Tk - Tj = -d' by linarith, show Tj - Tk = d' by linarith, hTj]
      ring
    · rw [h, profit_update c γ lamLo t' k j (Ne.symm hjk), profit_P c γ lamLo t' k j (Ne.symm hjk),
        ← hgL, ← hBL]
      apply br gL BL (t' j) (t' k) hreg' _ s
      unfold H
      rw [htj, htk, show Tj - Tk = d' by linarith, show Tk - Tj = -d' by linarith, hTk]
      ring
  · rw [demand_eq t j k hjk, demand_eq t' j k hjk, htj, htk, hdiff, ← hd]
    exact nn_strictAnti hd'lt

end P6Aux

theorem solution (c γ lamLo lamHi : ℝ) (hγ : 0 < γ) (hlo : 0 ≤ lamLo) (hlt : lamLo < lamHi)
    (hhi : lamHi ≤ 1) (hreg : γ * (1 - lamLo) ≤ 27 / 8)
    (t : Fin 2 → ℝ) (ht : NetFeePlatform.Competition.IsEquilibrium 0 c γ lamHi t) (j : Fin 2) (hdom : 1 / 2 < NetFeePlatform.Competition.demand 0 t j) :
    ∃ t' : Fin 2 → ℝ, NetFeePlatform.Competition.IsEquilibrium 0 c γ lamLo t' ∧ NetFeePlatform.Competition.demand 0 t j < NetFeePlatform.Competition.demand 0 t' j := by
  obtain ⟨k, hjk, hall⟩ : ∃ k : Fin 2, j ≠ k ∧ ∀ i : Fin 2, i = j ∨ i = k := by
    fin_cases j
    · exact ⟨1, by decide, by decide⟩
    · exact ⟨0, by decide, by decide⟩
  exact P6Aux.main c γ lamLo lamHi hγ hlt hhi hreg t ht j k hjk hall hdom
