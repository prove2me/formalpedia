-- Prove2me | solution 1 for KellyStochasticNetworks.FlowStability.per_flow_concavity_derivative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:40:04.692485+00:00
-- url     : https://prove2.me/submissions/e29daa5a-9a67-45e3-a9a0-642a0420d607

import Mathlib
import Definitions.Def_KellyStochasticNetworks_FlowStability_Network

open KellyStochasticNetworks.FlowStability

/-- convexity of `t ^ p` for `p < 0` on positive reals (pointwise form) -/
lemma g79k_rpow_neg_convex {p : ℝ} (hp : p < 0) {x y a b : ℝ} (hx : 0 < x) (hy : 0 < y)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a * x + b * y) ^ p ≤ a * x ^ p + b * y ^ p := by
  have hxy : 0 < a * x + b * y := by
    rcases ha.lt_or_eq with ha' | ha'
    · positivity
    · subst ha'; simp at hab; subst hab; simpa using hy
  have hlog : a * Real.log x + b * Real.log y ≤ Real.log (a * x + b * y) := by
    have := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hy) ha hb hab
    simpa [smul_eq_mul] using this
  rw [Real.rpow_def_of_pos hxy, Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy]
  calc Real.exp (Real.log (a * x + b * y) * p)
      ≤ Real.exp (a * (Real.log x * p) + b * (Real.log y * p)) := by
        apply Real.exp_le_exp.mpr; nlinarith
    _ ≤ a * Real.exp (Real.log x * p) + b * Real.exp (Real.log y * p) := by
        have := convexOn_exp.2 (Set.mem_univ (Real.log x * p)) (Set.mem_univ (Real.log y * p)) ha hb hab
        simpa [smul_eq_mul] using this

lemma g79k_term {α a b c u v : ℝ} (hα : 0 < α) (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hu : 0 ≤ u) (hv : 0 ≤ v) (hpos : 1 ≤ α → 0 < c → 0 < u ∧ 0 < v) :
    (if α = 1 then a * (c * Real.log u) + b * (c * Real.log v)
      else a * (c * (u ^ (1 - α) / (1 - α))) + b * (c * (v ^ (1 - α) / (1 - α)))) ≤
    (if α = 1 then c * Real.log (a * u + b * v)
      else c * ((a * u + b * v) ^ (1 - α) / (1 - α))) := by
  rcases hc.lt_or_eq with hc' | hc'
  swap
  · subst hc'; split_ifs <;> simp
  split_ifs with h1
  · obtain ⟨hu', hv'⟩ := hpos h1.ge hc'
    have := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.mpr hu') (Set.mem_Ioi.mpr hv') ha hb hab
    simp only [smul_eq_mul] at this
    nlinarith
  · rcases lt_or_gt_of_ne h1 with hlt | hgt
    · have h1a : 0 < 1 - α := by linarith
      have := (Real.concaveOn_rpow (p := 1 - α) (by linarith) (by linarith)).2
        (Set.mem_Ici.mpr hu) (Set.mem_Ici.mpr hv) ha hb hab
      simp only [smul_eq_mul] at this
      have key : a * (u ^ (1 - α) / (1 - α)) + b * (v ^ (1 - α) / (1 - α)) ≤
          (a * u + b * v) ^ (1 - α) / (1 - α) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
        have hi : 0 < (1 - α)⁻¹ := inv_pos.mpr h1a
        nlinarith
      nlinarith
    · obtain ⟨hu', hv'⟩ := hpos hgt.le hc'
      have h1a : 1 - α < 0 := by linarith
      have := g79k_rpow_neg_convex h1a hu' hv' ha hb hab
      have key : a * (u ^ (1 - α) / (1 - α)) + b * (v ^ (1 - α) / (1 - α)) ≤
          (a * u + b * v) ^ (1 - α) / (1 - α) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
        have hi : (1 - α)⁻¹ < 0 := inv_lt_zero.mpr h1a
        nlinarith
      nlinarith

theorem solution {R : ℕ} (w : Fin R → ℝ) (n : State R)
    (alpha : ℝ) (ha : 0 < alpha) (hw : ∀ r, 0 < w r) :
    ConcaveOn ℝ (utilityDomain n alpha) (perFlowUtility w n alpha) ∧
    ∀ (x : Fin R → ℝ) (r : Fin R), (0 < n r → 0 < x r) →
      HasDerivAt (fun t => perFlowUtility w n alpha (Function.update x r t))
        (w r * (n r : ℝ) * x r ^ (-alpha)) (x r) := by
  have hform : ∀ x : Fin R → ℝ, perFlowUtility w n alpha x =
      ∑ i, (if alpha = 1 then (w i * (n i : ℝ)) * Real.log (x i)
        else (w i * (n i : ℝ)) * (x i ^ (1 - alpha) / (1 - alpha))) := by
    intro x
    unfold perFlowUtility KellyStochasticNetworks.alphaFairObjective
    split_ifs <;> simp
  constructor
  · refine ⟨?_, ?_⟩
    · intro x hx y hy a b ha' hb' hab
      refine ⟨fun r => ?_, fun h1 r hr => ?_⟩
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have := hx.1 r; have := hy.1 r; positivity
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have h1x := hx.2 h1 r hr; have h1y := hy.2 h1 r hr
        rcases ha'.lt_or_eq with ha'' | ha''
        · have := mul_pos ha'' h1x; have := mul_nonneg hb' h1y.le; linarith
        · subst ha''; simp at hab; subst hab; simpa using h1y
    · intro x hx y hy a b ha' hb' hab
      rw [hform, hform, hform, smul_eq_mul, smul_eq_mul, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have hc : 0 ≤ w i * (n i : ℝ) := mul_nonneg (hw i).le (Nat.cast_nonneg _)
      have := g79k_term (u := x i) (v := y i) ha hc ha' hb' hab (hx.1 i) (hy.1 i) (by
        intro h1 hc'
        have hn : 0 < n i := by
          rcases Nat.eq_zero_or_pos (n i) with h | h
          · simp [h] at hc'
          · exact h
        exact ⟨hx.2 h1 i hn, hy.2 h1 i hn⟩)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      split_ifs at this ⊢ <;> linarith
  · intro x r hxr
    simp_rw [hform]
    have hder : ∀ i ∈ Finset.univ, HasDerivAt
        (fun t => if alpha = 1 then (w i * (n i : ℝ)) * Real.log (Function.update x r t i)
          else (w i * (n i : ℝ)) * (Function.update x r t i ^ (1 - alpha) / (1 - alpha)))
        (if i = r then w r * (n r : ℝ) * x r ^ (-alpha) else 0) (x r) := by
      intro i _
      by_cases hir : i = r
      · subst hir
        simp only [Function.update_self, if_true]
        rcases Nat.eq_zero_or_pos (n i) with h0 | hpos
        · have : (fun t : ℝ => if alpha = 1 then (w i * (n i : ℝ)) * Real.log t
              else (w i * (n i : ℝ)) * (t ^ (1 - alpha) / (1 - alpha))) = fun _ => 0 := by
            funext t; simp [h0]
          rw [this]; simpa [h0] using hasDerivAt_const (x i) (0 : ℝ)
        · have hx0 := hxr hpos
          split_ifs with h1
          · subst h1
            have := (Real.hasDerivAt_log hx0.ne').const_mul (w i * (n i : ℝ))
            exact this.congr_deriv (by rw [Real.rpow_neg_one])
          · have h1a : (1 - alpha) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
            have := ((Real.hasDerivAt_rpow_const (p := 1 - alpha) (Or.inl hx0.ne')).div_const
              (1 - alpha)).const_mul (w i * (n i : ℝ))
            exact this.congr_deriv (by rw [show 1 - alpha - 1 = -alpha by ring]; field_simp)
      · simp only [Function.update_of_ne hir, hir, if_false]
        exact hasDerivAt_const _ _
    have := HasDerivAt.fun_sum hder
    simpa using this
