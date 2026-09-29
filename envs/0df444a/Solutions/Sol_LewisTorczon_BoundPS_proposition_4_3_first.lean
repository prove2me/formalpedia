-- Prove2me | solution 1 for LewisTorczon.BoundPS.proposition_4_3_first
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:03:51.647428+00:00
-- url     : https://prove2.me/submissions/46636dd2-5dc8-40a2-a87d-ac85f53008f3

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

theorem aux_p43_box_convex {n : ℕ} (lo hi : Fin n → EReal) : Convex ℝ (box lo hi) := by
  intro x hx y hy a b ha hb hab j
  obtain ⟨hx1, hx2⟩ := hx j
  obtain ⟨hy1, hy2⟩ := hy j
  have e : ((a • x + b • y) j : ℝ) = a * x j + b * y j := by simp
  rw [e]
  have hx' : x j = a * x j + b * x j := by rw [← add_mul, hab, one_mul]
  have hy' : y j = a * y j + b * y j := by rw [← add_mul, hab, one_mul]
  have h1 : min (x j) (y j) ≤ a * x j + b * y j := by
    rcases le_total (x j) (y j) with h | h
    · rw [min_eq_left h]; nlinarith [mul_nonneg hb (sub_nonneg.2 h), mul_nonneg ha (sub_nonneg.2 h)]
    · rw [min_eq_right h]; nlinarith [mul_nonneg hb (sub_nonneg.2 h), mul_nonneg ha (sub_nonneg.2 h)]
  have h2 : a * x j + b * y j ≤ max (x j) (y j) := by
    rcases le_total (x j) (y j) with h | h
    · rw [max_eq_right h]; nlinarith [mul_nonneg hb (sub_nonneg.2 h), mul_nonneg ha (sub_nonneg.2 h)]
    · rw [max_eq_left h]; nlinarith [mul_nonneg hb (sub_nonneg.2 h), mul_nonneg ha (sub_nonneg.2 h)]
  constructor
  · calc lo j ≤ ((min (x j) (y j) : ℝ) : EReal) := by
          rcases le_total (x j) (y j) with h | h
          · rw [min_eq_left h]; exact hx1
          · rw [min_eq_right h]; exact hy1
      _ ≤ _ := EReal.coe_le_coe_iff.2 h1
  · calc (((a * x j + b * y j) : ℝ) : EReal) ≤ ((max (x j) (y j) : ℝ) : EReal) :=
          EReal.coe_le_coe_iff.2 h2
      _ ≤ hi j := by
          rcases le_total (x j) (y j) with h | h
          · rw [max_eq_right h]; exact hy2
          · rw [max_eq_left h]; exact hx2

theorem aux_p43_iter_mem {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (R : GPSRun n m) (hR : IsGPSRun P lo hi f R) :
    ∀ k, R.x k ∈ levelSet lo hi f (R.x 0) := by
  intro k
  induction k with
  | zero => exact ⟨hR.x_zero_mem, le_rfl⟩
  | succ k ih =>
    rw [hR.x_succ k]
    split_ifs with h
    · exact ⟨hR.step_feasible k, le_trans h.le ih.2⟩
    · exact ih

theorem aux_p43_Δ_pos {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (R : GPSRun n m) (hR : IsGPSRun P lo hi f R) :
    ∀ k, 0 < R.Δ k := by
  have hτ : (0 : ℝ) < (P.τ : ℝ) := by
    have := P.one_lt_τ
    have : (0 : ℚ) < P.τ := by linarith
    exact_mod_cast this
  intro k
  induction k with
  | zero => exact hR.Δ_zero_pos
  | succ k ih =>
    by_cases h : f (R.x k + R.s k) < f (R.x k)
    · obtain ⟨w, -, hw⟩ := hR.Δ_succ_success k h
      rw [hw]; exact mul_pos (zpow_pos hτ _) ih
    · rw [hR.Δ_succ_failure k h]; exact mul_pos (zpow_pos hτ _) ih

/-- Properties of the clamp. -/
theorem aux_p43_clamp (a b : EReal) (x t : ℝ) (ha : a ≤ (x : EReal)) (hb : (x : EReal) ≤ b) :
    a ≤ ((clampCoord a b t : ℝ) : EReal) ∧ ((clampCoord a b t : ℝ) : EReal) ≤ b ∧
    (x < clampCoord a b t → clampCoord a b t ≤ t) ∧
    (clampCoord a b t < x → t ≤ clampCoord a b t) := by
  have hab : a ≤ b := ha.trans hb
  set c : EReal := min b (t : EReal) with hc
  set m : EReal := max a c with hm
  have hmt : m ≠ ⊤ := by
    have ha' : a ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top x) ha
    have hc' : c ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top t) (min_le_right _ _)
    rw [hm]
    rcases le_total a c with h | h
    · rw [max_eq_right h]; exact hc'
    · rw [max_eq_left h]; exact ha'
  have hmb : m ≠ ⊥ := by
    have hb' : b ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot x) hb
    have hc' : c ≠ ⊥ := by
      rw [hc]
      rcases le_total b (t : EReal) with h | h
      · rw [min_eq_left h]; exact hb'
      · rw [min_eq_right h]; exact EReal.coe_ne_bot t
    exact ne_bot_of_le_ne_bot hc' (le_max_right _ _)
  have key : ((clampCoord a b t : ℝ) : EReal) = m := by
    unfold clampCoord
    exact EReal.coe_toReal hmt hmb
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [key]; exact le_max_left _ _
  · rw [key]; exact max_le hab (min_le_left _ _)
  · intro h
    have h' : (x : EReal) < m := by rw [← key]; exact EReal.coe_lt_coe_iff.2 h
    have hxc : (x : EReal) < c := by
      rcases lt_max_iff.1 h' with h1 | h1
      · exact absurd h1 (not_lt.2 ha)
      · exact h1
    have : m ≤ (t : EReal) := by
      apply max_le
      · exact ha.trans (hxc.le.trans (min_le_right _ _))
      · exact min_le_right _ _
    rw [← key] at this
    exact EReal.coe_le_coe_iff.1 this
  · intro h
    have h' : m < (x : EReal) := by rw [← key]; exact EReal.coe_lt_coe_iff.2 h
    have hcx : c < (x : EReal) := lt_of_le_of_lt (le_max_right _ _) h'
    have hct : c = (t : EReal) := by
      rw [hc]
      rcases le_total b (t : EReal) with h2 | h2
      · exfalso; rw [hc, min_eq_left h2] at hcx; exact absurd hb (not_le.2 hcx)
      · exact min_eq_right h2
    have : (t : EReal) ≤ m := by rw [← hct]; exact le_max_right _ _
    rw [← key] at this
    exact EReal.coe_le_coe_iff.1 this

theorem aux_p43_step {n : ℕ} (P : GPSParams n) (M : Matrix (Fin n) (Fin n) ℤ)
    (hd : (P.B * M.map (fun a : ℤ => (a : ℝ))).IsDiag) (Δ : ℝ) (j : Fin n) :
    stepOf P Δ (M.transpose j) =
      EuclideanSpace.single j (Δ * (P.B * M.map (fun a : ℤ => (a : ℝ))) j j) := by
  ext l
  have hA : (P.B * M.map (fun a : ℤ => (a : ℝ))) l j = ∑ r, P.B l r * (M r j : ℝ) := by
    simp [Matrix.mul_apply]
  by_cases hl : l = j
  · subst hl
    rw [hA]
    simp [stepOf, Matrix.mulVec, dotProduct]
  · have h0 : (P.B * M.map (fun a : ℤ => (a : ℝ))) l j = 0 := hd hl
    rw [hA] at h0
    simp [stepOf, Matrix.mulVec, dotProduct, hl, h0]

theorem aux_p43_step_neg {n : ℕ} (P : GPSParams n) (Δ : ℝ) (c : Fin n → ℤ) :
    stepOf P Δ (-c) = - stepOf P Δ c := by
  ext l
  simp [stepOf, Matrix.mulVec, dotProduct]

theorem aux_p43_diag_ne {n : ℕ} (P : GPSParams n) (M : Matrix (Fin n) (Fin n) ℤ)
    (hM : M.det ≠ 0) (hd : (P.B * M.map (fun a : ℤ => (a : ℝ))).IsDiag) (j : Fin n) :
    (P.B * M.map (fun a : ℤ => (a : ℝ))) j j ≠ 0 := by
  have h1 : (P.B * M.map (fun a : ℤ => (a : ℝ))).det ≠ 0 := by
    rw [Matrix.det_mul, ← Int.cast_det]
    exact mul_ne_zero P.B_det_ne_zero (Int.cast_ne_zero.2 hM)
  rw [← hd.diagonal_diag, Matrix.det_diagonal] at h1
  exact Finset.prod_ne_zero_iff.1 h1 j (Finset.mem_univ _)

theorem aux_p43_exists_coord {n : ℕ} (q : EuclideanSpace ℝ (Fin n)) (η : ℝ) (hη : 0 < η)
    (h : η < ‖q‖) : ∃ j, η / (n + 1) < |q j| := by
  by_contra hc
  push Not at hc
  have hε : 0 ≤ η / (n + 1) := by positivity
  have h1 : ‖q‖ ^ 2 ≤ η ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc ∑ i, (q i) ^ 2 ≤ ∑ _i : Fin n, (η / (n + 1)) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          have := hc i
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = n * (η / (n + 1)) ^ 2 := by simp
      _ ≤ η ^ 2 := by
          rw [div_pow, mul_div_assoc']
          rw [div_le_iff₀ (by positivity)]
          have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          nlinarith [sq_nonneg η, mul_nonneg this (sq_nonneg η)]
  have := pow_lt_pow_left₀ h hη.le two_ne_zero
  linarith

theorem aux_p43_projQ_apply {n : ℕ} (lo hi : Fin n → EReal) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    (projQ lo hi f x) j = clampCoord (lo j) (hi j) (x j - gradient f x j) - x j := by
  simp [projQ, boxProj]

theorem aux_p43_fderiv_single {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) (a : ℝ) :
    fderiv ℝ f x (EuclideanSpace.single j a) = a * gradient f x j := by
  have : fderiv ℝ f x (EuclideanSpace.single j a) =
      inner ℝ (gradient f x) (EuclideanSpace.single j a) := by
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  rw [this, EuclideanSpace.inner_single_right]
  simp

theorem aux_p43_decrease {n : ℕ} (lo hi : Fin n → EReal) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hΩU : box lo hi ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ box lo hi)
    (ε ρ : ℝ) (hε : 0 < ε)
    (hρ : ∀ y, dist x y < ρ → dist (fderiv ℝ f x) (fderiv ℝ f y) < ε)
    (j : Fin n) (hq : ε < |(projQ lo hi f x) j|) (a : ℝ)
    (ha : 0 < a * (projQ lo hi f x) j) (haε : |a| ≤ ε) (haρ : |a| < ρ) :
    x + EuclideanSpace.single j a ∈ box lo hi ∧ f (x + EuclideanSpace.single j a) < f x := by
  set g := gradient f x j with hg
  set Q := (projQ lo hi f x) j with hQ
  set y := clampCoord (lo j) (hi j) (x j - g) with hy
  have hQy : Q = y - x j := by rw [hQ, aux_p43_projQ_apply]
  obtain ⟨hy1, hy2, hy3, hy4⟩ := aux_p43_clamp (lo j) (hi j) (x j) (x j - g) (hx j).1 (hx j).2
  rw [← hy] at hy1 hy2 hy3 hy4
  -- sign information
  have hcase : (0 < Q ∧ 0 < a ∧ a ≤ Q ∧ g < -ε) ∨ (Q < 0 ∧ a < 0 ∧ Q ≤ a ∧ ε < g) := by
    rcases lt_trichotomy Q 0 with h | h | h
    · right
      have ha' : a < 0 := by
        by_contra hc; push Not at hc; nlinarith
      have habsQ : |Q| = -Q := abs_of_neg h
      have habsa : |a| = -a := abs_of_neg ha'
      refine ⟨h, ha', by linarith, ?_⟩
      have := hy4 (by linarith)
      linarith
    · exfalso; rw [h] at ha; simp at ha
    · left
      have ha' : 0 < a := by
        by_contra hc; push Not at hc; nlinarith
      have habsQ : |Q| = Q := abs_of_pos h
      have habsa : |a| = a := abs_of_pos ha'
      refine ⟨h, ha', by linarith, ?_⟩
      have := hy3 (by linarith)
      linarith
  have hmem : x + EuclideanSpace.single j a ∈ box lo hi := by
    intro l
    by_cases hl : l = j
    · subst hl
      have e : ((x + EuclideanSpace.single l a) l : ℝ) = x l + a := by simp
      rw [e]
      rcases hcase with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
      · constructor
        · exact (hx l).1.trans (EReal.coe_le_coe_iff.2 (by linarith))
        · exact le_trans (EReal.coe_le_coe_iff.2 (by linarith)) hy2
      · constructor
        · exact le_trans hy1 (EReal.coe_le_coe_iff.2 (by linarith))
        · exact le_trans (EReal.coe_le_coe_iff.2 (by linarith)) (hx l).2
    · have e : ((x + EuclideanSpace.single j a) l : ℝ) = x l := by simp [hl]
      rw [e]
      exact hx l
  refine ⟨hmem, ?_⟩
  -- mean value inequality on s = box ∩ ball x ρ
  set s := box lo hi ∩ Metric.ball x ρ with hs
  have hρpos : 0 < ρ := lt_of_le_of_lt (abs_nonneg a) haρ
  have hsc : Convex ℝ s := (aux_p43_box_convex lo hi).inter (convex_ball x ρ)
  have hxs : x ∈ s := ⟨hx, Metric.mem_ball_self hρpos⟩
  have hvs : x + EuclideanSpace.single j a ∈ s := by
    refine ⟨hmem, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    simpa using haρ
  have hdiff : ∀ z ∈ s, DifferentiableAt ℝ f z := by
    intro z hz
    exact (hf.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds (hΩU hz.1))
  have hbound : ∀ z ∈ s, ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ ε := by
    intro z hz
    have h1 : dist x z < ρ := by
      have := hz.2
      rw [Metric.mem_ball] at this
      rwa [dist_comm]
    have h2 := hρ z h1
    rw [dist_comm, dist_eq_norm] at h2
    exact h2.le
  have key := hsc.norm_image_sub_le_of_norm_fderiv_le' hdiff hbound hxs hvs
  rw [add_sub_cancel_left, aux_p43_fderiv_single] at key
  have hn : ‖EuclideanSpace.single j a‖ = |a| := by simp
  rw [hn] at key
  have key2 := (le_abs_self _).trans (Real.norm_eq_abs _ ▸ key)
  rw [← hg] at key2
  rcases hcase with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · rw [abs_of_pos h2] at key2
    nlinarith
  · rw [abs_of_neg h2] at key2
    nlinarith

end LewisTorczon.BoundPS

open LewisTorczon.BoundPS

theorem solution {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hΩU : box lo hi ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (R : GPSRun n m) (hR : IsGPSRun P lo hi f R)
    (hcpt : IsCompact (levelSet lo hi f (R.x 0))) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ k, R.Δ k < δ → η < ‖projQ lo hi f (R.x k)‖ →
      f (R.x k + R.s k) < f (R.x k) ∧ R.x k + R.s k ∈ box lo hi := by
  intro η hη
  set ε : ℝ := η / (n + 1) with hεdef
  have hε : 0 < ε := by positivity
  have hcont : ∀ a ∈ levelSet lo hi f (R.x 0), ContinuousAt (fderiv ℝ f) a := fun a ha =>
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).continuousAt (hU.mem_nhds (hΩU ha.1))
  have hunif := hcpt.uniformContinuousAt_of_continuousAt (fderiv ℝ f) hcont
    (Metric.dist_mem_uniformity hε)
  obtain ⟨ρ, hρ, hρ'⟩ := Metric.mem_uniformity_dist.1 hunif
  set D : ℝ := ∑ M ∈ P.𝕄, ∑ i, |(P.B * M.map (fun a : ℤ => (a : ℝ))) i i| + 1 with hD
  have hD0 : 0 ≤ ∑ M ∈ P.𝕄, ∑ i, |(P.B * M.map (fun a : ℤ => (a : ℝ))) i i| :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hDpos : 0 < D := by linarith
  refine ⟨min ρ ε / D, div_pos (lt_min hρ hε) hDpos, ?_⟩
  intro k hk hq
  refine ⟨?_, hR.step_feasible k⟩
  apply hR.simple_decrease k
  have hxk := aux_p43_iter_mem P lo hi f R hR k
  obtain ⟨j, hj⟩ := aux_p43_exists_coord (projQ lo hi f (R.x k)) η hη hq
  have hd := hR.diag k
  have hdj := aux_p43_diag_ne P (R.M k) (P.𝕄_det_ne_zero _ (hR.M_mem k)) hd j
  have hΔ := aux_p43_Δ_pos P lo hi f R hR k
  set A := P.B * (R.M k).map (fun a : ℤ => (a : ℝ)) with hA
  set Q := (projQ lo hi f (R.x k)) j with hQ
  have hQ0 : Q ≠ 0 := by
    intro h; rw [h, abs_zero] at hj; linarith
  have hAle : |A j j| ≤ D - 1 := by
    have h1 : |A j j| ≤ ∑ i, |A i i| :=
      Finset.single_le_sum (f := fun i => |A i i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have h2 : ∑ i, |A i i| ≤ ∑ M ∈ P.𝕄, ∑ i, |(P.B * M.map (fun a : ℤ => (a : ℝ))) i i| :=
      Finset.single_le_sum (f := fun M => ∑ i, |(P.B * M.map (fun a : ℤ => (a : ℝ))) i i|)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (hR.M_mem k)
    linarith
  have hkD : R.Δ k * D < min ρ ε := (lt_div_iff₀ hDpos).1 hk
  have habs : |R.Δ k * A j j| < min ρ ε := by
    rw [abs_mul, abs_of_pos hΔ]
    have : R.Δ k * |A j j| ≤ R.Δ k * (D - 1) := mul_le_mul_of_nonneg_left hAle hΔ.le
    nlinarith
  have habsρ : |R.Δ k * A j j| < ρ := lt_of_lt_of_le habs (min_le_left _ _)
  have habsε : |R.Δ k * A j j| ≤ ε := (lt_of_lt_of_le habs (min_le_right _ _)).le
  have hρx : ∀ y, dist (R.x k) y < ρ → dist (fderiv ℝ f (R.x k)) (fderiv ℝ f y) < ε :=
    fun y hy => hρ' hy hxk
  have hprod : R.Δ k * A j j * Q ≠ 0 := mul_ne_zero (mul_ne_zero hΔ.ne' hdj) hQ0
  by_cases hs : 0 < R.Δ k * A j j * Q
  · refine ⟨(R.M k).transpose j, ⟨j, Or.inl rfl⟩, ?_⟩
    rw [aux_p43_step P (R.M k) hd]
    exact aux_p43_decrease lo hi f U hU hΩU hf (R.x k) hxk.1 ε ρ hε hρx j hj _ hs habsε habsρ
  · refine ⟨-((R.M k).transpose j), ⟨j, Or.inr rfl⟩, ?_⟩
    have e : stepOf P (R.Δ k) (-((R.M k).transpose j)) =
        EuclideanSpace.single j (-(R.Δ k * A j j)) := by
      rw [aux_p43_step_neg, aux_p43_step P (R.M k) hd]
      ext l
      by_cases hl : l = j
      · subst hl; simp; exact Or.inl rfl
      · simp [hl]
    rw [e]
    have hs' : 0 < -(R.Δ k * A j j) * Q := by
      have : R.Δ k * A j j * Q < 0 := lt_of_le_of_ne (not_lt.1 hs) hprod
      linarith
    exact aux_p43_decrease lo hi f U hU hΩU hf (R.x k) hxk.1 ε ρ hε hρx j hj _ hs'
      (by rw [abs_neg]; exact habsε) (by rw [abs_neg]; exact habsρ)
