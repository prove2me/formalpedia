-- Prove2me | solution 1 for MirrorBP.JEA.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T18:06:29.216191+00:00
-- url     : https://prove2.me/submissions/5fd0937b-1c77-4f30-81bb-4424dacc0e7b

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_MBP
import Definitions.Def_MirrorBP_JEA_SPP

namespace MirrorBP.JEA.Lemma1Aux

open Finset MirrorBP.JEA Set

/-- A function with nonnegative derivative on `[x, y]` is larger at `y`. -/
theorem le_of_hasDeriv_nonneg (g g' : ℝ → ℝ) (x y : ℝ) (hxy : x ≤ y)
    (hd : ∀ u ∈ Icc x y, HasDerivAt g (g' u) u) (hpos : ∀ u ∈ Icc x y, 0 ≤ g' u) :
    g x ≤ g y := by
  have hc : ContinuousOn g (Icc x y) := fun u hu => (hd u hu).continuousAt.continuousWithinAt
  have hdi : DifferentiableOn ℝ g (interior (Icc x y)) := fun u hu =>
    (hd u (interior_subset hu)).differentiableAt.differentiableWithinAt
  have := (convex_Icc x y).mul_sub_le_image_sub_of_le_deriv hc hdi (C := 0)
    (fun u hu => by rw [(hd u (interior_subset hu)).deriv]; exact hpos u (interior_subset hu))
    x (left_mem_Icc.mpr hxy) y (right_mem_Icc.mpr hxy) hxy
  linarith

/-- Lipschitz bound from a derivative bound: `f a − f x ≤ B (a − x)` for `x ≤ a`. -/
theorem lip_bound (f : ℝ → ℝ) (hfC1 : ContDiffOn ℝ 1 f (Ioi 0)) (x a B : ℝ) (hx : 0 < x)
    (hxa : x ≤ a) (hB : ∀ u ∈ Icc x a, |deriv f u| ≤ B) : f a - f x ≤ B * (a - x) := by
  have hdf : ∀ u ∈ Icc x a, HasDerivAt f (deriv f u) u := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hx hu.1
    have : DifferentiableAt ℝ f u :=
      ((hfC1.differentiableOn one_ne_zero) u hu0).differentiableAt (Ioi_mem_nhds hu0)
    exact this.hasDerivAt
  have := le_of_hasDeriv_nonneg (fun u => B * u - f u) (fun u => B - deriv f u) x a hxa
    (fun u hu => ((hasDerivAt_id u).const_mul B |>.sub (hdf u hu)).congr_deriv (by simp))
    (fun u hu => by have := hB u hu; have := le_abs_self (deriv f u); linarith)
  linarith

/-- Second-order bound on the left: `F₁(a) − F₁(a − h) ≥ h f(a) − B h²/2`. -/
theorem taylor_left (f F₁ : ℝ → ℝ) (hfC1 : ContDiffOn ℝ 1 f (Ioi 0))
    (hF : ∀ x : ℝ, 0 < x → HasDerivAt F₁ (f x) x) (a h B : ℝ) (hh : 0 ≤ h) (hpos : 0 < a - h)
    (hB : ∀ u ∈ Icc (a - h) a, |deriv f u| ≤ B) :
    h * f a - B * h ^ 2 / 2 ≤ F₁ a - F₁ (a - h) := by
  have hψ := le_of_hasDeriv_nonneg (fun x => F₁ x - x * f a - B * (a - x) ^ 2 / 2)
    (fun x => f x - f a + B * (a - x)) (a - h) a (by linarith)
    (fun u hu => by
      have h1 := hF u (by linarith [hu.1])
      have h2 : HasDerivAt (fun x => x * f a) (f a) u := by
        simpa using (hasDerivAt_id u).mul_const (f a)
      have h3 : HasDerivAt (fun x => B * (a - x) ^ 2 / 2) (-(B * (a - u))) u := by
        have := ((hasDerivAt_id' u).const_sub a).pow 2 |>.const_mul B |>.div_const 2
        exact this.congr_deriv (by ring)
      exact ((h1.sub h2).sub h3).congr_deriv (by ring))
    (fun u hu => by
      have := lip_bound f hfC1 u a B (by linarith [hu.1]) hu.2
        (fun v hv => hB v ⟨by linarith [hu.1, hv.1], hv.2⟩)
      linarith)
  nlinarith

/-- Second-order bound on the right: `F₁(b) − F₁(b + h) ≥ −h f(b) − B h²/2`. -/
theorem taylor_right (f F₁ : ℝ → ℝ) (hfC1 : ContDiffOn ℝ 1 f (Ioi 0))
    (hF : ∀ x : ℝ, 0 < x → HasDerivAt F₁ (f x) x) (b h B : ℝ) (hh : 0 ≤ h) (hpos : 0 < b)
    (hB : ∀ u ∈ Icc b (b + h), |deriv f u| ≤ B) :
    -(h * f b) - B * h ^ 2 / 2 ≤ F₁ b - F₁ (b + h) := by
  have hχ := le_of_hasDeriv_nonneg (fun x => -(F₁ x - x * f b - B * (x - b) ^ 2 / 2))
    (fun x => -(f x - f b - B * (x - b))) b (b + h) (by linarith)
    (fun u hu => by
      have h1 := hF u (by linarith [hu.1])
      have h2 : HasDerivAt (fun x => x * f b) (f b) u := by
        simpa using (hasDerivAt_id u).mul_const (f b)
      have h3 : HasDerivAt (fun x => B * (x - b) ^ 2 / 2) (B * (u - b)) u := by
        have := ((hasDerivAt_id' u).sub_const b).pow 2 |>.const_mul B |>.div_const 2
        exact this.congr_deriv (by ring)
      exact ((h1.sub h2).sub h3).neg)
    (fun u hu => by
      have := lip_bound f hfC1 b u B hpos hu.1
        (fun v hv => hB v ⟨hv.1, by linarith [hu.2, hv.2]⟩)
      linarith)
  nlinarith

variable {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]

theorem Kt_pos (m K : ℕ) (hK : 1 ≤ K) : 0 < Kt m K := by
  unfold Kt
  have : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have : 0 ≤ (m : ℝ) * Real.sqrt K := by positivity
  linarith

theorem qbar_pos (K : ℕ) (hK : 1 ≤ K) (q : V → ℕ) (j : V) : 0 < qbar K q j := by
  unfold qbar
  have : 0 < Real.sqrt K := Real.sqrt_pos.mpr (by exact_mod_cast hK)
  have : (0 : ℝ) ≤ q j := by positivity
  exact div_pos (by linarith) (Kt_pos _ K hK)

theorem step_cast (q : V → ℕ) (j0 k0 : V) (hj : 0 < q j0) (i : V) :
    ((step q (some (j0, k0)) i : ℕ) : ℝ)
      = q i - (if i = j0 then 1 else 0) + (if i = k0 then 1 else 0) := by
  simp only [step, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  by_cases h1 : i = j0
  · subst h1
    have : 1 ≤ q i := hj
    by_cases h2 : i = k0
    · subst h2; simp; rw [Nat.cast_sub this]; simp
    · simp [h2]; rw [Nat.cast_sub this]; simp
  · by_cases h2 : i = k0
    · subst h2; simp [h1]
    · simp [h1, h2]

theorem qbar_step (K : ℕ) (q : V → ℕ) (j0 k0 : V) (hj : 0 < q j0) (i : V) :
    qbar K (step q (some (j0, k0))) i
      = qbar K q i - (if i = j0 then 1 else 0) / Kt (Fintype.card V) K
        + (if i = k0 then 1 else 0) / Kt (Fintype.card V) K := by
  unfold qbar
  rw [step_cast q j0 k0 hj i]
  ring

theorem gDual_term (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (f : ℝ → ℝ) (K : ℕ)
    (sel : (V → ℕ) → Ty → V × V) (hsel : IsArgmaxSel P D w f K sel) (q : V → ℕ) (τ : Ty) :
    (if h : (P τ ×ˢ D τ).Nonempty then
      (P τ ×ˢ D τ).sup' h (fun p => max 0 (w p.1 τ p.2 + f (qbar K q p.1) - f (qbar K q p.2)))
      else 0) = max 0 (score w f K q τ (sel q τ).1 (sel q τ).2) := by
  have hmem : (sel q τ) ∈ P τ ×ˢ D τ := mem_product.mpr (hsel.mem q τ)
  have hne : (P τ ×ˢ D τ).Nonempty := ⟨_, hmem⟩
  rw [dif_pos hne]
  apply le_antisymm
  · apply sup'_le
    intro p hp
    have := hsel.max q τ p.1 (mem_product.mp hp).1 p.2 (mem_product.mp hp).2
    unfold score at this
    exact max_le_max le_rfl this
  · exact le_sup'_of_le _ hmem (by unfold score; exact le_rfl)


theorem step_self (q : V → ℕ) (j : V) (hj : 0 < q j) : step q (some (j, j)) = q := by
  funext i
  simp only [step, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  split_ifs with h
  · subst h; omega
  · simp

theorem Fpot_step (F₁ : ℝ → ℝ) (K : ℕ) (q : V → ℕ) (j k : V) (hj : 0 < q j) (hjk : j ≠ k) :
    Fpot F₁ (qbar K q) - Fpot F₁ (qbar K (step q (some (j, k))))
      = (F₁ (qbar K q j) - F₁ (qbar K q j - 1 / Kt (Fintype.card V) K))
        + (F₁ (qbar K q k) - F₁ (qbar K q k + 1 / Kt (Fintype.card V) K)) := by
  unfold Fpot
  rw [← sum_sub_distrib]
  rw [sum_eq_add j k hjk]
  · rw [qbar_step K q j k hj j, qbar_step K q j k hj k]
    simp [hjk, Ne.symm hjk]
  · intro c _ hc
    rw [qbar_step K q j k hj c]
    simp [hc.1, hc.2]
  · intro h; exact absurd (Finset.mem_univ j) h
  · intro h; exact absurd (Finset.mem_univ k) h

/-- The one-type inequality behind Lemma 1. -/
theorem per_type (P D : Ty → Finset V) (w : V → Ty → V → ℝ)
    (hw : ∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1)
    (K : ℕ) (hK : 1 ≤ K) (q : V → ℕ)
    (f F₁ : ℝ → ℝ) (hf : StrictMonoOn f (Set.Ioi 0)) (hfC1 : ContDiffOn ℝ 1 f (Set.Ioi 0))
    (hF : ∀ x : ℝ, 0 < x → HasDerivAt F₁ (f x) x)
    (sel : (V → ℕ) → Ty → V × V) (hsel : IsArgmaxSel P D w f K sel) (B : ℝ)
    (hB : ∀ j, ∀ x ∈ Set.Icc (qbar K q j - 1 / Kt (Fintype.card V) K)
        (qbar K q j + 1 / Kt (Fintype.card V) K), 0 < x → |deriv f x| ≤ B) (hB0 : 0 ≤ B)
    (τ : Ty) :
    max 0 (score w f K q τ (sel q τ).1 (sel q τ).2) - pay w τ (mbpDecision w f K sel q τ)
      ≤ Kt (Fintype.card V) K * (Fpot F₁ (qbar K q)
          - Fpot F₁ (qbar K (step q (mbpDecision w f K sel q τ))))
        + B / Kt (Fintype.card V) K + (if ∃ j, q j = 0 then (1 : ℝ) else 0) := by
  have hKt := Kt_pos (Fintype.card V) K hK
  set κ := Kt (Fintype.card V) K with hκ
  rcases hp : sel q τ with ⟨j, k⟩
  have hjP : j ∈ P τ := by have := (hsel.mem q τ).1; rw [hp] at this; exact this
  have hkD : k ∈ D τ := by have := (hsel.mem q τ).2; rw [hp] at this; exact this
  have hind0 : (0 : ℝ) ≤ (if ∃ j, q j = 0 then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  have hBk : 0 ≤ B / κ := div_nonneg hB0 hKt.le
  unfold mbpDecision
  rw [hp]
  simp only
  by_cases hc : 0 ≤ score w f K q τ j k ∧ 0 < q j
  · rw [if_pos hc]
    -- MBP serves the customer with (j, k)
    rw [max_eq_right hc.1]
    simp only [pay, score]
    by_cases hjk : j = k
    · subst hjk
      rw [step_self q j hc.2]
      simp only [sub_self, mul_zero, zero_add]
      linarith
    · rw [Fpot_step F₁ K q j k hc.2 hjk]
      have hqj : (1 : ℝ) ≤ q j := by exact_mod_cast hc.2
      have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr (by exact_mod_cast hK)
      have hpos : 0 < qbar K q j - 1 / κ := by
        unfold qbar
        rw [← hκ, div_sub_div_same]
        apply div_pos _ hKt
        linarith
      have hh : 0 ≤ 1 / κ := by positivity
      have tl := taylor_left f F₁ hfC1 hF (qbar K q j) (1 / κ) B hh hpos
        (fun u hu => hB j u ⟨hu.1, by linarith [hu.2]⟩ (by linarith [hu.1]))
      have tr := taylor_right f F₁ hfC1 hF (qbar K q k) (1 / κ) B hh (qbar_pos K hK q k)
        (fun u hu => hB k u ⟨by linarith [hu.1], hu.2⟩
          (by linarith [hu.1, qbar_pos K hK q k]))
      have e1 : κ * (1 / κ * f (qbar K q j) - B * (1 / κ) ^ 2 / 2
          + (-(1 / κ * f (qbar K q k)) - B * (1 / κ) ^ 2 / 2))
          = f (qbar K q j) - f (qbar K q k) - B / κ := by
        field_simp; ring
      have e2 := mul_le_mul_of_nonneg_left (add_le_add tl tr) hKt.le
      linarith
  · rw [if_neg hc]
    -- MBP drops the customer
    simp only [pay, step, sub_self, mul_zero, zero_add]
    by_cases hs : 0 ≤ score w f K q τ j k
    · have hq0 : q j = 0 := by
        by_contra hne
        exact hc ⟨hs, Nat.pos_of_ne_zero hne⟩
      rw [if_pos ⟨j, hq0⟩, max_eq_right hs]
      have hle : qbar K q j ≤ qbar K q k := by
        unfold qbar
        apply div_le_div_of_nonneg_right _ hKt.le
        rw [hq0]; simp
      have hfm := hf.monotoneOn (qbar_pos K hK q j) (qbar_pos K hK q k) hle
      have hw1 : w j τ k ≤ 1 := le_trans (le_abs_self _) (hw τ j hjP k hkD)
      unfold score
      linarith
    · push Not at hs
      rw [max_eq_left hs.le]
      linarith

end MirrorBP.JEA.Lemma1Aux

open Finset MirrorBP.JEA

theorem solution {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]
    (P D : Ty → Finset V) (w : V → Ty → V → ℝ)
    (hm : 1 < Fintype.card V) (hP : ∀ τ, (P τ).Nonempty) (hD : ∀ τ, (D τ).Nonempty)
    (hw : ∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, |w j τ k| ≤ 1)
    (φ : Ty → ℝ) (hφ : IsRate φ) (K : ℕ) (hK : 1 ≤ K) (q : V → ℕ) (hq : q ∈ StateSpace V K)
    (f F₁ : ℝ → ℝ) (hf : StrictMonoOn f (Set.Ioi 0)) (hfC1 : ContDiffOn ℝ 1 f (Set.Ioi 0))
    (hF : ∀ x : ℝ, 0 < x → HasDerivAt F₁ (f x) x)
    (sel : (V → ℕ) → Ty → V × V) (hsel : IsArgmaxSel P D w f K sel) (B : ℝ)
    (hB : ∀ j, ∀ x ∈ Set.Icc (qbar K q j - 1 / Kt (Fintype.card V) K)
        (qbar K q j + 1 / Kt (Fintype.card V) K), 0 < x → |deriv f x| ≤ B) :
    Wspp P D w φ - ∑ τ, φ τ * pay w τ (mbpDecision w f K sel q τ)
      ≤ Kt (Fintype.card V) K * (Fpot F₁ (qbar K q)
            - ∑ τ, φ τ * Fpot F₁ (qbar K (step q (mbpDecision w f K sel q τ))))
        + B / Kt (Fintype.card V) K
        + (Wspp P D w φ - gDual P D w φ (fun j => f (qbar K q j)))
        + (if ∃ j, q j = 0 then (1 : ℝ) else 0) := by
  have hKt := Lemma1Aux.Kt_pos (Fintype.card V) K hK
  obtain ⟨j0⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hB0 : 0 ≤ B := by
    have hpos := Lemma1Aux.qbar_pos K hK q j0
    have h1 : 0 ≤ 1 / Kt (Fintype.card V) K := by positivity
    have := hB j0 (qbar K q j0) ⟨by linarith, by linarith⟩ hpos
    exact le_trans (abs_nonneg _) this
  have hg : gDual P D w φ (fun j => f (qbar K q j))
      = ∑ τ, φ τ * max 0 (score w f K q τ (sel q τ).1 (sel q τ).2) := by
    unfold gDual
    apply sum_congr rfl
    intro τ _
    rw [Lemma1Aux.gDual_term P D w f K sel hsel q τ]
  have hpt := Lemma1Aux.per_type P D w hw K hK q f F₁ hf hfC1 hF sel hsel B hB hB0
  set c := B / Kt (Fintype.card V) K + (if ∃ j, q j = 0 then (1 : ℝ) else 0)
  have hsum : ∑ τ, φ τ * (max 0 (score w f K q τ (sel q τ).1 (sel q τ).2)
        - pay w τ (mbpDecision w f K sel q τ))
      ≤ ∑ τ, φ τ * (Kt (Fintype.card V) K * (Fpot F₁ (qbar K q)
          - Fpot F₁ (qbar K (step q (mbpDecision w f K sel q τ)))) + c) := by
    apply sum_le_sum
    intro τ _
    apply mul_le_mul_of_nonneg_left _ (hφ.1 τ)
    have := hpt τ
    linarith
  have e1 : ∑ τ, φ τ * (max 0 (score w f K q τ (sel q τ).1 (sel q τ).2)
        - pay w τ (mbpDecision w f K sel q τ))
      = gDual P D w φ (fun j => f (qbar K q j)) - ∑ τ, φ τ * pay w τ (mbpDecision w f K sel q τ) := by
    rw [hg, ← sum_sub_distrib]
    apply sum_congr rfl; intro τ _; ring
  have e2 : ∑ τ, φ τ * (Kt (Fintype.card V) K * (Fpot F₁ (qbar K q)
          - Fpot F₁ (qbar K (step q (mbpDecision w f K sel q τ)))) + c)
      = Kt (Fintype.card V) K * (Fpot F₁ (qbar K q)
          - ∑ τ, φ τ * Fpot F₁ (qbar K (step q (mbpDecision w f K sel q τ)))) + c := by
    have : ∑ τ, φ τ * (Kt (Fintype.card V) K * (Fpot F₁ (qbar K q)
          - Fpot F₁ (qbar K (step q (mbpDecision w f K sel q τ)))) + c)
        = Kt (Fintype.card V) K * (Fpot F₁ (qbar K q) * ∑ τ, φ τ
          - ∑ τ, φ τ * Fpot F₁ (qbar K (step q (mbpDecision w f K sel q τ)))) + c * ∑ τ, φ τ := by
      simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      apply sum_congr rfl; intro τ _; ring
    rw [this, hφ.2]; ring
  linarith
