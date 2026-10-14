-- Prove2me | solution 1 for ModernOnlineLearning.FTRL.corollary_7_6
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:16:30.042022+00:00
-- url     : https://prove2.me/submissions/de5782f5-4160-4bbd-a2e7-98c063110456

import Mathlib
import Definitions.Def_ModernOnlineLearning_FTRL_Defs

set_option autoImplicit false

namespace RRAux_ModernOnlineLearning_FTRL_corollary_7_6

open ModernOnlineLearning.FTRL

theorem seg_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) (hv : Convex ℝ V) (f : E → ℝ) (hf : IsSubdifferentiableOn V f)
    (x y : E) (hx : x ∈ V) (hy : y ∈ V) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    f (a • x + b • y) ≤ a * f x + b * f y := by
  obtain ⟨g, hg⟩ := hf _ (hv hx hy ha hb hab)
  have h1 := hg x
  have h2 := hg y
  have e : a * g (x - (a • x + b • y)) + b * g (y - (a • x + b • y)) = 0 := by
    rw [← smul_eq_mul, ← smul_eq_mul, ← map_smul, ← map_smul, ← map_add]
    have : a • (x - (a • x + b • y)) + b • (y - (a • x + b • y)) = 0 := by
      rw [smul_sub, smul_sub, smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
      have hb' : b = 1 - a := by linarith
      subst hb'
      module
    rw [this, map_zero]
  have k1 := mul_le_mul_of_nonneg_left h1 ha
  have k2 := mul_le_mul_of_nonneg_left h2 hb
  rw [mul_add] at k1 k2
  have hw : f (a • x + b • y) = a * f (a • x + b • y) + b * f (a • x + b • y) := by
    rw [← add_mul, hab, one_mul]
  linarith

theorem growth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) (ψ h : E → ℝ) (c mu m : ℝ) (hc : 0 < c) (hmu : 0 ≤ mu)
    (hψ : StrongConvexOn V mu ψ)
    (hh : ∀ x ∈ V, ∀ y ∈ V, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      h (a • x + b • y) ≤ a * h x + b * h y)
    (x y : E) (hx : x ∈ V) (hy : y ∈ V)
    (hmin : ∀ w ∈ V, c * (ψ x - m) + h x ≤ c * (ψ w - m) + h w) :
    c * mu / 2 * ‖y - x‖ ^ 2 ≤ (c * (ψ y - m) + h y) - (c * (ψ x - m) + h x) := by
  set D := (c * (ψ y - m) + h y) - (c * (ψ x - m) + h x) with hD
  set K := c * mu / 2 * ‖y - x‖ ^ 2 with hK
  have hD0 : 0 ≤ D := by have := hmin y hy; linarith
  have key : ∀ s : ℝ, 0 < s → s < 1 → (1 - s) * K ≤ D := by
    intro s hs0 hs1
    have hw := hψ.2 hx hy (show (0:ℝ) ≤ 1 - s by linarith) hs0.le (show 1 - s + s = 1 by ring)
    have hw2 := hh x hx y hy (1 - s) s (by linarith) hs0.le (by ring)
    have hm := hmin _ (hψ.1 hx hy (by linarith) hs0.le (by ring) : (1 - s) • x + s • y ∈ V)
    simp only [smul_eq_mul] at hw
    rw [norm_sub_rev] at hw
    have hcw := mul_le_mul_of_nonneg_left hw hc.le
    -- s * D ≥ s * (1-s) * K
    have : s * ((1 - s) * K) ≤ s * D := by
      rw [hD, hK]
      nlinarith
    exact le_of_mul_le_mul_left this hs0
  by_contra hlt
  push Not at hlt
  have hK0 : 0 < K := lt_of_le_of_lt hD0 hlt
  have := key ((K - D) / (2 * K)) (by apply div_pos <;> linarith)
    (by rw [div_lt_one (by linarith)]; linarith)
  have e : (1 - (K - D) / (2 * K)) * K = (K + D) / 2 := by field_simp; ring
  rw [e] at this
  linarith

theorem quad_bound (A G r η mu : ℝ) (hη : 0 < η) (hmu : 0 < mu)
    (h : A ≤ G * r - (1 / η) * mu / 2 * r ^ 2) :
    A ≤ η / (2 * mu) * G ^ 2 := by
  have : G * r - (1 / η) * mu / 2 * r ^ 2 ≤ η / (2 * mu) * G ^ 2 := by
    have e : η / (2 * mu) * G ^ 2 - (G * r - (1 / η) * mu / 2 * r ^ 2) =
        (η * G - mu * r) ^ 2 / (2 * η * mu) := by field_simp; ring
    have : 0 ≤ (η * G - mu * r) ^ 2 / (2 * η * mu) := by positivity
    linarith
  linarith

theorem tele (a : ℕ → ℝ) (n : ℕ) :
    ∑ t ∈ Finset.Icc 1 n, (a t - a (t + 1)) = a 1 - a (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]; ring

theorem sqrt_sum (n : ℕ) : ∑ t ∈ Finset.Icc 1 n, 1 / Real.sqrt (t : ℝ) ≤ 2 * Real.sqrt n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h1 : 0 < Real.sqrt ((k + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have h2 : Real.sqrt (k : ℝ) ≤ Real.sqrt ((k + 1 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt (by push_cast; linarith)
    have h3 : Real.sqrt ((k + 1 : ℕ) : ℝ) ^ 2 = ((k + 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
    have h4 : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt (by positivity)
    have h5 : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
    have : 1 / Real.sqrt ((k + 1 : ℕ) : ℝ) ≤
        2 * Real.sqrt ((k + 1 : ℕ) : ℝ) - 2 * Real.sqrt k := by
      rw [div_le_iff₀ h1]
      push_cast at h3 ⊢
      nlinarith
    linarith

theorem opnorm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) (f : E → ℝ) (L : ℝ) (hL : 0 ≤ L) (hf : IsLipschitzOnOpenNeighborhood V f L)
    (x : E) (hx : x ∈ V) (g : E →L[ℝ] ℝ) (hg : IsSubgradientAt f x g) : ‖g‖ ≤ L := by
  obtain ⟨U, hU, hVU, hlip⟩ := hf
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x (hVU hx)
  have one : ∀ v : E, g v ≤ L * ‖v‖ := by
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    set δ := ε / (2 * ‖v‖) with hδ
    have hδpos : 0 < δ := by positivity
    have hmem : x + δ • v ∈ U := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hδpos, hδ]
      field_simp
      linarith
    have h1 := hg (x + δ • v)
    rw [add_sub_cancel_left, map_smul, smul_eq_mul] at h1
    have h2 := hlip _ hmem x (hVU hx)
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos] at h2
    have h3 := (abs_le.mp h2).2
    have : δ * g v ≤ δ * (L * ‖v‖) := by nlinarith
    exact le_of_mul_le_mul_left this hδpos
  apply ContinuousLinearMap.opNorm_le_bound _ hL
  intro v
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have := one (-v); rw [map_neg, norm_neg] at this; linarith
  · exact one v


theorem scal (α L mu s τ : ℝ) (hs : 0 < s) (hτ : 0 < τ) (hL : 0 < L) (hmu : s ^ 2 = mu) :
    α * s / (L * τ) / (2 * mu) * L ^ 2 = α * L / (2 * s) * (1 / τ) := by
  subst hmu; field_simp

theorem part1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) (ψ : E → ℝ)
    (mu : ℝ) (hmu : 0 < mu) (hψstrong : StrongConvexOn V mu ψ)
    (z₀ : E) (hz₀ : IsMinimizerOn V ψ z₀)
    (ℓ : ℕ → E → ℝ) (η : ℕ → ℝ) (n : ℕ)
    (hη : ∀ s < n + 1, 0 < η s)
    (x : ℕ → E)
    (hRun : IsFTRLRunUpTo V (scheduledRegularizer ψ (ψ z₀) η (n + 1)) ℓ x (n + 1))
    (hSubdiff : ∀ t ∈ Finset.Icc 1 (n + 1), IsSubdifferentiableOn V (ℓ t))
    (g : ℕ → (E →L[ℝ] ℝ))
    (hg : ∀ t ∈ Finset.Icc 1 (n + 1), IsSubgradientAt (ℓ t) (x t) (g t))
    (u : E) (hu : u ∈ V) :
    (∑ t ∈ Finset.Icc 1 (n + 1), (ℓ t (x t) - ℓ t u)) ≤
      (ψ u - ψ z₀) / η n +
      (∑ t ∈ Finset.Icc 1 (n + 1), η (t - 1) / (2 * mu) * ‖g t‖ ^ 2) +
      (∑ t ∈ Finset.Icc 1 n, (1 / η (t - 1) - 1 / η t) * (ψ (x (t + 1)) - ψ z₀)) := by
  set m := ψ z₀ with hm
  set Ψ := scheduledRegularizer ψ m η (n + 1) with hΨ
  have hΨle : ∀ t z, t ≤ n + 1 → Ψ t z = (ψ z - m) / η (t - 1) := by
    intro t z ht; simp only [hΨ, scheduledRegularizer, if_pos ht]
  have hΨlast : ∀ z, Ψ (n + 2) z = (ψ z - m) / η n := by
    intro z; simp only [hΨ, scheduledRegularizer, if_neg (show ¬ (n + 2 ≤ n + 1) by omega),
      Nat.add_sub_cancel]
  have hxV : ∀ t ∈ Finset.Icc 1 (n + 2), x t ∈ V := fun t ht => (hRun t ht).1
  have hmin : ∀ t ∈ Finset.Icc 1 (n + 2), ∀ y ∈ V, F Ψ ℓ t (x t) ≤ F Ψ ℓ t y :=
    fun t ht => (hRun t ht).2
  have hFsucc : ∀ t, 1 ≤ t → ∀ z, F Ψ ℓ (t + 1) z = F Ψ ℓ t z + ℓ t z + (Ψ (t + 1) z - Ψ t z) := by
    intro t ht z
    unfold F
    rw [Finset.sum_Ico_succ_top ht]; ring
  have hψnn : ∀ z ∈ V, 0 ≤ ψ z - m := fun z hz => by have := hz₀.2 z hz; rw [hm]; linarith
  -- per-step bound
  have hstep : ∀ t ∈ Finset.Icc 1 (n + 1),
      F Ψ ℓ t (x t) + ℓ t (x t) - F Ψ ℓ (t + 1) (x (t + 1)) ≤
        η (t - 1) / (2 * mu) * ‖g t‖ ^ 2 + (Ψ t (x (t + 1)) - Ψ (t + 1) (x (t + 1))) := by
    intro t ht
    have ht' := Finset.mem_Icc.mp ht
    have hηt : 0 < η (t - 1) := hη _ (by omega)
    have hxt : x t ∈ V := hxV t (by simp; omega)
    have hxt1 : x (t + 1) ∈ V := hxV (t + 1) (by simp; omega)
    have hFform : ∀ z, F Ψ ℓ t z = (1 / η (t - 1)) * (ψ z - m) +
        ∑ i ∈ Finset.Ico 1 t, ℓ i z := by
      intro z; unfold F; rw [hΨle t z ht'.2]; ring
    have hconv : ∀ a ∈ V, ∀ b ∈ V, ∀ p q : ℝ, 0 ≤ p → 0 ≤ q → p + q = 1 →
        (∑ i ∈ Finset.Ico 1 t, ℓ i (p • a + q • b)) ≤
          p * (∑ i ∈ Finset.Ico 1 t, ℓ i a) + q * (∑ i ∈ Finset.Ico 1 t, ℓ i b) := by
      intro a ha b hb p q hp hq hpq
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_Ico.mp hi
      exact seg_convex V hψstrong.1 (ℓ i) (hSubdiff i (by simp; omega)) a b ha hb p q hp hq hpq
    have hgr := growth V ψ (fun z => ∑ i ∈ Finset.Ico 1 t, ℓ i z) (1 / η (t - 1)) mu m
      (by positivity) hmu.le hψstrong hconv (x t) (x (t + 1)) hxt hxt1
      (fun w hw => by
        have := hmin t (by simp; omega) w hw
        rw [hFform, hFform] at this
        exact this)
    rw [← hFform, ← hFform] at hgr
    have hsg := hg t ht (x (t + 1))
    have hgle : -(‖g t‖ * ‖x (t + 1) - x t‖) ≤ g t (x (t + 1) - x t) := by
      have := ContinuousLinearMap.le_opNorm (g t) (x (t + 1) - x t)
      rw [Real.norm_eq_abs] at this
      linarith [neg_abs_le (g t (x (t + 1) - x t))]
    rw [hFsucc t ht'.1]
    have q := quad_bound (F Ψ ℓ t (x t) - F Ψ ℓ t (x (t + 1)) + (ℓ t (x t) - ℓ t (x (t + 1))))
      ‖g t‖ ‖x (t + 1) - x t‖ (η (t - 1)) mu hηt hmu (by linarith)
    linarith
  -- sum
  have hsum := Finset.sum_le_sum hstep
  rw [Finset.sum_add_distrib] at hsum
  have htel : ∑ t ∈ Finset.Icc 1 (n + 1),
      (F Ψ ℓ t (x t) + ℓ t (x t) - F Ψ ℓ (t + 1) (x (t + 1))) =
      (F Ψ ℓ 1 (x 1) - F Ψ ℓ (n + 1 + 1) (x (n + 1 + 1))) +
        ∑ t ∈ Finset.Icc 1 (n + 1), ℓ t (x t) := by
    rw [← tele (fun t => F Ψ ℓ t (x t)) (n + 1), ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro t _; ring
  rw [htel] at hsum
  -- the Ψ-difference sum
  have hΨsum : ∑ t ∈ Finset.Icc 1 (n + 1), (Ψ t (x (t + 1)) - Ψ (t + 1) (x (t + 1))) =
      ∑ t ∈ Finset.Icc 1 n, (1 / η (t - 1) - 1 / η t) * (ψ (x (t + 1)) - ψ z₀) := by
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hlast : Ψ (n + 1) (x (n + 1 + 1)) - Ψ (n + 1 + 1) (x (n + 1 + 1)) = 0 := by
      rw [hΨle _ _ le_rfl, show n + 1 + 1 = n + 2 by rfl, hΨlast, Nat.add_sub_cancel]; ring
    rw [hlast, add_zero]
    apply Finset.sum_congr rfl
    intro t ht
    have ht' := Finset.mem_Icc.mp ht
    rw [hΨle t _ (by omega), hΨle (t + 1) _ (by omega), Nat.add_sub_cancel]
    ring
  rw [hΨsum] at hsum
  -- comparator side
  have hu_sum : ∑ t ∈ Finset.Icc 1 (n + 1), ℓ t u = F Ψ ℓ (n + 2) u - Ψ (n + 2) u := by
    unfold F
    rw [show n + 2 = n + 1 + 1 by rfl, Finset.Ico_add_one_right_eq_Icc]; ring
  have hlastmin := hmin (n + 2) (by simp) u hu
  have hF1 : 0 ≤ F Ψ ℓ 1 (x 1) := by
    unfold F
    simp only [Finset.Ico_self, Finset.sum_empty, add_zero]
    rw [hΨle 1 _ (by omega)]
    exact div_nonneg (hψnn _ (hxV 1 (by simp))) (hη 0 (by omega)).le
  rw [Finset.sum_sub_distrib, hu_sum, hΨlast]
  have e2 : n + 1 + 1 = n + 2 := rfl
  rw [e2] at hsum
  linarith

end RRAux_ModernOnlineLearning_FTRL_corollary_7_6

open ModernOnlineLearning.FTRL in
-- Orabona, Corollary 7.6
theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (V : Set E) (hVclosed : IsClosed V) (hVconvex : Convex ℝ V)
    (hVnonempty : V.Nonempty) (ψ : E → ℝ)
    (hψclosed : IsClosedFunctionOn V ψ)
    (mu : ℝ) (hmu : 0 < mu) (hψstrong : StrongConvexOn V mu ψ)
    (z₀ : E) (hz₀ : IsMinimizerOn V ψ z₀)
    (ℓ : ℕ → E → ℝ) (η : ℕ → ℝ) (T : ℕ) (hT : 1 ≤ T)
    (hη : ∀ s < T, 0 < η s)
    (x : ℕ → E)
    (hRun : IsFTRLRunUpTo V (scheduledRegularizer ψ (ψ z₀) η T) ℓ x T)
    (hSubdiff : ∀ t ∈ Finset.Icc 1 T, IsSubdifferentiableOn V (ℓ t)) :
    (∀ g : ℕ → (E →L[ℝ] ℝ),
      (∀ t ∈ Finset.Icc 1 T, IsSubgradientAt (ℓ t) (x t) (g t)) →
      ∀ u ∈ V,
        (∑ t ∈ Finset.Icc 1 T, (ℓ t (x t) - ℓ t u)) ≤
          (ψ u - ψ z₀) / η (T - 1) +
          (∑ t ∈ Finset.Icc 1 T, η (t - 1) / (2 * mu) * ‖g t‖ ^ 2) +
          (∑ t ∈ Finset.Icc 1 (T - 1),
            (1 / η (t - 1) - 1 / η t) * (ψ (x (t + 1)) - ψ z₀))) ∧
    (∀ (α L : ℝ), 0 < α → 0 < L →
      (∀ t ∈ Finset.Icc 1 T, IsLipschitzOnOpenNeighborhood V (ℓ t) L) →
      (∀ t ∈ Finset.Icc 1 T,
        η (t - 1) = α * Real.sqrt mu / (L * Real.sqrt (t : ℝ))) →
      ∀ u ∈ V,
        (∑ t ∈ Finset.Icc 1 T, ℓ t (x t)) -
          (∑ t ∈ Finset.Icc 1 T, ℓ t u) ≤
          ((ψ u - ψ z₀) / α + α) * (L * Real.sqrt (T : ℝ) / Real.sqrt mu)) := by
  obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have P1 := RRAux_ModernOnlineLearning_FTRL_corollary_7_6.part1 V ψ mu hmu hψstrong z₀ hz₀ ℓ η n
    hη x hRun hSubdiff
  refine ⟨fun g hg u hu => P1 g hg u hu, ?_⟩
  intro α L hα hL hlip hsched u hu
  have hxV : ∀ t ∈ Finset.Icc 1 (n + 1 + 1), x t ∈ V := fun t ht => (hRun t ht).1
  have hex : ∀ t, ∃ g : E →L[ℝ] ℝ, t ∈ Finset.Icc 1 (n + 1) → IsSubgradientAt (ℓ t) (x t) g := by
    intro t
    by_cases ht : t ∈ Finset.Icc 1 (n + 1)
    · obtain ⟨g, hg⟩ := hSubdiff t ht (x t) (hxV t (by simp at ht ⊢; omega))
      exact ⟨g, fun _ => hg⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose g hg using hex
  have h1 := P1 g hg u hu
  rw [Finset.sum_sub_distrib] at h1
  have hsm : 0 < Real.sqrt mu := Real.sqrt_pos.mpr hmu
  -- third sum is nonpositive
  have h3 : ∑ t ∈ Finset.Icc 1 n, (1 / η (t - 1) - 1 / η t) * (ψ (x (t + 1)) - ψ z₀) ≤ 0 := by
    apply Finset.sum_nonpos
    intro t ht
    have ht' := Finset.mem_Icc.mp ht
    have hψ0 : 0 ≤ ψ (x (t + 1)) - ψ z₀ := by
      have := hz₀.2 _ (hxV (t + 1) (by simp; omega)); linarith
    have ha := hsched t (by simp; omega)
    have hb := hsched (t + 1) (by simp; omega)
    rw [Nat.add_sub_cancel] at hb
    have hle : 1 / η (t - 1) ≤ 1 / η t := by
      rw [ha, hb, one_div_div, one_div_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hL.le
      exact Real.sqrt_le_sqrt (by push_cast; linarith)
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hψ0
  -- second sum
  have h2 : ∑ t ∈ Finset.Icc 1 (n + 1), η (t - 1) / (2 * mu) * ‖g t‖ ^ 2 ≤
      α * (L * Real.sqrt ((n + 1 : ℕ) : ℝ) / Real.sqrt mu) := by
    calc ∑ t ∈ Finset.Icc 1 (n + 1), η (t - 1) / (2 * mu) * ‖g t‖ ^ 2
        ≤ ∑ t ∈ Finset.Icc 1 (n + 1), (α * L / (2 * Real.sqrt mu)) * (1 / Real.sqrt (t : ℝ)) := by
          apply Finset.sum_le_sum
          intro t ht
          have hgn := RRAux_ModernOnlineLearning_FTRL_corollary_7_6.opnorm_le V (ℓ t) L hL.le
            (hlip t ht) (x t) (hxV t (by simp at ht ⊢; omega)) (g t) (hg t ht)
          have hg2 : ‖g t‖ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hgn 2
          have hηt : 0 < η (t - 1) := hη _ (by simp at ht; omega)
          have hst : 0 < Real.sqrt (t : ℝ) :=
            Real.sqrt_pos.mpr (by have := (Finset.mem_Icc.mp ht).1; positivity)
          calc η (t - 1) / (2 * mu) * ‖g t‖ ^ 2 ≤ η (t - 1) / (2 * mu) * L ^ 2 :=
                mul_le_mul_of_nonneg_left hg2 (by positivity)
            _ = _ := by
                rw [hsched t ht]
                exact RRAux_ModernOnlineLearning_FTRL_corollary_7_6.scal α L mu (Real.sqrt mu)
                  (Real.sqrt (t : ℝ)) hsm hst hL (Real.sq_sqrt hmu.le)
      _ = (α * L / (2 * Real.sqrt mu)) * ∑ t ∈ Finset.Icc 1 (n + 1), 1 / Real.sqrt (t : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (α * L / (2 * Real.sqrt mu)) * (2 * Real.sqrt ((n + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left (RRAux_ModernOnlineLearning_FTRL_corollary_7_6.sqrt_sum _)
            (by positivity)
      _ = _ := by field_simp
  -- first term
  have hηn := hsched (n + 1) (by simp)
  rw [Nat.add_sub_cancel] at hηn
  have h0 : (ψ u - ψ z₀) / η n =
      (ψ u - ψ z₀) / α * (L * Real.sqrt ((n + 1 : ℕ) : ℝ) / Real.sqrt mu) := by
    rw [hηn]
    have : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    field_simp
  have : ((ψ u - ψ z₀) / α + α) * (L * Real.sqrt ((n + 1 : ℕ) : ℝ) / Real.sqrt mu) =
      (ψ u - ψ z₀) / α * (L * Real.sqrt ((n + 1 : ℕ) : ℝ) / Real.sqrt mu) +
      α * (L * Real.sqrt ((n + 1 : ℕ) : ℝ) / Real.sqrt mu) := by ring
  rw [this]
  linarith

#print axioms solution
