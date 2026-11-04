-- Prove2me | solution 1 for NesterovSSAAudit.SSA.expected_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T05:09:57.513406+00:00
-- url     : https://prove2.me/submissions/3abe230f-7e0e-4487-99bf-87b12b767780

import Mathlib
import Definitions.Def_NesterovSSAAudit_SSA_randomExecution

set_option autoImplicit false

namespace SSAExpAux1c4

open Finset MeasureTheory PrimalDualSubgrad.Stoch NesterovSSAAudit.SSA

section Det

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Quadratic growth of a strongly convex objective at its minimizer over `Q`. -/
lemma growth {Q : Set E} {d : E → ℝ} {σ : ℝ} (hsc : StrongConvexOn Q σ d) {β : ℝ} (hβ : 0 < β)
    (S : StrongDual ℝ E) {x1 : E} (hx1 : x1 ∈ Q)
    (hmin : ∀ x ∈ Q, S x1 + β * d x1 ≤ S x + β * d x) (y : E) (hy : y ∈ Q) :
    S x1 + β * d x1 + β * (σ / 2) * ‖y - x1‖ ^ 2 ≤ S y + β * d y := by
  set A := S y + β * d y - (S x1 + β * d x1) with hA
  set B := β * (σ / 2) * ‖y - x1‖ ^ 2 with hB
  have hA0 : 0 ≤ A := by have := hmin y hy; linarith
  have key : ∀ t : ℝ, 0 < t → t < 1 → (1 - t) * B ≤ A := by
    intro t ht0 ht1
    have hz := hsc.2 hy hx1 ht0.le (by linarith : (0:ℝ) ≤ 1 - t) (by ring)
    have hm := hmin (t • y + (1 - t) • x1) (hsc.1 hy hx1 ht0.le (by linarith) (by ring))
    have hS : S (t • y + (1 - t) • x1) = t * S y + (1 - t) * S x1 := by
      simp [map_add, map_smul, smul_eq_mul]
    rw [hS] at hm
    simp only [smul_eq_mul] at hz
    have h1 := mul_le_mul_of_nonneg_left hz hβ.le
    have h2 : t * ((1 - t) * B) ≤ t * A := by rw [hA, hB]; nlinarith
    exact le_of_mul_le_mul_left h2 ht0
  have hBA : B ≤ A := by
    by_contra hcon
    push_neg at hcon
    have hB0 : 0 < B := lt_of_le_of_lt hA0 hcon
    have := key ((B - A) / (2 * B)) (by apply div_pos <;> linarith)
      (by rw [div_lt_one (by linarith)]; linarith)
    have e : (1 - (B - A) / (2 * B)) * B = (A + B) / 2 := by field_simp; ring
    rw [e] at this; linarith
  linarith

lemma d_nonneg {Q : Set E} {d : E → ℝ} {σ : ℝ} {x0 : E} (hd : ProxFunction Q d σ x0) {x : E}
    (hx : x ∈ Q) : 0 ≤ d x := by
  have := hd.x0_isMin x hx; rw [hd.d_x0] at this; exact this

/-- The argmin condition in the `S + β d` form. -/
lemma argmin_of {Q : Set E} {d : E → ℝ} {π : ℝ → StrongDual ℝ E → E} (hπ : IsArgminMap Q d π)
    {β : ℝ} (hβ : 0 < β) (S : StrongDual ℝ E) :
    π β (-S) ∈ Q ∧ ∀ x ∈ Q, S (π β (-S)) + β * d (π β (-S)) ≤ S x + β * d x := by
  obtain ⟨h1, h2⟩ := hπ β hβ (-S)
  refine ⟨h1, fun x hx => ?_⟩
  have := h2 x hx
  simpa [ContinuousLinearMap.neg_apply] using this

/-- Lipschitz continuity of the argmin map. -/
lemma argmin_lip {Q : Set E} {d : E → ℝ} {σ : ℝ} {x0 : E} (hd : ProxFunction Q d σ x0)
    {π : ℝ → StrongDual ℝ E → E} (hπ : IsArgminMap Q d π) {β : ℝ} (hβ : 0 < β)
    (S1 S2 : StrongDual ℝ E) :
    ‖π β (-S1) - π β (-S2)‖ ≤ 1 / (β * σ) * ‖S1 - S2‖ := by
  obtain ⟨m1, h1⟩ := argmin_of hπ hβ S1
  obtain ⟨m2, h2⟩ := argmin_of hπ hβ S2
  set x1 := π β (-S1)
  set x2 := π β (-S2)
  have g1 := growth hd.strongConvexOn hβ S1 m1 h1 x2 m2
  have g2 := growth hd.strongConvexOn hβ S2 m2 h2 x1 m1
  have hσ := hd.sigma_pos
  have hc : 0 < β * σ := mul_pos hβ hσ
  set r := ‖x1 - x2‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr' : ‖x2 - x1‖ = r := norm_sub_rev _ _
  rw [hr'] at g1
  have hlin : (S1 - S2) (x2 - x1) ≤ ‖S1 - S2‖ * r := by
    have := (S1 - S2).le_opNorm (x2 - x1)
    rw [hr'] at this
    exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using this)
  have hexp : (S1 - S2) (x2 - x1) = S1 x2 - S1 x1 - S2 x2 + S2 x1 := by
    simp [map_sub]; ring
  rw [hexp] at hlin
  have hq : β * σ * r ^ 2 ≤ ‖S1 - S2‖ * r := by linarith
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc]
  rcases hr0.lt_or_eq with hpos | hzero
  · have := le_of_mul_le_mul_right (by nlinarith : r * (β * σ) * r ≤ ‖S1 - S2‖ * r) hpos
    linarith
  · rw [← hzero]; simp [norm_nonneg]

lemma argmin_continuous {Q : Set E} {d : E → ℝ} {σ : ℝ} {x0 : E} (hd : ProxFunction Q d σ x0)
    {π : ℝ → StrongDual ℝ E → E} (hπ : IsArgminMap Q d π) {β : ℝ} (hβ : 0 < β) :
    Continuous (fun S : StrongDual ℝ E => π β (-S)) := by
  refine (LipschitzWith.of_dist_le' (K := 1 / (β * σ)) fun S1 S2 => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  exact argmin_lip hd hπ hβ S1 S2

/-- Distance of an argmin point from the prox-center. -/
lemma argmin_dist {Q : Set E} {d : E → ℝ} {σ : ℝ} {x0 : E} (hd : ProxFunction Q d σ x0)
    {π : ℝ → StrongDual ℝ E → E} (hπ : IsArgminMap Q d π) {β : ℝ} (hβ : 0 < β)
    (S : StrongDual ℝ E) :
    ‖π β (-S) - x0‖ ≤ 2 / (β * σ) * ‖S‖ := by
  obtain ⟨m1, h1⟩ := argmin_of hπ hβ S
  set x1 := π β (-S)
  have g := growth hd.strongConvexOn hβ S m1 h1 x0 hd.x0_mem
  rw [hd.d_x0] at g
  have hdx := d_nonneg hd m1
  have hσ := hd.sigma_pos
  have hc : 0 < β * σ := mul_pos hβ hσ
  set r := ‖x1 - x0‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr' : ‖x0 - x1‖ = r := norm_sub_rev _ _
  rw [hr'] at g
  have hlin : S (x0 - x1) ≤ ‖S‖ * r := by
    have := S.le_opNorm (x0 - x1)
    rw [hr'] at this
    exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using this)
  rw [map_sub] at hlin
  have hq : β * σ * r ^ 2 ≤ 2 * (‖S‖ * r) := by nlinarith [mul_nonneg hβ.le hdx]
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  rcases hr0.lt_or_eq with hpos | hzero
  · have := le_of_mul_le_mul_right (by nlinarith : r * (β * σ) * r ≤ (2 * ‖S‖) * r) hpos
    linarith
  · rw [← hzero]; simp [norm_nonneg]

lemma betaHat_ge_one : ∀ n, 1 ≤ betaHat n
  | 0 => by simp [betaHat]
  | 1 => by simp [betaHat]
  | (n + 2) => by
    have := betaHat_ge_one (n + 1)
    simp only [betaHat]
    have : 0 ≤ 1 / betaHat (n + 1) := by positivity
    linarith

lemma betaHat_mono (n : ℕ) : betaHat n ≤ betaHat (n + 1) := by
  rcases n with _ | n
  · simp [betaHat]
  · have := betaHat_ge_one (n + 1)
    show betaHat (n + 1) ≤ betaHat (n + 1) + 1 / betaHat (n + 1)
    have : 0 ≤ 1 / betaHat (n + 1) := by positivity
    linarith

lemma betaHat_sum (k : ℕ) : ∑ i ∈ range (k + 1), 1 / betaHat i = betaHat (k + 1) := by
  induction k with
  | zero => simp [betaHat]
  | succ k ih =>
    rw [sum_range_succ, ih]
    show _ = betaHat (k + 1) + 1 / betaHat (k + 1)
    rfl

end Det

section Path

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {Ξ : Type*}

lemma s_succ (π : ℝ → StrongDual ℝ E → E) (γ : ℝ) (x0 : E) (a : E → Ξ → StrongDual ℝ E)
    (ω : ℕ → Ξ) (n : ℕ) :
    (historyState π γ x0 a (n + 1) (fun j => ω j.val)).2
      = (historyState π γ x0 a n (fun j => ω j.val)).2 + a (pathPoint π γ x0 a ω n) (ω n) :=
  rfl

lemma run_succ (π : ℝ → StrongDual ℝ E → E) (γ : ℝ) (x0 : E) (a : E → Ξ → StrongDual ℝ E)
    (ω : ℕ → Ξ) (n : ℕ) :
    pathPoint π γ x0 a ω (n + 1)
      = π (γ * betaHat (n + 1)) (-(historyState π γ x0 a (n + 1) (fun j => ω j.val)).2) := rfl

lemma s_sum (π : ℝ → StrongDual ℝ E → E) (γ : ℝ) (x0 : E) (a : E → Ξ → StrongDual ℝ E)
    (ω : ℕ → Ξ) : ∀ n, (historyState π γ x0 a n (fun j => ω j.val)).2
      = ∑ i ∈ range n, a (pathPoint π γ x0 a ω i) (ω i)
  | 0 => by simp [historyState]
  | n + 1 => by rw [sum_range_succ, ← s_sum π γ x0 a ω n]; rfl

lemma run_mem {Q : Set E} {d : E → ℝ} {σ : ℝ} {x0 : E} (hd : ProxFunction Q d σ x0)
    {π : ℝ → StrongDual ℝ E → E} (hπ : IsArgminMap Q d π) {γ : ℝ} (hγ : 0 < γ)
    (a : E → Ξ → StrongDual ℝ E) (ω : ℕ → Ξ) : ∀ n, pathPoint π γ x0 a ω n ∈ Q
  | 0 => hd.x0_mem
  | n + 1 => by
    rw [run_succ]
    exact (argmin_of hπ (mul_pos hγ (lt_of_lt_of_le one_pos (betaHat_ge_one _))) _).1

lemma run_min {Q : Set E} {d : E → ℝ} {σ : ℝ} {x0 : E} (hd : ProxFunction Q d σ x0)
    {π : ℝ → StrongDual ℝ E → E} (hπ : IsArgminMap Q d π) {γ : ℝ} (hγ : 0 < γ)
    (a : E → Ξ → StrongDual ℝ E) (ω : ℕ → Ξ) (n : ℕ) : ∀ x ∈ Q,
    (historyState π γ x0 a n (fun j => ω j.val)).2 (pathPoint π γ x0 a ω n)
        + γ * betaHat n * d (pathPoint π γ x0 a ω n)
      ≤ (historyState π γ x0 a n (fun j => ω j.val)).2 x + γ * betaHat n * d x := by
  intro x hx
  rcases n with _ | n
  · have h1 : pathPoint π γ x0 a ω 0 = x0 := rfl
    have h2 : (historyState π γ x0 a 0 (fun j => ω j.val)).2 = 0 := rfl
    rw [h1, h2, hd.d_x0]
    have := d_nonneg hd hx
    have := betaHat_ge_one 0
    simp only [ContinuousLinearMap.zero_apply, mul_zero, zero_add]
    positivity
  · rw [run_succ]
    exact (argmin_of hπ (mul_pos hγ (lt_of_lt_of_le one_pos (betaHat_ge_one _))) _).2 x hx

lemma potential {Q : Set E} {d : E → ℝ} {σ : ℝ} {x0 : E} (hd : ProxFunction Q d σ x0)
    {π : ℝ → StrongDual ℝ E → E} (hπ : IsArgminMap Q d π) {γ : ℝ} (hγ : 0 < γ)
    (a : E → Ξ → StrongDual ℝ E) (L : ℝ) (hL : ∀ x ∈ Q, ∀ ξ, ‖a x ξ‖ ≤ L) (ω : ℕ → Ξ) :
    ∀ n, ∑ i ∈ range n, (a (pathPoint π γ x0 a ω i) (ω i) (pathPoint π γ x0 a ω i)
        - L ^ 2 / (2 * σ * (γ * betaHat i)))
      ≤ (historyState π γ x0 a n (fun j => ω j.val)).2 (pathPoint π γ x0 a ω n)
          + γ * betaHat n * d (pathPoint π γ x0 a ω n)
  | 0 => by
    have h1 : pathPoint π γ x0 a ω 0 = x0 := rfl
    have h2 : (historyState π γ x0 a 0 (fun j => ω j.val)).2 = 0 := rfl
    simp [h1, h2, hd.d_x0]
  | n + 1 => by
    have ih := potential hd hπ hγ a L hL ω n
    rw [sum_range_succ]
    set xn := pathPoint π γ x0 a ω n
    set xn1 := pathPoint π γ x0 a ω (n + 1)
    set sn := (historyState π γ x0 a n (fun j => ω j.val)).2
    set g := a xn (ω n)
    have hs : (historyState π γ x0 a (n + 1) (fun j => ω j.val)).2 = sn + g := s_succ π γ x0 a ω n
    rw [hs, ContinuousLinearMap.add_apply]
    have hβn : 0 < γ * betaHat n := mul_pos hγ (lt_of_lt_of_le one_pos (betaHat_ge_one _))
    have hmn : xn ∈ Q := run_mem hd hπ hγ a ω n
    have hmn1 : xn1 ∈ Q := run_mem hd hπ hγ a ω (n + 1)
    have hgr := growth hd.strongConvexOn hβn sn hmn (run_min hd hπ hγ a ω n) xn1 hmn1
    have hdn1 := d_nonneg hd hmn1
    have hmono : γ * betaHat n * d xn1 ≤ γ * betaHat (n + 1) * d xn1 := by
      apply mul_le_mul_of_nonneg_right _ hdn1
      exact mul_le_mul_of_nonneg_left (betaHat_mono n) hγ.le
    set r := ‖xn1 - xn‖
    have hr0 : 0 ≤ r := norm_nonneg _
    have hgL : ‖g‖ ≤ L := hL xn hmn (ω n)
    have hg1 : g xn - L * r ≤ g xn1 := by
      have h := g.le_opNorm (xn1 - xn)
      have h' : |g (xn1 - xn)| ≤ L * r :=
        le_trans (by simpa [Real.norm_eq_abs] using h) (mul_le_mul_of_nonneg_right hgL hr0)
      rw [map_sub] at h'
      have := neg_abs_le (g xn1 - g xn)
      linarith
    have hσ := hd.sigma_pos
    set c := γ * betaHat n with hc
    have hcσ : 0 < c * σ := mul_pos hβn hσ
    have amgm : L * r - c * (σ / 2) * r ^ 2 ≤ L ^ 2 / (2 * σ * c) := by
      have h0 : 0 ≤ (c * σ * r - L) ^ 2 / (2 * (c * σ)) := by positivity
      have e : (c * σ * r - L) ^ 2 / (2 * (c * σ))
          = c * (σ / 2) * r ^ 2 - L * r + L ^ 2 / (2 * σ * c) := by
        field_simp; ring
      linarith
    linarith

lemma pathwise {Q : Set E} {d : E → ℝ} {σ : ℝ} {x0 : E} (hd : ProxFunction Q d σ x0)
    {π : ℝ → StrongDual ℝ E → E} (hπ : IsArgminMap Q d π) {γ : ℝ} (hγ : 0 < γ)
    (a : E → Ξ → StrongDual ℝ E) (L : ℝ) (hL : ∀ x ∈ Q, ∀ ξ, ‖a x ξ‖ ≤ L) (ω : ℕ → Ξ)
    (xstar : E) (hxstar : xstar ∈ Q) (k : ℕ) :
    ∑ i ∈ range (k + 1), a (pathPoint π γ x0 a ω i) (ω i) (pathPoint π γ x0 a ω i - xstar)
      ≤ betaHat (k + 1) * (γ * d xstar + L ^ 2 / (2 * σ * γ)) := by
  have hp := potential hd hπ hγ a L hL ω (k + 1)
  have hm := run_min hd hπ hγ a ω (k + 1) xstar hxstar
  have hsum := s_sum π γ x0 a ω (k + 1)
  have hsx : (historyState π γ x0 a (k + 1) (fun j => ω j.val)).2 xstar
      = ∑ i ∈ range (k + 1), a (pathPoint π γ x0 a ω i) (ω i) xstar := by
    rw [hsum, ContinuousLinearMap.sum_apply]
  rw [hsx] at hm
  rw [sum_sub_distrib] at hp
  have hL2 : ∑ i ∈ range (k + 1), L ^ 2 / (2 * σ * (γ * betaHat i))
      = L ^ 2 / (2 * σ * γ) * betaHat (k + 1) := by
    rw [← betaHat_sum k, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    have := betaHat_ge_one i
    have := hd.sigma_pos
    field_simp
  rw [hL2] at hp
  simp only [map_sub]
  rw [sum_sub_distrib]
  nlinarith

lemma lip_f {Q : Set E} (f : E → Ξ → ℝ) (a : E → Ξ → StrongDual ℝ E) (L : ℝ)
    (hf : RawOracle Q f a L) (x y : E) (hx : x ∈ Q) (hy : y ∈ Q) (ξ : Ξ) :
    |f x ξ - f y ξ| ≤ L * ‖x - y‖ := by
  have h1 : f x ξ - f y ξ ≤ a x ξ (x - y) := hf.subgrad x hx ξ y hy
  have h2 : f y ξ - f x ξ ≤ a y ξ (y - x) := hf.subgrad y hy ξ x hx
  have b1 : |a x ξ (x - y)| ≤ L * ‖x - y‖ := by
    have := (a x ξ).le_opNorm (x - y)
    exact le_trans (by simpa [Real.norm_eq_abs] using this)
      (mul_le_mul_of_nonneg_right (hf.bound x hx ξ) (norm_nonneg _))
  have b2 : |a y ξ (y - x)| ≤ L * ‖x - y‖ := by
    have := (a y ξ).le_opNorm (y - x)
    rw [norm_sub_rev] at this
    exact le_trans (by simpa [Real.norm_eq_abs] using this)
      (mul_le_mul_of_nonneg_right (hf.bound y hy ξ) (norm_nonneg _))
  rw [abs_le]
  constructor
  · have := le_abs_self (a y ξ (y - x)); linarith
  · have := le_abs_self (a x ξ (x - y)); linarith

end Path

section Meas

variable {Ξ : Type*} [MeasurableSpace Ξ]

lemma restr_mp (μ : Measure Ξ) [IsProbabilityMeasure μ] (n : ℕ) :
    ∀ m (hnm : n ≤ m), MeasurePreserving
      (fun h : Fin m → Ξ => fun j : Fin n => h (Fin.castLE hnm j))
      (historyLaw μ m) (historyLaw μ n) := by
  intro m hnm
  induction m, hnm using Nat.le_induction with
  | base =>
    convert MeasurePreserving.id (historyLaw μ n) using 1
    funext h j
    rfl
  | succ m hnm ih =>
    have hinit : MeasurePreserving (fun h : Fin (m + 1) → Ξ => fun j : Fin m => h j.castSucc)
        (historyLaw μ (m + 1)) (historyLaw μ m) := by
      haveI : IsProbabilityMeasure (historyLaw μ m) := by unfold historyLaw; infer_instance
      have h2 : MeasurePreserving
          (Prod.snd ∘ ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Ξ) (Fin.last m)))
          (historyLaw μ (m + 1)) (historyLaw μ m) :=
        (measurePreserving_snd (μ := μ) (ν := historyLaw μ m)).comp
          (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) (Fin.last m))
      have e : (fun h : Fin (m + 1) → Ξ => fun j : Fin m => h j.castSucc)
          = Prod.snd ∘ ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Ξ) (Fin.last m)) := by
        funext h j
        simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.removeNth, Fin.init]
      rw [e]
      exact h2
    convert ih.comp hinit using 1
    funext h j
    rfl

lemma fub_le (μ : Measure Ξ) [IsProbabilityMeasure μ] (k : ℕ) (i : Fin (k + 1))
    (G F : (Fin (k + 1) → Ξ) → ℝ)
    (hG : Integrable G (historyLaw μ (k + 1))) (hF : Integrable F (historyLaw μ (k + 1)))
    (hcond : ∀ h' : Fin k → Ξ, Integrable (fun ξ => F (Fin.insertNth i ξ h')) μ →
      ∫ ξ, G (Fin.insertNth i ξ h') ∂μ ≤ ∫ ξ, F (Fin.insertNth i ξ h') ∂μ) :
    ∫ h, G h ∂(historyLaw μ (k + 1)) ≤ ∫ h, F h ∂(historyLaw μ (k + 1)) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => Ξ) i with he
  have hmp : MeasurePreserving e (historyLaw μ (k + 1))
      (μ.prod (Measure.pi fun _ : Fin k => μ)) :=
    measurePreserving_piFinSuccAbove (fun _ => μ) i
  have hmps := hmp.symm
  have hsymm : ∀ ξ (h' : Fin k → Ξ), e.symm (ξ, h') = Fin.insertNth i ξ h' := fun ξ h' => by
    rw [he]
    first
    | rfl
    | simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  have hi1 : Integrable (G ∘ e.symm) (μ.prod (Measure.pi fun _ : Fin k => μ)) :=
    (hmps.integrable_comp_emb e.symm.measurableEmbedding).mpr hG
  have hi2 : Integrable (F ∘ e.symm) (μ.prod (Measure.pi fun _ : Fin k => μ)) :=
    (hmps.integrable_comp_emb e.symm.measurableEmbedding).mpr hF
  calc ∫ h, G h ∂(historyLaw μ (k + 1))
      = ∫ p, (G ∘ e.symm) p ∂(μ.prod (Measure.pi fun _ : Fin k => μ)) :=
        (hmps.integral_comp' G).symm
    _ = ∫ h', ∫ ξ, (G ∘ e.symm) (ξ, h') ∂μ ∂(Measure.pi fun _ : Fin k => μ) :=
        integral_prod_symm _ hi1
    _ ≤ ∫ h', ∫ ξ, (F ∘ e.symm) (ξ, h') ∂μ ∂(Measure.pi fun _ : Fin k => μ) := by
        refine integral_mono_ae hi1.integral_prod_right hi2.integral_prod_right ?_
        filter_upwards [hi2.prod_left_ae] with h' hh'
        simp only [Function.comp, hsymm] at hh' ⊢
        exact hcond h' hh'
    _ = ∫ p, (F ∘ e.symm) p ∂(μ.prod (Measure.pi fun _ : Fin k => μ)) :=
        (integral_prod_symm _ hi2).symm
    _ = ∫ h, F h ∂(historyLaw μ (k + 1)) := hmps.integral_comp' F

lemma pad_restr {k : ℕ} (n : ℕ) (hn : n ≤ k + 1) (h : Fin (k + 1) → Ξ) :
    (fun j : Fin n => padHistory h j.val) = fun j => h (Fin.castLE hn j) := by
  funext j
  have hj : j.val < k + 1 := lt_of_lt_of_le j.isLt hn
  simp only [padHistory, hj, dif_pos]
  rfl

end Meas

end SSAExpAux1c4

set_option maxHeartbeats 1000000 in
open Finset MeasureTheory PrimalDualSubgrad.Stoch NesterovSSAAudit.SSA in
theorem solution {E Ξ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace Ξ]
    (Q : Set E) (d : E → ℝ) (σ : ℝ) (x0 : E) (hd : ProxFunction Q d σ x0)
    (π : ℝ → StrongDual ℝ E → E) (hπ : IsArgminMap Q d π)
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (f : E → Ξ → ℝ) (a : E → Ξ → StrongDual ℝ E)
    (L : ℝ) (hf : RawOracle Q f a L)
    (hsections : ∀ x ∈ Q, Integrable (f x) μ)
    (γ : ℝ) (hγ : 0 < γ) (hrandom : IsRandomExecution μ π γ x0 a)
    (xstar : E) (hxstar : xstar ∈ Q)
    (hmin : ∀ x ∈ Q, population μ f xstar ≤ population μ f x)
    (k : ℕ) :
    Integrable (fun h : Fin (k + 1) → Ξ =>
      population μ f (pathAverage π γ x0 a (padHistory h) k)) (historyLaw μ (k + 1)) ∧
    (∫ h : Fin (k + 1) → Ξ, population μ f (pathAverage π γ x0 a (padHistory h) k)
        ∂(historyLaw μ (k + 1))) - population μ f xstar
      ≤ betaHat (k + 1) / ((k : ℝ) + 1) * (γ * d xstar + L ^ 2 / (2 * σ * γ)) := by
  classical
  letI mE : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI mD : MeasurableSpace (StrongDual ℝ E) := borel (StrongDual ℝ E)
  haveI : BorelSpace (StrongDual ℝ E) := ⟨rfl⟩
  have hr : ∀ n : ℕ,
      AEMeasurable (fun h => (historyState π γ x0 a n h).1) (historyLaw μ n) ∧
      AEMeasurable (fun h => (historyState π γ x0 a n h).2) (historyLaw μ n) := hrandom
  haveI hne : Nonempty Ξ := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h1 := measure_univ (μ := μ)
    rw [Set.univ_eq_empty_iff.mpr hne, measure_empty] at h1
    exact zero_ne_one h1
  obtain ⟨ξ0⟩ := hne
  set P := historyLaw μ (k + 1) with hPdef
  haveI hP : IsProbabilityMeasure P := by rw [hPdef]; unfold historyLaw; infer_instance
  let X : ℕ → (Fin (k + 1) → Ξ) → E := fun i h => pathPoint π γ x0 a (padHistory h) i
  let S : ℕ → (Fin (k + 1) → Ξ) → StrongDual ℝ E := fun i h =>
    (historyState π γ x0 a i (fun j => padHistory h j.val)).2
  let φ : E → ℝ := population μ f
  let ψ : E → ℝ := fun x => φ x - φ xstar
  let C : ℝ := betaHat (k + 1) * (γ * d xstar + L ^ 2 / (2 * σ * γ))
  let w : ℝ := 1 / ((k : ℝ) + 1)
  show Integrable (fun h => φ (w • ∑ i ∈ range (k + 1), X i h)) P ∧
    ∫ h, φ (w • ∑ i ∈ range (k + 1), X i h) ∂P - φ xstar
      ≤ betaHat (k + 1) / ((k : ℝ) + 1) * (γ * d xstar + L ^ 2 / (2 * σ * γ))
  have hL0 : 0 ≤ L := hf.nonneg
  -- measurability of the states
  have hXmeas : ∀ i ≤ k + 1, AEMeasurable (X i) P := by
    intro i hi
    have h1 := (hr i).1.comp_quasiMeasurePreserving
      (SSAExpAux1c4.restr_mp μ i (k + 1) hi).quasiMeasurePreserving
    refine h1.congr (Filter.Eventually.of_forall fun h => ?_)
    simp only [Function.comp, X, pathPoint]
    rw [SSAExpAux1c4.pad_restr i hi h]
  have hSmeas : ∀ i ≤ k + 1, AEMeasurable (S i) P := by
    intro i hi
    have h1 := (hr i).2.comp_quasiMeasurePreserving
      (SSAExpAux1c4.restr_mp μ i (k + 1) hi).quasiMeasurePreserving
    refine h1.congr (Filter.Eventually.of_forall fun h => ?_)
    simp only [Function.comp, S]
    rw [SSAExpAux1c4.pad_restr i hi h]
  have hXmem : ∀ i h, X i h ∈ Q := fun i h => SSAExpAux1c4.run_mem hd hπ hγ a (padHistory h) i
  -- Lipschitz bounds for the population objective
  have hφlip : ∀ x ∈ Q, ∀ y ∈ Q, |φ x - φ y| ≤ L * ‖x - y‖ := by
    intro x hx y hy
    have e : φ x - φ y = ∫ ξ, (f x ξ - f y ξ) ∂μ :=
      (integral_sub (hsections x hx) (hsections y hy)).symm
    rw [e]
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun ξ => f x ξ - f y ξ)
      (C := L * ‖x - y‖)
      (Filter.Eventually.of_forall fun ξ => by
        simpa [Real.norm_eq_abs] using SSAExpAux1c4.lip_f f a L hf x y hx hy ξ)
    simpa [Real.norm_eq_abs, probReal_univ] using this
  have hψlip : LipschitzOnWith (Real.toNNReal L) ψ Q := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [Real.dist_eq, Real.coe_toNNReal _ hL0, dist_eq_norm]
    have e : ψ x - ψ y = φ x - φ y := by simp only [ψ]; ring
    rw [e]
    exact hφlip x hx y hy
  obtain ⟨ψt, hψt, hEq⟩ := hψlip.extend_real
  have hcomp : ∀ Y : (Fin (k + 1) → Ξ) → E, AEMeasurable Y P → (∀ h, Y h ∈ Q) →
      AEMeasurable (fun h => ψ (Y h)) P := fun Y hY hQ =>
    (hψt.continuous.measurable.comp_aemeasurable hY).congr
      (Filter.Eventually.of_forall fun h => (hEq (hQ h)).symm)
  have hψbd : ∀ x ∈ Q, |ψ x| ≤ L * ‖x - xstar‖ := fun x hx => hφlip x hx xstar hxstar
  have hψnn : ∀ x ∈ Q, 0 ≤ ψ x := fun x hx => by
    have := hmin x hx
    simp only [ψ, φ]
    linarith
  -- deterministic bounds on the iterates
  have hXbd : ∀ i, ∃ R, ∀ h, ‖X i h - xstar‖ ≤ R := by
    intro i
    rcases i with _ | n
    · exact ⟨‖x0 - xstar‖, fun h => le_rfl⟩
    · refine ⟨2 / (γ * betaHat (n + 1) * σ) * (((n : ℝ) + 1) * L) + ‖x0 - xstar‖, fun h => ?_⟩
      have hβ : 0 < γ * betaHat (n + 1) :=
        mul_pos hγ (lt_of_lt_of_le one_pos (SSAExpAux1c4.betaHat_ge_one _))
      have h1 := SSAExpAux1c4.argmin_dist hd hπ hβ
        (historyState π γ x0 a (n + 1) (fun j => padHistory h j.val)).2
      have hs : ‖(historyState π γ x0 a (n + 1) (fun j => padHistory h j.val)).2‖
          ≤ ((n : ℝ) + 1) * L := by
        rw [SSAExpAux1c4.s_sum]
        refine le_trans (norm_sum_le _ _) ?_
        refine le_trans (sum_le_sum fun i _ =>
          hf.bound _ (SSAExpAux1c4.run_mem hd hπ hγ a _ i) _) ?_
        simp
      have hc : 0 ≤ 2 / (γ * betaHat (n + 1) * σ) := by have := hd.sigma_pos; positivity
      have h3 : ‖X (n + 1) h - x0‖ ≤ 2 / (γ * betaHat (n + 1) * σ) * (((n : ℝ) + 1) * L) :=
        le_trans h1 (mul_le_mul_of_nonneg_left hs hc)
      have h2 : X (n + 1) h - xstar = (X (n + 1) h - x0) + (x0 - xstar) := by abel
      rw [h2]
      refine le_trans (norm_add_le _ _) ?_
      linarith
  have hψX_int : ∀ i ≤ k + 1, Integrable (fun h => ψ (X i h)) P := by
    intro i hi
    obtain ⟨R, hR⟩ := hXbd i
    refine Integrable.of_bound (hcomp _ (hXmeas i hi) (hXmem i)).aestronglyMeasurable (L * R)
      (Filter.Eventually.of_forall fun h => ?_)
    rw [Real.norm_eq_abs]
    exact le_trans (hψbd _ (hXmem i h)) (mul_le_mul_of_nonneg_left (hR h) hL0)
  -- the linearised losses
  let F : ℕ → (Fin (k + 1) → Ξ) → ℝ := fun i h => a (X i h) (padHistory h i) (X i h - xstar)
  have hev : Continuous fun p : StrongDual ℝ E × E => p.1 p.2 :=
    continuous_fst.clm_apply continuous_snd
  have hF_int : ∀ i ≤ k, Integrable (F i) P := by
    intro i hi
    obtain ⟨R, hR⟩ := hXbd i
    have hm : AEMeasurable (fun h => S (i + 1) h (X i h - xstar) - S i h (X i h - xstar)) P :=
      (hev.aemeasurable2 (hSmeas (i + 1) (by omega)) ((hXmeas i (by omega)).sub_const xstar)).sub
        (hev.aemeasurable2 (hSmeas i (by omega)) ((hXmeas i (by omega)).sub_const xstar))
    have heq : (fun h => S (i + 1) h (X i h - xstar) - S i h (X i h - xstar)) = F i := by
      funext h
      simp only [S, F, X, SSAExpAux1c4.s_succ, ContinuousLinearMap.add_apply]
      ring
    rw [heq] at hm
    refine Integrable.of_bound hm.aestronglyMeasurable (L * R)
      (Filter.Eventually.of_forall fun h => ?_)
    rw [Real.norm_eq_abs]
    have hb := (a (X i h) (padHistory h i)).le_opNorm (X i h - xstar)
    rw [Real.norm_eq_abs] at hb
    refine le_trans hb ?_
    exact mul_le_mul (hf.bound _ (hXmem i h) _) (hR h) (norm_nonneg _) hL0
  -- one step of conditioning
  have hstep : ∀ i ∈ range (k + 1), ∫ h, ψ (X i h) ∂P ≤ ∫ h, F i h ∂P := by
    intro i hi
    have hik : i < k + 1 := mem_range.mp hi
    refine SSAExpAux1c4.fub_le μ k ⟨i, hik⟩ (fun h => ψ (X i h)) (F i)
      (hψX_int i (by omega)) (hF_int i (by omega)) ?_
    intro h' hint
    have hdiag : ∀ ξ, padHistory (Fin.insertNth (⟨i, hik⟩ : Fin (k + 1)) ξ h') i = ξ := by
      intro ξ
      simp [padHistory, hik]
    have hsame : ∀ ξ, X i (Fin.insertNth (⟨i, hik⟩ : Fin (k + 1)) ξ h')
        = X i (Fin.insertNth (⟨i, hik⟩ : Fin (k + 1)) ξ0 h') := by
      intro ξ
      simp only [X, pathPoint]
      congr 2
      funext j
      have hj : j.val < k + 1 := by omega
      simp only [padHistory, hj, dif_pos]
      have hne : (⟨j.val, hj⟩ : Fin (k + 1)) ≠ ⟨i, hik⟩ := by
        intro heq
        have := congrArg Fin.val heq
        simp at this
        omega
      obtain ⟨m', hm'⟩ := Fin.exists_succAbove_eq hne
      rw [← hm', Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
    set X0 := X i (Fin.insertNth (⟨i, hik⟩ : Fin (k + 1)) ξ0 h') with hX0
    have hX0Q : X0 ∈ Q := hXmem i _
    have hFpt : ∀ ξ, F i (Fin.insertNth (⟨i, hik⟩ : Fin (k + 1)) ξ h') = a X0 ξ (X0 - xstar) := by
      intro ξ
      simp only [F]
      rw [hsame ξ, hdiag ξ]
    have hGpt : ∀ ξ, ψ (X i (Fin.insertNth (⟨i, hik⟩ : Fin (k + 1)) ξ h')) = ψ X0 := by
      intro ξ
      rw [hsame ξ]
    simp only [hGpt, hFpt] at hint ⊢
    rw [integral_const, probReal_univ, one_smul]
    have e : ψ X0 = ∫ ξ, (f X0 ξ - f xstar ξ) ∂μ :=
      (integral_sub (hsections X0 hX0Q) (hsections xstar hxstar)).symm
    rw [e]
    refine integral_mono ((hsections X0 hX0Q).sub (hsections xstar hxstar)) hint fun ξ => ?_
    exact hf.subgrad X0 hX0Q ξ xstar hxstar
  -- convexity of the population objective
  have hconv : ConvexOn ℝ Q φ := by
    refine ⟨hd.convex, fun x hx y hy s t hs ht hst => ?_⟩
    have hmem : s • x + t • y ∈ Q := hd.convex hx hy hs ht hst
    simp only [φ, population, smul_eq_mul]
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hsections x hx).const_mul s) ((hsections y hy).const_mul t)]
    refine integral_mono (hsections _ hmem)
      (((hsections x hx).const_mul s).add ((hsections y hy).const_mul t)) fun ξ => ?_
    have := (hf.convex ξ).2 hx hy hs ht hst
    simpa [smul_eq_mul] using this
  have hw0 : 0 ≤ w := by positivity
  have hwsum : ∑ _i ∈ range (k + 1), w = 1 := by
    simp only [sum_const, card_range, nsmul_eq_mul, w]
    push_cast
    field_simp
  have hxbar_mem : ∀ h, w • ∑ i ∈ range (k + 1), X i h ∈ Q := by
    intro h
    rw [smul_sum]
    exact hd.convex.sum_mem (fun i _ => hw0) hwsum (fun i _ => hXmem i h)
  have hjensen : ∀ h, ψ (w • ∑ i ∈ range (k + 1), X i h) ≤ w * ∑ i ∈ range (k + 1), ψ (X i h) := by
    intro h
    have hJ := hconv.map_sum_le (t := range (k + 1)) (w := fun _ => w) (p := fun i => X i h)
      (fun i _ => hw0) hwsum (fun i _ => hXmem i h)
    simp only [smul_eq_mul] at hJ
    simp only [ψ]
    rw [smul_sum, mul_sum]
    have e1 : ∑ i ∈ range (k + 1), w * (φ (X i h) - φ xstar)
        = ∑ i ∈ range (k + 1), w * φ (X i h) - (∑ _i ∈ range (k + 1), w) * φ xstar := by
      rw [sum_mul, ← sum_sub_distrib]
      refine sum_congr rfl fun i _ => ?_
      ring
    rw [e1, hwsum]
    linarith
  have hxbar_meas : AEMeasurable (fun h => w • ∑ i ∈ range (k + 1), X i h) P :=
    (Finset.aemeasurable_fun_sum (range (k + 1)) fun i hi => hXmeas i (by have := mem_range.mp hi; omega)).const_smul _
  have hsumψ_int : Integrable (fun h => w * ∑ i ∈ range (k + 1), ψ (X i h)) P :=
    (integrable_finset_sum _ fun i hi => hψX_int i (by have := mem_range.mp hi; omega)).const_mul w
  have hψxbar_int : Integrable (fun h => ψ (w • ∑ i ∈ range (k + 1), X i h)) P := by
    refine Integrable.mono' hsumψ_int (hcomp _ hxbar_meas hxbar_mem).aestronglyMeasurable
      (Filter.Eventually.of_forall fun h => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hψnn _ (hxbar_mem h))]
    exact hjensen h
  have hpt : ∀ h, φ (w • ∑ i ∈ range (k + 1), X i h)
      = ψ (w • ∑ i ∈ range (k + 1), X i h) + φ xstar := fun h => by simp only [ψ]; ring
  have hφxbar_int : Integrable (fun h => φ (w • ∑ i ∈ range (k + 1), X i h)) P := by
    have := hψxbar_int.add (integrable_const (φ xstar))
    exact this.congr (Filter.Eventually.of_forall fun h => (hpt h).symm)
  refine ⟨hφxbar_int, ?_⟩
  have step1 : ∫ h, φ (w • ∑ i ∈ range (k + 1), X i h) ∂P
      = ∫ h, ψ (w • ∑ i ∈ range (k + 1), X i h) ∂P + φ xstar := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_add hψxbar_int (integrable_const _), integral_const, probReal_univ, one_smul]
  have step2 : ∫ h, ψ (w • ∑ i ∈ range (k + 1), X i h) ∂P
      ≤ w * ∑ i ∈ range (k + 1), ∫ h, ψ (X i h) ∂P := by
    rw [← integral_finset_sum _ (fun i hi => hψX_int i (by have := mem_range.mp hi; omega)),
      ← integral_const_mul]
    exact integral_mono hψxbar_int hsumψ_int hjensen
  have step3 : ∑ i ∈ range (k + 1), ∫ h, ψ (X i h) ∂P ≤ C := by
    refine le_trans (sum_le_sum hstep) ?_
    rw [← integral_finset_sum _ (fun i hi => hF_int i (by have := mem_range.mp hi; omega))]
    have := integral_mono
      (integrable_finset_sum _ fun i hi => hF_int i (by have := mem_range.mp hi; omega))
      (integrable_const C)
      (fun h => SSAExpAux1c4.pathwise hd hπ hγ a L hf.bound (padHistory h) xstar hxstar k)
    rwa [integral_const, probReal_univ, one_smul] at this
  have hC : betaHat (k + 1) / ((k : ℝ) + 1) * (γ * d xstar + L ^ 2 / (2 * σ * γ)) = w * C := by
    simp only [C, w]; ring
  rw [step1, hC]
  have := mul_le_mul_of_nonneg_left step3 hw0
  linarith
