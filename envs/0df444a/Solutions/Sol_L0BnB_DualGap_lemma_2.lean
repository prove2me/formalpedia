-- Prove2me | solution 1 for L0BnB.DualGap.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T03:50:22.247645+00:00
-- url     : https://prove2.me/submissions/76aebf13-ffb4-4c47-b303-d6cfd453d199

import Mathlib
import Definitions.Def_L0BnB_DualGap_Setup
import Definitions.Def_L0BnB_DualGap_Duals
import Theorems.Thm_L0BnB_DualGap_alphaStar_norm_le_one

set_option autoImplicit false

namespace L0BnB.DualGap.Aux

open L0BnB.DualGap

/-- Cauchy–Schwarz against a unit column. -/
lemma abs_colInner_le {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (i : Fin p)
    (hXi : ∑ r, X r i ^ 2 = 1) (a : Fin n → ℝ) :
    |colInner X a i| ≤ Real.sqrt (∑ r, a r ^ 2) := by
  unfold colInner
  apply Real.abs_le_sqrt
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a (fun r => X r i)
  simpa [hXi] using this

/-- The limit lemma: a nonnegative expression `h (K - a) + q h²` for all small `h > 0`
forces `a ≤ K`. -/
lemma le_of_small {a K q δ : ℝ} (hq : 0 ≤ q) (hδ : 0 < δ)
    (h : ∀ t, 0 < t → t ≤ δ → 0 ≤ t * (K - a) + q * t ^ 2) : a ≤ K := by
  by_contra hcon
  push Not at hcon
  set t := min δ ((a - K) / (2 * (q + 1))) with ht
  have hpos : 0 < (a - K) / (2 * (q + 1)) := by
    apply div_pos <;> linarith
  have ht0 : 0 < t := lt_min hδ hpos
  have ht1 : t ≤ δ := min_le_left _ _
  have ht2 : t ≤ (a - K) / (2 * (q + 1)) := min_le_right _ _
  have := h t ht0 ht1
  have h3 : t * (2 * (q + 1)) ≤ a - K := by
    rwa [le_div_iff₀ (by linarith)] at ht2
  nlinarith

/-- The residual/colInner identity: `colInner (alphaHat) = - colInner (resid)`. -/
lemma colInner_neg {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (a : Fin n → ℝ) (i : Fin p) :
    colInner X (fun r => - a r) i = - colInner X a i := by
  unfold colInner
  simp [Finset.sum_neg_distrib]

lemma mulVec_update {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (β : Fin p → ℝ) (i : Fin p) (t : ℝ)
    (r : Fin n) :
    Matrix.mulVec X (Function.update β i t) r = Matrix.mulVec X β r + (t - β i) * X r i := by
  have : Function.update β i t = β + Pi.single i (t - β i) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  rw [this, Matrix.mulVec_add]
  simp [Matrix.mulVec_single, mul_comm]

lemma sum_update_comp {p : ℕ} (β : Fin p → ℝ) (i : Fin p) (t : ℝ) (f : ℝ → ℝ) :
    ∑ j, f (Function.update β i t j) = ∑ j, f (β j) + (f t - f (β i)) := by
  have : ∀ j, f (Function.update β i t j) = f (β j) + (if j = i then f t - f (β i) else 0) := by
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  simp_rw [this, Finset.sum_add_distrib]
  simp

/-- The coordinate objective along coordinate `i`. -/
lemma F_update {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (β : Fin p → ℝ) (i : Fin p) (t : ℝ) :
    L0BnB.Reduced.F X y lam0 lam2 M (Function.update β i t) =
      L0BnB.Reduced.F X y lam0 lam2 M β - (t - β i) * colInner X (resid X y β) i
        + (1 / 2) * (∑ r, X r i ^ 2) * (t - β i) ^ 2
        + (L0BnB.Reduced.psi lam0 lam2 M t - L0BnB.Reduced.psi lam0 lam2 M (β i)) := by
  unfold L0BnB.Reduced.F L0BnB.Reduced.lsLoss colInner resid
  rw [sum_update_comp β i t (L0BnB.Reduced.psi lam0 lam2 M)]
  simp_rw [mulVec_update]
  have : ∀ r, (y r - (Matrix.mulVec X β r + (t - β i) * X r i)) ^ 2 =
      (y r - Matrix.mulVec X β r) ^ 2 - 2 * (t - β i) * ((y r - Matrix.mulVec X β r) * X r i)
        + (t - β i) ^ 2 * X r i ^ 2 := by intro r; ring
  simp_rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

lemma reverseHuber_zero : L0BnB.Reduced.reverseHuber 0 = 0 := by
  simp [L0BnB.Reduced.reverseHuber]

lemma psi_zero (lam0 lam2 M : ℝ) : L0BnB.Reduced.psi lam0 lam2 M 0 = 0 := by
  unfold L0BnB.Reduced.psi L0BnB.Reduced.psi1 L0BnB.Reduced.psi2
  split_ifs <;> simp [reverseHuber_zero]

lemma reverseHuber_ge_abs (u : ℝ) : |u| ≤ L0BnB.Reduced.reverseHuber u := by
  unfold L0BnB.Reduced.reverseHuber
  split_ifs with h
  · exact le_rfl
  · nlinarith [sq_abs u, sq_nonneg (|u| - 1)]

lemma sqrt_aux {lam0 lam2 : ℝ} (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) :
    lam0 * Real.sqrt (lam2 / lam0) = Real.sqrt (lam0 * lam2) := by
  rw [show lam0 * lam2 = lam0 ^ 2 * (lam2 / lam0) by field_simp]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hlam0.le]

/-- `ψ(t) ≥ c(λ₀,λ₂,M) |t|` everywhere. -/
lemma psi_ge {lam0 lam2 M : ℝ} (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (t : ℝ) :
    cThr lam0 lam2 M * |t| ≤ L0BnB.Reduced.psi lam0 lam2 M t := by
  unfold cThr L0BnB.Reduced.psi L0BnB.Reduced.psi1 L0BnB.Reduced.psi2
  split_ifs with h
  · have := reverseHuber_ge_abs (t * Real.sqrt (lam2 / lam0))
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at this
    have h2 : 2 * Real.sqrt (lam0 * lam2) * |t| = 2 * lam0 * (|t| * Real.sqrt (lam2 / lam0)) := by
      rw [← sqrt_aux hlam0 hlam2]; ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left this (by linarith)
  · exact le_rfl

/-- `ψ(t) = c(λ₀,λ₂,M) |t|` for small `t`. -/
lemma psi_eq_small {lam0 lam2 M : ℝ} (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (t : ℝ)
    (ht : |t| ≤ Real.sqrt (lam0 / lam2)) :
    L0BnB.Reduced.psi lam0 lam2 M t = cThr lam0 lam2 M * |t| := by
  unfold cThr L0BnB.Reduced.psi L0BnB.Reduced.psi1 L0BnB.Reduced.psi2
  split_ifs with h
  · unfold L0BnB.Reduced.reverseHuber
    have hs : 0 < Real.sqrt (lam2 / lam0) := Real.sqrt_pos.2 (div_pos hlam2 hlam0)
    have hprod : Real.sqrt (lam0 / lam2) * Real.sqrt (lam2 / lam0) = 1 := by
      rw [← Real.sqrt_mul (div_pos hlam0 hlam2).le]
      rw [show lam0 / lam2 * (lam2 / lam0) = 1 by field_simp]
      simp
    have hle : |t * Real.sqrt (lam2 / lam0)| ≤ 1 := by
      rw [abs_mul, abs_of_pos hs]
      calc |t| * Real.sqrt (lam2 / lam0) ≤ Real.sqrt (lam0 / lam2) * Real.sqrt (lam2 / lam0) :=
            mul_le_mul_of_nonneg_right ht hs.le
        _ = 1 := hprod
    rw [if_pos hle, abs_mul, abs_of_pos hs, ← sqrt_aux hlam0 hlam2]
    ring
  · rfl

/-- Proposition 3 core: for `β i = 0`, `0` minimizes the coordinate problem iff
`|⟨r, Xᵢ⟩| ≤ c`. -/
lemma isMinOn_iff {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hX : ∀ i, ∑ r, X r i ^ 2 = 1) (β : Fin p → ℝ) (i : Fin p) (hi : β i = 0) :
    IsMinOn (coordObj X y lam0 lam2 M β i) (Set.Icc (-M) M) 0 ↔
      |colInner X (resid X y β) i| ≤ cThr lam0 lam2 M := by
  set c := colInner X (resid X y β) i
  have key : ∀ t, coordObj X y lam0 lam2 M β i t - coordObj X y lam0 lam2 M β i 0 =
      - t * c + (1 / 2) * t ^ 2 + L0BnB.Reduced.psi lam0 lam2 M t := by
    intro t
    unfold coordObj
    rw [F_update, F_update, hi, hX i, psi_zero]
    ring
  constructor
  · intro hmin
    have hmin' : ∀ t ∈ Set.Icc (-M) M, 0 ≤ - t * c + (1 / 2) * t ^ 2 + L0BnB.Reduced.psi lam0 lam2 M t := by
      intro t ht
      have := hmin ht
      simp only [Set.mem_ofPred_eq] at this
      have := key t
      linarith
    have hδ : 0 < min M (Real.sqrt (lam0 / lam2)) :=
      lt_min hM (Real.sqrt_pos.2 (div_pos hlam0 hlam2))
    apply le_of_small (q := 1 / 2) (by norm_num) hδ
    intro t ht0 htδ
    have htM : t ≤ M := htδ.trans (min_le_left _ _)
    have hts : |t| ≤ Real.sqrt (lam0 / lam2) := by
      rw [abs_of_pos ht0]; exact htδ.trans (min_le_right _ _)
    rcases le_or_gt 0 c with hc | hc
    · have := hmin' t ⟨by linarith, htM⟩
      rw [psi_eq_small hlam0 hlam2 t hts, abs_of_pos ht0] at this
      rw [abs_of_nonneg hc]
      nlinarith
    · have hts' : |-t| ≤ Real.sqrt (lam0 / lam2) := by rwa [abs_neg]
      have := hmin' (-t) ⟨by linarith, by linarith⟩
      rw [psi_eq_small hlam0 hlam2 (-t) hts', abs_neg, abs_of_pos ht0] at this
      rw [abs_of_neg hc]
      nlinarith
  · intro hc t _
    simp only [Set.mem_ofPred_eq]
    have h1 := key t
    have h2 := psi_ge (M := M) hlam0 hlam2 t
    have h3 : t * c ≤ |t| * |c| := by rw [← abs_mul]; exact le_abs_self _
    have h4 : |t| * |c| ≤ |t| * cThr lam0 lam2 M := mul_le_mul_of_nonneg_left hc (abs_nonneg t)
    nlinarith [sq_nonneg t]

theorem prop3 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hX : ∀ i, ∑ r, X r i ^ 2 = 1) (βhat : Fin p → ℝ) :
    Vset X y lam0 lam2 M βhat =
      Finset.univ.filter
        (fun i => βhat i = 0 ∧ cThr lam0 lam2 M < |colInner X (resid X y βhat) i|) := by
  unfold Vset
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hi, hn⟩
    exact ⟨hi, by rw [isMinOn_iff X y lam0 lam2 M hlam0 hlam2 hM hX βhat i hi] at hn; push Not at hn; exact hn⟩
  · rintro ⟨hi, hn⟩
    refine ⟨hi, ?_⟩
    rw [isMinOn_iff X y lam0 lam2 M hlam0 hlam2 hM hX βhat i hi]
    exact not_le.2 hn

lemma sum_update_dep {p : ℕ} (β : Fin p → ℝ) (i : Fin p) (t : ℝ) (f : Fin p → ℝ → ℝ) :
    ∑ j, f j (Function.update β i t j) = ∑ j, f j (β j) + (f i t - f i (β i)) := by
  have : ∀ j, f j (Function.update β i t j) = f j (β j) + (if j = i then f i t - f i (β i) else 0) := by
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  simp_rw [this, Finset.sum_add_distrib]
  simp

lemma colInner_sub {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (a b : Fin n → ℝ) (i : Fin p) :
    colInner X (fun r => a r - b r) i = colInner X a i - colInner X b i := by
  unfold colInner
  simp [sub_mul, Finset.sum_sub_distrib]

lemma hat_eq {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (βs βhat : Fin p → ℝ) :
    alphaHat X y βhat = fun r => L0BnB.Duality.alphaStar X y βs r - Matrix.mulVec X (βs - βhat) r := by
  funext r
  simp [alphaHat, L0BnB.Duality.alphaStar, L0BnB.Duality.rStar, resid, Matrix.mulVec_sub]

/-- Algebraic core of (53). -/
lemma gen53 {n : ℕ} (a d y : Fin n → ℝ) (ha : Real.sqrt (∑ r, a r ^ 2) ≤ 1)
    (hy : ∑ r, y r ^ 2 = 1) :
    (1 / 2) * ∑ r, (a r - d r) ^ 2 + ∑ r, (a r - d r) * y r ≤
      (1 / 2) * Real.sqrt (∑ r, d r ^ 2) ^ 2 + 2 * Real.sqrt (∑ r, d r ^ 2)
        + (1 / 2) * ∑ r, a r ^ 2 + ∑ r, a r * y r := by
  have hd : Real.sqrt (∑ r, d r ^ 2) ^ 2 = ∑ r, d r ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun r _ => sq_nonneg _))
  have h1 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun r => - a r) d
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun r => - y r) d
  simp only [neg_sq] at h1 h2
  rw [hy, Real.sqrt_one] at h2
  have hε : 0 ≤ Real.sqrt (∑ r, d r ^ 2) := Real.sqrt_nonneg _
  have h1' : ∑ r, -a r * d r ≤ Real.sqrt (∑ r, d r ^ 2) := by
    calc _ ≤ _ := h1
      _ ≤ 1 * Real.sqrt (∑ r, d r ^ 2) := mul_le_mul_of_nonneg_right ha hε
      _ = _ := one_mul _
  have e1 : ∑ r, (a r - d r) ^ 2 = ∑ r, a r ^ 2 + 2 * ∑ r, -a r * d r + ∑ r, d r ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun r _ => by ring)
  have e2 : ∑ r, (a r - d r) * y r = ∑ r, a r * y r + ∑ r, -y r * d r := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun r _ => by ring)
  rw [e1, e2, hd]
  linarith

theorem ineq53 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hy : ∑ r, y r ^ 2 = 1) (βs : Fin p → ℝ) (hβs : IsOptimal X y lam0 lam2 M βs)
    (βhat : Fin p → ℝ) :
    (1 / 2) * ∑ r, alphaHat X y βhat r ^ 2 + ∑ r, alphaHat X y βhat r * y r ≤
      (1 / 2) * primalGap X βs βhat ^ 2 + 2 * primalGap X βs βhat
        + (1 / 2) * ∑ r, L0BnB.Duality.alphaStar X y βs r ^ 2 + ∑ r, L0BnB.Duality.alphaStar X y βs r * y r := by
  have ha := alphaStar_norm_le_one X y lam0 lam2 M hlam0 hlam2 hM hy βs hβs
  rw [hat_eq X y βs βhat]
  exact gen53 _ _ y ha hy

theorem ineq56 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hy : ∑ r, y r ^ 2 = 1) (βs : Fin p → ℝ) (hβs : IsOptimal X y lam0 lam2 M βs)
    (βhat μhat : Fin p → ℝ) :
    -(1 / 2) * ∑ r, L0BnB.Duality.rhoStar X y βs r ^ 2 - ∑ r, L0BnB.Duality.rhoStar X y βs r * y r
        - 2 * primalGap X βs βhat - (1 / 2) * primalGap X βs βhat ^ 2 - M * ∑ i, |μhat i|
      ≤ L0BnB.Duality.h2 y M (rhoHat X y βhat) μhat := by
  have := ineq53 X y lam0 lam2 M hlam0 hlam2 hM hy βs hβs βhat
  unfold L0BnB.Duality.h2
  have e1 : rhoHat X y βhat = alphaHat X y βhat := rfl
  have e2 : L0BnB.Duality.rhoStar X y βs = L0BnB.Duality.alphaStar X y βs := rfl
  rw [e1, e2]
  linarith

/-- Feasibility of `[|ρᵀXᵢ| − κ]₊` and minimality of `μ̂`: closed form (28). -/
theorem eq28 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (βhat μhat : Fin p → ℝ) (hμ : IsMuHat X y lam0 lam2 M βhat μhat) :
    ∀ i, μhat i = max (|colInner X (rhoHat X y βhat) i| - lam0 / M - lam2 * M) 0 := by
  obtain ⟨hfeas, hmax⟩ := hμ
  set m : Fin p → ℝ := fun i => max (|colInner X (rhoHat X y βhat) i| - lam0 / M - lam2 * M) 0
  have hmfeas : L0BnB.Duality.Feas22 X lam0 lam2 M (rhoHat X y βhat) m := by
    intro i
    have : |L0BnB.Duality.colDot X (rhoHat X y βhat) i| - lam0 / M - lam2 * M ≤ m i := le_max_left _ _
    linarith
  have hle := hmax m hmfeas
  unfold L0BnB.Duality.h2 at hle
  have hsum : ∑ i, |μhat i| ≤ ∑ i, |m i| := by
    have := mul_le_mul_of_nonneg_left (le_refl M) hM.le
    nlinarith
  have hpt : ∀ i, |m i| ≤ |μhat i| := by
    intro i
    have hf := hfeas i
    rw [abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · have : L0BnB.Duality.colDot X (rhoHat X y βhat) i = colInner X (rhoHat X y βhat) i := rfl
      rw [this] at hf
      linarith [le_abs_self (μhat i)]
    · exact abs_nonneg _
  have heq : ∀ i, |m i| = |μhat i| := by
    have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun i _ => hpt i)).1
      (le_antisymm (Finset.sum_le_sum (fun i _ => hpt i)) hsum)
    exact fun i => this i (Finset.mem_univ i)
  intro i
  have hi := heq i
  have hf := hfeas i
  have : L0BnB.Duality.colDot X (rhoHat X y βhat) i = colInner X (rhoHat X y βhat) i := rfl
  rw [this] at hf
  show μhat i = m i
  rw [abs_of_nonneg (le_max_right _ _)] at hi
  rcases le_or_gt (|colInner X (rhoHat X y βhat) i| - lam0 / M - lam2 * M) 0 with h | h
  · have hm0 : m i = 0 := max_eq_right h
    rw [hm0] at hi ⊢
    exact abs_eq_zero.1 hi.symm
  · have hm : m i = |colInner X (rhoHat X y βhat) i| - lam0 / M - lam2 * M := max_eq_left h.le
    have hpos : 0 ≤ μhat i := by linarith
    rw [abs_of_nonneg hpos] at hi
    exact hi.symm

lemma psi_case2 {lam0 lam2 M : ℝ} (hreg : M < Real.sqrt (lam0 / lam2)) (t : ℝ) :
    L0BnB.Reduced.psi lam0 lam2 M t = (lam0 / M + lam2 * M) * |t| := by
  unfold L0BnB.Reduced.psi L0BnB.Reduced.psi2
  rw [if_neg (not_le.2 hreg)]

theorem eq58 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hreg : M < Real.sqrt (lam0 / lam2))
    (βs : Fin p → ℝ) (hβs : IsOptimal X y lam0 lam2 M βs) :
    ∀ i, (|βs i| < M → |colInner X (L0BnB.Duality.rhoStar X y βs) i| ≤ lam0 / M + lam2 * M) ∧
      (|βs i| = M → lam0 / M + lam2 * M ≤ |colInner X (L0BnB.Duality.rhoStar X y βs) i|) := by
  intro i
  obtain ⟨hbox, hopt⟩ := hβs
  set κ := lam0 / M + lam2 * M
  set c := colInner X (resid X y βs) i
  set q := ∑ r, X r i ^ 2
  set b := βs i
  have hq : 0 ≤ q := Finset.sum_nonneg (fun r _ => sq_nonneg _)
  have hρ : colInner X (L0BnB.Duality.rhoStar X y βs) i = - c := colInner_neg X _ i
  rw [hρ, abs_neg]
  have key : ∀ t, |t| ≤ M → 0 ≤ -(t - b) * c + (1 / 2) * q * (t - b) ^ 2 + κ * (|t| - |b|) := by
    intro t ht
    have hmem : Function.update βs i t ∈ L0BnB.Reduced.box p M := by
      intro j
      by_cases hj : j = i
      · subst hj; simpa using ht
      · simp [hj]; exact hbox j
    have := hopt _ hmem
    rw [F_update, psi_case2 hreg, psi_case2 hreg] at this
    nlinarith
  have hbM : |b| ≤ M := hbox i
  constructor
  · intro hlt
    have hδ : 0 < M - |b| := by linarith
    rcases le_or_gt 0 c with hc | hc
    · rw [abs_of_nonneg hc]
      apply le_of_small (q := (1 / 2) * q) (by positivity) hδ
      intro h h0 hδ'
      have ht : |b + h| ≤ M := (abs_add_le _ _).trans (by rw [abs_of_pos h0]; linarith)
      have := key (b + h) ht
      have hab : |b + h| - |b| ≤ h := by
        have := abs_add_le b h; rw [abs_of_pos h0] at this; linarith
      have hκ : 0 ≤ κ := by positivity
      have : κ * (|b + h| - |b|) ≤ κ * h := mul_le_mul_of_nonneg_left hab hκ
      have e : b + h - b = h := by ring
      rw [e] at *
      nlinarith
    · rw [abs_of_neg hc]
      apply le_of_small (q := (1 / 2) * q) (by positivity) hδ
      intro h h0 hδ'
      have ht : |b - h| ≤ M := (abs_sub _ _).trans (by rw [abs_of_pos h0]; linarith)
      have := key (b - h) ht
      have hab : |b - h| - |b| ≤ h := by
        have := abs_sub b h; rw [abs_of_pos h0] at this; linarith
      have hκ : 0 ≤ κ := by positivity
      have : κ * (|b - h| - |b|) ≤ κ * h := mul_le_mul_of_nonneg_left hab hκ
      have e : b - h - b = -h := by ring
      rw [e] at *
      nlinarith
  · intro heq
    rcases abs_eq hM.le |>.1 heq with hb | hb
    · -- b = M; move inward
      have : κ ≤ c := by
        apply le_of_small (q := (1 / 2) * q) (by positivity) hM
        intro h h0 hδ'
        have ht : |b - h| ≤ M := by rw [hb, abs_of_nonneg (by linarith)]; linarith
        have := key (b - h) ht
        rw [hb, abs_of_nonneg (by linarith : 0 ≤ M - h), abs_of_pos hM] at this
        nlinarith
      exact this.trans (le_abs_self c)
    · have : κ ≤ -c := by
        apply le_of_small (q := (1 / 2) * q) (by positivity) hM
        intro h h0 hδ'
        have ht : |b + h| ≤ M := by rw [hb, abs_of_nonpos (by linarith)]; linarith
        have := key (b + h) ht
        rw [hb, abs_of_nonpos (by linarith : -M + h ≤ 0), abs_neg, abs_of_pos hM] at this
        nlinarith
      exact this.trans (neg_le_abs c)

lemma colInner_hat_sub {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (βs βhat : Fin p → ℝ) (i : Fin p) :
    colInner X (alphaHat X y βhat) i =
      colInner X (L0BnB.Duality.alphaStar X y βs) i - colInner X (Matrix.mulVec X (βs - βhat)) i := by
  rw [hat_eq X y βs βhat, colInner_sub]

lemma abs_gap_le {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (hX : ∀ i, ∑ r, X r i ^ 2 = 1)
    (βs βhat : Fin p → ℝ) (i : Fin p) :
    |colInner X (Matrix.mulVec X (βs - βhat)) i| ≤ primalGap X βs βhat :=
  abs_colInner_le X i (hX i) _

theorem ineq57 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hreg : M < Real.sqrt (lam0 / lam2)) (hX : ∀ i, ∑ r, X r i ^ 2 = 1)
    (βs : Fin p → ℝ) (hβs : IsOptimal X y lam0 lam2 M βs)
    (βhat μhat : Fin p → ℝ) (hμ : IsMuHat X y lam0 lam2 M βhat μhat)
    (i : Fin p) (hi : βhat i ≠ 0) :
    |μhat i| ≤ primalGap X βs βhat + |L0BnB.Duality.muStar X y lam0 lam2 M βs i| := by
  rw [eq28 X y lam0 lam2 M hlam0 hlam2 hM βhat μhat hμ i, abs_of_nonneg (le_max_right _ _)]
  have h58 := eq58 X y lam0 lam2 M hlam0 hlam2 hM hreg βs hβs i
  have hsub := colInner_hat_sub X y βs βhat i
  have he := abs_gap_le X hX βs βhat i
  have e1 : colInner X (rhoHat X y βhat) i = colInner X (alphaHat X y βhat) i := rfl
  have e2 : colInner X (L0BnB.Duality.rhoStar X y βs) i =
      colInner X (L0BnB.Duality.alphaStar X y βs) i := rfl
  rw [e1]
  rw [e2] at h58
  set a := colInner X (L0BnB.Duality.alphaStar X y βs) i
  set e := colInner X (Matrix.mulVec X (βs - βhat)) i
  set ε := primalGap X βs βhat
  have hε : 0 ≤ ε := Real.sqrt_nonneg _
  have habs : |colInner X (alphaHat X y βhat) i| ≤ |a| + ε := by
    rw [hsub]
    calc |a - e| ≤ |a| + |e| := abs_sub _ _
      _ ≤ |a| + ε := by linarith
  have hbox := hβs.1 i
  apply max_le _ (by positivity)
  by_cases hbM : |βs i| = M
  · have hmu : L0BnB.Duality.muStar X y lam0 lam2 M βs i =
        |L0BnB.Duality.colDot X (L0BnB.Duality.rhoStar X y βs) i| - lam0 / M - lam2 * M := by
      unfold L0BnB.Duality.muStar; rw [if_pos hbM]
    rw [hmu]
    have : L0BnB.Duality.colDot X (L0BnB.Duality.rhoStar X y βs) i = a := rfl
    rw [this]
    linarith [le_abs_self (|a| - lam0 / M - lam2 * M)]
  · have hlt : |βs i| < M := lt_of_le_of_ne hbox hbM
    have := (h58.1 hlt)
    linarith [abs_nonneg (L0BnB.Duality.muStar X y lam0 lam2 M βs i)]

lemma v_nonneg {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (lam0 lam2 M : ℝ) (hM : 0 < M)
    (α : Fin n → ℝ) (g : ℝ) (i : Fin p) : 0 ≤ v X lam0 lam2 M α g i := by
  unfold v
  have := le_max_right ((colInner X α i - g) ^ 2 / (4 * lam2) - lam0) 0
  have : 0 ≤ M * |g| := mul_nonneg hM.le (abs_nonneg g)
  linarith

/-- `γ̂ᵢ` minimizes `v(α̂, ·)` coordinatewise. -/
lemma gammaHat_min {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (βhat γhat : Fin p → ℝ) (hγ : IsGammaHat X y lam0 lam2 M βhat γhat)
    (i : Fin p) (g : ℝ) :
    v X lam0 lam2 M (alphaHat X y βhat) (γhat i) i ≤ v X lam0 lam2 M (alphaHat X y βhat) g i := by
  have := hγ (Function.update γhat i g)
  unfold h1 at this
  rw [sum_update_dep γhat i g (fun j t => v X lam0 lam2 M (alphaHat X y βhat) t j)] at this
  linarith

theorem lemma2 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hreg : Real.sqrt (lam0 / lam2) ≤ M)
    (hX : ∀ i, ∑ r, X r i ^ 2 = 1) (hy : ∑ r, y r ^ 2 = 1)
    (βs : Fin p → ℝ) (hβs : IsOptimal X y lam0 lam2 M βs)
    (βhat : Fin p → ℝ) (hbox : βhat ∈ L0BnB.Reduced.box p M) (hV : Vset X y lam0 lam2 M βhat = ∅)
    (γhat : Fin p → ℝ) (hγ : IsGammaHat X y lam0 lam2 M βhat γhat) :
    (∀ i, βhat i = 0 → v X lam0 lam2 M (alphaHat X y βhat) (γhat i) i = 0) ∧
    (∀ i, βhat i ≠ 0 →
      v X lam0 lam2 M (alphaHat X y βhat) (γhat i) i ≤
        cLemma2 lam2 M βs i * primalGap X βs βhat + (4 * lam2)⁻¹ * primalGap X βs βhat ^ 2
          + v X lam0 lam2 M (L0BnB.Duality.alphaStar X y βs) (L0BnB.Duality.gammaStar X y lam2 M βs i) i) := by
  constructor
  · intro i hi
    apply le_antisymm _ (v_nonneg X lam0 lam2 M hM _ _ i)
    refine (gammaHat_min X y lam0 lam2 M βhat γhat hγ i 0).trans ?_
    have hc : |colInner X (resid X y βhat) i| ≤ cThr lam0 lam2 M := by
      by_contra hcon
      have : i ∈ Vset X y lam0 lam2 M βhat := by
        rw [prop3 X y lam0 lam2 M hlam0 hlam2 hM hX βhat]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hi, not_le.1 hcon⟩
      rw [hV] at this; simp at this
    have hthr : cThr lam0 lam2 M = 2 * Real.sqrt (lam0 * lam2) := by
      unfold cThr; rw [if_pos hreg]
    rw [hthr] at hc
    have e1 : colInner X (alphaHat X y βhat) i = - colInner X (resid X y βhat) i := colInner_neg X _ i
    unfold v
    rw [e1]
    simp only [sub_zero, abs_zero, mul_zero, add_zero]
    apply max_le _ le_rfl
    have hsq : (-colInner X (resid X y βhat) i) ^ 2 ≤ 4 * (lam0 * lam2) := by
      rw [neg_sq]
      have := sq_le_sq' (neg_le_of_abs_le hc) (le_of_abs_le hc)
      rw [mul_pow, Real.sq_sqrt (by positivity)] at this
      linarith
    rw [sub_nonpos, div_le_iff₀ (by positivity)]
    linarith
  · intro i _
    set g := L0BnB.Duality.gammaStar X y lam2 M βs i
    refine (gammaHat_min X y lam0 lam2 M βhat γhat hγ i g).trans ?_
    set a := colInner X (L0BnB.Duality.alphaStar X y βs) i
    set e := colInner X (Matrix.mulVec X (βs - βhat)) i
    set ε := primalGap X βs βhat
    set ci := cLemma2 lam2 M βs i
    have hε : 0 ≤ ε := Real.sqrt_nonneg _
    have he : |e| ≤ ε := abs_gap_le X hX βs βhat i
    have hsub : colInner X (alphaHat X y βhat) i = a - e := colInner_hat_sub X y βs βhat i
    have hci0 : 0 ≤ ci := by
      unfold ci cLemma2; split_ifs <;> positivity
    -- the key bound |a - g| ≤ 2 λ₂ cᵢ
    have hag : |a - g| ≤ 2 * lam2 * ci := by
      have hbox' := hβs.1 i
      by_cases hbM : |βs i| = M
      · have hg : g = a - 2 * M * lam2 * Real.sign a := by
          show L0BnB.Duality.gammaStar X y lam2 M βs i = _
          unfold L0BnB.Duality.gammaStar; rw [if_pos hbM]; rfl
        have hci : ci = M := by
          show cLemma2 lam2 M βs i = M
          unfold cLemma2; rw [if_neg (by rw [hbM]; exact lt_irrefl M)]
        rw [hg, hci, show a - (a - 2 * M * lam2 * Real.sign a) = 2 * M * lam2 * Real.sign a by ring,
          abs_mul, abs_of_pos (by positivity)]
        rcases Real.sign_apply_eq a with h | h | h <;> rw [h] <;> norm_num <;> nlinarith
      · have hlt : |βs i| < M := lt_of_le_of_ne hbox' hbM
        have hg : g = 0 := by
          show L0BnB.Duality.gammaStar X y lam2 M βs i = 0
          unfold L0BnB.Duality.gammaStar; rw [if_neg hbM]
        have hci : ci = (2 * lam2)⁻¹ := by
          show cLemma2 lam2 M βs i = _
          unfold cLemma2; rw [if_pos hlt]
        rw [hg, hci, sub_zero, show 2 * lam2 * (2 * lam2)⁻¹ = 1 by field_simp]
        exact (abs_colInner_le X i (hX i) _).trans
          (alphaStar_norm_le_one X y lam0 lam2 M hlam0 hlam2 hM hy βs hβs)
    unfold v
    rw [hsub]
    have hquad : (a - e - g) ^ 2 ≤ (a - g) ^ 2 + 4 * lam2 * ci * ε + ε ^ 2 := by
      have h1 : (a - e - g) ^ 2 = (a - g) ^ 2 - 2 * (a - g) * e + e ^ 2 := by ring
      have h2 : -(2 * (a - g) * e) ≤ 2 * |a - g| * |e| := by
        have := neg_abs_le ((a - g) * e)
        rw [abs_mul] at this
        linarith
      have h3 : |a - g| * |e| ≤ (2 * lam2 * ci) * ε :=
        mul_le_mul hag he (abs_nonneg _) (by positivity)
      have h4 : e ^ 2 ≤ ε ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) he 2
      nlinarith
    have hdiv : (a - e - g) ^ 2 / (4 * lam2) ≤
        (a - g) ^ 2 / (4 * lam2) + (ci * ε + (4 * lam2)⁻¹ * ε ^ 2) := by
      rw [div_le_iff₀ (by positivity)]
      have : ((a - g) ^ 2 / (4 * lam2) + (ci * ε + (4 * lam2)⁻¹ * ε ^ 2)) * (4 * lam2) =
          (a - g) ^ 2 + 4 * lam2 * ci * ε + ε ^ 2 := by field_simp; ring
      rw [this]; exact hquad
    have hE : 0 ≤ ci * ε + (4 * lam2)⁻¹ * ε ^ 2 := by positivity
    have : max ((a - e - g) ^ 2 / (4 * lam2) - lam0) 0 ≤
        max ((a - g) ^ 2 / (4 * lam2) - lam0) 0 + (ci * ε + (4 * lam2)⁻¹ * ε ^ 2) := by
      apply max_le
      · linarith [le_max_left ((a - g) ^ 2 / (4 * lam2) - lam0) 0]
      · linarith [le_max_right ((a - g) ^ 2 / (4 * lam2) - lam0) 0]
    linarith

theorem thm3 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hX : ∀ i, ∑ r, X r i ^ 2 = 1) (hy : ∑ r, y r ^ 2 = 1)
    (βs : Fin p → ℝ) (hβs : IsOptimal X y lam0 lam2 M βs)
    (βhat : Fin p → ℝ) (hbox : βhat ∈ L0BnB.Reduced.box p M) (hV : Vset X y lam0 lam2 M βhat = ∅)
    (γhat : Fin p → ℝ) (hγ : IsGammaHat X y lam0 lam2 M βhat γhat)
    (μhat : Fin p → ℝ) (hμ : IsMuHat X y lam0 lam2 M βhat μhat) :
    (Real.sqrt (lam0 / lam2) ≤ M →
      h1 X y lam0 lam2 M (L0BnB.Duality.alphaStar X y βs) (L0BnB.Duality.gammaStar X y lam2 M βs)
          - 2 * primalGap X βs βhat - (1 / 2) * primalGap X βs βhat ^ 2
          - ∑ i ∈ supp βhat,
              (cLemma2 lam2 M βs i * primalGap X βs βhat + (4 * lam2)⁻¹ * primalGap X βs βhat ^ 2)
        ≤ h1 X y lam0 lam2 M (alphaHat X y βhat) γhat) ∧
    (M < Real.sqrt (lam0 / lam2) →
      L0BnB.Duality.h2 y M (L0BnB.Duality.rhoStar X y βs) (L0BnB.Duality.muStar X y lam0 lam2 M βs)
          - primalGap X βs βhat * (2 + M * ((supp βhat).card : ℝ)) - primalGap X βs βhat ^ 2 / 2
        ≤ L0BnB.Duality.h2 y M (rhoHat X y βhat) μhat) := by
  classical
  set ε := primalGap X βs βhat
  constructor
  · intro hreg
    obtain ⟨hA, hB⟩ := lemma2 X y lam0 lam2 M hlam0 hlam2 hM hreg hX hy βs hβs βhat hbox hV γhat hγ
    have h53 := ineq53 X y lam0 lam2 M hlam0 hlam2 hM hy βs hβs βhat
    set E : Fin p → ℝ := fun i => cLemma2 lam2 M βs i * ε + (4 * lam2)⁻¹ * ε ^ 2
    have hpt : ∀ i, v X lam0 lam2 M (alphaHat X y βhat) (γhat i) i ≤
        (if βhat i ≠ 0 then E i else 0) +
          v X lam0 lam2 M (L0BnB.Duality.alphaStar X y βs) (L0BnB.Duality.gammaStar X y lam2 M βs i) i := by
      intro i
      by_cases hi : βhat i = 0
      · rw [hA i hi, if_neg (not_not.2 hi), zero_add]
        exact v_nonneg X lam0 lam2 M hM _ _ i
      · rw [if_pos hi]; exact hB i hi
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpt i)
    rw [Finset.sum_add_distrib, ← Finset.sum_filter] at hsum
    have hsupp : supp βhat = Finset.univ.filter (fun i => βhat i ≠ 0) := by
      unfold supp; congr
    unfold h1
    rw [hsupp]
    linarith
  · intro hreg
    have h56 := ineq56 X y lam0 lam2 M hlam0 hlam2 hM hy βs hβs βhat μhat
    have hpt : ∀ i, |μhat i| ≤ (if βhat i ≠ 0 then ε else 0) +
        |L0BnB.Duality.muStar X y lam0 lam2 M βs i| := by
      intro i
      by_cases hi : βhat i = 0
      · rw [if_neg (not_not.2 hi), zero_add]
        have hc : |colInner X (resid X y βhat) i| ≤ cThr lam0 lam2 M := by
          by_contra hcon
          have : i ∈ Vset X y lam0 lam2 M βhat := by
            rw [prop3 X y lam0 lam2 M hlam0 hlam2 hM hX βhat]
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hi, not_le.1 hcon⟩
          rw [hV] at this; simp at this
        have hthr : cThr lam0 lam2 M = lam0 / M + lam2 * M := by
          unfold cThr; rw [if_neg (not_le.2 hreg)]
        rw [hthr] at hc
        have e1 : colInner X (rhoHat X y βhat) i = - colInner X (resid X y βhat) i :=
          colInner_neg X _ i
        rw [eq28 X y lam0 lam2 M hlam0 hlam2 hM βhat μhat hμ i, e1, abs_neg,
          max_eq_right (by linarith)]
        simp
      · rw [if_pos hi]
        exact ineq57 X y lam0 lam2 M hlam0 hlam2 hM hreg hX βs hβs βhat μhat hμ i hi
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpt i)
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at hsum
    have hsupp : supp βhat = Finset.univ.filter (fun i => βhat i ≠ 0) := by
      unfold supp; congr
    rw [hsupp]
    have hMs := mul_le_mul_of_nonneg_left hsum hM.le
    unfold L0BnB.Duality.h2 at h56 ⊢
    have e2 : L0BnB.Duality.rhoStar X y βs = L0BnB.Duality.rhoStar X y βs := rfl
    nlinarith

end L0BnB.DualGap.Aux

open L0BnB.DualGap

theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hreg : Real.sqrt (lam0 / lam2) ≤ M)
    (hX : ∀ i, ∑ r, X r i ^ 2 = 1) (hy : ∑ r, y r ^ 2 = 1)
    (βs : Fin p → ℝ) (hβs : IsOptimal X y lam0 lam2 M βs)
    (βhat : Fin p → ℝ) (hbox : βhat ∈ L0BnB.Reduced.box p M) (hV : Vset X y lam0 lam2 M βhat = ∅)
    (γhat : Fin p → ℝ) (hγ : IsGammaHat X y lam0 lam2 M βhat γhat) :
    (∀ i, βhat i = 0 → v X lam0 lam2 M (alphaHat X y βhat) (γhat i) i = 0) ∧
    (∀ i, βhat i ≠ 0 →
      v X lam0 lam2 M (alphaHat X y βhat) (γhat i) i ≤
        cLemma2 lam2 M βs i * primalGap X βs βhat + (4 * lam2)⁻¹ * primalGap X βs βhat ^ 2
          + v X lam0 lam2 M (L0BnB.Duality.alphaStar X y βs) (L0BnB.Duality.gammaStar X y lam2 M βs i) i) :=
  L0BnB.DualGap.Aux.lemma2 X y lam0 lam2 M hlam0 hlam2 hM hreg hX hy βs hβs βhat hbox hV γhat hγ
