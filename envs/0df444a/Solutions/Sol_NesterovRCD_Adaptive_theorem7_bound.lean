-- Prove2me | solution 1 for NesterovRCD.Adaptive.theorem7_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T13:35:51.567497+00:00
-- url     : https://prove2.me/submissions/064299a6-579d-41f4-9ab7-c30fa7116855

import Mathlib
import Definitions.Def_ConvexOptAlg_CoordDescent_Defs
import Definitions.Def_NesterovRCD_Adaptive_RACDM

open ConvexOptAlg.CoordDescent NesterovRCD.Adaptive

namespace RACDMProof

variable {n : ℕ}

lemma inner_eq_sum (v w : Vec n) : inner ℝ v w = ∑ i, v i * w i := by
  simp [PiLp.inner_apply, mul_comm]

lemma inner_single (v : Vec n) (i : Fin n) (u : ℝ) :
    inner ℝ v (u • EuclideanSpace.single i (1 : ℝ)) = u * v i := by
  rw [inner_smul_right, EuclideanSpace.inner_single_right]
  simp

lemma line_deriv {f : Vec n → ℝ} {g : Vec n → Vec n} (hg : ∀ x, HasGradientAt f (g x) x)
    (x h : Vec n) (t : ℝ) :
    HasDerivAt (fun u : ℝ => f (x + u • h)) (inner ℝ (g (x + t • h)) h) t := by
  have h1 := (hg (x + t • h)).hasFDerivAt.comp_hasDerivAt t
    (by simpa only [id_eq, one_smul] using (((hasDerivAt_id t).smul_const h).const_add x))
  simpa [Function.comp_def] using h1

lemma convex_support {f : Vec n → ℝ} {g : Vec n → Vec n} (hc : ConvexOn ℝ Set.univ f)
    (hg : ∀ x, HasGradientAt f (g x) x) (x y : Vec n) :
    f x + inner ℝ (g x) (y - x) ≤ f y := by
  have hline : ConvexOn ℝ Set.univ (fun t : ℝ => f (x + t • (y - x))) := by
    refine ⟨convex_univ, ?_⟩
    intro u _ v _ a b ha hb hab
    convert hc.2 (Set.mem_univ (x + u • (y - x)))
      (Set.mem_univ (x + v • (y - x))) ha hb hab using 1
    apply congrArg f
    calc
      x + (a * u + b * v) • (y - x) = (a + b) • x + (a * u + b * v) • (y - x) := by
        rw [hab, one_smul]
      _ = a • (x + u • (y - x)) + b • (x + v • (y - x)) := by module
  have hd := line_deriv hg x (y - x) 0
  simp only [zero_smul, add_zero] at hd
  have hs := hline.le_slope_of_hasDerivAt (Set.mem_univ (0 : ℝ))
    (Set.mem_univ (1 : ℝ)) zero_lt_one hd
  simp only [slope, zero_smul, add_zero, one_smul, add_sub_cancel, sub_zero,
    inv_one, one_smul, vsub_eq_sub] at hs
  linarith

/-- Coordinate descent lemma: `f(x + u eᵢ) ≤ f(x) + u ∇ᵢf(x) + Lᵢ u²/2`. -/
lemma coord_upper {f : Vec n → ℝ} {g : Vec n → Vec n} {L : Fin n → ℝ}
    (hL : IsCoordSmooth f g L) (x : Vec n) (i : Fin n) (u : ℝ) :
    f (x + u • EuclideanSpace.single i (1 : ℝ)) ≤ f x + u * g x i + L i / 2 * u ^ 2 := by
  set e : Vec n := EuclideanSpace.single i (1 : ℝ) with he
  let G : ℝ → ℝ := fun t => f (x + t • (u • e)) - f x - t * (u * g x i) - L i / 2 * t ^ 2 * u ^ 2
  have hd (t : ℝ) : HasDerivAt G
      (u * g (x + (t * u) • e) i - u * g x i - L i * t * u ^ 2) t := by
    have hf := line_deriv hL.1 x (u • e) t
    have hin : inner ℝ (g (x + t • (u • e))) (u • e) = u * g (x + (t * u) • e) i := by
      rw [he, inner_single, smul_smul]
    rw [hin] at hf
    have hD := ((hf.sub_const (f x)).sub ((hasDerivAt_id t).mul_const
      (u * g x i))).sub
      ((((hasDerivAt_id t).pow 2).const_mul (L i / 2)).mul_const (u ^ 2))
    exact hD.congr_deriv (by simp only [id, one_mul, mul_one, Nat.cast_ofNat]; ring)
  have hsign (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      u * g (x + (t * u) • e) i - u * g x i - L i * t * u ^ 2 ≤ 0 := by
    have hn := hL.2 i x (t * u)
    rw [abs_mul, abs_of_nonneg ht.1] at hn
    have h1 : u * (g (x + (t * u) • e) i - g x i) ≤ |u| * |g (x + (t * u) • e) i - g x i| := by
      rw [← abs_mul]; exact le_abs_self _
    have h2 := mul_le_mul_of_nonneg_left hn (abs_nonneg u)
    have h3 : |u| * (L i * (t * |u|)) = L i * t * u ^ 2 := by
      rw [show u ^ 2 = |u| * |u| by rw [abs_mul_abs_self u]; ring]; ring
    nlinarith
  have hg : AntitoneOn G (Set.Icc (0 : ℝ) 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => (hd t).hasDerivWithinAt)
      (fun t ht => hsign t (interior_subset ht))
  have hh := hg (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by constructor <;> norm_num) zero_le_one
  simp only [G, zero_smul, add_zero, zero_mul, one_smul, one_mul, sub_self] at hh
  norm_num at hh
  linarith

lemma L_nonneg {f : Vec n → ℝ} {g : Vec n → Vec n} {L : Fin n → ℝ}
    (hL : IsCoordSmooth f g L) (i : Fin n) : 0 ≤ L i := by
  have h := hL.2 i 0 1
  simp only [abs_one, mul_one] at h
  exact (abs_nonneg _).trans h

lemma trial_eq (g : Vec n → Vec n) (x : Vec n) (i : Fin n) (ℓ : ℝ) :
    trial g x i ℓ = x + (-(ℓ⁻¹ * g x i)) • EuclideanSpace.single i (1 : ℝ) := by
  simp only [trial, neg_smul, sub_eq_add_neg]

/-- The loop test fails as soon as the estimate exceeds `L_i`. -/
lemma test_fails {f : Vec n → ℝ} {g : Vec n → Vec n} {L : Fin n → ℝ}
    (hL : IsCoordSmooth f g L) (x : Vec n) (i : Fin n) (lam : ℝ) (hlam : L i < lam) :
    ¬ (g x i * g (trial g x i lam) i < 0) := by
  intro h
  have hL0 := L_nonneg hL i
  have hlpos : 0 < lam := lt_of_le_of_lt hL0 hlam
  set a := g x i with ha
  set b := g (trial g x i lam) i with hb
  have hn := hL.2 i x (-(lam⁻¹ * a))
  rw [← trial_eq, ← hb] at hn
  rw [abs_neg, abs_mul, abs_of_pos (inv_pos.mpr hlpos)] at hn
  have hD : lam * |b - a| ≤ L i * |a| := by
    have := mul_le_mul_of_nonneg_left hn hlpos.le
    calc lam * |b - a| ≤ lam * (L i * (lam⁻¹ * |a|)) := this
      _ = L i * |a| := by field_simp
  have habs : -(a * (b - a)) ≤ |a| * |b - a| := by
    rw [← abs_mul]; exact neg_le_abs _
  have ha2 : a ^ 2 = |a| ^ 2 := (sq_abs a).symm
  have h1 : |a| ^ 2 < |a| * |b - a| := by nlinarith
  have h2 : lam * |a| ^ 2 < |a| * (lam * |b - a|) := by nlinarith
  have h3 : |a| * (lam * |b - a|) ≤ |a| * (L i * |a|) :=
    mul_le_mul_of_nonneg_left hD (abs_nonneg a)
  have h4 : L i * |a| ^ 2 ≤ lam * |a| ^ 2 :=
    mul_le_mul_of_nonneg_right hlam.le (sq_nonneg _)
  nlinarith

theorem eq_6_4' {f : Vec n → ℝ} {g : Vec n → Vec n} {L : Fin n → ℝ}
    (hL : IsCoordSmooth f g L) (x : Vec n) (i : Fin n) (ℓ : ℝ) (hℓ : 0 < ℓ) (hℓL : ℓ ≤ L i) :
    (∃ d : ℕ, ¬ (g x i * g (trial g x i (2 ^ d * ℓ)) i < 0)) ∧
      2 ^ doublings g x i ℓ * ℓ ≤ 2 * L i := by
  have hLpos : 0 < L i := lt_of_lt_of_le hℓ hℓL
  refine ⟨?_, ?_⟩
  · obtain ⟨d, hd⟩ := pow_unbounded_of_one_lt (L i / ℓ) (by norm_num : (1 : ℝ) < 2)
    refine ⟨d, test_fails hL x i _ ?_⟩
    rwa [div_lt_iff₀ hℓ] at hd
  · by_contra hcon
    push_neg at hcon
    obtain ⟨m', hm'⟩ : ∃ m', doublings g x i ℓ = m' + 1 := by
      rcases Nat.eq_zero_or_eq_succ_pred (doublings g x i ℓ) with h0 | h
      · rw [h0] at hcon; norm_num at hcon; linarith
      · exact ⟨_, h⟩
    rw [hm', pow_succ] at hcon
    have hmem : m' ∈ {d : ℕ | ¬ (g x i * g (trial g x i (2 ^ d * ℓ)) i < 0)} :=
      test_fails hL x i _ (by linarith)
    have := Nat.sInf_le hmem
    change doublings g x i ℓ ≤ m' at this
    omega

lemma racdmStep_eq (g : Vec n → Vec n) (x : Vec n) (Lh : Fin n → ℝ) (i : Fin n) :
    racdmStep g (x, Lh) i =
      (trial g x i (2 ^ doublings g x i (Lh i) * Lh i),
        Function.update Lh i (2 ^ doublings g x i (Lh i) * Lh i / 2)) := rfl

lemma doublings_mem {f : Vec n → ℝ} {g : Vec n → Vec n} {L : Fin n → ℝ}
    (hL : IsCoordSmooth f g L) (x : Vec n) (i : Fin n) (ℓ : ℝ) (hℓ : 0 < ℓ) (hℓL : ℓ ≤ L i) :
    ¬ (g x i * g (trial g x i (2 ^ doublings g x i ℓ * ℓ)) i < 0) := by
  have hne := (eq_6_4' hL x i ℓ hℓ hℓL).1
  exact Nat.sInf_mem (s := {d : ℕ | ¬ (g x i * g (trial g x i (2 ^ d * ℓ)) i < 0)}) hne

lemma step_bounds {f : Vec n → ℝ} {g : Vec n → Vec n} {L : Fin n → ℝ}
    (hL : IsCoordSmooth f g L) (x : Vec n) (Lh : Fin n → ℝ)
    (hLh : ∀ i, 0 < Lh i ∧ Lh i ≤ L i) (j : Fin n) :
    ∀ i, 0 < (racdmStep g (x, Lh) j).2 i ∧ (racdmStep g (x, Lh) j).2 i ≤ L i := by
  intro i
  rw [racdmStep_eq]
  by_cases hij : i = j
  · subst hij
    simp only [Function.update_self]
    have h2 := (eq_6_4' hL x i (Lh i) (hLh i).1 (hLh i).2).2
    have h1 : (1 : ℝ) ≤ 2 ^ doublings g x i (Lh i) := one_le_pow₀ (by norm_num)
    have hp := (hLh i).1
    constructor
    · have : 0 < 2 ^ doublings g x i (Lh i) * Lh i := by positivity
      linarith
    · linarith
  · simp only [Function.update_of_ne hij]
    exact hLh i

theorem theorem7_bound' {f : Vec n → ℝ} {g : Vec n → Vec n} {L : Fin n → ℝ}
    (hL : IsCoordSmooth f g L) (L0 : Fin n → ℝ) (hL0 : ∀ i, 0 < L0 i ∧ L0 i ≤ L i)
    (x0 : Vec n) : ∀ (k : ℕ) (idx : Fin k → Fin n) (i : Fin n),
    0 < (racdm g L0 x0 k idx).2 i ∧ (racdm g L0 x0 k idx).2 i ≤ L i := by
  intro k
  induction k with
  | zero => intro idx i; exact hL0 i
  | succ k ih =>
    intro idx i
    change 0 < (racdmStep g (racdm g L0 x0 k (Fin.init idx)) (idx (Fin.last k))).2 i ∧
      (racdmStep g (racdm g L0 x0 k (Fin.init idx)) (idx (Fin.last k))).2 i ≤ L i
    exact step_bounds hL _ _ (ih (Fin.init idx)) _ i

theorem step_decrease' {f : Vec n → ℝ} {g : Vec n → Vec n}
    (hconv : ConvexOn ℝ Set.univ f) {L : Fin n → ℝ} (hL : IsCoordSmooth f g L)
    (x : Vec n) (Lh : Fin n → ℝ) (i : Fin n) (hpos : 0 < Lh i) (hle : Lh i ≤ L i) :
    3 / (8 * L i) * g x i ^ 2 ≤ f x - f (racdmStep g (x, Lh) i).1 := by
  have hLpos : 0 < L i := lt_of_lt_of_le hpos hle
  rw [racdmStep_eq]
  simp only
  set ℓ := 2 ^ doublings g x i (Lh i) * Lh i with hℓdef
  have hℓ2 : ℓ ≤ 2 * L i := (eq_6_4' hL x i (Lh i) hpos hle).2
  have hℓpos : 0 < ℓ := by positivity
  have hab0 := doublings_mem hL x i (Lh i) hpos hle
  rw [← hℓdef] at hab0
  set e : Vec n := EuclideanSpace.single i (1 : ℝ) with he
  set a := g x i with ha
  set xp := trial g x i ℓ with hxp
  set b := g xp i with hb
  have hab : 0 ≤ a * b := le_of_not_gt hab0
  set u := -(ℓ⁻¹ * a) with hu
  have hxp' : xp = x + u • e := trial_eq g x i ℓ
  set w := -((a - b) / L i) with hw
  set z := x + w • e with hz
  have hdesc : f z ≤ f x + w * a + L i / 2 * w ^ 2 := coord_upper hL x i w
  have hsupp := convex_support hconv hL.1 xp z
  have hzx : z - xp = (w - u) • e := by rw [hz, hxp']; module
  rw [hzx] at hsupp
  rw [inner_single] at hsupp
  have key : (w - u) * b - w * a - L i / 2 * w ^ 2 = (a - b) ^ 2 / (2 * L i) + a * b / ℓ := by
    rw [hw, hu]; field_simp; ring
  have hcmp : a * b / (2 * L i) ≤ a * b / ℓ :=
    div_le_div_of_nonneg_left hab hℓpos hℓ2
  have hsq : (a - b) ^ 2 / (2 * L i) + a * b / (2 * L i) - 3 / (8 * L i) * a ^ 2 =
      (b - a / 2) ^ 2 / (2 * L i) := by field_simp; ring
  have hnn : 0 ≤ (b - a / 2) ^ 2 / (2 * L i) := by positivity
  linarith

lemma pGamma_zero (hn : 0 < n) (L : Fin n → ℝ) (i : Fin n) : pGamma L 0 i = 1 / n := by
  simp [pGamma, Real.rpow_zero]

lemma wnormDual_one_sq {L : Fin n → ℝ} (hL : ∀ i, 0 < L i) (v : Vec n) :
    wnormDual L 1 v ^ 2 = ∑ i, v i ^ 2 / L i := by
  unfold wnormDual
  rw [Real.sq_sqrt]
  · simp [Real.rpow_one]
  · exact Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (Real.rpow_nonneg (hL i).le _)

theorem expected_decrease' (hn : 0 < n) {f : Vec n → ℝ} {g : Vec n → Vec n}
    (hconv : ConvexOn ℝ Set.univ f) {L : Fin n → ℝ} (hL : IsCoordSmooth f g L)
    (x : Vec n) (Lh : Fin n → ℝ) (hLh : ∀ i, 0 < Lh i ∧ Lh i ≤ L i) :
    3 / (8 * n) * wnormDual L 1 (g x) ^ 2 ≤
      f x - ∑ i, pGamma L 0 i * f (racdmStep g (x, Lh) i).1 := by
  have hLpos : ∀ i, 0 < L i := fun i => lt_of_lt_of_le (hLh i).1 (hLh i).2
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rw [wnormDual_one_sq hLpos]
  simp only [pGamma_zero hn]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (step_decrease' hconv hL x Lh i (hLh i).1 (hLh i).2)
      (show (0 : ℝ) ≤ 1 / n by positivity))
  have h1 : ∑ i : Fin n, 1 / (n : ℝ) * (f x - f (racdmStep g (x, Lh) i).1) =
      f x - ∑ i, 1 / (n : ℝ) * f (racdmStep g (x, Lh) i).1 := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have h2 : ∑ i : Fin n, 1 / (n : ℝ) * (3 / (8 * L i) * g x i ^ 2) =
      3 / (8 * n) * ∑ i, g x i ^ 2 / L i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have := hLpos i
    field_simp
  linarith

/-! ### Expectations over the draws -/

def ex (p : Fin n → ℝ) (k : ℕ) (F : (Fin k → Fin n) → ℝ) : ℝ :=
  ∑ idx : Fin k → Fin n, (∏ s, p (idx s)) * F idx

lemma rcdExpect_eq (β : Fin n → ℝ) (γ : ℝ) (k : ℕ) (F : (Fin k → Fin n) → ℝ) :
    rcdExpect β γ k F = ex (pGamma β γ) k F := rfl

theorem ex_zero (p : Fin n → ℝ) (F : (Fin 0 → Fin n) → ℝ) :
    ex p 0 F = F Fin.elim0 := by
  simp [ex]
  exact congrArg F (Subsingleton.elim _ _)

theorem ex_succ (p : Fin n → ℝ) (k : ℕ) (F : (Fin (k + 1) → Fin n) → ℝ) :
    ex p (k + 1) F = ex p k (fun idx => ∑ i, p i * F (Fin.snoc idx i)) := by
  classical
  unfold ex
  rw [← (Fin.snocEquiv (fun _ : Fin (k + 1) => Fin n)).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.snocEquiv_apply]
  have hw (i : Fin n) (idx : Fin k → Fin n) :
      (∏ j : Fin (k + 1), p ((Fin.snoc idx i : Fin (k + 1) → Fin n) j)) =
        (∏ j, p (idx j)) * p i := by
    rw [Fin.prod_univ_castSucc]
    simp
  simp_rw [hw]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro idx _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (∏ j, p (idx j)) * p i * F (Fin.snoc idx i) =
    (∏ j, p (idx j)) * (p i * F (Fin.snoc idx i))
  ring

theorem ex_one {p : Fin n → ℝ} (hp : ∑ i, p i = 1) :
    ∀ k, ex p k (fun _ => 1) = 1 := by
  intro k
  induction k with
  | zero => simp [ex]
  | succ k ih =>
    rw [ex_succ]
    simpa only [mul_one, hp] using ih

theorem ex_const {p : Fin n → ℝ} (hp : ∑ i, p i = 1) (k : ℕ) (c : ℝ) :
    ex p k (fun _ => c) = c := by
  unfold ex
  rw [← Finset.sum_mul]
  have h := ex_one hp k
  simp only [ex, mul_one] at h
  rw [h, one_mul]

theorem ex_add (p : Fin n → ℝ) (k : ℕ) (F G : (Fin k → Fin n) → ℝ) :
    ex p k (fun idx => F idx + G idx) = ex p k F + ex p k G := by
  simp only [ex, mul_add, Finset.sum_add_distrib]

theorem ex_sub (p : Fin n → ℝ) (k : ℕ) (F G : (Fin k → Fin n) → ℝ) :
    ex p k (fun idx => F idx - G idx) = ex p k F - ex p k G := by
  simp only [ex, mul_sub, Finset.sum_sub_distrib]

theorem ex_mul (p : Fin n → ℝ) (k : ℕ) (c : ℝ) (F : (Fin k → Fin n) → ℝ) :
    ex p k (fun idx => c * F idx) = c * ex p k F := by
  simp only [ex, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro idx _
  ring

theorem ex_mono {p : Fin n → ℝ} (hp : ∀ i, 0 ≤ p i) (k : ℕ)
    {F G : (Fin k → Fin n) → ℝ} (h : ∀ idx, F idx ≤ G idx) :
    ex p k F ≤ ex p k G := by
  apply Finset.sum_le_sum
  intro idx _
  exact mul_le_mul_of_nonneg_left (h idx) (Finset.prod_nonneg fun j _ => hp (idx j))

theorem ex_nonneg {p : Fin n → ℝ} (hp : ∀ i, 0 ≤ p i) (k : ℕ)
    {F : (Fin k → Fin n) → ℝ} (h : ∀ idx, 0 ≤ F idx) : 0 ≤ ex p k F := by
  apply Finset.sum_nonneg
  intro idx _
  exact mul_nonneg (Finset.prod_nonneg fun j _ => hp (idx j)) (h idx)

theorem ex_sq {p : Fin n → ℝ} (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (k : ℕ) (F : (Fin k → Fin n) → ℝ) :
    ex p k F ^ 2 ≤ ex p k (fun idx => F idx ^ 2) := by
  have h := ex_nonneg hp k (fun idx => sq_nonneg (F idx - ex p k F))
  have he : ex p k (fun idx => (F idx - ex p k F) ^ 2) =
      ex p k (fun idx => F idx ^ 2) - ex p k F ^ 2 := by
    have hf : (fun idx => (F idx - ex p k F) ^ 2) =
        (fun idx => F idx ^ 2 - (2 * ex p k F) * F idx + ex p k F ^ 2) := by
      funext idx
      ring
    rw [hf, ex_add, ex_sub, ex_mul, ex_const hs]
    ring
  rw [he] at h
  linarith

theorem scalar_rate {C m : ℝ} (hC : 0 ≤ C) (hm : 2 ≤ m) (a : ℕ → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hzero : a 0 ≤ C / m)
    (hstep : ∀ k, a k ^ 2 ≤ C * (a k - a (k + 1))) :
    ∀ k : ℕ, a k ≤ C / ((k : ℝ) + m) := by
  by_cases hc : C = 0
  · intro k
    have h := hstep k
    rw [hc] at h ⊢
    simp only [zero_mul, zero_div] at h ⊢
    nlinarith [sq_nonneg (a k)]
  have hcp : 0 < C := lt_of_le_of_ne hC (Ne.symm hc)
  intro k
  induction k with
  | zero => simpa using hzero
  | succ k ih =>
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
    have hd : 0 < (k : ℝ) + m := by linarith
    have hd' : 0 < (k : ℝ) + m + 1 := by linarith
    have hbound : a k * ((k : ℝ) + m) ≤ C := (le_div_iff₀ hd).mp ih
    have hu : C / ((k : ℝ) + m) ≤ C / 2 := by
      apply div_le_div_of_nonneg_left hC (by norm_num)
      linarith
    have hmono : C * a k - a k ^ 2 ≤
        C * (C / ((k : ℝ) + m)) - (C / ((k : ℝ) + m)) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ih)
        (show 0 ≤ C - a k - C / ((k : ℝ) + m) by linarith [ha k])]
    have hnext : C * (C / ((k : ℝ) + m)) - (C / ((k : ℝ) + m)) ^ 2 ≤
        C * (C / ((k : ℝ) + m + 1)) := by
      have hid : C * (C / ((k : ℝ) + m + 1)) -
          (C * (C / ((k : ℝ) + m)) - (C / ((k : ℝ) + m)) ^ 2) =
          C ^ 2 / (((k : ℝ) + m) ^ 2 * ((k : ℝ) + m + 1)) := by
        field_simp; ring
      have : 0 ≤ C ^ 2 / (((k : ℝ) + m) ^ 2 * ((k : ℝ) + m + 1)) := by positivity
      linarith
    have hs := hstep k
    have hn : C * a (k + 1) ≤ C * (C / ((k : ℝ) + m + 1)) := by linarith
    have hr := (mul_le_mul_iff_right₀ hcp).mp hn
    rw [Nat.cast_add, Nat.cast_one]
    rw [show (k : ℝ) + 1 + m = (k : ℝ) + m + 1 by ring]
    exact hr

/-! ### Geometry: minimizer, upper model, duality -/

lemma grad_min_zero {f : Vec n → ℝ} {g : Vec n → Vec n} {L : Fin n → ℝ}
    (hL : IsCoordSmooth f g L) (hLpos : ∀ i, 0 < L i) {xs : Vec n}
    (hxs : ∀ y, f xs ≤ f y) (i : Fin n) : g xs i = 0 := by
  have h := coord_upper hL xs i (-(g xs i / L i))
  have h2 := hxs (xs + (-(g xs i / L i)) • EuclideanSpace.single i (1 : ℝ))
  have hl := hLpos i
  have hid : -(g xs i / L i) * g xs i + L i / 2 * (-(g xs i / L i)) ^ 2 =
      -(g xs i ^ 2 / (2 * L i)) := by field_simp; ring
  have h3 : 0 ≤ -(g xs i ^ 2 / (2 * L i)) := by linarith
  have h4 : 0 ≤ g xs i ^ 2 / (2 * L i) := by positivity
  have h5 : g xs i ^ 2 / (2 * L i) = 0 := by linarith
  rw [div_eq_zero_iff] at h5
  rcases h5 with h5 | h5
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h5
  · linarith

lemma sum_single_eq (h : Vec n) :
    (∑ i, h i • EuclideanSpace.single i (1 : ℝ)) = h := by
  ext j
  simp [Pi.single_apply]

lemma wnorm_one_sq {L : Fin n → ℝ} (hL : ∀ i, 0 ≤ L i) (v : Vec n) :
    wnorm L 1 v ^ 2 = ∑ i, L i * v i ^ 2 := by
  unfold wnorm
  rw [Real.sq_sqrt]
  · simp [Real.rpow_one]
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (Real.rpow_nonneg (hL i) _) (sq_nonneg _)

lemma full_upper {f : Vec n → ℝ} {g : Vec n → Vec n} (hc : ConvexOn ℝ Set.univ f)
    {L : Fin n → ℝ} (hL : IsCoordSmooth f g L) (hn : 0 < n) (x h : Vec n) :
    f (x + h) ≤ f x + inner ℝ (g x) h + n / 2 * ∑ i, L i * h i ^ 2 := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set e : Fin n → Vec n := fun i => EuclideanSpace.single i (1 : ℝ) with he
  have h1 : ∀ i, (1 / (n : ℝ)) • (x + ((n : ℝ) * h i) • e i) = (1 / (n : ℝ)) • x + h i • e i := by
    intro i; rw [smul_add, smul_smul]; congr 2; field_simp
  have hmean : (∑ i, (1 / (n : ℝ)) • (x + ((n : ℝ) * h i) • e i)) = x + h := by
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, he]
    simp only [sum_single_eq]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_one_div_cancel hnr.ne', one_smul]
  have hj := hc.map_sum_le (t := Finset.univ) (w := fun _ => 1 / (n : ℝ))
    (p := fun i => x + ((n : ℝ) * h i) • e i)
    (fun i _ => by positivity) (by simp; field_simp)
    (fun i _ => Set.mem_univ _)
  rw [hmean] at hj
  have hi (i : Fin n) : (1 / (n : ℝ)) • f (x + ((n : ℝ) * h i) • e i) ≤
      (1 / (n : ℝ)) * f x + h i * g x i + n / 2 * (L i * h i ^ 2) := by
    have hu := mul_le_mul_of_nonneg_left (coord_upper hL x i ((n : ℝ) * h i))
      (show (0 : ℝ) ≤ 1 / n by positivity)
    rw [smul_eq_mul]
    calc 1 / (n : ℝ) * f (x + ((n : ℝ) * h i) • e i) ≤ _ := hu
      _ = _ := by field_simp
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  have hsum : (∑ i, ((1 / (n : ℝ)) * f x + h i * g x i + n / 2 * (L i * h i ^ 2))) =
      f x + inner ℝ (g x) h + n / 2 * ∑ i, L i * h i ^ 2 := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum, inner_eq_sum]
    field_simp
    simp only [mul_comm]
  rw [hsum] at hs
  exact hj.trans hs

lemma cauchy_schwarz {L : Fin n → ℝ} (hL : ∀ i, 0 < L i) (v w : Vec n) :
    inner ℝ v w ≤ wnormDual L 1 v * wnorm L 1 w := by
  rw [inner_eq_sum]
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => v i / Real.sqrt (L i))
    (fun i => Real.sqrt (L i) * w i)
  have e1 : ∀ i, v i / Real.sqrt (L i) * (Real.sqrt (L i) * w i) = v i * w i := by
    intro i; have := Real.sqrt_pos.mpr (hL i); field_simp
  have e2 : ∀ i, (v i / Real.sqrt (L i)) ^ 2 = v i ^ 2 / L i ^ (1 : ℝ) := by
    intro i; rw [div_pow, Real.sq_sqrt (hL i).le, Real.rpow_one]
  have e3 : ∀ i, (Real.sqrt (L i) * w i) ^ 2 = L i ^ (1 : ℝ) * w i ^ 2 := by
    intro i; rw [mul_pow, Real.sq_sqrt (hL i).le, Real.rpow_one]
  simp only [e1, e2, e3] at h
  exact h

lemma wnorm_nonneg' (L : Fin n → ℝ) (v : Vec n) : 0 ≤ wnorm L 1 v := Real.sqrt_nonneg _

lemma wnormDual_nonneg' (L : Fin n → ℝ) (v : Vec n) : 0 ≤ wnormDual L 1 v := Real.sqrt_nonneg _

/-- The core of (6.2): from item 1 of Theorem 7, the one-step decrease, and the expected
decrease, the rate `8nR²/(16+3k)` follows. -/
theorem rate_from {n : ℕ} (hn : 0 < n) (f : Vec n → ℝ) (g : Vec n → Vec n)
    (hconv : ConvexOn ℝ Set.univ f) (L : Fin n → ℝ) (hL : IsCoordSmooth f g L)
    (L0 : Fin n → ℝ) (hL0 : ∀ i, 0 < L0 i ∧ L0 i ≤ L i) (x0 xs : Vec n)
    (hxs : ∀ y, f xs ≤ f y) (R : ℝ)
    (hR : ∀ x, f x ≤ f x0 → ∀ ys, (∀ y, f ys ≤ f y) → wnorm L 1 (x - ys) ≤ R) (k : ℕ)
    (hB : ∀ (k : ℕ) (idx : Fin k → Fin n) (i : Fin n),
      0 < (racdm g L0 x0 k idx).2 i ∧ (racdm g L0 x0 k idx).2 i ≤ L i)
    (hS : ∀ (x : Vec n) (Lh : Fin n → ℝ) (i : Fin n), 0 < Lh i → Lh i ≤ L i →
      3 / (8 * L i) * g x i ^ 2 ≤ f x - f (racdmStep g (x, Lh) i).1)
    (hE : ∀ (x : Vec n) (Lh : Fin n → ℝ), (∀ i, 0 < Lh i ∧ Lh i ≤ L i) →
      3 / (8 * n) * wnormDual L 1 (g x) ^ 2 ≤
        f x - ∑ i, pGamma L 0 i * f (racdmStep g (x, Lh) i).1) :
    rcdExpect L 0 k (fun idx => f (racdm g L0 x0 k idx).1) - f xs ≤
      8 * n * R ^ 2 / (16 + 3 * k) := by
  have hLpos : ∀ i, 0 < L i := fun i => lt_of_lt_of_le (hL0 i).1 (hL0 i).2
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set p := pGamma L 0 with hpdef
  have hp : ∀ i, 0 ≤ p i := fun i => by rw [hpdef, pGamma_zero hn]; positivity
  have hpsum : ∑ i, p i = 1 := by
    simp only [hpdef, pGamma_zero hn, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  -- monotonicity of the run
  have hlevel : ∀ k (idx : Fin k → Fin n), f (racdm g L0 x0 k idx).1 ≤ f x0 := by
    intro k
    induction k with
    | zero => intro idx; exact le_refl _
    | succ k ih =>
      intro idx
      have hb := hB k (Fin.init idx) (idx (Fin.last k))
      have hs := hS (racdm g L0 x0 k (Fin.init idx)).1 (racdm g L0 x0 k (Fin.init idx)).2
        (idx (Fin.last k)) hb.1 hb.2
      have h0 : 0 ≤ 3 / (8 * L (idx (Fin.last k))) *
          g (racdm g L0 x0 k (Fin.init idx)).1 (idx (Fin.last k)) ^ 2 := by
        have := hLpos (idx (Fin.last k)); positivity
      change f (racdmStep g (racdm g L0 x0 k (Fin.init idx)) (idx (Fin.last k))).1 ≤ f x0
      have := ih (Fin.init idx)
      linarith
  have hR0 : 0 ≤ R := (wnorm_nonneg' L (x0 - xs)).trans (hR x0 le_rfl xs hxs)
  set C : ℝ := 8 * n * R ^ 2 / 3 with hC
  have hC0 : 0 ≤ C := by positivity
  -- per-point bound
  have hpt : ∀ (x : Vec n) (Lh : Fin n → ℝ), (∀ i, 0 < Lh i ∧ Lh i ≤ L i) → f x ≤ f x0 →
      (f x - f xs) ^ 2 ≤ C * (f x - ∑ i, p i * f (racdmStep g (x, Lh) i).1) := by
    intro x Lh hLh hx
    have hs := convex_support hconv hL.1 x xs
    have hneg : inner ℝ (g x) (xs - x) = - inner ℝ (g x) (x - xs) := by
      rw [← inner_neg_right, neg_sub]
    rw [hneg] at hs
    have hcs := cauchy_schwarz hLpos (g x) (x - xs)
    have hr := mul_le_mul_of_nonneg_left (hR x hx xs hxs) (wnormDual_nonneg' L (g x))
    have hh : 0 ≤ f x - f xs := sub_nonneg.mpr (hxs x)
    have hb : f x - f xs ≤ wnormDual L 1 (g x) * R := by linarith
    have hb0 := mul_nonneg (wnormDual_nonneg' L (g x)) hR0
    have hsq : (f x - f xs) ^ 2 ≤ (wnormDual L 1 (g x) * R) ^ 2 := pow_le_pow_left₀ hh hb 2
    have he := hE x Lh hLh
    have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 8 * n * R ^ 2 / 3 by positivity)
    have hid : 8 * n * R ^ 2 / 3 * (3 / (8 * n) * wnormDual L 1 (g x) ^ 2) =
        (wnormDual L 1 (g x) * R) ^ 2 := by field_simp
    rw [hid] at hm
    exact hsq.trans hm
  let a : ℕ → ℝ := fun j => ex p j (fun idx => f (racdm g L0 x0 j idx).1) - f xs
  have hgap (j : ℕ) : ex p j (fun idx => f (racdm g L0 x0 j idx).1 - f xs) = a j := by
    rw [ex_sub, ex_const hpsum]
  have ha (j : ℕ) : 0 ≤ a j := by
    rw [← hgap j]
    exact ex_nonneg hp j (fun idx => sub_nonneg.mpr (hxs _))
  have hz : a 0 ≤ C / (16 / 3) := by
    have h := full_upper hconv hL hn xs (x0 - xs)
    rw [add_sub_cancel] at h
    have hz0 : inner ℝ (g xs) (x0 - xs) = 0 := by
      rw [inner_eq_sum]; simp [grad_min_zero hL hLpos hxs]
    rw [hz0, add_zero, ← wnorm_one_sq (fun i => (hLpos i).le)] at h
    have hr := hR x0 le_rfl xs hxs
    have hsq : wnorm L 1 (x0 - xs) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (wnorm_nonneg' _ _) hr 2
    have hm := mul_le_mul_of_nonneg_left hsq (show (0 : ℝ) ≤ n / 2 by positivity)
    simp only [a]
    rw [ex_zero]
    have : C / (16 / 3) = n / 2 * R ^ 2 := by rw [hC]; field_simp; ring
    rw [this]
    change f x0 - f xs ≤ _
    linarith
  have hrun (j : ℕ) : ex p (j + 1) (fun idx => f (racdm g L0 x0 (j + 1) idx).1) =
      ex p j (fun idx => ∑ i, p i * f (racdmStep g (racdm g L0 x0 j idx) i).1) := by
    rw [ex_succ]
    simp only [racdm, Fin.snoc_last, Fin.init_snoc]
  have hs (j : ℕ) : a j ^ 2 ≤ C * (a j - a (j + 1)) := by
    calc
      a j ^ 2 = ex p j (fun idx => f (racdm g L0 x0 j idx).1 - f xs) ^ 2 := by rw [hgap]
      _ ≤ ex p j (fun idx => (f (racdm g L0 x0 j idx).1 - f xs) ^ 2) := ex_sq hp hpsum j _
      _ ≤ ex p j (fun idx => C * (f (racdm g L0 x0 j idx).1 -
          ∑ i, p i * f (racdmStep g (racdm g L0 x0 j idx) i).1)) := by
        apply ex_mono hp
        intro idx
        exact hpt _ _ (hB j idx) (hlevel j idx)
      _ = C * (a j - a (j + 1)) := by
        rw [ex_mul, ex_sub, ← hrun]
        simp only [a]
        ring
  have h := scalar_rate hC0 (by norm_num : (2 : ℝ) ≤ 16 / 3) a ha hz hs k
  rw [rcdExpect_eq]
  simp only [a] at h
  have : C / ((k : ℝ) + 16 / 3) = 8 * n * R ^ 2 / (16 + 3 * k) := by
    rw [hC]; field_simp; ring
  rw [this] at h
  exact h

end RACDMProof

theorem rate_direct {n : ℕ} (hn : 0 < n) (f : Vec n → ℝ) (g : Vec n → Vec n)
    (hconv : ConvexOn ℝ Set.univ f) (L : Fin n → ℝ) (hL : IsCoordSmooth f g L)
    (L0 : Fin n → ℝ) (hL0 : ∀ i, 0 < L0 i ∧ L0 i ≤ L i) (x0 xs : Vec n)
    (hxs : ∀ y, f xs ≤ f y) (R : ℝ)
    (hR : ∀ x, f x ≤ f x0 → ∀ ys, (∀ y, f ys ≤ f y) → wnorm L 1 (x - ys) ≤ R) (k : ℕ) :
    rcdExpect L 0 k (fun idx => f (racdm g L0 x0 k idx).1) - f xs ≤
      8 * n * R ^ 2 / (16 + 3 * k) :=
  RACDMProof.rate_from hn f g hconv L hL L0 hL0 x0 xs hxs R hR k
    (RACDMProof.theorem7_bound' hL L0 hL0 x0)
    (fun x Lh i h1 h2 => RACDMProof.step_decrease' hconv hL x Lh i h1 h2)
    (fun x Lh hLh => RACDMProof.expected_decrease' hn hconv hL x Lh hLh)

namespace RACDMProof

variable {n : ℕ}

/-- Cost of the first `k` iterations (same shape as `numDerivs`, with `k` iterations). -/
noncomputable def cost (g : Vec n → Vec n) (L0 : Fin n → ℝ) (x0 : Vec n) (k : ℕ)
    (idx : Fin k → Fin n) : ℕ :=
  ∑ j : Fin k,
    (doublings g (racdm g L0 x0 j (fun s => idx (Fin.castLE (le_of_lt j.isLt) s))).1 (idx j)
        ((racdm g L0 x0 j (fun s => idx (Fin.castLE (le_of_lt j.isLt) s))).2 (idx j)) + 1)

lemma cost_succ (g : Vec n → Vec n) (L0 : Fin n → ℝ) (x0 : Vec n) (k : ℕ)
    (idx : Fin (k + 1) → Fin n) :
    cost g L0 x0 (k + 1) idx = cost g L0 x0 k (Fin.init idx) +
      (doublings g (racdm g L0 x0 k (Fin.init idx)).1 (idx (Fin.last k))
        ((racdm g L0 x0 k (Fin.init idx)).2 (idx (Fin.last k))) + 1) := by
  unfold cost
  rw [Fin.sum_univ_castSucc]
  rfl

lemma logb_update (Lh : Fin n → ℝ) (j : Fin n) (v : ℝ) :
    ∑ i, Real.logb 2 (Function.update Lh j v i) =
      ∑ i, Real.logb 2 (Lh i) + (Real.logb 2 v - Real.logb 2 (Lh j)) := by
  have h : ∀ i, Real.logb 2 (Function.update Lh j v i) =
      Real.logb 2 (Lh i) + if i = j then (Real.logb 2 v - Real.logb 2 (Lh j)) else 0 := by
    intro i
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Function.update_of_ne hij]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem cost_identity {f : Vec n → ℝ} {g : Vec n → Vec n} {L : Fin n → ℝ}
    (hL : IsCoordSmooth f g L) (L0 : Fin n → ℝ) (hL0 : ∀ i, 0 < L0 i ∧ L0 i ≤ L i)
    (x0 : Vec n) : ∀ (k : ℕ) (idx : Fin k → Fin n),
    (cost g L0 x0 k idx : ℝ) = 2 * k + ∑ i, Real.logb 2 ((racdm g L0 x0 k idx).2 i) -
      ∑ i, Real.logb 2 (L0 i) := by
  intro k
  induction k with
  | zero => intro idx; simp [cost, racdm]
  | succ k ih =>
    intro idx
    rw [cost_succ]
    push_cast
    rw [ih (Fin.init idx)]
    set st := racdm g L0 x0 k (Fin.init idx) with hst
    set j := idx (Fin.last k) with hj
    have hpos := (theorem7_bound' hL L0 hL0 x0 k (Fin.init idx) j).1
    rw [← hst] at hpos
    change _ = 2 * ((k : ℝ) + 1) + ∑ i, Real.logb 2 ((racdmStep g st j).2 i) - _
    have hstep : racdmStep g st j = racdmStep g (st.1, st.2) j := rfl
    rw [hstep, racdmStep_eq]
    simp only
    rw [logb_update]
    set d := doublings g st.1 j (st.2 j)
    have h2 : Real.logb 2 (2 ^ d * st.2 j / 2) = d + Real.logb 2 (st.2 j) - 1 := by
      rw [Real.logb_div (by positivity) (by norm_num), Real.logb_mul (by positivity) hpos.ne',
        Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
      ring
    rw [h2]
    ring

theorem theorem7_count' {f : Vec n → ℝ} {g : Vec n → Vec n} {L : Fin n → ℝ}
    (hL : IsCoordSmooth f g L) (L0 : Fin n → ℝ) (hL0 : ∀ i, 0 < L0 i ∧ L0 i ≤ L i)
    (x0 : Vec n) (k : ℕ) (idx : Fin (k + 1) → Fin n) :
    (numDerivs g L0 x0 k idx : ℝ) ≤ 2 * (k + 1) + ∑ i, Real.logb 2 (L i / L0 i) := by
  have he : numDerivs g L0 x0 k idx = cost g L0 x0 (k + 1) idx := rfl
  rw [he, cost_identity hL L0 hL0 x0 (k + 1) idx]
  have hb := theorem7_bound' hL L0 hL0 x0 (k + 1) idx
  have hsum : ∑ i, Real.logb 2 ((racdm g L0 x0 (k + 1) idx).2 i) ≤ ∑ i, Real.logb 2 (L i) :=
    Finset.sum_le_sum fun i _ => Real.logb_le_logb_of_le (by norm_num) (hb i).1 (hb i).2
  have hdiv : ∑ i, Real.logb 2 (L i / L0 i) = ∑ i, Real.logb 2 (L i) - ∑ i, Real.logb 2 (L0 i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have h1 := (hL0 i).1
    have h2 := lt_of_lt_of_le h1 (hL0 i).2
    rw [Real.logb_div h2.ne' h1.ne']
  rw [hdiv]
  push_cast
  linarith

end RACDMProof

theorem solution {n : ℕ} (f : Vec n → ℝ) (g : Vec n → Vec n) (L : Fin n → ℝ)
    (hL : IsCoordSmooth f g L) (L0 : Fin n → ℝ) (hL0 : ∀ i, 0 < L0 i ∧ L0 i ≤ L i)
    (x0 : Vec n) (k : ℕ) (idx : Fin k → Fin n) (i : Fin n) :
    0 < (racdm g L0 x0 k idx).2 i ∧ (racdm g L0 x0 k idx).2 i ≤ L i :=
  RACDMProof.theorem7_bound' (f := f) hL L0 hL0 x0 k idx i
