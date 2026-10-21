-- Prove2me | solution 1 for LQGMapII.Kolmogorov.chaining_claim
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:14:01.060994+00:00
-- url     : https://prove2.me/submissions/9cd4cf91-cb69-4cc4-89e2-00641d064409

import Mathlib
import Definitions.Def_LQGMapII_Kolmogorov_Setting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory LQGMapII.Kolmogorov
open scoped NNReal ENNReal

namespace ChainAux

def cl (x : ℝ) : ℝ := max 0 (min 1 x)

lemma cl_mem (x : ℝ) : cl x ∈ Set.Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

lemma cl_of_mem {x : ℝ} (h : x ∈ Set.Icc (0:ℝ) 1) : cl x = x := by
  unfold cl
  rw [min_eq_right h.2, max_eq_right h.1]

/-- cube point with (clamped) coordinates `a j / 2^k` -/
noncomputable def P {d : ℕ} (k : ℕ) (a : Fin d → ℕ) : Cube d :=
  ⟨WithLp.toLp 2 (fun j => cl ((a j : ℝ) / 2 ^ k)), fun j => cl_mem _⟩

lemma P_apply {d k : ℕ} (a : Fin d → ℕ) (j : Fin d) (h : a j ≤ 2 ^ k) :
    ((P k a : Cube d) : EuclideanSpace ℝ (Fin d)) j = (a j : ℝ) / 2 ^ k := by
  show cl ((a j : ℝ) / 2 ^ k) = _
  apply cl_of_mem
  have hk : (0:ℝ) < 2 ^ k := by positivity
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hk]
  exact_mod_cast h

lemma P_adj {d k : ℕ} (a : Fin d → ℕ) (ha : ∀ i, a i ≤ 2 ^ k) (j : Fin d) (hj : a j + 1 ≤ 2 ^ k) :
    IsAdjacentPair d k (P k a) (P k (Function.update a j (a j + 1))) := by
  have hb : ∀ i, Function.update a j (a j + 1) i ≤ 2 ^ k := by
    intro i
    by_cases hi : i = j
    · subst hi; simpa using hj
    · rw [Function.update_of_ne hi]; exact ha i
  refine ⟨fun i => ⟨(a i : ℤ), ?_⟩, fun i => ⟨((Function.update a j (a j + 1) i : ℕ) : ℤ), ?_⟩, j, ?_, ?_⟩
  · rw [P_apply a i (ha i)]; simp
  · rw [P_apply _ i (hb i)]; simp
  · intro i hi
    rw [P_apply a i (ha i), P_apply _ i (hb i), Function.update_of_ne hi]
  · rw [P_apply a j (ha j), P_apply _ j (hb j)]
    simp only [Function.update_self]
    have hk : (0:ℝ) < 2 ^ k := by positivity
    push_cast
    rw [← sub_div, show (a j : ℝ) - (a j + 1) = -1 by ring, neg_div, abs_neg, abs_of_pos (by positivity),
      inv_pow, one_div]


lemma rho_pow (γ : ℝ) (k : ℕ) : (((2:ℝ) ^ γ)⁻¹) ^ k = ((2:ℝ) ^ (γ * k))⁻¹ := by
  rw [inv_pow, ← Real.rpow_mul_natCast (by norm_num)]

def S {d : ℕ} (a b : Fin d → ℕ) : ℕ := ∑ j, Int.natAbs ((a j : ℤ) - (b j : ℤ))

lemma S_update {d : ℕ} (a b : Fin d → ℕ) (j : Fin d) (x : ℕ) :
    S (Function.update a j x) b + Int.natAbs ((a j : ℤ) - (b j : ℤ)) =
      S a b + Int.natAbs ((x : ℤ) - (b j : ℤ)) := by
  unfold S
  rw [← Finset.add_sum_erase Finset.univ (fun i => Int.natAbs (((Function.update a j x i : ℕ) : ℤ) - (b i : ℤ)))
      (Finset.mem_univ j),
    ← Finset.add_sum_erase Finset.univ (fun i => Int.natAbs (((a i : ℕ) : ℤ) - (b i : ℤ)))
      (Finset.mem_univ j)]
  have : ∑ i ∈ Finset.univ.erase j, Int.natAbs (((Function.update a j x i : ℕ) : ℤ) - (b i : ℤ)) =
      ∑ i ∈ Finset.univ.erase j, Int.natAbs (((a i : ℕ) : ℤ) - (b i : ℤ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [this]
  simp only [Function.update_self]
  ring

section
variable {d : ℕ} (γ t : ℝ) (f : Cube d → ℝ)
  (H : ∀ (k : ℕ) (u v : Cube d), IsAdjacentPair d k u v → (2 : ℝ) ^ (γ * k) * |f u - f v| ≤ t)

include H in
lemma step_bound (k : ℕ) (a : Fin d → ℕ) (ha : ∀ i, a i ≤ 2 ^ k) (j : Fin d) (hj : a j + 1 ≤ 2 ^ k) :
    |f (P k a) - f (P k (Function.update a j (a j + 1)))| ≤ t * (((2:ℝ) ^ γ)⁻¹) ^ k := by
  have h := H k _ _ (P_adj a ha j hj)
  rw [rho_pow]
  have hp : (0:ℝ) < (2:ℝ) ^ (γ * k) := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]
  exact h

include H in
lemma neighbor (k : ℕ) (a b : Fin d → ℕ) (ha : ∀ i, a i ≤ 2 ^ k) (hb : ∀ i, b i ≤ 2 ^ k) (hne : a ≠ b) :
    ∃ c : Fin d → ℕ, (∀ i, c i ≤ 2 ^ k) ∧
      |f (P k a) - f (P k c)| ≤ t * (((2:ℝ) ^ γ)⁻¹) ^ k ∧ S c b + 1 = S a b := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
  rcases lt_or_gt_of_ne hj with h | h
  · have hj1 : a j + 1 ≤ 2 ^ k := le_trans h (hb j)
    refine ⟨Function.update a j (a j + 1), ?_, step_bound γ t f H k a ha j hj1, ?_⟩
    · intro i
      by_cases hi : i = j
      · subst hi; simpa using hj1
      · rw [Function.update_of_ne hi]; exact ha i
    · have := S_update a b j (a j + 1)
      omega
  · have hj1 : 1 ≤ a j := by omega
    set c := Function.update a j (a j - 1) with hc
    have hcb : ∀ i, c i ≤ 2 ^ k := by
      intro i
      by_cases hi : i = j
      · subst hi; rw [hc, Function.update_self]; exact le_trans (Nat.sub_le _ _) (ha i)
      · rw [hc, Function.update_of_ne hi]; exact ha i
    have hcj : c j + 1 = a j := by simp [hc]; omega
    have hupd : Function.update c j (c j + 1) = a := by
      rw [hcj]; simp [hc]
    refine ⟨c, hcb, ?_, ?_⟩
    · have := step_bound γ t f H k c hcb j (by rw [hcj]; exact ha j)
      rw [hupd, abs_sub_comm] at this
      exact this
    · have := S_update a b j (a j - 1)
      rw [← hc] at this
      omega

include H in
lemma path_bound (k : ℕ) : ∀ (N : ℕ) (a b : Fin d → ℕ), (∀ i, a i ≤ 2 ^ k) → (∀ i, b i ≤ 2 ^ k) →
    S a b = N → |f (P k a) - f (P k b)| ≤ N * (t * (((2:ℝ) ^ γ)⁻¹) ^ k) := by
  intro N
  induction N with
  | zero =>
    intro a b ha hb hS
    have : a = b := by
      funext i
      have h0 : ∀ i ∈ Finset.univ, Int.natAbs ((a i : ℤ) - (b i : ℤ)) = 0 :=
        (Finset.sum_eq_zero_iff.1 hS)
      have := h0 i (Finset.mem_univ i)
      omega
    subst this
    simp
  | succ N ih =>
    intro a b ha hb hS
    have hne : a ≠ b := by
      rintro rfl
      simp [S] at hS
    obtain ⟨c, hc, hstep, hSc⟩ := neighbor γ t f H k a b ha hb hne
    have := ih c b hc hb (by omega)
    calc |f (P k a) - f (P k b)| ≤ |f (P k a) - f (P k c)| + |f (P k c) - f (P k b)| := abs_sub_le _ _ _
      _ ≤ t * (((2:ℝ) ^ γ)⁻¹) ^ k + N * (t * (((2:ℝ) ^ γ)⁻¹) ^ k) := add_le_add hstep this
      _ = ((N + 1 : ℕ) : ℝ) * (t * (((2:ℝ) ^ γ)⁻¹) ^ k) := by push_cast; ring
end


section
variable {d : ℕ} (γ t : ℝ) (f : Cube d → ℝ)
  (H : ∀ (k : ℕ) (u v : Cube d), IsAdjacentPair d k u v → (2 : ℝ) ^ (γ * k) * |f u - f v| ≤ t)

include H in
lemma t_nonneg (j : Fin d) : 0 ≤ t := by
  have hb : ∀ i : Fin d, (fun _ => 0 : Fin d → ℕ) i ≤ 2 ^ 0 := fun i => by simp
  have h := step_bound γ t f H 0 (fun _ => 0) hb j (by simp)
  simp only [pow_zero, mul_one] at h
  exact le_trans (abs_nonneg _) h

lemma P_double (k : ℕ) (c : Fin d → ℕ) :
    P k (fun j => c j / 2) = P (k + 1) (fun j => 2 * (c j / 2)) := by
  apply Subtype.ext
  show WithLp.toLp 2 _ = WithLp.toLp 2 _
  congr 1
  funext j
  congr 1
  push_cast
  rw [pow_succ]
  field_simp

include H in
lemma level_step (ht : 0 ≤ t) (k : ℕ) (c : Fin d → ℕ) (hc : ∀ i, c i ≤ 2 ^ (k + 1)) :
    |f (P (k + 1) c) - f (P k (fun j => c j / 2))| ≤ d * (t * (((2:ℝ) ^ γ)⁻¹) ^ (k + 1)) := by
  rw [P_double]
  have hb : ∀ i, 2 * (c i / 2) ≤ 2 ^ (k + 1) := fun i => le_trans (Nat.mul_div_le _ _) (hc i)
  have h := path_bound γ t f H (k + 1) (S c (fun j => 2 * (c j / 2))) c (fun j => 2 * (c j / 2)) hc hb rfl
  have hS : S c (fun j => 2 * (c j / 2)) ≤ d := by
    unfold S
    calc ∑ j, Int.natAbs ((c j : ℤ) - ((2 * (c j / 2) : ℕ) : ℤ)) ≤ ∑ _j : Fin d, 1 := by
          apply Finset.sum_le_sum
          intro j _
          omega
      _ = d := by simp
  have hτ : 0 ≤ t * (((2:ℝ) ^ γ)⁻¹) ^ (k + 1) := by positivity
  calc _ ≤ _ := h
    _ ≤ d * (t * (((2:ℝ) ^ γ)⁻¹) ^ (k + 1)) := by
        apply mul_le_mul_of_nonneg_right _ hτ
        exact_mod_cast hS

include H in
lemma telescope (ht : 0 ≤ t) (n : ℕ) : ∀ (s : ℕ) (a : Fin d → ℕ), (∀ i, a i ≤ 2 ^ (n + s)) →
    |f (P (n + s) a) - f (P n (fun j => a j / 2 ^ s))| ≤
      d * (t * ∑ i ∈ Finset.range s, (((2:ℝ) ^ γ)⁻¹) ^ (n + i + 1)) := by
  intro s
  induction s with
  | zero =>
    intro a ha
    simp
  | succ s ih =>
    intro a ha
    have h1 := level_step γ t f H ht (n + s) a ha
    have hb : ∀ i, a i / 2 ≤ 2 ^ (n + s) := by
      intro i
      have := ha i
      rw [show n + (s + 1) = (n + s) + 1 by ring, pow_succ] at this
      omega
    have h2 := ih (fun j => a j / 2) hb
    have e : (fun j => a j / 2 / 2 ^ s) = (fun j => a j / 2 ^ (s + 1)) := by
      funext j
      rw [Nat.div_div_eq_div_mul, mul_comm, ← pow_succ]
    rw [e] at h2
    rw [show n + (s + 1) = (n + s) + 1 by ring] at ha ⊢
    rw [Finset.sum_range_succ]
    calc |f (P (n + s + 1) a) - f (P n (fun j => a j / 2 ^ (s + 1)))|
        ≤ |f (P (n + s + 1) a) - f (P (n + s) (fun j => a j / 2))| +
          |f (P (n + s) (fun j => a j / 2)) - f (P n (fun j => a j / 2 ^ (s + 1)))| := abs_sub_le _ _ _
      _ ≤ d * (t * (((2:ℝ) ^ γ)⁻¹) ^ (n + s + 1)) +
          d * (t * ∑ i ∈ Finset.range s, (((2:ℝ) ^ γ)⁻¹) ^ (n + i + 1)) := add_le_add h1 h2
      _ = _ := by ring
end


lemma coord_nat (a b q : ℕ) (hq : 0 < q) (h : Int.natAbs ((a : ℤ) - b) ≤ q) :
    Int.natAbs (((a / q : ℕ) : ℤ) - ((b / q : ℕ) : ℤ)) ≤ 1 := by
  have h1 : a / q ≤ b / q + 1 := by
    calc a / q ≤ (b + q) / q := Nat.div_le_div_right (by omega)
      _ = b / q + 1 := Nat.add_div_right b hq
  have h2 : b / q ≤ a / q + 1 := by
    calc b / q ≤ (a + q) / q := Nat.div_le_div_right (by omega)
      _ = a / q + 1 := Nat.add_div_right a hq
  omega

lemma geom_bound (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (n s : ℕ) :
    ∑ i ∈ Finset.range s, r ^ (n + i + 1) ≤ r ^ (n + 1) / (1 - r) := by
  have h1 : ∀ i, r ^ (n + i + 1) = r ^ (n + 1) * r ^ i := by
    intro i; rw [← pow_add]; congr 1; ring
  simp_rw [h1]
  rw [← Finset.mul_sum]
  have h2 : ∑ i ∈ Finset.range s, r ^ i ≤ (1 - r)⁻¹ := by
    calc ∑ i ∈ Finset.range s, r ^ i ≤ ∑' i, r ^ i :=
          (summable_geometric_of_lt_one hr0.le hr1).sum_le_tsum _ (fun i _ => by positivity)
      _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0.le hr1
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

section
variable {d : ℕ} (γ t : ℝ) (f : Cube d → ℝ)
  (H : ∀ (k : ℕ) (u v : Cube d), IsAdjacentPair d k u v → (2 : ℝ) ^ (γ * k) * |f u - f v| ≤ t)

include H in
lemma mid_bound (ht : 0 ≤ t) (n s : ℕ) (a b : Fin d → ℕ) (ha : ∀ i, a i ≤ 2 ^ (n + s))
    (hb : ∀ i, b i ≤ 2 ^ (n + s)) (hc : ∀ j, Int.natAbs ((a j : ℤ) - b j) ≤ 2 ^ s) :
    |f (P n (fun j => a j / 2 ^ s)) - f (P n (fun j => b j / 2 ^ s))| ≤
      d * (t * (((2:ℝ) ^ γ)⁻¹) ^ n) := by
  have hq : 0 < 2 ^ s := by positivity
  have hdiv : ∀ x : ℕ, x ≤ 2 ^ (n + s) → x / 2 ^ s ≤ 2 ^ n := by
    intro x hx
    calc x / 2 ^ s ≤ 2 ^ (n + s) / 2 ^ s := Nat.div_le_div_right hx
      _ = 2 ^ n := by rw [pow_add, Nat.mul_div_cancel _ hq]
  have h := path_bound γ t f H n (S (fun j => a j / 2 ^ s) (fun j => b j / 2 ^ s))
    (fun j => a j / 2 ^ s) (fun j => b j / 2 ^ s) (fun i => hdiv _ (ha i)) (fun i => hdiv _ (hb i)) rfl
  have hS : S (fun j => a j / 2 ^ s) (fun j => b j / 2 ^ s) ≤ d := by
    unfold S
    calc ∑ j, Int.natAbs (((a j / 2 ^ s : ℕ) : ℤ) - ((b j / 2 ^ s : ℕ) : ℤ)) ≤ ∑ _j : Fin d, 1 :=
          Finset.sum_le_sum fun j _ => coord_nat _ _ _ hq (hc j)
      _ = d := by simp
  have hτ : 0 ≤ t * (((2:ℝ) ^ γ)⁻¹) ^ n := by positivity
  calc _ ≤ _ := h
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hS) hτ

end

lemma dyadic_index {d k : ℕ} (M : ℕ) (hkM : k ≤ M) (u : Cube d) (hu : u ∈ dyadicGrid d k) :
    ∃ a : Fin d → ℕ, (∀ i, a i ≤ 2 ^ M) ∧ u = P M a := by
  choose m hm using hu
  have hk : (0:ℝ) < (2:ℝ) ^ k := by positivity
  have hb : ∀ j, 0 ≤ m j ∧ m j ≤ 2 ^ k := by
    intro j
    have h1 := (u.2 j).1
    have h2 := (u.2 j).2
    rw [hm j] at h1 h2
    constructor
    · have : (0:ℝ) ≤ (m j : ℝ) := by
        rwa [le_div_iff₀ hk, zero_mul] at h1
      exact_mod_cast this
    · have : (m j : ℝ) ≤ (2:ℝ) ^ k := by
        rwa [div_le_one hk] at h2
      exact_mod_cast this
  refine ⟨fun j => (m j).toNat * 2 ^ (M - k), ?_, ?_⟩
  · intro j
    have h3 : (m j).toNat ≤ 2 ^ k := by
      have : ((m j).toNat : ℤ) = m j := Int.toNat_of_nonneg (hb j).1
      have h4 : ((m j).toNat : ℤ) ≤ 2 ^ k := by rw [this]; exact (hb j).2
      exact_mod_cast h4
    calc (m j).toNat * 2 ^ (M - k) ≤ 2 ^ k * 2 ^ (M - k) := Nat.mul_le_mul_right _ h3
      _ = 2 ^ M := by rw [← pow_add]; congr 1; omega
  · have hbd : ∀ j, (m j).toNat * 2 ^ (M - k) ≤ 2 ^ M := by
      intro j
      have h3 : (m j).toNat ≤ 2 ^ k := by
        have : ((m j).toNat : ℤ) = m j := Int.toNat_of_nonneg (hb j).1
        have h4 : ((m j).toNat : ℤ) ≤ 2 ^ k := by rw [this]; exact (hb j).2
        exact_mod_cast h4
      calc (m j).toNat * 2 ^ (M - k) ≤ 2 ^ k * 2 ^ (M - k) := Nat.mul_le_mul_right _ h3
        _ = 2 ^ M := by rw [← pow_add]; congr 1; omega
    apply Subtype.ext
    ext j
    rw [P_apply _ j (hbd j), hm j]
    have h3 : ((m j).toNat : ℝ) = (m j : ℝ) := by
      have : ((m j).toNat : ℤ) = m j := Int.toNat_of_nonneg (hb j).1
      exact_mod_cast this
    push_cast
    rw [h3]
    have : (2:ℝ) ^ M = 2 ^ k * 2 ^ (M - k) := by rw [← pow_add]; congr 1; omega
    rw [this]
    have : (0:ℝ) < 2 ^ (M - k) := by positivity
    field_simp

lemma choose_n (r : ℝ) (hr : 0 < r) : ∃ n : ℕ, (1/2 : ℝ) ^ (n + 1) < r ∧ (r ≤ (1/2 : ℝ) ^ n ∨ n = 0) := by
  rcases le_or_gt r 1 with h | h
  · obtain ⟨n, h1, h2⟩ := exists_nat_pow_near_of_lt_one hr h (by norm_num : (0:ℝ) < 1/2)
      (by norm_num : (1/2:ℝ) < 1)
    exact ⟨n, h1, Or.inl h2⟩
  · exact ⟨0, by norm_num; linarith, Or.inr rfl⟩

end ChainAux

open ChainAux in
theorem solution (d : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    ∃ c₃ : ℝ, 0 < c₃ ∧
      ∀ (f : Cube d → ℝ) (t : ℝ),
        (∀ (k : ℕ) (u v : Cube d), IsAdjacentPair d k u v → (2 : ℝ) ^ (γ * k) * |f u - f v| ≤ t) →
        ∀ u v, u ∈ ⋃ k, dyadicGrid d k → v ∈ ⋃ k, dyadicGrid d k →
          |f u - f v| ≤ c₃ * t * dist u v ^ γ := by
  have h2γ : 1 < (2:ℝ) ^ γ := Real.one_lt_rpow (by norm_num) hγ
  set B : ℝ := (2:ℝ) ^ γ with hB
  have hB0 : 0 < B := by positivity
  set r : ℝ := B⁻¹ with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ h2γ
  have h1r : 0 < 1 - r := by linarith
  have hrB : r * B = 1 := by rw [hr]; field_simp
  refine ⟨(2 * d + 1) * B / (1 - r), by positivity, ?_⟩
  intro f t H u v hu hv
  by_cases huv : u = v
  · subst huv; simp [Real.zero_rpow hγ.ne']
  obtain ⟨j, hj⟩ : ∃ j : Fin d, ((u : Cube d) : EuclideanSpace ℝ (Fin d)) j ≠
      ((v : Cube d) : EuclideanSpace ℝ (Fin d)) j := by
    by_contra h
    push Not at h
    apply huv
    apply Subtype.ext
    ext j
    exact h j
  have ht := t_nonneg γ t f H j
  have hdist : 0 < dist u v := dist_pos.2 huv
  obtain ⟨n, hn1, hn2⟩ := choose_n _ hdist
  have hcoord : ∀ i, |((u : Cube d) : EuclideanSpace ℝ (Fin d)) i - ((v : Cube d) : EuclideanSpace ℝ (Fin d)) i|
      ≤ (1 / 2 : ℝ) ^ n := by
    intro i
    rcases hn2 with h | h
    · refine le_trans ?_ h
      have h1 : ‖((u : Cube d) : EuclideanSpace ℝ (Fin d)) i - ((v : Cube d) : EuclideanSpace ℝ (Fin d)) i‖ ≤
          ‖((u : Cube d) : EuclideanSpace ℝ (Fin d)) - ((v : Cube d) : EuclideanSpace ℝ (Fin d))‖ := by
        have := PiLp.norm_apply_le (((u : Cube d) : EuclideanSpace ℝ (Fin d)) - ((v : Cube d) : EuclideanSpace ℝ (Fin d))) i
        simpa using this
      rw [Real.norm_eq_abs] at h1
      rw [Subtype.dist_eq, dist_eq_norm]
      exact h1
    · subst h
      have a1 := u.2 i
      have a2 := v.2 i
      rw [pow_zero, abs_le]
      constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  obtain ⟨k1, hk1⟩ := Set.mem_iUnion.1 hu
  obtain ⟨k2, hk2⟩ := Set.mem_iUnion.1 hv
  set s := max k1 k2 with hs
  obtain ⟨a, ha, hu'⟩ := dyadic_index (n + s) (by omega : k1 ≤ n + s) u hk1
  obtain ⟨b, hb, hv'⟩ := dyadic_index (n + s) (by omega : k2 ≤ n + s) v hk2
  have hc : ∀ i, Int.natAbs ((a i : ℤ) - (b i : ℤ)) ≤ 2 ^ s := by
    intro i
    have h := hcoord i
    rw [hu', hv', P_apply a i (ha i), P_apply b i (hb i), ← sub_div, abs_div,
      abs_of_pos (by positivity : (0:ℝ) < 2 ^ (n + s)), div_le_iff₀ (by positivity)] at h
    have h' : |((a i : ℝ) - (b i : ℝ))| ≤ (2:ℝ) ^ s := by
      refine le_trans h (le_of_eq ?_)
      rw [one_div, inv_pow, pow_add, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    have h'' : |((a i : ℤ) - (b i : ℤ))| ≤ (2:ℤ) ^ s := by
      have : ((|((a i : ℤ) - (b i : ℤ))| : ℤ) : ℝ) ≤ (((2:ℤ) ^ s : ℤ) : ℝ) := by
        push_cast; exact h'
      exact_mod_cast this
    have : ((Int.natAbs ((a i : ℤ) - (b i : ℤ)) : ℕ) : ℤ) ≤ (2:ℤ) ^ s := by
      rw [Int.natCast_natAbs]; exact h''
    exact_mod_cast this
  have T1 : |f u - f (P n (fun j => a j / 2 ^ s))| ≤
      d * (t * ∑ i ∈ Finset.range s, r ^ (n + i + 1)) := by
    rw [hu']; exact telescope γ t f H ht n s a ha
  have T2 : |f v - f (P n (fun j => b j / 2 ^ s))| ≤
      d * (t * ∑ i ∈ Finset.range s, r ^ (n + i + 1)) := by
    rw [hv']; exact telescope γ t f H ht n s b hb
  have M := mid_bound γ t f H ht n s a b ha hb hc
  have G := geom_bound r hr0 hr1 n s
  have tri : |f u - f v| ≤ |f u - f (P n (fun j => a j / 2 ^ s))| +
      |f (P n (fun j => a j / 2 ^ s)) - f (P n (fun j => b j / 2 ^ s))| +
      |f v - f (P n (fun j => b j / 2 ^ s))| := by
    have e1 := abs_sub_le (f u) (f (P n (fun j => a j / 2 ^ s))) (f v)
    have e2 := abs_sub_le (f (P n (fun j => a j / 2 ^ s))) (f (P n (fun j => b j / 2 ^ s))) (f v)
    have e3 : |f (P n (fun j => b j / 2 ^ s)) - f v| = |f v - f (P n (fun j => b j / 2 ^ s))| :=
      abs_sub_comm _ _
    linarith
  -- lower bound for the distance
  have hpow : r ^ (n + 1) ≤ dist u v ^ γ := by
    have e : ((1 / 2 : ℝ) ^ (n + 1)) ^ γ = r ^ (n + 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
        Real.rpow_natCast, hr, hB, one_div, Real.inv_rpow (by norm_num)]
    rw [← e]
    exact Real.rpow_le_rpow (by positivity) hn1.le hγ.le
  set D := dist u v ^ γ with hD
  have hD0 : 0 ≤ D := by positivity
  set x := r ^ n with hx
  have hx0 : 0 ≤ x := by positivity
  have hrx : r ^ (n + 1) = r * x := by rw [pow_succ, mul_comm]
  rw [hrx] at hpow
  have hxD : x ≤ B * D := by
    calc x = B * (r * x) := by rw [← mul_assoc, mul_comm B r, hrB, one_mul]
      _ ≤ B * D := mul_le_mul_of_nonneg_left hpow hB0.le
  set Gs := ∑ i ∈ Finset.range s, r ^ (n + i + 1) with hGs
  have hG' : Gs * (1 - r) ≤ r * x := by
    rw [← hrx]
    exact (le_div_iff₀ h1r).1 G
  have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg d
  have hdt : 0 ≤ (d:ℝ) * t := mul_nonneg hd0 ht
  have hA : (|f u - f v|) * (1 - r) ≤ (2 * d + 1) * B * t * D := by
    have h1 : |f u - f v| ≤ d * (t * Gs) + d * (t * x) + d * (t * Gs) := by
      have := tri
      linarith
    have h2 : (d * (t * Gs) + d * (t * x) + d * (t * Gs)) * (1 - r) ≤
        2 * (d * t) * (r * x) + d * t * x * (1 - r) := by
      have : (d:ℝ) * t * (Gs * (1 - r)) ≤ d * t * (r * x) := mul_le_mul_of_nonneg_left hG' hdt
      nlinarith
    have h3 : 2 * (d * t) * (r * x) + d * t * x * (1 - r) ≤ 2 * (d * t) * x := by
      nlinarith [mul_nonneg hdt hx0, mul_nonneg (mul_nonneg hdt hx0) hr0.le]
    have h4 : 2 * (d * t) * x ≤ (2 * d + 1) * B * t * D := by
      have : 2 * (d * t) * x ≤ 2 * (d * t) * (B * D) := mul_le_mul_of_nonneg_left hxD (by positivity)
      have h5 : 0 ≤ B * t * D := by positivity
      nlinarith
    calc |f u - f v| * (1 - r) ≤ (d * (t * Gs) + d * (t * x) + d * (t * Gs)) * (1 - r) :=
          mul_le_mul_of_nonneg_right h1 h1r.le
      _ ≤ _ := by linarith
  have : (2 * d + 1) * B / (1 - r) * t * D = ((2 * d + 1) * B * t * D) / (1 - r) := by ring
  rw [this, le_div_iff₀ h1r]
  exact hA
