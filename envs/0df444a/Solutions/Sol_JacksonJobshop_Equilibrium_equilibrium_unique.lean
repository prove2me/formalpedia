-- Prove2me | solution 1 for JacksonJobshop.Equilibrium.equilibrium_unique
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T03:37:33.561533+00:00
-- url     : https://prove2.me/submissions/f304816c-c78a-44fa-a34c-a84ce8225008

import Mathlib
import Definitions.Def_JacksonJobshop_Equilibrium_System

set_option autoImplicit false

namespace JacksonUniqueAux

open JacksonJobshop.Equilibrium
open scoped Matrix

variable {N : ℕ}

/-! ### Basic inequalities for `JobshopSystem` -/

lemma lam_nonneg (sys : JobshopSystem N) (K : ℕ) : 0 ≤ sys.lam K := by
  rcases sys.lam_assumption with h | ⟨K₀, h1, h2⟩
  · exact le_of_lt (h K)
  · by_cases hK : K ≤ K₀
    · exact le_of_lt (h1 K hK)
    · rw [h2 K (Nat.lt_of_not_ge hK)]

lemma mu_nonneg (sys : JobshopSystem N) (n : Fin N) (k : ℕ) : 0 ≤ sys.mu n k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [sys.mu_zero]
  · exact le_of_lt (sys.mu_pos n k hk)

lemma r_some_sum_eq (sys : JobshopSystem N) (n : Fin N) :
    sys.r (some n) none + ∑ m, sys.r (some n) (some m) = 1 := by
  have h := sys.r_sum (some n)
  rw [Fintype.sum_option] at h
  exact h

lemma r_some_sum_le_one (sys : JobshopSystem N) (n : Fin N) :
    ∑ m, sys.r (some n) (some m) ≤ 1 := by
  have h := r_some_sum_eq sys n
  have h0 := sys.r_nonneg (some n) none
  linarith

lemma r_none_sum_le_one (sys : JobshopSystem N) :
    ∑ n, sys.r none (some n) ≤ 1 := by
  have h := sys.r_sum none
  rw [Fintype.sum_option] at h
  have h0 := sys.r_nonneg none none
  linarith

lemma one_sub_r_diag (sys : JobshopSystem N) (n : Fin N) :
    1 - sys.r (some n) (some n) =
      sys.r (some n) none + ∑ m ∈ Finset.univ.erase n, sys.r (some n) (some m) := by
  have h := r_some_sum_eq sys n
  have hsplit : ∑ m, sys.r (some n) (some m) =
      sys.r (some n) (some n) + ∑ m ∈ Finset.univ.erase n, sys.r (some n) (some m) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ n)]
  linarith

lemma one_sub_r_diag_nonneg (sys : JobshopSystem N) (n : Fin N) :
    0 ≤ 1 - sys.r (some n) (some n) := by
  rw [one_sub_r_diag]
  exact add_nonneg (sys.r_nonneg _ _) (Finset.sum_nonneg fun m _ => sys.r_nonneg _ _)

/-! ### State update operations -/

def inc (k : Fin N → ℕ) (n : Fin N) : Fin N → ℕ :=
  Function.update k n (k n + 1)

def dec (k : Fin N → ℕ) (n : Fin N) : Fin N → ℕ :=
  Function.update k n (k n - 1)

def move (k : Fin N → ℕ) (n m : Fin N) : Fin N → ℕ :=
  Function.update (Function.update k n (k n - 1)) m (k m + 1)

lemma inc_self (k : Fin N → ℕ) (n : Fin N) : inc k n n = k n + 1 := by
  simp [inc]

lemma inc_of_ne (k : Fin N → ℕ) {n j : Fin N} (h : j ≠ n) : inc k n j = k j := by
  simp [inc, h]

lemma dec_self (k : Fin N → ℕ) (n : Fin N) : dec k n n = k n - 1 := by
  simp [dec]

lemma dec_of_ne (k : Fin N → ℕ) {n j : Fin N} (h : j ≠ n) : dec k n j = k j := by
  simp [dec, h]

lemma move_self_dst (k : Fin N → ℕ) (n m : Fin N) : move k n m m = k m + 1 := by
  simp [move]

lemma move_self_src (k : Fin N → ℕ) {n m : Fin N} (hmn : m ≠ n) : move k n m n = k n - 1 := by
  unfold move
  rw [Function.update_of_ne hmn.symm, Function.update_self]

lemma move_of_ne (k : Fin N → ℕ) {n m j : Fin N} (hjm : j ≠ m) (hjn : j ≠ n) :
    move k n m j = k j := by
  unfold move
  rw [Function.update_of_ne hjm, Function.update_of_ne hjn]

lemma dec_inc (k : Fin N → ℕ) (n : Fin N) : dec (inc k n) n = k := by
  ext j
  by_cases hj : j = n
  · subst hj; simp [dec, inc]
  · simp [dec, inc, hj]

lemma inc_dec (k : Fin N → ℕ) (n : Fin N) (hk : 0 < k n) : inc (dec k n) n = k := by
  ext j
  by_cases hj : j = n
  · subst hj; simp [inc, dec]; omega
  · simp [inc, dec, hj]

lemma inc_injective (n : Fin N) : Function.Injective (fun k : Fin N → ℕ => inc k n) := by
  intro k₁ k₂ h
  have := congrArg (fun k => dec k n) h
  simpa [dec_inc] using this

lemma move_move (k : Fin N → ℕ) {n m : Fin N} (hmn : m ≠ n) (hk : 0 < k n) :
    move (move k n m) m n = k := by
  ext j
  by_cases hjn : j = n
  · subst hjn
    rw [move_self_dst, move_self_src k hmn]
    omega
  · by_cases hjm : j = m
    · subst hjm
      rw [move_self_src _ hmn.symm, move_self_dst]
      omega
    · rw [move_of_ne _ hjn hjm, move_of_ne _ hjm hjn]

lemma S_inc (k : Fin N → ℕ) (n : Fin N) : S (inc k n) = S k + 1 := by
  unfold S inc
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ n),
      ← Finset.add_sum_erase _ k (Finset.mem_univ n)]
  have hsum : ∑ i ∈ Finset.univ.erase n, Function.update k n (k n + 1) i =
      ∑ i ∈ Finset.univ.erase n, k i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _
  rw [Function.update_self, hsum]
  omega

lemma S_dec (k : Fin N → ℕ) (n : Fin N) (hk : 0 < k n) : S (dec k n) + 1 = S k := by
  have h := S_inc (dec k n) n
  rw [inc_dec k n hk] at h
  omega

lemma S_move (k : Fin N → ℕ) {n m : Fin N} (hmn : m ≠ n) (hk : 0 < k n) :
    S (move k n m) = S k := by
  have h1 : move k n m = inc (dec k n) m := by
    ext j
    by_cases hjm : j = m
    · subst hjm; simp [move, inc, dec, hmn]
    · by_cases hjn : j = n
      · subst hjn; simp [move, inc, dec, hmn.symm]
      · simp [move, inc, dec, hjm, hjn]
  rw [h1, S_inc, S_dec k n hk]

/-! ### Routing matrix, Lyapunov weights, and exit reachability -/

def P (sys : JobshopSystem N) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun m n => sys.r (some m) (some n)

lemma one_sub_P_transpose_inj (sys : JobshopSystem N) :
    Function.Injective (1 - (P sys)ᵀ).mulVec := by
  intro v₁ v₂ h
  have h0 : (1 - (P sys)ᵀ).mulVec (v₁ - v₂) = 0 := by
    rw [Matrix.mulVec_sub, h, sub_self]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h0
  have he' : ∀ n, (sys.e + (v₁ - v₂)) n =
      sys.r none (some n) + ∑ m, (sys.e + (v₁ - v₂)) m * sys.r (some m) (some n) := by
    intro n
    have hn := congrFun h0 n
    simp only [Pi.sub_apply, Pi.zero_apply,
      Matrix.mulVec, dotProduct, Matrix.transpose_apply, P, Matrix.of_apply] at hn
    have htr := sys.e_traffic n
    simp only [Pi.add_apply, Pi.sub_apply, add_mul, Finset.sum_add_distrib]
    have hsum : ∑ m, (v₁ m - v₂ m) * sys.r (some m) (some n) =
        ∑ m, sys.r (some m) (some n) * (v₁ m - v₂ m) :=
      Finset.sum_congr rfl fun m _ => mul_comm _ _
    rw [hsum]
    linarith
  have heq := sys.e_unique (sys.e + (v₁ - v₂)) he'
  ext n
  have := congrFun heq n
  simp only [Pi.add_apply, Pi.sub_apply] at this
  linarith

lemma one_sub_P_det_ne_zero (sys : JobshopSystem N) : (1 - P sys).det ≠ 0 := by
  have hT : (1 - (P sys)ᵀ).det ≠ 0 := by
    intro hdet
    obtain ⟨v, hv_ne, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hinj := one_sub_P_transpose_inj sys
    have : v = 0 := hinj (by rw [hv0, Matrix.mulVec_zero])
    exact hv_ne this
  have hEq : (1 - (P sys)ᵀ) = (1 - P sys)ᵀ := by simp
  rw [hEq, Matrix.det_transpose] at hT
  exact hT

lemma exists_lyapunov_weights (sys : JobshopSystem N) :
    ∃ c : Fin N → ℝ, (∀ n, 1 ≤ c n) ∧
      ∀ n, c n - ∑ m, sys.r (some n) (some m) * c m = 1 := by
  have hdet : IsUnit (1 - P sys).det := isUnit_iff_ne_zero.mpr (one_sub_P_det_ne_zero sys)
  let c : Fin N → ℝ := (1 - P sys)⁻¹.mulVec (fun _ => 1)
  have hc_eq : ∀ n, c n - ∑ m, sys.r (some n) (some m) * c m = 1 := by
    intro n
    have hmul : (1 - P sys).mulVec c = fun _ => 1 := by
      simp [c, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hmul
    have hn := congrFun hmul n
    simpa [Matrix.mulVec, dotProduct, P] using hn
  have hc_nonneg : ∀ n, 0 ≤ c n := by
    have hne : (Finset.univ : Finset (Fin N)).Nonempty := by
      exact ⟨⟨0, sys.N_pos⟩, Finset.mem_univ _⟩
    obtain ⟨m₀, _, hm₀⟩ := Finset.exists_min_image Finset.univ c hne
    intro n
    have hmin : c m₀ ≤ c n := hm₀ n (Finset.mem_univ n)
    suffices h0 : 0 ≤ c m₀ by linarith
    by_contra hlt
    push Not at hlt
    have h1 : (∑ m, sys.r (some m₀) (some m)) * c m₀ ≤
        ∑ m, sys.r (some m₀) (some m) * c m := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun m _ =>
        mul_le_mul_of_nonneg_left (hm₀ m (Finset.mem_univ m)) (sys.r_nonneg _ _)
    have h2 : c m₀ ≤ (∑ m, sys.r (some m₀) (some m)) * c m₀ := by
      have hle := r_some_sum_le_one sys m₀
      nlinarith
    have h3 := hc_eq m₀
    linarith
  refine ⟨c, ?_, hc_eq⟩
  intro n
  have hsum : 0 ≤ ∑ m, sys.r (some n) (some m) * c m :=
    Finset.sum_nonneg fun m _ => mul_nonneg (sys.r_nonneg _ _) (hc_nonneg m)
  linarith [hc_eq n]

inductive CanExit (sys : JobshopSystem N) : Fin N → Prop
  | base {m : Fin N} : 0 < sys.r (some m) none → CanExit sys m
  | step {m n : Fin N} : 0 < sys.r (some m) (some n) → CanExit sys n → CanExit sys m

lemma canExit_all (sys : JobshopSystem N) (m : Fin N) : CanExit sys m := by
  classical
  by_contra hnot
  let C : Finset (Fin N) := Finset.univ.filter fun i => ¬ CanExit sys i
  have hmC : m ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ m, hnot⟩
  have hC_exit : ∀ i ∈ C, sys.r (some i) none = 0 := by
    intro i hi
    have hni : ¬ CanExit sys i := (Finset.mem_filter.mp hi).2
    have hnn := sys.r_nonneg (some i) none
    rcases eq_or_lt_of_le hnn with h | h
    · exact h.symm
    · exact absurd (CanExit.base h) hni
  have hC_closed : ∀ i ∈ C, ∀ j ∉ C, sys.r (some i) (some j) = 0 := by
    intro i hi j hj
    have hni : ¬ CanExit sys i := (Finset.mem_filter.mp hi).2
    have hcj : CanExit sys j := by
      by_contra hnj
      exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hnj⟩)
    have hnn := sys.r_nonneg (some i) (some j)
    rcases eq_or_lt_of_le hnn with h | h
    · exact h.symm
    · exact absurd (CanExit.step h hcj) hni
  let Q : Matrix {i // i ∈ C} {i // i ∈ C} ℝ :=
    Matrix.of fun i j => sys.r (some i.1) (some j.1)
  have hQ1 : (1 - Q).mulVec (fun _ => (1 : ℝ)) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    ext i
    simp only [Pi.sub_apply, Pi.zero_apply, Matrix.mulVec, dotProduct, Q, Matrix.of_apply, mul_one]
    have hsum_all := r_some_sum_eq sys i.1
    rw [hC_exit i.1 i.2, zero_add] at hsum_all
    have hsum_C : ∑ j : {j // j ∈ C}, sys.r (some i.1) (some j.1) =
        ∑ j : Fin N, sys.r (some i.1) (some j) := by
      rw [Finset.sum_coe_sort C (fun j => sys.r (some i.1) (some j))]
      apply Finset.sum_subset (Finset.subset_univ C)
      intro j _ hj
      exact hC_closed i.1 i.2 j hj
    rw [hsum_C, hsum_all, sub_self]
  have h1_ne : (fun _ : {i // i ∈ C} => (1 : ℝ)) ≠ 0 := by
    intro h
    have := congrFun h ⟨m, hmC⟩
    norm_num at this
  have hdetQ : (1 - Q).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨fun _ => 1, h1_ne, hQ1⟩
  have hdetQT : (1 - Qᵀ).det = 0 := by
    have : 1 - Qᵀ = (1 - Q)ᵀ := by simp
    rw [this, Matrix.det_transpose, hdetQ]
  obtain ⟨u, hu_ne, hu0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetQT
  let v : Fin N → ℝ := fun i => if h : i ∈ C then u ⟨i, h⟩ else 0
  have hv_ne : v ≠ 0 := by
    intro hv0
    apply hu_ne
    ext ⟨i, hi⟩
    have := congrFun hv0 i
    simpa [v, hi] using this
  have hv0 : (1 - (P sys)ᵀ).mulVec v = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    ext j
    simp only [Pi.sub_apply, Pi.zero_apply,
      Matrix.mulVec, dotProduct, Matrix.transpose_apply, P, Matrix.of_apply]
    by_cases hj : j ∈ C
    · rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hu0
      have huj := congrFun hu0 ⟨j, hj⟩
      simp only [Pi.sub_apply, Pi.zero_apply,
        Matrix.mulVec, dotProduct, Matrix.transpose_apply, Q, Matrix.of_apply] at huj
      have hsum : ∑ i : Fin N, sys.r (some i) (some j) * v i =
          ∑ i : {i // i ∈ C}, sys.r (some i.1) (some j) * u i := by
        have hsub : ∑ i ∈ C, sys.r (some i) (some j) * v i =
            ∑ i : Fin N, sys.r (some i) (some j) * v i := by
          apply Finset.sum_subset (Finset.subset_univ C)
          intro i _ hi
          simp [v, hi]
        rw [← hsub, ← Finset.sum_coe_sort C (fun i => sys.r (some i) (some j) * v i)]
        apply Finset.sum_congr rfl
        intro i _
        simp [v, i.2]
      rw [hsum]
      simpa [v, hj] using huj
    · have hsum : ∑ i : Fin N, sys.r (some i) (some j) * v i = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        by_cases hi : i ∈ C
        · rw [hC_closed i hi j hj, zero_mul]
        · simp [v, hi]
      rw [hsum]
      simp [v, hj]
  have hinj := one_sub_P_transpose_inj sys
  exact hv_ne (hinj (by rw [hv0, Matrix.mulVec_zero]))

/-! ### Reindexing lemmas and unified `tsum` balance identity -/

lemma tsum_arrival_inflow (sys : JobshopSystem N) (f u : (Fin N → ℕ) → ℝ) (n : Fin N) :
    (∑' k, f k * (if 0 < k n then
        sys.lam (S k - 1) * sys.r none (some n) * u (dec k n) else 0)) =
      ∑' k, f (inc k n) * (sys.lam (S k) * sys.r none (some n) * u k) := by
  symm
  have h := Function.Injective.tsum_eq (inc_injective n)
    (f := fun k => f k * (if 0 < k n then
        sys.lam (S k - 1) * sys.r none (some n) * u (dec k n) else 0)) ?_
  · rw [← h]
    congr 1
    ext k
    have hpos : 0 < inc k n n := by rw [inc_self]; omega
    simp [hpos, S_inc, dec_inc]
  · intro k hk
    simp only [Function.mem_support, ne_eq] at hk
    have hpos : 0 < k n := by
      by_contra hnot
      simp only [not_lt, Nat.le_zero] at hnot
      exact hk (by simp [hnot])
    exact ⟨dec k n, inc_dec k n hpos⟩

lemma summable_arrival_inflow_iff (sys : JobshopSystem N) (f u : (Fin N → ℕ) → ℝ) (n : Fin N) :
    Summable (fun k => f k * (if 0 < k n then
        sys.lam (S k - 1) * sys.r none (some n) * u (dec k n) else 0)) ↔
      Summable (fun k => f (inc k n) * (sys.lam (S k) * sys.r none (some n) * u k)) := by
  have h := Function.Injective.summable_iff (inc_injective n)
    (f := fun k => f k * (if 0 < k n then
        sys.lam (S k - 1) * sys.r none (some n) * u (dec k n) else 0)) ?_
  · rw [← h]
    have hEq : (fun k => f (inc k n) * (if 0 < inc k n n then
        sys.lam (S (inc k n) - 1) * sys.r none (some n) * u (dec (inc k n) n) else 0)) =
        fun k => f (inc k n) * (sys.lam (S k) * sys.r none (some n) * u k) := by
      ext k
      have hpos : 0 < inc k n n := by rw [inc_self]; omega
      simp [hpos, S_inc, dec_inc]
    change Summable (fun k => f (inc k n) * (if 0 < inc k n n then
        sys.lam (S (inc k n) - 1) * sys.r none (some n) * u (dec (inc k n) n) else 0)) ↔ _
    rw [hEq]
  · intro k hk
    have h0 : k n = 0 := by
      by_contra hne
      exact hk ⟨dec k n, inc_dec k n (Nat.pos_of_ne_zero hne)⟩
    simp [h0]

lemma tsum_departure_inflow (sys : JobshopSystem N) (f u : (Fin N → ℕ) → ℝ) (n : Fin N) :
    (∑' k, f k * (sys.mu n (k n + 1) * sys.r (some n) none * u (inc k n))) =
      ∑' k, f (dec k n) * (sys.mu n (k n) * sys.r (some n) none * u k) := by
  have h := Function.Injective.tsum_eq (inc_injective n)
    (f := fun k => f (dec k n) * (sys.mu n (k n) * sys.r (some n) none * u k)) ?_
  · rw [← h]
    congr 1
    ext k
    simp [dec_inc, inc_self]
  · intro k hk
    simp only [Function.mem_support, ne_eq] at hk
    have hpos : 0 < k n := by
      by_contra hnot
      simp only [not_lt, Nat.le_zero] at hnot
      exact hk (by simp [hnot, sys.mu_zero])
    exact ⟨dec k n, inc_dec k n hpos⟩

lemma summable_departure_inflow_iff (sys : JobshopSystem N) (f u : (Fin N → ℕ) → ℝ) (n : Fin N) :
    Summable (fun k => f k * (sys.mu n (k n + 1) * sys.r (some n) none * u (inc k n))) ↔
      Summable (fun k => f (dec k n) * (sys.mu n (k n) * sys.r (some n) none * u k)) := by
  have h := Function.Injective.summable_iff (inc_injective n)
    (f := fun k => f (dec k n) * (sys.mu n (k n) * sys.r (some n) none * u k)) ?_
  · rw [← h]
    have hEq : (fun k => f (dec (inc k n) n) * (sys.mu n (inc k n n) * sys.r (some n) none * u (inc k n))) =
        fun k => f k * (sys.mu n (k n + 1) * sys.r (some n) none * u (inc k n)) := by
      ext k; simp [dec_inc, inc_self]
    change _ ↔ Summable (fun k => f (dec (inc k n) n) * (sys.mu n (inc k n n) * sys.r (some n) none * u (inc k n)))
    rw [hEq]
  · intro k hk
    have h0 : k n = 0 := by
      by_contra hne
      exact hk ⟨dec k n, inc_dec k n (Nat.pos_of_ne_zero hne)⟩
    simp [h0, sys.mu_zero]

def moveEquiv {m n : Fin N} (hmn : m ≠ n) :
    {k : Fin N → ℕ // 0 < k m} ≃ {k : Fin N → ℕ // 0 < k n} where
  toFun k := ⟨move k.1 m n, by rw [move_self_dst]; omega⟩
  invFun k := ⟨move k.1 n m, by rw [move_self_dst]; omega⟩
  left_inv k := Subtype.ext (move_move k.1 hmn.symm k.2)
  right_inv k := Subtype.ext (move_move k.1 hmn k.2)

lemma tsum_move_inflow (sys : JobshopSystem N) (f u : (Fin N → ℕ) → ℝ)
    {m n : Fin N} (hmn : m ≠ n) :
    (∑' k, f k * (if m ≠ n ∧ 0 < k m then
        sys.mu n (k n + 1) * sys.r (some n) (some m) * u (move k m n) else 0)) =
      ∑' k, f (move k n m) * (sys.mu n (k n) * sys.r (some n) (some m) * u k) := by
  have hL : (∑' k, f k * (if m ≠ n ∧ 0 < k m then
        sys.mu n (k n + 1) * sys.r (some n) (some m) * u (move k m n) else 0)) =
      ∑' k : {k : Fin N → ℕ // 0 < k m},
        f k.1 * (sys.mu n (k.1 n + 1) * sys.r (some n) (some m) * u (move k.1 m n)) := by
    have hs := tsum_subtype_eq_of_support_subset (s := {k : Fin N → ℕ | 0 < k m})
      (f := fun k => f k * (if m ≠ n ∧ 0 < k m then
        sys.mu n (k n + 1) * sys.r (some n) (some m) * u (move k m n) else 0)) (fun k hk => by
          simp only [Function.mem_support, ne_eq] at hk
          change 0 < k m
          by_contra hnot
          exact hk (by simp [hnot]))
    rw [← hs]
    refine tsum_congr fun ⟨k, hk⟩ => ?_
    have hk' : 0 < k m := hk
    simp [hmn, hk']
  have hR : (∑' k, f (move k n m) * (sys.mu n (k n) * sys.r (some n) (some m) * u k)) =
      ∑' k : {k : Fin N → ℕ // 0 < k n},
        f (move k.1 n m) * (sys.mu n (k.1 n) * sys.r (some n) (some m) * u k.1) := by
    symm
    exact tsum_subtype_eq_of_support_subset (s := {k : Fin N → ℕ | 0 < k n})
      (f := fun k => f (move k n m) * (sys.mu n (k n) * sys.r (some n) (some m) * u k)) fun k hk => by
        simp only [Function.mem_support, ne_eq] at hk
        change 0 < k n
        by_contra hnot
        simp only [not_lt, Nat.le_zero] at hnot
        exact hk (by simp [hnot, sys.mu_zero])
  rw [hL, hR]
  rw [← (moveEquiv hmn).tsum_eq]
  refine tsum_congr fun ⟨k, hk⟩ => ?_
  simp only [moveEquiv, Equiv.coe_fn_mk]
  rw [move_move k hmn.symm hk, move_self_dst]

lemma summable_move_inflow_iff (sys : JobshopSystem N) (f u : (Fin N → ℕ) → ℝ)
    {m n : Fin N} (hmn : m ≠ n) :
    Summable (fun k => f k * (if m ≠ n ∧ 0 < k m then
        sys.mu n (k n + 1) * sys.r (some n) (some m) * u (move k m n) else 0)) ↔
      Summable (fun k => f (move k n m) * (sys.mu n (k n) * sys.r (some n) (some m) * u k)) := by
  have hL : Summable (fun k => f k * (if m ≠ n ∧ 0 < k m then
        sys.mu n (k n + 1) * sys.r (some n) (some m) * u (move k m n) else 0)) ↔
      Summable (fun k : {k : Fin N → ℕ // 0 < k m} =>
        f k.1 * (sys.mu n (k.1 n + 1) * sys.r (some n) (some m) * u (move k.1 m n))) := by
    have hs := summable_subtype_iff_indicator (s := {k : Fin N → ℕ | 0 < k m})
      (f := fun k => f k * (sys.mu n (k n + 1) * sys.r (some n) (some m) * u (move k m n)))
    have hEq : Set.indicator {k : Fin N → ℕ | 0 < k m}
        (fun k => f k * (sys.mu n (k n + 1) * sys.r (some n) (some m) * u (move k m n))) =
        fun k => f k * (if m ≠ n ∧ 0 < k m then
          sys.mu n (k n + 1) * sys.r (some n) (some m) * u (move k m n) else 0) := by
      ext k
      by_cases hk : 0 < k m <;> simp [Set.indicator, hmn, hk]
    rw [hEq] at hs
    exact hs.symm
  have hR : Summable (fun k => f (move k n m) * (sys.mu n (k n) * sys.r (some n) (some m) * u k)) ↔
      Summable (fun k : {k : Fin N → ℕ // 0 < k n} =>
        f (move k.1 n m) * (sys.mu n (k.1 n) * sys.r (some n) (some m) * u k.1)) := by
    have hs := summable_subtype_iff_indicator (s := {k : Fin N → ℕ | 0 < k n})
      (f := fun k => f (move k n m) * (sys.mu n (k n) * sys.r (some n) (some m) * u k))
    have hEq : Set.indicator {k : Fin N → ℕ | 0 < k n}
        (fun k => f (move k n m) * (sys.mu n (k n) * sys.r (some n) (some m) * u k)) =
        fun k => f (move k n m) * (sys.mu n (k n) * sys.r (some n) (some m) * u k) := by
      ext k
      by_cases hk : 0 < k n
      · simp [Set.indicator, hk]
      · have h0 : k n = 0 := by omega
        simp [Set.indicator, h0, sys.mu_zero]
    rw [hEq] at hs
    exact hs.symm
  rw [hL, hR, ← (moveEquiv hmn).summable_iff]
  have hEq : (fun k : {k : Fin N → ℕ // 0 < k m} =>
      f (move (moveEquiv hmn k).1 n m) *
        (sys.mu n ((moveEquiv hmn k).1 n) * sys.r (some n) (some m) * u (moveEquiv hmn k).1)) =
      fun k : {k : Fin N → ℕ // 0 < k m} =>
        f k.1 * (sys.mu n (k.1 n + 1) * sys.r (some n) (some m) * u (move k.1 m n)) := by
    ext ⟨k, hk⟩
    simp only [moveEquiv, Equiv.coe_fn_mk, move_move k hmn.symm hk, move_self_dst]
  change _ ↔ Summable (fun k : {k : Fin N → ℕ // 0 < k m} =>
      f (move (moveEquiv hmn k).1 n m) *
        (sys.mu n ((moveEquiv hmn k).1 n) * sys.r (some n) (some m) * u (moveEquiv hmn k).1))
  rw [hEq]

lemma tsum_mul_balance_eq (sys : JobshopSystem N) (f u : (Fin N → ℕ) → ℝ)
    (hbal : ∀ k, Balance sys u k)
    (hs_arr_out : ∀ n, Summable fun k => f k * (sys.lam (S k) * sys.r none (some n) * u k))
    (hs_arr_in : ∀ n, Summable fun k => f (inc k n) * (sys.lam (S k) * sys.r none (some n) * u k))
    (hs_dep_out : ∀ n, Summable fun k => f k * (sys.mu n (k n) * sys.r (some n) none * u k))
    (hs_dep_in : ∀ n, Summable fun k => f (dec k n) * (sys.mu n (k n) * sys.r (some n) none * u k))
    (hs_mov_out : ∀ m n, m ≠ n →
      Summable fun k => f k * (sys.mu n (k n) * sys.r (some n) (some m) * u k))
    (hs_mov_in : ∀ m n, m ≠ n →
      Summable fun k => f (move k n m) * (sys.mu n (k n) * sys.r (some n) (some m) * u k)) :
    (∑ n, ∑' k, (f (inc k n) - f k) * (sys.lam (S k) * sys.r none (some n) * u k)) +
    (∑ n, ∑' k, (f (dec k n) - f k) * (sys.mu n (k n) * sys.r (some n) none * u k)) +
    (∑ m, ∑ n, if m ≠ n then
      ∑' k, (f (move k n m) - f k) * (sys.mu n (k n) * sys.r (some n) (some m) * u k) else 0) = 0 := by
  have hpoint : ∀ k,
      (∑ n, -(f k * (sys.lam (S k) * sys.r none (some n) * u k))) +
      (∑ n, -(f k * (sys.mu n (k n) * sys.r (some n) none * u k))) +
      (∑ m, ∑ n, if m ≠ n then
          -(f k * (sys.mu n (k n) * sys.r (some n) (some m) * u k)) else 0) +
      (∑ n, f k * (if 0 < k n then
          sys.lam (S k - 1) * sys.r none (some n) * u (dec k n) else 0)) +
      (∑ n, f k * (sys.mu n (k n + 1) * sys.r (some n) none * u (inc k n))) +
      (∑ m, ∑ n, f k * (if m ≠ n ∧ 0 < k m then
          sys.mu n (k n + 1) * sys.r (some n) (some m) * u (move k m n) else 0)) = 0 := by
    intro k
    have hb := congrArg (fun x => f k * x) (hbal k)
    simp only [mul_zero] at hb
    refine Eq.trans ?_ hb.symm
    have hmove_out :
        (∑ m, ∑ n, if m ≠ n then -(f k * (sys.mu n (k n) * sys.r (some n) (some m) * u k)) else 0) =
        ∑ n, -(f k * (sys.mu n (k n) * (∑ m ∈ Finset.univ.erase n, sys.r (some n) (some m)) * u k)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n _
      rw [← Finset.sum_filter]
      have hfilt : Finset.univ.filter (fun m => m ≠ n) = Finset.univ.erase n := by
        ext m; simp
      rw [hfilt, Finset.sum_neg_distrib]
      congr 1
      rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    rw [hmove_out]
    have hdiag : ∀ n,
        -(f k * (sys.mu n (k n) * sys.r (some n) none * u k)) +
        -(f k * (sys.mu n (k n) * (∑ m ∈ Finset.univ.erase n, sys.r (some n) (some m)) * u k)) =
        -(f k * (sys.mu n (k n) * (1 - sys.r (some n) (some n)) * u k)) := by
      intro n
      rw [one_sub_r_diag sys n]
      ring
    have hcomb :
        (∑ n, -(f k * (sys.mu n (k n) * sys.r (some n) none * u k))) +
        (∑ n, -(f k * (sys.mu n (k n) * (∑ m ∈ Finset.univ.erase n, sys.r (some n) (some m)) * u k))) =
        ∑ n, -(f k * (sys.mu n (k n) * (1 - sys.r (some n) (some n)) * u k)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ => hdiag n
    have harr :
        (∑ n, -(f k * (sys.lam (S k) * sys.r none (some n) * u k))) =
        -(f k * (sys.lam (S k) * (∑ n, sys.r none (some n)) * u k)) := by
      rw [Finset.sum_neg_distrib]
      congr 1
      rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    have hmu_sum :
        (∑ n, -(f k * (sys.mu n (k n) * (1 - sys.r (some n) (some n)) * u k))) =
        -(f k * ((∑ n, sys.mu n (k n) * (1 - sys.r (some n) (some n))) * u k)) := by
      rw [Finset.sum_neg_distrib]
      congr 1
      rw [Finset.sum_mul, Finset.mul_sum]
    have h_arr_in_dist :
        f k * (∑ n, if 0 < k n then
          sys.lam (S k - 1) * sys.r none (some n) * u (Function.update k n (k n - 1)) else 0) =
        ∑ n, f k * (if 0 < k n then
          sys.lam (S k - 1) * sys.r none (some n) * u (dec k n) else 0) := by
      rw [Finset.mul_sum]; rfl
    have h_dep_in_dist :
        f k * (∑ n, sys.mu n (k n + 1) * sys.r (some n) none * u (Function.update k n (k n + 1))) =
        ∑ n, f k * (sys.mu n (k n + 1) * sys.r (some n) none * u (inc k n)) := by
      rw [Finset.mul_sum]; rfl
    have h_mov_in_dist :
        f k * (∑ m, ∑ n, if m ≠ n ∧ 0 < k m then
          sys.mu n (k n + 1) * sys.r (some n) (some m) *
            u (Function.update (Function.update k m (k m - 1)) n (k n + 1)) else 0) =
        ∑ m, ∑ n, f k * (if m ≠ n ∧ 0 < k m then
          sys.mu n (k n + 1) * sys.r (some n) (some m) * u (move k m n) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.mul_sum]; rfl
    -- Now combine everything
    have h1 :
        (∑ n, -(f k * (sys.lam (S k) * sys.r none (some n) * u k))) +
        (∑ n, -(f k * (sys.mu n (k n) * sys.r (some n) none * u k))) +
        (∑ n, -(f k * (sys.mu n (k n) * (∑ m ∈ Finset.univ.erase n, sys.r (some n) (some m)) * u k))) =
        f k * (-((sys.lam (S k) * ∑ n, sys.r none (some n)) +
          ∑ n, sys.mu n (k n) * (1 - sys.r (some n) (some n))) * u k) := by
      rw [add_assoc, hcomb, harr, hmu_sum]
      ring
    rw [h1, ← h_arr_in_dist, ← h_dep_in_dist, ← h_mov_in_dist]
    ring
  -- Now take tsum of hpoint
  have htsum0 : (∑' k, (
      (∑ n, -(f k * (sys.lam (S k) * sys.r none (some n) * u k))) +
      (∑ n, -(f k * (sys.mu n (k n) * sys.r (some n) none * u k))) +
      (∑ m, ∑ n, if m ≠ n then
          -(f k * (sys.mu n (k n) * sys.r (some n) (some m) * u k)) else 0) +
      (∑ n, f k * (if 0 < k n then
          sys.lam (S k - 1) * sys.r none (some n) * u (dec k n) else 0)) +
      (∑ n, f k * (sys.mu n (k n + 1) * sys.r (some n) none * u (inc k n))) +
      (∑ m, ∑ n, f k * (if m ≠ n ∧ 0 < k m then
          sys.mu n (k n + 1) * sys.r (some n) (some m) * u (move k m n) else 0)))) = 0 := by
    simp only [hpoint, tsum_zero]
  -- Summability of each of the 6 blocks
  have hs1 : Summable fun k => ∑ n, -(f k * (sys.lam (S k) * sys.r none (some n) * u k)) :=
    summable_sum fun n _ => (hs_arr_out n).neg
  have hs2 : Summable fun k => ∑ n, -(f k * (sys.mu n (k n) * sys.r (some n) none * u k)) :=
    summable_sum fun n _ => (hs_dep_out n).neg
  have hs3 : Summable fun k => ∑ m, ∑ n, if m ≠ n then
      -(f k * (sys.mu n (k n) * sys.r (some n) (some m) * u k)) else 0 := by
    refine summable_sum fun m _ => summable_sum fun n _ => ?_
    by_cases hmn : m ≠ n
    · simpa [hmn] using (hs_mov_out m n hmn).neg
    · simp [hmn, summable_zero]
  have hs4 : Summable fun k => ∑ n, f k * (if 0 < k n then
      sys.lam (S k - 1) * sys.r none (some n) * u (dec k n) else 0) :=
    summable_sum fun n _ => (summable_arrival_inflow_iff sys f u n).mpr (hs_arr_in n)
  have hs5 : Summable fun k => ∑ n, f k * (sys.mu n (k n + 1) * sys.r (some n) none * u (inc k n)) :=
    summable_sum fun n _ => (summable_departure_inflow_iff sys f u n).mpr (hs_dep_in n)
  have hs6 : Summable fun k => ∑ m, ∑ n, f k * (if m ≠ n ∧ 0 < k m then
      sys.mu n (k n + 1) * sys.r (some n) (some m) * u (move k m n) else 0) := by
    refine summable_sum fun m _ => summable_sum fun n _ => ?_
    by_cases hmn : m ≠ n
    · exact (summable_move_inflow_iff sys f u hmn).mpr (hs_mov_in m n hmn)
    · simp [hmn, summable_zero]
  -- Split tsum into 6 tsums
  rw [Summable.tsum_add (hs1.add hs2 |>.add hs3 |>.add hs4 |>.add hs5) hs6,
      Summable.tsum_add (hs1.add hs2 |>.add hs3 |>.add hs4) hs5,
      Summable.tsum_add (hs1.add hs2 |>.add hs3) hs4,
      Summable.tsum_add (hs1.add hs2) hs3,
      Summable.tsum_add hs1 hs2] at htsum0
  -- Commute tsum with finite sums in each block
  rw [Summable.tsum_finsetSum (fun n _ => (hs_arr_out n).neg)] at htsum0
  rw [Summable.tsum_finsetSum (fun n _ => (hs_dep_out n).neg)] at htsum0
  rw [Summable.tsum_finsetSum (fun m _ => summable_sum fun n _ => by
        by_cases hmn : m ≠ n
        · simpa [hmn] using (hs_mov_out m n hmn).neg
        · simp [hmn, summable_zero])] at htsum0
  rw [Summable.tsum_finsetSum (fun n _ => (summable_arrival_inflow_iff sys f u n).mpr (hs_arr_in n))] at htsum0
  rw [Summable.tsum_finsetSum (fun n _ => (summable_departure_inflow_iff sys f u n).mpr (hs_dep_in n))] at htsum0
  rw [Summable.tsum_finsetSum (fun m _ => summable_sum fun n _ => by
        by_cases hmn : m ≠ n
        · exact (summable_move_inflow_iff sys f u hmn).mpr (hs_mov_in m n hmn)
        · simp [hmn, summable_zero])] at htsum0
  -- Rewrite the inflow blocks using our reindexing lemmas and combine with outflow blocks
  have hB1 :
      (∑ n, ∑' k, -(f k * (sys.lam (S k) * sys.r none (some n) * u k))) +
      (∑ n, ∑' k, f k * (if 0 < k n then
          sys.lam (S k - 1) * sys.r none (some n) * u (dec k n) else 0)) =
      ∑ n, ∑' k, (f (inc k n) - f k) * (sys.lam (S k) * sys.r none (some n) * u k) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [tsum_arrival_inflow, tsum_neg, neg_add_eq_sub,
        ← Summable.tsum_sub (hs_arr_in n) (hs_arr_out n)]
    congr 1; ext k; ring
  have hB2 :
      (∑ n, ∑' k, -(f k * (sys.mu n (k n) * sys.r (some n) none * u k))) +
      (∑ n, ∑' k, f k * (sys.mu n (k n + 1) * sys.r (some n) none * u (inc k n))) =
      ∑ n, ∑' k, (f (dec k n) - f k) * (sys.mu n (k n) * sys.r (some n) none * u k) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [tsum_departure_inflow, tsum_neg, neg_add_eq_sub,
        ← Summable.tsum_sub (hs_dep_in n) (hs_dep_out n)]
    congr 1; ext k; ring
  have hB3 :
      (∑ m, ∑' k, ∑ n, if m ≠ n then
          -(f k * (sys.mu n (k n) * sys.r (some n) (some m) * u k)) else 0) +
      (∑ m, ∑' k, ∑ n, f k * (if m ≠ n ∧ 0 < k m then
          sys.mu n (k n + 1) * sys.r (some n) (some m) * u (move k m n) else 0)) =
      ∑ m, ∑ n, if m ≠ n then
          ∑' k, (f (move k n m) - f k) * (sys.mu n (k n) * sys.r (some n) (some m) * u k) else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rw [Summable.tsum_finsetSum (fun n _ => by
          by_cases hmn : m ≠ n
          · simpa [hmn] using (hs_mov_out m n hmn).neg
          · simp [hmn, summable_zero])]
    rw [Summable.tsum_finsetSum (fun n _ => by
          by_cases hmn : m ≠ n
          · exact (summable_move_inflow_iff sys f u hmn).mpr (hs_mov_in m n hmn)
          · simp [hmn, summable_zero])]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hmn : m ≠ n
    · simp only [if_pos hmn]
      rw [tsum_move_inflow sys f u hmn, tsum_neg, neg_add_eq_sub,
          ← Summable.tsum_sub (hs_mov_in m n hmn) (hs_mov_out m n hmn)]
      congr 1; ext k; ring
    · simp [hmn]
  linarith

/-! ### Lyapunov summability of service outflow rates -/

lemma finite_sublevel_S (M : ℕ) : Set.Finite {k : Fin N → ℕ | S k ≤ M} := by
  have hsub : {k : Fin N → ℕ | S k ≤ M} ⊆ Set.pi Set.univ (fun _ : Fin N => Set.Iic M) := by
    intro k hk n _
    have hle : k n ≤ S k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ n)
    exact le_trans hle hk
  exact (Set.Finite.pi fun _ => Set.finite_Iic M).subset hsub

lemma summable_of_finite_support_comp {g : (Fin N → ℕ) → ℝ}
    (hf : (Function.support g).Finite) : Summable g :=
  summable_of_ne_finset_zero (s := hf.toFinset) fun k hk => by
    by_contra hne
    exact hk (hf.mem_toFinset.mpr hne)

lemma summable_mu_mul_eq (sys : JobshopSystem N) {Λ : ℝ} (hΛ : ∀ K, sys.lam K ≤ Λ)
    {q : (Fin N → ℕ) → ℝ} (hq : IsEquilibrium sys q) :
    Summable fun k => (∑ n, sys.mu n (k n)) * q k := by
  classical
  obtain ⟨c, hc1, hceq⟩ := exists_lyapunov_weights sys
  let Φ : (Fin N → ℕ) → ℝ := fun k => ∑ n, c n * (k n : ℝ)
  have hS_le_Φ : ∀ k, (S k : ℝ) ≤ Φ k := by
    intro k
    simp only [S, Φ, Nat.cast_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    nlinarith [hc1 n, Nat.cast_nonneg (α := ℝ) (k n)]
  have hΦ_inc : ∀ k n, Φ k - Φ (inc k n) = -c n := by
    intro k n
    simp only [Φ, inc]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ n),
        ← Finset.add_sum_erase Finset.univ (fun i => c i * (Function.update k n (k n + 1) i : ℝ)) (Finset.mem_univ n)]
    have hsum : ∑ i ∈ Finset.univ.erase n, c i * (Function.update k n (k n + 1) i : ℝ) =
        ∑ i ∈ Finset.univ.erase n, c i * (k i : ℝ) :=
      Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [Function.update_self, hsum]
    push_cast; ring
  have hΦ_dec : ∀ k n, 0 < k n → Φ k - Φ (dec k n) = c n := by
    intro k n hk
    have h := hΦ_inc (dec k n) n
    rw [inc_dec k n hk] at h
    linarith
  have hΦ_move : ∀ k n m, m ≠ n → 0 < k n → Φ k - Φ (move k n m) = c n - c m := by
    intro k n m hmn hk
    have h1 : move k n m = inc (dec k n) m := by
      ext j
      by_cases hjm : j = m
      · subst hjm; simp [move, inc, dec, hmn]
      · by_cases hjn : j = n
        · subst hjn; simp [move, inc, dec, hmn.symm]
        · simp [move, inc, dec, hjm, hjn]
    rw [h1]
    have h2 := hΦ_inc (dec k n) m
    have h3 := hΦ_dec k n hk
    linarith
  have hbound_finset : ∀ s : Finset (Fin N → ℕ),
      ∑ k ∈ s, (∑ n, sys.mu n (k n)) * q k ≤ max Λ 0 * ∑ n, sys.r none (some n) * c n := by
    intro s
    let R : ℝ := ∑ k ∈ s, Φ k + 1
    have hΦ_nonneg : ∀ k, 0 ≤ Φ k := fun k =>
      Finset.sum_nonneg fun n _ => mul_nonneg (by linarith [hc1 n]) (Nat.cast_nonneg _)
    have hs_le_R : ∀ k ∈ s, Φ k ≤ R := by
      intro k hk
      have : Φ k ≤ ∑ j ∈ s, Φ j := Finset.single_le_sum (fun j _ => hΦ_nonneg j) hk
      linarith
    let f : (Fin N → ℕ) → ℝ := fun k => max (R - Φ k) 0
    have hG_fin : Set.Finite {k : Fin N → ℕ | Φ k ≤ R} := by
      refine (finite_sublevel_S (N := N) (Nat.floor R)).subset ?_
      intro k hk
      change S k ≤ Nat.floor R
      have h1 : (S k : ℝ) ≤ R := le_trans (hS_le_Φ k) hk
      exact Nat.le_floor h1
    have hf_supp : (Function.support f).Finite := by
      refine hG_fin.subset ?_
      intro k hk
      simp only [Function.mem_support, ne_eq, f] at hk
      change Φ k ≤ R
      by_contra hgt
      push Not at hgt
      exact hk (max_eq_right (by linarith))
    -- Summability of the 6 terms using finite support
    have hs_arr_out : ∀ n, Summable fun k => f k * (sys.lam (S k) * sys.r none (some n) * q k) := by
      intro n
      refine summable_of_finite_support_comp (hf_supp.subset ?_)
      intro k hk
      simp only [Function.mem_support, ne_eq] at hk ⊢
      intro hf0; exact hk (by simp [hf0])
    have hs_arr_in : ∀ n, Summable fun k => f (inc k n) * (sys.lam (S k) * sys.r none (some n) * q k) := by
      intro n
      have hsub : Function.support (fun k => f (inc k n) * (sys.lam (S k) * sys.r none (some n) * q k)) ⊆
          (fun k => inc k n) ⁻¹' Function.support f := by
        intro k hk
        simp only [Function.mem_support, ne_eq, Set.mem_preimage] at hk ⊢
        intro hf0; exact hk (by simp [hf0])
      exact summable_of_finite_support_comp ((hf_supp.preimage (inc_injective n).injOn).subset hsub)
    have hs_dep_out : ∀ n, Summable fun k => f k * (sys.mu n (k n) * sys.r (some n) none * q k) := by
      intro n
      refine summable_of_finite_support_comp (hf_supp.subset ?_)
      intro k hk
      simp only [Function.mem_support, ne_eq] at hk ⊢
      intro hf0; exact hk (by simp [hf0])
    have hs_dep_in : ∀ n, Summable fun k => f (dec k n) * (sys.mu n (k n) * sys.r (some n) none * q k) := by
      intro n
      rw [← summable_departure_inflow_iff]
      refine summable_of_finite_support_comp (hf_supp.subset ?_)
      intro k hk
      simp only [Function.mem_support, ne_eq] at hk ⊢
      intro hf0; exact hk (by simp [hf0])
    have hs_mov_out : ∀ m n, m ≠ n →
        Summable fun k => f k * (sys.mu n (k n) * sys.r (some n) (some m) * q k) := by
      intro m n _
      refine summable_of_finite_support_comp (hf_supp.subset ?_)
      intro k hk
      simp only [Function.mem_support, ne_eq] at hk ⊢
      intro hf0; exact hk (by simp [hf0])
    have hs_mov_in : ∀ m n, m ≠ n →
        Summable fun k => f (move k n m) * (sys.mu n (k n) * sys.r (some n) (some m) * q k) := by
      intro m n hmn
      rw [← summable_move_inflow_iff sys f q hmn]
      refine summable_of_finite_support_comp (hf_supp.subset ?_)
      intro k hk
      simp only [Function.mem_support, ne_eq] at hk ⊢
      intro hf0; exact hk (by simp [hf0])
    have hId := tsum_mul_balance_eq sys f q hq.2.2
      hs_arr_out hs_arr_in hs_dep_out hs_dep_in hs_mov_out hs_mov_in
    let G : Finset (Fin N → ℕ) := hG_fin.toFinset
    have hsG : s ⊆ G := fun k hk => hG_fin.mem_toFinset.mpr (hs_le_R k hk)
    -- Lower bound each (f k' - f k) by (if k ∈ G then Φ k - Φ k' else 0)
    have hdiff_ge : ∀ k k', (if k ∈ G then Φ k - Φ k' else 0) ≤ f k' - f k := by
      intro k k'
      by_cases hk : k ∈ G
      · simp only [if_pos hk, f]
        have hle : Φ k ≤ R := hG_fin.mem_toFinset.mp hk
        have hfk : max (R - Φ k) 0 = R - Φ k := max_eq_left (by linarith)
        rw [hfk]
        linarith [le_max_left (R - Φ k') 0]
      · simp only [if_neg hk, f]
        have hgt : R < Φ k := by
          have : ¬ Φ k ≤ R := fun hle => hk (hG_fin.mem_toFinset.mpr hle)
          linarith
        have hfk : max (R - Φ k) 0 = 0 := max_eq_right (by linarith)
        rw [hfk, sub_zero]
        exact le_max_right _ _
    -- Compare the tsums with the finite sums over G
    have hsum_arr :
        (∑ n, ∑ k ∈ G, (-c n) * (sys.lam (S k) * sys.r none (some n) * q k)) ≤
        (∑ n, ∑' k, (f (inc k n) - f k) * (sys.lam (S k) * sys.r none (some n) * q k)) := by
      refine Finset.sum_le_sum fun n _ => ?_
      have hts : (∑ k ∈ G, (-c n) * (sys.lam (S k) * sys.r none (some n) * q k)) =
          ∑' k, (if k ∈ G then Φ k - Φ (inc k n) else 0) * (sys.lam (S k) * sys.r none (some n) * q k) := by
        rw [tsum_eq_sum (s := G) (fun k hk => by simp [hk])]
        exact Finset.sum_congr rfl fun k hk => by rw [if_pos hk, hΦ_inc]
      rw [hts]
      refine Summable.tsum_le_tsum (fun k => ?_) ?_ ((hs_arr_in n).sub (hs_arr_out n) |>.congr fun k => by ring)
      · exact mul_le_mul_of_nonneg_right (hdiff_ge k (inc k n))
          (mul_nonneg (mul_nonneg (lam_nonneg sys _) (sys.r_nonneg _ _)) (hq.1 k))
      · exact summable_of_ne_finset_zero (s := G) fun k hk => by simp [hk]
    have hsum_dep :
        (∑ n, ∑ k ∈ G, c n * (sys.mu n (k n) * sys.r (some n) none * q k)) ≤
        (∑ n, ∑' k, (f (dec k n) - f k) * (sys.mu n (k n) * sys.r (some n) none * q k)) := by
      refine Finset.sum_le_sum fun n _ => ?_
      have hts : (∑ k ∈ G, c n * (sys.mu n (k n) * sys.r (some n) none * q k)) =
          ∑' k, (if k ∈ G then Φ k - Φ (dec k n) else 0) * (sys.mu n (k n) * sys.r (some n) none * q k) := by
        rw [tsum_eq_sum (s := G) (fun k hk => by simp [hk])]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [if_pos hk]
        rcases Nat.eq_zero_or_pos (k n) with h0 | hpos
        · simp [h0, sys.mu_zero]
        · rw [hΦ_dec k n hpos]
      rw [hts]
      refine Summable.tsum_le_tsum (fun k => ?_) ?_ ((hs_dep_in n).sub (hs_dep_out n) |>.congr fun k => by ring)
      · exact mul_le_mul_of_nonneg_right (hdiff_ge k (dec k n))
          (mul_nonneg (mul_nonneg (mu_nonneg sys _ _) (sys.r_nonneg _ _)) (hq.1 k))
      · exact summable_of_ne_finset_zero (s := G) fun k hk => by simp [hk]
    have hsum_mov :
        (∑ m, ∑ n, if m ≠ n then
          ∑ k ∈ G, (c n - c m) * (sys.mu n (k n) * sys.r (some n) (some m) * q k) else 0) ≤
        (∑ m, ∑ n, if m ≠ n then
          ∑' k, (f (move k n m) - f k) * (sys.mu n (k n) * sys.r (some n) (some m) * q k) else 0) := by
      refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun n _ => ?_
      by_cases hmn : m ≠ n
      · simp only [if_pos hmn]
        have hts : (∑ k ∈ G, (c n - c m) * (sys.mu n (k n) * sys.r (some n) (some m) * q k)) =
            ∑' k, (if k ∈ G then Φ k - Φ (move k n m) else 0) *
              (sys.mu n (k n) * sys.r (some n) (some m) * q k) := by
          rw [tsum_eq_sum (s := G) (fun k hk => by simp [hk])]
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [if_pos hk]
          rcases Nat.eq_zero_or_pos (k n) with h0 | hpos
          · simp [h0, sys.mu_zero]
          · rw [hΦ_move k n m hmn hpos]
        rw [hts]
        refine Summable.tsum_le_tsum (fun k => ?_) ?_
          ((hs_mov_in m n hmn).sub (hs_mov_out m n hmn) |>.congr fun k => by ring)
        · exact mul_le_mul_of_nonneg_right (hdiff_ge k (move k n m))
            (mul_nonneg (mul_nonneg (mu_nonneg sys _ _) (sys.r_nonneg _ _)) (hq.1 k))
        · exact summable_of_ne_finset_zero (s := G) fun k hk => by simp [hk]
      · simp [hmn]
    -- Combine the three inequalities: LHS ≤ 0
    have hle0 :
        (∑ n, ∑ k ∈ G, (-c n) * (sys.lam (S k) * sys.r none (some n) * q k)) +
        (∑ n, ∑ k ∈ G, c n * (sys.mu n (k n) * sys.r (some n) none * q k)) +
        (∑ m, ∑ n, if m ≠ n then
          ∑ k ∈ G, (c n - c m) * (sys.mu n (k n) * sys.r (some n) (some m) * q k) else 0) ≤ 0 := by
      linarith
    -- Simplify the μ-part of LHS to ∑ k ∈ G, (∑ n, sys.mu n (k n)) * q k
    have hmu_eq :
        (∑ n, ∑ k ∈ G, c n * (sys.mu n (k n) * sys.r (some n) none * q k)) +
        (∑ m, ∑ n, if m ≠ n then
          ∑ k ∈ G, (c n - c m) * (sys.mu n (k n) * sys.r (some n) (some m) * q k) else 0) =
        ∑ k ∈ G, (∑ n, sys.mu n (k n)) * q k := by
      have hmov_swap :
          (∑ m, ∑ n, if m ≠ n then
            ∑ k ∈ G, (c n - c m) * (sys.mu n (k n) * sys.r (some n) (some m) * q k) else 0) =
          ∑ k ∈ G, ∑ n, ∑ m ∈ Finset.univ.erase n,
            (c n - c m) * (sys.mu n (k n) * sys.r (some n) (some m) * q k) := by
        rw [Finset.sum_comm]
        have h1 : (∑ n, ∑ m, if m ≠ n then
            ∑ k ∈ G, (c n - c m) * (sys.mu n (k n) * sys.r (some n) (some m) * q k) else 0) =
            ∑ n, ∑ k ∈ G, ∑ m ∈ Finset.univ.erase n,
              (c n - c m) * (sys.mu n (k n) * sys.r (some n) (some m) * q k) := by
          apply Finset.sum_congr rfl
          intro n _
          rw [← Finset.sum_filter]
          have hfilt : Finset.univ.filter (fun m => m ≠ n) = Finset.univ.erase n := by
            ext m; simp
          rw [hfilt, Finset.sum_comm]
        rw [h1, Finset.sum_comm]
      rw [hmov_swap, Finset.sum_comm (s := Finset.univ) (t := G), ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.sum_add_distrib, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n _
      have hcoeff :
          c n * sys.r (some n) none +
          ∑ m ∈ Finset.univ.erase n, (c n - c m) * sys.r (some n) (some m) = 1 := by
        have hsplit : ∑ m ∈ Finset.univ.erase n, (c n - c m) * sys.r (some n) (some m) =
            c n * (∑ m ∈ Finset.univ.erase n, sys.r (some n) (some m)) -
            ∑ m ∈ Finset.univ.erase n, sys.r (some n) (some m) * c m := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl; intro m _; ring
        rw [hsplit]
        have hr : sys.r (some n) none + ∑ m ∈ Finset.univ.erase n, sys.r (some n) (some m) =
            1 - sys.r (some n) (some n) := (one_sub_r_diag sys n).symm
        have hc : ∑ m, sys.r (some n) (some m) * c m =
            sys.r (some n) (some n) * c n + ∑ m ∈ Finset.univ.erase n, sys.r (some n) (some m) * c m := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ n)]
        have hcn := hceq n
        have hr' : c n * (sys.r (some n) none + ∑ m ∈ Finset.univ.erase n, sys.r (some n) (some m)) =
            c n * (1 - sys.r (some n) (some n)) := congrArg (c n * ·) hr
        linarith
      have hfactor :
          c n * (sys.mu n (k n) * sys.r (some n) none * q k) +
          ∑ m ∈ Finset.univ.erase n, (c n - c m) * (sys.mu n (k n) * sys.r (some n) (some m) * q k) =
          (c n * sys.r (some n) none +
            ∑ m ∈ Finset.univ.erase n, (c n - c m) * sys.r (some n) (some m)) *
            (sys.mu n (k n) * q k) := by
        rw [add_mul, Finset.sum_mul]
        congr 1
        · ring
        · apply Finset.sum_congr rfl; intro m _; ring
      rw [hfactor, hcoeff, one_mul]
    -- Simplify the λ-part of LHS
    have hlam_eq :
        (∑ n, ∑ k ∈ G, (-c n) * (sys.lam (S k) * sys.r none (some n) * q k)) =
        -(∑ k ∈ G, sys.lam (S k) * (∑ n, sys.r none (some n) * c n) * q k) := by
      rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro n _; ring
    have hmu_le_lam :
        ∑ k ∈ G, (∑ n, sys.mu n (k n)) * q k ≤
        ∑ k ∈ G, sys.lam (S k) * (∑ n, sys.r none (some n) * c n) * q k := by
      linarith
    have hrc_nonneg : 0 ≤ ∑ n, sys.r none (some n) * c n :=
      Finset.sum_nonneg fun n _ => mul_nonneg (sys.r_nonneg _ _) (by linarith [hc1 n])
    have hlam_le_bound :
        ∑ k ∈ G, sys.lam (S k) * (∑ n, sys.r none (some n) * c n) * q k ≤
        max Λ 0 * ∑ n, sys.r none (some n) * c n := by
      have h1 : ∑ k ∈ G, sys.lam (S k) * (∑ n, sys.r none (some n) * c n) * q k ≤
          ∑ k ∈ G, (max Λ 0 * ∑ n, sys.r none (some n) * c n) * q k := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hlam_le : sys.lam (S k) ≤ max Λ 0 := le_trans (hΛ (S k)) (le_max_left _ _)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hlam_le hrc_nonneg) (hq.1 k)
      have h2 : ∑ k ∈ G, (max Λ 0 * ∑ n, sys.r none (some n) * c n) * q k =
          (max Λ 0 * ∑ n, sys.r none (some n) * c n) * ∑ k ∈ G, q k := by
        rw [← Finset.mul_sum]
      have h3 : ∑ k ∈ G, q k ≤ 1 := by
        have hsum_le := hq.2.1.summable.sum_le_tsum G (fun k _ => hq.1 k)
        rwa [hq.2.1.tsum_eq] at hsum_le
      have h4 : 0 ≤ max Λ 0 * ∑ n, sys.r none (some n) * c n :=
        mul_nonneg (le_max_right _ _) hrc_nonneg
      nlinarith
    have hs_le_G : ∑ k ∈ s, (∑ n, sys.mu n (k n)) * q k ≤
        ∑ k ∈ G, (∑ n, sys.mu n (k n)) * q k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsG fun k _ _ =>
        mul_nonneg (Finset.sum_nonneg fun n _ => mu_nonneg sys n (k n)) (hq.1 k)
    linarith
  exact summable_of_sum_le
    (fun k => mul_nonneg (Finset.sum_nonneg fun n _ => mu_nonneg sys n (k n)) (hq.1 k))
    hbound_finset

/-! ### Linearity of `Balance`, sign-closure, and reachability of `0` -/

lemma balance_sub (sys : JobshopSystem N) {q q' : (Fin N → ℕ) → ℝ}
    (hq : ∀ k, Balance sys q k) (hq' : ∀ k, Balance sys q' k) (k : Fin N → ℕ) :
    Balance sys (fun x => q x - q' x) k := by
  have h1 := hq k
  have h2 := hq' k
  unfold Balance at h1 h2 ⊢
  have harr :
      (∑ n, if 0 < k n then sys.lam (S k - 1) * sys.r none (some n) *
          (q (Function.update k n (k n - 1)) - q' (Function.update k n (k n - 1))) else 0) =
      (∑ n, if 0 < k n then sys.lam (S k - 1) * sys.r none (some n) *
          q (Function.update k n (k n - 1)) else 0) -
      (∑ n, if 0 < k n then sys.lam (S k - 1) * sys.r none (some n) *
          q' (Function.update k n (k n - 1)) else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    split_ifs <;> ring
  have hdep :
      (∑ n, sys.mu n (k n + 1) * sys.r (some n) none *
          (q (Function.update k n (k n + 1)) - q' (Function.update k n (k n + 1)))) =
      (∑ n, sys.mu n (k n + 1) * sys.r (some n) none * q (Function.update k n (k n + 1))) -
      (∑ n, sys.mu n (k n + 1) * sys.r (some n) none * q' (Function.update k n (k n + 1))) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro n _; ring
  have hmov :
      (∑ m, ∑ n, if m ≠ n ∧ 0 < k m then sys.mu n (k n + 1) * sys.r (some n) (some m) *
          (q (Function.update (Function.update k m (k m - 1)) n (k n + 1)) -
           q' (Function.update (Function.update k m (k m - 1)) n (k n + 1))) else 0) =
      (∑ m, ∑ n, if m ≠ n ∧ 0 < k m then sys.mu n (k n + 1) * sys.r (some n) (some m) *
          q (Function.update (Function.update k m (k m - 1)) n (k n + 1)) else 0) -
      (∑ m, ∑ n, if m ≠ n ∧ 0 < k m then sys.mu n (k n + 1) * sys.r (some n) (some m) *
          q' (Function.update (Function.update k m (k m - 1)) n (k n + 1)) else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro m _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro n _
    split_ifs <;> ring
  rw [harr, hdep, hmov]
  linarith

lemma balance_neg (sys : JobshopSystem N) {d : (Fin N → ℕ) → ℝ}
    (hd : ∀ k, Balance sys d k) (k : Fin N → ℕ) :
    Balance sys (fun x => -d x) k := by
  have h0 : ∀ x, Balance sys (fun _ => (0 : ℝ)) x := by
    intro x; unfold Balance; simp
  have := balance_sub sys h0 hd k
  simpa using this

lemma eq_zero_of_tsum_eq_zero {α : Type*} {g : α → ℝ}
    (hs : Summable g) (hnn : ∀ x, 0 ≤ g x) (ht : ∑' x, g x = 0) (x : α) : g x = 0 := by
  have hle : g x ≤ ∑' y, g y := by
    have h1 := hs.sum_le_tsum {x} (fun y _ => hnn y)
    simpa using h1
  linarith [hnn x]

lemma ind_diff_mul_nonpos (a b : ℝ) :
    ((if 0 < b then (1 : ℝ) else 0) - (if 0 < a then 1 else 0)) * a ≤ 0 := by
  by_cases ha : 0 < a <;> by_cases hb : 0 < b <;> simp [ha, hb] <;> linarith

lemma pos_set_closed (sys : JobshopSystem N) {d : (Fin N → ℕ) → ℝ}
    (hbal : ∀ k, Balance sys d k)
    (hs_lam : Summable fun k => sys.lam (S k) * |d k|)
    (hs_mu : Summable fun k => (∑ n, sys.mu n (k n)) * |d k|) :
    (∀ k n, 0 < d k → 0 < k n → 0 < sys.r (some n) none → 0 < d (dec k n)) ∧
    (∀ k n m, m ≠ n → 0 < d k → 0 < k n → 0 < sys.r (some n) (some m) → 0 < d (move k n m)) := by
  classical
  let f : (Fin N → ℕ) → ℝ := fun k => if 0 < d k then 1 else 0
  have hf_abs : ∀ k, |f k| ≤ 1 := by
    intro k; simp only [f]; split_ifs <;> norm_num
  have hdom_arr : ∀ g : (Fin N → ℕ) → ℝ, (∀ k, |g k| ≤ 1) → ∀ n,
      Summable fun k => g k * (sys.lam (S k) * sys.r none (some n) * d k) := by
    intro g hg n
    refine Summable.of_norm_bounded (g := fun k => sys.lam (S k) * |d k|) hs_lam fun k => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (lam_nonneg sys _), abs_of_nonneg (sys.r_nonneg _ _)]
    have hr : sys.r none (some n) ≤ 1 := by
      have h := sys.r_sum none
      rw [Fintype.sum_option] at h
      have hle : sys.r none (some n) ≤ ∑ m, sys.r none (some m) :=
        Finset.single_le_sum (fun m _ => sys.r_nonneg _ _) (Finset.mem_univ n)
      linarith [sys.r_nonneg none none]
    have h1 : sys.lam (S k) * sys.r none (some n) * |d k| ≤ sys.lam (S k) * |d k| := by
      have h0 : sys.lam (S k) * sys.r none (some n) ≤ sys.lam (S k) * 1 :=
        mul_le_mul_of_nonneg_left hr (lam_nonneg sys _)
      rw [mul_one] at h0
      exact mul_le_mul_of_nonneg_right h0 (abs_nonneg _)
    have h2 : |g k| * (sys.lam (S k) * sys.r none (some n) * |d k|) ≤
        1 * (sys.lam (S k) * |d k|) :=
      mul_le_mul (hg k) h1
        (mul_nonneg (mul_nonneg (lam_nonneg sys _) (sys.r_nonneg _ _)) (abs_nonneg _))
        zero_le_one
    linarith
  have hdom_mu : ∀ g : (Fin N → ℕ) → ℝ, (∀ k, |g k| ≤ 1) → ∀ (n : Fin N) (o : Option (Fin N)),
      Summable fun k => g k * (sys.mu n (k n) * sys.r (some n) o * d k) := by
    intro g hg n o
    refine Summable.of_norm_bounded (g := fun k => (∑ j, sys.mu j (k j)) * |d k|) hs_mu fun k => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (mu_nonneg sys _ _), abs_of_nonneg (sys.r_nonneg _ _)]
    have hr : sys.r (some n) o ≤ 1 := by
      have h := sys.r_sum (some n)
      have hle : sys.r (some n) o ≤ ∑ x, sys.r (some n) x :=
        Finset.single_le_sum (f := fun x => sys.r (some n) x) (fun x _ => sys.r_nonneg _ _) (Finset.mem_univ o)
      linarith
    have hmu : sys.mu n (k n) ≤ ∑ j, sys.mu j (k j) :=
      Finset.single_le_sum (fun j _ => mu_nonneg sys j (k j)) (Finset.mem_univ n)
    have h1 : sys.mu n (k n) * sys.r (some n) o ≤ ∑ j, sys.mu j (k j) := by
      calc sys.mu n (k n) * sys.r (some n) o
          ≤ sys.mu n (k n) * 1 := mul_le_mul_of_nonneg_left hr (mu_nonneg sys _ _)
        _ = sys.mu n (k n) := mul_one _
        _ ≤ ∑ j, sys.mu j (k j) := hmu
    have h2 : |g k| * (sys.mu n (k n) * sys.r (some n) o * |d k|) ≤
        1 * ((∑ j, sys.mu j (k j)) * |d k|) := by
      exact mul_le_mul (hg k)
        (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
        (mul_nonneg (mul_nonneg (mu_nonneg sys _ _) (sys.r_nonneg _ _)) (abs_nonneg _))
        zero_le_one
    linarith
  have hs_arr_out : ∀ n, Summable fun k => f k * (sys.lam (S k) * sys.r none (some n) * d k) :=
    hdom_arr f hf_abs
  have hs_arr_in : ∀ n, Summable fun k => f (inc k n) * (sys.lam (S k) * sys.r none (some n) * d k) :=
    fun n => hdom_arr (fun k => f (inc k n)) (fun k => hf_abs _) n
  have hs_dep_out : ∀ n, Summable fun k => f k * (sys.mu n (k n) * sys.r (some n) none * d k) :=
    fun n => hdom_mu f hf_abs n none
  have hs_dep_in : ∀ n, Summable fun k => f (dec k n) * (sys.mu n (k n) * sys.r (some n) none * d k) :=
    fun n => hdom_mu (fun k => f (dec k n)) (fun k => hf_abs _) n none
  have hs_mov_out : ∀ m n, m ≠ n →
      Summable fun k => f k * (sys.mu n (k n) * sys.r (some n) (some m) * d k) :=
    fun m n _ => hdom_mu f hf_abs n (some m)
  have hs_mov_in : ∀ m n, m ≠ n →
      Summable fun k => f (move k n m) * (sys.mu n (k n) * sys.r (some n) (some m) * d k) :=
    fun m n _ => hdom_mu (fun k => f (move k n m)) (fun k => hf_abs _) n (some m)
  have hId := tsum_mul_balance_eq sys f d hbal
    hs_arr_out hs_arr_in hs_dep_out hs_dep_in hs_mov_out hs_mov_in
  -- Nonpositivity of each term
  have hnp_arr : ∀ n k, (f (inc k n) - f k) * (sys.lam (S k) * sys.r none (some n) * d k) ≤ 0 := by
    intro n k
    have h1 : (f (inc k n) - f k) * (sys.lam (S k) * sys.r none (some n) * d k) =
        ((f (inc k n) - f k) * d k) * (sys.lam (S k) * sys.r none (some n)) := by ring
    rw [h1]
    exact mul_nonpos_of_nonpos_of_nonneg (ind_diff_mul_nonpos (d k) (d (inc k n)))
      (mul_nonneg (lam_nonneg sys _) (sys.r_nonneg _ _))
  have hnp_dep : ∀ n k, (f (dec k n) - f k) * (sys.mu n (k n) * sys.r (some n) none * d k) ≤ 0 := by
    intro n k
    have h1 : (f (dec k n) - f k) * (sys.mu n (k n) * sys.r (some n) none * d k) =
        ((f (dec k n) - f k) * d k) * (sys.mu n (k n) * sys.r (some n) none) := by ring
    rw [h1]
    exact mul_nonpos_of_nonpos_of_nonneg (ind_diff_mul_nonpos (d k) (d (dec k n)))
      (mul_nonneg (mu_nonneg sys _ _) (sys.r_nonneg _ _))
  have hnp_mov : ∀ m n k, (f (move k n m) - f k) * (sys.mu n (k n) * sys.r (some n) (some m) * d k) ≤ 0 := by
    intro m n k
    have h1 : (f (move k n m) - f k) * (sys.mu n (k n) * sys.r (some n) (some m) * d k) =
        ((f (move k n m) - f k) * d k) * (sys.mu n (k n) * sys.r (some n) (some m)) := by ring
    rw [h1]
    exact mul_nonpos_of_nonpos_of_nonneg (ind_diff_mul_nonpos (d k) (d (move k n m)))
      (mul_nonneg (mu_nonneg sys _ _) (sys.r_nonneg _ _))
  have hS1 : (∑ n, ∑' k, (f (inc k n) - f k) * (sys.lam (S k) * sys.r none (some n) * d k)) ≤ 0 :=
    Finset.sum_nonpos fun n _ => tsum_nonpos (hnp_arr n)
  have hS2 : (∑ n, ∑' k, (f (dec k n) - f k) * (sys.mu n (k n) * sys.r (some n) none * d k)) ≤ 0 :=
    Finset.sum_nonpos fun n _ => tsum_nonpos (hnp_dep n)
  have hS3 : (∑ m, ∑ n, if m ≠ n then
      ∑' k, (f (move k n m) - f k) * (sys.mu n (k n) * sys.r (some n) (some m) * d k) else 0) ≤ 0 :=
    Finset.sum_nonpos fun m _ => Finset.sum_nonpos fun n _ => by
      split_ifs with hmn
      · exact tsum_nonpos (hnp_mov m n)
      · exact le_rfl
  have hS2_eq : (∑ n, ∑' k, (f (dec k n) - f k) * (sys.mu n (k n) * sys.r (some n) none * d k)) = 0 := by
    linarith
  have hS3_eq : (∑ m, ∑ n, if m ≠ n then
      ∑' k, (f (move k n m) - f k) * (sys.mu n (k n) * sys.r (some n) (some m) * d k) else 0) = 0 := by
    linarith
  constructor
  · intro k n hdk hkn hr
    have htsum0 : (∑' j, (f (dec j n) - f j) * (sys.mu n (j n) * sys.r (some n) none * d j)) = 0 := by
      have hneg : ∑ n', -(∑' j, (f (dec j n') - f j) * (sys.mu n' (j n') * sys.r (some n') none * d j)) = 0 := by
        rw [Finset.sum_neg_distrib, hS2_eq, neg_zero]
      have hnn : ∀ n' ∈ (Finset.univ : Finset (Fin N)),
          0 ≤ -(∑' j, (f (dec j n') - f j) * (sys.mu n' (j n') * sys.r (some n') none * d j)) :=
        fun n' _ => neg_nonneg.mpr (tsum_nonpos (hnp_dep n'))
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hneg n (Finset.mem_univ n)
      linarith
    have hterm0 : (f (dec k n) - f k) * (sys.mu n (k n) * sys.r (some n) none * d k) = 0 := by
      have hs : Summable fun j => -((f (dec j n) - f j) * (sys.mu n (j n) * sys.r (some n) none * d j)) :=
        (((hs_dep_in n).sub (hs_dep_out n)).congr fun j => by ring).neg
      have hts : (∑' j, -((f (dec j n) - f j) * (sys.mu n (j n) * sys.r (some n) none * d j))) = 0 := by
        rw [tsum_neg, htsum0, neg_zero]
      have h0 := eq_zero_of_tsum_eq_zero hs (fun j => neg_nonneg.mpr (hnp_dep n j)) hts k
      linarith
    have hpos : 0 < sys.mu n (k n) * sys.r (some n) none * d k :=
      mul_pos (mul_pos (sys.mu_pos n (k n) hkn) hr) hdk
    have hfk : f (dec k n) = f k := by
      rcases mul_eq_zero.mp hterm0 with h | h
      · linarith
      · linarith
    simp only [f, if_pos hdk] at hfk
    by_contra hnot
    simp only [if_neg hnot] at hfk
    norm_num at hfk
  · intro k n m hmn hdk hkn hr
    have htsum0 : (∑' j, (f (move j n m) - f j) * (sys.mu n (j n) * sys.r (some n) (some m) * d j)) = 0 := by
      have hneg1 : ∑ m', -(∑ n', if m' ≠ n' then
          ∑' j, (f (move j n' m') - f j) * (sys.mu n' (j n') * sys.r (some n') (some m') * d j) else 0) = 0 := by
        rw [Finset.sum_neg_distrib, hS3_eq, neg_zero]
      have hnn1 : ∀ m' ∈ (Finset.univ : Finset (Fin N)),
          0 ≤ -(∑ n', if m' ≠ n' then
            ∑' j, (f (move j n' m') - f j) * (sys.mu n' (j n') * sys.r (some n') (some m') * d j) else 0) :=
        fun m' _ => neg_nonneg.mpr (Finset.sum_nonpos fun n' _ => by
          split_ifs with h'; exact tsum_nonpos (hnp_mov m' n'); exact le_rfl)
      have hm0 : (∑ n', if m ≠ n' then
          ∑' j, (f (move j n' m) - f j) * (sys.mu n' (j n') * sys.r (some n') (some m) * d j) else 0) = 0 := by
        have := (Finset.sum_eq_zero_iff_of_nonneg hnn1).mp hneg1 m (Finset.mem_univ m)
        linarith
      have hneg2 : ∑ n', -(if m ≠ n' then
          ∑' j, (f (move j n' m) - f j) * (sys.mu n' (j n') * sys.r (some n') (some m) * d j) else 0) = 0 := by
        rw [Finset.sum_neg_distrib, hm0, neg_zero]
      have hnn2 : ∀ n' ∈ (Finset.univ : Finset (Fin N)),
          0 ≤ -(if m ≠ n' then
            ∑' j, (f (move j n' m) - f j) * (sys.mu n' (j n') * sys.r (some n') (some m) * d j) else 0) :=
        fun n' _ => neg_nonneg.mpr (by
          split_ifs with h'; exact tsum_nonpos (hnp_mov m n'); exact le_rfl)
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn2).mp hneg2 n (Finset.mem_univ n)
      simp only [if_pos hmn] at this
      linarith
    have hterm0 : (f (move k n m) - f k) * (sys.mu n (k n) * sys.r (some n) (some m) * d k) = 0 := by
      have hs : Summable fun j => -((f (move j n m) - f j) * (sys.mu n (j n) * sys.r (some n) (some m) * d j)) :=
        (((hs_mov_in m n hmn).sub (hs_mov_out m n hmn)).congr fun j => by ring).neg
      have hts : (∑' j, -((f (move j n m) - f j) * (sys.mu n (j n) * sys.r (some n) (some m) * d j))) = 0 := by
        rw [tsum_neg, htsum0, neg_zero]
      have h0 := eq_zero_of_tsum_eq_zero hs (fun j => neg_nonneg.mpr (hnp_mov m n j)) hts k
      linarith
    have hpos : 0 < sys.mu n (k n) * sys.r (some n) (some m) * d k :=
      mul_pos (mul_pos (sys.mu_pos n (k n) hkn) hr) hdk
    have hfk : f (move k n m) = f k := by
      rcases mul_eq_zero.mp hterm0 with h | h
      · linarith
      · linarith
    simp only [f, if_pos hdk] at hfk
    by_contra hnot
    simp only [if_neg hnot] at hfk
    norm_num at hfk

lemma closed_imp_zero (sys : JobshopSystem N) {P : (Fin N → ℕ) → Prop}
    (hdec : ∀ k n, P k → 0 < k n → 0 < sys.r (some n) none → P (dec k n))
    (hmov : ∀ k n m, m ≠ n → P k → 0 < k n → 0 < sys.r (some n) (some m) → P (move k n m)) :
    ∀ M : ℕ, ∀ k : Fin N → ℕ, S k = M → P k → P 0 := by
  intro M
  induction M with
  | zero =>
    intro k hS hPk
    have hk0 : k = 0 := by
      ext n
      have hle : k n ≤ S k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ n)
      rw [hS] at hle
      exact Nat.le_zero.mp hle
    rwa [← hk0]
  | succ M ih =>
    intro k hS hPk
    have hex : ∃ n : Fin N, 0 < k n := by
      by_contra h
      push Not at h
      have : S k = 0 := Finset.sum_eq_zero fun n _ => Nat.le_zero.mp (h n)
      omega
    obtain ⟨n, hkn⟩ := hex
    have hce := canExit_all sys n
    have hstep : ∀ n', CanExit sys n' → ∀ k, S k = M + 1 → 0 < k n' → P k → P 0 := by
      intro n' hce'
      induction hce' with
      | base hr =>
        rename_i m'
        intro k hS hkm' hPk
        have hSdec : S (dec k m') = M := by
          have := S_dec k m' hkm'; omega
        exact ih (dec k m') hSdec (hdec k m' hPk hkm' hr)
      | @step a b hr _ ihce =>
        intro k hS hka hPk
        by_cases hab : b = a
        · subst hab
          exact ihce k hS hka hPk
        · have hPmov : P (move k a b) := hmov k a b hab hPk hka hr
          have hSmov : S (move k a b) = M + 1 := by rw [S_move k hab hka, hS]
          have hkb : 0 < move k a b b := by rw [move_self_dst]; omega
          exact ihce (move k a b) hSmov hkb hPmov
    exact hstep n hce k hS hkn hPk

end JacksonUniqueAux

open JacksonJobshop.Equilibrium in
theorem solution {N : ℕ} (sys : JobshopSystem N)
    (hbdd : ∃ Λ : ℝ, ∀ K, sys.lam K ≤ Λ) :
    ∀ q q' : (Fin N → ℕ) → ℝ, IsEquilibrium sys q → IsEquilibrium sys q' → q = q' := by
  intro q q' hq hq'
  obtain ⟨Λ, hΛ⟩ := hbdd
  have hmu_q := JacksonUniqueAux.summable_mu_mul_eq sys hΛ hq
  have hmu_q' := JacksonUniqueAux.summable_mu_mul_eq sys hΛ hq'
  let d : (Fin N → ℕ) → ℝ := fun k => q k - q' k
  have hd_sum : HasSum d 0 := by
    have := hq.2.1.sub hq'.2.1
    simpa [d] using this
  have hd_bal : ∀ k, Balance sys d k := JacksonUniqueAux.balance_sub sys hq.2.2 hq'.2.2
  have habs_le : ∀ k, |d k| ≤ q k + q' k := by
    intro k
    have := abs_sub (q k) (q' k)
    rwa [abs_of_nonneg (hq.1 k), abs_of_nonneg (hq'.1 k)] at this
  have hs_lam : Summable fun k => sys.lam (S k) * |d k| := by
    have hdom : Summable fun k => max Λ 0 * (q k + q' k) :=
      (hq.2.1.summable.add hq'.2.1.summable).mul_left (max Λ 0)
    refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg (JacksonUniqueAux.lam_nonneg sys _) (abs_nonneg _))
      (fun k => ?_) hdom
    have h1 : sys.lam (S k) ≤ max Λ 0 := le_trans (hΛ (S k)) (le_max_left _ _)
    exact mul_le_mul h1 (habs_le k) (abs_nonneg _) (le_max_right _ _)
  have hs_mu : Summable fun k => (∑ n, sys.mu n (k n)) * |d k| := by
    have hdom : Summable fun k => (∑ n, sys.mu n (k n)) * q k + (∑ n, sys.mu n (k n)) * q' k :=
      hmu_q.add hmu_q'
    refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg (Finset.sum_nonneg fun n _ => JacksonUniqueAux.mu_nonneg sys n (k n)) (abs_nonneg _))
      (fun k => ?_) hdom
    have hnn : 0 ≤ ∑ n, sys.mu n (k n) :=
      Finset.sum_nonneg fun n _ => JacksonUniqueAux.mu_nonneg sys n (k n)
    have h1 := mul_le_mul_of_nonneg_left (habs_le k) hnn
    linarith
  have hpos_imp : ∀ k, 0 < d k → 0 < d 0 := by
    intro k hdk
    obtain ⟨hdec, hmov⟩ := JacksonUniqueAux.pos_set_closed sys hd_bal hs_lam hs_mu
    exact JacksonUniqueAux.closed_imp_zero sys hdec hmov (S k) k rfl hdk
  have hneg_imp : ∀ k, d k < 0 → d 0 < 0 := by
    intro k hdk
    have hbal_neg : ∀ x, Balance sys (fun j => -d j) x := JacksonUniqueAux.balance_neg sys hd_bal
    have hs_lam_neg : Summable fun x => sys.lam (S x) * |-d x| := by simpa [abs_neg] using hs_lam
    have hs_mu_neg : Summable fun x => (∑ n, sys.mu n (x n)) * |-d x| := by simpa [abs_neg] using hs_mu
    obtain ⟨hdec, hmov⟩ := JacksonUniqueAux.pos_set_closed sys hbal_neg hs_lam_neg hs_mu_neg
    have h0 := JacksonUniqueAux.closed_imp_zero sys hdec hmov (S k) k rfl (neg_pos.mpr hdk)
    linarith
  have hd_zero : ∀ k, d k = 0 := by
    by_cases h0 : 0 ≤ d 0
    · have hnonneg : ∀ k, 0 ≤ d k := by
        intro k
        by_contra hlt
        push Not at hlt
        linarith [hneg_imp k hlt]
      exact fun k => JacksonUniqueAux.eq_zero_of_tsum_eq_zero hd_sum.summable hnonneg hd_sum.tsum_eq k
    · push Not at h0
      have hnonpos : ∀ k, d k ≤ 0 := by
        intro k
        by_contra hgt
        push Not at hgt
        linarith [hpos_imp k hgt]
      have hneg_sum : HasSum (fun k => -d k) 0 := by simpa using hd_sum.neg
      have hneg_zero := fun k =>
        JacksonUniqueAux.eq_zero_of_tsum_eq_zero hneg_sum.summable
          (fun j => neg_nonneg.mpr (hnonpos j)) hneg_sum.tsum_eq k
      intro k
      linarith [hneg_zero k]
  ext k
  have := hd_zero k
  dsimp only [d] at this
  linarith

