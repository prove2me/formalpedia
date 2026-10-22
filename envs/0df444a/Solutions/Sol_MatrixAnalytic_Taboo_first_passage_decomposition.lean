-- Prove2me | solution 1 for MatrixAnalytic.Taboo.first_passage_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:26:28.740104+00:00
-- url     : https://prove2.me/submissions/3ec5b143-7f02-489f-a61d-eb2cc251ae05

import Mathlib
import Definitions.Def_MatrixAnalytic_Taboo_Chain
import Definitions.Def_MatrixAnalytic_Taboo_TabooMatrices
open MatrixAnalytic.Taboo

open scoped ENNReal


lemma g70ma_pw_snoc {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) {n : ℕ}
    (ω : Fin (n + 1) → S) (k : S) :
    pathWeightE P (Fin.snoc ω k : Fin (n + 2) → S) = pathWeightE P ω * ennP P (ω (Fin.last n)) k := by
  unfold pathWeightE
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun m _ => ?_
    have h1 : m.castSucc.succ = m.succ.castSucc := by ext; simp
    rw [h1, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · have h1 : (Fin.last n).succ = Fin.last (n+1) := by ext; simp
    rw [h1, Fin.snoc_last, Fin.snoc_castSucc]

lemma g70ma_pw_cons {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) {n : ℕ}
    (ω : Fin (n + 1) → S) (k : S) :
    pathWeightE P (Fin.cons k ω : Fin (n + 2) → S) = ennP P k (ω 0) * pathWeightE P ω := by
  unfold pathWeightE
  rw [Fin.prod_univ_succ]
  congr 1

/-- tsum over paths of length n+2 split as snoc. -/
lemma g70ma_tsum_snoc {S : Type*} [Countable S] {n : ℕ} (f : (Fin (n + 2) → S) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → S, f ω = ∑' ω : Fin (n + 1) → S, ∑' k : S, f (Fin.snoc ω k) := by
  rw [← (Fin.snocEquiv (fun _ => S)).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
  rfl

lemma g70ma_tsum_cons {S : Type*} [Countable S] {n : ℕ} (f : (Fin (n + 2) → S) → ℝ≥0∞) :
    ∑' ω : Fin (n + 2) → S, f ω = ∑' k : S, ∑' ω : Fin (n + 1) → S, f (Fin.cons k ω) := by
  rw [← (Fin.consEquiv (fun _ => S)).tsum_eq, ENNReal.tsum_prod']
  rfl

open Classical in
lemma g70ma_inD_eq {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) (D : Set S) :
    ∀ n : ℕ, ∀ i ∈ D, ∀ j ∈ D,
    (∑' ω : Fin (n + 1) → S,
      if ω 0 = i ∧ ω (Fin.last n) = j ∧ ∀ m : Fin (n + 1), ω m ∈ D then pathWeightE P ω else 0)
      = subPow (ennP P) D n i j := by
  intro n
  induction n with
  | zero =>
    intro i hi j hj
    simp only [subPow]
    rw [← (Equiv.funUnique (Fin 1) S).symm.tsum_eq]
    simp only [Equiv.funUnique_symm_apply]
    by_cases hij : i = j
    · subst hij
      rw [tsum_eq_single i]
      · simp [hi, pathWeightE]
      · intro b hb; simp [Fin.last, hb]
    · rw [if_neg hij]
      apply ENNReal.tsum_eq_zero.mpr
      intro b
      simp only [Fin.last]
      split_ifs with h
      · exact absurd (h.1.symm.trans (by simpa using h.2.1)) hij
      · rfl
  | succ n ih =>
    intro i hi j hj
    rw [g70ma_tsum_snoc]
    simp only [subPow]
    have : ∀ k : D, subPow (ennP P) D n i k * ennP P k j =
        ∑' ω : Fin (n + 1) → S, (if ω 0 = i ∧ ω (Fin.last n) = k ∧ ∀ m : Fin (n + 1), ω m ∈ D
          then pathWeightE P ω else 0) * ennP P k j := by
      intro k
      rw [← ih i hi k k.2, ENNReal.tsum_mul_right]
    simp_rw [this]
    conv_rhs => rw [ENNReal.tsum_comm]
    refine tsum_congr fun (ω : Fin (n+1) → S) => ?_
    have h0 : ∀ k, (Fin.snoc ω k : Fin (n + 2) → S) 0 = ω 0 := fun k => by
      have : (0 : Fin (n + 2)) = (0 : Fin (n+1)).castSucc := rfl
      rw [this, Fin.snoc_castSucc]
    have hall : ∀ k, (∀ m : Fin (n + 2), (Fin.snoc ω k : Fin (n + 2) → S) m ∈ D) ↔
        (∀ m, ω m ∈ D) ∧ k ∈ D := fun k => by
      rw [Fin.forall_fin_succ']; simp
    simp_rw [h0, hall, Fin.snoc_last, g70ma_pw_snoc]
    by_cases hc : ω 0 = i ∧ ∀ m, ω m ∈ D
    · rw [tsum_eq_single j, tsum_eq_single (⟨ω (Fin.last n), hc.2 _⟩ : D)]
      · simp [hc, hj]
      · intro b hb
        rw [if_neg]; · simp
        intro h; exact hb (Subtype.ext h.2.1.symm)
      · intro b hb
        rw [if_neg]; intro h; exact hb h.2.1
    · rw [ENNReal.tsum_eq_zero.mpr, ENNReal.tsum_eq_zero.mpr]
      · intro b; rw [if_neg]; · simp
        intro h; exact hc ⟨h.1, h.2.2⟩
      · intro b; rw [if_neg]; intro h; exact hc ⟨h.1, h.2.2.1⟩

open Classical in
/-- paths of length `N` from `i` to `y` whose states at times `1..N` lie in `A`. -/
noncomputable def g70ma_G {S : Type*} [Countable S] (P : S → S → ℝ) (A : Set S) (N : ℕ) (i y : S) :
    ℝ≥0∞ :=
  ∑' ω : Fin (N + 1) → S,
    if ω 0 = i ∧ ω (Fin.last N) = y ∧ ∀ m : Fin (N + 1), m ≠ 0 → ω m ∈ A then pathWeightE P ω else 0

lemma g70ma_G_zero {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) (A : Set S) (i y : S) :
    g70ma_G P A 0 i y = if i = y then 1 else 0 := by
  classical
  unfold g70ma_G
  rw [← (Equiv.funUnique (Fin 1) S).symm.tsum_eq]
  simp only [Equiv.funUnique_symm_apply]
  by_cases hij : i = y
  · subst hij
    rw [tsum_eq_single i]
    · simp [pathWeightE]
    · intro b hb; simp [Fin.last, hb]
  · rw [if_neg hij]
    apply ENNReal.tsum_eq_zero.mpr
    intro b
    simp only [Fin.last]
    split_ifs with h
    · exact absurd (h.1.symm.trans (by simpa using h.2.1)) hij
    · rfl

open Classical in
/-- endpoint step: paths of length `n+1` from `i` to `j` with interior in `A`. -/
lemma g70ma_endstep {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) (A : Set S) (n : ℕ)
    (i j : S) :
    (∑' ω : Fin (n + 2) → S,
      if ω 0 = i ∧ ω (Fin.last (n + 1)) = j ∧
        ∀ m : Fin (n + 2), m ≠ 0 → m ≠ Fin.last (n + 1) → ω m ∈ A then pathWeightE P ω else 0)
      = ∑' x, g70ma_G P A n i x * ennP P x j := by
  rw [g70ma_tsum_snoc]
  unfold g70ma_G
  simp_rw [← ENNReal.tsum_mul_right]
  conv_rhs => rw [ENNReal.tsum_comm]
  refine tsum_congr fun (ω : Fin (n+1) → S) => ?_
  have h0 : ∀ k, (Fin.snoc ω k : Fin (n + 2) → S) 0 = ω 0 := fun k => by
    have : (0 : Fin (n + 2)) = (0 : Fin (n+1)).castSucc := rfl
    rw [this, Fin.snoc_castSucc]
  have hall : ∀ k, (∀ m : Fin (n + 2), m ≠ 0 → m ≠ Fin.last (n + 1) →
      (Fin.snoc ω k : Fin (n + 2) → S) m ∈ A) ↔ (∀ m : Fin (n + 1), m ≠ 0 → ω m ∈ A) := fun k => by
    rw [Fin.forall_fin_succ']
    simp only [Fin.snoc_castSucc, ne_eq, not_true_eq_false, IsEmpty.forall_iff, imp_true_iff, and_true]
    refine forall_congr' fun m => ?_
    have e1 : (m.castSucc = 0) ↔ m = 0 := by
      constructor
      · intro h; exact Fin.ext (by simpa using congrArg Fin.val h)
      · rintro rfl; rfl
    have e2 : m.castSucc ≠ Fin.last (n+1) := Fin.castSucc_ne_last m
    simp [e1, e2]
  simp_rw [h0, hall, Fin.snoc_last, g70ma_pw_snoc]
  rw [tsum_eq_single j, tsum_eq_single (ω (Fin.last n))]
  · by_cases hc : ω 0 = i ∧ ∀ m : Fin (n + 1), m ≠ 0 → ω m ∈ A
    · simp [hc]
    · rw [if_neg, if_neg, zero_mul]
      · rintro ⟨a, -, b⟩; exact hc ⟨a, b⟩
      · rintro ⟨a, -, b⟩; exact hc ⟨a, b⟩
  · intro b hb; rw [if_neg, zero_mul]; rintro ⟨-, h, -⟩; exact hb h.symm
  · intro b hb; rw [if_neg]; rintro ⟨-, h, -⟩; exact hb h

open Classical in
lemma g70ma_G_succ {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) (A : Set S) (n : ℕ)
    (i y : S) :
    g70ma_G P A (n + 1) i y = if y ∈ A then ∑' x, g70ma_G P A n i x * ennP P x y else 0 := by
  rw [← g70ma_endstep]
  by_cases hy : y ∈ A
  · rw [if_pos hy]
    unfold g70ma_G
    refine tsum_congr fun ω => ?_
    congr 1
    apply propext
    constructor
    · rintro ⟨a, b, c⟩; exact ⟨a, b, fun m h1 _ => c m h1⟩
    · rintro ⟨a, b, c⟩
      refine ⟨a, b, fun m h1 => ?_⟩
      by_cases hm : m = Fin.last (n+1)
      · subst hm; rw [b]; exact hy
      · exact c m h1 hm
  · rw [if_neg hy]
    unfold g70ma_G
    apply ENNReal.tsum_eq_zero.mpr
    intro ω
    rw [if_neg]
    rintro ⟨-, b, c⟩
    exact hy (b ▸ c _ (by simp [Fin.ext_iff]))

lemma g70ma_G_mem {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) (A : Set S) (n : ℕ)
    (i x : S) (hi : i ∈ A) (hx : x ∉ A) : g70ma_G P A n i x = 0 := by
  cases n with
  | zero => rw [g70ma_G_zero, if_neg]; rintro rfl; exact hx hi
  | succ n => rw [g70ma_G_succ, if_neg hx]

lemma g70ma_cauchy_le (g h : ℕ → ℝ≥0∞) (N : ℕ) :
    ∑ n ∈ Finset.range N, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, g p.1 * h p.2 ≤
      (∑ a ∈ Finset.range N, g a) * ∑' b, h b := by
  simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => g a * h b)]
  rw [Finset.range_eq_Ico, Finset.sum_mul]
  have := Finset.sum_Ico_Ico_comm 0 N (fun a n => g a * h (n - a))
  simp only [Nat.succ_eq_add_one] at this ⊢
  simp only [← Finset.range_eq_Ico] at this ⊢
  rw [← this]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.mul_sum]
  gcongr
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  exact ENNReal.sum_le_tsum _

lemma g70ma_claim {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) (T D : Set S)
    (hTD : Disjoint T D) (i : S) (hi : i ∈ D) : ∀ N y,
    g70ma_G P Tᶜ N i y = ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal N,
      ∑' k : D, g70ma_G P Tᶜ ab.1 i k * g70ma_G P {x | x ∉ D ∧ x ∉ T} ab.2 k y := by
  classical
  intro N
  induction N with
  | zero =>
    intro y
    simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, g70ma_G_zero]
    rw [tsum_eq_single ⟨i, hi⟩]
    · simp
    · intro b hb
      have : i ≠ b := fun h => hb (Subtype.ext h.symm)
      simp [this]
  | succ N ih =>
    intro y
    rw [Finset.Nat.sum_antidiagonal_succ']
    have hterm0 : ∑' k : D, g70ma_G P Tᶜ (N+1) i k * g70ma_G P {x | x ∉ D ∧ x ∉ T} 0 k y =
        if y ∈ D then g70ma_G P Tᶜ (N+1) i y else 0 := by
      simp only [g70ma_G_zero]
      split_ifs with hy
      · rw [tsum_eq_single ⟨y, hy⟩]
        · simp
        · intro b hb
          have : (b : S) ≠ y := fun h => hb (Subtype.ext h)
          simp [this]
      · apply ENNReal.tsum_eq_zero.mpr
        intro b
        have : (b : S) ≠ y := fun h => hy (h ▸ b.2)
        simp [this]
    have hterms : ∀ p : ℕ × ℕ, ∑' k : D, g70ma_G P Tᶜ p.1 i k *
        g70ma_G P {x | x ∉ D ∧ x ∉ T} (p.2 + 1) k y =
        if y ∈ {x | x ∉ D ∧ x ∉ T} then ∑' x, (∑' k : D, g70ma_G P Tᶜ p.1 i k *
          g70ma_G P {x | x ∉ D ∧ x ∉ T} p.2 k x) * ennP P x y else 0 := by
      intro p
      simp only [g70ma_G_succ P {x | x ∉ D ∧ x ∉ T} p.2]
      split_ifs
      · simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_comm]
        simp_rw [mul_assoc]
      · simp
    rw [hterm0, Finset.sum_congr rfl (fun p _ => hterms p)]
    by_cases hyT : y ∈ T
    · have hyD : y ∉ D := fun h => Set.disjoint_left.mp hTD hyT h
      rw [g70ma_G_succ, if_neg (by simpa using hyT), if_neg hyD]
      simp [hyT]
    by_cases hyD : y ∈ D
    · rw [if_pos hyD]
      simp [hyD]
    · rw [if_neg hyD, zero_add, g70ma_G_succ, if_pos (by simpa using hyT)]
      have hA : y ∈ {x | x ∉ D ∧ x ∉ T} := ⟨hyD, hyT⟩
      simp only [if_pos hA]
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      refine tsum_congr fun x => ?_
      rw [ih x, Finset.sum_mul]

lemma g70ma_tabooP_eq {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) (T : Set S)
    (N : ℕ) (i y : S) (hy : y ∉ T) : tabooP P T N i y = g70ma_G P Tᶜ N i y := by
  unfold tabooP g70ma_G
  refine tsum_congr fun ω => ?_
  congr 1
  apply propext
  constructor
  · rintro ⟨a, b, c⟩
    refine ⟨a, b, fun m h1 => ?_⟩
    by_cases hm : m = Fin.last N
    · subst hm; rw [b]; exact hy
    · exact c m h1 hm
  · rintro ⟨a, b, c⟩
    exact ⟨a, b, fun m h1 _ => c m h1⟩

lemma g70ma_fp_eq {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) (T : Set S)
    (i j : S) (hj : j ∈ T) :
    firstPassageF P T i j = ∑' n, ∑' x, g70ma_G P Tᶜ n i x * ennP P x j := by
  unfold firstPassageF
  refine tsum_congr fun n => ?_
  rw [← g70ma_endstep]
  refine tsum_congr fun ω => ?_
  congr 1
  apply propext
  simp only [hj, true_and, Set.mem_compl_iff]

lemma g70ma_tabooF_eq {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) (T' D' : Set S)
    (l j : S) (hj : j ∈ D') (hj' : j ∉ T') :
    tabooF P T' D' l j = ∑' n, ∑' x, g70ma_G P {x | x ∉ D' ∧ x ∉ T'} n l x * ennP P x j := by
  unfold tabooF
  refine tsum_congr fun n => ?_
  rw [← g70ma_endstep]
  refine tsum_congr fun ω => ?_
  congr 1
  apply propext
  simp only [hj, hj', true_and, not_false_eq_true, Set.mem_setOf_eq]

lemma g70ma_soj_eq {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) (A : Set S)
    (i k : S) (hi : i ∈ A) : sojournN P A i k = ∑' n, g70ma_G P A n i k := by
  unfold sojournN g70ma_G
  refine tsum_congr fun n => tsum_congr fun ω => ?_
  congr 1
  apply propext
  constructor
  · rintro ⟨a, b, c⟩; exact ⟨a, b, fun m _ => c m⟩
  · rintro ⟨a, b, c⟩
    refine ⟨a, b, fun m => ?_⟩
    by_cases hm : m = 0
    · subst hm; rw [a]; exact hi
    · exact c m hm

lemma g70ma_setA {S' : Type*} (D T : Set S') : {x | x ∉ T ∧ x ∉ D} = {x | x ∉ D ∧ x ∉ T} := by
  ext x; simp only [Set.mem_setOf_eq]; exact and_comm

/-- one step: `G_{n+1}(i,k) = Σ_{a+b=n} Σ_{l∈D} G_a(i,l) F_b(l,k)` for `k ∉ T`. -/
lemma g70ma_step {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) (T D : Set S)
    (hTD : Disjoint T D) (i : S) (hi : i ∈ D) (n : ℕ) (k : S) (hk : k ∉ T) :
    g70ma_G P Tᶜ (n + 1) i k = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ∑' l : D,
      g70ma_G P Tᶜ p.1 i l * ∑' x, g70ma_G P {x | x ∉ D ∧ x ∉ T} p.2 l x * ennP P x k := by
  classical
  rw [g70ma_G_succ, if_pos (show k ∈ Tᶜ from hk)]
  simp_rw [g70ma_claim P T D hTD i hi n, Finset.sum_mul, ← ENNReal.tsum_mul_right]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun l => ?_
  rw [← ENNReal.tsum_mul_left]
  simp_rw [mul_assoc]

lemma g70ma_cauchy (f g : ℕ → ℝ≥0∞) :
    (∑' a, f a) * (∑' b, g b) =
      ∑' n, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, f p.1 * g p.2 := by
  rw [← ENNReal.tsum_mul_right]
  simp_rw [← ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_prod (f := fun a b => f a * g b),
    ← (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun n => ?_
  exact Finset.tsum_subtype (Finset.HasAntidiagonal.antidiagonal n) (fun p => f p.1 * g p.2)

lemma g70ma_form2 {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) (T D : Set S)
    (hTD : Disjoint T D) (i : S) (hi : i ∈ D) (j : S) (hj : j ∈ T) :
    firstPassageF P T i j = ∑' k : D, tabooR P T i k * tabooF P D T k j := by
  have hjD : j ∉ D := fun h => Set.disjoint_left.mp hTD hj h
  have hkT : ∀ k : D, (k : S) ∉ T := fun k h => Set.disjoint_left.mp hTD h k.2
  have hRF : ∀ k : D, tabooR P T i k * tabooF P D T k j =
      (∑' a, g70ma_G P Tᶜ a i k) *
        ∑' b, ∑' x, g70ma_G P {x | x ∉ D ∧ x ∉ T} b k x * ennP P x j := by
    intro k
    unfold tabooR
    rw [g70ma_tabooF_eq P D T k j hj hjD, g70ma_setA]
    simp_rw [g70ma_tabooP_eq P T _ i k (hkT k)]
  rw [tsum_congr hRF]
  simp_rw [g70ma_cauchy]
  classical
  rw [ENNReal.tsum_comm, g70ma_fp_eq P T i j hj]
  refine tsum_congr fun n => ?_
  simp_rw [g70ma_claim P T D hTD i hi n, Finset.sum_mul, ← ENNReal.tsum_mul_right]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable),
    Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun l => ?_
  rw [← ENNReal.tsum_mul_left]
  simp_rw [mul_assoc]

lemma g70ma_L {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) (T D : Set S)
    (hTD : Disjoint T D) (i : S) (hi : i ∈ D) (k : S) (hk : k ∈ D) :
    tabooR P T i k = seriesInv (tabooF P T D) D i k := by
  have hkT : ∀ k, k ∈ D → k ∉ T := fun k hk h => Set.disjoint_left.mp hTD h hk
  have hF : ∀ l k, k ∈ D → tabooF P T D l k =
      ∑' b, ∑' x, g70ma_G P {x | x ∉ D ∧ x ∉ T} b l x * ennP P x k :=
    fun l k hk => g70ma_tabooF_eq P T D l k hk (hkT k hk)
  have hR : tabooR P T i k = ∑' a, g70ma_G P Tᶜ a i k := by
    unfold tabooR; simp_rw [g70ma_tabooP_eq P T _ i k (hkT k hk)]
  rw [hR]
  have Xeq : ∀ k, seriesInv (tabooF P T D) D i k = (if i = k then 1 else 0) +
      ∑' l : D, seriesInv (tabooF P T D) D i l * tabooF P T D l k := by
    intro k
    unfold seriesInv
    rw [tsum_eq_zero_add' ENNReal.summable]
    simp only [subPow]
    congr 1
    simp_rw [← ENNReal.tsum_mul_right]
    exact ENNReal.tsum_comm
  have Req : ∀ k, k ∈ D → ∑' a, g70ma_G P Tᶜ a i k = (if i = k then 1 else 0) +
      ∑' l : D, (∑' a, g70ma_G P Tᶜ a i l) * tabooF P T D l k := by
    intro k hk
    rw [tsum_eq_zero_add' ENNReal.summable, g70ma_G_zero]
    congr 1
    simp_rw [g70ma_step P T D hTD i hi _ k (hkT k hk), hF _ k hk, g70ma_cauchy]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun n => ?_
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply le_antisymm
  · -- R ≤ X
    have key : ∀ N, ∀ k, k ∈ D →
        ∑ a ∈ Finset.range N, g70ma_G P Tᶜ a i k ≤ seriesInv (tabooF P T D) D i k := by
      intro N
      induction N with
      | zero => intro k _; simp
      | succ N ih =>
        intro k hk
        rw [Finset.sum_range_succ', g70ma_G_zero, Xeq k, add_comm]
        gcongr
        simp_rw [g70ma_step P T D hTD i hi _ k (hkT k hk)]
        simp_rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine ENNReal.tsum_le_tsum fun l => ?_
        calc _ ≤ (∑ a ∈ Finset.range N, g70ma_G P Tᶜ a i l) *
              ∑' b, ∑' x, g70ma_G P {x | x ∉ D ∧ x ∉ T} b l x * ennP P x k :=
              g70ma_cauchy_le _ _ N
          _ ≤ _ := by rw [← hF l k hk]; gcongr; exact ih l l.2
    exact ENNReal.tsum_le_of_sum_range_le fun N => key N k hk
  · -- X ≤ R
    have key : ∀ ν, ∀ k, k ∈ D →
        ∑ v ∈ Finset.range ν, subPow (tabooF P T D) D v i k ≤ ∑' a, g70ma_G P Tᶜ a i k := by
      intro ν
      induction ν with
      | zero => intro k _; simp
      | succ ν ih =>
        intro k hk
        rw [Finset.sum_range_succ', Req k hk, add_comm]
        simp only [subPow]
        gcongr
        rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine ENNReal.tsum_le_tsum fun l => ?_
        rw [← Finset.sum_mul]
        gcongr
        exact ih l l.2
    exact ENNReal.tsum_le_of_sum_range_le fun N => key N k hk



/-- Latouche & Ramaswami, Lemma 5.2.4 (p. 117). Under the standing assumptions of Chapter 5 (an
irreducible, aperiodic chain on a countable state space `S` with transition matrix `P`), for any
disjoint subsets `T` and `D`, the matrix `F_{DT}` of first passage probabilities from the states
of `D` to `T` satisfies
(5.25) `F_{DT} = (I − ₜF_{DD})⁻¹ _DF_{DT} = ₜR_{DD} _DF_{DT}`,
where `_DF_{DT}` is `ₜF` with the roles of the sets exchanged (taboo `D`, target `T`); and in
particular, for `D = Tᶜ`,
(5.26) `F_{TᶜT} = N_{Tᶜ} P_{TᶜT}`. -/
theorem solution {S : Type*} [Countable S] [DecidableEq S]
    (P : S → S → ℝ) (hP : IsStochasticC P) (hirr : IrreducibleC P) (hape : AperiodicC P)
    (T D : Set S) (hTD : Disjoint T D) :
    -- (5.25)
    (∀ i ∈ D, ∀ j ∈ T,
      firstPassageF P T i j = ∑' k : D, seriesInv (tabooF P T D) D i k * tabooF P D T k j ∧
      firstPassageF P T i j = ∑' k : D, tabooR P T i k * tabooF P D T k j) ∧
    -- (5.26)
    (∀ i ∉ T, ∀ j ∈ T,
      firstPassageF P T i j = ∑' k : (Tᶜ : Set S), sojournN P Tᶜ i k * ennP P k j) := by
  refine ⟨fun i hi j hj => ?_, fun i hi j hj => ?_⟩
  · refine ⟨?_, g70ma_form2 P T D hTD i hi j hj⟩
    rw [g70ma_form2 P T D hTD i hi j hj]
    refine tsum_congr fun (k : D) => ?_
    rw [g70ma_L P T D hTD i hi k k.2]
  · rw [g70ma_fp_eq P T i j hj]
    have hs : ∀ k : (Tᶜ : Set S), sojournN P Tᶜ i k * ennP P k j =
        ∑' n, g70ma_G P Tᶜ n i k * ennP P k j := fun k => by
      rw [g70ma_soj_eq P Tᶜ i k hi, ENNReal.tsum_mul_right]
    rw [tsum_congr hs]
    conv_rhs => rw [ENNReal.tsum_comm]
    refine tsum_congr fun (n : ℕ) => ?_
    refine (tsum_subtype_eq_of_support_subset (s := (Tᶜ : Set S)) ?_).symm
    intro x hx
    by_contra hxT
    exact hx (by simp [g70ma_G_mem P Tᶜ n i x hi hxT])


