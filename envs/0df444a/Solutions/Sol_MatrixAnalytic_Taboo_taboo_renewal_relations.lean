-- Prove2me | solution 1 for MatrixAnalytic.Taboo.taboo_renewal_relations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:44:45.334805+00:00
-- url     : https://prove2.me/submissions/30e104ec-8749-4843-b5b7-44691520eb0b

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


lemma g70ma_G_cons {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) (A : Set S) (n : ℕ)
    (x y : S) : g70ma_G P A (n + 1) x y = ∑' z : A, ennP P x z * g70ma_G P A n z y := by
  classical
  induction n generalizing y with
  | zero =>
    rw [g70ma_G_succ]
    simp only [g70ma_G_zero]
    split_ifs with hy
    · rw [tsum_eq_single x, tsum_eq_single ⟨y, hy⟩]
      · simp
      · intro b hb
        have : (b : S) ≠ y := fun h => hb (Subtype.ext h)
        simp [this]
      · intro b hb; simp [Ne.symm hb]
    · symm; apply ENNReal.tsum_eq_zero.mpr
      intro b
      have : (b : S) ≠ y := fun h => hy (h ▸ b.2)
      simp [this]
  | succ n ih =>
    rw [g70ma_G_succ]
    simp_rw [ih]
    simp only [g70ma_G_succ P A n]
    by_cases hy : y ∈ A
    · simp only [hy, if_true]
      simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      simp_rw [mul_assoc]
    · simp [hy]

lemma g70ma_G_cons_le {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) (A : Set S) (n : ℕ)
    (x z y : S) (hz : z ∈ A) : ennP P x z * g70ma_G P A n z y ≤ g70ma_G P A (n + 1) x y := by
  rw [g70ma_G_cons]
  exact ENNReal.le_tsum (f := fun z : A => ennP P x z * g70ma_G P A n z y) ⟨z, hz⟩

lemma g70ma_stepPow_nonneg {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ)
    (hP0 : ∀ x y, 0 ≤ P x y) : ∀ t x y, 0 ≤ stepPow P t x y := by
  intro t
  induction t with
  | zero => intro x y; simp only [stepPow]; split_ifs <;> norm_num
  | succ t ih => intro x y; simp only [stepPow]; exact tsum_nonneg fun z => mul_nonneg (ih _ _) (hP0 _ _)

lemma g70ma_stepPow_pos {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ)
    (hP0 : ∀ x y, 0 ≤ P x y) : ∀ t x y, 0 < stepPow P t x y → g70ma_G P Set.univ t x y ≠ 0 := by
  intro t
  induction t with
  | zero =>
    intro x y h
    simp only [stepPow] at h
    rw [g70ma_G_zero]
    split_ifs at h with hxy
    · simp [hxy]
    · norm_num at h
  | succ t ih =>
    intro x y h
    simp only [stepPow] at h
    obtain ⟨z, hz⟩ : ∃ z, stepPow P t x z * P z y ≠ 0 := by
      by_contra hc
      push Not at hc
      rw [tsum_congr hc, tsum_zero] at h
      exact lt_irrefl _ h
    have h1 : 0 < stepPow P t x z :=
      lt_of_le_of_ne (g70ma_stepPow_nonneg P hP0 t x z) (Ne.symm (left_ne_zero_of_mul hz))
    have h2 : 0 < P z y := lt_of_le_of_ne (hP0 z y) (Ne.symm (right_ne_zero_of_mul hz))
    rw [g70ma_G_succ, if_pos (Set.mem_univ y)]
    apply ne_of_gt
    calc (0 : ℝ≥0∞) < g70ma_G P Set.univ t x z * ennP P z y :=
          ENNReal.mul_pos (ih x z h1) (by simp [ennP, h2])
      _ ≤ _ := ENNReal.le_tsum z

open Classical in
/-- total mass: `Σ_{n<N} Σ_w G_n(i,w) out(w) + Σ_w G_N(i,w) = 1`. -/
lemma g70ma_mass {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) (hP : IsStochasticC P)
    (A : Set S) (i : S) : ∀ N,
    ∑ n ∈ Finset.range N, ∑' w, g70ma_G P A n i w * ∑' y, (if y ∈ A then 0 else ennP P w y)
      + ∑' w, g70ma_G P A N i w = 1 := by
  classical
  have hrow : ∀ w, ∑' y, ennP P w y = 1 := by
    intro w
    unfold ennP
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun y => hP.1 w y) (hP.2 w).summable, (hP.2 w).tsum_eq]
    simp
  have hsplit : ∀ w, ∑' y, (if y ∈ A then 0 else ennP P w y) +
      ∑' y, (if y ∈ A then ennP P w y else 0) = 1 := by
    intro w
    rw [← ENNReal.tsum_add, ← hrow w]
    refine tsum_congr fun y => ?_
    split_ifs <;> simp
  intro N
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add, g70ma_G_zero]
    rw [tsum_eq_single i]
    · simp
    · intro b hb; simp [Ne.symm hb]
  | succ N ih =>
    rw [Finset.sum_range_succ, add_assoc]
    convert ih using 2
    simp only [g70ma_G_succ P A N]
    have : ∀ w, (if w ∈ A then ∑' x, g70ma_G P A N i x * ennP P x w else 0) =
        ∑' x, g70ma_G P A N i x * (if w ∈ A then ennP P x w else 0) := by
      intro w; split_ifs <;> simp
    simp_rw [this]
    rw [ENNReal.tsum_comm, ← ENNReal.tsum_add]
    refine tsum_congr fun x => ?_
    rw [ENNReal.tsum_mul_left, ← mul_add, hsplit, mul_one]

open Classical in
lemma g70ma_mass_le {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) (hP : IsStochasticC P)
    (A : Set S) (i : S) :
    ∑' n, ∑' w, g70ma_G P A n i w * ∑' y, (if y ∈ A then 0 else ennP P w y) ≤ 1 :=
  ENNReal.tsum_le_of_sum_range_le fun N => by
    rw [← g70ma_mass P hP A i N]; exact le_self_add

lemma g70ma_claim' {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) (T D : Set S)
    (hTD : Disjoint T D) (i : S) (hi : i ∉ D) : ∀ N y,
    g70ma_G P Tᶜ N i y = g70ma_G P {x | x ∉ D ∧ x ∉ T} N i y + ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal N,
      ∑' k : D, g70ma_G P Tᶜ ab.1 i k * g70ma_G P {x | x ∉ D ∧ x ∉ T} ab.2 k y := by
  classical
  intro N
  induction N with
  | zero =>
    intro y
    simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, g70ma_G_zero]
    have : (∑' k : D, (if i = (k : S) then (1 : ℝ≥0∞) else 0) * (if (k : S) = y then 1 else 0)) = 0 := by
      apply ENNReal.tsum_eq_zero.mpr
      intro k
      have : i ≠ k := fun h => hi (h ▸ k.2)
      simp [this]
    rw [this, add_zero]
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
    rw [g70ma_G_succ P {x | x ∉ D ∧ x ∉ T} N]
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
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ← ENNReal.tsum_add]
      refine tsum_congr fun x => ?_
      rw [ih x, add_mul, Finset.sum_mul]

lemma g70ma_step' {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) (T D : Set S)
    (hTD : Disjoint T D) (i : S) (hi : i ∉ D) (n : ℕ) (k : S) (hk : k ∉ T) :
    g70ma_G P Tᶜ (n + 1) i k = ∑' x, g70ma_G P {x | x ∉ D ∧ x ∉ T} n i x * ennP P x k +
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ∑' l : D,
      g70ma_G P Tᶜ p.1 i l * ∑' x, g70ma_G P {x | x ∉ D ∧ x ∉ T} p.2 l x * ennP P x k := by
  classical
  rw [g70ma_G_succ, if_pos (show k ∈ Tᶜ from hk)]
  simp_rw [g70ma_claim' P T D hTD i hi n, add_mul]
  rw [ENNReal.tsum_add]
  congr 1
  simp_rw [Finset.sum_mul, ← ENNReal.tsum_mul_right]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun l => ?_
  rw [← ENNReal.tsum_mul_left]
  simp_rw [mul_assoc]

lemma g70ma_Xeq {S : Type*} [Countable S] [DecidableEq S] (M : S → S → ℝ≥0∞) (D : Set S)
    (i k : S) : seriesInv M D i k = (if i = k then 1 else 0) +
      ∑' l : D, seriesInv M D i l * M l k := by
  unfold seriesInv
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [subPow]
  congr 1
  simp_rw [← ENNReal.tsum_mul_right]
  exact ENNReal.tsum_comm

lemma g70ma_R21 {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) (T D : Set S)
    (hTD : Disjoint T D) (i : S) (hi : i ∉ D) (j : S) (hj : j ∈ D) :
    ∑' a, g70ma_G P Tᶜ a i j =
      ∑' k : D, tabooF P T D i k * seriesInv (tabooF P T D) D k j := by
  have hkT : ∀ k, k ∈ D → k ∉ T := fun k hk h => Set.disjoint_left.mp hTD h hk
  have hF : ∀ l k, k ∈ D → tabooF P T D l k =
      ∑' b, ∑' x, g70ma_G P {x | x ∉ D ∧ x ∉ T} b l x * ennP P x k :=
    fun l k hk => g70ma_tabooF_eq P T D l k hk (hkT k hk)
  have G0 : ∀ k, k ∈ D → g70ma_G P Tᶜ 0 i k = 0 := fun k hk => by
    rw [g70ma_G_zero, if_neg]; rintro rfl; exact hi hk
  have Req : ∀ k, k ∈ D → ∑' a, g70ma_G P Tᶜ a i k = tabooF P T D i k +
      ∑' l : D, (∑' a, g70ma_G P Tᶜ a i l) * tabooF P T D l k := by
    intro k hk
    rw [tsum_eq_zero_add' ENNReal.summable, G0 k hk, zero_add]
    simp_rw [g70ma_step' P T D hTD i hi _ k (hkT k hk)]
    rw [ENNReal.tsum_add, hF i k hk]
    congr 1
    simp_rw [hF _ k hk, g70ma_cauchy]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun n => ?_
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  set F := tabooF P T D
  set X := seriesInv F D
  have Yeq : ∀ k, k ∈ D → ∑' k' : D, F i k' * X k' k =
      F i k + ∑' l : D, (∑' k' : D, F i k' * X k' l) * F l k := by
    intro k hk
    simp_rw [X, g70ma_Xeq F D _ k, mul_add, ENNReal.tsum_add]
    congr 1
    · rw [tsum_eq_single ⟨k, hk⟩]
      · simp
      · intro b hb
        have : (b : S) ≠ k := fun h => hb (Subtype.ext h)
        simp [this]
    · simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      simp_rw [mul_assoc]
  apply le_antisymm
  · have key : ∀ N, ∀ k, k ∈ D →
        ∑ a ∈ Finset.range N, g70ma_G P Tᶜ a i k ≤ ∑' k' : D, F i k' * X k' k := by
      intro N
      induction N with
      | zero => intro k _; simp
      | succ N ih =>
        intro k hk
        rw [Finset.sum_range_succ', G0 k hk, add_zero, Yeq k hk]
        simp_rw [g70ma_step' P T D hTD i hi _ k (hkT k hk)]
        rw [Finset.sum_add_distrib]
        gcongr
        · rw [hF i k hk]; exact ENNReal.sum_le_tsum _
        · simp_rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
          refine ENNReal.tsum_le_tsum fun l => ?_
          calc _ ≤ (∑ a ∈ Finset.range N, g70ma_G P Tᶜ a i l) *
                ∑' b, ∑' x, g70ma_G P {x | x ∉ D ∧ x ∉ T} b l x * ennP P x k :=
                g70ma_cauchy_le _ _ N
            _ ≤ _ := by rw [← hF l k hk]; gcongr; exact ih l l.2
    exact ENNReal.tsum_le_of_sum_range_le fun N => key N j hj
  · have key : ∀ n, ∀ k, k ∈ D →
        ∑ v ∈ Finset.range n, ∑' k' : D, F i k' * subPow F D v k' k ≤ ∑' a, g70ma_G P Tᶜ a i k := by
      intro n
      induction n with
      | zero => intro k _; simp
      | succ n ih =>
        intro k hk
        rw [Finset.sum_range_succ', Req k hk, add_comm]
        simp only [subPow]
        gcongr
        · rw [tsum_eq_single ⟨k, hk⟩]
          · simp
          · intro b hb
            have : (b : S) ≠ k := fun h => hb (Subtype.ext h)
            simp [this]
        · simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
          simp_rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
          rw [ENNReal.tsum_comm]
          refine ENNReal.tsum_le_tsum fun l => ?_
          simp_rw [← mul_assoc, ← Finset.sum_mul]
          rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]
          gcongr
          rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
          exact ih l l.2
    have : ∑' k' : D, F i k' * X k' j = ∑' v, ∑' k' : D, F i k' * subPow F D v k' j := by
      simp_rw [X, seriesInv, ← ENNReal.tsum_mul_left]
      exact ENNReal.tsum_comm
    rw [this]
    exact ENNReal.tsum_le_of_sum_range_le fun N => key N j hj

open Classical in
lemma g70ma_fin {S : Type*} [Countable S] [DecidableEq S] (P : S → S → ℝ) (hP : IsStochasticC P)
    (hirr : IrreducibleC P) (T : Set S) (hTne : T.Nonempty) (j : S) (hjT : j ∉ T)
    (i : S) (hiT : i ∉ T) : tabooR P T i j < ⊤ := by
  set A : Set S := {x | x ∉ ({j} : Set S) ∧ x ∉ T} with hA
  set e : S → ℝ≥0∞ := fun x => ∑' n, ∑' w, g70ma_G P A n x w *
    ∑' y, (if y ∈ T then ennP P w y else 0) with he
  have hTD : Disjoint T {j} := Set.disjoint_singleton_right.mpr hjT
  -- e is positive at j
  have Q : ∀ t, ∀ x, x ∉ T → ∀ y0 ∈ T, g70ma_G P Set.univ t x y0 ≠ 0 →
      e x ≠ 0 ∨ ∃ t' < t, ∃ y ∈ T, g70ma_G P Set.univ t' j y ≠ 0 := by
    intro t
    induction t with
    | zero =>
      intro x hx y0 hy0 hG
      rw [g70ma_G_zero] at hG
      split_ifs at hG with h
      · exact absurd (h ▸ hy0) hx
      · exact absurd rfl hG
    | succ t ih =>
      intro x hx y0 hy0 hG
      rw [g70ma_G_cons] at hG
      obtain ⟨⟨z, hzu⟩, hz⟩ : ∃ z : (Set.univ : Set S), ennP P x z * g70ma_G P Set.univ t z y0 ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hG (ENNReal.tsum_eq_zero.mpr hc)
      have hM : ennP P x z ≠ 0 := left_ne_zero_of_mul hz
      have hGz : g70ma_G P Set.univ t z y0 ≠ 0 := right_ne_zero_of_mul hz
      by_cases hzT : z ∈ T
      · left
        intro h0
        have h1 := ENNReal.tsum_eq_zero.mp (ENNReal.tsum_eq_zero.mp h0 0) x
        rw [g70ma_G_zero, if_pos rfl, one_mul] at h1
        have h2 := ENNReal.tsum_eq_zero.mp h1 z
        rw [if_pos hzT] at h2
        exact hM h2
      by_cases hzj : z = j
      · right; subst hzj; exact ⟨t, Nat.lt_succ_self t, y0, hy0, hGz⟩
      have hzA : z ∈ A := ⟨hzj, hzT⟩
      rcases ih z hzT y0 hy0 hGz with h | ⟨t', ht', y, hy, hG'⟩
      · left
        intro h0
        apply h
        apply ENNReal.tsum_eq_zero.mpr
        intro n
        apply ENNReal.tsum_eq_zero.mpr
        intro w
        have h1 := ENNReal.tsum_eq_zero.mp (ENNReal.tsum_eq_zero.mp h0 (n + 1)) w
        have h2 := g70ma_G_cons_le P A n x z w hzA
        rcases mul_eq_zero.mp h1 with h3 | h3
        · rw [h3, nonpos_iff_eq_zero] at h2
          rcases mul_eq_zero.mp h2 with h4 | h4
          · exact absurd h4 hM
          · rw [h4, zero_mul]
        · rw [h3, mul_zero]
      · right; exact ⟨t', Nat.lt_succ_of_lt ht', y, hy, hG'⟩
  obtain ⟨y0, hy0⟩ := hTne
  have hex : ∃ t, ∃ y ∈ T, g70ma_G P Set.univ t j y ≠ 0 := by
    obtain ⟨t, ht⟩ := hirr j y0
    exact ⟨t, y0, hy0, g70ma_stepPow_pos P hP.1 t j y0 ht⟩
  have hepos : e j ≠ 0 := by
    obtain ⟨y, hy, hG⟩ := Nat.find_spec hex
    rcases Q _ j hjT y hy hG with h | ⟨t', ht', h'⟩
    · exact h
    · exact absurd h' (Nat.find_min hex ht')
  -- f + e j ≤ 1
  have hfF : ∀ x, tabooF P T {j} x j = ∑' n, ∑' w, g70ma_G P A n x w * ennP P w j := by
    intro x; exact g70ma_tabooF_eq P T {j} x j rfl hjT
  have hout : ∀ w, ennP P w j + ∑' y, (if y ∈ T then ennP P w y else 0) =
      ∑' y, (if y ∈ A then 0 else ennP P w y) := by
    intro w
    have : ∀ y, (if y ∈ A then 0 else ennP P w y) =
        (if y = j then ennP P w y else 0) + (if y ∈ T then ennP P w y else 0) := by
      intro y
      by_cases hyj : y = j
      · subst hyj; simp [hA, hjT]
      by_cases hyT : y ∈ T
      · simp [hA, hyT, hyj]
      · simp [hA, hyT, hyj]
    rw [tsum_congr this, ENNReal.tsum_add, tsum_ite_eq]
  have hfe : tabooF P T {j} j j + e j ≤ 1 := by
    rw [hfF, he]
    simp only
    rw [← ENNReal.tsum_add]
    simp_rw [← ENNReal.tsum_add, ← mul_add, hout]
    convert g70ma_mass_le P hP A j
  have hf1 : tabooF P T {j} j j < 1 := by
    have hne : tabooF P T {j} j j ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans le_self_add hfe)
    exact lt_of_lt_of_le (ENNReal.lt_add_right hne hepos) hfe
  have hpow : ∀ ν, subPow (tabooF P T {j}) {j} ν j j = tabooF P T {j} j j ^ ν := by
    intro ν
    induction ν with
    | zero => simp [subPow]
    | succ ν ih =>
      simp only [subPow]
      rw [tsum_singleton (f := fun k => subPow (tabooF P T {j}) {j} ν j k * tabooF P T {j} k j), ih,
        pow_succ]
  have hX : seriesInv (tabooF P T {j}) {j} j j < ⊤ := by
    unfold seriesInv
    simp_rw [hpow]
    rw [ENNReal.tsum_geometric]
    exact lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr (tsub_pos_iff_lt.mpr hf1).ne')
  by_cases hij : i = j
  · rw [hij, g70ma_L P T {j} hTD j rfl j rfl]; exact hX
  · have hR : tabooR P T i j = ∑' a, g70ma_G P Tᶜ a i j := by
      unfold tabooR; simp_rw [g70ma_tabooP_eq P T _ i j hjT]
    rw [hR, g70ma_R21 P T {j} hTD i hij j rfl]
    rw [tsum_singleton (f := fun k => tabooF P T {j} i k * seriesInv (tabooF P T {j}) {j} k j)]
    have hF1 : tabooF P T {j} i j ≤ 1 := by
      rw [hfF]
      refine le_trans ?_ (g70ma_mass_le P hP A i)
      gcongr with n w
      refine le_trans ?_ (ENNReal.le_tsum j)
      have : j ∉ A := fun h => h.1 rfl
      simp [this]
    calc tabooF P T {j} i j * seriesInv (tabooF P T {j}) {j} j j
        ≤ 1 * seriesInv (tabooF P T {j}) {j} j j := by gcongr
      _ < ⊤ := by rw [one_mul]; exact hX



/-- Latouche & Ramaswami, Theorem 5.2.3 (p. 116). Under the standing assumptions of Chapter 5
(an irreducible, aperiodic chain on a countable state space `S` with transition matrix `P`), for
any disjoint subsets `T` and `D` (with `T` nonempty):
(5.21) `ₜR_{TD} = ₜF_{TD} ₜR_{DD}`, and
(5.22) `ₜR_{DD} = Σ_{ν ≥ 0} (ₜF_{DD})^ν = (I − ₜF_{DD})⁻¹`, the series converging entrywise. -/
theorem solution {S : Type*} [Countable S] [DecidableEq S]
    (P : S → S → ℝ) (hP : IsStochasticC P) (hirr : IrreducibleC P) (hape : AperiodicC P)
    (T D : Set S) (hT : T.Nonempty) (hTD : Disjoint T D) :
    -- (5.21)
    (∀ i ∈ T, ∀ j ∈ D, tabooR P T i j = ∑' k : D, tabooF P T D i k * tabooR P T k j) ∧
    -- (5.22)
    (∀ i ∈ D, ∀ j ∈ D,
      tabooR P T i j = seriesInv (tabooF P T D) D i j ∧ seriesInv (tabooF P T D) D i j < ⊤) := by
  have hDT : ∀ k, k ∈ D → k ∉ T := fun k hk h => Set.disjoint_left.mp hTD h hk
  refine ⟨fun i hi j hj => ?_, fun i hi j hj => ⟨g70ma_L P T D hTD i hi j hj, ?_⟩⟩
  · have hR : tabooR P T i j = ∑' a, g70ma_G P Tᶜ a i j := by
      unfold tabooR; simp_rw [g70ma_tabooP_eq P T _ i j (hDT j hj)]
    rw [hR, g70ma_R21 P T D hTD i (fun h => hDT i h hi) j hj]
    refine tsum_congr fun (k : D) => ?_
    rw [g70ma_L P T D hTD k k.2 j hj]
  · rw [← g70ma_L P T D hTD i hi j hj]
    exact g70ma_fin P hP hirr T hT j (hDT j hj) i (hDT i hi)


