-- Prove2me | solution 1 for HighDimProb.RandomMatrices.error_correcting_code_guarantee_v2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-10T00:36:12.344676+00:00
-- url     : https://prove2.me/submissions/b86eacb2-435b-4ed2-972f-05c2c81b5486

/-
SPDX-License-Identifier: Apache-2.0
Complete proof of the canonical corrected error-correcting code guarantee.
All custom proof bodies are included; only canonical definitions and Mathlib
are imported. Finite Hamming packing, weighted ball counts and decoder construction are reconstructed.
-/
import Definitions.Def_HighDimProb_RandomMatrices_hammingDist
import Definitions.Def_HighDimProb_RandomMatrices_IsErrorCorrectingCode
import Mathlib

/- Complete module: HammingBasic -/
section

namespace HighDimProb.RandomMatrices

lemma hammingDist_self {n : ℕ} (x : Fin n → Bool) : hammingDist x x = 0 := by
  simp [hammingDist]

lemma hammingDist_symm {n : ℕ} (x y : Fin n → Bool) : hammingDist x y = hammingDist y x := by
  simp only [hammingDist, ne_comm]

lemma hammingDist_triangle {n : ℕ} (x y z : Fin n → Bool) :
    hammingDist x z ≤ hammingDist x y + hammingDist y z := by
  unfold hammingDist
  apply le_trans (Finset.card_le_card (show
    Finset.univ.filter (fun i => x i ≠ z i) ⊆
      Finset.univ.filter (fun i => x i ≠ y i) ∪ Finset.univ.filter (fun i => y i ≠ z i) from ?_))
    (Finset.card_union_le _ _)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hi ⊢
  by_contra h
  push Not at h
  exact hi (h.1.trans h.2)

end HighDimProb.RandomMatrices

end

/- Complete module: HammingPacking -/
section

namespace HighDimProb.RandomMatrices

lemma exists_hamming_packing (n m : ℕ) :
    ∃ C : Finset (Fin n → Bool),
      (C : Set (Fin n → Bool)).Pairwise (fun x y => m < hammingDist x y) ∧
      ∀ x : Fin n → Bool, ∃ c ∈ C, hammingDist x c ≤ m := by
  classical
  let family : Finset (Finset (Fin n → Bool)) :=
    Finset.univ.filter (fun C => (C : Set (Fin n → Bool)).Pairwise (fun x y => m < hammingDist x y))
  have he : (∅ : Finset (Fin n → Bool)) ∈ family := by simp [family]
  obtain ⟨C, hC⟩ := family.exists_maximal ⟨∅, he⟩
  have hsep : (C : Set (Fin n → Bool)).Pairwise (fun x y => m < hammingDist x y) := by
    simpa only [family, Finset.mem_filter, Finset.mem_univ, true_and] using hC.1
  refine ⟨C, hsep, ?_⟩
  intro x
  by_contra hno
  push Not at hno
  have hxnot : x ∉ C := by
    intro hx
    have hh := hno x hx
    simp [hammingDist_self] at hh
  have hnew : insert x C ∈ family := by
    simp only [family, Finset.mem_filter, Finset.mem_univ, true_and]
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with rfl | haC
    · rcases Finset.mem_insert.mp hb with rfl | hbC
      · exact (hab rfl).elim
      · exact hno b hbC
    · rcases Finset.mem_insert.mp hb with rfl | hbC
      · simpa only [hammingDist_symm] using hno a haC
      · exact hsep haC hbC hab
  exact hC.not_gt hnew (Finset.ssubset_insert hxnot)

lemma hamming_cover_card (n m : ℕ) (C : Finset (Fin n → Bool))
    (hc : ∀ x : Fin n → Bool, ∃ c ∈ C, hammingDist x c ≤ m) :
    2 ^ n ≤ ∑ c ∈ C, (Finset.univ.filter (fun x => hammingDist x c ≤ m)).card := by
  classical
  have hu : (Finset.univ : Finset (Fin n → Bool)) =
      C.biUnion (fun c => Finset.univ.filter (fun x => hammingDist x c ≤ m)) := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_filter, true_and, true_iff]
    exact hc x
  have hh := Finset.card_biUnion_le (s := C)
    (t := fun c => Finset.univ.filter (fun x => hammingDist x c ≤ m))
  rw [← hu] at hh
  simpa using hh

end HighDimProb.RandomMatrices

end

/- Complete module: PackingCardinality -/
section

namespace HighDimProb.RandomMatrices

lemma packing_card_of_ball_bound (k n m : ℕ) (C : Finset (Fin n → Bool)) (B : ℝ)
    (hB : 0 < B)
    (hc : ∀ x : Fin n → Bool, ∃ c ∈ C, hammingDist x c ≤ m)
    (hb : ∀ c ∈ C, ((Finset.univ.filter (fun x => hammingDist x c ≤ m)).card : ℝ) ≤ B)
    (hnum : (2 : ℝ) ^ k * B ≤ 2 ^ n) : 2 ^ k ≤ C.card := by
  classical
  have hcover : (2 : ℝ) ^ n ≤
      ∑ c ∈ C, ((Finset.univ.filter (fun x => hammingDist x c ≤ m)).card : ℝ) := by
    exact_mod_cast hamming_cover_card n m C hc
  have hsum : (∑ c ∈ C, ((Finset.univ.filter (fun x => hammingDist x c ≤ m)).card : ℝ)) ≤
      (C.card : ℝ) * B := by
    calc
      _ ≤ ∑ _c ∈ C, B := Finset.sum_le_sum hb
      _ = _ := by simp
  have hh : (2 : ℝ) ^ k ≤ C.card :=
    (mul_le_mul_iff_left₀ hB).mp (by simpa only [mul_comm B] using hnum.trans (hcover.trans hsum))
  exact_mod_cast hh

end HighDimProb.RandomMatrices

end

/- Complete module: PackingDecoder -/
section

namespace HighDimProb.RandomMatrices

lemma code_of_packing (k n r : ℕ) (C : Finset (Fin n → Bool))
    (hsep : (C : Set (Fin n → Bool)).Pairwise (fun x y => 2 * r < hammingDist x y))
    (hcard : 2 ^ k ≤ C.card) :
    ∃ E : (Fin k → Bool) → (Fin n → Bool), ∃ D : (Fin n → Bool) → (Fin k → Bool),
      IsErrorCorrectingCode (r := r) E D := by
  classical
  have hc : Fintype.card (Fin k → Bool) ≤ Fintype.card C := by simpa using hcard
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  let E : (Fin k → Bool) → (Fin n → Bool) := fun x => (e x).val
  have hinj : Function.Injective E := fun x y hxy => e.injective (Subtype.ext hxy)
  have huniq : ∀ y x z, hammingDist y (E x) ≤ r → hammingDist y (E z) ≤ r → x = z := by
    intro y x z hx hz
    by_contra hne
    have hdiff : E x ≠ E z := fun hh => hne (hinj hh)
    have hh := hsep (e x).property (e z).property hdiff
    change 2 * r < hammingDist (E x) (E z) at hh
    have ht := hammingDist_triangle (E x) y (E z)
    rw [hammingDist_symm (E x) y] at ht
    omega
  let D : (Fin n → Bool) → (Fin k → Bool) := fun y =>
    if h : ∃ x, hammingDist y (E x) ≤ r then Classical.choose h else fun _ => false
  refine ⟨E, D, ?_⟩
  intro x y hxy
  have hex : ∃ z, hammingDist y (E z) ≤ r := ⟨x, hxy⟩
  dsimp [D]
  rw [dif_pos hex]
  exact huniq y (Classical.choose hex) x (Classical.choose_spec hex) hxy

end HighDimProb.RandomMatrices

end

/- Complete module: HammingWeight -/
section

open scoped BigOperators

namespace HighDimProb.RandomMatrices

theorem hamming_weight_product {n : ℕ} (x c : Fin n → Bool) (q : ℝ) :
    q ^ hammingDist x c = ∏ i, if x i = c i then 1 else q := by
  classical
  simp only [hammingDist, ← Finset.prod_const]
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp_all

theorem hamming_weight_sum {n : ℕ} (c : Fin n → Bool) (q : ℝ) :
    ∑ x : Fin n → Bool, q ^ hammingDist x c = (1+q)^n := by
  classical
  simp_rw [hamming_weight_product]
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) => if b = c i then (1 : ℝ) else q)]
  have h : ∀ i : Fin n, ∑ b : Bool, (if b = c i then (1 : ℝ) else q) = 1+q := by
    intro i
    cases c i <;> simp [add_comm]
  simp_rw [h]
  simp

theorem hamming_ball_weight_bound {n m : ℕ} (c : Fin n → Bool) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ((Finset.univ.filter (fun x : Fin n → Bool => hammingDist x c ≤ m)).card : ℝ) * q^m
      ≤ (1+q)^n := by
  classical
  calc
    _ = ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => hammingDist x c ≤ m), q^m := by simp
    _ ≤ ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => hammingDist x c ≤ m),
        q ^ hammingDist x c := by
      apply Finset.sum_le_sum
      intro x hx
      exact pow_le_pow_of_le_one hq0 hq1 (Finset.mem_filter.mp hx).2
    _ ≤ ∑ x : Fin n → Bool, q ^ hammingDist x c := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro x _ _
      exact pow_nonneg hq0 _
    _ = _ := hamming_weight_sum c q

end HighDimProb.RandomMatrices

end

/- Complete module: HammingBallVolume -/
section

namespace HighDimProb.RandomMatrices

theorem hamming_ball_card_bound (n m : ℕ) (hm : 0 < m) (hmn : m ≤ n)
    (c : Fin n → Bool) :
    ((Finset.univ.filter (fun x : Fin n → Bool => hammingDist x c ≤ m)).card : ℝ) ≤
      (Real.exp 1 * (n : ℝ) / (m : ℝ)) ^ m := by
  classical
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hnp : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le hm hmn)
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hq0 : 0 < (m : ℝ) / n := div_pos hmp hnp
  have hq1 : (m : ℝ) / n ≤ 1 := (div_le_one hnp).mpr hmnR
  have hb := hamming_ball_weight_bound (m := m) c hq0.le hq1
  have he : (1 + (m : ℝ) / n) ^ n ≤ Real.exp (m : ℝ) := by
    calc
      _ ≤ (Real.exp ((m : ℝ) / n)) ^ n := by
        gcongr
        simpa only [add_comm] using Real.add_one_le_exp ((m : ℝ) / n)
      _ = Real.exp (m : ℝ) := by
        rw [← Real.exp_nat_mul]
        congr 1
        field_simp
  have hmul : (Real.exp 1 * (n : ℝ) / (m : ℝ)) ^ m * ((m : ℝ) / n) ^ m =
      Real.exp (m : ℝ) := by
    rw [← mul_pow]
    have hcancel : Real.exp 1 * (n : ℝ) / (m : ℝ) * ((m : ℝ) / n) = Real.exp 1 := by
      field_simp
    rw [hcancel, ← Real.exp_nat_mul]
    simp
  apply (mul_le_mul_iff_left₀ (pow_pos hq0 m)).mp
  rw [hmul]
  exact hb.trans he

end HighDimProb.RandomMatrices

end

/- Complete module: CodingNumeric -/
section

namespace HighDimProb.RandomMatrices

theorem coding_numeric_bound (k n r : ℕ) (hn : 0 < n) (hr : 0 < r)
    (h : (n : ℝ) ≥ (k : ℝ) + 2 * (r : ℝ) *
      Real.logb 2 (Real.exp 1 * (n : ℝ) / (2 * (r : ℝ)))) :
    (2 : ℝ)^k * (Real.exp 1 * (n : ℝ) / (2 * (r : ℝ)))^(2*r) ≤ (2 : ℝ)^n := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr
  have hb : 0 < Real.exp 1 * (n : ℝ) / (2 * (r : ℝ)) := by positivity
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (Real.log_le_log_iff (mul_pos (by positivity) (pow_pos hb _)) (by positivity)).mp
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
  have hh := mul_le_mul_of_nonneg_right h h2.le
  simp only [Real.logb, add_mul, mul_assoc, div_mul_cancel₀ _ h2.ne'] at hh
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hh

end HighDimProb.RandomMatrices

end

/- Complete module: CodingRoot -/
section

namespace HighDimProb.RandomMatrices

/-- **Theorem 4.3.5** (Guarantees for an error correcting code), Vershynin, *High-Dimensional
Probability* (2018), p. 88 — **corrected statement**.

Assume that positive integers `k, n, r` with `2r ≤ n` are such that `n ≥ k + 2r log₂(en/(2r))`.
Then there exists an error correcting code that encodes `k`-bit strings into `n`-bit strings and
can correct `r` errors (Definition 4.3.3, `IsErrorCorrectingCode`).

Correction to the printed source: the book states the theorem without the restriction
`2r ≤ n`, but its proof applies Exercise 4.2.16 (and the binomial bound of Exercise 0.0.5)
with `m = 2r`, which are stated only "for every integer `m ∈ [0, n]`". Without `2r ≤ n` the
printed statement is false: for `(k, n, r) = (1, 1, 2)` the hypothesis holds (since
`log₂(e/4) < 0`) but no code with two codewords can correct `r ≥ n/2` errors (the accepted
disproof of the retired version). With `2r ≤ n` the printed proof goes through verbatim:
`P({0,1}ⁿ, d_H, 2r) ≥ N({0,1}ⁿ, d_H, 2r) ≥ 2ⁿ (2r/(en))^{2r} ≥ 2ᵏ`, then Lemma 4.3.4. -/
theorem error_correcting_code_guarantee_v2 (k n r : ℕ) (hk : 0 < k) (hn : 0 < n) (hr : 0 < r)
    (hrn : 2 * r ≤ n)
    (h : (n : ℝ) ≥ (k : ℝ) + 2 * (r : ℝ) * Real.logb 2 (Real.exp 1 * (n : ℝ) / (2 * (r : ℝ)))) :
    ∃ E : (Fin k → Bool) → (Fin n → Bool), ∃ D : (Fin n → Bool) → (Fin k → Bool),
      IsErrorCorrectingCode (r := r) E D := by
  classical
  have _positive_messages := hk
  obtain ⟨C, hsep, hcover⟩ := exists_hamming_packing n (2 * r)
  apply code_of_packing k n r C hsep
  apply packing_card_of_ball_bound k n (2*r) C
    ((Real.exp 1 * (n : ℝ) / (2 * (r : ℝ)))^(2*r))
  · have hnp : (0 : ℝ) < n := by exact_mod_cast hn
    have hrp : (0 : ℝ) < r := by exact_mod_cast hr
    positivity
  · exact hcover
  · intro c _
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      hamming_ball_card_bound n (2*r) (by omega) hrn c
  · exact coding_numeric_bound k n r hn hr h

end HighDimProb.RandomMatrices

open HighDimProb.RandomMatrices

theorem solution (k n r : ℕ) (hk : 0 < k) (hn : 0 < n) (hr : 0 < r)
    (hrn : 2 * r ≤ n)
    (h : (n : ℝ) ≥ (k : ℝ) + 2 * (r : ℝ) * Real.logb 2 (Real.exp 1 * (n : ℝ) / (2 * (r : ℝ)))) :
    ∃ E : (Fin k → Bool) → (Fin n → Bool), ∃ D : (Fin n → Bool) → (Fin k → Bool),
      IsErrorCorrectingCode (r := r) E D := by
  exact error_correcting_code_guarantee_v2 k n r hk hn hr hrn h

end
