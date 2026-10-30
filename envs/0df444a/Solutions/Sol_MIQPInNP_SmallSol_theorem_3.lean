-- Prove2me | solution 1 for MIQPInNP.SmallSol.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T08:49:40.471569+00:00
-- url     : https://prove2.me/submissions/277cf7a6-1447-4ca2-800c-4f50bd764093

import Mathlib
import Definitions.Def_MIQPInNP_SmallSol_Setting
import Theorems.Thm_MIQPInNP_SmallSol_proposition_4
import Theorems.Thm_MIQPInNP_SmallSol_lemma_6
import Theorems.Thm_MIQPInNP_SmallSol_lemma_7
import Theorems.Thm_MIQPInNP_SmallSol_claim_1
import Theorems.Thm_MIQPInNP_SmallSol_claim_2

/-! ### Part A -/

open MIQPInNP.SmallSol
open scoped BigOperators

namespace MIQPT1

/-! ## Bit-size calculus -/

/-- `q` is `E`-small: numerator and denominator at most `2^E` in absolute value. -/
def Sm (E : ℕ) (q : ℚ) : Prop := q.num.natAbs ≤ 2 ^ E ∧ q.den ≤ 2 ^ E

lemma two_pow_mono {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by norm_num) h

lemma Sm.mono {E E' : ℕ} {q : ℚ} (h : Sm E q) (hE : E ≤ E') : Sm E' q :=
  ⟨h.1.trans (two_pow_mono hE), h.2.trans (two_pow_mono hE)⟩

lemma size_le_of_le_two_pow {k E : ℕ} (h : k ≤ 2 ^ E) : Nat.size k ≤ E + 1 := by
  rw [Nat.size_le]
  calc k ≤ 2 ^ E := h
    _ < 2 ^ (E + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)

lemma Sm.bitSize_le {E : ℕ} {q : ℚ} (h : Sm E q) : bitSize q ≤ 2 * E + 3 := by
  unfold bitSize
  have := size_le_of_le_two_pow h.1
  have := size_le_of_le_two_pow h.2
  omega

lemma sm_bitSize (q : ℚ) : Sm (bitSize q) q := by
  unfold bitSize
  constructor
  · calc q.num.natAbs ≤ 2 ^ Nat.size q.num.natAbs := (Nat.lt_size_self _).le
      _ ≤ _ := two_pow_mono (by omega)
  · calc q.den ≤ 2 ^ Nat.size q.den := (Nat.lt_size_self _).le
      _ ≤ _ := two_pow_mono (by omega)

lemma sm_of_div {E : ℕ} (N D : ℤ) (hD : D ≠ 0) (hN : N.natAbs ≤ 2 ^ E) (hD' : D.natAbs ≤ 2 ^ E) :
    Sm E ((N : ℚ) / (D : ℚ)) := by
  rw [← Rat.divInt_eq_div]
  constructor
  · have h1 := Rat.num_dvd N hD
    rcases eq_or_ne N 0 with h0 | h0
    · subst h0; simp
    · have := Int.natAbs_dvd_natAbs.mpr h1
      exact (Nat.le_of_dvd (Int.natAbs_pos.mpr h0) this).trans hN
  · have h1 := Rat.den_dvd N D
    have h2 : (Rat.divInt N D).den ∣ D.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr h1
      simpa using this
    exact (Nat.le_of_dvd (Int.natAbs_pos.mpr hD) h2).trans hD'

lemma sm_zero (E : ℕ) : Sm E 0 := by
  constructor <;> simp [Nat.one_le_two_pow]

lemma sm_int {E : ℕ} (z : ℤ) (h : z.natAbs ≤ 2 ^ E) : Sm E (z : ℚ) := by
  constructor
  · simpa using h
  · simp [Nat.one_le_two_pow]

lemma sm_nat {E : ℕ} (k : ℕ) (h : k ≤ 2 ^ E) : Sm E (k : ℚ) := by
  have := sm_int (E := E) (k : ℤ) (by simpa using h)
  simpa using this

lemma sm_neg {E : ℕ} {q : ℚ} (h : Sm E q) : Sm E (-q) := by
  constructor
  · simpa [Rat.num_neg_eq_neg_num] using h.1
  · simpa [Rat.den_neg_eq_den] using h.2

lemma sm_add {E1 E2 : ℕ} {a b : ℚ} (ha : Sm E1 a) (hb : Sm E2 b) : Sm (E1 + E2 + 1) (a + b) := by
  have key : a + b = ((a.num * b.den + b.num * a.den : ℤ) : ℚ) / ((a.den * b.den : ℤ) : ℚ) := by
    nth_rewrite 1 [← Rat.num_div_den a, ← Rat.num_div_den b]
    have h1 : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_nz
    have h2 : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.den_nz
    push_cast
    field_simp
  rw [key]
  apply sm_of_div
  · exact_mod_cast Nat.mul_ne_zero a.den_nz b.den_nz
  · calc (a.num * b.den + b.num * a.den).natAbs
          ≤ (a.num * b.den).natAbs + (b.num * a.den).natAbs := Int.natAbs_add_le _ _
      _ = a.num.natAbs * b.den + b.num.natAbs * a.den := by simp [Int.natAbs_mul]
      _ ≤ 2 ^ E1 * 2 ^ E2 + 2 ^ E2 * 2 ^ E1 := by
          gcongr
          · exact ha.1
          · exact hb.2
          · exact hb.1
          · exact ha.2
      _ = 2 ^ (E1 + E2 + 1) := by rw [pow_succ, pow_add]; ring
  · calc ((a.den : ℤ) * b.den).natAbs = a.den * b.den := by simp [Int.natAbs_mul]
      _ ≤ 2 ^ E1 * 2 ^ E2 := Nat.mul_le_mul ha.2 hb.2
      _ ≤ 2 ^ (E1 + E2 + 1) := by rw [← pow_add]; exact two_pow_mono (by omega)

lemma sm_sub {E1 E2 : ℕ} {a b : ℚ} (ha : Sm E1 a) (hb : Sm E2 b) : Sm (E1 + E2 + 1) (a - b) := by
  rw [sub_eq_add_neg]; exact sm_add ha (sm_neg hb)

lemma sm_mul {E1 E2 : ℕ} {a b : ℚ} (ha : Sm E1 a) (hb : Sm E2 b) : Sm (E1 + E2) (a * b) := by
  have key : a * b = ((a.num * b.num : ℤ) : ℚ) / ((a.den * b.den : ℤ) : ℚ) := by
    nth_rewrite 1 [← Rat.num_div_den a, ← Rat.num_div_den b]
    have h1 : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_nz
    have h2 : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.den_nz
    push_cast
    field_simp
  rw [key]
  apply sm_of_div
  · exact_mod_cast Nat.mul_ne_zero a.den_nz b.den_nz
  · rw [Int.natAbs_mul, pow_add]; exact Nat.mul_le_mul ha.1 hb.1
  · simp only [Int.natAbs_mul, Int.natAbs_natCast, pow_add]; exact Nat.mul_le_mul ha.2 hb.2

lemma sm_inv {E : ℕ} {q : ℚ} (h : Sm E q) : Sm E q⁻¹ := by
  rcases eq_or_ne q 0 with h0 | h0
  · subst h0; simpa using sm_zero E
  have key : q⁻¹ = ((q.den : ℤ) : ℚ) / ((q.num : ℤ) : ℚ) := by
    nth_rewrite 1 [← Rat.num_div_den q]
    rw [inv_div]; push_cast; rfl
  rw [key]
  apply sm_of_div
  · exact Rat.num_ne_zero.mpr h0
  · simpa using h.2
  · exact h.1

lemma sm_div {E1 E2 : ℕ} {a b : ℚ} (ha : Sm E1 a) (hb : Sm E2 b) : Sm (E1 + E2) (a / b) := by
  rw [div_eq_mul_inv]; exact sm_mul ha (sm_inv hb)

lemma sm_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) {E : ℕ} (h : ∀ i ∈ s, Sm E (f i)) :
    Sm (s.card * (E + 1)) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sm_zero 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact (sm_add h1 h2).mono (by ring_nf; omega)

lemma sm_sum_univ {n : ℕ} (f : Fin n → ℚ) {E : ℕ} (h : ∀ i, Sm E (f i)) :
    Sm (n * (E + 1)) (∑ i, f i) := by
  have := sm_sum Finset.univ f (fun i _ => h i)
  simpa using this

lemma sm_abs_le {E : ℕ} {q : ℚ} (h : Sm E q) : |q| ≤ 2 ^ E := by
  have hq : |q| ≤ |(q.num : ℚ)| := by
    nth_rewrite 1 [← Rat.num_div_den q]
    rw [abs_div]
    have : (1 : ℚ) ≤ |(q.den : ℚ)| := by
      rw [abs_of_pos (by exact_mod_cast q.den_pos)]; exact_mod_cast q.den_pos
    exact div_le_self (abs_nonneg _) this
  calc |q| ≤ |(q.num : ℚ)| := hq
    _ ≤ 2 ^ E := by
        have : ((q.num.natAbs : ℕ) : ℚ) ≤ 2 ^ E := by exact_mod_cast h.1
        rw [Nat.cast_natAbs, Int.cast_abs] at this
        exact this

lemma sm_abs_ge {E : ℕ} {q : ℚ} (h : Sm E q) (h0 : q ≠ 0) : 1 / 2 ^ E ≤ |q| := by
  have := sm_abs_le (sm_inv h)
  rw [abs_inv] at this
  have hpos : 0 < |q| := abs_pos.mpr h0
  rw [div_le_iff₀ (by positivity)]
  calc (1 : ℚ) = |q| * |q|⁻¹ := by field_simp
    _ ≤ |q| * 2 ^ E := by gcongr

lemma sm_abs_le_real {E : ℕ} {q : ℚ} (h : Sm E q) : |(q : ℝ)| ≤ 2 ^ E := by
  have := sm_abs_le h
  exact_mod_cast this

/-! ## Sizes of vectors and matrices -/

lemma bitSize_le_vecSize {n : ℕ} (v : Fin n → ℚ) (i : Fin n) : bitSize (v i) ≤ vecSize v := by
  unfold vecSize
  have := Finset.single_le_sum (f := fun j => bitSize (v j)) (fun j _ => Nat.zero_le _)
    (Finset.mem_univ i)
  omega

lemma sm_of_vecSize {n : ℕ} (v : Fin n → ℚ) (i : Fin n) : Sm (vecSize v) (v i) :=
  (sm_bitSize _).mono (bitSize_le_vecSize v i)

lemma n_le_vecSize {n : ℕ} (v : Fin n → ℚ) : n ≤ vecSize v := by unfold vecSize; omega

lemma bitSize_le_matSize {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) (j : Fin n) :
    bitSize (M i j) ≤ matSize M := by
  unfold matSize
  have h1 := Finset.single_le_sum (f := fun j => bitSize (M i j)) (fun j _ => Nat.zero_le _)
    (Finset.mem_univ j)
  have h2 := Finset.single_le_sum (f := fun i => ∑ j, bitSize (M i j)) (fun j _ => Nat.zero_le _)
    (Finset.mem_univ i)
  omega

lemma sm_of_matSize {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) (j : Fin n) :
    Sm (matSize M) (M i j) :=
  (sm_bitSize _).mono (bitSize_le_matSize M i j)

lemma mn_le_matSize {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) : m * n ≤ matSize M := by
  unfold matSize; omega

lemma vecSize_le_of_sm {n E : ℕ} (v : Fin n → ℚ) (h : ∀ i, Sm E (v i)) :
    vecSize v ≤ n * (2 * E + 4) := by
  unfold vecSize
  have : ∑ i, bitSize (v i) ≤ ∑ _i : Fin n, (2 * E + 3) :=
    Finset.sum_le_sum (fun i _ => (h i).bitSize_le)
  simp at this
  nlinarith

lemma matSize_le_of_sm {m n E : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) (h : ∀ i j, Sm E (M i j)) :
    matSize M ≤ m * n * (2 * E + 4) := by
  unfold matSize
  have : ∑ i, ∑ j, bitSize (M i j) ≤ ∑ _i : Fin m, ∑ _j : Fin n, (2 * E + 3) :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => (h i j).bitSize_le))
  simp at this
  nlinarith

lemma bitSize_zero : bitSize 0 = 2 := by decide

lemma vecSize_zero (n : ℕ) : vecSize (0 : Fin n → ℚ) = 3 * n := by
  unfold vecSize; simp [bitSize_zero]; ring

lemma matSize_zero (m n : ℕ) : matSize (0 : Matrix (Fin m) (Fin n) ℚ) = 3 * (m * n) := by
  unfold matSize; simp [bitSize_zero]; ring

/-! ## Polynomials over ℕ -/

lemma peval_mono (g : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : g.eval a ≤ g.eval b := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval_add]; omega
  | monomial k c =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

lemma le_peval_self_add (g : Polynomial ℕ) (x : ℕ) : x ≤ (g + Polynomial.X).eval x := by
  simp

end MIQPT1

namespace MIQPT1

/-! ## Exponent bounds of the form `K * W^j` -/

lemma one_le_pow_of_one_le' {W : ℕ} (hW : 1 ≤ W) (j : ℕ) : 1 ≤ W ^ j := Nat.one_le_pow _ _ hW

lemma smW_mul {W K1 K2 j : ℕ} {a b : ℚ} (ha : Sm (K1 * W ^ j) a) (hb : Sm (K2 * W ^ j) b) :
    Sm ((K1 + K2) * W ^ j) (a * b) := by
  have := sm_mul ha hb; rwa [← add_mul] at this

lemma smW_add {W K1 K2 j : ℕ} (hW : 1 ≤ W) {a b : ℚ} (ha : Sm (K1 * W ^ j) a)
    (hb : Sm (K2 * W ^ j) b) : Sm ((K1 + K2 + 1) * W ^ j) (a + b) := by
  have := sm_add ha hb
  refine this.mono ?_
  have := one_le_pow_of_one_le' hW j
  nlinarith

lemma smW_sub {W K1 K2 j : ℕ} (hW : 1 ≤ W) {a b : ℚ} (ha : Sm (K1 * W ^ j) a)
    (hb : Sm (K2 * W ^ j) b) : Sm ((K1 + K2 + 1) * W ^ j) (a - b) := by
  rw [sub_eq_add_neg]; exact smW_add hW ha (sm_neg hb)

lemma smW_lift {W K j : ℕ} (hW : 1 ≤ W) {a : ℚ} (ha : Sm (K * W ^ j) a) (K' j' : ℕ)
    (hK : K ≤ K') (hj : j ≤ j') : Sm (K' * W ^ j') a :=
  ha.mono (Nat.mul_le_mul hK (Nat.pow_le_pow_right hW hj))

lemma smW_sum {W K j n : ℕ} (hW : 1 ≤ W) (hn : n ≤ W) (f : Fin n → ℚ)
    (h : ∀ i, Sm (K * W ^ j) (f i)) : Sm ((K + 1) * W ^ (j + 1)) (∑ i, f i) := by
  refine (sm_sum_univ f h).mono ?_
  have := one_le_pow_of_one_le' hW j
  calc n * (K * W ^ j + 1) ≤ W * (K * W ^ j + W ^ j) := Nat.mul_le_mul hn (by omega)
    _ = (K + 1) * W ^ (j + 1) := by ring

lemma smW_of_le {W E : ℕ} {a : ℚ} (h : Sm E a) (hE : E ≤ W) : Sm (1 * W ^ 1) a :=
  h.mono (by simpa using hE)

end MIQPT1
/-! ### Part B -/

open MIQPInNP.SmallSol
open scoped BigOperators

namespace MIQPT1

lemma mem_polyhedron_toReal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (x : Fin n → ℚ) : toReal x ∈ polyhedron A b ↔ ∀ i, ∑ j, A i j * x j ≤ b i := by
  unfold polyhedron toReal
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h i; have := h i; exact_mod_cast this
  · intro h i; have := h i; exact_mod_cast this

lemma quadForm_toReal {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    quadForm H (toReal x) = ((∑ i, ∑ j, x i * H i j * x j : ℚ) : ℝ) := by
  unfold quadForm toReal; push_cast; rfl

lemma quadVal_toReal {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (d : ℚ)
    (x : Fin n → ℚ) :
    quadVal H c d (toReal x) =
      ((∑ i, ∑ j, x i * H i j * x j + ∑ i, c i * x i + d : ℚ) : ℝ) := by
  unfold quadVal quadForm toReal; push_cast; rfl

lemma isClosed_polyhedron {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) :
    IsClosed (polyhedron A b) := by
  have : polyhedron A b = ⋂ i, {x : Fin n → ℝ | ∑ j, (A i j : ℝ) * x j ≤ (b i : ℝ)} := by
    ext x; simp [polyhedron]
  rw [this]
  refine isClosed_iInter (fun i => isClosed_le ?_ continuous_const)
  fun_prop

lemma continuous_quadVal {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (d : ℚ) :
    Continuous (quadVal H c d) := by
  unfold quadVal quadForm; fun_prop

lemma isCompact_polyhedron {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (hb : Bornology.IsBounded (polyhedron A b)) : IsCompact (polyhedron A b) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_polyhedron A b) hb

end MIQPT1
/-! ### Part C -/

open MIQPInNP.SmallSol
open scoped BigOperators

namespace MIQPT1

lemma mem_intCone_image {n d : ℕ} (v : Fin d → Fin n → ℝ) (S : Set (Fin d)) (x : Fin n → ℝ) :
    x ∈ intCone (v '' S) ↔
      ∃ μ : Fin d → ℕ, (∀ j, j ∉ S → μ j = 0) ∧ x = ∑ j, μ j • v j := by
  classical
  constructor
  · intro hx
    unfold intCone at hx
    induction hx using AddSubmonoid.closure_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      refine ⟨Pi.single j 1, ?_, ?_⟩
      · intro k hk; have : k ≠ j := fun h => hk (h ▸ hj); simp [Pi.single_apply, this]
      · rw [Finset.sum_eq_single j]
        · simp
        · intro k _ hk; simp [Pi.single_apply, hk]
        · simp
    | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨μ1, h1, hh1⟩ := hy
      obtain ⟨μ2, h2, hh2⟩ := hz
      refine ⟨μ1 + μ2, ?_, ?_⟩
      · intro j hj; simp [h1 j hj, h2 j hj]
      · rw [hh1, hh2, ← Finset.sum_add_distrib]; congr 1; ext j; simp [add_smul]
  · rintro ⟨μ, hμ, rfl⟩
    unfold intCone
    refine AddSubmonoid.sum_mem _ (fun j _ => ?_)
    by_cases hj : j ∈ S
    · exact AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure (Set.mem_image_of_mem v hj)) _
    · rw [hμ j hj, zero_smul]; exact AddSubmonoid.zero_mem _

lemma mem_intCone_range {n d : ℕ} (v : Fin d → Fin n → ℝ) (x : Fin n → ℝ) :
    x ∈ intCone (Set.range v) ↔ ∃ μ : Fin d → ℕ, x = ∑ j, μ j • v j := by
  rw [← Set.image_univ, mem_intCone_image]
  simp

lemma mem_cone_image {n d : ℕ} (v : Fin d → Fin n → ℝ) (S : Set (Fin d)) (x : Fin n → ℝ) :
    x ∈ cone (v '' S) ↔
      ∃ l : Fin d → ℝ, (∀ j, 0 ≤ l j) ∧ (∀ j, j ∉ S → l j = 0) ∧ x = ∑ j, l j • v j := by
  classical
  constructor
  · intro hx
    unfold cone at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      refine ⟨Pi.single j 1, ?_, ?_, ?_⟩
      · intro k; by_cases h : k = j <;> simp [Pi.single_apply, h]
      · intro k hk; have : k ≠ j := fun h => hk (h ▸ hj); simp [Pi.single_apply, this]
      · rw [Finset.sum_eq_single j]
        · simp
        · intro k _ hk; simp [Pi.single_apply, hk]
        · simp
    | zero => exact ⟨0, fun _ => le_rfl, fun _ _ => rfl, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨μ1, h0, h1, hh1⟩ := hy
      obtain ⟨μ2, h0', h2, hh2⟩ := hz
      refine ⟨μ1 + μ2, fun j => add_nonneg (h0 j) (h0' j), ?_, ?_⟩
      · intro j hj; simp [h1 j hj, h2 j hj]
      · rw [hh1, hh2, ← Finset.sum_add_distrib]; congr 1; ext j u; simp; ring
    | smul a y _ hy =>
      obtain ⟨μ, h0, h1, hh⟩ := hy
      rw [hh]
      refine ⟨fun j => (a : ℝ) * μ j, fun j => mul_nonneg a.2 (h0 j), ?_, ?_⟩
      · intro j hj; simp [h1 j hj]
      · rw [Finset.smul_sum]; congr 1; ext j u
        simp [NNReal.smul_def, mul_assoc]
  · rintro ⟨l, hl0, hl, rfl⟩
    unfold cone
    refine Submodule.sum_mem _ (fun j _ => ?_)
    by_cases hj : j ∈ S
    · have : l j • v j = (⟨l j, hl0 j⟩ : NNReal) • v j := by
        ext u; simp [NNReal.smul_def]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · rw [hl j hj, zero_smul]; exact Submodule.zero_mem _

lemma mem_cone_range {n d : ℕ} (v : Fin d → Fin n → ℝ) (x : Fin n → ℝ) :
    x ∈ cone (Set.range v) ↔ ∃ l : Fin d → ℝ, (∀ j, 0 ≤ l j) ∧ x = ∑ j, l j • v j := by
  rw [← Set.image_univ, mem_cone_image]
  simp

lemma intCone_subset_cone {n : ℕ} (S : Set (Fin n → ℝ)) : intCone S ⊆ cone S := by
  intro x hx
  unfold intCone at hx
  unfold cone
  induction hx using AddSubmonoid.closure_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz

lemma cone_mono {n : ℕ} {S T : Set (Fin n → ℝ)} (h : S ⊆ T) : cone S ⊆ cone T := by
  unfold cone; exact Submodule.span_mono h

/-- A cone generated inside a set closed under nonneg combinations. -/
lemma cone_subset_of {n : ℕ} (S : Set (Fin n → ℝ)) (K : Set (Fin n → ℝ))
    (h0 : (0 : Fin n → ℝ) ∈ K) (hadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K)
    (hsmul : ∀ (t : ℝ), 0 ≤ t → ∀ x ∈ K, t • x ∈ K) (hS : S ⊆ K) : cone S ⊆ K := by
  intro x hx
  unfold cone at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact hS hy
  | zero => exact h0
  | add y z _ _ hy hz => exact hadd y hy z hz
  | smul a y _ hy => rw [NNReal.smul_def]; exact hsmul a a.2 y hy

lemma recCone_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : (0 : Fin n → ℝ) ∈ recCone A := by
  intro i; simp

lemma recCone_add {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    ∀ x ∈ recCone A, ∀ y ∈ recCone A, x + y ∈ recCone A := by
  intro x hx y hy i
  have h1 := hx i; have h2 := hy i
  simp only [Pi.zero_apply, Rat.cast_zero] at h1 h2 ⊢
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  linarith

lemma recCone_smul {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    ∀ (t : ℝ), 0 ≤ t → ∀ x ∈ recCone A, t • x ∈ recCone A := by
  intro t ht x hx i
  have h1 := hx i
  simp only [Pi.zero_apply, Rat.cast_zero] at h1 ⊢
  simp only [Pi.smul_apply, smul_eq_mul]
  have : ∑ j, (A i j : ℝ) * (t * x j) = t * ∑ j, (A i j : ℝ) * x j := by
    rw [Finset.mul_sum]; congr 1; ext j; ring
  rw [this]
  exact mul_nonpos_of_nonneg_of_nonpos ht h1

lemma cone_subset_recCone {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (S : Set (Fin n → ℝ))
    (hS : S ⊆ recCone A) : cone S ⊆ recCone A :=
  cone_subset_of S _ (recCone_zero A) (recCone_add A) (recCone_smul A) hS

/-- Membership in the polyhedron plus recession cone. -/
lemma polyhedron_add_recCone {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (x y : Fin n → ℝ) (hx : x ∈ polyhedron A b) (hy : y ∈ recCone A) : x + y ∈ polyhedron A b := by
  intro i
  have h1 := hx i; have h2 := hy i
  simp only [recCone, polyhedron, Pi.zero_apply, Rat.cast_zero, Set.mem_setOf_eq] at h1 h2 ⊢
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  linarith

end MIQPT1
/-! ### Part D -/

open MIQPInNP.SmallSol
open scoped BigOperators

namespace MIQPT1

/-! ## Rational versions of the quadratic function -/

def qf {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) : ℚ := ∑ i, ∑ j, x i * H i j * x j

def qv {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (d : ℚ) (x : Fin n → ℚ) : ℚ :=
  qf H x + ∑ i, c i * x i + d

def lin {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (x r : Fin n → ℚ) : ℚ :=
  ∑ i, ∑ j, (x i * H i j * r j + r i * H i j * x j) + ∑ i, c i * r i

lemma quadForm_eq_qf {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    quadForm H (toReal x) = (qf H x : ℝ) := by
  unfold quadForm toReal qf; push_cast; rfl

lemma quadVal_eq_qv {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (d : ℚ)
    (x : Fin n → ℚ) : quadVal H c d (toReal x) = (qv H c d x : ℝ) := by
  unfold quadVal qv; rw [quadForm_eq_qf]; unfold toReal; push_cast; rfl

lemma qv_add_smul {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (d : ℚ)
    (x r : Fin n → ℚ) (t : ℚ) :
    qv H c d (x + t • r) = qv H c d x + t * lin H c x r + t ^ 2 * qf H r := by
  have p1 : ∑ i, ∑ j, (x + t • r) i * H i j * (x + t • r) j = ∑ i, ∑ j, x i * H i j * x j +
      t * ∑ i, ∑ j, (x i * H i j * r j + r i * H i j * x j) +
      t ^ 2 * ∑ i, ∑ j, r i * H i j * r j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have p2 : ∑ i, c i * (x + t • r) i = ∑ i, c i * x i + t * ∑ i, c i * r i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  unfold qv lin qf
  rw [p1, p2]; ring

lemma quadForm_smul {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℝ) (t : ℝ) :
    quadForm H (t • x) = t ^ 2 * quadForm H x := by
  unfold quadForm
  rw [Finset.mul_sum]; congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j
  simp only [Pi.smul_apply, smul_eq_mul]; ring

/-! ## Stacking systems -/

def stack {m1 m2 n : ℕ} (A : Matrix (Fin m1) (Fin n) ℚ) (A' : Matrix (Fin m2) (Fin n) ℚ) :
    Matrix (Fin (m1 + m2)) (Fin n) ℚ := Fin.append A A'

def stackv {m1 m2 : ℕ} (b : Fin m1 → ℚ) (b' : Fin m2 → ℚ) : Fin (m1 + m2) → ℚ := Fin.append b b'

lemma stack_castAdd {m1 m2 n : ℕ} (A : Matrix (Fin m1) (Fin n) ℚ) (A' : Matrix (Fin m2) (Fin n) ℚ)
    (i : Fin m1) : stack A A' (Fin.castAdd m2 i) = A i := by
  unfold stack; exact Fin.append_left _ _ _

lemma stack_natAdd {m1 m2 n : ℕ} (A : Matrix (Fin m1) (Fin n) ℚ) (A' : Matrix (Fin m2) (Fin n) ℚ)
    (i : Fin m2) : stack A A' (Fin.natAdd m1 i) = A' i := by
  unfold stack; exact Fin.append_right _ _ _

lemma stackv_castAdd {m1 m2 : ℕ} (b : Fin m1 → ℚ) (b' : Fin m2 → ℚ) (i : Fin m1) :
    stackv b b' (Fin.castAdd m2 i) = b i := by
  unfold stackv; exact Fin.append_left _ _ _

lemma stackv_natAdd {m1 m2 : ℕ} (b : Fin m1 → ℚ) (b' : Fin m2 → ℚ) (i : Fin m2) :
    stackv b b' (Fin.natAdd m1 i) = b' i := by
  unfold stackv; exact Fin.append_right _ _ _

lemma polyhedron_stack {m1 m2 n : ℕ} (A : Matrix (Fin m1) (Fin n) ℚ) (A' : Matrix (Fin m2) (Fin n) ℚ)
    (b : Fin m1 → ℚ) (b' : Fin m2 → ℚ) :
    polyhedron (stack A A') (stackv b b') = polyhedron A b ∩ polyhedron A' b' := by
  ext x
  simp only [polyhedron, Set.mem_inter_iff, Set.mem_setOf_eq]
  rw [Fin.forall_fin_add]
  simp [stack_castAdd, stack_natAdd, stackv_castAdd, stackv_natAdd]

lemma matSize_stack {m1 m2 n : ℕ} (A : Matrix (Fin m1) (Fin n) ℚ) (A' : Matrix (Fin m2) (Fin n) ℚ) :
    matSize (stack A A') = matSize A + matSize A' := by
  unfold matSize
  rw [Fin.sum_univ_add]
  simp [stack_castAdd, stack_natAdd]
  ring

lemma vecSize_stackv {m1 m2 : ℕ} (b : Fin m1 → ℚ) (b' : Fin m2 → ℚ) :
    vecSize (stackv b b') = vecSize b + vecSize b' := by
  unfold vecSize
  rw [Fin.sum_univ_add]
  simp [stackv_castAdd, stackv_natAdd]
  ring

lemma bitSize_neg (q : ℚ) : bitSize (-q) = bitSize q := by
  unfold bitSize; simp

lemma matSize_neg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : matSize (-A) = matSize A := by
  unfold matSize; simp [bitSize_neg]

lemma bitSize_one : bitSize 1 = 3 := by decide

lemma vecSize_one (n : ℕ) : vecSize (1 : Fin n → ℚ) = 4 * n := by
  unfold vecSize; simp [bitSize_one]; ring

/-! ## Pointed polyhedra -/

lemma bounded_of_pointed {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (hA : IsPointedPoly A)
    (S : Set (Fin n → ℝ)) (B : ℝ) (hS : ∀ x ∈ S, ∀ i, |∑ j, (A i j : ℝ) * x j| ≤ B) :
    Bornology.IsBounded S := by
  let L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ) := Matrix.mulVecLin (A.map (fun q : ℚ => (q : ℝ)))
  have hL : ∀ x i, L x i = ∑ j, (A i j : ℝ) * x j := by
    intro x i; simp [L, Matrix.mulVec, dotProduct]
  have hinj : Function.Injective L := by
    intro x y hxy
    have h0 : ∀ i, ∑ j, (A i j : ℝ) * (x - y) j = 0 := by
      intro i
      have := congrFun hxy i
      rw [hL, hL] at this
      simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      linarith
    have := hA (x - y) h0
    exact sub_eq_zero.mp this
  obtain ⟨K, -, hK⟩ := (LinearMap.injective_iff_antilipschitz L).mp hinj
  rw [isBounded_iff_forall_norm_le]
  refine ⟨K * max B 0, fun x hx => ?_⟩
  have h1 := hK.le_mul_dist x 0
  simp only [dist_zero_right, map_zero] at h1
  have h2 : ‖L x‖ ≤ max B 0 := by
    rw [pi_norm_le_iff_of_nonneg (le_max_right _ _)]
    intro i
    rw [Real.norm_eq_abs, hL]
    exact (hS x hx i).trans (le_max_left _ _)
  calc ‖x‖ ≤ K * ‖L x‖ := h1
    _ ≤ K * max B 0 := by gcongr

lemma pointed_poly_bounded {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (hA : IsPointedPoly A)
    (P : Set (Fin n → ℝ)) (hP : P ⊆ polyhedron (stack A (-A)) (stackv 0 1)) :
    Bornology.IsBounded P := by
  refine bounded_of_pointed A hA P 1 (fun x hx i => ?_)
  have := hP hx
  rw [polyhedron_stack] at this
  obtain ⟨h1, h2⟩ := this
  have a1 := h1 i; have a2 := h2 i
  simp only [Pi.zero_apply, Rat.cast_zero, Pi.one_apply, Rat.cast_one, Matrix.neg_apply,
    Rat.cast_neg, neg_mul, Finset.sum_neg_distrib] at a1 a2
  rw [abs_le]; constructor <;> linarith

end MIQPT1
/-! ### Part D2 -/

open MIQPInNP.SmallSol
open scoped BigOperators Pointwise

namespace MIQPT1

lemma quadVal_zero_zero {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℝ) :
    quadVal H 0 0 x = quadForm H x := by
  unfold quadVal; simp

lemma n_le_matSize_sq {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) : n ≤ matSize H :=
  (Nat.le_mul_self n).trans (mn_le_matSize H)

lemma sm_qf {n W : ℕ} (hW : 1 ≤ W) (hn : n ≤ W) (H : Matrix (Fin n) (Fin n) ℚ)
    (x : Fin n → ℚ) (hH : ∀ i j, Sm (1 * W ^ 1) (H i j)) (hx : ∀ i, Sm (1 * W ^ 1) (x i)) :
    Sm (5 * W ^ 3) (qf H x) := by
  unfold qf
  have h1 : ∀ i j, Sm ((1 + 1 + 1) * W ^ 1) (x i * H i j * x j) :=
    fun i j => smW_mul (smW_mul (hx i) (hH i j)) (hx j)
  have h2 := fun i => smW_sum hW hn _ (h1 i)
  have h3 := smW_sum hW hn _ h2
  exact h3.mono (le_of_eq (by ring))

lemma sm_lin {n W : ℕ} (hW : 1 ≤ W) (hn : n ≤ W) (H : Matrix (Fin n) (Fin n) ℚ)
    (c x r : Fin n → ℚ) (hH : ∀ i j, Sm (1 * W ^ 1) (H i j)) (hc : ∀ i, Sm (1 * W ^ 1) (c i))
    (hx : ∀ i, Sm (1 * W ^ 1) (x i)) (hr : ∀ i, Sm (1 * W ^ 1) (r i)) :
    Sm (13 * W ^ 3) (lin H c x r) := by
  unfold lin
  have h1 := fun i j => smW_add hW (smW_mul (smW_mul (hx i) (hH i j)) (hr j))
      (smW_mul (smW_mul (hr i) (hH i j)) (hx j))
  have h2 := smW_sum hW hn _ (fun i => smW_sum hW hn _ (h1 i))
  have h3 := smW_sum hW hn _ (fun i => smW_mul (hc i) (hr i))
  have h3' := smW_lift hW h3 (1 + 1 + 1) 3 (by norm_num) (by norm_num)
  exact (smW_add hW h2 h3').mono (le_of_eq (by ring))

lemma sm_qv {n W : ℕ} (hW : 1 ≤ W) (hn : n ≤ W) (H : Matrix (Fin n) (Fin n) ℚ)
    (c x : Fin n → ℚ) (d : ℚ) (hH : ∀ i j, Sm (1 * W ^ 1) (H i j))
    (hc : ∀ i, Sm (1 * W ^ 1) (c i)) (hd : Sm (1 * W ^ 1) d) (hx : ∀ i, Sm (1 * W ^ 1) (x i)) :
    Sm (11 * W ^ 3) (qv H c d x) := by
  unfold qv
  have h1 := sm_qf hW hn H x hH hx
  have h3 := smW_sum hW hn _ (fun i => smW_mul (hc i) (hx i))
  have h3' := smW_lift hW h3 (1 + 1 + 1) 3 (by norm_num) (by norm_num)
  have hd' := smW_lift hW hd 1 3 le_rfl (by norm_num)
  exact (smW_add hW (smW_add hW h1 h3') hd').mono (le_of_eq (by ring))

lemma prod_den_le {n : ℕ} (r : Fin n → ℚ) : ∏ i, (r i).den ≤ 2 ^ vecSize r := by
  calc ∏ i, (r i).den ≤ ∏ i, 2 ^ bitSize (r i) :=
        Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i _ => (sm_bitSize (r i)).2)
    _ = 2 ^ ∑ i, bitSize (r i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ 2 ^ vecSize r := two_pow_mono (by unfold vecSize; omega)

lemma int_of_den_dvd (q : ℚ) (D : ℕ) (h : q.den ∣ D) : ∃ z : ℤ, (D : ℚ) * q = z := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k * q.num, ?_⟩
  rw [hk]; push_cast
  rw [mul_comm (q.den : ℚ) k, mul_assoc, mul_comm (q.den : ℚ) q, Rat.mul_den_eq_num]

lemma mixed_add {n p : ℕ} (x y : Fin n → ℚ) (hx : IsMixedInt p (toReal x))
    (hy : ∀ i : Fin n, (i : ℕ) < p → ∃ z : ℤ, y i = z) : IsMixedInt p (toReal (x + y)) := by
  intro i hi
  obtain ⟨z1, hz1⟩ := hx i hi
  obtain ⟨z2, hz2⟩ := hy i hi
  refine ⟨z1 + z2, ?_⟩
  unfold toReal at hz1 ⊢
  simp only [Pi.add_apply, Rat.cast_add, hz1, hz2]; push_cast; ring

lemma sm_W_of_vecSize {n W : ℕ} (v : Fin n → ℚ) (h : vecSize v ≤ W) (i : Fin n) :
    Sm (1 * W ^ 1) (v i) := (sm_of_vecSize v i).mono (by simpa using h)

lemma sm_W_of_matSize {m n W : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) (h : matSize M ≤ W)
    (i : Fin m) (j : Fin n) : Sm (1 * W ^ 1) (M i j) := (sm_of_matSize M i j).mono (by simpa using h)

lemma mem_polyhedron_add_smul {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (x r : Fin n → ℚ) (t : ℚ) (ht : 0 ≤ t) (hx : toReal x ∈ polyhedron A b)
    (hr : toReal r ∈ recCone A) : toReal (x + t • r) ∈ polyhedron A b := by
  rw [mem_polyhedron_toReal] at hx ⊢
  have hr' : ∀ i, ∑ j, A i j * r j ≤ 0 := by
    have := (mem_polyhedron_toReal A 0 r).mp hr
    simpa using this
  intro i
  have e : ∑ j, A i j * (x + t • r) j = ∑ j, A i j * x j + t * ∑ j, A i j * r j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [e]
  have := hx i; have := hr' i
  nlinarith

end MIQPT1
/-! ### Part R0 -/

open MIQPInNP.SmallSol

namespace M5Core

open Finset Matrix

noncomputable def rdot {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) (x : Fin n → ℝ) : ℝ :=
  ∑ j, (A i j : ℝ) * x j

lemma rdot_add_smul {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) (x v : Fin n → ℝ) (t : ℝ) :
    rdot A i (x + t • v) = rdot A i x + t * rdot A i v := by
  unfold rdot
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl; intro j _; ring

lemma rdot_sub {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) (x y : Fin n → ℝ) :
    rdot A i (x - y) = rdot A i x - rdot A i y := by
  unfold rdot
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma rdot_smul {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) (v : Fin n → ℝ) (t : ℝ) :
    rdot A i (t • v) = t * rdot A i v := by
  have := rdot_add_smul A i 0 v t
  simpa [rdot] using this

lemma mem_poly_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (x : Fin n → ℝ) :
    x ∈ polyhedron A b ↔ ∀ i, rdot A i x ≤ b i := Iff.rfl

theorem descent {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (a : Fin n → ℝ)
    (hH : ∀ d : Fin n → ℝ, (∃ i, rdot A i d ≠ 0) →
      ∃ s : ℝ, ∑ j, a j * (s * d j) ≤ 0 ∧ ∃ i, 0 < s * rdot A i d) :
    ∀ x ∈ polyhedron A b, ∃ x' ∈ polyhedron A b, ∑ j, a j * x' j ≤ ∑ j, a j * x j ∧
      ∀ d : Fin n → ℝ, (∀ i, rdot A i x' = b i → rdot A i d = 0) → ∀ i, rdot A i d = 0 := by
  classical
  intro x hx
  induction hk : (univ.filter fun i => rdot A i x < b i).card using Nat.strong_induction_on
    generalizing x with
  | _ k ih =>
  by_cases hend : ∀ d : Fin n → ℝ, (∀ i, rdot A i x = b i → rdot A i d = 0) → ∀ i, rdot A i d = 0
  · exact ⟨x, hx, le_rfl, hend⟩
  push Not at hend
  obtain ⟨d, hdT, i1, hi1⟩ := hend
  obtain ⟨s, hsa, i2, hi2⟩ := hH d ⟨i1, hi1⟩
  set v : Fin n → ℝ := s • d with hv
  have hvT : ∀ i, rdot A i x = b i → rdot A i v = 0 := by
    intro i hi; rw [hv, rdot_smul, hdT i hi, mul_zero]
  have hvi2 : 0 < rdot A i2 v := by rw [hv, rdot_smul]; exact hi2
  set bad := univ.filter (fun i => 0 < rdot A i v) with hbad
  have hne : bad.Nonempty := ⟨i2, by simp [bad, hvi2]⟩
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image bad (fun i => (b i - rdot A i x) / rdot A i v) hne
  have hvi0 : 0 < rdot A i0 v := by simpa [bad] using hi0
  set τ := (b i0 - rdot A i0 x) / rdot A i0 v with hτ
  have hxi0 : rdot A i0 x < b i0 := by
    rcases (hx i0).lt_or_eq with h | h
    · exact h
    · exact absurd (hvT i0 h) hvi0.ne'
  have hτpos : 0 < τ := div_pos (by linarith) hvi0
  set x1 := x + τ • v with hx1
  have hx1P : x1 ∈ polyhedron A b := by
    intro i
    show rdot A i x1 ≤ b i
    rw [hx1, rdot_add_smul]
    by_cases hc : 0 < rdot A i v
    · have := hmin i (by simp [bad, hc])
      rw [div_le_div_iff₀ hvi0 hc] at this
      have h2 : τ * rdot A i v ≤ b i - rdot A i x := by
        rw [hτ, div_mul_eq_mul_div, div_le_iff₀ hvi0]; linarith
      linarith
    · push Not at hc
      have h3 : rdot A i x ≤ b i := hx i
      nlinarith
  have hx1i0 : rdot A i0 x1 = b i0 := by
    rw [hx1, rdot_add_smul, hτ, div_mul_cancel₀ _ hvi0.ne']; ring
  have hsub : (univ.filter fun i => rdot A i x1 < b i) ⊂ (univ.filter fun i => rdot A i x < b i) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨i0, by simp [hxi0], by simp [hx1i0]⟩
    · intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro h
      rcases (hx i).lt_or_eq with h' | h'
      · exact h'
      · rw [hx1, rdot_add_smul, hvT i h', mul_zero, add_zero] at h
        exact absurd h' h.ne
  have hlt := Finset.card_lt_card hsub
  obtain ⟨x', hx'P, hx'a, hx'end⟩ := ih _ (hk ▸ hlt) x1 hx1P rfl
  refine ⟨x', hx'P, le_trans hx'a ?_, hx'end⟩
  have : ∑ j, a j * x1 j = ∑ j, a j * x j + τ * ∑ j, a j * (s * d j) := by
    simp only [hx1, hv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1; apply Finset.sum_congr rfl; intro j _; ring
  rw [this]
  nlinarith


def rs {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (i : Fin m) : ℕ :=
  ∑ j, bitSize (A i j) + bitSize (b i)

def alpha (n S : ℕ) : ℕ := n * n + n * (2 * S)

lemma den_le_two_pow (q : ℚ) : q.den ≤ 2 ^ bitSize q := by
  have h1 := Nat.lt_size_self q.den
  have h2 : 2 ^ Nat.size q.den ≤ 2 ^ bitSize q := Nat.pow_le_pow_right (by norm_num) (by unfold bitSize; omega)
  omega

lemma natAbs_num_le_two_pow (q : ℚ) : q.num.natAbs ≤ 2 ^ bitSize q := by
  have h1 := Nat.lt_size_self q.num.natAbs
  have h2 : 2 ^ Nat.size q.num.natAbs ≤ 2 ^ bitSize q :=
    Nat.pow_le_pow_right (by norm_num) (by unfold bitSize; omega)
  omega

lemma scale_int (q : ℚ) (C : ℕ) (h : q.den ∣ C) :
    ∃ z : ℤ, (C : ℚ) * q = z ∧ z.natAbs ≤ C * q.num.natAbs := by
  obtain ⟨t, rfl⟩ := h
  refine ⟨t * q.num, ?_, ?_⟩
  · push_cast
    have := Rat.mul_den_eq_num q
    rw [← this]; ring
  · rw [Int.natAbs_mul, Int.natAbs_natCast]
    rw [mul_assoc]
    exact Nat.le_mul_of_pos_left _ q.den_pos

theorem small_solve {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (T : Finset (Fin m))
    (x : Fin n → ℝ) (hx : ∀ i ∈ T, rdot A i x = b i) :
    ∃ y : Fin n → ℚ, (∀ i ∈ T, rdot A i (toReal y) = b i) ∧
      ∃ I : Finset (Fin m), I.card ≤ n ∧ ∃ D : ℤ, D ≠ 0 ∧ |D| ≤ 2 ^ alpha n (∑ i ∈ I, rs A b i) ∧
        ∀ j, ∃ P : ℤ, |P| ≤ 2 ^ alpha n (∑ i ∈ I, rs A b i) ∧ (y j : ℚ) = P / D := by
  classical
  let v : T → (Fin n → ℚ) := fun i => A i.1
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℚ v
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hk : Fintype.card κ ≤ n := by
    have := hli.fintype_card_le_finrank; simpa using this
  let R : Matrix κ (Fin n) ℚ := fun l j => A (a l).1 j
  have hRrow : LinearIndependent ℚ R.row := hli
  have hcols : Submodule.span ℚ (Set.range R.col) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_row,
      finrank_span_eq_card hRrow, Module.finrank_fintype_fun_eq_card]
  obtain ⟨κ', a', ha', hspan', hli'⟩ := exists_linearIndependent' ℚ R.col
  have : Finite κ' := Finite.of_injective a' ha'
  let : Fintype κ' := Fintype.ofFinite κ'
  have hcard' : Fintype.card κ' = Fintype.card κ := by
    have h1 := linearIndependent_iff_card_eq_finrank_span.mp hli'
    rw [h1, Set.finrank, hspan', hcols, finrank_top, Module.finrank_fintype_fun_eq_card]
  let eqv : κ ≃ κ' := Fintype.equivOfCardEq hcard'.symm
  let f : κ → Fin n := fun c => a' (eqv c)
  have hf : Function.Injective f := ha'.comp eqv.injective
  let M : Matrix κ κ ℚ := fun l c => A (a l).1 (f c)
  have hMcol : LinearIndependent ℚ M.col := by
    have : M.col = R.col ∘ a' ∘ eqv := by ext c l; rfl
    rw [this]; exact hli'.comp eqv eqv.injective
  have hdet : M.det ≠ 0 := by
    have := Matrix.linearIndependent_cols_iff_isUnit.mp hMcol
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at this; exact this
  let β : κ → ℚ := fun l => b (a l).1
  let z : κ → ℚ := (M.det)⁻¹ • M.cramer β
  have hMz : M *ᵥ z = β := by
    simp only [z, Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul, inv_mul_cancel₀ hdet, one_smul]
  let y : Fin n → ℚ := fun j => ∑ c, if f c = j then z c else 0
  have hy : ∀ (w : Fin n → ℚ), ∑ j, w j * y j = ∑ c, w (f c) * z c := by
    intro w
    simp only [y, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro c _
    rw [Finset.sum_ite_eq]
    simp
  have hrow : ∀ l : κ, ∑ j, A (a l).1 j * y j = b (a l).1 := by
    intro l
    rw [hy]
    have := congrFun hMz l
    simpa [Matrix.mulVec, dotProduct, M, β] using this
  have hall : ∀ i ∈ T, ∑ j, A i j * y j = b i := by
    intro i hiT
    have hmem : v ⟨i, hiT⟩ ∈ Submodule.span ℚ (Set.range (v ∘ a)) := by
      rw [hspan]; exact Submodule.subset_span ⟨_, rfl⟩
    obtain ⟨μ, hμ⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hmem
    have hAi : ∀ j, A i j = ∑ l, μ l * A (a l).1 j := by
      intro j; have := congrFun hμ j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, v] at this
      rw [← this]
    have e1 : ∑ j, A i j * y j = ∑ l, μ l * b (a l).1 := by
      simp_rw [hAi, Finset.sum_mul]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro l _
      rw [← hrow l, Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    have e2 : (b i : ℝ) = ∑ l, (μ l : ℝ) * b (a l).1 := by
      rw [← hx i hiT]; unfold rdot
      simp_rw [hAi]; push_cast; simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro l _
      rw [← hx _ (a l).2]; unfold rdot; rw [Finset.mul_sum]; apply Finset.sum_congr rfl
      intro j _; ring
    rw [e1]; exact_mod_cast e2.symm
  refine ⟨y, ?_, ?_⟩
  · intro i hi
    unfold rdot toReal
    exact_mod_cast hall i hi
  -- bounds
  let S := ∑ l, rs A b (a l).1
  let I : Finset (Fin m) := univ.image (fun l => (a l).1)
  have hinj : Function.Injective (fun l => (a l).1) := Subtype.val_injective.comp ha
  have hIcard : I.card = Fintype.card κ := by
    rw [Finset.card_image_of_injective _ hinj]; rfl
  have hIS : ∑ i ∈ I, rs A b i = S := Finset.sum_image (fun _ _ _ _ h => hinj h)
  refine ⟨I, hIcard ▸ hk, ?_⟩
  rw [hIS]
  let C : ℕ := ∏ l, ((∏ j, (A (a l).1 j).den) * (b (a l).1).den)
  have hCpos : 0 < C := by
    apply Finset.prod_pos; intro l _
    apply Nat.mul_pos (Finset.prod_pos (fun j _ => (A (a l).1 j).den_pos)) (b (a l).1).den_pos
  have hCle : C ≤ 2 ^ S := by
    have : ∀ l, (∏ j, (A (a l).1 j).den) * (b (a l).1).den ≤ 2 ^ rs A b (a l).1 := by
      intro l
      unfold rs
      rw [pow_add, ← Finset.prod_pow_eq_pow_sum]
      exact Nat.mul_le_mul (Finset.prod_le_prod' (fun j _ => den_le_two_pow _)) (den_le_two_pow _)
    calc C ≤ ∏ l, 2 ^ rs A b (a l).1 := Finset.prod_le_prod' (fun l _ => this l)
      _ = 2 ^ S := Finset.prod_pow_eq_pow_sum _ _ _
  have hbitle : ∀ l, (∀ j, bitSize (A (a l).1 j) ≤ S) ∧ bitSize (b (a l).1) ≤ S := by
    intro l
    have h1 : rs A b (a l).1 ≤ S := Finset.single_le_sum (f := fun l => rs A b (a l).1)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
    refine ⟨fun j => ?_, ?_⟩
    · have : bitSize (A (a l).1 j) ≤ ∑ j, bitSize (A (a l).1 j) :=
        Finset.single_le_sum (f := fun j => bitSize (A (a l).1 j)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ j)
      unfold rs at h1; omega
    · unfold rs at h1; omega
  have hent : ∀ q : ℚ, q.den ∣ C → bitSize q ≤ S → ∃ zq : ℤ, (C : ℚ) * q = zq ∧ |zq| ≤ 2 ^ (2 * S) := by
    intro q hd hb
    obtain ⟨zq, hzq, hzb⟩ := scale_int q C hd
    refine ⟨zq, hzq, ?_⟩
    have h2 : zq.natAbs ≤ 2 ^ (2 * S) := by
      calc zq.natAbs ≤ C * q.num.natAbs := hzb
        _ ≤ 2 ^ S * 2 ^ S := Nat.mul_le_mul hCle
            (le_trans (natAbs_num_le_two_pow q) (Nat.pow_le_pow_right (by norm_num) hb))
        _ = 2 ^ (2 * S) := by rw [← pow_add]; ring_nf
    rw [Int.abs_eq_natAbs]; exact_mod_cast h2
  have hdvdA : ∀ l j, (A (a l).1 j).den ∣ C := by
    intro l j
    exact dvd_trans (dvd_trans (Finset.dvd_prod_of_mem (fun j => (A (a l).1 j).den) (Finset.mem_univ j))
      (dvd_mul_right _ _))
      (Finset.dvd_prod_of_mem (fun l => (∏ j, (A (a l).1 j).den) * (b (a l).1).den) (Finset.mem_univ l))
  have hdvdb : ∀ l, (b (a l).1).den ∣ C := by
    intro l
    exact dvd_trans (dvd_mul_left _ _)
      (Finset.dvd_prod_of_mem (fun l => (∏ j, (A (a l).1 j).den) * (b (a l).1).den) (Finset.mem_univ l))
  have hMent : ∀ l c, ∃ zq : ℤ, (C : ℚ) * M l c = zq ∧ |zq| ≤ 2 ^ (2 * S) :=
    fun l c => hent _ (hdvdA l (f c)) ((hbitle l).1 (f c))
  have hβent : ∀ l, ∃ zq : ℤ, (C : ℚ) * β l = zq ∧ |zq| ≤ 2 ^ (2 * S) :=
    fun l => hent _ (hdvdb l) (hbitle l).2
  choose NM hNM1 hNM2 using hMent
  choose Nβ hNβ1 hNβ2 using hβent
  let N : Matrix κ κ ℤ := Matrix.of NM
  have hNcast : N.map (Int.cast : ℤ → ℚ) = (C : ℚ) • M := by
    ext l c; simp [N, hNM1]
  have hdetcast : ∀ N' : Matrix κ κ ℤ, ((N'.det : ℤ) : ℚ) = (N'.map (Int.cast : ℤ → ℚ)).det := by
    intro N'
    have := RingHom.map_det (Int.castRingHom ℚ) N'
    simpa [RingHom.mapMatrix_apply] using this
  have hNdet : (N.det : ℚ) = (C : ℚ) ^ Fintype.card κ * M.det := by
    rw [hdetcast, hNcast, Matrix.det_smul]
  have hCq : (C : ℚ) ≠ 0 := by exact_mod_cast hCpos.ne'
  have hD0 : N.det ≠ 0 := by
    intro h
    have : (N.det : ℚ) = 0 := by rw [h]; simp
    rw [hNdet] at this
    exact (mul_ne_zero (pow_ne_zero _ hCq) hdet) this
  have hbound : ∀ N' : Matrix κ κ ℤ, (∀ l c, |N' l c| ≤ 2 ^ (2 * S)) →
      |N'.det| ≤ 2 ^ alpha n S := by
    intro N' hN'
    have h1 := Matrix.det_le (abv := AbsoluteValue.abs) hN'
    simp only [AbsoluteValue.abs_apply, nsmul_eq_mul] at h1
    refine le_trans h1 ?_
    have hfac : ((Fintype.card κ).factorial : ℤ) ≤ 2 ^ (n * n) := by
      have : (Fintype.card κ).factorial ≤ 2 ^ (n * n) := by
        calc (Fintype.card κ).factorial ≤ n.factorial := Nat.factorial_le hk
          _ ≤ n ^ n := Nat.factorial_le_pow _
          _ ≤ (2 ^ n) ^ n := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
          _ = 2 ^ (n * n) := by rw [← pow_mul]
      exact_mod_cast this
    have hpow : ((2 : ℤ) ^ (2 * S)) ^ Fintype.card κ ≤ 2 ^ (n * (2 * S)) := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (by rw [mul_comm]; exact Nat.mul_le_mul_right _ hk)
    unfold alpha
    rw [pow_add]
    exact mul_le_mul hfac hpow (by positivity) (by positivity)
  refine ⟨N.det, hD0, hbound N (fun l c => hNM2 l c), ?_⟩
  intro j
  by_cases hj : ∃ c, f c = j
  · obtain ⟨c, rfl⟩ := hj
    let Nc : Matrix κ κ ℤ := N.updateCol c Nβ
    refine ⟨Nc.det, hbound Nc ?_, ?_⟩
    · intro l c'
      simp only [Nc, Matrix.updateCol_apply]
      split_ifs
      · exact hNβ2 l
      · exact hNM2 l c'
    · have hyc : y (f c) = z c := by
        simp only [y]
        rw [Finset.sum_eq_single c]
        · simp
        · intro c' _ hc'; simp [hf.ne hc']
        · simp
      rw [hyc]
      have hNccast : Nc.map (Int.cast : ℤ → ℚ) = (C : ℚ) • M.updateCol c β := by
        ext l c'
        simp only [Nc, Matrix.map_apply, Matrix.updateCol_apply, Matrix.smul_apply, smul_eq_mul]
        split_ifs
        · rw [hNβ1]
        · simp [N, hNM1]
      rw [hdetcast Nc, hNccast, Matrix.det_smul, hNdet]
      simp only [z, Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply]
      field_simp
  · refine ⟨0, by simp, ?_⟩
    push Not at hj
    simp only [y]
    rw [Finset.sum_eq_zero (fun c _ => by simp [hj c])]
    simp


theorem small_point {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (a : Fin n → ℝ)
    (hH : ∀ d : Fin n → ℝ, (∃ i, rdot A i d ≠ 0) →
      ∃ s : ℝ, ∑ j, a j * (s * d j) ≤ 0 ∧ ∃ i, 0 < s * rdot A i d)
    (hH' : ∀ d : Fin n → ℝ, (∀ i, rdot A i d = 0) → ∑ j, a j * d j = 0)
    (x : Fin n → ℝ) (hx : x ∈ polyhedron A b) :
    ∃ y : Fin n → ℚ, toReal y ∈ polyhedron A b ∧ ∑ j, a j * toReal y j ≤ ∑ j, a j * x j ∧
      ∃ I : Finset (Fin m), I.card ≤ n ∧ ∃ D : ℤ, D ≠ 0 ∧ |D| ≤ 2 ^ alpha n (∑ i ∈ I, rs A b i) ∧
        ∀ j, ∃ P : ℤ, |P| ≤ 2 ^ alpha n (∑ i ∈ I, rs A b i) ∧ (y j : ℚ) = P / D := by
  classical
  obtain ⟨x', hx'P, hx'a, hend⟩ := descent A b a hH x hx
  obtain ⟨y, hyT, I, hI, D, hD, hDb, hP⟩ :=
    small_solve A b (univ.filter fun i => rdot A i x' = b i) x' (by simp)
  have hd : ∀ i, rdot A i (toReal y - x') = 0 :=
    hend _ (fun i hi => by rw [rdot_sub, hyT i (by simp [hi]), hi]; ring)
  refine ⟨y, fun i => ?_, ?_, I, hI, D, hD, hDb, hP⟩
  · show rdot A i (toReal y) ≤ b i
    have h1 := hd i
    rw [rdot_sub] at h1
    have h2 : rdot A i x' ≤ b i := hx'P i
    linarith
  · have := hH' _ hd
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib] at this
    linarith

lemma bitSize_div_le (P D : ℤ) (hD : D ≠ 0) (α : ℕ) (hP : |P| ≤ 2 ^ α) (hDb : |D| ≤ 2 ^ α) :
    bitSize ((P : ℚ) / D) ≤ 2 * α + 3 := by
  rw [← Rat.divInt_eq_div]
  have hnum : (Rat.divInt P D).num.natAbs ≤ 2 ^ α := by
    by_cases hP0 : P = 0
    · subst hP0; simp
    · have h1 := Int.natAbs_le_of_dvd_ne_zero (Rat.num_dvd P hD) hP0
      have h2 : P.natAbs ≤ 2 ^ α := by
        have : ((P.natAbs : ℕ) : ℤ) ≤ 2 ^ α := by rw [Int.natCast_natAbs]; exact hP
        exact_mod_cast this
      omega
  have hden : (Rat.divInt P D).den ≤ 2 ^ α := by
    have h1 := Int.le_of_dvd (by rw [abs_pos]; exact hD) ((Rat.den_dvd P D).trans (self_dvd_abs D))
    have : ((Rat.divInt P D).den : ℤ) ≤ 2 ^ α := le_trans h1 hDb
    exact_mod_cast this
  have s1 : Nat.size (Rat.divInt P D).num.natAbs ≤ α + 1 := by
    have := Nat.one_le_two_pow (n := α); rw [Nat.size_le, pow_succ]; omega
  have s2 : Nat.size (Rat.divInt P D).den ≤ α + 1 := by
    have := Nat.one_le_two_pow (n := α); rw [Nat.size_le, pow_succ]; omega
  unfold bitSize; omega

lemma vecSize_le_of_rep {n : ℕ} (y : Fin n → ℚ) (α : ℕ) (D : ℤ) (hD : D ≠ 0) (hDb : |D| ≤ 2 ^ α)
    (hP : ∀ j, ∃ P : ℤ, |P| ≤ 2 ^ α ∧ (y j : ℚ) = P / D) :
    vecSize y ≤ n * (2 * α + 4) := by
  unfold vecSize
  have : ∀ j, bitSize (y j) ≤ 2 * α + 3 := by
    intro j; obtain ⟨P, hPb, hPe⟩ := hP j; rw [hPe]; exact bitSize_div_le P D hD α hPb hDb
  have h2 := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => this j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  nlinarith

end M5Core
/-! ### Part R1 -/

open MIQPInNP.SmallSol
open scoped BigOperators Pointwise

namespace MIQPT1

/-- Every non-empty rational polyhedron contains a small rational point (from the descent and
Cramer argument of `M5Core.small_point`). -/
lemma small_feasible {m N : ℕ} (B : Matrix (Fin m) (Fin N) ℚ) (e : Fin m → ℚ) (z : Fin N → ℝ)
    (hz : z ∈ polyhedron B e) :
    ∃ zq : Fin N → ℚ, toReal zq ∈ polyhedron B e ∧
      ∀ j, Sm (M5Core.alpha N (matSize B + vecSize e)) (zq j) := by
  obtain ⟨y, hy, -, I, -, D, hD, hDb, hP⟩ := M5Core.small_point B e 0
    (fun d ⟨i, hi⟩ => ⟨M5Core.rdot B i d, by simp, i, by nlinarith [sq_pos_of_ne_zero hi]⟩)
    (fun d _ => by simp) z hz
  refine ⟨y, hy, fun j => ?_⟩
  obtain ⟨P, hPb, hPe⟩ := hP j
  have hS : ∑ i ∈ I, M5Core.rs B e i ≤ matSize B + vecSize e := by
    calc ∑ i ∈ I, M5Core.rs B e i ≤ ∑ i, M5Core.rs B e i :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ I)
      _ = ∑ i, ∑ j, bitSize (B i j) + ∑ i, bitSize (e i) := by
          simp [M5Core.rs, Finset.sum_add_distrib]
      _ ≤ matSize B + vecSize e := by unfold matSize vecSize; omega
  have hα : M5Core.alpha N (∑ i ∈ I, M5Core.rs B e i) ≤ M5Core.alpha N (matSize B + vecSize e) := by
    unfold M5Core.alpha; gcongr
  rw [hPe]
  apply (sm_of_div P D hD _ _).mono hα
  · have : (P.natAbs : ℤ) ≤ 2 ^ M5Core.alpha N (∑ i ∈ I, M5Core.rs B e i) := by
      rw [Int.natCast_natAbs]; exact hPb
    exact_mod_cast this
  · have : (D.natAbs : ℤ) ≤ 2 ^ M5Core.alpha N (∑ i ∈ I, M5Core.rs B e i) := by
      rw [Int.natCast_natAbs]; exact hDb
    exact_mod_cast this

/-- Horizontal concatenation of matrices. -/
def hcat {k n m : ℕ} (L : Matrix (Fin k) (Fin n) ℚ) (R : Matrix (Fin k) (Fin m) ℚ) :
    Matrix (Fin k) (Fin (n + m)) ℚ := fun i => Fin.append (L i) (R i)

lemma hcat_row {k n m : ℕ} (L : Matrix (Fin k) (Fin n) ℚ) (R : Matrix (Fin k) (Fin m) ℚ)
    (i : Fin k) (z : Fin (n + m) → ℝ) :
    ∑ j, ((hcat L R i j : ℚ) : ℝ) * z j =
      ∑ j, (L i j : ℝ) * z (Fin.castAdd m j) + ∑ j, (R i j : ℝ) * z (Fin.natAdd n j) := by
  rw [Fin.sum_univ_add]
  simp [hcat, Fin.append_left, Fin.append_right]

lemma matSize_hcat {k n m : ℕ} (L : Matrix (Fin k) (Fin n) ℚ) (R : Matrix (Fin k) (Fin m) ℚ) :
    matSize (hcat L R) = matSize L + matSize R := by
  unfold matSize
  have : ∀ i, ∑ j, bitSize (hcat L R i j) = ∑ j, bitSize (L i j) + ∑ j, bitSize (R i j) := by
    intro i; rw [Fin.sum_univ_add]; simp [hcat, Fin.append_left, Fin.append_right]
  simp only [this, Finset.sum_add_distrib]
  ring

/-- The symmetric part of `H`. -/
def symH {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => (H i j + H j i) / 2

lemma symH_transpose {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) : (symH H).transpose = symH H := by
  ext i j; simp [symH, Matrix.transpose_apply]; ring

lemma quadForm_symH {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℝ) :
    quadForm (symH H) x = quadForm H x := by
  unfold quadForm symH
  have swap : ∑ i, ∑ j, x i * (H j i : ℝ) * x j = ∑ i, ∑ j, x i * (H i j : ℝ) * x j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  have e : ∀ i j, x i * (((H i j + H j i) / 2 : ℚ) : ℝ) * x j =
      (1 / 2) * (x i * (H i j : ℝ) * x j) + (1 / 2) * (x i * (H j i : ℝ) * x j) := by
    intro i j; push_cast; ring
  simp_rw [e, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [swap]; ring

lemma quadVal_symH {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (d : ℚ)
    (x : Fin n → ℝ) : quadVal (symH H) c d x = quadVal H c d x := by
  unfold quadVal; rw [quadForm_symH]

lemma sm_symH {n W : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (hH : ∀ i j, Sm (1 * W ^ 1) (H i j)) :
    ∀ i j, Sm (2 * W + 2) (symH H i j) := by
  intro i j
  have := sm_div (sm_add (hH i j) (hH j i)) (show Sm 1 (2 : ℚ) by constructor <;> simp)
  simp only [symH]
  exact this.mono (by ring_nf; omega)

end MIQPT1
/-! ### Part R2 -/

open MIQPInNP.SmallSol
open scoped BigOperators Pointwise Topology

namespace MIQPT1

/-- Real version of the expansion `Q(x + t v)` for symmetric `H` (copy used for Theorem 3). -/
lemma qv_add_smul_sym {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (hsym : H.transpose = H)
    (c : Fin n → ℚ) (d : ℚ) (y r : Fin n → ℝ) (t : ℝ) :
    quadVal H c d (y + t • r) = quadVal H c d y +
      t * (2 * (∑ u, ∑ v, y u * (H u v : ℝ) * r v) + ∑ u, (c u : ℝ) * r u) +
      t ^ 2 * quadForm H r := by
  have hs : ∀ u v, H v u = H u v := fun u v => by
    have := congrFun (congrFun hsym u) v; simpa [Matrix.transpose_apply] using this
  have swap : ∑ u, ∑ v, r u * (H u v : ℝ) * y v = ∑ u, ∑ v, y u * (H u v : ℝ) * r v := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
    rw [hs u v]; ring
  have p1 : ∑ i, ∑ j, (y + t • r) i * (H i j : ℝ) * (y + t • r) j = ∑ i, ∑ j, y i * (H i j : ℝ) * y j +
      t * ∑ i, ∑ j, (y i * (H i j : ℝ) * r j + r i * (H i j : ℝ) * y j) +
      t ^ 2 * ∑ i, ∑ j, r i * (H i j : ℝ) * r j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have p2 : ∑ i, (c i : ℝ) * (y + t • r) i = ∑ i, (c i : ℝ) * y i + t * ∑ i, (c i : ℝ) * r i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have p3 : ∑ i, ∑ j, (y i * (H i j : ℝ) * r j + r i * (H i j : ℝ) * y j) =
      2 * ∑ u, ∑ v, y u * (H u v : ℝ) * r v := by
    simp only [Finset.sum_add_distrib]; rw [swap]; ring
  unfold quadVal quadForm
  rw [p1, p2, p3]; ring

/-- First-order optimality along directions of the minimal face. -/
lemma stationary {m n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (hsym : H.transpose = H)
    (c : Fin n → ℚ) (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (xs : Fin n → ℝ)
    (hxs : xs ∈ polyhedron A b) (hmin : ∀ y ∈ polyhedron A b, quadVal H c 0 xs ≤ quadVal H c 0 y)
    (v : Fin n → ℝ) (hv : ∀ i, ∑ j, (A i j : ℝ) * xs j = b i → ∑ j, (A i j : ℝ) * v j = 0) :
    2 * (∑ u, ∑ w, xs u * (H u w : ℝ) * v w) + ∑ u, (c u : ℝ) * v u = 0 := by
  set G := 2 * (∑ u, ∑ w, xs u * (H u w : ℝ) * v w) + ∑ u, (c u : ℝ) * v u with hG
  have hφ : (fun t : ℝ => quadVal H c 0 (xs + t • v)) =
      fun t => quadVal H c 0 xs + t * G + t ^ 2 * quadForm H v := by
    funext t; rw [qv_add_smul_sym H hsym]
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), xs + t • v ∈ polyhedron A b := by
    have : ∀ i, ∀ᶠ t in 𝓝 (0 : ℝ), ∑ j, (A i j : ℝ) * (xs + t • v) j ≤ b i := by
      intro i
      have e : ∀ t : ℝ, ∑ j, (A i j : ℝ) * (xs + t • v) j =
          ∑ j, (A i j : ℝ) * xs j + t * ∑ j, (A i j : ℝ) * v j := by
        intro t
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      by_cases htight : ∑ j, (A i j : ℝ) * xs j = b i
      · refine Filter.Eventually.of_forall (fun t => ?_)
        rw [e, hv i htight, htight]; simp
      · have hlt : ∑ j, (A i j : ℝ) * xs j < b i := lt_of_le_of_ne (hxs i) htight
        have hc : Continuous fun t : ℝ => ∑ j, (A i j : ℝ) * xs j + t * ∑ j, (A i j : ℝ) * v j := by
          fun_prop
        have := hc.tendsto 0
        simp only [zero_mul, add_zero] at this
        have h2 := this.eventually (gt_mem_nhds hlt)
        exact h2.mono (fun t ht => by rw [e]; exact ht.le)
    exact Filter.eventually_all.mpr this
  have hloc : IsLocalMin (fun t : ℝ => quadVal H c 0 (xs + t • v)) 0 := by
    refine hev.mono (fun t ht => ?_)
    simp only [zero_smul, add_zero]
    exact hmin _ ht
  rw [hφ] at hloc
  have hd : HasDerivAt (fun t : ℝ => quadVal H c 0 xs + t * G + t ^ 2 * quadForm H v) G 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t * G) G 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const G
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2 * quadForm H v) 0 0 := by
      simpa using (hasDerivAt_pow 2 (0 : ℝ)).mul_const (quadForm H v)
    have h3 : HasDerivAt (fun t : ℝ => quadVal H c 0 xs + t * G + t ^ 2 * quadForm H v) (G + 0) 0 :=
      (h1.const_add (quadVal H c 0 xs)).add h2
    rw [add_zero] at h3
    exact h3
  exact hloc.hasDerivAt_eq_zero hd

/-- Lagrange multipliers: a functional vanishing on the kernel of the tight rows is a
combination of them. -/
lemma multipliers {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (I : Finset (Fin m)) (g : Fin n → ℝ)
    (hg : ∀ v : Fin n → ℝ, (∀ i ∈ I, ∑ j, (A i j : ℝ) * v j = 0) → ∑ u, g u * v u = 0) :
    ∃ y : Fin m → ℝ, ∀ u, g u = ∑ i, (if i ∈ I then (A i u : ℝ) else 0) * y i := by
  classical
  set AI : Matrix (Fin m) (Fin n) ℝ := Matrix.of fun i j => if i ∈ I then (A i j : ℝ) else 0
    with hAI
  set f := Matrix.mulVecLin AI with hf
  let φ : Module.Dual ℝ (Fin n → ℝ) :=
    { toFun := fun v => ∑ u, g u * v u
      map_add' := fun v w => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun a v => by simp [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring) }
  have hφ : φ ∈ (LinearMap.ker f).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    rw [LinearMap.mem_ker] at hw
    show ∑ u, g u * w u = 0
    apply hg
    intro i hi
    have := congrFun hw i
    simpa [hf, hAI, Matrix.mulVec, dotProduct, hi] using this
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hφ
  obtain ⟨ψ, hψ⟩ := hφ
  refine ⟨fun i => ψ (fun j => if i = j then 1 else 0), fun u => ?_⟩
  have h1 : g u = φ (Pi.single u (1 : ℝ)) := by
    show g u = ∑ w, g w * (Pi.single u (1 : ℝ) : Fin n → ℝ) w
    rw [Finset.sum_eq_single u] <;> simp (config := { contextual := true })
  rw [h1, ← hψ, LinearMap.dualMap_apply, LinearMap.pi_apply_eq_sum_univ]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [smul_eq_mul]
  congr 1
  simp only [hf, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hAI, Matrix.of_apply]
  rw [Finset.sum_eq_single u]
  · simp
  · intro j _ hj; simp [Pi.single_apply, hj]
  · simp

end MIQPT1
/-! ### Part R3 -/

open MIQPInNP.SmallSol
open scoped BigOperators Pointwise

namespace MIQPT1

lemma lin_grad {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (x v : Fin n → ℝ) :
    2 * (∑ u, ∑ w, x u * (H u w : ℝ) * v w) + ∑ w, (c w : ℝ) * v w =
      ∑ w, (2 * ∑ u, x u * (H u w : ℝ) + c w) * v w := by
  have h : ∑ u, ∑ w, x u * (H u w : ℝ) * v w = ∑ w, (∑ u, x u * (H u w : ℝ)) * v w := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun w _ => by rw [Finset.sum_mul])
  rw [h, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun w _ => by ring)

lemma grad_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (I : Finset (Fin m)) (g : Fin n → ℝ)
    (y : Fin m → ℝ) (hg : ∀ w, g w = ∑ i, (if i ∈ I then (A i w : ℝ) else 0) * y i)
    (δ : Fin n → ℝ) (hδ : ∀ i ∈ I, ∑ j, (A i j : ℝ) * δ j = 0) : ∑ w, g w * δ w = 0 := by
  simp_rw [hg, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  by_cases hi : i ∈ I
  · have := hδ i hi
    simp only [hi, if_true]
    calc ∑ w, (A i w : ℝ) * y i * δ w = y i * ∑ w, (A i w : ℝ) * δ w := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ = 0 := by rw [this, mul_zero]
  · simp [hi]

/-- Theorem 3, second part: a QP whose minimum is attained has a small optimal solution. -/
theorem thm3b : ∃ g : Polynomial ℕ, ∀ (n m : ℕ) (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ)
    (d : ℚ) (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
    (∃ x ∈ polyhedron A b, ∀ y ∈ polyhedron A b, quadVal H c 0 x ≤ quadVal H c 0 y) →
    ∃ xh : Fin n → ℚ, toReal xh ∈ polyhedron A b ∧
      (∀ y ∈ polyhedron A b, quadVal H c 0 (toReal xh) ≤ quadVal H c 0 y) ∧
      vecSize xh ≤ g.eval (instSize H c d A b) := by
  classical
  refine ⟨Polynomial.X * (2 * ((2 * Polynomial.X) * (2 * Polynomial.X) + (2 * Polynomial.X) *
    (2 * (Polynomial.X + 3 * (Polynomial.X * Polynomial.X) +
      (Polynomial.X * Polynomial.X * (2 * Polynomial.X + 4) + 3 * (Polynomial.X * Polynomial.X)) +
      2 * (Polynomial.X * Polynomial.X * (2 * (2 * Polynomial.X + 3) + 4) +
        Polynomial.X * Polynomial.X * (2 * Polynomial.X + 4)) +
      (3 * Polynomial.X + Polynomial.X * (2 * Polynomial.X + 4))))) + 4), ?_⟩
  rintro n m H c d A b ⟨xs, hxs, hmin⟩
  set Hs := symH H with hHs
  have hsym : Hs.transpose = Hs := symH_transpose H
  have hmin' : ∀ y ∈ polyhedron A b, quadVal Hs c 0 xs ≤ quadVal Hs c 0 y := by
    intro y hy; rw [quadVal_symH, quadVal_symH]; exact hmin y hy
  set I := Finset.univ.filter (fun i => ∑ j, (A i j : ℝ) * xs j = b i) with hI
  set gs : Fin n → ℝ := fun w => 2 * ∑ u, xs u * (Hs u w : ℝ) + c w with hgs
  have hgsv : ∀ v : Fin n → ℝ, (∀ i ∈ I, ∑ j, (A i j : ℝ) * v j = 0) → ∑ w, gs w * v w = 0 := by
    intro v hv
    have := stationary Hs hsym c A b xs hxs hmin' v (fun i hi => hv i (by simp [hI, hi]))
    rw [lin_grad] at this
    exact this
  obtain ⟨ys, hys⟩ := multipliers A I gs hgsv
  -- the rational system
  set AI : Matrix (Fin m) (Fin n) ℚ := fun i j => if i ∈ I then A i j else 0 with hAI
  set bI : Fin m → ℚ := fun i => if i ∈ I then b i else 0 with hbI
  set Hst : Matrix (Fin n) (Fin n) ℚ := fun w u => 2 * Hs u w with hHst
  set AIt : Matrix (Fin n) (Fin m) ℚ := fun w i => AI i w with hAIt
  set B := stack (stack (hcat A (0 : Matrix (Fin m) (Fin m) ℚ)) (hcat (-AI) (0 : Matrix (Fin m) (Fin m) ℚ)))
    (stack (hcat Hst (-AIt)) (hcat (-Hst) AIt)) with hB
  set e := stackv (stackv b (-bI)) (stackv (-c) c) with he
  have hmemB : ∀ z : Fin (n + m) → ℝ, z ∈ polyhedron B e ↔
      (∀ i, ∑ j, (A i j : ℝ) * z (Fin.castAdd m j) ≤ b i) ∧
      (∀ i, -(∑ j, (AI i j : ℝ) * z (Fin.castAdd m j)) ≤ -(bI i : ℝ)) ∧
      (∀ w, ∑ u, (Hst w u : ℝ) * z (Fin.castAdd m u) - ∑ i, (AIt w i : ℝ) * z (Fin.natAdd n i)
        ≤ -(c w : ℝ)) ∧
      (∀ w, -(∑ u, (Hst w u : ℝ) * z (Fin.castAdd m u)) + ∑ i, (AIt w i : ℝ) * z (Fin.natAdd n i)
        ≤ (c w : ℝ)) := by
    intro z
    rw [hB, he, polyhedron_stack, polyhedron_stack, polyhedron_stack]
    simp only [polyhedron, Set.mem_inter_iff, Set.mem_setOf_eq, hcat_row]
    simp [Matrix.neg_apply, Finset.sum_neg_distrib, sub_eq_add_neg, and_assoc]
  -- the real solution (xs, ys)
  set zs : Fin (n + m) → ℝ := Fin.append xs ys with hzs
  have hzsx : ∀ j, zs (Fin.castAdd m j) = xs j := fun j => Fin.append_left _ _ _
  have hzsy : ∀ i, zs (Fin.natAdd n i) = ys i := fun i => Fin.append_right _ _ _
  have hstat_s : ∀ w, ∑ u, (Hst w u : ℝ) * xs u - ∑ i, (AIt w i : ℝ) * ys i = -(c w : ℝ) := by
    intro w
    have h1 := hys w
    simp only [hgs] at h1
    have e1 : ∑ u, (Hst w u : ℝ) * xs u = 2 * ∑ u, xs u * (Hs u w : ℝ) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun u _ => ?_); simp [hHst]; ring
    have e2 : ∑ i, (AIt w i : ℝ) * ys i = ∑ i, (if i ∈ I then (A i w : ℝ) else 0) * ys i := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases hi : i ∈ I <;> simp [hAIt, hAI, hi]
    rw [e1, e2]; linarith
  have hzs : zs ∈ polyhedron B e := by
    rw [hmemB]
    simp only [hzsx, hzsy]
    refine ⟨fun i => hxs i, fun i => ?_, fun w => le_of_eq (hstat_s w),
      fun w => by have := hstat_s w; linarith⟩
    by_cases hi : i ∈ I
    · have : ∑ j, (A i j : ℝ) * xs j = b i := by simpa [hI] using hi
      simp [hAI, hbI, hi, this]
    · simp [hAI, hbI, hi]
  obtain ⟨zq, hzq, hzS⟩ := small_feasible B e zs hzs
  set xh : Fin n → ℚ := fun u => zq (Fin.castAdd m u) with hxh
  set yh : Fin m → ℚ := fun i => zq (Fin.natAdd n i) with hyh
  obtain ⟨h1, h2, h3, h4⟩ := (hmemB _).mp hzq
  have hP : toReal xh ∈ polyhedron A b := fun i => by simpa [toReal, hxh] using h1 i
  have hT : ∀ i ∈ I, ∑ j, (A i j : ℝ) * toReal xh j = b i := by
    intro i hi
    have a1 := h1 i; have a2 := h2 i
    have e : ∀ j, (AI i j : ℝ) = A i j := by intro j; simp [hAI, hi]
    have eb : (bI i : ℝ) = b i := by simp [hbI, hi]
    simp only [e, eb] at a2
    have : ∀ j, toReal xh j = toReal zq (Fin.castAdd m j) := fun j => rfl
    simp only [this]
    linarith
  have hstat_h : ∀ w, 2 * ∑ u, toReal xh u * (Hs u w : ℝ) + c w =
      ∑ i, (if i ∈ I then (A i w : ℝ) else 0) * toReal yh i := by
    intro w
    have a3 := h3 w; have a4 := h4 w
    have e1 : ∑ u, (Hst w u : ℝ) * (toReal zq) (Fin.castAdd m u) =
        2 * ∑ u, toReal xh u * (Hs u w : ℝ) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun u _ => ?_)
      simp [hHst, toReal, hxh]; ring
    have e2 : ∑ i, (AIt w i : ℝ) * (toReal zq) (Fin.natAdd n i) =
        ∑ i, (if i ∈ I then (A i w : ℝ) else 0) * toReal yh i := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases hi : i ∈ I <;> simp [hAIt, hAI, hi, toReal, hyh]
    rw [e1, e2] at a3 a4
    linarith
  refine ⟨xh, hP, ?_, ?_⟩
  · -- optimality
    set δ := toReal xh - xs with hδ
    have hAδ : ∀ i ∈ I, ∑ j, (A i j : ℝ) * δ j = 0 := by
      intro i hi
      have := hT i hi
      have h' : ∑ j, (A i j : ℝ) * xs j = b i := by simpa [hI] using hi
      simp only [hδ, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      linarith
    have E1 := qv_add_smul_sym Hs hsym c 0 xs δ 1
    have E2 := qv_add_smul_sym Hs hsym c 0 (toReal xh) (-δ) 1
    rw [lin_grad] at E1 E2
    have L1 : ∑ w, (2 * ∑ u, xs u * (Hs u w : ℝ) + c w) * δ w = 0 :=
      grad_zero A I gs ys hys δ hAδ
    have L2 : ∑ w, (2 * ∑ u, toReal xh u * (Hs u w : ℝ) + c w) * (-δ) w = 0 := by
      have := grad_zero A I _ (toReal yh) hstat_h (-δ) (fun i hi => by
        simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, hAδ i hi, neg_zero])
      exact this
    have hQ : quadForm Hs (-δ) = quadForm Hs δ := by
      rw [show -δ = (-1 : ℝ) • δ by simp, quadForm_smul]; ring
    have ex1 : xs + (1 : ℝ) • δ = toReal xh := by simp [hδ]
    have ex2 : toReal xh + (1 : ℝ) • (-δ) = xs := by simp [hδ]
    rw [ex1, L1] at E1
    rw [ex2, L2, hQ] at E2
    have heq : quadVal Hs c 0 (toReal xh) = quadVal Hs c 0 xs := by nlinarith
    intro y hy
    rw [← quadVal_symH H c 0 (toReal xh), ← hHs, heq, hHs, quadVal_symH]
    exact hmin y hy
  · -- size
    obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = instSize H c d A b := ⟨_, rfl⟩
    rw [← hΦ]
    have hnc := n_le_vecSize c
    have hmb := n_le_vecSize b
    have hHΦ : matSize H ≤ Φ := by rw [hΦ]; unfold instSize; omega
    have hAΦ : matSize A ≤ Φ := by rw [hΦ]; unfold instSize; omega
    have hbΦ : vecSize b ≤ Φ := by rw [hΦ]; unfold instSize; omega
    have hcΦ : vecSize c ≤ Φ := by rw [hΦ]; unfold instSize; omega
    have hnΦ : n ≤ Φ := by omega
    have hmΦ : m ≤ Φ := by omega
    have hHS : ∀ i j, Sm (1 * Φ ^ 1) (H i j) := sm_W_of_matSize H hHΦ
    have hAS : ∀ i j, Sm (1 * Φ ^ 1) (A i j) := sm_W_of_matSize A hAΦ
    have hbS : ∀ i, Sm (1 * Φ ^ 1) (b i) := sm_W_of_vecSize b hbΦ
    have hHsS := sm_symH H hHS
    have hHstS : ∀ w u, Sm (2 * Φ + 3) (Hst w u) := fun w u =>
      (sm_mul (show Sm 1 (2 : ℚ) by constructor <;> simp) (hHsS u w)).mono (by omega)
    have hAIS : ∀ i j, Sm Φ (AI i j) := fun i j => by
      by_cases hi : i ∈ I
      · simpa [hAI, hi] using hAS i j
      · simpa [hAI, hi] using sm_zero Φ
    have hbIS : ∀ i, Sm Φ (bI i) := fun i => by
      by_cases hi : i ∈ I
      · simpa [hbI, hi] using hbS i
      · simpa [hbI, hi] using sm_zero Φ
    have b1 : matSize (hcat A (0 : Matrix (Fin m) (Fin m) ℚ)) ≤ Φ + 3 * (Φ * Φ) := by
      rw [matSize_hcat, matSize_zero]
      have := Nat.mul_le_mul hmΦ hmΦ
      omega
    have b2 : matSize (hcat (-AI) (0 : Matrix (Fin m) (Fin m) ℚ)) ≤
        Φ * Φ * (2 * Φ + 4) + 3 * (Φ * Φ) := by
      rw [matSize_hcat, matSize_zero, matSize_neg]
      have h1 := matSize_le_of_sm AI hAIS
      have h2 : m * n * (2 * Φ + 4) ≤ Φ * Φ * (2 * Φ + 4) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hmΦ hnΦ)
      have := Nat.mul_le_mul hmΦ hmΦ
      omega
    have b3 : matSize (hcat Hst (-AIt)) ≤
        Φ * Φ * (2 * (2 * Φ + 3) + 4) + Φ * Φ * (2 * Φ + 4) := by
      rw [matSize_hcat, matSize_neg]
      have h1 := matSize_le_of_sm Hst hHstS
      have h2 := matSize_le_of_sm AIt (fun w i => hAIS i w)
      have h3 : n * n * (2 * (2 * Φ + 3) + 4) ≤ Φ * Φ * (2 * (2 * Φ + 3) + 4) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hnΦ hnΦ)
      have h4 : n * m * (2 * Φ + 4) ≤ Φ * Φ * (2 * Φ + 4) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hnΦ hmΦ)
      omega
    have b4 : matSize (hcat (-Hst) AIt) ≤
        Φ * Φ * (2 * (2 * Φ + 3) + 4) + Φ * Φ * (2 * Φ + 4) := by
      rw [matSize_hcat, matSize_neg]
      have h1 := matSize_le_of_sm Hst hHstS
      have h2 := matSize_le_of_sm AIt (fun w i => hAIS i w)
      have h3 : n * n * (2 * (2 * Φ + 3) + 4) ≤ Φ * Φ * (2 * (2 * Φ + 3) + 4) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hnΦ hnΦ)
      have h4 : n * m * (2 * Φ + 4) ≤ Φ * Φ * (2 * Φ + 4) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hnΦ hmΦ)
      omega
    have b5 : vecSize e ≤ 3 * Φ + Φ * (2 * Φ + 4) := by
      rw [he, vecSize_stackv, vecSize_stackv, vecSize_stackv]
      have hneg : ∀ {k : ℕ} (v : Fin k → ℚ), vecSize (-v) = vecSize v := by
        intro k v; unfold vecSize; simp [bitSize_neg]
      rw [hneg, hneg]
      have h1 := vecSize_le_of_sm bI hbIS
      have h2 : m * (2 * Φ + 4) ≤ Φ * (2 * Φ + 4) := Nat.mul_le_mul_right _ hmΦ
      omega
    have hSB : matSize B + vecSize e ≤ Φ + 3 * (Φ * Φ) +
        (Φ * Φ * (2 * Φ + 4) + 3 * (Φ * Φ)) +
        2 * (Φ * Φ * (2 * (2 * Φ + 3) + 4) + Φ * Φ * (2 * Φ + 4)) +
        (3 * Φ + Φ * (2 * Φ + 4)) := by
      rw [hB, matSize_stack, matSize_stack, matSize_stack]
      omega
    have hE : M5Core.alpha (n + m) (matSize B + vecSize e) ≤
        (2 * Φ) * (2 * Φ) + (2 * Φ) * (2 * (Φ + 3 * (Φ * Φ) +
        (Φ * Φ * (2 * Φ + 4) + 3 * (Φ * Φ)) +
        2 * (Φ * Φ * (2 * (2 * Φ + 3) + 4) + Φ * Φ * (2 * Φ + 4)) +
        (3 * Φ + Φ * (2 * Φ + 4)))) := by
      unfold M5Core.alpha
      have hnm : n + m ≤ 2 * Φ := by omega
      gcongr
    have hxS : ∀ u, Sm (M5Core.alpha (n + m) (matSize B + vecSize e)) (xh u) := fun u => hzS _
    refine (vecSize_le_of_sm xh hxS).trans ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    exact Nat.mul_le_mul hnΦ (by omega)

end MIQPT1
/-! ### Part Bsm -/

open MIQPInNP.SmallSol
open scoped BigOperators

namespace MIQPT1

/-- Small minimiser of a quadratic over a bounded polyhedron (from Theorem 3). -/
theorem small_min : ∃ G : Polynomial ℕ, ∀ (n m : ℕ) (H : Matrix (Fin n) (Fin n) ℚ)
    (c : Fin n → ℚ) (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
    Bornology.IsBounded (polyhedron A b) → ∀ x ∈ polyhedron A b,
    ∃ xh : Fin n → ℚ, toReal xh ∈ polyhedron A b ∧
      quadVal H c 0 (toReal xh) ≤ quadVal H c 0 x ∧
      vecSize xh ≤ G.eval (matSize H + vecSize c + matSize A + vecSize b) := by
  obtain ⟨g, h2⟩ := thm3b
  refine ⟨g.comp (Polynomial.X + 2), ?_⟩
  intro n m H c A b hb x hx
  obtain ⟨y, hy, hmin⟩ := (isCompact_polyhedron A b hb).exists_isMinOn ⟨x, hx⟩
    (continuous_quadVal H c 0).continuousOn
  obtain ⟨xh, hxh, hopt, hsz⟩ := h2 n m H c 0 A b ⟨y, hy, fun z hz => hmin hz⟩
  refine ⟨xh, hxh, hopt x hx, ?_⟩
  have : instSize H c 0 A b = matSize H + vecSize c + matSize A + vecSize b + 2 := by
    unfold instSize; rw [bitSize_zero]; ring
  rw [this] at hsz
  simpa [Polynomial.eval_comp] using hsz

end MIQPT1
/-! ### Part E -/

open MIQPInNP.SmallSol
open scoped BigOperators Pointwise

namespace MIQPT1

/-- Case 1, first ingredient: a small rational recession direction of negative curvature. -/
theorem small_neg_ray : ∃ G : Polynomial ℕ, ∀ (n m : ℕ) (H : Matrix (Fin n) (Fin n) ℚ)
    (A : Matrix (Fin m) (Fin n) ℚ), IsPointedPoly A → (∃ r ∈ recCone A, quadForm H r < 0) →
    ∃ r : Fin n → ℚ, toReal r ∈ recCone A ∧ qf H r < 0 ∧
      vecSize r ≤ G.eval (matSize H + matSize A + m) := by
  obtain ⟨G0, hG0⟩ := small_min
  refine ⟨G0.comp (7 * Polynomial.X), ?_⟩
  rintro n m H A hA ⟨r0, hr0, hneg⟩
  set B : ℝ := ∑ i, |∑ j, (A i j : ℝ) * r0 j| with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  set t : ℝ := 1 / (1 + B) with ht
  have ht0 : 0 < t := by positivity
  have htB : t * B ≤ 1 := by
    rw [ht, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
  have hy : t • r0 ∈ polyhedron (stack A (-A)) (stackv 0 1) := by
    rw [polyhedron_stack]
    refine ⟨recCone_smul A t ht0.le r0 hr0, fun i => ?_⟩
    simp only [Pi.one_apply, Rat.cast_one, Matrix.neg_apply, Rat.cast_neg, neg_mul,
      Finset.sum_neg_distrib, Pi.smul_apply, smul_eq_mul]
    have e : ∑ j, (A i j : ℝ) * (t * r0 j) = t * ∑ j, (A i j : ℝ) * r0 j := by
      rw [Finset.mul_sum]; congr 1; ext j; ring
    rw [e]
    have h1 : -(∑ j, (A i j : ℝ) * r0 j) ≤ B :=
      (neg_le_abs _).trans (Finset.single_le_sum (f := fun i => |∑ j, (A i j : ℝ) * r0 j|)
        (fun i _ => abs_nonneg _) (Finset.mem_univ i))
    nlinarith
  have hbd := pointed_poly_bounded A hA _ le_rfl
  obtain ⟨xh, hxh, hval, hsz⟩ := hG0 n (m + m) H 0 (stack A (-A)) (stackv 0 1) hbd _ hy
  refine ⟨xh, ?_, ?_, ?_⟩
  · rw [polyhedron_stack] at hxh; exact hxh.1
  · rw [quadVal_zero_zero, quadVal_zero_zero, quadForm_smul, quadForm_eq_qf] at hval
    have : t ^ 2 * quadForm H r0 < 0 := mul_neg_of_pos_of_neg (by positivity) hneg
    exact_mod_cast hval.trans_lt this
  · rw [matSize_stack, matSize_neg, vecSize_stackv, vecSize_zero, vecSize_zero, vecSize_one]
      at hsz
    refine hsz.trans ?_
    simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    apply peval_mono
    have := n_le_matSize_sq H
    omega

/-- Case 1, second ingredient: a small mixed-integer point of a pointed polyhedron
(from Proposition 4 and Theorem 3). -/
theorem small_mixed : ∃ G : Polynomial ℕ, ∀ (p q m : ℕ) (A : Matrix (Fin m) (Fin (p + q)) ℚ)
    (b : Fin m → ℚ), IsPointedPoly A → ∀ x ∈ polyhedron A b, IsMixedInt p x →
    ∃ xh : Fin (p + q) → ℚ, toReal xh ∈ polyhedron A b ∧ IsMixedInt p (toReal xh) ∧
      vecSize xh ≤ G.eval (matSize A + vecSize b + (p + q)) := by
  obtain ⟨g4, h4⟩ := proposition_4
  obtain ⟨G0, hG0⟩ := small_min
  refine ⟨G0.comp (6 * Polynomial.X ^ 2 + g4), ?_⟩
  intro p q m A b hA x hx hxm
  obtain ⟨N, mi, Ai, bi, KK, heq, hP, -, -⟩ := h4 p q m A b (fun _ => hA)
  have hx' : x ∈ {x | x ∈ polyhedron A b ∧ IsMixedInt p x} := ⟨hx, hxm⟩
  rw [heq] at hx'
  simp only [Set.mem_iUnion] at hx'
  obtain ⟨i, R, hR, hxR⟩ := hx'
  obtain ⟨y, hy, z, -, -⟩ := Set.mem_add.mp hxR
  obtain ⟨xh, hxh, -, hsz⟩ := hG0 (p + q) (mi i) 0 0 (Ai i) (bi i) (hP i).1 y hy
  have hmem : toReal xh ∈ {x | x ∈ polyhedron A b ∧ IsMixedInt p x} := by
    rw [heq]
    simp only [Set.mem_iUnion]
    exact ⟨i, R, hR, Set.mem_add.mpr ⟨_, hxh, 0, AddSubmonoid.zero_mem _, add_zero _⟩⟩
  refine ⟨xh, hmem.1, hmem.2, ?_⟩
  rw [matSize_zero, vecSize_zero] at hsz
  refine hsz.trans ?_
  simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_ofNat]
  apply peval_mono
  have h1 := (hP i).2
  have h2 : g4.eval (matSize A + vecSize b) ≤ g4.eval (matSize A + vecSize b + (p + q)) :=
    peval_mono _ (by omega)
  have h3 : 3 * ((p + q) * (p + q)) + 3 * (p + q) ≤
      6 * (matSize A + vecSize b + (p + q)) ^ 2 := by
    set s := matSize A + vecSize b
    have e1 := Nat.le_mul_self (p + q)
    have e2 : (p + q) * (p + q) ≤ (s + (p + q)) ^ 2 := by
      rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
    omega
  omega

end MIQPT1
/-! ### Part F -/

open MIQPInNP.SmallSol
open scoped BigOperators Pointwise

namespace MIQPT1

lemma quad_ineq (a β γ t : ℚ) (ha : a < 0) (ht : (|β| + |γ|) / |a| + 1 ≤ t) :
    γ + t * β + t ^ 2 * a ≤ 0 := by
  have hapos : 0 < |a| := abs_pos.mpr ha.ne
  have haabs : |a| = -a := abs_of_neg ha
  have hy0 : 0 ≤ (|β| + |γ|) / |a| := by positivity
  have hT1 : (1 : ℚ) ≤ t := by linarith
  have hya : (|β| + |γ|) / |a| * |a| = |β| + |γ| := by field_simp
  have e1 : t * |a| ≥ |β| + |γ| := by
    have := mul_le_mul_of_nonneg_right ht hapos.le
    nlinarith
  have e2 : t ^ 2 * |a| ≥ t * |β| + |γ| := by
    have : t * (t * |a|) ≥ t * (|β| + |γ|) := mul_le_mul_of_nonneg_left e1 (by linarith)
    nlinarith [abs_nonneg γ, abs_nonneg β]
  have h1 := le_abs_self γ
  have h2 : t * β ≤ t * |β| := mul_le_mul_of_nonneg_left (le_abs_self β) (by linarith)
  rw [haabs] at e2
  have h3 : t ^ 2 * a = -(t ^ 2 * -a) := by ring
  linarith

lemma k_bound (a β γ : ℚ) (E : ℕ) (hE1 : 1 ≤ E) (ha : Sm (5 * E) a) (ha0 : a ≠ 0)
    (hβ : Sm (13 * E) β) (hγ : Sm (11 * E) γ) : ⌈(|β| + |γ|) / |a|⌉₊ + 1 ≤ 2 ^ (20 * E) := by
  have hapos : 0 < |a| := abs_pos.mpr ha0
  have hinv : 1 / |a| ≤ 2 ^ (5 * E) := by
    have := sm_abs_ge ha ha0
    rw [div_le_iff₀ hapos]
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hb1 := sm_abs_le hβ
  have hg1 := sm_abs_le hγ
  have hy0 : 0 ≤ (|β| + |γ|) / |a| := by positivity
  have hyb : (|β| + |γ|) / |a| ≤ (2 ^ (13 * E) + 2 ^ (11 * E)) * 2 ^ (5 * E) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (by linarith) hinv (by positivity) (by positivity)
  have hk' : ((⌈(|β| + |γ|) / |a|⌉₊ + 1 : ℕ) : ℚ) ≤ (|β| + |γ|) / |a| + 2 := by
    push_cast; linarith [Nat.ceil_lt_add_one hy0]
  set u : ℚ := 2 ^ E with hu_def
  have hu : (2 : ℚ) ≤ u := by
    calc (2 : ℚ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ E := pow_le_pow_right₀ (by norm_num) hE1
  have p13 : (2 : ℚ) ^ (13 * E) = u ^ 13 := by rw [hu_def, ← pow_mul, mul_comm]
  have p11 : (2 : ℚ) ^ (11 * E) = u ^ 11 := by rw [hu_def, ← pow_mul, mul_comm]
  have p5 : (2 : ℚ) ^ (5 * E) = u ^ 5 := by rw [hu_def, ← pow_mul, mul_comm]
  have p20 : (2 : ℚ) ^ (20 * E) = u ^ 20 := by rw [hu_def, ← pow_mul, mul_comm]
  rw [p13, p11, p5] at hyb
  have hfin : (u ^ 13 + u ^ 11) * u ^ 5 + 2 ≤ u ^ 20 := by
    have h1 : u ^ 16 ≤ u ^ 18 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h2 : (1 : ℚ) ≤ u ^ 18 := one_le_pow₀ (by linarith)
    have h3 : u ^ 20 = u ^ 2 * u ^ 18 := by ring
    have h4 : (4 : ℚ) ≤ u ^ 2 := by nlinarith
    have e : (u ^ 13 + u ^ 11) * u ^ 5 = u ^ 18 + u ^ 16 := by ring
    rw [e, h3]; nlinarith
  have : ((⌈(|β| + |γ|) / |a|⌉₊ + 1 : ℕ) : ℚ) ≤ 2 ^ (20 * E) := by
    rw [p20]; linarith
  exact_mod_cast this

/-- Case 1 of the proof of Theorem 1 (pointed polyhedron, negative curvature direction). -/
theorem case1 : ∃ G : Polynomial ℕ, ∀ (n p m : ℕ), p ≤ n →
    ∀ (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (d : ℚ)
      (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ), IsPointedPoly A →
      (feasSet p H c d A b).Nonempty → (∃ r ∈ recCone A, quadForm H r < 0) →
      ∃ x0 : Fin n → ℚ, toReal x0 ∈ feasSet p H c d A b ∧
        vecSize x0 ≤ G.eval (instSize H c d A b) := by
  obtain ⟨G2, h2⟩ := small_neg_ray
  obtain ⟨G3, h3⟩ := small_mixed
  refine ⟨Polynomial.X * (48 * (Polynomial.X + G2 + G3 + 1) ^ 3 + 4), ?_⟩
  intro n p m hpn H c d A b hA ⟨x, hxF⟩ hneg
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hpn
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = instSize H c d A b := ⟨_, rfl⟩
  rw [← hΦ]
  obtain ⟨r, hrrec, hrneg, hrsz⟩ := h2 _ m H A hA hneg
  obtain ⟨xt, hxtP, hxtM, hxtsz⟩ := h3 p q m A b hA x hxF.2.1 hxF.2.2
  obtain ⟨W, hWdef⟩ : ∃ W, W = Φ + G2.eval Φ + G3.eval Φ + 1 := ⟨_, rfl⟩
  have hm : m ≤ vecSize b := n_le_vecSize b
  have hnc : p + q ≤ vecSize c := n_le_vecSize c
  have hΦ1 : matSize H + matSize A + m ≤ Φ := by rw [hΦ]; unfold instSize; omega
  have hΦ2 : matSize A + vecSize b + (p + q) ≤ Φ := by rw [hΦ]; unfold instSize; omega
  have hΦH : matSize H ≤ Φ := by rw [hΦ]; unfold instSize; omega
  have hΦc : vecSize c ≤ Φ := by rw [hΦ]; unfold instSize; omega
  have hΦd : bitSize d ≤ Φ := by rw [hΦ]; unfold instSize; omega
  have hW1 : 1 ≤ W := by omega
  have hnW : p + q ≤ W := by omega
  have hrW : vecSize r ≤ W := by
    have := peval_mono G2 hΦ1; omega
  have hxtW : vecSize xt ≤ W := by
    have := peval_mono G3 hΦ2; omega
  have hr := sm_W_of_vecSize r hrW
  have hxt := sm_W_of_vecSize xt hxtW
  have hH := sm_W_of_matSize H (hΦH.trans (by omega : Φ ≤ W))
  have hc := sm_W_of_vecSize c (hΦc.trans (by omega : Φ ≤ W))
  have hd : Sm (1 * W ^ 1) d := (sm_bitSize d).mono (by simp; omega)
  set a := qf H r with ha_def
  set β := lin H c xt r with hβ_def
  set γ := qv H c d xt with hγ_def
  have ha := sm_qf hW1 hnW H r hH hr
  have hβ := sm_lin hW1 hnW H c xt r hH hc hxt hr
  have hγ := sm_qv hW1 hnW H c xt d hH hc hd hxt
  set D := ∏ i, (r i).den with hD
  have hD1 : 1 ≤ D := Nat.one_le_iff_ne_zero.mpr
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (r i).den_nz))
  have hDle : D ≤ 2 ^ W := (prod_den_le r).trans (two_pow_mono hrW)
  have hDdvd : ∀ i, (r i).den ∣ D := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  clear_value D
  set k : ℕ := ⌈(|β| + |γ|) / |a|⌉₊ + 1 with hk
  have ha0 : a < 0 := hrneg
  have hkle : k ≤ 2 ^ (20 * W ^ 3) :=
    k_bound a β γ (W ^ 3) (Nat.one_le_pow _ _ hW1) ha ha0.ne hβ hγ
  have hky : (|β| + |γ|) / |a| + 1 ≤ (k : ℚ) := by
    rw [hk]; push_cast; linarith [Nat.le_ceil ((|β| + |γ|) / |a|)]
  clear_value k
  set t : ℕ := k * D with ht
  have htk : (k : ℚ) ≤ t := by
    rw [ht]; push_cast
    have : (1 : ℚ) ≤ D := by exact_mod_cast hD1
    have : (0 : ℚ) ≤ k := by positivity
    nlinarith
  clear_value t
  set x0 : Fin (p + q) → ℚ := xt + (t : ℚ) • r with hx0
  have hval : qv H c d x0 ≤ 0 := by
    rw [hx0, qv_add_smul]
    have := quad_ineq a β γ t ha0 (hky.trans htk)
    rw [← hβ_def, ← hγ_def, ← ha_def]
    linarith
  have hkS : Sm (20 * W ^ 3) (k : ℚ) := sm_nat k hkle
  have hDS : Sm (1 * W ^ 3) (D : ℚ) := sm_nat D (hDle.trans (two_pow_mono (by
    calc W = W ^ 1 := (pow_one W).symm
      _ ≤ W ^ 3 := Nat.pow_le_pow_right hW1 (by norm_num)
      _ = 1 * W ^ 3 := (one_mul _).symm)))
  have htS : Sm (21 * W ^ 3) (t : ℚ) := by
    have := smW_mul hkS hDS
    rw [ht]; push_cast; exact this.mono (le_of_eq (by ring))
  have hx0S : ∀ i, Sm (24 * W ^ 3) (x0 i) := by
    intro i
    have h1 := smW_lift hW1 (hr i) 1 3 le_rfl (by norm_num)
    have h2 := smW_lift hW1 (hxt i) 1 3 le_rfl (by norm_num)
    have := smW_add hW1 h2 (smW_mul htS h1)
    rw [hx0, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact this.mono (by omega)
  refine ⟨x0, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [quadVal_eq_qv]; exact_mod_cast hval
  · exact mem_polyhedron_add_smul A b xt r t (by positivity) hxtP hrrec
  · apply mixed_add xt _ hxtM
    intro i _
    obtain ⟨z, hz⟩ := int_of_den_dvd (r i) D (hDdvd i)
    refine ⟨k * z, ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, ht]; push_cast
    rw [mul_assoc, hz]
  · have hv := vecSize_le_of_sm x0 hx0S
    refine hv.trans ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one, Polynomial.eval_ofNat]
    rw [← hWdef]
    have : p + q ≤ Φ := by omega
    calc (p + q) * (2 * (24 * W ^ 3) + 4) ≤ Φ * (2 * (24 * W ^ 3) + 4) :=
          Nat.mul_le_mul_right _ this
      _ = Φ * (48 * W ^ 3 + 4) := by ring

end MIQPT1
/-! ### Part G -/

open MIQPInNP.SmallSol
open scoped BigOperators Pointwise

namespace MIQPT1

lemma quadVal_add_smul_real {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (hsym : H.transpose = H)
    (c : Fin n → ℚ) (d : ℚ) (y r : Fin n → ℝ) (t : ℝ) :
    quadVal H c d (y + t • r) = quadVal H c d y +
      t * (2 * (∑ u, ∑ v, y u * (H u v : ℝ) * r v) + ∑ u, (c u : ℝ) * r u) +
      t ^ 2 * quadForm H r := by
  have hs : ∀ u v, H v u = H u v := fun u v => by
    have := congrFun (congrFun hsym u) v; simpa [Matrix.transpose_apply] using this
  have swap : ∑ u, ∑ v, r u * (H u v : ℝ) * y v = ∑ u, ∑ v, y u * (H u v : ℝ) * r v := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
    rw [hs u v]; ring
  have p1 : ∑ i, ∑ j, (y + t • r) i * (H i j : ℝ) * (y + t • r) j = ∑ i, ∑ j, y i * (H i j : ℝ) * y j +
      t * ∑ i, ∑ j, (y i * (H i j : ℝ) * r j + r i * (H i j : ℝ) * y j) +
      t ^ 2 * ∑ i, ∑ j, r i * (H i j : ℝ) * r j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have p2 : ∑ i, (c i : ℝ) * (y + t • r) i = ∑ i, (c i : ℝ) * y i + t * ∑ i, (c i : ℝ) * r i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have p3 : ∑ i, ∑ j, (y i * (H i j : ℝ) * r j + r i * (H i j : ℝ) * y j) =
      2 * ∑ u, ∑ v, y u * (H u v : ℝ) * r v := by
    simp only [Finset.sum_add_distrib]; rw [swap]; ring
  unfold quadVal quadForm
  rw [p1, p2, p3]; ring

lemma intCone_image_subset_range {n d : ℕ} (v : Fin d → Fin n → ℝ) (S : Set (Fin d)) :
    intCone (v '' S) ⊆ intCone (Set.range v) := by
  unfold intCone
  exact AddSubmonoid.closure_mono (Set.image_subset_range v S)

lemma intCone_add_mem {n : ℕ} (S : Set (Fin n → ℝ)) {x y : Fin n → ℝ} (hx : x ∈ intCone S)
    (hy : y ∈ intCone S) : x + y ∈ intCone S := AddSubmonoid.add_mem _ hx hy

lemma intCone_nsmul_mem {n : ℕ} (S : Set (Fin n → ℝ)) {x : Fin n → ℝ} (hx : x ∈ S) (k : ℕ) :
    k • x ∈ intCone S := AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure hx) k

/-- Removing the zero-curvature directions does not increase the objective (Case 2b). -/
lemma elim_J {n d : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (hsym : H.transpose = H) (c : Fin n → ℚ)
    (dd : ℚ) (P : Set (Fin n → ℝ)) (s : Fin d → Fin n → ℝ) (p : Fin n → ℝ) (hp : p ∈ P)
    (μ : Fin d → ℕ)
    (hJ : ∀ i, quadForm H (s i) = 0 → ∀ y ∈ P + intCone (s '' {j | j ≠ i}),
      0 ≤ 2 * (∑ u, ∑ v, y u * (H u v : ℝ) * s i v) + ∑ u, (c u : ℝ) * s i u) :
    ∀ T : Finset (Fin d), (∀ i ∈ T, quadForm H (s i) = 0) →
      quadVal H c dd (p + ∑ j, (if j ∈ T then 0 else μ j) • s j) ≤
        quadVal H c dd (p + ∑ j, μ j • s j) := by
  classical
  intro T
  induction T using Finset.induction_on with
  | empty => intro _; simp
  | insert i T hiT ih =>
    intro hT
    have hi : quadForm H (s i) = 0 := hT i (Finset.mem_insert_self i T)
    have ih' := ih (fun j hj => hT j (Finset.mem_insert_of_mem hj))
    set ν : Fin d → ℕ := fun j => if j ∈ insert i T then 0 else μ j with hν
    set y := p + ∑ j, ν j • s j with hy
    have hsplit : p + ∑ j, (if j ∈ T then 0 else μ j) • s j = y + (μ i : ℝ) • s i := by
      rw [hy, add_assoc]
      congr 1
      have : ∀ j, (if j ∈ T then 0 else μ j) • s j = ν j • s j + (if j = i then μ i else 0) • s j := by
        intro j
        by_cases hj : j = i
        · subst hj; simp [hν, hiT]
        · have : j ∈ insert i T ↔ j ∈ T := by simp [hj]
          simp [hν, this, hj]
      rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single i]
      · simp [Nat.cast_smul_eq_nsmul]
      · intro j _ hj; simp [hj]
      · simp
    have hyP : y ∈ P + intCone (s '' {j | j ≠ i}) := by
      refine Set.mem_add.mpr ⟨p, hp, ∑ j, ν j • s j, ?_, rfl⟩
      rw [mem_intCone_image]
      exact ⟨ν, fun j hj => by simp at hj; simp [hν, hj], rfl⟩
    have hlin := hJ i hi y hyP
    have := quadVal_add_smul_real H hsym c dd y (s i) (μ i)
    rw [hi, mul_zero, add_zero] at this
    have hmu : (0 : ℝ) ≤ μ i := by positivity
    calc quadVal H c dd (p + ∑ j, ν j • s j) = quadVal H c dd y := by rw [hy]
      _ ≤ quadVal H c dd (y + (μ i : ℝ) • s i) := by
          rw [this]; nlinarith
      _ = quadVal H c dd (p + ∑ j, (if j ∈ T then 0 else μ j) • s j) := by rw [hsplit]
      _ ≤ _ := ih'

lemma vecSize_single_le {n : ℕ} (u : Fin n) (a : ℚ) (ha : Sm 0 a) :
    vecSize (Pi.single u a : Fin n → ℚ) ≤ n * 4 := by
  have := vecSize_le_of_sm (E := 0) (Pi.single u a : Fin n → ℚ) (fun i => by
    by_cases h : i = u
    · subst h; simpa using ha
    · simpa [h] using sm_zero 0)
  simpa using this

lemma sm0_one : Sm 0 (1 : ℚ) := by constructor <;> simp
lemma sm0_neg_one : Sm 0 (-1 : ℚ) := sm_neg sm0_one

/-- Coordinates of a bounded rational polyhedron are bounded by `2^poly`. -/
theorem poly_coord_bound : ∃ G : Polynomial ℕ, ∀ (n m : ℕ) (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ), Bornology.IsBounded (polyhedron A b) → ∀ x ∈ polyhedron A b, ∀ u,
    |x u| ≤ 2 ^ (G.eval (matSize A + vecSize b + n)) := by
  obtain ⟨G0, hG0⟩ := small_min
  refine ⟨G0.comp (7 * Polynomial.X ^ 2), ?_⟩
  intro n m A b hb x hx u
  have key : ∀ (a : ℚ), Sm 0 a → ∃ xh : Fin n → ℚ, (a : ℝ) * (xh u : ℝ) ≤ a * x u ∧
      vecSize xh ≤ G0.eval (7 * (matSize A + vecSize b + n) ^ 2) := by
    intro a ha
    obtain ⟨xh, -, hle, hsz⟩ := hG0 n m 0 (Pi.single u a) A b hb x hx
    refine ⟨xh, ?_, ?_⟩
    · unfold quadVal quadForm at hle
      simp only [Matrix.zero_apply, Rat.cast_zero, mul_zero, zero_mul, Finset.sum_const_zero,
        zero_add, add_zero] at hle
      rw [Finset.sum_eq_single u (fun j _ hj => by simp [hj]) (by simp),
        Finset.sum_eq_single u (fun j _ hj => by simp [hj]) (by simp)] at hle
      simpa [toReal] using hle
    · refine hsz.trans (peval_mono _ ?_)
      rw [matSize_zero]
      have := vecSize_single_le u a ha
      set S := matSize A + vecSize b + n
      have h1 : n ≤ S := by omega
      have h2 : n * n ≤ S ^ 2 := by rw [sq]; exact Nat.mul_le_mul h1 h1
      have h3 : S ≤ S ^ 2 := by rw [sq]; exact Nat.le_mul_self S
      omega
  obtain ⟨x1, h1, s1⟩ := key 1 sm0_one
  obtain ⟨x2, h2, s2⟩ := key (-1) sm0_neg_one
  have b1 := sm_abs_le_real ((sm_of_vecSize x1 u).mono s1)
  have b2 := sm_abs_le_real ((sm_of_vecSize x2 u).mono s2)
  simp only [Rat.cast_one, one_mul, Rat.cast_neg, neg_mul, neg_le_neg_iff] at h1 h2
  simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_ofNat]
  rw [abs_le] at b1 b2 ⊢
  push_cast at b1 b2 ⊢
  constructor <;> linarith

lemma mem_translate {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (w : Fin n → ℚ)
    (y : Fin n → ℝ) : y ∈ polyhedron A (b + A.mulVec w) ↔ y - toReal w ∈ polyhedron A b := by
  simp only [polyhedron, Set.mem_setOf_eq, Pi.add_apply, Matrix.mulVec, dotProduct, toReal,
    Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  push_cast
  constructor <;> intro h i <;> have := h i <;> linarith

lemma bounded_translate {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) (w : Fin n → ℚ)
    (hb : Bornology.IsBounded (polyhedron A b)) :
    Bornology.IsBounded (polyhedron A (b + A.mulVec w)) := by
  rw [isBounded_iff_forall_norm_le] at hb ⊢
  obtain ⟨C, hC⟩ := hb
  refine ⟨C + ‖toReal w‖, fun y hy => ?_⟩
  have := hC _ ((mem_translate A b w y).mp hy)
  calc ‖y‖ = ‖(y - toReal w) + toReal w‖ := by rw [sub_add_cancel]
    _ ≤ ‖y - toReal w‖ + ‖toReal w‖ := norm_add_le _ _
    _ ≤ C + ‖toReal w‖ := by linarith

lemma card_le_of_li {n d : ℕ} (v : Fin d → Fin n → ℝ) (h : LinearIndependent ℝ v) : d ≤ n := by
  have := h.fintype_card_le_finrank
  simpa using this

end MIQPT1
/-! ### Part H -/

open MIQPInNP.SmallSol
open scoped BigOperators Pointwise

namespace MIQPT1

lemma lin_eq_of_symm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (hsym : H.transpose = H)
    (c x r : Fin n → ℚ) :
    ((lin H c x r : ℚ) : ℝ) = 2 * (∑ u, ∑ v, toReal x u * (H u v : ℝ) * toReal r v) +
      ∑ u, (c u : ℝ) * toReal r u := by
  have hs : ∀ u v, H v u = H u v := fun u v => by
    have := congrFun (congrFun hsym u) v; simpa [Matrix.transpose_apply] using this
  have swap : ∑ u, ∑ v, r u * H u v * x v = ∑ u, ∑ v, x u * H u v * r v := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
    rw [hs u v]; ring
  have : lin H c x r = 2 * (∑ u, ∑ v, x u * H u v * r v) + ∑ u, c u * r u := by
    unfold lin; simp only [Finset.sum_add_distrib]; rw [swap]; ring
  rw [this]; unfold toReal; push_cast; rfl

lemma toReal_add_nsmul {n : ℕ} (x r : Fin n → ℚ) (k : ℕ) :
    toReal (x + (k : ℚ) • r) = toReal x + k • toReal r := by
  ext u; simp [toReal, nsmul_eq_mul]

lemma mu_bound (a l : ℚ) (E : ℕ) (hE1 : 1 ≤ E) (ha : Sm (11 * E) a) (hl0 : l ≠ 0)
    (hl : Sm (13 * E) l) : ⌈a / |l|⌉₊ ≤ 2 ^ (25 * E) := by
  have hlpos : 0 < |l| := abs_pos.mpr hl0
  rcases le_or_gt a 0 with h | h
  · have : a / |l| ≤ 0 := div_nonpos_of_nonpos_of_nonneg h hlpos.le
    rw [Nat.ceil_eq_zero.mpr this]; exact Nat.zero_le _
  have hinv : 1 / |l| ≤ 2 ^ (13 * E) := by
    have := sm_abs_ge hl hl0
    rw [div_le_iff₀ hlpos]
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have ha1 : a ≤ 2 ^ (11 * E) := (le_abs_self a).trans (sm_abs_le ha)
  have hy : a / |l| ≤ 2 ^ (11 * E) * 2 ^ (13 * E) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul ha1 hinv (by positivity) (by positivity)
  have hc : ((⌈a / |l|⌉₊ : ℕ) : ℚ) ≤ 2 ^ (11 * E) * 2 ^ (13 * E) + 1 := by
    linarith [Nat.ceil_lt_add_one (show 0 ≤ a / |l| by positivity)]
  have h2 : (2 : ℚ) ^ (11 * E) * 2 ^ (13 * E) + 1 ≤ 2 ^ (25 * E) := by
    rw [← pow_add]
    have h1 : (1 : ℚ) ≤ 2 ^ (24 * E) := one_le_pow₀ (by norm_num)
    have : (2 : ℚ) ^ (25 * E) = 2 ^ E * 2 ^ (24 * E) := by rw [← pow_add]; ring_nf
    have h3 : (2 : ℚ) ≤ 2 ^ E := by
      calc (2 : ℚ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ E := pow_le_pow_right₀ (by norm_num) hE1
    rw [this, show 11 * E + 13 * E = 24 * E by ring]
    nlinarith
  exact_mod_cast hc.trans h2

/-- Subcase 2a (Claim 1). -/
theorem core3a : ∃ G : Polynomial ℕ, ∀ (n mP d : ℕ) (A' : Matrix (Fin mP) (Fin n) ℚ)
    (b' : Fin mP → ℚ) (s : Fin d → Fin n → ℚ) (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ)
    (dd : ℚ), H.transpose = H → Bornology.IsBounded (polyhedron A' b') →
    LinearIndependent ℝ (fun j => toReal (s j)) →
    (∃ i, quadForm H (toReal (s i)) = 0 ∧
      ∃ y ∈ polyhedron A' b' + intCone ((fun j => toReal (s j)) '' {j | j ≠ i}),
        2 * (∑ u, ∑ v, y u * (H u v : ℝ) * toReal (s i) v) + ∑ u, (c u : ℝ) * toReal (s i) u
          < 0) →
    ∃ x0 : Fin n → ℚ,
      toReal x0 ∈ polyhedron A' b' + intCone (Set.range fun j => toReal (s j)) ∧
      quadVal H c dd (toReal x0) ≤ 0 ∧
      vecSize x0 ≤ G.eval (matSize A' + vecSize b' + ∑ j, vecSize (s j) + matSize H +
        vecSize c + bitSize dd) := by
  obtain ⟨g1, h1⟩ := claim_1
  refine ⟨Polynomial.X * (56 * (Polynomial.X + g1 + 1) ^ 3 + 4), ?_⟩
  rintro n mP d A' b' s H c dd hsym hb hli ⟨i, hQi, y, hy, hlin⟩
  obtain ⟨xt, hxtmem, hxtneg, hxtsz⟩ := h1 n mP d A' b' s H c i hb hli hQi ⟨y, hy, hlin⟩
  obtain ⟨S, hS⟩ : ∃ S, S = matSize A' + vecSize b' + ∑ j, vecSize (s j) + matSize H +
      vecSize c + bitSize dd := ⟨_, rfl⟩
  rw [← hS]
  obtain ⟨W, hW⟩ : ∃ W, W = S + g1.eval S + 1 := ⟨_, rfl⟩
  have hsi : vecSize (s i) ≤ ∑ j, vecSize (s j) :=
    Finset.single_le_sum (f := fun j => vecSize (s j)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have hnc := n_le_vecSize c
  have hW1 : 1 ≤ W := by omega
  have hnW : n ≤ W := by omega
  have hxtW : vecSize xt ≤ W := by
    have := peval_mono g1 (show matSize A' + vecSize b' + ∑ j, vecSize (s j) + matSize H +
      vecSize c ≤ S by omega)
    omega
  have hxt := sm_W_of_vecSize xt hxtW
  have hsW := sm_W_of_vecSize (s i) (show vecSize (s i) ≤ W by omega)
  have hH := sm_W_of_matSize H (show matSize H ≤ W by omega)
  have hc := sm_W_of_vecSize c (show vecSize c ≤ W by omega)
  have hd : Sm (1 * W ^ 1) dd := (sm_bitSize dd).mono (by simp; omega)
  set ℓ := lin H c xt (s i) with hℓ
  have hℓneg : ℓ < 0 := by
    have := lin_eq_of_symm H hsym c xt (s i)
    rw [← hℓ] at this
    have h2 : ((ℓ : ℚ) : ℝ) < 0 := by rw [this]; exact hxtneg
    exact_mod_cast h2
  have hqf : qf H (s i) = 0 := by
    have := quadForm_eq_qf H (s i); rw [hQi] at this; exact_mod_cast this.symm
  set a := qv H c dd xt with ha_def
  have haS := sm_qv hW1 hnW H c xt dd hH hc hd hxt
  have hℓS := sm_lin hW1 hnW H c xt (s i) hH hc hxt hsW
  set μ : ℕ := ⌈a / |ℓ|⌉₊ with hμ
  have hμb : μ ≤ 2 ^ (25 * W ^ 3) :=
    mu_bound a ℓ (W ^ 3) (Nat.one_le_pow _ _ hW1) haS hℓneg.ne hℓS
  have hμa : a / |ℓ| ≤ μ := Nat.le_ceil _
  clear_value μ
  set x0 := xt + (μ : ℚ) • s i with hx0
  have hval : qv H c dd x0 ≤ 0 := by
    rw [hx0, qv_add_smul, hqf, mul_zero, add_zero, ← ha_def, ← hℓ]
    have hl : 0 < |ℓ| := abs_pos.mpr hℓneg.ne
    have habs : |ℓ| = -ℓ := abs_of_neg hℓneg
    have : a ≤ μ * |ℓ| := by
      have := mul_le_mul_of_nonneg_right hμa hl.le
      rwa [div_mul_cancel₀ _ hl.ne'] at this
    rw [habs] at this
    linarith
  have hμS : Sm (25 * W ^ 3) (μ : ℚ) := sm_nat μ hμb
  have hx0S : ∀ u, Sm (28 * W ^ 3) (x0 u) := by
    intro u
    have h1 := smW_lift hW1 (hsW u) 1 3 le_rfl (by norm_num)
    have h2 := smW_lift hW1 (hxt u) 1 3 le_rfl (by norm_num)
    have := smW_add hW1 h2 (smW_mul hμS h1)
    rw [hx0, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact this.mono (by omega)
  refine ⟨x0, ?_, ?_, ?_⟩
  · rw [hx0, toReal_add_nsmul]
    obtain ⟨p, hp, z, hz, hpz⟩ := Set.mem_add.mp hxtmem
    rw [← hpz, add_assoc]
    refine Set.mem_add.mpr ⟨p, hp, _, intCone_add_mem _ (intCone_image_subset_range _ _ hz)
      (intCone_nsmul_mem _ (Set.mem_range_self (f := fun j => toReal (s j)) i) μ), rfl⟩
  · rw [quadVal_eq_qv]; exact_mod_cast hval
  · refine (vecSize_le_of_sm x0 hx0S).trans ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one, Polynomial.eval_ofNat]
    rw [← hW]
    have : n ≤ S := by omega
    calc n * (2 * (28 * W ^ 3) + 4) ≤ S * (2 * (28 * W ^ 3) + 4) := Nat.mul_le_mul_right _ this
      _ = S * (56 * W ^ 3 + 4) := by ring

end MIQPT1
/-! ### Part I -/

open MIQPInNP.SmallSol
open scoped BigOperators Pointwise

namespace MIQPT1

lemma abs_le_euclidNorm {n : ℕ} (x : Fin n → ℝ) (u : Fin n) : |x u| ≤ euclidNorm x := by
  unfold euclidNorm
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ u)

lemma quadVal_d {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (d : ℚ) (y : Fin n → ℝ) :
    quadVal H c d y = quadVal H c 0 y + d := by
  unfold quadVal; simp

lemma toReal_sum_smul {n d : ℕ} (μ : Fin d → ℕ) (s : Fin d → Fin n → ℚ) :
    toReal (∑ j, (μ j : ℚ) • s j) = ∑ j, μ j • toReal (s j) := by
  ext u; simp [toReal, Finset.sum_apply, nsmul_eq_mul]

lemma dot_bound {n W : ℕ} (f : Fin n → ℚ) (y : Fin n → ℝ) (B : ℝ) (hB : 0 ≤ B) (hn : n ≤ W)
    (hf : ∀ k, Sm (1 * W ^ 1) (f k)) (hy : ∀ k, |y k| ≤ B) :
    |∑ k, (f k : ℝ) * y k| ≤ W * 2 ^ W * B := by
  calc |∑ k, (f k : ℝ) * y k| ≤ ∑ k, |(f k : ℝ) * y k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, (2 : ℝ) ^ W * B := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        rw [abs_mul]
        have := sm_abs_le_real (hf k)
        simp only [one_mul, pow_one] at this
        exact mul_le_mul this (hy k) (abs_nonneg _) (by positivity)
    _ = n * (2 ^ W * B) := by simp
    _ ≤ W * (2 ^ W * B) := by
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (by positivity)
    _ = W * 2 ^ W * B := by ring

/-- Subcase 2b (Claim 2 and the final small-solution step). -/
theorem core3b : ∃ G : Polynomial ℕ, ∀ (n mP d : ℕ) (A' : Matrix (Fin mP) (Fin n) ℚ)
    (b' : Fin mP → ℚ) (s : Fin d → Fin n → ℚ) (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ)
    (dd : ℚ) (f : Fin n → ℚ), H.transpose = H → Bornology.IsBounded (polyhedron A' b') →
    LinearIndependent ℝ (fun j => toReal (s j)) →
    (∀ x ∈ cone ((fun j => toReal (s j)) '' {j | quadForm H (toReal (s j)) ≠ 0}),
      x ≠ 0 → 0 < quadForm H x) →
    (∀ j, 0 < ∑ k, (f k : ℝ) * toReal (s j) k) →
    (∀ i, quadForm H (toReal (s i)) = 0 →
      ∀ y ∈ polyhedron A' b' + intCone ((fun j => toReal (s j)) '' {j | j ≠ i}),
        0 ≤ 2 * (∑ u, ∑ v, y u * (H u v : ℝ) * toReal (s i) v) + ∑ u, (c u : ℝ) * toReal (s i) u) →
    (∃ x ∈ polyhedron A' b' + intCone (Set.range fun j => toReal (s j)), quadVal H c dd x ≤ 0) →
    ∃ x0 : Fin n → ℚ,
      toReal x0 ∈ polyhedron A' b' + intCone (Set.range fun j => toReal (s j)) ∧
      quadVal H c dd (toReal x0) ≤ 0 ∧
      vecSize x0 ≤ G.eval (matSize A' + vecSize b' + ∑ j, vecSize (s j) + matSize H +
        vecSize c + bitSize dd + vecSize f) := by
  obtain ⟨g2, h2⟩ := claim_2
  obtain ⟨Gc, hGc⟩ := poly_coord_bound
  obtain ⟨G0, hG0⟩ := small_min
  refine ⟨G0.comp ((Polynomial.X + g2 + Gc + 1) +
    (Polynomial.X + g2 + Gc + 1) * (26 * (Polynomial.X + g2 + Gc + 1) ^ 4 + 4)), ?_⟩
  intro n mP d A' b' s H c dd f hsym hb hli hpos hf hJ ⟨x, hx, hxQ⟩
  obtain ⟨S, hS⟩ : ∃ S, S = matSize A' + vecSize b' + ∑ j, vecSize (s j) + matSize H +
      vecSize c + bitSize dd + vecSize f := ⟨_, rfl⟩
  rw [← hS]
  obtain ⟨W, hW⟩ : ∃ W, W = S + g2.eval S + Gc.eval S + 1 := ⟨_, rfl⟩
  have hnc := n_le_vecSize c
  have hmb := n_le_vecSize b'
  have hdn : d ≤ n := card_le_of_li _ hli
  have hW1 : 1 ≤ W := by omega
  have hnW : n ≤ W := by omega
  have hdW : d ≤ W := by omega
  have hsW : ∀ j, vecSize (s j) ≤ W := fun j => by
    have := Finset.single_le_sum (f := fun j => vecSize (s j)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
    omega
  have hfW : vecSize f ≤ W := by omega
  have hsS := fun j => sm_W_of_vecSize (s j) (hsW j)
  have hfS := sm_W_of_vecSize f hfW
  have hAS := sm_W_of_matSize A' (show matSize A' ≤ W by omega)
  have hbS := sm_W_of_vecSize b' (show vecSize b' ≤ W by omega)
  obtain ⟨p, hp, z, hz, rfl⟩ := Set.mem_add.mp hx
  obtain ⟨μ, rfl⟩ := (mem_intCone_range _ _).mp hz
  set sR : Fin d → Fin n → ℝ := fun j => toReal (s j) with hsR
  set μ' : Fin d → ℕ := fun j => if quadForm H (sR j) = 0 then 0 else μ j with hμ'
  have hx'Q : quadVal H c dd (p + ∑ j, μ' j • sR j) ≤ 0 := by
    have := elim_J H hsym c dd (polyhedron A' b') sR p hp μ hJ
      (Finset.univ.filter (fun j => quadForm H (sR j) = 0)) (by simp)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this.trans hxQ
  have hx'mem : p + ∑ j, μ' j • sR j ∈
      polyhedron A' b' + intCone (sR '' {j | quadForm H (sR j) ≠ 0}) := by
    refine Set.mem_add.mpr ⟨p, hp, _, (mem_intCone_image _ _ _).mpr ⟨μ', fun j hj => ?_, rfl⟩, rfl⟩
    simp only [Set.mem_setOf_eq, not_not] at hj
    simp [hμ', hj]
  obtain ⟨v, hvsz, hvb⟩ := h2 n mP d A' b' s H c dd hb hli hpos
  have hnorm := hvb _ hx'mem hx'Q
  -- bounds on v and on the coordinates
  have hvW : bitSize v ≤ W := by
    have := peval_mono g2 (show matSize A' + vecSize b' + ∑ j, vecSize (s j) + matSize H +
      vecSize c + bitSize dd ≤ S by omega)
    omega
  have hv2 : (v : ℝ) ≤ 2 ^ W := by
    have := sm_abs_le_real ((sm_bitSize v).mono hvW)
    exact (le_abs_self _).trans this
  have hpW : ∀ u, |p u| ≤ 2 ^ W := by
    intro u
    have := hGc n mP A' b' hb p hp u
    refine this.trans (pow_le_pow_right₀ (by norm_num) ?_)
    have := peval_mono Gc (show matSize A' + vecSize b' + n ≤ S by omega)
    omega
  have hx'W : ∀ u, |(p + ∑ j, μ' j • sR j) u| ≤ 2 ^ W := fun u =>
    ((abs_le_euclidNorm _ u).trans hnorm).trans hv2
  -- bound on the coefficients
  have hφ : ∀ j, Sm ((1 + 1 + 1) * W ^ (1 + 1)) (∑ k, f k * s j k) := fun j =>
    smW_sum hW1 hnW _ (fun k => smW_mul (hfS k) (hsS j k))
  have hφeq : ∀ j, ∑ k, (f k : ℝ) * sR j k = ((∑ k, f k * s j k : ℚ) : ℝ) := by
    intro j; simp [hsR, toReal]
  have hμ'b : ∀ j, μ' j ≤ 2 ^ (7 * W ^ 2) := by
    intro j
    have hlin : ∑ k, (f k : ℝ) * (p + ∑ j, μ' j • sR j) k =
        ∑ k, (f k : ℝ) * p k + ∑ j, (μ' j : ℝ) * ∑ k, (f k : ℝ) * sR j k := by
      have e : ∀ k, (p + ∑ j, μ' j • sR j) k = p k + ∑ j, (μ' j : ℝ) * sR j k := by
        intro k; simp [Finset.sum_apply, nsmul_eq_mul]
      rw [Finset.sum_congr rfl (fun k _ => by rw [e k])]
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
      ring
    have hnonneg : ∀ i, 0 ≤ (μ' i : ℝ) * ∑ k, (f k : ℝ) * sR i k :=
      fun i => mul_nonneg (by positivity) (hf i).le
    have hsingle : (μ' j : ℝ) * ∑ k, (f k : ℝ) * sR j k ≤
        ∑ i, (μ' i : ℝ) * ∑ k, (f k : ℝ) * sR i k :=
      Finset.single_le_sum (f := fun i => (μ' i : ℝ) * ∑ k, (f k : ℝ) * sR i k)
        (fun i _ => hnonneg i) (Finset.mem_univ j)
    have hb1 := dot_bound f _ _ (by positivity) hnW hfS hx'W
    have hb2 := dot_bound f p _ (by positivity) hnW hfS hpW
    have hφpos := hf j
    rw [hφeq] at hφpos
    have hφlow := sm_abs_ge (hφ j) (by exact_mod_cast hφpos.ne')
    rw [abs_of_pos (by exact_mod_cast hφpos)] at hφlow
    have hφlow' : (1 : ℝ) / 2 ^ (3 * W ^ 2) ≤ ((∑ k, f k * s j k : ℚ) : ℝ) := by
      have e : (1 + 1 + 1) * W ^ (1 + 1) = 3 * W ^ 2 := by ring
      rw [e] at hφlow
      have h' : ((1 / 2 ^ (3 * W ^ 2) : ℚ) : ℝ) ≤ ((∑ k, f k * s j k : ℚ) : ℝ) := by
        exact_mod_cast hφlow
      simpa using h'
    have hmain : (μ' j : ℝ) * ((∑ k, f k * s j k : ℚ) : ℝ) ≤ 2 * (W * 2 ^ W * 2 ^ W) := by
      rw [← hφeq]
      have := abs_le.mp hb1; have := abs_le.mp hb2
      linarith
    have hW2 : (W : ℝ) ≤ 2 ^ W := by exact_mod_cast (Nat.lt_two_pow_self).le
    have hpow : (2 : ℝ) * (W * 2 ^ W * 2 ^ W) * 2 ^ (3 * W ^ 2) ≤ 2 ^ (7 * W ^ 2) := by
      have e1 : (2 : ℝ) * (W * 2 ^ W * 2 ^ W) ≤ 2 ^ (3 * W + 1) := by
        calc (2 : ℝ) * (W * 2 ^ W * 2 ^ W) ≤ 2 * (2 ^ W * 2 ^ W * 2 ^ W) := by gcongr
          _ = 2 ^ (3 * W + 1) := by
            rw [show 3 * W + 1 = W + W + W + 1 by ring, pow_succ, pow_add, pow_add]; ring
      have e2 : 3 * W + 1 ≤ 4 * W ^ 2 := by nlinarith
      calc (2 : ℝ) * (W * 2 ^ W * 2 ^ W) * 2 ^ (3 * W ^ 2) ≤ 2 ^ (3 * W + 1) * 2 ^ (3 * W ^ 2) :=
            by gcongr
        _ = 2 ^ (3 * W + 1 + 3 * W ^ 2) := (pow_add _ _ _).symm
        _ ≤ 2 ^ (7 * W ^ 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hφpos' : (0 : ℝ) < ((∑ k, f k * s j k : ℚ) : ℝ) := by exact_mod_cast hφpos
    have key : (μ' j : ℝ) ≤ 2 ^ (7 * W ^ 2) := by
      have h3 : (1 : ℝ) / 2 ^ (3 * W ^ 2) ≤ ((∑ k, f k * s j k : ℚ) : ℝ) := hφlow'
      have h4 : (μ' j : ℝ) * (1 / 2 ^ (3 * W ^ 2)) ≤ 2 * (W * 2 ^ W * 2 ^ W) :=
        (mul_le_mul_of_nonneg_left h3 (by positivity)).trans hmain
      have h5 : (μ' j : ℝ) ≤ 2 * (W * 2 ^ W * 2 ^ W) * 2 ^ (3 * W ^ 2) := by
        rw [mul_one_div, div_le_iff₀ (by positivity)] at h4; exact h4
      exact h5.trans hpow
    exact_mod_cast key
  -- the translation vector
  set w : Fin n → ℚ := ∑ j, (μ' j : ℚ) • s j with hw
  have hwR : toReal w = ∑ j, μ' j • sR j := toReal_sum_smul μ' s
  have hwS : ∀ u, Sm (9 * W ^ 3) (w u) := by
    intro u
    have hμS : ∀ j, Sm (7 * W ^ 2) (μ' j : ℚ) := fun j => sm_nat _ (hμ'b j)
    have : ∀ j, Sm ((7 + 1) * W ^ 2) ((μ' j : ℚ) * s j u) := fun j =>
      smW_mul (hμS j) (smW_lift hW1 (hsS j u) 1 2 le_rfl (by norm_num))
    have h := smW_sum hW1 hdW _ this
    have e : w u = ∑ j, (μ' j : ℚ) * s j u := by simp [hw, Finset.sum_apply]
    rw [e]; exact h.mono (le_of_eq (by ring))
  set b'' := b' + A'.mulVec w with hb''
  have hb''S : ∀ i, Sm (13 * W ^ 4) (b'' i) := by
    intro i
    have : ∀ j, Sm ((1 + 9) * W ^ 3) (A' i j * w j) := fun j =>
      smW_mul (smW_lift hW1 (hAS i j) 1 3 le_rfl (by norm_num)) (hwS j)
    have h := smW_sum hW1 hnW _ this
    have h' := smW_add hW1 (smW_lift hW1 (hbS i) 1 4 le_rfl (by norm_num))
      (h.mono (le_of_eq (by ring)) : Sm (11 * W ^ 4) _)
    have e : b'' i = b' i + ∑ j, A' i j * w j := by
      simp [hb'', Matrix.mulVec, dotProduct]
    rw [e]; exact h'.mono (by omega)
  have hx'in : p + ∑ j, μ' j • sR j ∈ polyhedron A' b'' := by
    rw [hb'', mem_translate, hwR, add_sub_cancel_right]; exact hp
  obtain ⟨xh, hxh, hxhle, hxhsz⟩ := hG0 n mP H c A' b'' (bounded_translate A' b' w hb) _ hx'in
  refine ⟨xh, ?_, ?_, ?_⟩
  · have h1 := (mem_translate A' b' w (toReal xh)).mp hxh
    refine Set.mem_add.mpr ⟨_, h1, toReal w, ?_, sub_add_cancel _ _⟩
    rw [hwR]; exact (mem_intCone_range _ _).mpr ⟨μ', rfl⟩
  · rw [quadVal_d]; rw [quadVal_d] at hx'Q; linarith
  · refine hxhsz.trans ?_
    rw [Polynomial.eval_comp]
    apply peval_mono
    have hv := vecSize_le_of_sm b'' hb''S
    simp only [ Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
    rw [← hW]
    have : mP * (2 * (13 * W ^ 4) + 4) ≤ W * (26 * W ^ 4 + 4) := by
      calc mP * (2 * (13 * W ^ 4) + 4) ≤ W * (2 * (13 * W ^ 4) + 4) :=
            Nat.mul_le_mul_right _ (by omega)
        _ = W * (26 * W ^ 4 + 4) := by ring
    omega

end MIQPT1
/-! ### Part J -/

open MIQPInNP.SmallSol
open scoped BigOperators Pointwise

namespace MIQPT1

open Matrix

/-- The Gram matrix of integral vectors. -/
def gram {n d : ℕ} (rr : Fin d → Fin n → ℤ) : Matrix (Fin d) (Fin d) ℤ :=
  fun k l => ∑ u, rr k u * rr l u

/-- The real matrix whose columns are the vectors `rr k`. -/
def colMat {n d : ℕ} (rr : Fin d → Fin n → ℤ) : Matrix (Fin n) (Fin d) ℝ :=
  fun u k => (rr k u : ℝ)

lemma gram_map {n d : ℕ} (rr : Fin d → Fin n → ℤ) :
    (Int.castRingHom ℝ).mapMatrix (gram rr) = (colMat rr).transpose * colMat rr := by
  ext k l; simp [gram, colMat, Matrix.mul_apply]

lemma gram_det_ne_zero {n d : ℕ} (rr : Fin d → Fin n → ℤ)
    (hli : LinearIndependent ℝ (fun k => fun u => (rr k u : ℝ))) : (gram rr).det ≠ 0 := by
  classical
  intro h0
  have h1 : ((Int.castRingHom ℝ).mapMatrix (gram rr)).det = 0 := by
    rw [← RingHom.map_det, h0, map_zero]
  rw [gram_map] at h1
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h1
  have h2 : (colMat rr *ᵥ v) ⬝ᵥ (colMat rr *ᵥ v) = 0 := by
    have : v ⬝ᵥ (((colMat rr).transpose * colMat rr) *ᵥ v) = 0 := by rw [hv]; simp
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose] at this
    exact this
  have h3 : colMat rr *ᵥ v = 0 := dotProduct_self_eq_zero.mp h2
  have h4 : ∑ k, v k • (fun u => (rr k u : ℝ)) = 0 := by
    ext u
    have := congrFun h3 u
    simp only [Matrix.mulVec, dotProduct, colMat, Pi.zero_apply] at this
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← this]; exact Finset.sum_congr rfl (fun k _ => by ring)
  have := Fintype.linearIndependent_iff.mp hli v h4
  exact hv0 (funext this)

lemma gram_det_bound {n d E : ℕ} (rr : Fin d → Fin n → ℤ) (hE : ∀ k u, |rr k u| ≤ 2 ^ E) :
    (gram rr).det.natAbs ≤ 2 ^ (d * d + d * n + 2 * E * d) := by
  have hx : ∀ k l, AbsoluteValue.abs (gram rr k l) ≤ (n : ℤ) * 2 ^ (2 * E) := by
    intro k l
    simp only [AbsoluteValue.abs_apply, gram]
    calc |∑ u, rr k u * rr l u| ≤ ∑ u, |rr k u * rr l u| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _u : Fin n, (2 : ℤ) ^ (2 * E) := by
          refine Finset.sum_le_sum (fun u _ => ?_)
          rw [abs_mul, two_mul, pow_add]
          exact mul_le_mul (hE k u) (hE l u) (abs_nonneg _) (by positivity)
      _ = n * 2 ^ (2 * E) := by simp
  have h := Matrix.det_le hx
  simp only [AbsoluteValue.abs_apply, Fintype.card_fin, nsmul_eq_mul] at h
  have h1 : ((d.factorial : ℕ) : ℤ) ≤ 2 ^ (d * d) := by
    have : d.factorial ≤ d ^ d := Nat.factorial_le_pow d
    have h2 : d ^ d ≤ (2 ^ d) ^ d := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le d
    rw [← pow_mul] at h2
    exact_mod_cast this.trans h2
  have h2 : ((n : ℤ) * 2 ^ (2 * E)) ^ d ≤ 2 ^ (d * n + 2 * E * d) := by
    have : (n : ℤ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
    calc ((n : ℤ) * 2 ^ (2 * E)) ^ d ≤ ((2 : ℤ) ^ n * 2 ^ (2 * E)) ^ d := by gcongr
      _ = 2 ^ (d * n + 2 * E * d) := by rw [← pow_add, ← pow_mul]; ring_nf
  have h3 : |(gram rr).det| ≤ 2 ^ (d * d + d * n + 2 * E * d) := by
    calc |(gram rr).det| ≤ (d.factorial : ℤ) * ((n : ℤ) * 2 ^ (2 * E)) ^ d := h
      _ ≤ 2 ^ (d * d) * 2 ^ (d * n + 2 * E * d) := by gcongr
      _ = 2 ^ (d * d + d * n + 2 * E * d) := by rw [← pow_add]; ring_nf
  have : ((gram rr).det.natAbs : ℤ) ≤ 2 ^ (d * d + d * n + 2 * E * d) := by
    rw [Int.natCast_natAbs]; exact h3
  exact_mod_cast this

/-- Scaling rational vectors in the real span of independent integral vectors into their lattice. -/
lemma lattice_scale {n d d' : ℕ} (rr : Fin d → Fin n → ℤ)
    (hli : LinearIndependent ℝ (fun k => fun u => (rr k u : ℝ))) (g : Fin d' → Fin n → ℚ)
    (hg : ∀ j, toReal (g j) ∈ Submodule.span ℝ (Set.range (fun k => fun u => (rr k u : ℝ)))) :
    ∀ j, ∃ a : Fin d → ℤ, ∀ u,
      (((gram rr).det.natAbs * ∏ j, ∏ u, (g j u).den : ℕ) : ℚ) * g j u =
        ∑ k, (a k : ℚ) * rr k u := by
  classical
  intro j
  set δ := ∏ j, ∏ u, (g j u).den with hδ
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hg j)
  have hc' : ∀ u, ∑ k, c k * (rr k u : ℝ) = (g j u : ℝ) := by
    intro u
    have := congrFun hc u
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, toReal] at this
    exact this
  have hW : ∀ u, ∃ z : ℤ, (δ : ℚ) * g j u = z := fun u =>
    int_of_den_dvd (g j u) δ ((Finset.dvd_prod_of_mem _ (Finset.mem_univ u)).trans
      (Finset.dvd_prod_of_mem (fun j => ∏ u, (g j u).den) (Finset.mem_univ j)))
  choose Wz hWz using hW
  set Gz := gram rr with hGz
  let a0 : Fin d → ℤ := Gz.adjugate *ᵥ (fun k => ∑ u, rr k u * Wz u)
  refine ⟨fun k => Gz.det.sign * a0 k, fun u => ?_⟩
  -- real computation
  set Gr := (Int.castRingHom ℝ).mapMatrix Gz with hGr
  have hGr' : Gr = (colMat rr).transpose * colMat rr := gram_map rr
  set β : Fin d → ℝ := (δ : ℝ) • c with hβ
  have hMβ : colMat rr *ᵥ β = fun u => (Wz u : ℝ) := by
    ext u
    have h1 : ((δ : ℚ) * g j u : ℚ) = (Wz u : ℚ) := hWz u
    have h2 : ((δ : ℝ) * (g j u : ℝ)) = (Wz u : ℝ) := by exact_mod_cast h1
    rw [← h2, ← hc' u]
    simp only [Matrix.mulVec, dotProduct, colMat, hβ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have ha0 : (fun k => (a0 k : ℝ)) = Gr.adjugate *ᵥ ((colMat rr).transpose *ᵥ (fun u => (Wz u : ℝ))) := by
    rw [hGr, ← RingHom.map_adjugate]
    ext k
    simp [a0, Matrix.mulVec, dotProduct, colMat]
  have ha0' : (fun k => (a0 k : ℝ)) = (Gz.det : ℝ) • β := by
    rw [ha0, ← hMβ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← hGr',
      Matrix.adjugate_mul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hGr, ← RingHom.map_det]; rfl
  have hfin : ∑ k, (a0 k : ℝ) * (rr k u : ℝ) = (Gz.det : ℝ) * (Wz u : ℝ) := by
    have := congrFun (congrArg (fun v => colMat rr *ᵥ v) ha0') u
    simp only [Matrix.mulVec_smul, hMβ, Pi.smul_apply, smul_eq_mul] at this
    rw [← this]
    simp only [Matrix.mulVec, dotProduct, colMat]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have h : (Gz.det.sign * Gz.det : ℤ) = (Gz.det.natAbs : ℤ) := Int.sign_mul_self _
  have hsign : ((Gz.det.sign : ℤ) : ℝ) * ((Gz.det : ℤ) : ℝ) = ((Gz.det.natAbs : ℕ) : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) h
    simp only [Int.cast_mul, Int.cast_natCast] at this
    exact this
  have hreal : ((((Gz.det.natAbs * δ : ℕ) : ℚ) * g j u : ℚ) : ℝ) =
      ((∑ k, ((Gz.det.sign * a0 k : ℤ) : ℚ) * rr k u : ℚ) : ℝ) := by
    simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_sum, Rat.cast_intCast, Nat.cast_mul,
      Int.cast_mul]
    have h1 : ((δ : ℝ) * (g j u : ℝ)) = (Wz u : ℝ) := by exact_mod_cast hWz u
    simp_rw [mul_assoc ((Gz.det.sign : ℤ) : ℝ)]
    rw [← Finset.mul_sum, hfin, ← mul_assoc, hsign, mul_assoc, h1]
  exact_mod_cast hreal

end MIQPT1
/-! ### Part K -/

open MIQPInNP.SmallSol
open scoped BigOperators Pointwise

namespace MIQPT1

lemma euclidNorm_smul {n : ℕ} (a : ℝ) (x : Fin n → ℝ) : euclidNorm (a • x) = |a| * euclidNorm x := by
  unfold euclidNorm
  have : ∑ i, (a • x) i ^ 2 = a ^ 2 * ∑ i, x i ^ 2 := by
    rw [Finset.mul_sum]; congr 1; ext i; simp [Pi.smul_apply, smul_eq_mul]; ring
  rw [this, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

lemma euclidNorm_pos {n : ℕ} (x : Fin n → ℝ) (hx : x ≠ 0) : 0 < euclidNorm x := by
  unfold euclidNorm
  apply Real.sqrt_pos.mpr
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h; push_neg at h; exact hx (funext h)
  calc 0 < x i ^ 2 := by positivity
    _ ≤ ∑ j, x j ^ 2 := Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)

lemma cone_subset_span {n : ℕ} (S : Set (Fin n → ℝ)) : cone S ⊆ Submodule.span ℝ S := by
  intro x hx
  unfold cone at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | smul a y _ hy => rw [NNReal.smul_def]; exact Submodule.smul_mem _ _ hy

lemma pointed_of_li {n d : ℕ} (v : Fin d → Fin n → ℝ) (hli : LinearIndependent ℝ v) :
    IsPointedCone (cone (Set.range v)) := by
  intro x hx hnx
  obtain ⟨l, hl0, rfl⟩ := (mem_cone_range v _).mp hx
  obtain ⟨l', hl0', hl'⟩ := (mem_cone_range v _).mp hnx
  have h : ∑ j, (l j + l' j) • v j = 0 := by
    simp only [add_smul, Finset.sum_add_distrib]; rw [← hl']; simp
  have := Fintype.linearIndependent_iff.mp hli _ h
  have hz : ∀ j, l j = 0 := fun j => by
    have := this j; linarith [hl0 j, hl0' j]
  simp [hz]

lemma int_lattice_cone {n d : ℕ} (v : Fin d → Fin n → ℝ) (hli : LinearIndependent ℝ v)
    (κ : Fin d → ℤ) (hy : ∑ k, (κ k : ℝ) • v k ∈ cone (Set.range v)) :
    ∑ k, (κ k : ℝ) • v k ∈ intCone (Set.range v) := by
  obtain ⟨l, hl0, hl⟩ := (mem_cone_range v _).mp hy
  have h : ∑ k, ((κ k : ℝ) - l k) • v k = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]; rw [hl]; simp
  have := Fintype.linearIndependent_iff.mp hli _ h
  have hk : ∀ k, (κ k : ℝ) = l k := fun k => by linarith [this k]
  have hk0 : ∀ k, 0 ≤ κ k := fun k => by
    have := hl0 k; rw [← hk k] at this; exact_mod_cast this
  rw [mem_intCone_range]
  refine ⟨fun k => (κ k).toNat, ?_⟩
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have : ((κ k).toNat : ℝ) = κ k := by exact_mod_cast Int.toNat_of_nonneg (hk0 k)
  rw [← this, Nat.cast_smul_eq_nsmul]

lemma li_smul {n d : ℕ} (g : Fin d → Fin n → ℚ) (hli : LinearIndependent ℝ (fun j => toReal (g j)))
    (D : ℚ) (hD : D ≠ 0) : LinearIndependent ℝ (fun j => toReal (D • g j)) := by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro c hc i
  have h : ∑ j, (c j * D) • toReal (g j) = 0 := by
    rw [← hc]; congr 1; ext j u; simp [toReal, mul_assoc]
  have := hli _ h i
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD
  exact (mul_eq_zero.mp this).resolve_right hD'

lemma toReal_smul {n : ℕ} (D : ℚ) (g : Fin n → ℚ) : toReal (D • g) = (D : ℝ) • toReal g := by
  ext u; simp [toReal]

/-- The positivity hypothesis of Claim 2, derived from property (b) of Lemma 7. -/
lemma pos_of_7b {n d : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (g : Fin d → Fin n → ℚ) (f : Fin n → ℚ)
    (hpsd : ∀ x ∈ cone (Set.range fun j => toReal (g j)), 0 ≤ quadForm H x)
    (hfg : ∀ j, 0 < ∑ u, (f u : ℝ) * toReal (g j) u)
    (hb : ∀ S : Finset (Fin d),
      IsLeast (quadForm H '' (cone ((fun j => toReal (g j)) '' (S : Set (Fin d))) ∩ hyperplane f)) 0 →
        ∃ j ∈ S, quadForm H (toReal (g j)) = 0)
    (D : ℚ) (hD : 0 < D) :
    ∀ x ∈ cone ((fun j => toReal (D • g j)) '' {j | quadForm H (toReal (D • g j)) ≠ 0}),
      x ≠ 0 → 0 < quadForm H x := by
  classical
  intro x hx hx0
  have hQ : ∀ j, quadForm H (toReal (D • g j)) = (D : ℝ) ^ 2 * quadForm H (toReal (g j)) := by
    intro j; rw [toReal_smul, quadForm_smul]
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  obtain ⟨l, hl0, hlS, rfl⟩ := (mem_cone_image _ _ _).mp hx
  set S : Finset (Fin d) := Finset.univ.filter (fun j => quadForm H (toReal (g j)) ≠ 0) with hS
  have hlS' : ∀ j, j ∉ (S : Set (Fin d)) → l j * D = 0 := by
    intro j hj
    have : j ∉ {j | quadForm H (toReal (D • g j)) ≠ 0} := by
      simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, not_not] at hj
      simp only [Set.mem_setOf_eq, not_not, hQ, hj, mul_zero]
    rw [hlS j this, zero_mul]
  have hxg : ∑ j, l j • toReal (D • g j) = ∑ j, (l j * D) • toReal (g j) := by
    congr 1; ext j u; simp [toReal, mul_assoc, mul_comm]
  rw [hxg] at hx0 ⊢
  have hcone : ∑ j, (l j * D) • toReal (g j) ∈ cone (Set.range fun j => toReal (g j)) :=
    (mem_cone_range _ _).mpr ⟨_, fun j => mul_nonneg (hl0 j) hD'.le, rfl⟩
  have hnonneg := hpsd _ hcone
  rcases hnonneg.lt_or_eq with h | h
  · exact h
  exfalso
  set x := ∑ j, (l j * D) • toReal (g j) with hxdef
  set φ := ∑ u, (f u : ℝ) * x u with hφ
  have hφeq : φ = ∑ j, (l j * D) * ∑ u, (f u : ℝ) * toReal (g j) u := by
    rw [hφ, hxdef]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun u _ => by ring))
  have hφpos : 0 < φ := by
    rw [hφeq]
    obtain ⟨j, hj⟩ : ∃ j, l j * D ≠ 0 := by
      by_contra hcon; push_neg at hcon
      apply hx0; rw [hxdef]; simp [hcon]
    have hjpos : 0 < l j * D := lt_of_le_of_ne (mul_nonneg (hl0 j) hD'.le) (Ne.symm hj)
    calc 0 < l j * D * ∑ u, (f u : ℝ) * toReal (g j) u := mul_pos hjpos (hfg j)
      _ ≤ _ := Finset.single_le_sum (f := fun j => (l j * D) * ∑ u, (f u : ℝ) * toReal (g j) u)
          (fun i _ => mul_nonneg (mul_nonneg (hl0 i) hD'.le) (hfg i).le) (Finset.mem_univ j)
  set y := (1 / φ) • x with hy
  have hyS : y ∈ cone ((fun j => toReal (g j)) '' (S : Set (Fin d))) := by
    rw [mem_cone_image]
    refine ⟨fun j => (1 / φ) * (l j * D), fun j => mul_nonneg (by positivity)
      (mul_nonneg (hl0 j) hD'.le), fun j hj => by simp [hlS' j hj], ?_⟩
    rw [hy, hxdef, Finset.smul_sum]
    congr 1; ext j u; simp [mul_assoc]
  have hyH : y ∈ hyperplane f := by
    show ∑ j, (f j : ℝ) * y j = 1
    rw [hy]
    simp only [Pi.smul_apply, smul_eq_mul]
    have : ∑ j, (f j : ℝ) * (1 / φ * x j) = (1 / φ) * φ := by
      rw [hφ, Finset.mul_sum]; congr 1; ext j; ring
    rw [this]; field_simp
  have hQy : quadForm H y = 0 := by rw [hy, quadForm_smul, ← h, mul_zero]
  have hleast : IsLeast (quadForm H '' (cone ((fun j => toReal (g j)) '' (S : Set (Fin d))) ∩
      hyperplane f)) 0 := by
    refine ⟨⟨y, ⟨hyS, hyH⟩, hQy⟩, ?_⟩
    rintro _ ⟨z, ⟨hz, -⟩, rfl⟩
    exact hpsd z (cone_mono (Set.image_subset_range _ _) hz)
  obtain ⟨j, hjS, hj0⟩ := hb S hleast
  simp [hS] at hjS
  exact hjS hj0

end MIQPT1
/-! ### Part L -/

open MIQPInNP.SmallSol
open scoped BigOperators Pointwise

namespace MIQPT1

lemma dot_pos_of_cone {n d : ℕ} (v : Fin d → Fin n → ℝ) (f : Fin n → ℚ)
    (hf : ∀ k, 0 < ∑ u, (f u : ℝ) * v k u) (y : Fin n → ℝ) (hy : y ∈ cone (Set.range v))
    (hy0 : y ≠ 0) : 0 < ∑ u, (f u : ℝ) * y u := by
  obtain ⟨l, hl0, rfl⟩ := (mem_cone_range v _).mp hy
  have e : ∑ u, (f u : ℝ) * (∑ k, l k • v k) u = ∑ k, l k * ∑ u, (f u : ℝ) * v k u := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun u _ => by ring))
  rw [e]
  obtain ⟨k, hk⟩ : ∃ k, l k ≠ 0 := by
    by_contra hcon; push_neg at hcon; apply hy0; simp [hcon]
  have hkpos : 0 < l k := lt_of_le_of_ne (hl0 k) (Ne.symm hk)
  calc 0 < l k * ∑ u, (f u : ℝ) * v k u := mul_pos hkpos (hf k)
    _ ≤ _ := Finset.single_le_sum (f := fun k => l k * ∑ u, (f u : ℝ) * v k u)
        (fun i _ => mul_nonneg (hl0 i) (hf i).le) (Finset.mem_univ k)

/-- A normalizing functional from Lemma 6 (or `0` when there are no rays). -/
theorem exists_f : ∃ G : Polynomial ℕ, ∀ (n d : ℕ) (rq : Fin d → Fin n → ℚ),
    LinearIndependent ℝ (fun j => toReal (rq j)) →
    ∃ f : Fin n → ℚ, vecSize f ≤ G.eval (∑ k, vecSize (rq k) + n) ∧
      ∀ k, 0 < ∑ u, (f u : ℝ) * toReal (rq k) u := by
  obtain ⟨g6, h6⟩ := lemma_6
  refine ⟨g6 + 3 * Polynomial.X, ?_⟩
  intro n d rq hli
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    refine ⟨0, ?_, fun k => k.elim0⟩
    rw [vecSize_zero]; simp
  obtain ⟨f, hf1, hf2, -⟩ := h6 n d rq hd (pointed_of_li _ hli)
  refine ⟨f, ?_, fun k => ?_⟩
  · refine hf1.trans ?_
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    have : (Finset.univ.sup fun i => vecSize (rq i)) ≤ ∑ k, vecSize (rq k) + n := by
      apply Finset.sup_le
      intro i _
      have := Finset.single_le_sum (f := fun k => vecSize (rq k)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
      omega
    have := peval_mono g6 this
    omega
  · set r := toReal (rq k) with hr
    have hr0 : r ≠ 0 := hli.ne_zero k
    have hnr := euclidNorm_pos r hr0
    set x := (1 / euclidNorm r) • r with hx
    have hxc : x ∈ cone (Set.range fun i => toReal (rq i)) := by
      rw [mem_cone_range]
      refine ⟨Pi.single k (1 / euclidNorm r), fun j => ?_, ?_⟩
      · by_cases h : j = k
        · subst h; simp; positivity
        · simp [h]
      · rw [Finset.sum_eq_single k]
        · simp [hx, hr]
        · intro j _ hj; simp [hj]
        · simp
    have hx1 : euclidNorm x = 1 := by
      rw [hx, euclidNorm_smul, abs_of_pos (by positivity)]; field_simp
    have hR := hf2 x hxc hx1
    set R := Finset.univ.sup' ⟨⟨0, hd⟩, Finset.mem_univ _⟩ fun i => euclidNorm (toReal (rq i))
    have hRpos : 0 < R := lt_of_lt_of_le hnr
      (Finset.le_sup' (fun i => euclidNorm (toReal (rq i))) (Finset.mem_univ k))
    have hfx : 0 < ∑ j, (f j : ℝ) * x j := lt_of_lt_of_le (by positivity) hR
    have e : ∑ j, (f j : ℝ) * r j = euclidNorm r * ∑ j, (f j : ℝ) * x j := by
      rw [hx, Finset.mul_sum]; congr 1; ext j; simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
    rw [e]; exact mul_pos hnr hfx

/-- The lattice shift: write `z ∈ int.cone(R) ∩ cone(g)` as a bounded lattice point plus
non-negative integer multiples of the scaled generators `D g_j`. -/
lemma shift_decomp {n d d' : ℕ} (rr : Fin d → Fin n → ℤ) (g : Fin d' → Fin n → ℚ) (D : ℕ)
    (a : Fin d' → Fin d → ℤ) (ha : ∀ j u, (D : ℚ) * g j u = ∑ k, (a j k : ℚ) * rr k u)
    (hD : 0 < D) (z : Fin n → ℝ) (hz1 : z ∈ intCone (Set.range fun k => fun u => (rr k u : ℝ)))
    (hz2 : z ∈ cone (Set.range fun j => toReal (g j))) :
    ∃ (τ : Fin d → ℤ) (ν : Fin d' → ℕ) (l : Fin d' → ℝ), (∀ j, 0 ≤ l j ∧ l j ≤ D) ∧
      toReal (fun u => ∑ k, (τ k : ℚ) * rr k u) = ∑ j, l j • toReal (g j) ∧
      z = toReal (fun u => ∑ k, (τ k : ℚ) * rr k u) + ∑ j, ν j • toReal ((D : ℚ) • g j) := by
  obtain ⟨lam, hlam0, hzlam⟩ := (mem_cone_range _ _).mp hz2
  obtain ⟨μ, hzμ⟩ := (mem_intCone_range _ _).mp hz1
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  set ν : Fin d' → ℕ := fun j => ⌊lam j / D⌋₊ with hν
  set τ : Fin d → ℤ := fun k => (μ k : ℤ) - ∑ j, (ν j : ℤ) * a j k with hτ
  set l : Fin d' → ℝ := fun j => lam j - ν j * D with hl
  have e3 : ∀ j u, (D : ℝ) * (g j u : ℝ) = ∑ k, (a j k : ℝ) * (rr k u : ℝ) := by
    intro j u
    have := congrArg (fun q : ℚ => (q : ℝ)) (ha j u)
    push_cast at this; exact this
  have ht : toReal (fun u => ∑ k, (τ k : ℚ) * rr k u) = ∑ j, l j • toReal (g j) := by
    ext u
    have e1 : z u = ∑ j, lam j * (g j u : ℝ) := by
      rw [hzlam]; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, toReal]
    have e2 : z u = ∑ k, (μ k : ℝ) * (rr k u : ℝ) := by
      rw [hzμ]; simp only [Finset.sum_apply, Pi.smul_apply]; simp only [nsmul_eq_mul]
    simp only [toReal, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hτ, hl]
    push_cast
    calc ∑ k, ((μ k : ℝ) - ∑ j, (ν j : ℝ) * (a j k : ℝ)) * (rr k u : ℝ)
        = ∑ k, (μ k : ℝ) * (rr k u : ℝ) - ∑ j, (ν j : ℝ) * ∑ k, (a j k : ℝ) * (rr k u : ℝ) := by
          simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
          congr 1
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => by ring))
      _ = ∑ j, lam j * (g j u : ℝ) - ∑ j, (ν j : ℝ) * ((D : ℝ) * (g j u : ℝ)) := by
          rw [← e2, e1]
          congr 1
          exact Finset.sum_congr rfl (fun j _ => by rw [e3 j u])
      _ = ∑ j, (lam j - (ν j : ℝ) * D) * (g j u : ℝ) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
  refine ⟨τ, ν, l, ?_, ht, ?_⟩
  · intro j
    have h1 : (ν j : ℝ) ≤ lam j / D := Nat.floor_le (div_nonneg (hlam0 j) hDr.le)
    have h2 : lam j / D < ν j + 1 := Nat.lt_floor_add_one _
    rw [le_div_iff₀ hDr] at h1
    rw [div_lt_iff₀ hDr] at h2
    simp only [hl]
    constructor <;> nlinarith
  · rw [ht, hzlam]
    ext u
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply]
    simp only [nsmul_eq_mul, smul_eq_mul, hl, toReal, Pi.smul_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    push_cast; ring

end MIQPT1
/-! ### Part M -/

open MIQPInNP.SmallSol
open scoped BigOperators Pointwise

namespace MIQPT1

lemma shift_back {n d d' : ℕ} (rr : Fin d → Fin n → ℤ) (g : Fin d' → Fin n → ℚ) (D : ℕ)
    (a : Fin d' → Fin d → ℤ) (ha : ∀ j u, (D : ℚ) * g j u = ∑ k, (a j k : ℚ) * rr k u)
    (hli : LinearIndependent ℝ (fun k => fun u => (rr k u : ℝ)))
    (hgsub : cone (Set.range fun j => toReal (g j)) ⊆ cone (Set.range fun k => fun u => (rr k u : ℝ)))
    (τ : Fin d → ℤ) (l : Fin d' → ℝ) (hl : ∀ j, 0 ≤ l j)
    (ht : toReal (fun u => ∑ k, (τ k : ℚ) * rr k u) = ∑ j, l j • toReal (g j)) (ν : Fin d' → ℕ) :
    toReal (fun u => ∑ k, (τ k : ℚ) * rr k u) + ∑ j, ν j • toReal ((D : ℚ) • g j) ∈
      intCone (Set.range fun k => fun u => (rr k u : ℝ)) := by
  have e3 : ∀ j u, (D : ℝ) * (g j u : ℝ) = ∑ k, (a j k : ℝ) * (rr k u : ℝ) := by
    intro j u
    have := congrArg (fun q : ℚ => (q : ℝ)) (ha j u)
    push_cast at this; exact this
  set κ : Fin d → ℤ := fun k => τ k + ∑ j, (ν j : ℤ) * a j k with hκ
  have hrep : toReal (fun u => ∑ k, (τ k : ℚ) * rr k u) + ∑ j, ν j • toReal ((D : ℚ) • g j) =
      ∑ k, (κ k : ℝ) • (fun u => (rr k u : ℝ)) := by
    ext u
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
    simp only [nsmul_eq_mul, smul_eq_mul, toReal, Pi.smul_apply, hκ]
    push_cast
    have : ∀ j, (D : ℝ) * (g j u : ℝ) = ∑ k, (a j k : ℝ) * (rr k u : ℝ) := fun j => e3 j u
    simp_rw [this]
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => by ring))
  rw [hrep]
  apply int_lattice_cone _ hli
  rw [← hrep, ht]
  apply hgsub
  rw [mem_cone_range]
  refine ⟨fun j => l j + ν j * D, fun j => add_nonneg (hl j) (by positivity), ?_⟩
  ext u
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
  simp only [nsmul_eq_mul, smul_eq_mul, toReal, Pi.smul_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  push_cast; ring

end MIQPT1
/-! ### Part N -/

open MIQPInNP.SmallSol
open scoped BigOperators Pointwise

namespace MIQPT1

lemma pow_mono_W {W : ℕ} (hW : 1 ≤ W) {a b : ℕ} (h : a ≤ b) : W ^ a ≤ W ^ b :=
  Nat.pow_le_pow_right hW h

lemma den_prod_le {n d W : ℕ} (g : Fin d → Fin n → ℚ) (hd : d ≤ W) (hg : ∀ j, vecSize (g j) ≤ W) :
    ∏ j, ∏ u, (g j u).den ≤ 2 ^ (W ^ 2) := by
  calc ∏ j, ∏ u, (g j u).den ≤ ∏ j : Fin d, 2 ^ W :=
        Finset.prod_le_prod (fun j _ => Nat.zero_le _)
          (fun j _ => (prod_den_le (g j)).trans (two_pow_mono (hg j)))
    _ = 2 ^ (d * W) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul,
          mul_comm]
    _ ≤ 2 ^ (W ^ 2) := two_pow_mono (by rw [sq]; exact Nat.mul_le_mul_right _ hd)

/-- Case 2 core: from a polytope plus the integer cone of independent integral rays. -/
theorem core2 : ∃ G : Polynomial ℕ, ∀ (n mP d : ℕ) (A' : Matrix (Fin mP) (Fin n) ℚ)
    (b' : Fin mP → ℚ) (rr : Fin d → Fin n → ℤ) (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ)
    (dd : ℚ), H.transpose = H → Bornology.IsBounded (polyhedron A' b') →
    LinearIndependent ℝ (fun k => fun u => (rr k u : ℝ)) →
    (∀ x ∈ cone (Set.range fun k => fun u => (rr k u : ℝ)), 0 ≤ quadForm H x) →
    (∃ x ∈ polyhedron A' b' + intCone (Set.range fun k => fun u => (rr k u : ℝ)),
      quadVal H c dd x ≤ 0) →
    ∃ x0 : Fin n → ℚ,
      toReal x0 ∈ polyhedron A' b' + intCone (Set.range fun k => fun u => (rr k u : ℝ)) ∧
      quadVal H c dd (toReal x0) ≤ 0 ∧
      vecSize x0 ≤ G.eval (matSize A' + vecSize b' + ∑ k, vecSize (fun u => (rr k u : ℚ)) +
        matSize H + vecSize c + bitSize dd) := by
  obtain ⟨Gf, hGf⟩ := exists_f
  obtain ⟨g7, h7⟩ := lemma_7
  obtain ⟨Ga, hGa⟩ := core3a
  obtain ⟨Gb, hGb⟩ := core3b
  refine ⟨(Ga + Gb).comp (60 * ((Polynomial.X + Gf + 1) +
    g7.comp (Polynomial.X + Gf + 1) + 1) ^ 5), ?_⟩
  intro n mP d A' b' rr H c dd hsym hb hli hpsd ⟨x, hx, hxQ⟩
  set rR : Fin d → Fin n → ℝ := fun k => fun u => (rr k u : ℝ) with hrR
  set rq : Fin d → Fin n → ℚ := fun k u => (rr k u : ℚ) with hrq
  have hrqR : (fun k => toReal (rq k)) = rR := by ext k u; simp [toReal, hrq, hrR]
  have hliq : LinearIndependent ℝ (fun k => toReal (rq k)) := by rw [hrqR]; exact hli
  have hpsdq : ∀ x ∈ cone (Set.range fun k => toReal (rq k)), 0 ≤ quadForm H x := by
    rw [hrqR]; exact hpsd
  obtain ⟨S, hS⟩ : ∃ S, S = matSize A' + vecSize b' + ∑ k, vecSize (rq k) + matSize H +
      vecSize c + bitSize dd := ⟨_, rfl⟩
  rw [show (∑ k, vecSize (fun u => (rr k u : ℚ))) = ∑ k, vecSize (rq k) from rfl, ← hS]
  have hnc := n_le_vecSize c
  have hmb := n_le_vecSize b'
  have hdn : d ≤ n := card_le_of_li _ hli
  obtain ⟨f, hfsz, hfpos⟩ := hGf n d rq hliq
  obtain ⟨W1, hW1⟩ : ∃ W, W = S + Gf.eval S + 1 := ⟨_, rfl⟩
  have hfGf : vecSize f ≤ Gf.eval S := hfsz.trans (peval_mono Gf (by omega))
  have hfW1 : vecSize f ≤ W1 := by omega
  obtain ⟨N7, gens, hunion, h7b, h7c⟩ := h7 n d H rq f hliq hpsdq hfpos
  obtain ⟨W2, hW2⟩ : ∃ W, W = W1 + g7.eval W1 + 1 := ⟨_, rfl⟩
  have hW21 : 1 ≤ W2 := by omega
  have hSW2 : S ≤ W2 := by omega
  -- decompose x
  obtain ⟨p, hp, z, hz, rfl⟩ := Set.mem_add.mp hx
  have hzc : z ∈ cone (Set.range fun k => toReal (rq k)) := by
    rw [hrqR]; exact intCone_subset_cone _ hz
  rw [← hunion] at hzc
  obtain ⟨i0, hi0⟩ := Set.mem_iUnion.mp hzc
  set g := gens i0 with hg
  have hgsubq : cone (Set.range fun j => toReal (g j)) ⊆ cone (Set.range fun k => toReal (rq k)) := by
    rw [← hunion]; exact Set.subset_iUnion (fun i => cone (Set.range fun j => toReal (gens i j))) i0
  have hgsub : cone (Set.range fun j => toReal (g j)) ⊆ cone (Set.range rR) := by
    rw [← hrqR]; exact hgsubq
  have hgself : ∀ j, toReal (g j) ∈ cone (Set.range fun j => toReal (g j)) := by
    intro j; unfold cone; exact Submodule.subset_span (Set.mem_range_self j)
  have hgspan : ∀ j, toReal (g j) ∈ Submodule.span ℝ (Set.range rR) := fun j =>
    cone_subset_span _ (hgsub (hgself j))
  obtain ⟨hgli, hgsz⟩ := h7c i0
  have hgW : ∀ j, vecSize (g j) ≤ W2 := by
    intro j; have : vecSize (g j) ≤ _ := hgsz j
    have h2 := peval_mono g7 (show matSize H + ∑ k, vecSize (rq k) + vecSize f ≤ W1 by omega)
    omega
  have hfg : ∀ j, 0 < ∑ u, (f u : ℝ) * toReal (g j) u := fun j =>
    dot_pos_of_cone (fun k => toReal (rq k)) f hfpos _ (hgsubq (hgself j)) (hgli.ne_zero j)
  -- lattice scaling
  have hlat := lattice_scale rr hli g hgspan
  choose a ha using hlat
  set D : ℕ := (gram rr).det.natAbs * ∏ j, ∏ u, (g j u).den with hD
  have hD0 : 0 < D := by
    apply Nat.mul_pos (Int.natAbs_pos.mpr (gram_det_ne_zero rr hli))
    exact Finset.prod_pos (fun j _ => Finset.prod_pos (fun u _ => (g j u).den_pos))
  have hrrW : ∀ k u, |rr k u| ≤ 2 ^ W2 := by
    intro k u
    have h1 := sm_abs_le ((sm_of_vecSize (rq k) u).mono (show vecSize (rq k) ≤ W2 by
      have := Finset.single_le_sum (f := fun k => vecSize (rq k)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ k)
      omega))
    have : |((rr k u : ℤ) : ℚ)| ≤ 2 ^ W2 := h1
    exact_mod_cast this
  have hDle : D ≤ 2 ^ (5 * W2 ^ 2) := by
    have h1 := gram_det_bound rr hrrW
    have h2 := den_prod_le g (hdn.trans (by omega)) hgW
    have h3 : d * d + d * n + 2 * W2 * d ≤ 4 * W2 ^ 2 := by
      have : d ≤ W2 := by omega
      have : n ≤ W2 := by omega
      nlinarith
    calc D ≤ 2 ^ (d * d + d * n + 2 * W2 * d) * 2 ^ (W2 ^ 2) := Nat.mul_le_mul h1 h2
      _ ≤ 2 ^ (4 * W2 ^ 2) * 2 ^ (W2 ^ 2) := Nat.mul_le_mul_right _ (two_pow_mono h3)
      _ = 2 ^ (5 * W2 ^ 2) := by rw [← pow_add]; ring_nf
  clear_value D
  -- scaled generators
  set s : Fin d → Fin n → ℚ := fun j => (D : ℚ) • g j with hs
  have hsli : LinearIndependent ℝ (fun j => toReal (s j)) :=
    li_smul g hgli D (by exact_mod_cast hD0.ne')
  have hspos := pos_of_7b H g f (fun x hx => hpsd x (hgsub hx)) hfg (h7b i0) D
    (by exact_mod_cast hD0)
  have hfs : ∀ j, 0 < ∑ k, (f k : ℝ) * toReal (s j) k := by
    intro j
    have e : ∑ k, (f k : ℝ) * toReal (s j) k = (D : ℝ) * ∑ k, (f k : ℝ) * toReal (g j) k := by
      rw [Finset.mul_sum]; congr 1; ext k; simp [hs, toReal]; ring
    rw [e]; exact mul_pos (by exact_mod_cast hD0) (hfg j)
  -- the lattice shift
  obtain ⟨τ, ν, l, hl, ht, hzeq⟩ := shift_decomp rr g D a ha hD0 z hz hi0
  set tq : Fin n → ℚ := fun u => ∑ k, (τ k : ℚ) * rr k u with htq
  have hDS : Sm (5 * W2 ^ 2) (D : ℚ) := sm_nat D hDle
  have hgS : ∀ j u, Sm (1 * W2 ^ 1) (g j u) := fun j u => sm_W_of_vecSize (g j) (hgW j) u
  have htqS : ∀ u, Sm (7 * W2 ^ 2) (tq u) := by
    intro u
    have hint : tq u = ((∑ k, τ k * rr k u : ℤ) : ℚ) := by simp [htq]
    rw [hint]
    apply sm_int
    have hreal : (tq u : ℝ) = ∑ j, l j * (g j u : ℝ) := by
      have := congrFun ht u
      simpa [toReal, Finset.sum_apply] using this
    have hb1 : |(tq u : ℝ)| ≤ d * (D * 2 ^ W2) := by
      rw [hreal]
      calc |∑ j, l j * (g j u : ℝ)| ≤ ∑ j, |l j * (g j u : ℝ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin d, (D : ℝ) * 2 ^ W2 := by
            refine Finset.sum_le_sum (fun j _ => ?_)
            rw [abs_mul, abs_of_nonneg (hl j).1]
            have := sm_abs_le_real (hgS j u)
            simp only [one_mul, pow_one] at this
            exact mul_le_mul (hl j).2 this (abs_nonneg _) (by positivity)
        _ = d * (D * 2 ^ W2) := by simp
    have hb2 : (d : ℝ) * (D * 2 ^ W2) ≤ 2 ^ (7 * W2 ^ 2) := by
      have h1 : (d : ℝ) ≤ 2 ^ W2 := by
        have : d < 2 ^ d := Nat.lt_two_pow_self
        have : (2 : ℕ) ^ d ≤ 2 ^ W2 := two_pow_mono (by omega)
        exact_mod_cast (by omega : d ≤ 2 ^ W2)
      have h2 : (D : ℝ) ≤ 2 ^ (5 * W2 ^ 2) := by exact_mod_cast hDle
      calc (d : ℝ) * (D * 2 ^ W2) ≤ 2 ^ W2 * (2 ^ (5 * W2 ^ 2) * 2 ^ W2) := by gcongr
        _ = 2 ^ (W2 + 5 * W2 ^ 2 + W2) := by rw [pow_add, pow_add]; ring
        _ ≤ 2 ^ (7 * W2 ^ 2) := pow_le_pow_right₀ (by norm_num) (by nlinarith)
    have hb3 : |((∑ k, τ k * rr k u : ℤ) : ℝ)| ≤ 2 ^ (7 * W2 ^ 2) := by
      have : ((∑ k, τ k * rr k u : ℤ) : ℝ) = (tq u : ℝ) := by rw [hint]; push_cast; rfl
      rw [this]; linarith
    have hb4 : ((∑ k, τ k * rr k u).natAbs : ℝ) ≤ 2 ^ (7 * W2 ^ 2) := by
      rw [Nat.cast_natAbs, Int.cast_abs]; exact hb3
    exact_mod_cast hb4
  -- the translated polytope
  set b'' : Fin mP → ℚ := b' + A'.mulVec tq with hb''
  have hb''bd : Bornology.IsBounded (polyhedron A' b'') := bounded_translate A' b' tq hb
  have hxin : p + z ∈ polyhedron A' b'' + intCone (Set.range fun j => toReal (s j)) := by
    rw [hzeq]
    refine Set.mem_add.mpr ⟨p + toReal tq, ?_, ∑ j, ν j • toReal ((D : ℚ) • g j), ?_, by abel⟩
    · rw [hb'', mem_translate, add_sub_cancel_right]; exact hp
    · exact (mem_intCone_range _ _).mpr ⟨ν, rfl⟩
  -- sizes of the new data
  have hsS : ∀ j u, Sm (6 * W2 ^ 2) (s j u) := by
    intro j u
    have := sm_mul hDS ((hgS j u).mono (show 1 * W2 ^ 1 ≤ W2 ^ 2 by
      simpa using pow_mono_W hW21 (show 1 ≤ 2 by norm_num)))
    simp only [hs, Pi.smul_apply, smul_eq_mul]
    exact this.mono (by omega)
  have hsV : ∀ j, vecSize (s j) ≤ W2 * (12 * W2 ^ 2 + 4) := by
    intro j
    have := vecSize_le_of_sm (s j) (hsS j)
    calc vecSize (s j) ≤ n * (2 * (6 * W2 ^ 2) + 4) := this
      _ ≤ W2 * (2 * (6 * W2 ^ 2) + 4) := Nat.mul_le_mul_right _ (by omega)
      _ = W2 * (12 * W2 ^ 2 + 4) := by ring
  have hsSum : ∑ j, vecSize (s j) ≤ W2 * (W2 * (12 * W2 ^ 2 + 4)) := by
    calc ∑ j, vecSize (s j) ≤ ∑ _j : Fin d, W2 * (12 * W2 ^ 2 + 4) :=
          Finset.sum_le_sum (fun j _ => hsV j)
      _ = d * (W2 * (12 * W2 ^ 2 + 4)) := by simp
      _ ≤ W2 * (W2 * (12 * W2 ^ 2 + 4)) := Nat.mul_le_mul_right _ (by omega)
  have hAS : ∀ i u, Sm (1 * W2 ^ 2) (A' i u) := fun i u =>
    (sm_of_matSize A' i u).mono (by
      have := pow_mono_W hW21 (show 1 ≤ 2 by norm_num); simp at this; omega)
  have hbS : ∀ i, Sm (1 * W2 ^ 3) (b' i) := fun i =>
    (sm_of_vecSize b' i).mono (by
      have := pow_mono_W hW21 (show 1 ≤ 3 by norm_num); simp at this; omega)
  have hb''S : ∀ i, Sm (11 * W2 ^ 3) (b'' i) := by
    intro i
    have h1 : ∀ u, Sm ((1 + 7) * W2 ^ 2) (A' i u * tq u) := fun u => smW_mul (hAS i u) (htqS u)
    have h2 := smW_sum hW21 (show n ≤ W2 by omega) _ h1
    have h3 := smW_add hW21 (hbS i) h2
    have e : b'' i = b' i + ∑ u, A' i u * tq u := by simp [hb'', Matrix.mulVec, dotProduct]
    rw [e]; exact h3.mono (by omega)
  have hb''V : vecSize b'' ≤ W2 * (22 * W2 ^ 3 + 4) := by
    have := vecSize_le_of_sm b'' hb''S
    calc vecSize b'' ≤ mP * (2 * (11 * W2 ^ 3) + 4) := this
      _ ≤ W2 * (2 * (11 * W2 ^ 3) + 4) := Nat.mul_le_mul_right _ (by omega)
      _ = W2 * (22 * W2 ^ 3 + 4) := by ring
  obtain ⟨S3, hS3def⟩ : ∃ S3, S3 = matSize A' + vecSize b'' + ∑ j, vecSize (s j) + matSize H +
      vecSize c + bitSize dd + vecSize f := ⟨_, rfl⟩
  have hS3 : S3 ≤ 60 * W2 ^ 5 := by
    have e1 := pow_mono_W hW21 (show 1 ≤ 5 by norm_num)
    have e2 := pow_mono_W hW21 (show 2 ≤ 5 by norm_num)
    have e4 := pow_mono_W hW21 (show 4 ≤ 5 by norm_num)
    have e : W2 * (22 * W2 ^ 3 + 4) + W2 * (W2 * (12 * W2 ^ 2 + 4)) =
        34 * W2 ^ 4 + 4 * W2 ^ 2 + 4 * W2 := by ring
    simp only [pow_one] at e1
    omega
  have key : ∃ x0 : Fin n → ℚ,
      toReal x0 ∈ polyhedron A' b'' + intCone (Set.range fun j => toReal (s j)) ∧
      quadVal H c dd (toReal x0) ≤ 0 ∧ vecSize x0 ≤ (Ga + Gb).eval S3 := by
    by_cases h2a : ∃ i, quadForm H (toReal (s i)) = 0 ∧
        ∃ y ∈ polyhedron A' b'' + intCone ((fun j => toReal (s j)) '' {j | j ≠ i}),
          2 * (∑ u, ∑ v, y u * (H u v : ℝ) * toReal (s i) v) + ∑ u, (c u : ℝ) * toReal (s i) u
            < 0
    · obtain ⟨x0, h1, h2, h3⟩ := hGa n mP d A' b'' s H c dd hsym hb''bd hsli h2a
      refine ⟨x0, h1, h2, h3.trans ?_⟩
      simp only [Polynomial.eval_add]
      have := peval_mono Ga (show matSize A' + vecSize b'' + ∑ j, vecSize (s j) + matSize H +
        vecSize c + bitSize dd ≤ S3 by omega)
      omega
    · push_neg at h2a
      obtain ⟨x0, h1, h2, h3⟩ := hGb n mP d A' b'' s H c dd f hsym hb''bd hsli hspos hfs h2a
        ⟨_, hxin, hxQ⟩
      refine ⟨x0, h1, h2, h3.trans ?_⟩
      simp only [Polynomial.eval_add]
      rw [← hS3def]; omega
  obtain ⟨x0, hx0m, hx0Q, hx0s⟩ := key
  refine ⟨x0, ?_, hx0Q, ?_⟩
  · obtain ⟨y, hy, w, hw, hyw⟩ := Set.mem_add.mp hx0m
    obtain ⟨ν', rfl⟩ := (mem_intCone_range _ _).mp hw
    have hy' := (mem_translate A' b' tq y).mp hy
    have hback := shift_back rr g D a ha hli hgsub τ l (fun j => (hl j).1) ht ν'
    rw [← hyw]
    refine Set.mem_add.mpr ⟨y - toReal tq, hy', _, hback, ?_⟩
    simp only [hs]
    abel
  · refine hx0s.trans ?_
    rw [Polynomial.eval_comp]
    apply peval_mono
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one, Polynomial.eval_ofNat, Polynomial.eval_comp]
    rw [← hW1, ← hW2]
    exact hS3

end MIQPT1
/-! ### Part O -/

open MIQPInNP.SmallSol
open scoped BigOperators Pointwise

namespace MIQPT1

/-- Case 2 of the proof of Theorem 1 (pointed polyhedron, copositive recession cone). -/
theorem case2 : ∃ G : Polynomial ℕ, ∀ (n p m : ℕ), p ≤ n →
    ∀ (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (d : ℚ)
      (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ), H.transpose = H → IsPointedPoly A →
      (feasSet p H c d A b).Nonempty → (∀ r ∈ recCone A, 0 ≤ quadForm H r) →
      ∃ x0 : Fin n → ℚ, toReal x0 ∈ feasSet p H c d A b ∧
        vecSize x0 ≤ G.eval (instSize H c d A b) := by
  obtain ⟨g4, h4⟩ := proposition_4
  obtain ⟨G2, h2⟩ := core2
  refine ⟨G2.comp (Polynomial.X + g4 + Polynomial.X * g4), ?_⟩
  intro n p m hpn H c d A b hsym hA ⟨x, hxF⟩ hcop
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hpn
  obtain ⟨N, mi, Ai, bi, KK, heq, hP, hR, hli⟩ := h4 p q m A b (fun _ => hA)
  have hx' : x ∈ {x | x ∈ polyhedron A b ∧ IsMixedInt p x} := ⟨hxF.2.1, hxF.2.2⟩
  rw [heq] at hx'
  simp only [Set.mem_iUnion] at hx'
  obtain ⟨i, R, hRK, hxR⟩ := hx'
  -- enumerate R
  set e := R.equivFin with he
  set dR := R.card with hdR
  set rr : Fin dR → Fin (p + q) → ℤ := fun k => ((e.symm k : R) : Fin (p + q) → ℤ) with hrr
  have himg : (fun r j => (r j : ℝ)) '' (R : Set (Fin (p + q) → ℤ)) =
      Set.range (fun k => fun u => (rr k u : ℝ)) := by
    ext v
    constructor
    · rintro ⟨r, hr, rfl⟩
      refine ⟨e ⟨r, hr⟩, ?_⟩
      simp [hrr]
    · rintro ⟨k, rfl⟩
      exact ⟨rr k, (e.symm k).2, rfl⟩
  have hlik : LinearIndependent ℝ (fun k => fun u => (rr k u : ℝ)) :=
    (hli R hRK).comp (fun k => e.symm k) e.symm.injective
  have hcone : ∀ y ∈ cone (Set.range fun k => fun u => (rr k u : ℝ)), 0 ≤ quadForm H y := by
    intro y hy
    apply hcop
    refine cone_subset_recCone A _ ?_ hy
    rintro _ ⟨k, rfl⟩
    exact (hR R hRK (rr k) (e.symm k).2).1.1
  rw [himg] at hxR
  obtain ⟨x0, hx0m, hx0Q, hx0s⟩ := h2 (p + q) (mi i) dR (Ai i) (bi i) rr H c d hsym (hP i).1
    hlik hcone ⟨x, hxR, hxF.1⟩
  have hmem : toReal x0 ∈ {x | x ∈ polyhedron A b ∧ IsMixedInt p x} := by
    rw [heq]
    simp only [Set.mem_iUnion]
    refine ⟨i, R, hRK, ?_⟩
    rw [himg]; exact hx0m
  refine ⟨x0, ⟨hx0Q, hmem.1, hmem.2⟩, hx0s.trans ?_⟩
  rw [Polynomial.eval_comp]
  apply peval_mono
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
  set Φ := instSize H c d A b with hΦ
  have hdn : dR ≤ p + q := card_le_of_li _ hlik
  have hnc := n_le_vecSize c
  have h4b : g4.eval (matSize A + vecSize b) ≤ g4.eval Φ := peval_mono _ (by rw [hΦ]; unfold instSize; omega)
  have hsum : ∑ k, vecSize (fun u => (rr k u : ℚ)) ≤ Φ * g4.eval Φ := by
    calc ∑ k, vecSize (fun u => (rr k u : ℚ)) ≤ ∑ _k : Fin dR, g4.eval Φ :=
          Finset.sum_le_sum (fun k _ => ((hR R hRK (rr k) (e.symm k).2).2).trans h4b)
      _ = dR * g4.eval Φ := by simp
      _ ≤ Φ * g4.eval Φ := Nat.mul_le_mul_right _ (by rw [hΦ]; unfold instSize; omega)
  have hPi := (hP i).2
  have : matSize H + vecSize c + bitSize d ≤ Φ := by rw [hΦ]; unfold instSize; omega
  omega

/-- Theorem 1 for a symmetric `H` and a pointed polyhedron. -/
theorem main_ps : ∃ G : Polynomial ℕ, ∀ (n p m : ℕ), p ≤ n →
    ∀ (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (d : ℚ)
      (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ), H.transpose = H → IsPointedPoly A →
      (feasSet p H c d A b).Nonempty →
      ∃ x0 : Fin n → ℚ, toReal x0 ∈ feasSet p H c d A b ∧
        vecSize x0 ≤ G.eval (instSize H c d A b) := by
  obtain ⟨G1, h1⟩ := case1
  obtain ⟨G2, h2⟩ := case2
  refine ⟨G1 + G2, ?_⟩
  intro n p m hpn H c d A b hsym hA hF
  by_cases hneg : ∃ r ∈ recCone A, quadForm H r < 0
  · obtain ⟨x0, hx0, hs⟩ := h1 n p m hpn H c d A b hA hF hneg
    exact ⟨x0, hx0, hs.trans (by simp)⟩
  · push_neg at hneg
    obtain ⟨x0, hx0, hs⟩ := h2 n p m hpn H c d A b hsym hA hF hneg
    exact ⟨x0, hx0, hs.trans (by simp)⟩

end MIQPT1
/-! ### Part P -/

open MIQPInNP.SmallSol
open scoped BigOperators Pointwise

namespace MIQPT1

/-- The symmetric part `(H + Hᵀ)/2`. -/
def symmPart {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => (H i j + H j i) / 2

lemma symmPart_transpose {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) :
    (symmPart H).transpose = symmPart H := by
  ext i j; simp [symmPart, Matrix.transpose_apply]; ring

lemma quadForm_symmPart {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℝ) :
    quadForm (symmPart H) x = quadForm H x := by
  unfold quadForm symmPart
  have swap : ∑ i, ∑ j, x i * (H j i : ℝ) * x j = ∑ i, ∑ j, x i * (H i j : ℝ) * x j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  have e : ∀ i j, x i * (((H i j + H j i) / 2 : ℚ) : ℝ) * x j =
      (1 / 2) * (x i * (H i j : ℝ) * x j) + (1 / 2) * (x i * (H j i : ℝ) * x j) := by
    intro i j; push_cast; ring
  simp_rw [e, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [swap]; ring

lemma feasSet_symmPart {n m p : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (d : ℚ)
    (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) :
    feasSet p (symmPart H) c d A b = feasSet p H c d A b := by
  ext x; simp [feasSet, quadVal, quadForm_symmPart]

lemma sm_two : Sm 1 (2 : ℚ) := by constructor <;> simp

lemma matSize_symmPart {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) :
    matSize (symmPart H) ≤ 12 * matSize H := by
  have hb : ∀ i j, bitSize (symmPart H i j) ≤ 2 * bitSize (H i j) + 2 * bitSize (H j i) + 7 := by
    intro i j
    have := (sm_div (sm_add (sm_bitSize (H i j)) (sm_bitSize (H j i))) sm_two).bitSize_le
    simp only [symmPart]; omega
  have hs : ∑ i, ∑ j, bitSize (symmPart H i j) ≤
      2 * ∑ i, ∑ j, bitSize (H i j) + 2 * ∑ i, ∑ j, bitSize (H j i) + 7 * (n * n) := by
    calc ∑ i, ∑ j, bitSize (symmPart H i j) ≤
        ∑ i, ∑ j, (2 * bitSize (H i j) + 2 * bitSize (H j i) + 7) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hb i j))
      _ = 2 * ∑ i, ∑ j, bitSize (H i j) + 2 * ∑ i, ∑ j, bitSize (H j i) + 7 * (n * n) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]; simp; ring
  have hswap : ∑ i, ∑ j, bitSize (H j i) = ∑ i, ∑ j, bitSize (H i j) := Finset.sum_comm
  unfold matSize at hs ⊢
  rw [hswap] at hs
  omega

/-- Orthant sign constraints. -/
noncomputable def orth {n : ℕ} (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.diagonal (fun i => if 0 ≤ x i then -1 else 1)

lemma orth_row {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (y : Fin n → ℝ) :
    ∑ j, ((orth x i j : ℚ) : ℝ) * y j = ((if 0 ≤ x i then -1 else 1 : ℚ) : ℝ) * y i := by
  rw [Finset.sum_eq_single i]
  · simp [orth, Matrix.diagonal_apply]
  · intro j _ hj; simp [orth, Matrix.diagonal_apply, Ne.symm hj]
  · simp

lemma orth_mem {n : ℕ} (x : Fin n → ℝ) : x ∈ polyhedron (orth x) 0 := by
  intro i
  rw [orth_row]
  split_ifs with h
  · simp; linarith
  · simp; push_neg at h; linarith

lemma pointed_stack_orth {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (x : Fin n → ℝ) :
    IsPointedPoly (stack A (orth x)) := by
  intro y hy
  ext i
  have := hy (Fin.natAdd m i)
  rw [stack_natAdd] at this
  have h := orth_row x i y
  rw [this] at h
  split_ifs at h with hx
  · simp at h; simp; linarith
  · simp at h; simp; linarith

lemma matSize_orth {n : ℕ} (x : Fin n → ℝ) : matSize (orth x) ≤ 4 * (n * n) := by
  have := matSize_le_of_sm (E := 0) (orth x) (fun i j => by
    by_cases h : i = j
    · subst h; simp only [orth, Matrix.diagonal_apply_eq]
      split_ifs
      · exact sm0_neg_one
      · exact sm0_one
    · simp only [orth, Matrix.diagonal_apply_ne _ h]; exact sm_zero 0)
  simpa [mul_comm] using this

end MIQPT1

namespace MIQPT1

theorem thm1_gen :
    ∃ f : Polynomial ℕ, ∀ (n p m : ℕ), p ≤ n →
      ∀ (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (d : ℚ)
        (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
        (feasSet p H c d A b).Nonempty →
        ∃ x0 : Fin n → ℚ, toReal x0 ∈ feasSet p H c d A b ∧
          vecSize x0 ≤ f.eval (instSize H c d A b) := by
  obtain ⟨G, hG⟩ := main_ps
  refine ⟨G.comp (19 * Polynomial.X), ?_⟩
  intro n p m hpn H c d A b ⟨x, hx⟩
  have hx' : x ∈ feasSet p (symmPart H) c d (stack A (orth x)) (stackv b 0) := by
    rw [feasSet_symmPart]
    refine ⟨hx.1, ?_, hx.2.2⟩
    rw [polyhedron_stack]
    exact ⟨hx.2.1, orth_mem x⟩
  obtain ⟨x0, hx0, hs⟩ := hG n p (m + n) hpn (symmPart H) c d (stack A (orth x)) (stackv b 0)
    (symmPart_transpose H) (pointed_stack_orth A x) ⟨x, hx'⟩
  refine ⟨x0, ?_, hs.trans ?_⟩
  · rw [feasSet_symmPart] at hx0
    refine ⟨hx0.1, ?_, hx0.2.2⟩
    have := hx0.2.1
    rw [polyhedron_stack] at this
    exact this.1
  · rw [Polynomial.eval_comp]
    apply peval_mono
    simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    unfold instSize
    rw [matSize_stack, vecSize_stackv, vecSize_zero]
    have h1 := matSize_symmPart H
    have h2 := matSize_orth x
    have h3 := mn_le_matSize H
    have h4 := Nat.le_mul_self n
    omega

end MIQPT1
/-! ### Part T3 -/

open MIQPInNP.SmallSol

open MIQPT1 in
theorem solution :
    ∃ g : Polynomial ℕ,
      (∀ (n m : ℕ) (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (d : ℚ)
        (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
        (feasSet 0 H c d A b).Nonempty →
        ∃ xh : Fin n → ℚ, toReal xh ∈ feasSet 0 H c d A b ∧
          vecSize xh ≤ g.eval (instSize H c d A b)) ∧
      (∀ (n m : ℕ) (H : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) (d : ℚ)
        (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
        (∃ x ∈ polyhedron A b, ∀ y ∈ polyhedron A b, quadVal H c 0 x ≤ quadVal H c 0 y) →
        ∃ xh : Fin n → ℚ, toReal xh ∈ polyhedron A b ∧
          (∀ y ∈ polyhedron A b, quadVal H c 0 (toReal xh) ≤ quadVal H c 0 y) ∧
          vecSize xh ≤ g.eval (instSize H c d A b)) := by
  obtain ⟨f, hf⟩ := thm1_gen
  obtain ⟨g, hg⟩ := thm3b
  refine ⟨f + g, fun n m H c d A b hF => ?_, fun n m H c d A b hmin => ?_⟩
  · obtain ⟨x0, hx0, hs⟩ := hf n 0 m (Nat.zero_le n) H c d A b hF
    exact ⟨x0, hx0, hs.trans (by simp)⟩
  · obtain ⟨x0, hx0, hopt, hs⟩ := hg n m H c d A b hmin
    exact ⟨x0, hx0, hopt, hs.trans (by simp)⟩
