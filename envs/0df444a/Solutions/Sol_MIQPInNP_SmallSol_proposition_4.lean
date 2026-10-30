-- Prove2me | solution 1 for MIQPInNP.SmallSol.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T09:12:21.547709+00:00
-- url     : https://prove2.me/submissions/23d46511-5476-44af-9472-4fda7e7c1017

import Mathlib
import Definitions.Def_MIQPInNP_SmallSol_Setting

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
/-! ### Part U1 -/

open MIQPInNP.SmallSol
open scoped BigOperators Pointwise

namespace MIQPT1

/-- Row value `G_i · y`. -/
noncomputable def rv {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) (y : Fin n → ℝ) : ℝ :=
  ∑ j, (G i j : ℝ) * y j

lemma rv_add_smul {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) (y d : Fin n → ℝ) (t : ℝ) :
    rv G i (y + t • d) = rv G i y + t * rv G i d := by
  unfold rv
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma rv_combo {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) (y z : Fin n → ℝ) (a b : ℝ) :
    rv G i (a • y + b • z) = a * rv G i y + b * rv G i z := by
  unfold rv
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- `v` is a vertex of `{G y ≤ h}`: the tight rows determine it. -/
def IsVert {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℚ) (h : Fin m → ℚ) (v : Fin n → ℝ) : Prop :=
  v ∈ polyhedron G h ∧ ∀ d : Fin n → ℝ, (∀ i, rv G i v = h i → rv G i d = 0) → d = 0

/-- The non-tight rows. -/
noncomputable def slackSet {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℚ) (h : Fin m → ℚ)
    (y : Fin n → ℝ) : Finset (Fin m) :=
  by classical exact Finset.univ.filter (fun i => rv G i y ≠ h i)

lemma move {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℚ) (h : Fin m → ℚ) (y : Fin n → ℝ)
    (hy : y ∈ polyhedron G h) (d : Fin n → ℝ) (hd : ∀ i, rv G i y = h i → rv G i d = 0)
    (hpos : ∃ i, 0 < rv G i d) :
    ∃ t : ℝ, 0 < t ∧ y + t • d ∈ polyhedron G h ∧
      (slackSet G h (y + t • d)).card < (slackSet G h y).card := by
  classical
  set S := Finset.univ.filter (fun i => 0 < rv G i d) with hS
  have hSne : S.Nonempty := by obtain ⟨i, hi⟩ := hpos; exact ⟨i, by simp [hS, hi]⟩
  obtain ⟨i0, hi0, hmin⟩ := S.exists_min_image (fun i => ((h i : ℝ) - rv G i y) / rv G i d) hSne
  have hi0pos : 0 < rv G i0 d := by simpa [hS] using hi0
  have hslack : ∀ i ∈ S, 0 < (h i : ℝ) - rv G i y := by
    intro i hi
    have hipos : 0 < rv G i d := by simpa [hS] using hi
    have hle : rv G i y ≤ h i := hy i
    rcases hle.lt_or_eq with hlt | heq
    · linarith
    · exact absurd (hd i heq) hipos.ne'
  set t := ((h i0 : ℝ) - rv G i0 y) / rv G i0 d with ht
  have htpos : 0 < t := div_pos (hslack i0 hi0) hi0pos
  have hmem : y + t • d ∈ polyhedron G h := by
    intro i
    show rv G i (y + t • d) ≤ h i
    rw [rv_add_smul]
    by_cases hi : 0 < rv G i d
    · have h1 := hmin i (by simp [hS, hi])
      have : t * rv G i d ≤ (h i : ℝ) - rv G i y := by
        have := mul_le_mul_of_nonneg_right h1 hi.le
        rwa [div_mul_cancel₀ _ hi.ne'] at this
      linarith
    · push_neg at hi
      have h1 : rv G i y ≤ h i := hy i
      have : t * rv G i d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos htpos.le hi
      linarith
  refine ⟨t, htpos, hmem, Finset.card_lt_card ⟨?_, ?_⟩⟩
  · intro i hi
    simp only [slackSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    intro heq
    apply hi
    rw [rv_add_smul, hd i heq, mul_zero, add_zero, heq]
  · intro hsub
    have h1 : i0 ∈ slackSet G h y := by
      simp only [slackSet, Finset.mem_filter, Finset.mem_univ, true_and]
      have := hslack i0 hi0; intro h'; linarith
    have h2 := hsub h1
    simp only [slackSet, Finset.mem_filter, Finset.mem_univ, true_and] at h2
    apply h2
    rw [rv_add_smul, ht, div_mul_cancel₀ _ hi0pos.ne']; ring

/-- Induction over the faces of a pointed polyhedron. -/
theorem face_induction {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℚ) (h : Fin m → ℚ)
    (hpt : ∀ d : Fin n → ℝ, (∀ i, rv G i d = 0) → d = 0)
    (Φ : (Fin n → ℝ) → Prop) (hV : ∀ v, IsVert G h v → Φ v)
    (hC : ∀ y1 ∈ polyhedron G h, ∀ y2 ∈ polyhedron G h, Φ y1 → Φ y2 → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a + b = 1 → Φ (a • y1 + b • y2))
    (hR : ∀ y ∈ polyhedron G h, Φ y → ∀ d : Fin n → ℝ, (∀ i, rv G i d ≤ 0) → ∀ t : ℝ, 0 ≤ t →
      Φ (y + t • d)) :
    ∀ y ∈ polyhedron G h, Φ y := by
  classical
  intro y hy
  induction hk : (slackSet G h y).card using Nat.strong_induction_on generalizing y with
  | _ k ih =>
  by_cases hvert : IsVert G h y
  · exact hV y hvert
  have : ∃ d : Fin n → ℝ, (∀ i, rv G i y = h i → rv G i d = 0) ∧ d ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hvert ⟨hy, hcon⟩
  obtain ⟨d, hd, hd0⟩ := this
  have hd' : ∀ i, rv G i y = h i → rv G i (-d) = 0 := by
    intro i hi; have := hd i hi; unfold rv at this ⊢; simp [this]
  have rvneg : ∀ i, rv G i (-d) = - rv G i d := by intro i; unfold rv; simp
  by_cases hp : ∃ i, 0 < rv G i d
  · obtain ⟨t1, ht1, hy1, hc1⟩ := move G h y hy d hd hp
    have IH1 := ih _ (hk ▸ hc1) (y + t1 • d) hy1 rfl
    by_cases hn : ∃ i, 0 < rv G i (-d)
    · obtain ⟨t2, ht2, hy2, hc2⟩ := move G h y hy (-d) hd' hn
      have IH2 := ih _ (hk ▸ hc2) (y + t2 • -d) hy2 rfl
      have key := hC _ hy1 _ hy2 IH1 IH2 (t2 / (t1 + t2)) (t1 / (t1 + t2)) (by positivity)
        (by positivity) (by field_simp; ring)
      convert key using 1
      have hsum : 0 < t1 + t2 := by positivity
      have hab : t2 / (t1 + t2) + t1 / (t1 + t2) = 1 := by field_simp; ring
      have h0 : t2 / (t1 + t2) * t1 - t1 / (t1 + t2) * t2 = 0 := by ring
      ext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
      linear_combination (-(y j)) * hab + (-(d j)) * h0
    · push_neg at hn
      -- `-(-d) = d` is a recession direction... here `d` itself: rows with `-d > 0` absent,
      -- so `rv G i d ≥ 0`; hence `-d` is a recession direction
      have hrec : ∀ i, rv G i (-d) ≤ 0 := hn
      have := hR _ hy1 IH1 (-d) hrec t1 ht1.le
      convert this using 1
      ext j; simp
  · push_neg at hp
    have hn : ∃ i, 0 < rv G i (-d) := by
      by_contra hcon
      push_neg at hcon
      apply hd0
      apply hpt
      intro i
      have h1 := hp i; have h2 := hcon i; rw [rvneg] at h2; linarith
    obtain ⟨t2, ht2, hy2, hc2⟩ := move G h y hy (-d) hd' hn
    have IH2 := ih _ (hk ▸ hc2) (y + t2 • -d) hy2 rfl
    have := hR _ hy2 IH2 d hp t2 ht2.le
    convert this using 1
    ext j; simp

end MIQPT1
/-! ### Part U2 -/

open MIQPInNP.SmallSol
open scoped BigOperators Pointwise

namespace MIQPT1

lemma sm_of_PD_bound {E : ℕ} (P D : ℤ) (hD : D ≠ 0) (hP : |P| ≤ 2 ^ E) (hDb : |D| ≤ 2 ^ E) :
    Sm E ((P : ℚ) / D) := by
  apply sm_of_div P D hD
  · have : (P.natAbs : ℤ) ≤ 2 ^ E := by rw [Int.natCast_natAbs]; exact hP
    exact_mod_cast this
  · have : (D.natAbs : ℤ) ≤ 2 ^ E := by rw [Int.natCast_natAbs]; exact hDb
    exact_mod_cast this

lemma rs_sum_le {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℚ) (h : Fin m → ℚ) (I : Finset (Fin m)) :
    ∑ i ∈ I, M5Core.rs G h i ≤ matSize G + vecSize h := by
  calc ∑ i ∈ I, M5Core.rs G h i ≤ ∑ i, M5Core.rs G h i :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ I)
    _ = ∑ i, ∑ j, bitSize (G i j) + ∑ i, bitSize (h i) := by
        simp [M5Core.rs, Finset.sum_add_distrib]
    _ ≤ matSize G + vecSize h := by unfold matSize vecSize; omega

/-- Vertices are small rational points. -/
lemma vert_small {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℚ) (h : Fin m → ℚ) (v : Fin n → ℝ)
    (hv : IsVert G h v) : ∃ vq : Fin n → ℚ, v = toReal vq ∧
      ∀ j, Sm (M5Core.alpha n (matSize G + vecSize h)) (vq j) := by
  classical
  obtain ⟨y, hyT, I, -, D, hD, hDb, hP⟩ := M5Core.small_solve G h
    (Finset.univ.filter (fun i => rv G i v = h i)) v
    (fun i hi => by have := (Finset.mem_filter.mp hi).2; exact this)
  have hyv : toReal y = v := by
    have := hv.2 (toReal y - v) (fun i hi => by
      have h1 := hyT i (by simp [hi])
      unfold rv; unfold M5Core.rdot at h1; unfold rv at hi
      simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      linarith)
    exact sub_eq_zero.mp this
  refine ⟨y, hyv.symm, fun j => ?_⟩
  obtain ⟨P, hPb, hPe⟩ := hP j
  have hα : M5Core.alpha n (∑ i ∈ I, M5Core.rs G h i) ≤ M5Core.alpha n (matSize G + vecSize h) := by
    unfold M5Core.alpha; gcongr; exact rs_sum_le G h I
  rw [hPe]
  exact (sm_of_PD_bound P D hD hPb hDb).mono hα

lemma vert_finite {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℚ) (h : Fin m → ℚ) :
    {v | IsVert G h v}.Finite := by
  classical
  refine Set.Finite.of_finite_image (f := fun v => Finset.univ.filter (fun i => rv G i v = h i))
    (Set.toFinite _) ?_
  · intro v hv w hw heq
    simp only at heq
    have hd := hv.2 (v - w) (fun i hi => by
      have hi' : i ∈ Finset.univ.filter (fun i => rv G i v = h i) := by simp [hi]
      rw [heq] at hi'
      have hwi : rv G i w = h i := by simpa using hi'
      unfold rv at hi hwi ⊢
      simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      linarith)
    exact sub_eq_zero.mp hd

lemma rec_zero_of_bounded {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℚ) (h : Fin m → ℚ)
    (hb : Bornology.IsBounded (polyhedron G h)) (y : Fin n → ℝ) (hy : y ∈ polyhedron G h)
    (d : Fin n → ℝ) (hd : ∀ i, rv G i d ≤ 0) : d = 0 := by
  rw [isBounded_iff_forall_norm_le] at hb
  obtain ⟨C, hC⟩ := hb
  have hmem : ∀ t : ℝ, 0 ≤ t → y + t • d ∈ polyhedron G h := by
    intro t ht i
    show rv G i (y + t • d) ≤ h i
    rw [rv_add_smul]
    have : t * rv G i d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht (hd i)
    have h1 : rv G i y ≤ h i := hy i
    linarith
  by_contra hne
  have hpos : 0 < ‖d‖ := norm_pos_iff.mpr hne
  set t := (C + ‖y‖ + 1) / ‖d‖ with ht
  have ht0 : 0 ≤ t := by
    have : 0 ≤ C := (norm_nonneg y).trans (hC y hy)
    positivity
  have h1 := hC _ (hmem t ht0)
  have h2 : ‖t • d‖ ≤ ‖y + t • d‖ + ‖y‖ := by
    calc ‖t • d‖ = ‖(y + t • d) - y‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖y + t • d‖ + ‖y‖ := norm_sub_le _ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, ht, div_mul_cancel₀ _ hpos.ne'] at h2
  linarith

lemma pointed_of_bounded {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℚ) (h : Fin m → ℚ)
    (hb : Bornology.IsBounded (polyhedron G h)) (y : Fin n → ℝ) (hy : y ∈ polyhedron G h) :
    ∀ d : Fin n → ℝ, (∀ i, rv G i d = 0) → d = 0 :=
  fun d hd => rec_zero_of_bounded G h hb y hy d (fun i => le_of_eq (hd i))

/-- Minkowski for polytopes: a bounded polyhedron is the convex hull of its vertices. -/
theorem vert_hull {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℚ) (h : Fin m → ℚ)
    (hb : Bornology.IsBounded (polyhedron G h)) :
    ∀ y ∈ polyhedron G h, y ∈ convexHull ℝ {v | IsVert G h v} := by
  intro y hy
  refine face_induction G h (pointed_of_bounded G h hb y hy) (fun z => z ∈ convexHull ℝ {v | IsVert G h v})
    (fun v hv => subset_convexHull ℝ _ hv) ?_ ?_ y hy
  · intro y1 _ y2 _ h1 h2 a b ha hb' hab
    exact (convex_convexHull ℝ _) h1 h2 ha hb' hab
  · intro z hz hΦ d hd t _
    rw [rec_zero_of_bounded G h hb z hz d hd, smul_zero, add_zero]; exact hΦ

lemma polyhedron_convex {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℚ) (h : Fin m → ℚ)
    (y1 y2 : Fin n → ℝ) (h1 : y1 ∈ polyhedron G h) (h2 : y2 ∈ polyhedron G h) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : a • y1 + b • y2 ∈ polyhedron G h := by
  intro i
  show rv G i (a • y1 + b • y2) ≤ h i
  rw [rv_combo]
  have e1 : rv G i y1 ≤ h i := h1 i
  have e2 : rv G i y2 ≤ h i := h2 i
  have f1 := mul_le_mul_of_nonneg_left e1 ha
  have f2 := mul_le_mul_of_nonneg_left e2 hb
  have : a * (h i : ℝ) + b * h i = h i := by rw [← add_mul, hab, one_mul]
  linarith

/-- Every point of a pointed polyhedron is a point of small norm plus a recession direction. -/
theorem decomp {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℚ) (h : Fin m → ℚ)
    (hpt : ∀ d : Fin n → ℝ, (∀ i, rv G i d = 0) → d = 0) :
    ∀ y ∈ polyhedron G h, ∃ v r : Fin n → ℝ, v ∈ polyhedron G h ∧ (∀ i, rv G i r ≤ 0) ∧
      y = v + r ∧ ∀ j, |v j| ≤ 2 ^ M5Core.alpha n (matSize G + vecSize h) := by
  refine face_induction G h hpt _ ?_ ?_ ?_
  · intro v hv
    refine ⟨v, 0, hv.1, fun i => by simp [rv], by simp, fun j => ?_⟩
    obtain ⟨vq, rfl, hvq⟩ := vert_small G h v hv
    exact sm_abs_le_real (hvq j)
  · rintro y1 hy1 y2 hy2 ⟨v1, r1, hv1, hr1, rfl, hb1⟩ ⟨v2, r2, hv2, hr2, rfl, hb2⟩ a b ha hb hab
    refine ⟨a • v1 + b • v2, a • r1 + b • r2, polyhedron_convex G h v1 v2 hv1 hv2 a b ha hb hab,
      fun i => ?_, by ext j; simp; ring, fun j => ?_⟩
    · rw [rv_combo]; nlinarith [hr1 i, hr2 i]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc |a * v1 j + b * v2 j| ≤ a * |v1 j| + b * |v2 j| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
        _ ≤ a * 2 ^ M5Core.alpha n (matSize G + vecSize h) +
            b * 2 ^ M5Core.alpha n (matSize G + vecSize h) := by
            gcongr
            · exact hb1 j
            · exact hb2 j
        _ = _ := by rw [← add_mul, hab, one_mul]
  · rintro y _ ⟨v, r, hv, hr, rfl, hb⟩ d hd t ht
    refine ⟨v, r + t • d, hv, fun i => ?_, by ext j; simp; ring, hb⟩
    rw [show r + t • d = r + t • d from rfl, rv_add_smul]
    nlinarith [hr i, hd i]

end MIQPT1
/-! ### Part U3 -/

open MIQPInNP.SmallSol
open scoped BigOperators Pointwise

namespace MIQPT1

def rowv {n : ℕ} (φ : Fin n → ℚ) : Matrix (Fin 1) (Fin n) ℚ := fun _ k => φ k

/-- The normalising functional `f = -∑ᵢ Aᵢ` of a pointed recession cone. -/
def normF {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : Fin n → ℚ := fun j => -∑ i, A i j

def sliceG {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : Matrix (Fin (m + (1 + 1))) (Fin n) ℚ :=
  stack A (stack (rowv (normF A)) (rowv (-normF A)))

def sliceH (m : ℕ) : Fin (m + (1 + 1)) → ℚ :=
  stackv 0 (stackv (fun _ => 1) (fun _ => -1))

lemma normF_dot {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (y : Fin n → ℝ) :
    ∑ j, ((normF A j : ℚ) : ℝ) * y j = ∑ i, -rv A i y := by
  unfold normF rv
  simp only [Rat.cast_neg, Rat.cast_sum, neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma rv_sliceG_cast {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) (y : Fin n → ℝ) :
    rv (sliceG A) (Fin.castAdd (1 + 1) i) y = rv A i y := by
  unfold rv sliceG; rw [stack_castAdd]

lemma rv_sliceG_f {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (y : Fin n → ℝ) :
    rv (sliceG A) (Fin.natAdd m (Fin.castAdd 1 0)) y = ∑ i, -rv A i y := by
  unfold sliceG
  have : rv (stack A (stack (rowv (normF A)) (rowv (-normF A)))) (Fin.natAdd m (Fin.castAdd 1 0)) y
      = ∑ j, ((normF A j : ℚ) : ℝ) * y j := by
    unfold rv; rw [stack_natAdd, stack_castAdd]; rfl
  rw [this, normF_dot]

lemma rv_sliceG_nf {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (y : Fin n → ℝ) :
    rv (sliceG A) (Fin.natAdd m (Fin.natAdd 1 0)) y = -∑ i, -rv A i y := by
  unfold sliceG
  have : rv (stack A (stack (rowv (normF A)) (rowv (-normF A)))) (Fin.natAdd m (Fin.natAdd 1 0)) y
      = -∑ j, ((normF A j : ℚ) : ℝ) * y j := by
    unfold rv; rw [stack_natAdd, stack_natAdd]
    simp [rowv, Finset.sum_neg_distrib]
  rw [this, normF_dot]

lemma sliceH_cast (m : ℕ) (i : Fin m) : sliceH m (Fin.castAdd (1 + 1) i) = 0 := by
  unfold sliceH; rw [stackv_castAdd]; rfl
lemma sliceH_f (m : ℕ) : sliceH m (Fin.natAdd m (Fin.castAdd 1 0)) = 1 := by
  unfold sliceH; rw [stackv_natAdd, stackv_castAdd]
lemma sliceH_nf (m : ℕ) : sliceH m (Fin.natAdd m (Fin.natAdd 1 0)) = -1 := by
  unfold sliceH; rw [stackv_natAdd, stackv_natAdd]

lemma forall_slice {m : ℕ} (P : Fin (m + (1 + 1)) → Prop) :
    (∀ i, P i) ↔ (∀ i : Fin m, P (Fin.castAdd (1 + 1) i)) ∧ P (Fin.natAdd m (Fin.castAdd 1 0)) ∧
      P (Fin.natAdd m (Fin.natAdd 1 0)) := by
  rw [Fin.forall_fin_add]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2 _, h2 _⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun k => ?_⟩
    refine Fin.addCases (fun a => ?_) (fun a => ?_) k
    · have : a = 0 := Subsingleton.elim _ _
      subst this; exact h2
    · have : a = 0 := Subsingleton.elim _ _
      subst this; exact h3

lemma slice_cases {m : ℕ} (i : Fin (m + (1 + 1))) :
    (∃ k : Fin m, i = Fin.castAdd (1 + 1) k) ∨ i = Fin.natAdd m (Fin.castAdd 1 0) ∨
      i = Fin.natAdd m (Fin.natAdd 1 0) := by
  have := (forall_slice (fun i : Fin (m + (1 + 1)) => (∃ k : Fin m, i = Fin.castAdd (1 + 1) k) ∨
    i = Fin.natAdd m (Fin.castAdd 1 0) ∨ i = Fin.natAdd m (Fin.natAdd 1 0))).mpr
    ⟨fun k => Or.inl ⟨k, rfl⟩, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩
  exact this i

lemma mem_slice {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (y : Fin n → ℝ) :
    y ∈ polyhedron (sliceG A) (sliceH m) ↔ (∀ i, rv A i y ≤ 0) ∧ ∑ i, -rv A i y = 1 := by
  show (∀ i, rv (sliceG A) i y ≤ sliceH m i) ↔ _
  rw [forall_slice]
  simp only [rv_sliceG_cast, rv_sliceG_f, rv_sliceG_nf, sliceH_cast, sliceH_f, sliceH_nf,
    Rat.cast_zero, Rat.cast_one, Rat.cast_neg]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, le_of_eq h2, by linarith⟩

lemma slice_bounded {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (hA : IsPointedPoly A) :
    Bornology.IsBounded (polyhedron (sliceG A) (sliceH m)) := by
  refine bounded_of_pointed A hA _ 1 (fun y hy i => ?_)
  obtain ⟨h1, h2⟩ := (mem_slice A y).mp hy
  have hle : -rv A i y ≤ 1 := by
    rw [← h2]
    exact Finset.single_le_sum (f := fun i => -rv A i y) (fun j _ => by linarith [h1 j])
      (Finset.mem_univ i)
  show |rv A i y| ≤ 1
  rw [abs_le]; constructor <;> linarith [h1 i]

lemma rv_eq_zero_of_sum {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (y : Fin n → ℝ)
    (h1 : ∀ i, rv A i y ≤ 0) (h2 : ∑ i, -rv A i y = 0) : ∀ i, rv A i y = 0 := by
  intro i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by linarith [h1 j])).mp h2 i
    (Finset.mem_univ i)
  linarith

lemma cone_convex {n : ℕ} (S : Set (Fin n → ℝ)) : Convex ℝ (cone S) := by
  intro x hx y hy a b ha hb _
  unfold cone at hx hy ⊢
  have h1 : a • x = (⟨a, ha⟩ : NNReal) • x := by ext u; simp [NNReal.smul_def]
  have h2 : b • y = (⟨b, hb⟩ : NNReal) • y := by ext u; simp [NNReal.smul_def]
  rw [h1, h2]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hx) (Submodule.smul_mem _ _ hy)

/-- A pointed rational cone is generated by the vertices of its slice. -/
theorem cone_gen {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (hA : IsPointedPoly A) :
    ∀ y ∈ recCone A, y ∈ cone {v | IsVert (sliceG A) (sliceH m) v} := by
  intro y hy
  have hy' : ∀ i, rv A i y ≤ 0 := fun i => by
    have := hy i; simpa [rv] using this
  set s := ∑ i, -rv A i y with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg (fun i _ => by linarith [hy' i])
  rcases hs0.lt_or_eq with hpos | hzero
  · set z := (1 / s) • y with hz
    have hzQ : z ∈ polyhedron (sliceG A) (sliceH m) := by
      rw [mem_slice]
      refine ⟨fun i => ?_, ?_⟩
      · rw [hz, show (1 / s) • y = 0 + (1 / s) • y by simp, rv_add_smul]
        simp [rv]
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by simpa [rv] using hy' i)
      · have : ∀ i, -rv A i z = (1 / s) * -rv A i y := by
          intro i; rw [hz, show (1 / s) • y = 0 + (1 / s) • y by simp, rv_add_smul]; simp [rv]
        rw [Finset.sum_congr rfl (fun i _ => this i), ← Finset.mul_sum, ← hs]
        field_simp
    have hzc := vert_hull _ _ (slice_bounded A hA) z hzQ
    have hzc' : z ∈ cone {v | IsVert (sliceG A) (sliceH m) v} :=
      convexHull_min (fun v hv => by unfold cone; exact Submodule.subset_span hv) (cone_convex _) hzc
    have : y = s • z := by rw [hz, smul_smul, mul_one_div_cancel hpos.ne', one_smul]
    rw [this]
    unfold cone at hzc' ⊢
    have h1 : s • z = (⟨s, hpos.le⟩ : NNReal) • z := by ext u; simp [NNReal.smul_def]
    rw [h1]; exact Submodule.smul_mem _ _ hzc'
  · have := rv_eq_zero_of_sum A y hy' hzero.symm
    have hy0 : y = 0 := hA y (fun i => by have := this i; simpa [rv] using this)
    rw [hy0]; unfold cone; exact Submodule.zero_mem _

/-- Vertices of the slice span extreme rays of the cone. -/
theorem vert_extreme {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (v : Fin n → ℝ)
    (hv : IsVert (sliceG A) (sliceH m) v) : IsExtremeRayOf (recCone A) v := by
  obtain ⟨hv1, hv2⟩ := (mem_slice A v).mp hv.1
  have hrec : ∀ x, x ∈ recCone A ↔ ∀ i, rv A i x ≤ 0 := by
    intro x; constructor
    · intro hx i; have := hx i; simpa [rv] using this
    · intro hx i; have := hx i; simpa [rv] using this
  refine ⟨(hrec v).mpr hv1, fun h0 => by simp [h0, rv] at hv2, fun u hu w hw huw => ?_⟩
  rw [hrec] at hu hw
  set t := ∑ i, -rv A i u with ht
  refine ⟨t, Finset.sum_nonneg (fun i _ => by linarith [hu i]), ?_⟩
  have hd := hv.2 (u - t • v) (fun i hi => ?_)
  · exact sub_eq_zero.mp hd
  · have hsub : rv (sliceG A) i (u - t • v) = rv (sliceG A) i u - t * rv (sliceG A) i v := by
      rw [show u - t • v = u + (-t) • v by rw [neg_smul, sub_eq_add_neg], rv_add_smul]; ring
    rw [hsub]
    rcases slice_cases i with ⟨k, rfl⟩ | rfl | rfl
    · have hk := hi
      rw [rv_sliceG_cast] at hk ⊢
      rw [rv_sliceG_cast]
      have hk' : rv A k v = 0 := by rw [hk, sliceH_cast]; simp
      have : rv A k u + rv A k w = 0 := by
        rw [← hk', ← huw]; unfold rv; rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_); simp; ring
      have : rv A k u = 0 := by linarith [hu k, hw k]
      rw [this, hk']; ring
    · rw [rv_sliceG_f, rv_sliceG_f, hv2, ← ht]; ring
    · rw [rv_sliceG_nf, rv_sliceG_nf, hv2, ← ht]; ring

lemma extreme_smul {n : ℕ} {m : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (v : Fin n → ℝ)
    (hv : IsExtremeRayOf (recCone A) v) (c : ℝ) (hc : 0 < c) :
    IsExtremeRayOf (recCone A) (c • v) := by
  obtain ⟨h1, h2, h3⟩ := hv
  refine ⟨recCone_smul A c hc.le v h1, smul_ne_zero hc.ne' h2, fun u hu w hw huw => ?_⟩
  obtain ⟨t, ht, hut⟩ := h3 ((1 / c) • u) (recCone_smul A _ (by positivity) u hu)
    ((1 / c) • w) (recCone_smul A _ (by positivity) w hw)
    (by rw [← smul_add, huw, smul_smul, one_div_mul_cancel hc.ne', one_smul])
  refine ⟨t, ht, ?_⟩
  have : u = c • ((1 / c) • u) := by rw [smul_smul, mul_one_div_cancel hc.ne', one_smul]
  rw [this, hut, smul_smul, smul_smul, mul_comm]

end MIQPT1
/-! ### Part U4 -/

open MIQPInNP.SmallSol
open scoped BigOperators Pointwise

namespace MIQPT1

/-- Integer vectors read as real vectors. -/
def iR {n : ℕ} (r : Fin n → ℤ) : Fin n → ℝ := fun j => (r j : ℝ)

lemma mem_cone_finset {n : ℕ} (T : Finset (Fin n → ℤ)) (y : Fin n → ℝ) :
    y ∈ cone (iR '' (T : Set (Fin n → ℤ))) ↔
      ∃ l : (Fin n → ℤ) → ℝ, (∀ r, 0 ≤ l r) ∧ y = ∑ r ∈ T, l r • iR r := by
  classical
  constructor
  · intro hy
    unfold cone at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, hr, rfl⟩ := hx
      refine ⟨fun s => if s = r then 1 else 0, fun s => by simp only; split_ifs <;> norm_num, ?_⟩
      rw [Finset.sum_eq_single r]
      · simp
      · intro s _ hs; simp [hs]
      · intro h; exact absurd hr h
    | zero => exact ⟨0, fun _ => le_rfl, by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨l1, h1, rfl⟩ := hx
      obtain ⟨l2, h2, rfl⟩ := hz
      refine ⟨l1 + l2, fun r => add_nonneg (h1 r) (h2 r), ?_⟩
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun r _ => by simp [add_smul])
    | smul a x _ hx =>
      obtain ⟨l, h, rfl⟩ := hx
      refine ⟨fun r => (a : ℝ) * l r, fun r => mul_nonneg a.2 (h r), ?_⟩
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [NNReal.smul_def, smul_smul]
  · rintro ⟨l, hl, rfl⟩
    unfold cone
    refine Submodule.sum_mem _ (fun r hr => ?_)
    have : l r • iR r = (⟨l r, hl r⟩ : NNReal) • iR r := by ext u; simp [NNReal.smul_def]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, hr, rfl⟩)

/-- Carathéodory's theorem for cones. -/
theorem caratheodory_cone {n : ℕ} (T : Finset (Fin n → ℤ)) :
    ∀ y ∈ cone (iR '' (T : Set (Fin n → ℤ))), ∃ T' ⊆ T,
      LinearIndependent ℝ (fun r : T' => iR (r : Fin n → ℤ)) ∧
      y ∈ cone (iR '' (T' : Set (Fin n → ℤ))) := by
  classical
  induction T using Finset.strongInduction with
  | H T ih =>
    intro y hy
    by_cases hli : LinearIndependent ℝ (fun r : T => iR (r : Fin n → ℤ))
    · exact ⟨T, le_rfl, hli, hy⟩
    obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hli
    -- extend and normalise the dependency
    set G0 : (Fin n → ℤ) → ℝ := fun r => if h : r ∈ T then g ⟨r, h⟩ else 0 with hG0
    have hG0sum : ∑ r ∈ T, G0 r • iR r = 0 := by
      rw [← hg, ← Finset.sum_attach]
      refine Finset.sum_bij (fun r _ => r) (fun _ _ => Finset.mem_univ _) (fun _ _ _ _ h => h)
        (fun b _ => ⟨b, Finset.mem_attach _ _, rfl⟩) (fun r _ => ?_)
      simp [hG0, r.2]
    obtain ⟨G, hGsum, hGpos, hGout⟩ : ∃ G : (Fin n → ℤ) → ℝ, ∑ r ∈ T, G r • iR r = 0 ∧
        (∃ r ∈ T, 0 < G r) ∧ ∀ r, r ∉ T → G r = 0 := by
      have hi0' : G0 i0 ≠ 0 := by simp [hG0, i0.2, hi0]
      rcases hi0'.lt_or_gt with hneg | hpos
      · refine ⟨fun r => -G0 r, ?_, ⟨i0, i0.2, by simp; linarith⟩, fun r hr => by simp [hG0, hr]⟩
        simp only [neg_smul, Finset.sum_neg_distrib, hG0sum, neg_zero]
      · exact ⟨G0, hG0sum, ⟨i0, i0.2, hpos⟩, fun r hr => by simp [hG0, hr]⟩
    obtain ⟨l, hl, rfl⟩ := (mem_cone_finset T y).mp hy
    set Pos := T.filter (fun r => 0 < G r) with hPos
    have hPne : Pos.Nonempty := by
      obtain ⟨r, hr, hr'⟩ := hGpos; exact ⟨r, by simp [hPos, hr, hr']⟩
    obtain ⟨r0, hr0, hmin⟩ := Pos.exists_min_image (fun r => l r / G r) hPne
    obtain ⟨hr0T, hr0pos⟩ : r0 ∈ T ∧ 0 < G r0 := by simpa [hPos] using hr0
    set θ := l r0 / G r0 with hθ
    have hθ0 : 0 ≤ θ := div_nonneg (hl r0) hr0pos.le
    set l' : (Fin n → ℤ) → ℝ := fun r => l r - θ * G r with hl'
    have hl'0 : ∀ r, 0 ≤ l' r := by
      intro r
      by_cases hr : r ∈ Pos
      · obtain ⟨-, hrpos⟩ : r ∈ T ∧ 0 < G r := by simpa [hPos] using hr
        have := hmin r hr
        have : θ * G r ≤ l r := by
          have h2 := mul_le_mul_of_nonneg_right this hrpos.le
          rwa [div_mul_cancel₀ _ hrpos.ne'] at h2
        simp only [hl']; linarith
      · have : G r ≤ 0 := by
          by_cases hrT : r ∈ T
          · have : ¬ (0 < G r) := fun h => hr (by simp [hPos, hrT, h])
            linarith [not_lt.mp this]
          · rw [hGout r hrT]
        simp only [hl']; nlinarith [hl r]
    have hl'r0 : l' r0 = 0 := by simp only [hl', hθ]; field_simp; ring
    have hy' : ∑ r ∈ T, l r • iR r = ∑ r ∈ T.erase r0, l' r • iR r := by
      have h1 : ∑ r ∈ T, l r • iR r = ∑ r ∈ T, l' r • iR r := by
        have : ∑ r ∈ T, l' r • iR r = ∑ r ∈ T, l r • iR r - θ • ∑ r ∈ T, G r • iR r := by
          rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun r _ => ?_)
          rw [smul_smul, ← sub_smul]
        rw [this, hGsum, smul_zero, sub_zero]
      rw [h1, ← Finset.add_sum_erase T _ hr0T, hl'r0, zero_smul, zero_add]
    have hmem : ∑ r ∈ T, l r • iR r ∈ cone (iR '' ((T.erase r0 : Finset _) : Set (Fin n → ℤ))) := by
      rw [hy', mem_cone_finset]; exact ⟨l', hl'0, rfl⟩
    obtain ⟨T', hT', hli', hy''⟩ := ih (T.erase r0) (Finset.erase_ssubset hr0T) _ hmem
    exact ⟨T', hT'.trans (Finset.erase_subset r0 T), hli', hy''⟩

end MIQPT1
/-! ### Part U5 -/

open MIQPInNP.SmallSol
open scoped BigOperators Pointwise

namespace MIQPT1

/-- Exponent bound for slice vertices. -/
def EVb {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : ℕ :=
  M5Core.alpha n (matSize (sliceG A) + vecSize (sliceH m))

/-- Exponent bound for the integral rays. -/
def ERb {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : ℕ := n * (2 * EVb A + 4) + EVb A

lemma ray_of_vert {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (v : Fin n → ℝ)
    (hv : IsVert (sliceG A) (sliceH m) v) :
    ∃ rz : Fin n → ℤ, (∃ c : ℝ, 0 < c ∧ iR rz = c • v) ∧ ∀ j, Sm (ERb A) (rz j : ℚ) := by
  obtain ⟨vq, rfl, hvq⟩ := vert_small _ _ v hv
  set D := ∏ j, (vq j).den with hD
  have hD1 : 1 ≤ D := Nat.one_le_iff_ne_zero.mpr
    (Finset.prod_ne_zero_iff.mpr (fun j _ => (vq j).den_nz))
  have hint : ∀ j, ∃ z : ℤ, (D : ℚ) * vq j = z := fun j =>
    int_of_den_dvd (vq j) D (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
  choose rz hrz using hint
  refine ⟨rz, ⟨D, by exact_mod_cast hD1, ?_⟩, fun j => ?_⟩
  · ext j
    simp only [iR, Pi.smul_apply, smul_eq_mul, toReal]
    have := hrz j
    have h' : ((rz j : ℚ) : ℝ) = ((D : ℚ) * vq j : ℚ) := by rw [this]
    push_cast at h'; rw [h']
  · rw [← hrz j]
    have hDle : D ≤ 2 ^ (n * (2 * EVb A + 4)) :=
      (prod_den_le vq).trans (two_pow_mono (vecSize_le_of_sm vq hvq))
    have := sm_mul (sm_nat D hDle) (hvq j)
    exact this

theorem rays_exist {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (hA : IsPointedPoly A) :
    ∃ R0 : Finset (Fin n → ℤ), (∀ r ∈ R0, IsExtremeRayOf (recCone A) (iR r)) ∧
      (∀ r ∈ R0, ∀ j, Sm (ERb A) (r j : ℚ)) ∧ ∀ y ∈ recCone A, y ∈ cone (iR '' (R0 : Set _)) := by
  classical
  have hfin := vert_finite (sliceG A) (sliceH m)
  have hray : ∀ v ∈ {v | IsVert (sliceG A) (sliceH m) v}, ∃ rz : Fin n → ℤ,
      (∃ c : ℝ, 0 < c ∧ iR rz = c • v) ∧ ∀ j, Sm (ERb A) (rz j : ℚ) :=
    fun v hv => ray_of_vert A v hv
  choose! RZ hRZ using hray
  refine ⟨hfin.toFinset.image RZ, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
    rw [Set.Finite.mem_toFinset] at hv
    obtain ⟨⟨c, hc, he⟩, -⟩ := hRZ v hv
    rw [he]; exact extreme_smul A v (vert_extreme A v hv) c hc
  · intro r hr
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
    rw [Set.Finite.mem_toFinset] at hv
    exact (hRZ v hv).2
  · intro y hy
    have h1 := cone_gen A hA y hy
    have hsub : cone {v | IsVert (sliceG A) (sliceH m) v} ⊆
        cone (iR '' ((hfin.toFinset.image RZ : Finset _) : Set (Fin n → ℤ))) := by
      unfold cone
      intro z hz
      have : Submodule.span NNReal {v | IsVert (sliceG A) (sliceH m) v} ≤
          Submodule.span NNReal (iR '' ((hfin.toFinset.image RZ : Finset _) : Set (Fin n → ℤ))) := by
        rw [Submodule.span_le]
        intro v hv
        obtain ⟨⟨c, hc, he⟩, -⟩ := hRZ v hv
        have hvmem : iR (RZ v) ∈ Submodule.span NNReal
            (iR '' ((hfin.toFinset.image RZ : Finset _) : Set (Fin n → ℤ))) :=
          Submodule.subset_span ⟨RZ v, by simp [Finset.mem_image]; exact ⟨v, hv, rfl⟩, rfl⟩
        have : v = (⟨1 / c, by positivity⟩ : NNReal) • iR (RZ v) := by
          rw [he]; ext u; simp [NNReal.smul_def]; field_simp
        rw [this]
        exact Submodule.smul_mem _ _ hvmem
      exact this hz
    exact hsub h1

end MIQPT1
/-! ### Part U6 -/

open MIQPInNP.SmallSol
open scoped BigOperators Pointwise

namespace MIQPT1

/-- Coordinate selector for the integer coordinates. -/
def selP (p q : ℕ) : Matrix (Fin p) (Fin (p + q)) ℚ :=
  fun k j => if j = Fin.castAdd q k then 1 else 0

/-- The polytope `{Ax ≤ b, |x_j| ≤ M, x_k = ȳ_k (k < p)}`. -/
def boxA {m p q : ℕ} (A : Matrix (Fin m) (Fin (p + q)) ℚ) :
    Matrix (Fin (m + ((p + q) + ((p + q) + (p + p))))) (Fin (p + q)) ℚ :=
  stack A (stack 1 (stack (-1) (stack (selP p q) (-selP p q))))

def boxB {m p q : ℕ} (b : Fin m → ℚ) (M : ℕ) (y : Fin p → ℤ) :
    Fin (m + ((p + q) + ((p + q) + (p + p)))) → ℚ :=
  stackv b (stackv (fun _ => (M : ℚ)) (stackv (fun _ => (M : ℚ))
    (stackv (fun k => (y k : ℚ)) (fun k => -(y k : ℚ)))))

lemma row_one {n : ℕ} (i : Fin n) (x : Fin n → ℝ) :
    ∑ j, (((1 : Matrix (Fin n) (Fin n) ℚ) i j : ℚ) : ℝ) * x j = x i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Matrix.one_apply, Ne.symm hj]
  · simp

lemma row_selP {p q : ℕ} (k : Fin p) (x : Fin (p + q) → ℝ) :
    ∑ j, ((selP p q k j : ℚ) : ℝ) * x j = x (Fin.castAdd q k) := by
  rw [Finset.sum_eq_single (Fin.castAdd q k)]
  · simp [selP]
  · intro j _ hj; simp [selP, hj]
  · simp

lemma mem_box {m p q : ℕ} (A : Matrix (Fin m) (Fin (p + q)) ℚ) (b : Fin m → ℚ) (M : ℕ)
    (y : Fin p → ℤ) (x : Fin (p + q) → ℝ) :
    x ∈ polyhedron (boxA A) (boxB b M y) ↔ x ∈ polyhedron A b ∧ (∀ j, |x j| ≤ M) ∧
      ∀ k, x (Fin.castAdd q k) = y k := by
  unfold boxA boxB
  rw [polyhedron_stack, polyhedron_stack, polyhedron_stack, polyhedron_stack]
  simp only [polyhedron, Set.mem_inter_iff, Set.mem_setOf_eq, Matrix.neg_apply, Rat.cast_neg,
    neg_mul, Finset.sum_neg_distrib, row_one, row_selP, Rat.cast_natCast, Rat.cast_intCast]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, fun j => abs_le.mpr ⟨by linarith [h3 j], h2 j⟩, fun k => ?_⟩
    linarith [h4 k, h5 k]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun j => (abs_le.mp (h2 j)).2, fun j => by linarith [(abs_le.mp (h2 j)).1],
      fun k => le_of_eq (h3 k), fun k => by rw [h3 k]⟩

lemma box_bounded {m p q : ℕ} (A : Matrix (Fin m) (Fin (p + q)) ℚ) (b : Fin m → ℚ) (M : ℕ)
    (y : Fin p → ℤ) : Bornology.IsBounded (polyhedron (boxA A) (boxB b M y)) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨M, fun x hx => ?_⟩
  obtain ⟨-, h2, -⟩ := (mem_box A b M y x).mp hx
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro j; rw [Real.norm_eq_abs]; exact h2 j

lemma intCone_int {n : ℕ} (S : Set (Fin n → ℤ)) (z : Fin n → ℝ) (hz : z ∈ intCone (iR '' S)) :
    ∀ j, ∃ w : ℤ, z j = w := by
  unfold intCone at hz
  induction hz using AddSubmonoid.closure_induction with
  | mem x hx => obtain ⟨r, -, rfl⟩ := hx; exact fun j => ⟨r j, rfl⟩
  | zero => exact fun j => ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    intro j
    obtain ⟨a, ha⟩ := hx j; obtain ⟨c, hc⟩ := hy j
    exact ⟨a + c, by simp [ha, hc]⟩

lemma n_le_m_of_pointed {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (hA : IsPointedPoly A) : n ≤ m := by
  let L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ) := Matrix.mulVecLin (A.map (fun q : ℚ => (q : ℝ)))
  have hinj : Function.Injective L := by
    intro x y hxy
    have h0 : ∀ i, ∑ j, (A i j : ℝ) * (x - y) j = 0 := by
      intro i
      have := congrFun hxy i
      simp only [L, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.map_apply] at this
      simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      linarith
    exact sub_eq_zero.mp (hA _ h0)
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using this

end MIQPT1
/-! ### Part U7 -/

open MIQPInNP.SmallSol
open scoped BigOperators Pointwise

namespace MIQPT1

lemma sm0_oneU : Sm 0 (1 : ℚ) := by constructor <;> simp

def q1b (S : ℕ) : ℕ := S + 2 * (S * (2 * (S * (S + 1)) + 4)) + 3 * S + 8
def evb (S : ℕ) : ℕ := S * S + S * (2 * q1b S)
def erb (S : ℕ) : ℕ := S * (2 * evb S + 4) + evb S
def emb (S : ℕ) : ℕ := (S * S + S * (2 * S)) + erb S + S + 1
def totb (S : ℕ) : ℕ := (S + 16 * (S * S)) + (S + 4 * S * (2 * emb S + 4)) + S * (2 * erb S + 4)

open Polynomial in
noncomputable def totP : Polynomial ℕ :=
  let q1 : Polynomial ℕ := X + 2 * (X * (2 * (X * (X + 1)) + 4)) + 3 * X + 8
  let ev : Polynomial ℕ := X * X + X * (2 * q1)
  let er : Polynomial ℕ := X * (2 * ev + 4) + ev
  let em : Polynomial ℕ := (X * X + X * (2 * X)) + er + X + 1
  (X + 16 * (X * X)) + (X + 4 * X * (2 * em + 4)) + X * (2 * er + 4)

lemma totP_eval (S : ℕ) : totP.eval S = totb S := by
  simp [totP, totb, emb, erb, evb, q1b]

lemma mixed_iff {p q : ℕ} (x : Fin (p + q) → ℝ) :
    IsMixedInt p x ↔ ∀ k : Fin p, ∃ z : ℤ, x (Fin.castAdd q k) = z := by
  constructor
  · intro h k; exact h _ (by simp)
  · intro h i hi
    have : i = Fin.castAdd q ⟨i, hi⟩ := Fin.ext rfl
    rw [this]; exact h _

lemma ERb_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) (S : ℕ) (hS : matSize A ≤ S) (hn : n ≤ S)
    (hm : m ≤ S) : ERb A ≤ erb S := by
  have hf : ∀ j, Sm (m * (S + 1)) (normF A j) := by
    intro j
    have := sm_sum_univ (fun i => A i j) (fun i => (sm_of_matSize A i j).mono hS)
    exact sm_neg this
  have h1 : matSize (rowv (normF A)) ≤ 1 * n * (2 * (m * (S + 1)) + 4) :=
    matSize_le_of_sm _ (fun _ j => hf j)
  have h2 : matSize (rowv (-normF A)) ≤ 1 * n * (2 * (m * (S + 1)) + 4) :=
    matSize_le_of_sm _ (fun _ j => sm_neg (hf j))
  have h3 : vecSize (sliceH m) = 3 * m + 8 := by
    unfold sliceH; rw [vecSize_stackv, vecSize_stackv, vecSize_zero]
    have a1 : vecSize (fun _ : Fin 1 => (1 : ℚ)) = 4 := by decide
    have a2 : vecSize (fun _ : Fin 1 => (-1 : ℚ)) = 4 := by decide
    rw [a1, a2]
  have h4 : matSize (sliceG A) + vecSize (sliceH m) ≤ q1b S := by
    unfold sliceG; rw [matSize_stack, matSize_stack, h3]
    have : 1 * n * (2 * (m * (S + 1)) + 4) ≤ S * (2 * (S * (S + 1)) + 4) := by
      rw [one_mul]; gcongr
    unfold q1b; omega
  have h5 : EVb A ≤ evb S := by
    unfold EVb M5Core.alpha evb; gcongr
  unfold ERb erb; gcongr

/-- Proposition 4 (Del Pia–Dey–Molinaro), with polytopes cut out by boxes and integer fibres. -/
theorem prop4 : ∃ g : Polynomial ℕ, ∀ (p q m : ℕ) (A : Matrix (Fin m) (Fin (p + q)) ℚ)
    (b : Fin m → ℚ),
    ((polyhedron A b).Nonempty → IsPointedPoly A) →
    ∃ (N : ℕ) (mi : Fin N → ℕ) (Ai : (i : Fin N) → Matrix (Fin (mi i)) (Fin (p + q)) ℚ)
      (bi : (i : Fin N) → Fin (mi i) → ℚ) (KK : Finset (Finset (Fin (p + q) → ℤ))),
      {x | x ∈ polyhedron A b ∧ IsMixedInt p x} =
        (⋃ i, ⋃ R ∈ KK,
          polyhedron (Ai i) (bi i) + intCone ((fun r j => (r j : ℝ)) '' (R : Set (Fin (p + q) → ℤ)))) ∧
      (∀ i, Bornology.IsBounded (polyhedron (Ai i) (bi i)) ∧
        matSize (Ai i) + vecSize (bi i) ≤ g.eval (matSize A + vecSize b)) ∧
      (∀ R ∈ KK, ∀ r ∈ R, IsExtremeRayOf (recCone A) (fun j => (r j : ℝ)) ∧
        vecSize (fun j => (r j : ℚ)) ≤ g.eval (matSize A + vecSize b)) ∧
      (∀ R ∈ KK, LinearIndependent ℝ (fun r : R => fun j => ((r : Fin (p + q) → ℤ) j : ℝ))) := by
  classical
  refine ⟨totP, ?_⟩
  intro p q m A b hpt
  by_cases hne : (polyhedron A b).Nonempty
  swap
  · refine ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, ∅, ?_, fun i => i.elim0,
      fun R hR => absurd hR (Finset.notMem_empty R), fun R hR => absurd hR (Finset.notMem_empty R)⟩
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.notMem_empty, Set.iUnion_of_empty,
      Set.iUnion_empty, Set.mem_empty_iff_false, iff_false, not_and]
    · intro hx; exact absurd ⟨x, hx⟩ hne
  have hA := hpt hne
  have hrvpt : ∀ d : Fin (p + q) → ℝ, (∀ i, rv A i d = 0) → d = 0 := fun d hd => hA d hd
  obtain ⟨R0, hR0e, hR0s, hR0c⟩ := rays_exist A hA
  set EP := M5Core.alpha (p + q) (matSize A + vecSize b) with hEP
  set ER := ERb A with hER
  set EM := EP + ER + (p + q) + 1 with hEM
  set M : ℕ := 2 ^ EM with hM
  set Y := Fintype.piFinset (fun _ : Fin p => Finset.Icc (-(M : ℤ)) M) with hY
  set e := Y.equivFin with he
  set KK := R0.powerset.filter (fun T : Finset (Fin (p + q) → ℤ) =>
    LinearIndependent ℝ (fun r : ↥T => iR (r : Fin (p + q) → ℤ)))
    with hKK
  have hrayrec : ∀ r ∈ R0, iR r ∈ recCone A := fun r hr => (hR0e r hr).1
  have hconeR : ∀ T ⊆ R0, cone (iR '' (T : Set (Fin (p + q) → ℤ))) ⊆ recCone A := by
    intro T hT
    apply cone_subset_recCone
    rintro _ ⟨r, hr, rfl⟩; exact hrayrec r (hT hr)
  -- sizes
  set S := matSize A + vecSize b with hS
  have hnm := n_le_m_of_pointed A hA
  have hmb := n_le_vecSize b
  have hmS : m ≤ S := by omega
  have hnS : (p + q) ≤ S := by
    have := mn_le_matSize A
    have : (p + q) ≤ m * (p + q) := by
      rcases Nat.eq_zero_or_pos (p + q) with h0 | hpos
      · omega
      · exact Nat.le_mul_of_pos_left (p + q) (by omega)
    omega
  have hERb : ER ≤ erb S := ERb_le A S (by omega) hnS hmS
  have hEMb : EM ≤ emb S := by
    have : EP ≤ S * S + S * (2 * S) := by
      rw [hEP]; unfold M5Core.alpha; gcongr
    unfold emb; omega
  refine ⟨Y.card, fun _ => m + ((p + q) + ((p + q) + (p + p))), fun _ => boxA A,
    fun i => boxB b M (e.symm i).1, KK, ?_, ?_, ?_, ?_⟩
  · ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨hxP, hxM⟩
      obtain ⟨v, r, hv, hr, hxe, hvb⟩ := decomp A b hrvpt x hxP
      have hr' : r ∈ recCone A := fun i => by have := hr i; simpa [rv] using this
      obtain ⟨T, hT, hTli, hrT⟩ := caratheodory_cone R0 r (hR0c r hr')
      obtain ⟨l, hl, hrl⟩ := (mem_cone_finset T r).mp hrT
      set zint := ∑ t ∈ T, ⌊l t⌋₊ • iR t with hzint
      set x' := v + ∑ t ∈ T, (l t - ⌊l t⌋₊) • iR t with hx'
      have hxx : x = x' + zint := by
        rw [hxe, hrl, hx', hzint, add_assoc, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [← Nat.cast_smul_eq_nsmul ℝ, ← add_smul]; congr 1; ring
      have hfrac : ∀ t, 0 ≤ l t - ⌊l t⌋₊ := fun t => by linarith [Nat.floor_le (hl t)]
      have hfrac1 : ∀ t, l t - ⌊l t⌋₊ ≤ 1 := fun t => by linarith [Nat.lt_floor_add_one (l t)]
      have hx'P : x' ∈ polyhedron A b := by
        apply polyhedron_add_recCone A b v _ hv
        apply hconeR T hT
        rw [mem_cone_finset]
        exact ⟨fun t => l t - ⌊l t⌋₊, hfrac, rfl⟩
      have hzint_int : ∀ j, ∃ w : ℤ, zint j = w := by
        intro j
        refine ⟨∑ t ∈ T, (⌊l t⌋₊ : ℤ) * t j, ?_⟩
        simp [hzint, Finset.sum_apply, iR, nsmul_eq_mul]
      have hx'int : ∀ k : Fin p, ∃ w : ℤ, x' (Fin.castAdd q k) = w := by
        intro k
        obtain ⟨w1, hw1⟩ := (mixed_iff x).mp hxM k
        obtain ⟨w2, hw2⟩ := hzint_int (Fin.castAdd q k)
        refine ⟨w1 - w2, ?_⟩
        have : x' = x - zint := by rw [hxx]; abel
        rw [this, Pi.sub_apply, hw1, hw2]; push_cast; ring
      have hTcard : T.card ≤ (p + q) := by
        have := hTli.fintype_card_le_finrank
        simpa using this
      have hbound : ∀ j, |x' j| ≤ M := by
        intro j
        have h1 : |(∑ t ∈ T, (l t - ⌊l t⌋₊) • iR t) j| ≤ T.card * 2 ^ ER := by
          rw [Finset.sum_apply]
          calc |∑ t ∈ T, ((l t - ⌊l t⌋₊) • iR t) j| ≤ ∑ t ∈ T, |((l t - ⌊l t⌋₊) • iR t) j| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ _t ∈ T, (2 : ℝ) ^ ER := by
                refine Finset.sum_le_sum (fun t ht => ?_)
                simp only [Pi.smul_apply, smul_eq_mul, abs_mul, iR]
                have hs := hR0s t (hT ht) j
                have := sm_abs_le_real hs
                rw [abs_of_nonneg (hfrac t)]
                have h' : |((t j : ℚ) : ℝ)| = |((t j : ℤ) : ℝ)| := by push_cast; rfl
                rw [h'] at this
                calc (l t - ⌊l t⌋₊) * |((t j : ℤ) : ℝ)| ≤ 1 * 2 ^ ER :=
                      mul_le_mul (hfrac1 t) this (abs_nonneg _) (by norm_num)
                  _ = 2 ^ ER := one_mul _
            _ = T.card * 2 ^ ER := by simp
        have h2 : |x' j| ≤ 2 ^ EP + T.card * 2 ^ ER := by
          rw [hx', Pi.add_apply]
          exact (abs_add_le _ _).trans (add_le_add (hvb j) h1)
        have h3 : (2 : ℝ) ^ EP + T.card * 2 ^ ER ≤ M := by
          rw [hM, hEM]; push_cast
          have hc : (T.card : ℝ) ≤ 2 ^ (p + q) := by
            have : T.card < 2 ^ T.card := Nat.lt_two_pow_self
            have h2' : 2 ^ T.card ≤ 2 ^ (p + q) := two_pow_mono hTcard
            exact_mod_cast (by omega : T.card ≤ 2 ^ (p + q))
          have e1 : (2 : ℝ) ^ EP ≤ 2 ^ (EP + ER + (p + q)) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          have e2 : (T.card : ℝ) * 2 ^ ER ≤ 2 ^ (EP + ER + (p + q)) := by
            calc (T.card : ℝ) * 2 ^ ER ≤ 2 ^ (p + q) * 2 ^ ER := by gcongr
              _ = 2 ^ ((p + q) + ER) := (pow_add _ _ _).symm
              _ ≤ 2 ^ (EP + ER + (p + q)) := pow_le_pow_right₀ (by norm_num) (by omega)
          rw [pow_succ]; linarith
        linarith
      choose ybar hybar using hx'int
      have hyY : ybar ∈ Y := by
        rw [hY, Fintype.mem_piFinset]
        intro k
        rw [Finset.mem_Icc]
        have := hbound (Fin.castAdd q k)
        rw [hybar k] at this
        have h' : |(ybar k : ℝ)| ≤ (M : ℝ) := this
        rw [abs_le] at h'
        constructor
        · have : (-(M : ℝ)) ≤ ybar k := h'.1
          exact_mod_cast this
        · have : (ybar k : ℝ) ≤ M := h'.2
          exact_mod_cast this
      refine ⟨e ⟨ybar, hyY⟩, T, ?_, Set.mem_add.mpr ⟨x', ?_, zint, ?_, hxx.symm⟩⟩
      · rw [hKK, Finset.mem_filter, Finset.mem_powerset]; exact ⟨hT, hTli⟩
      · rw [mem_box, Equiv.symm_apply_apply]
        exact ⟨hx'P, hbound, fun k => hybar k⟩
      · show zint ∈ intCone (iR '' (T : Set (Fin (p + q) → ℤ)))
        rw [hzint]
        exact AddSubmonoid.sum_mem _ (fun t ht =>
          AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure (Set.mem_image_of_mem iR ht)) _)
    · rintro ⟨i, R, hRK, hx⟩
      obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_add.mp hx
      obtain ⟨hyP, -, hyfix⟩ := (mem_box A b M _ y).mp hy
      have hRsub : R ⊆ R0 := by
        rw [hKK, Finset.mem_filter, Finset.mem_powerset] at hRK; exact hRK.1
      have hz' : z ∈ intCone (iR '' (R : Set (Fin (p + q) → ℤ))) := hz
      have hzrec : z ∈ recCone A := hconeR R hRsub (intCone_subset_cone _ hz')
      refine ⟨polyhedron_add_recCone A b y z hyP hzrec, (mixed_iff _).mpr (fun k => ?_)⟩
      obtain ⟨w, hw⟩ := intCone_int _ z hz' (Fin.castAdd q k)
      refine ⟨(e.symm i : Fin p → ℤ) k + w, ?_⟩
      rw [Pi.add_apply, hyfix k, hw]; push_cast; ring
  · intro i
    refine ⟨box_bounded A b M _, ?_⟩
    rw [totP_eval]
    -- size of the box system
    have z1 : matSize (boxA A) ≤ matSize A + 16 * ((p + q) * (p + q)) := by
      unfold boxA
      rw [matSize_stack, matSize_stack, matSize_stack, matSize_stack, matSize_neg, matSize_neg]
      have a1 : matSize (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℚ) ≤ (p + q) * (p + q) * 4 := by
        simpa using matSize_le_of_sm (E := 0) (1 : Matrix (Fin (p + q)) (Fin (p + q)) ℚ) (fun i j => by
          by_cases h : i = j
          · subst h; simp only [Matrix.one_apply_eq]; exact sm0_oneU
          · simp only [Matrix.one_apply_ne h]; exact sm_zero 0)
      have a2 : matSize (selP p q) ≤ p * (p + q) * 4 := by
        simpa using matSize_le_of_sm (E := 0) (selP p q) (fun k j => by
          by_cases h : j = Fin.castAdd q k
          · simp only [selP, h, if_true]; exact sm0_oneU
          · simp only [selP, h, if_false]; exact sm_zero 0)
      have a3 : p * (p + q) ≤ (p + q) * (p + q) := Nat.mul_le_mul_right _ (by omega)
      omega
    have z2 : vecSize (boxB (q := q) b M (e.symm i).1) ≤ vecSize b + 4 * (p + q) * (2 * EM + 4) := by
      unfold boxB
      rw [vecSize_stackv, vecSize_stackv, vecSize_stackv, vecSize_stackv]
      have hMS : Sm EM (M : ℚ) := sm_nat M le_rfl
      have c1 : vecSize (fun _ : Fin (p + q) => (M : ℚ)) ≤ (p + q) * (2 * EM + 4) :=
        vecSize_le_of_sm _ (fun _ => hMS)
      have hyS : ∀ k, Sm EM ((e.symm i : Fin p → ℤ) k : ℚ) := by
        intro k
        have hmem : (e.symm i).1 ∈ Fintype.piFinset (fun _ : Fin p => Finset.Icc (-(M : ℤ)) M) :=
          (e.symm i).2
        have := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hmem k)
        apply sm_int
        have : ((e.symm i : Fin p → ℤ) k).natAbs ≤ M := by omega
        exact this
      have c2 : vecSize (fun k => ((e.symm i : Fin p → ℤ) k : ℚ)) ≤ p * (2 * EM + 4) :=
        vecSize_le_of_sm _ hyS
      have c3 : vecSize (fun k => -((e.symm i : Fin p → ℤ) k : ℚ)) ≤ p * (2 * EM + 4) :=
        vecSize_le_of_sm _ (fun k => sm_neg (hyS k))
      have c4 : p * (2 * EM + 4) ≤ (p + q) * (2 * EM + 4) := Nat.mul_le_mul_right _ (by omega)
      have : 4 * (p + q) * (2 * EM + 4) = (p + q) * (2 * EM + 4) + (p + q) * (2 * EM + 4) + (p + q) * (2 * EM + 4) +
          (p + q) * (2 * EM + 4) := by ring
      omega
    have z3 : 4 * (p + q) * (2 * EM + 4) ≤ 4 * S * (2 * emb S + 4) := by gcongr
    have z4 : (p + q) * (p + q) ≤ S * S := Nat.mul_le_mul hnS hnS
    unfold totb
    beta_reduce
    omega
  · intro R hRK r hr
    have hRsub : R ⊆ R0 := by
      rw [hKK, Finset.mem_filter, Finset.mem_powerset] at hRK; exact hRK.1
    refine ⟨hR0e r (hRsub hr), ?_⟩
    rw [totP_eval]
    have h1 : vecSize (fun j => (r j : ℚ)) ≤ (p + q) * (2 * ER + 4) :=
      vecSize_le_of_sm _ (hR0s r (hRsub hr))
    have h2 : (p + q) * (2 * ER + 4) ≤ S * (2 * erb S + 4) := by gcongr
    unfold totb
    omega
  · intro R hRK
    rw [hKK, Finset.mem_filter] at hRK
    exact hRK.2

end MIQPT1
/-! ### Part U8 -/

open MIQPInNP.SmallSol
open scoped Pointwise

theorem solution :
    ∃ g : Polynomial ℕ, ∀ (p q m : ℕ) (A : Matrix (Fin m) (Fin (p + q)) ℚ) (b : Fin m → ℚ),
      ((polyhedron A b).Nonempty → IsPointedPoly A) →
      ∃ (N : ℕ) (mi : Fin N → ℕ) (Ai : (i : Fin N) → Matrix (Fin (mi i)) (Fin (p + q)) ℚ)
        (bi : (i : Fin N) → Fin (mi i) → ℚ) (KK : Finset (Finset (Fin (p + q) → ℤ))),
        {x | x ∈ polyhedron A b ∧ IsMixedInt p x} =
          (⋃ i, ⋃ R ∈ KK,
            polyhedron (Ai i) (bi i) + intCone ((fun r j => (r j : ℝ)) '' (R : Set (Fin (p + q) → ℤ)))) ∧
        (∀ i, Bornology.IsBounded (polyhedron (Ai i) (bi i)) ∧
          matSize (Ai i) + vecSize (bi i) ≤ g.eval (matSize A + vecSize b)) ∧
        (∀ R ∈ KK, ∀ r ∈ R, IsExtremeRayOf (recCone A) (fun j => (r j : ℝ)) ∧
          vecSize (fun j => (r j : ℚ)) ≤ g.eval (matSize A + vecSize b)) ∧
        (∀ R ∈ KK, LinearIndependent ℝ (fun r : R => fun j => ((r : Fin (p + q) → ℤ) j : ℝ))) :=
  MIQPT1.prop4
