-- Prove2me | solution 2 for MIQPInNP.SmallSol.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T08:47:01.103107+00:00
-- url     : https://prove2.me/submissions/14780424-cf69-4dbf-b078-ce3abe7f6750

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
/-! ### Part Q1 -/

open MIQPInNP.SmallSol
open scoped BigOperators Pointwise

namespace MIQPT1

open Matrix

/-- The Gram-type matrix `M_{kl} = r_kᵀ H r_l` of the quadratic form in coefficient space. -/
def coefM {n d : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (r : Fin d → Fin n → ℚ) :
    Matrix (Fin d) (Fin d) ℚ :=
  fun k l => ∑ u, ∑ v, r k u * H u v * r l v

lemma quadForm_eq_dot {n : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℝ) :
    quadForm H x = x ⬝ᵥ (H.map (fun q : ℚ => (q : ℝ)) *ᵥ x) := by
  unfold quadForm
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

lemma quadForm_comb {n d : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (r : Fin d → Fin n → ℚ)
    (l : Fin d → ℝ) :
    quadForm H (∑ k, l k • toReal (r k)) = quadForm (coefM H r) l := by
  set R : Matrix (Fin n) (Fin d) ℝ := Matrix.of fun u k => (r k u : ℝ) with hR
  have hx : ∑ k, l k • toReal (r k) = R *ᵥ l := by
    ext u; simp [hR, Matrix.mulVec, dotProduct, toReal, Finset.sum_apply, mul_comm]
  have hM : (coefM H r).map (fun q : ℚ => (q : ℝ)) =
      R.transpose * H.map (fun q : ℚ => (q : ℝ)) * R := by
    ext k l'
    rw [hR]
    simp only [Matrix.map_apply, coefM, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul,
      Matrix.of_apply]
    push_cast
    rw [Finset.sum_comm]
  rw [quadForm_eq_dot, quadForm_eq_dot, hx, hM, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec l R.transpose, Matrix.vecMul_transpose]

lemma dot_comb {n d : ℕ} (f : Fin n → ℚ) (r : Fin d → Fin n → ℚ) (l : Fin d → ℝ) :
    ∑ u, (f u : ℝ) * (∑ k, l k • toReal (r k)) u =
      ∑ k, ((∑ u, f u * r k u : ℚ) : ℝ) * l k := by
  unfold toReal
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun u _ => by ring))

/-- Row matrix of a vector. -/
def rowM {d : ℕ} (φ : Fin d → ℚ) : Matrix (Fin 1) (Fin d) ℚ := fun _ k => φ k

/-- Selector diagonal: `λ_k ≤ 0` for `k ∉ T`. -/
def offT {d : ℕ} (T : Finset (Fin d)) : Matrix (Fin d) (Fin d) ℚ :=
  Matrix.diagonal (fun k => if k ∈ T then 0 else 1)

/-- The coefficient polytope `{λ ≥ 0, supp λ ⊆ T, φᵀλ = 1}`. -/
def coefA {d : ℕ} (T : Finset (Fin d)) (φ : Fin d → ℚ) : Matrix (Fin (d + d + (1 + 1))) (Fin d) ℚ :=
  stack (stack (-1) (offT T)) (stack (rowM φ) (rowM (-φ)))

def coefB (d : ℕ) : Fin (d + d + (1 + 1)) → ℚ :=
  stackv (stackv 0 0) (stackv (fun _ => 1) (fun _ => -1))

lemma mem_coefPoly {d : ℕ} (T : Finset (Fin d)) (φ : Fin d → ℚ) (l : Fin d → ℝ) :
    l ∈ polyhedron (coefA T φ) (coefB d) ↔
      (∀ k, 0 ≤ l k) ∧ (∀ k, k ∉ T → l k ≤ 0) ∧ ∑ k, (φ k : ℝ) * l k = 1 := by
  unfold coefA coefB
  rw [polyhedron_stack, polyhedron_stack, polyhedron_stack]
  simp only [polyhedron, Set.mem_inter_iff, Set.mem_setOf_eq]
  have h1 : ∀ k, ∑ j, (((-1 : Matrix (Fin d) (Fin d) ℚ) k j : ℚ) : ℝ) * l j = - l k := by
    intro k
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj; simp [Matrix.one_apply, Ne.symm hj]
    · simp
  have h2 : ∀ k, ∑ j, ((offT T k j : ℚ) : ℝ) * l j = if k ∈ T then 0 else l k := by
    intro k
    rw [Finset.sum_eq_single k]
    · by_cases hk : k ∈ T <;> simp [offT, hk]
    · intro j _ hj; simp [offT, Ne.symm hj]
    · simp
  simp only [h1, h2, rowM, Pi.zero_apply, Rat.cast_zero, Pi.neg_apply, Rat.cast_neg, neg_mul,
    Finset.sum_neg_distrib, Rat.cast_one]
  constructor
  · rintro ⟨⟨ha, hb⟩, hc, hd⟩
    refine ⟨fun k => by have := ha k; linarith, fun k hk => by
      have := hb k; simpa [hk] using this, ?_⟩
    have := hc 0; have := hd 0; linarith
  · rintro ⟨ha, hb, hc⟩
    refine ⟨⟨fun k => by have := ha k; linarith, fun k => ?_⟩, fun _ => le_of_eq hc,
      fun _ => by linarith⟩
    by_cases hk : k ∈ T
    · simp [hk]
    · simpa [hk] using hb k hk

lemma coefPoly_bounded {d : ℕ} (T : Finset (Fin d)) (φ : Fin d → ℚ) (hφ : ∀ k, (0 : ℝ) < φ k) :
    Bornology.IsBounded (polyhedron (coefA T φ) (coefB d)) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨∑ k, 1 / (φ k : ℝ), fun l hl => ?_⟩
  obtain ⟨h0, -, h1⟩ := (mem_coefPoly T φ l).mp hl
  rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun k _ => (one_div_pos.mpr (hφ k)).le))]
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (h0 k)]
  have hk : (φ k : ℝ) * l k ≤ 1 := by
    rw [← h1]
    exact Finset.single_le_sum (f := fun k => (φ k : ℝ) * l k)
      (fun i _ => mul_nonneg (hφ i).le (h0 i)) (Finset.mem_univ k)
  have : l k ≤ 1 / (φ k : ℝ) := by
    rw [le_div_iff₀ (hφ k)]; linarith
  exact this.trans (Finset.single_le_sum (f := fun k => 1 / (φ k : ℝ))
    (fun i _ => (one_div_pos.mpr (hφ i)).le) (Finset.mem_univ k))

end MIQPT1
/-! ### Part Q2 -/

open MIQPInNP.SmallSol
open scoped BigOperators Pointwise

namespace MIQPT1

lemma sm0_oneQ : Sm 0 (1 : ℚ) := by constructor <;> simp

lemma sm0_matSize_le {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) (h : ∀ i j, Sm 0 (M i j)) :
    matSize M ≤ m * n * 4 := by
  simpa using matSize_le_of_sm (E := 0) M h

lemma matSize_coefA {d W : ℕ} (hW : 1 ≤ W) (T : Finset (Fin d)) (φ : Fin d → ℚ)
    (hφ : ∀ k, Sm (3 * W ^ 2) (φ k)) :
    matSize (coefA T φ) ≤ d * d * 8 + 2 * (d * (6 * W ^ 2 + 4)) := by
  unfold coefA
  rw [matSize_stack, matSize_stack, matSize_stack, matSize_neg]
  have h1 : matSize (1 : Matrix (Fin d) (Fin d) ℚ) ≤ d * d * 4 := sm0_matSize_le _ (fun i j => by
    by_cases h : i = j
    · subst h; simpa using sm0_oneQ
    · simpa [Matrix.one_apply, h] using sm_zero 0)
  have h2 : matSize (offT T) ≤ d * d * 4 := sm0_matSize_le _ (fun i j => by
    by_cases h : i = j
    · subst h; by_cases hi : i ∈ T
      · simpa [offT, hi] using sm_zero 0
      · simpa [offT, hi] using sm0_oneQ
    · simpa [offT, Matrix.diagonal_apply_ne _ h] using sm_zero 0)
  have h3 : matSize (rowM φ) ≤ 1 * d * (2 * (3 * W ^ 2) + 4) :=
    matSize_le_of_sm _ (fun _ k => hφ k)
  have h4 : matSize (rowM (-φ)) ≤ 1 * d * (2 * (3 * W ^ 2) + 4) :=
    matSize_le_of_sm _ (fun _ k => sm_neg (hφ k))
  have e : 1 * d * (2 * (3 * W ^ 2) + 4) = d * (6 * W ^ 2 + 4) := by ring
  rw [e] at h3 h4
  omega

lemma vecSize_coefB (d : ℕ) : vecSize (coefB d) = 6 * d + 8 := by
  unfold coefB
  rw [vecSize_stackv, vecSize_stackv, vecSize_stackv, vecSize_zero]
  have h1 : vecSize (fun _ : Fin 1 => (1 : ℚ)) = 4 := by decide
  have h2 : vecSize (fun _ : Fin 1 => (-1 : ℚ)) = 4 := by decide
  rw [h1, h2]; ring

/-- The minimiser `x̄` of Lemma 7 over a face `cone(r_T) ∩ 𝓗`, via Theorem 3 in coefficient
space. -/
theorem xbar_exists : ∃ G : Polynomial ℕ, ∀ (n d : ℕ) (H : Matrix (Fin n) (Fin n) ℚ)
    (r : Fin d → Fin n → ℚ) (f : Fin n → ℚ), (∀ j, 0 < ∑ u, (f u : ℝ) * toReal (r j) u) →
    ∀ T : Finset (Fin d), T.Nonempty →
    ∃ α : Fin d → ℚ, (∀ k, 0 ≤ α k) ∧ (∀ k, k ∉ T → α k = 0) ∧
      ∑ k, (∑ u, f u * r k u) * α k = 1 ∧
      (∀ y ∈ cone ((fun j => toReal (r j)) '' (T : Set (Fin d))) ∩ hyperplane f,
        quadForm H (∑ k, (α k : ℝ) • toReal (r k)) ≤ quadForm H y) ∧
      vecSize (∑ k, α k • r k) ≤ G.eval (matSize H + ∑ k, vecSize (r k) + vecSize f) := by
  obtain ⟨G0, hG0⟩ := small_min
  refine ⟨((Polynomial.X + 1) + G0.comp (60 * (Polynomial.X + 1) ^ 5)) *
    (6 * ((Polynomial.X + 1) + G0.comp (60 * (Polynomial.X + 1) ^ 5)) ^ 2 + 4), ?_⟩
  intro n d H r f hf T hT
  set φ : Fin d → ℚ := fun k => ∑ u, f u * r k u with hφdef
  have hφ : ∀ k, (0 : ℝ) < φ k := by
    intro k; have := hf k; simp only [hφdef, toReal] at this ⊢; push_cast; exact this
  have hb := coefPoly_bounded T φ hφ
  obtain ⟨k0, hk0⟩ := hT
  set l0 : Fin d → ℝ := Pi.single k0 (1 / (φ k0 : ℝ)) with hl0
  have hl0P : l0 ∈ polyhedron (coefA T φ) (coefB d) := by
    rw [mem_coefPoly]
    refine ⟨fun k => ?_, fun k hk => ?_, ?_⟩
    · by_cases h : k = k0
      · subst h; simp [hl0]; exact_mod_cast (hφ k).le
      · simp [hl0, h]
    · have : k ≠ k0 := fun h => hk (h ▸ hk0)
      simp [hl0, this]
    · rw [Finset.sum_eq_single k0]
      · simp [hl0]; field_simp [(hφ k0).ne']
      · intro j _ hj; simp [hl0, hj]
      · simp
  obtain ⟨lm, hlm, hmin⟩ := (isCompact_polyhedron _ _ hb).exists_isMinOn ⟨l0, hl0P⟩
    (continuous_quadVal (coefM H r) 0 0).continuousOn
  obtain ⟨α, hαP, hαle, hαsz⟩ := hG0 d (d + d + (1 + 1)) (coefM H r) 0 (coefA T φ) (coefB d) hb
    lm hlm
  obtain ⟨hα0, hαT, hα1⟩ := (mem_coefPoly T φ (toReal α)).mp hαP
  refine ⟨α, fun k => ?_, fun k hk => ?_, ?_, ?_, ?_⟩
  · have := hα0 k; simp only [toReal] at this; exact_mod_cast this
  · have h1 := hα0 k; have h2 := hαT k hk; simp only [toReal] at h1 h2
    have : (α k : ℝ) = 0 := le_antisymm h2 h1
    exact_mod_cast this
  · have : ((∑ k, φ k * α k : ℚ) : ℝ) = 1 := by push_cast; simpa [toReal] using hα1
    exact_mod_cast this
  · rintro y ⟨hyc, hyh⟩
    obtain ⟨l, hl0', hlT, rfl⟩ := (mem_cone_image _ _ _).mp hyc
    have hlP : l ∈ polyhedron (coefA T φ) (coefB d) := by
      rw [mem_coefPoly]
      refine ⟨hl0', fun k hk => le_of_eq (hlT k hk), ?_⟩
      have : ∑ u, (f u : ℝ) * (∑ k, l k • toReal (r k)) u = 1 := hyh
      rw [dot_comb] at this
      simpa [hφdef] using this
    rw [quadForm_comb, quadForm_comb]
    have h1 := hmin hlP
    simp only [Set.mem_setOf_eq] at h1
    rw [quadVal_zero_zero, quadVal_zero_zero] at hαle h1
    exact hαle.trans h1
  · -- sizes
    obtain ⟨S, hS⟩ : ∃ S, S = matSize H + ∑ k, vecSize (r k) + vecSize f := ⟨_, rfl⟩
    rw [← hS]
    obtain ⟨W, hW⟩ : ∃ W, W = S + 1 := ⟨_, rfl⟩
    have hW1 : 1 ≤ W := by omega
    have hnf := n_le_vecSize f
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; have := hf k0; simp at this
      · exact h
    have hdS : d ≤ S := by
      have : ∑ _k : Fin d, 1 ≤ ∑ k, vecSize (r k) :=
        Finset.sum_le_sum (fun k _ => hn1.trans (n_le_vecSize (r k)))
      simp at this; omega
    have hdW : d ≤ W := by omega
    have hnW : n ≤ W := by omega
    have hrS : ∀ k u, Sm (1 * W ^ 1) (r k u) := fun k u => sm_W_of_vecSize (r k) (by
      have := Finset.single_le_sum (f := fun k => vecSize (r k)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ k)
      omega) u
    have hHS := sm_W_of_matSize H (show matSize H ≤ W by omega)
    have hfS := sm_W_of_vecSize f (show vecSize f ≤ W by omega)
    have hφS : ∀ k, Sm (3 * W ^ 2) (φ k) := fun k =>
      (smW_sum hW1 hnW _ (fun u => smW_mul (hfS u) (hrS k u))).mono (le_of_eq (by ring))
    have hMS : ∀ k l, Sm (5 * W ^ 3) (coefM H r k l) := by
      intro k l
      have := smW_sum hW1 hnW _ (fun u => smW_sum hW1 hnW _ (fun v =>
        smW_mul (smW_mul (hrS k u) (hHS u v)) (hrS l v)))
      exact this.mono (le_of_eq (by ring))
    have hMsz : matSize (coefM H r) ≤ d * d * (2 * (5 * W ^ 3) + 4) := matSize_le_of_sm _ hMS
    have hAsz := matSize_coefA hW1 T φ hφS
    have hBsz := vecSize_coefB d
    have harg : matSize (coefM H r) + vecSize (0 : Fin d → ℚ) + matSize (coefA T φ) +
        vecSize (coefB d) ≤ 60 * W ^ 5 := by
      rw [vecSize_zero, hBsz]
      have e1 : d * d * (2 * (5 * W ^ 3) + 4) ≤ W * W * (10 * W ^ 3 + 4) := by
        have := Nat.mul_le_mul hdW hdW
        calc d * d * (2 * (5 * W ^ 3) + 4) ≤ W * W * (2 * (5 * W ^ 3) + 4) :=
              Nat.mul_le_mul_right _ this
          _ = W * W * (10 * W ^ 3 + 4) := by ring
      have e2 : d * d * 8 + 2 * (d * (6 * W ^ 2 + 4)) ≤ W * W * 8 + 2 * (W * (6 * W ^ 2 + 4)) := by
        have := Nat.mul_le_mul hdW hdW
        have := Nat.mul_le_mul_right (6 * W ^ 2 + 4) hdW
        omega
      have p1 : W ≤ W ^ 5 := by simpa using Nat.pow_le_pow_right hW1 (show 1 ≤ 5 by norm_num)
      have p2 : W ^ 2 ≤ W ^ 5 := Nat.pow_le_pow_right hW1 (show 2 ≤ 5 by norm_num)
      have p3 : W ^ 3 ≤ W ^ 5 := Nat.pow_le_pow_right hW1 (show 3 ≤ 5 by norm_num)
      have p0 : 1 ≤ W ^ 5 := Nat.one_le_pow _ _ hW1
      have q1 : W * W * (10 * W ^ 3 + 4) = 10 * W ^ 5 + 4 * W ^ 2 := by ring
      have q2 : W * W * 8 + 2 * (W * (6 * W ^ 2 + 4)) = 8 * W ^ 2 + 12 * W ^ 3 + 8 * W := by ring
      omega
    have hαW : vecSize α ≤ G0.eval (60 * W ^ 5) := hαsz.trans (peval_mono _ harg)
    obtain ⟨W', hW'⟩ : ∃ W', W' = W + G0.eval (60 * W ^ 5) := ⟨_, rfl⟩
    have hW'1 : 1 ≤ W' := by omega
    have hxS : ∀ u, Sm (3 * W' ^ 2) ((∑ k, α k • r k) u) := by
      intro u
      have e : (∑ k, α k • r k) u = ∑ k, α k * r k u := by simp [Finset.sum_apply]
      rw [e]
      have := smW_sum hW'1 (show d ≤ W' by omega) _ (fun k =>
        smW_mul (sm_W_of_vecSize α (show vecSize α ≤ W' by omega) k)
          ((hrS k u).mono (show 1 * W ^ 1 ≤ 1 * W' ^ 1 by simp; omega)))
      exact this.mono (le_of_eq (by ring))
    refine (vecSize_le_of_sm _ hxS).trans ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one, Polynomial.eval_ofNat, Polynomial.eval_comp]
    rw [← hW, ← hW']
    calc n * (2 * (3 * W' ^ 2) + 4) ≤ W' * (2 * (3 * W' ^ 2) + 4) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = W' * (6 * W' ^ 2 + 4) := by ring

end MIQPT1
/-! ### Part Q3 -/

open MIQPInNP.SmallSol
open scoped BigOperators Pointwise

namespace MIQPT1

/-- Linear independence of the vectors `w j`, `j ∈ T`. -/
def LIon {n d : ℕ} (T : Finset (Fin d)) (w : Fin d → Fin n → ℚ) : Prop :=
  ∀ c : Fin d → ℝ, (∀ j, j ∉ T → c j = 0) → ∑ j, c j • toReal (w j) = 0 → ∀ j, c j = 0

/-- The cone spanned by the vectors `w j`, `j ∈ T`. -/
def coneT {n d : ℕ} (w : Fin d → Fin n → ℚ) (T : Finset (Fin d)) : Set (Fin n → ℝ) :=
  cone ((fun j => toReal (w j)) '' (T : Set (Fin d)))

lemma mem_coneT {n d : ℕ} (w : Fin d → Fin n → ℚ) (T : Finset (Fin d)) (y : Fin n → ℝ) :
    y ∈ coneT w T ↔ ∃ l : Fin d → ℝ, (∀ j, 0 ≤ l j) ∧ (∀ j, j ∉ T → l j = 0) ∧
      y = ∑ j, l j • toReal (w j) := by
  unfold coneT; rw [mem_cone_image]; simp

lemma coneT_subset {n d : ℕ} (w v : Fin d → Fin n → ℚ) (T : Finset (Fin d)) (X : Set (Fin n → ℝ))
    (hX : X = cone ((fun j => toReal (v j)) '' (T : Set (Fin d))))
    (h : ∀ j ∈ T, toReal (w j) ∈ X) : coneT w T ⊆ X := by
  subst hX
  unfold coneT cone
  intro y hy
  have : Submodule.span NNReal ((fun j => toReal (w j)) '' (T : Set (Fin d))) ≤
      Submodule.span NNReal ((fun j => toReal (v j)) '' (T : Set (Fin d))) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    exact h j hj
  exact this hy

lemma coneT_mono {n d : ℕ} (w : Fin d → Fin n → ℚ) {T T' : Finset (Fin d)} (h : T ⊆ T') :
    coneT w T ⊆ coneT w T' := by
  unfold coneT; exact cone_mono (Set.image_mono (by exact_mod_cast h))

lemma gen_mem_coneT {n d : ℕ} (w : Fin d → Fin n → ℚ) (T : Finset (Fin d)) (j : Fin d)
    (hj : j ∈ T) : toReal (w j) ∈ coneT w T := by
  unfold coneT cone; exact Submodule.subset_span ⟨j, hj, rfl⟩

lemma toReal_sum_smulQ {n d : ℕ} (a : Fin d → ℚ) (r : Fin d → Fin n → ℚ) :
    toReal (∑ k, a k • r k) = ∑ k, (a k : ℝ) • toReal (r k) := by
  ext u; simp [toReal, Finset.sum_apply]

lemma coneT_empty_hyp {n d : ℕ} (w : Fin d → Fin n → ℚ) (f : Fin n → ℚ) (z : Fin n → ℝ)
    (hz : z ∈ coneT w ∅) (hh : z ∈ hyperplane f) : False := by
  obtain ⟨l, -, hl, rfl⟩ := (mem_coneT w ∅ z).mp hz
  have : ∀ j, l j = 0 := fun j => hl j (Finset.notMem_empty j)
  have hh' : ∑ j, (f j : ℝ) * (∑ k, l k • toReal (w k)) j = 1 := hh
  simp [this] at hh'

/-- The statement proved by induction on faces in Lemma 7. -/
def L7P {n d : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (r : Fin d → Fin n → ℚ) (f : Fin n → ℚ)
    (xb : Finset (Fin d) → Fin d → ℚ) (T : Finset (Fin d)) (L : List (Fin d → Fin n → ℚ)) : Prop :=
  (∀ w ∈ L, LIon T w ∧
    (∀ j ∈ T, (∃ k, w j = r k) ∨ (∃ T' : Finset (Fin d), T'.Nonempty ∧ w j = ∑ k, xb T' k • r k)) ∧
    coneT w T ⊆ coneT r T ∧
    ∀ T' ⊆ T, IsLeast (quadForm H '' (coneT w T' ∩ hyperplane f)) 0 →
      ∃ j ∈ T', quadForm H (toReal (w j)) = 0) ∧
  ∀ y ∈ coneT r T, ∃ w ∈ L, y ∈ coneT w T

lemma L7P_base {n d : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (r : Fin d → Fin n → ℚ) (f : Fin n → ℚ)
    (xb : Finset (Fin d) → Fin d → ℚ) (hli : LinearIndependent ℝ (fun j => toReal (r j)))
    (T : Finset (Fin d)) (hpos : ∀ z ∈ coneT r T ∩ hyperplane f, 0 < quadForm H z) :
    L7P H r f xb T [r] := by
  refine ⟨fun w hw => ?_, fun y hy => ⟨r, List.mem_singleton_self r, hy⟩⟩
  rw [List.mem_singleton] at hw
  subst hw
  refine ⟨fun c _ hc => Fintype.linearIndependent_iff.mp hli c hc, fun j _ => Or.inl ⟨j, rfl⟩,
    le_rfl, fun T' hT' hleast => ?_⟩
  exfalso
  obtain ⟨z, ⟨hz1, hz2⟩, hz0⟩ := hleast.1
  have := hpos z ⟨coneT_mono w hT' hz1, hz2⟩
  linarith

lemma LIon_update {n d : ℕ} (r : Fin d → Fin n → ℚ)
    (hli : LinearIndependent ℝ (fun j => toReal (r j))) (T : Finset (Fin d)) (k : Fin d)
    (hk : k ∈ T) (w : Fin d → Fin n → ℚ) (hw : LIon (T.erase k) w)
    (hwc : ∀ j ∈ T.erase k, toReal (w j) ∈ coneT r (T.erase k)) (x : Fin n → ℚ) (α : Fin d → ℝ)
    (hx : toReal x = ∑ i, α i • toReal (r i)) (hαk : α k ≠ 0) :
    LIon T (Function.update w k x) := by
  classical
  intro c hc hsum
  have hrep : ∀ j, ∃ γ : Fin d → ℝ, (∀ i, i ∉ T.erase k → γ i = 0) ∧
      (j ∈ T.erase k → toReal (w j) = ∑ i, γ i • toReal (r i)) := by
    intro j
    by_cases hj : j ∈ T.erase k
    · obtain ⟨l, -, hl, he⟩ := (mem_coneT r _ _).mp (hwc j hj)
      exact ⟨l, hl, fun _ => he⟩
    · exact ⟨0, fun _ _ => rfl, fun h => absurd h hj⟩
  choose γ hγ0 hγ using hrep
  set c' := Function.update c k 0 with hc'
  have key : ∑ j, c j • toReal (Function.update w k x j) =
      c k • toReal x + ∑ j, c' j • toReal (w j) := by
    have : ∀ j, c j • toReal (Function.update w k x j) =
        (if j = k then c k • toReal x else 0) + c' j • toReal (w j) := by
      intro j
      by_cases hj : j = k
      · subst hj; simp [hc']
      · simp [hc', hj, Function.update_of_ne hj]
    rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  have hc'w : ∑ j, c' j • toReal (w j) = ∑ i, (∑ j, c' j * γ j i) • toReal (r i) := by
    have : ∀ j, c' j • toReal (w j) = c' j • ∑ i, γ j i • toReal (r i) := by
      intro j
      by_cases hj : j ∈ T.erase k
      · rw [hγ j hj]
      · have : c' j = 0 := by
          by_cases hjk : j = k
          · subst hjk; simp [hc']
          · have : j ∉ T := fun h => hj (Finset.mem_erase.mpr ⟨hjk, h⟩)
            simp [hc', hjk, hc j this]
        simp [this]
    rw [Finset.sum_congr rfl (fun j _ => this j)]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_smul]
  have htot : ∑ i, (c k * α i + ∑ j, c' j * γ j i) • toReal (r i) = 0 := by
    rw [← hsum, key, hc'w, hx, Finset.smul_sum]
    simp only [smul_smul, add_smul, Finset.sum_add_distrib]
  have hcoef := Fintype.linearIndependent_iff.mp hli _ htot
  have hck : c k = 0 := by
    have h := hcoef k
    have : ∀ j, γ j k = 0 := fun j => hγ0 j k (Finset.notMem_erase k T)
    simp only [this, mul_zero, Finset.sum_const_zero, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_right hαk
  have hsum' : ∑ j, c' j • toReal (w j) = 0 := by
    rw [← hsum, key, hck, zero_smul, zero_add]
  have hc'0 := hw c' (fun j hj => by
    by_cases hjk : j = k
    · subst hjk; simp [hc']
    · have : j ∉ T := fun h => hj (Finset.mem_erase.mpr ⟨hjk, h⟩)
      simp [hc', hjk, hc j this]) hsum'
  intro j
  by_cases hjk : j = k
  · subst hjk; exact hck
  · have := hc'0 j; simpa [hc', hjk] using this

lemma sum_update_split {n d : ℕ} (c : Fin d → ℝ) (w : Fin d → Fin n → ℚ) (k : Fin d)
    (x : Fin n → ℚ) : ∑ j, c j • toReal (Function.update w k x j) =
      c k • toReal x + ∑ j, Function.update c k 0 j • toReal (w j) := by
  classical
  have : ∀ j, c j • toReal (Function.update w k x j) =
      (if j = k then c k • toReal x else 0) + Function.update c k 0 j • toReal (w j) := by
    intro j
    by_cases hj : j = k
    · subst hj; simp
    · simp [hj, Function.update_of_ne hj]
  rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

lemma L7P_step {n d : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (r : Fin d → Fin n → ℚ) (f : Fin n → ℚ)
    (xb : Finset (Fin d) → Fin d → ℚ) (hli : LinearIndependent ℝ (fun j => toReal (r j)))
    (T : Finset (Fin d)) (hT : T.Nonempty)
    (hα0 : ∀ k, 0 ≤ xb T k) (hαT : ∀ k, k ∉ T → xb T k = 0) (hne : ∃ k, xb T k ≠ 0)
    (hQ : quadForm H (toReal (∑ k, xb T k • r k)) = 0)
    (ih : ∀ k ∈ T, xb T k ≠ 0 → ∃ L, L7P H r f xb (T.erase k) L) :
    ∃ L, L7P H r f xb T L := by
  classical
  set α := xb T with hα
  set xbar := ∑ k, α k • r k with hxbar
  have hxR : toReal xbar = ∑ i, (α i : ℝ) • toReal (r i) := toReal_sum_smulQ α r
  have hxcone : toReal xbar ∈ coneT r T := by
    rw [mem_coneT]
    refine ⟨fun i => (α i : ℝ), fun i => by simp only; exact_mod_cast hα0 i, fun i hi => by
      simp [hαT i hi], hxR⟩
  set K := T.filter (fun k => 0 < α k) with hK
  have hKne : K.Nonempty := by
    obtain ⟨k, hk⟩ := hne
    have hkT : k ∈ T := by by_contra h; exact hk (hαT k h)
    exact ⟨k, Finset.mem_filter.mpr ⟨hkT, lt_of_le_of_ne (hα0 k) (Ne.symm hk)⟩⟩
  have hih : ∀ k ∈ K, ∃ L, L7P H r f xb (T.erase k) L := by
    intro k hk
    obtain ⟨hkT, hkpos⟩ := Finset.mem_filter.mp hk
    exact ih k hkT hkpos.ne'
  choose! Lf hLf using hih
  refine ⟨K.toList.flatMap (fun k => (Lf k).map (fun w => Function.update w k xbar)), ?_, ?_⟩
  · intro w' hw'
    obtain ⟨k, hkK, hw'⟩ := List.mem_flatMap.mp hw'
    rw [Finset.mem_toList] at hkK
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hw'
    obtain ⟨hkT, hkpos⟩ := Finset.mem_filter.mp hkK
    obtain ⟨hLI, hgood, hsub, hb⟩ := (hLf k hkK).1 w hw
    have hwc : ∀ j ∈ T.erase k, toReal (w j) ∈ coneT r (T.erase k) :=
      fun j hj => hsub (gen_mem_coneT w _ j hj)
    refine ⟨LIon_update r hli T k hkT w hLI hwc xbar (fun i => (α i : ℝ)) hxR
      (by exact_mod_cast hkpos.ne'), ?_, ?_, ?_⟩
    · intro j hj
      by_cases hjk : j = k
      · subst hjk; right; exact ⟨T, hT, by simp [hxbar, hα]⟩
      · rw [Function.update_of_ne hjk]; exact hgood j (Finset.mem_erase.mpr ⟨hjk, hj⟩)
    · refine coneT_subset _ r T _ rfl (fun j hj => ?_)
      by_cases hjk : j = k
      · subst hjk; simpa using hxcone
      · rw [Function.update_of_ne hjk]
        exact coneT_mono r (Finset.erase_subset k T) (hwc j (Finset.mem_erase.mpr ⟨hjk, hj⟩))
    · intro T' hT' hleast
      by_cases hkT' : k ∈ T'
      · exact ⟨k, hkT', by simpa using hQ⟩
      · have hT'e : T' ⊆ T.erase k := fun j hj =>
          Finset.mem_erase.mpr ⟨fun h => hkT' (h ▸ hj), hT' hj⟩
        have heq : coneT (Function.update w k xbar) T' = coneT w T' := by
          unfold coneT
          congr 1
          refine Set.image_congr (fun j hj => ?_)
          have : j ≠ k := fun h => hkT' (h ▸ hj)
          simp [Function.update_of_ne this]
        rw [heq] at hleast
        obtain ⟨j, hj, hq⟩ := hb T' hT'e hleast
        have : j ≠ k := fun h => hkT' (h ▸ hj)
        exact ⟨j, hj, by rw [Function.update_of_ne this]; exact hq⟩
  · intro y hy
    obtain ⟨l, hl0, hlT, rfl⟩ := (mem_coneT r T y).mp hy
    obtain ⟨k, hkK, hkmin⟩ := K.exists_min_image (fun i => l i / (α i : ℝ)) hKne
    obtain ⟨hkT, hkpos⟩ := Finset.mem_filter.mp hkK
    have hkposR : (0 : ℝ) < α k := by exact_mod_cast hkpos
    set t := l k / (α k : ℝ) with ht
    have ht0 : 0 ≤ t := div_nonneg (hl0 k) hkposR.le
    set y' := ∑ i, (l i - t * α i) • toReal (r i) with hy'
    have hy'c : y' ∈ coneT r (T.erase k) := by
      rw [mem_coneT]
      refine ⟨fun i => l i - t * α i, fun i => ?_, fun i hi => ?_, rfl⟩
      · by_cases hiK : i ∈ K
        · have h1 := hkmin i hiK
          obtain ⟨-, hipos⟩ := Finset.mem_filter.mp hiK
          have hiposR : (0 : ℝ) < α i := by exact_mod_cast hipos
          have : t * α i ≤ l i := by
            have := mul_le_mul_of_nonneg_right h1 hiposR.le
            rwa [div_mul_cancel₀ _ hiposR.ne'] at this
          simp only; linarith
        · have : α i = 0 := by
            by_cases hiT : i ∈ T
            · have : ¬ 0 < α i := fun h => hiK (Finset.mem_filter.mpr ⟨hiT, h⟩)
              exact le_antisymm (not_lt.mp this) (hα0 i)
            · exact hαT i hiT
          simp [this, hl0 i]
      · by_cases hik : i = k
        · subst hik; simp only [ht]; field_simp; ring
        · have hiT : i ∉ T := fun h => hi (Finset.mem_erase.mpr ⟨hik, h⟩)
          simp [hlT i hiT, hαT i hiT]
    obtain ⟨w, hw, hyw⟩ := (hLf k hkK).2 y' hy'c
    obtain ⟨γ, hγ0, hγT, hγe⟩ := (mem_coneT w _ y').mp hyw
    have hγk : γ k = 0 := hγT k (Finset.notMem_erase k T)
    refine ⟨Function.update w k xbar, List.mem_flatMap.mpr ⟨k, Finset.mem_toList.mpr hkK,
      List.mem_map.mpr ⟨w, hw, rfl⟩⟩, ?_⟩
    rw [mem_coneT]
    refine ⟨Function.update γ k t, fun j => ?_, fun j hj => ?_, ?_⟩
    · by_cases hjk : j = k
      · subst hjk; simpa using ht0
      · simp [Function.update_of_ne hjk, hγ0 j]
    · have hjk : j ≠ k := fun h => hj (h ▸ hkT)
      rw [Function.update_of_ne hjk]
      exact hγT j (fun h => hj (Finset.mem_of_mem_erase h))
    · rw [sum_update_split, Function.update_self, Function.update_idem]
      have : Function.update γ k 0 = γ := by
        rw [← hγk]; exact Function.update_eq_self k γ
      rw [this, ← hγe, hy', hxR, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [smul_smul, ← add_smul]; congr 1; ring

end MIQPT1
/-! ### Part Q4 -/

open MIQPInNP.SmallSol
open scoped BigOperators Pointwise

namespace MIQPT1

lemma L7P_all {n d : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (r : Fin d → Fin n → ℚ) (f : Fin n → ℚ)
    (xb : Finset (Fin d) → Fin d → ℚ) (hli : LinearIndependent ℝ (fun j => toReal (r j)))
    (hpsd : ∀ x ∈ cone (Set.range fun j => toReal (r j)), 0 ≤ quadForm H x)
    (hxb : ∀ T : Finset (Fin d), T.Nonempty → (∀ k, 0 ≤ xb T k) ∧ (∀ k, k ∉ T → xb T k = 0) ∧
      ∑ k, (∑ u, f u * r k u) * xb T k = 1 ∧
      (∀ y ∈ cone ((fun j => toReal (r j)) '' (T : Set (Fin d))) ∩ hyperplane f,
        quadForm H (∑ k, (xb T k : ℝ) • toReal (r k)) ≤ quadForm H y)) :
    ∀ T : Finset (Fin d), ∃ L, L7P H r f xb T L := by
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
    by_cases hpos : ∀ z ∈ coneT r T ∩ hyperplane f, 0 < quadForm H z
    · exact ⟨_, L7P_base H r f xb hli T hpos⟩
    · push_neg at hpos
      obtain ⟨z, ⟨hz1, hz2⟩, hzQ⟩ := hpos
      have hT : T.Nonempty := by
        rcases T.eq_empty_or_nonempty with h | h
        · subst h; exact (coneT_empty_hyp r f z hz1 hz2).elim
        · exact h
      obtain ⟨h0, hT', h1, hmin⟩ := hxb T hT
      apply L7P_step H r f xb hli T hT h0 hT'
      · by_contra hcon
        push_neg at hcon
        simp [hcon] at h1
      · rw [toReal_sum_smulQ]
        have hle := hmin z ⟨hz1, hz2⟩
        have hge : 0 ≤ quadForm H (∑ k, (xb T k : ℝ) • toReal (r k)) := by
          apply hpsd
          rw [mem_cone_range]
          exact ⟨fun k => (xb T k : ℝ), fun k => by simp only; exact_mod_cast h0 k, rfl⟩
        linarith
      · intro k hk _
        exact ih (T.erase k) (Finset.erase_ssubset hk)

lemma coneT_univ {n d : ℕ} (w : Fin d → Fin n → ℚ) :
    coneT w Finset.univ = cone (Set.range fun j => toReal (w j)) := by
  unfold coneT; rw [Finset.coe_univ, Set.image_univ]

end MIQPT1

open MIQPT1 in
theorem solution :
    ∃ g : Polynomial ℕ, ∀ (n d : ℕ) (H : Matrix (Fin n) (Fin n) ℚ) (r : Fin d → Fin n → ℚ)
      (f : Fin n → ℚ),
      LinearIndependent ℝ (fun j => toReal (r j)) →
      (∀ x ∈ cone (Set.range fun j => toReal (r j)), 0 ≤ quadForm H x) →
      (∀ j, 0 < ∑ k, (f k : ℝ) * toReal (r j) k) →
      ∃ (N : ℕ) (gens : Fin N → Fin d → Fin n → ℚ),
        (⋃ i, cone (Set.range fun j => toReal (gens i j))) =
          cone (Set.range fun j => toReal (r j)) ∧
        (∀ (i : Fin N) (S : Finset (Fin d)),
          IsLeast (quadForm H ''
              (cone ((fun j => toReal (gens i j)) '' (S : Set (Fin d))) ∩ hyperplane f)) 0 →
            ∃ j ∈ S, quadForm H (toReal (gens i j)) = 0) ∧
        (∀ i, LinearIndependent ℝ (fun j => toReal (gens i j)) ∧
          ∀ j, vecSize (gens i j) ≤ g.eval (matSize H + ∑ k, vecSize (r k) + vecSize f)) := by
  classical
  obtain ⟨Gx, hGx⟩ := xbar_exists
  refine ⟨Polynomial.X + Gx, ?_⟩
  intro n d H r f hli hpsd hfpos
  have hxbex : ∀ T : Finset (Fin d), ∃ α : Fin d → ℚ, T.Nonempty →
      ((∀ k, 0 ≤ α k) ∧ (∀ k, k ∉ T → α k = 0) ∧ ∑ k, (∑ u, f u * r k u) * α k = 1 ∧
      (∀ y ∈ cone ((fun j => toReal (r j)) '' (T : Set (Fin d))) ∩ hyperplane f,
        quadForm H (∑ k, (α k : ℝ) • toReal (r k)) ≤ quadForm H y) ∧
      vecSize (∑ k, α k • r k) ≤ Gx.eval (matSize H + ∑ k, vecSize (r k) + vecSize f)) := by
    intro T
    by_cases hT : T.Nonempty
    · obtain ⟨α, h⟩ := hGx n d H r f hfpos T hT
      exact ⟨α, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hT⟩
  choose xb hxb using hxbex
  obtain ⟨hL1, hL2⟩ := Classical.choose_spec (L7P_all H r f xb hli hpsd
    (fun T hT => ⟨(hxb T hT).1, (hxb T hT).2.1, (hxb T hT).2.2.1, (hxb T hT).2.2.2.1⟩) Finset.univ)
  set L := Classical.choose (L7P_all H r f xb hli hpsd
    (fun T hT => ⟨(hxb T hT).1, (hxb T hT).2.1, (hxb T hT).2.2.1, (hxb T hT).2.2.2.1⟩) Finset.univ)
  refine ⟨L.length, fun i => L.get i, ?_, ?_, ?_⟩
  · ext y
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      have := (hL1 (L.get i) (List.get_mem L i)).2.2.1
      rw [coneT_univ, coneT_univ] at this
      exact this hi
    · intro hy
      rw [← coneT_univ] at hy
      obtain ⟨w, hw, hyw⟩ := hL2 y hy
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hw
      exact ⟨i, by rw [← coneT_univ]; exact hyw⟩
  · intro i S hleast
    exact (hL1 (L.get i) (List.get_mem L i)).2.2.2 S (Finset.subset_univ S) hleast
  · intro i
    obtain ⟨hLI, hgood, -, -⟩ := hL1 (L.get i) (List.get_mem L i)
    refine ⟨Fintype.linearIndependent_iff.mpr (fun c hc j => hLI c (fun j hj =>
      absurd (Finset.mem_univ j) hj) hc j), fun j => ?_⟩
    simp only [Polynomial.eval_add, Polynomial.eval_X]
    rcases hgood j (Finset.mem_univ j) with ⟨k, hk⟩ | ⟨T', hT', hk⟩
    · rw [hk]
      have := Finset.single_le_sum (f := fun k => vecSize (r k)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ k)
      omega
    · rw [hk]
      have := ((hxb T' hT').2.2.2.2)
      omega
