-- Prove2me | solution 1 for MatrixAnalytic.LogReduction.HLU_limits
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-26T12:58:51.789996+00:00
-- url     : https://prove2.me/submissions/33b714d2-a40f-41cd-8605-f44a1193ee49

import Mathlib
import Definitions.Def_MatrixAnalytic_LogReduction_Chain
import Definitions.Def_MatrixAnalytic_LogReduction_QBD
import Definitions.Def_MatrixAnalytic_LogReduction_Passage

open scoped ENNReal

namespace MatrixAnalytic.LogReduction.A3HL

open Filter Topology

section generic

variable {V : Type} [Countable V] [DecidableEq V]

open Classical in
/-- ENNReal version of the avoidance tail. -/
noncomputable def E (P : V → V → ℝ) (A : Set V) (t : ℕ) (y : V) : ℝ≥0∞ :=
  ∑' ω : Fin (t + 1) → V, ENNReal.ofReal
    (if ω 0 = y ∧ ∀ i : Fin (t + 1), i ≠ 0 → ω i ∉ A then pathWeightC P ω else 0)

theorem pw_nonneg (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) {t : ℕ} (ω : Fin (t + 1) → V) :
    0 ≤ pathWeightC P ω :=
  Finset.prod_nonneg fun _ _ => hP _ _

theorem toReal_E (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (A : Set V) (t : ℕ) (y : V) :
    setAvoidTailC P y A t = (E P A t y).toReal := by
  unfold E setAvoidTailC
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  refine tsum_congr fun ω => ?_
  rw [ENNReal.toReal_ofReal]
  split_ifs
  · exact pw_nonneg P hP ω
  · exact le_rfl

theorem E_zero (P : V → V → ℝ) (A : Set V) (y : V) : E P A 0 y = 1 := by
  unfold E
  rw [tsum_eq_single (fun _ => y)]
  · simp [pathWeightC]
  · intro ω hω
    have : ω 0 ≠ y := fun h => hω (funext fun i => by
      rw [show i = 0 from Fin.ext (Nat.lt_one_iff.mp i.isLt), h])
    simp [this]

omit [Countable V] [DecidableEq V] in
theorem pw_cons (P : V → V → ℝ) {t : ℕ} (y : V) (ω : Fin (t + 1) → V) :
    pathWeightC P (Fin.cons y ω : Fin (t + 2) → V) = P y (ω 0) * pathWeightC P ω := by
  unfold pathWeightC
  rw [Fin.prod_univ_succ]
  congr 1

open Classical in
theorem E_succ (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (A : Set V) (t : ℕ) (y : V) :
    E P A (t + 1) y = ∑' z, ENNReal.ofReal (P y z) * (if z ∈ A then 0 else E P A t z) := by
  -- RHS as a double sum
  have hR : ∀ z, ENNReal.ofReal (P y z) * (if z ∈ A then 0 else E P A t z) =
      ∑' ω : Fin (t + 1) → V, ENNReal.ofReal (P y z) * (if z ∈ A then 0 else ENNReal.ofReal
        (if ω 0 = z ∧ ∀ i : Fin (t + 1), i ≠ 0 → ω i ∉ A then pathWeightC P ω else 0)) := by
    intro z
    by_cases hz : z ∈ A
    · simp [hz]
    · simp only [hz, if_false]
      rw [ENNReal.tsum_mul_left]; rfl
  rw [tsum_congr hR, ENNReal.tsum_comm]
  unfold E
  rw [← (Fin.consEquiv (fun _ : Fin (t + 2) => V)).tsum_eq, ENNReal.tsum_prod',
    tsum_eq_single y]
  · refine tsum_congr fun ω => ?_
    rw [tsum_eq_single (ω 0)]
    · simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, true_and, pw_cons]
      have hiff : (∀ i : Fin (t + 2), i ≠ 0 → (Fin.cons y ω : Fin (t + 2) → V) i ∉ A) ↔
          ω 0 ∉ A ∧ ∀ i : Fin (t + 1), i ≠ 0 → ω i ∉ A := by
        constructor
        · intro h
          refine ⟨by simpa using h 1 (by simp), fun i hi => ?_⟩
          simpa using h i.succ (Fin.succ_ne_zero i)
        · intro h i hi
          obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hi
          rw [Fin.cons_succ]
          by_cases hj : j = 0
          · subst hj; exact h.1
          · exact h.2 j hj
      by_cases hc : ∀ i : Fin (t + 1 + 1), i ≠ 0 → (Fin.cons y ω : Fin (t + 2) → V) i ∉ A
      · obtain ⟨h0, h1⟩ := hiff.mp hc
        rw [if_pos hc, if_neg h0, if_pos h1, ENNReal.ofReal_mul (hP _ _)]
      · rw [if_neg hc]
        by_cases h0 : ω 0 ∈ A
        · simp [h0]
        · have h1 : ¬ ∀ i : Fin (t + 1), i ≠ 0 → ω i ∉ A := fun h1 => hc (hiff.mpr ⟨h0, h1⟩)
          rw [if_neg h0, if_neg h1]; simp
    · intro z hz
      by_cases hzA : z ∈ A
      · simp [hzA]
      · simp [hzA, Ne.symm hz]
  · intro v hv
    simp [Fin.consEquiv, hv]

open Classical in
theorem E_le_one (P : V → V → ℝ) (hP : IsStochasticC P) (A : Set V) (t : ℕ) (y : V) :
    E P A t y ≤ 1 := by
  induction t generalizing y with
  | zero => rw [E_zero]
  | succ t ih =>
    rw [E_succ P hP.1]
    calc ∑' z, ENNReal.ofReal (P y z) * (if z ∈ A then 0 else E P A t z)
        ≤ ∑' z, ENNReal.ofReal (P y z) := by
          refine ENNReal.tsum_le_tsum fun z => ?_
          split_ifs
          · simp
          · exact mul_le_of_le_one_right' (ih z)
      _ = 1 := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (hP.1 y) (hP.2 y).summable, (hP.2 y).tsum_eq]
          simp

end generic

section passage

variable {ι : Type} [Countable ι] [DecidableEq ι]

open Classical in
noncomputable def F (P : ℕ × ι → ℕ × ι → ℝ) (T : Set (ℕ × ι)) (y : ℕ × ι) (t : ℕ)
    (x : ℕ × ι) : ℝ≥0∞ :=
  ∑' ω : Fin (t + 2) → ℕ × ι,
    if ω 0 = x ∧ ω (Fin.last (t + 1)) = y ∧ y ∈ T ∧
        ∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ T
    then pathWeightE P ω else 0

theorem firstEntrance_eq (P : ℕ × ι → ℕ × ι → ℝ) (T : Set (ℕ × ι)) (x y : ℕ × ι) :
    firstEntrance P T x y = ∑' t, F P T y t x := rfl

theorem pwE_cons (P : ℕ × ι → ℕ × ι → ℝ) {t : ℕ} (y : ℕ × ι) (ω : Fin (t + 1) → ℕ × ι) :
    pathWeightE P (Fin.cons y ω : Fin (t + 2) → ℕ × ι) =
      ENNReal.ofReal (P y (ω 0)) * pathWeightE P ω := by
  unfold pathWeightE
  rw [Fin.prod_univ_succ]
  congr 1

open Classical in
theorem F_zero (P : ℕ × ι → ℕ × ι → ℝ) (T : Set (ℕ × ι)) (y x : ℕ × ι) :
    F P T y 0 x = if y ∈ T then ENNReal.ofReal (P x y) else 0 := by
  unfold F
  rw [tsum_eq_single ![x, y]]
  · by_cases hy : y ∈ T
    · have : ∀ m : Fin 2, m ≠ 0 → m ≠ Fin.last 1 → False := by
        intro m h0 h1; fin_cases m <;> simp_all
      simp [hy, pathWeightE, this]
    · simp [hy]
  · intro ω hω
    have : ¬ (ω 0 = x ∧ ω (Fin.last 1) = y) := by
      rintro ⟨h0, h1⟩
      apply hω
      funext m
      fin_cases m
      · simpa using h0
      · simpa using h1
    rw [if_neg (fun h => this ⟨h.1, h.2.1⟩)]

open Classical in
theorem F_succ (P : ℕ × ι → ℕ × ι → ℝ) (hP : ∀ x y, 0 ≤ P x y) (T : Set (ℕ × ι))
    (y : ℕ × ι) (t : ℕ) (x : ℕ × ι) :
    F P T y (t + 1) x = ∑' z, ENNReal.ofReal (P x z) * (if z ∈ T then 0 else F P T y t z) := by
  have hR : ∀ z, ENNReal.ofReal (P x z) * (if z ∈ T then 0 else F P T y t z) =
      ∑' ω : Fin (t + 2) → ℕ × ι, ENNReal.ofReal (P x z) * (if z ∈ T then 0 else
        (if ω 0 = z ∧ ω (Fin.last (t + 1)) = y ∧ y ∈ T ∧
          ∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ T
        then pathWeightE P ω else 0)) := by
    intro z
    by_cases hz : z ∈ T
    · simp [hz]
    · simp only [hz, if_false]
      rw [ENNReal.tsum_mul_left]; rfl
  rw [tsum_congr hR, ENNReal.tsum_comm]
  unfold F
  rw [← (Fin.consEquiv (fun _ : Fin (t + 3) => ℕ × ι)).tsum_eq, ENNReal.tsum_prod',
    tsum_eq_single x]
  · refine tsum_congr fun ω => ?_
    rw [tsum_eq_single (ω 0)]
    · simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, true_and, pwE_cons]
      have hl : (Fin.cons x ω : Fin (t + 3) → ℕ × ι) (Fin.last (t + 2)) =
          ω (Fin.last (t + 1)) := by
        rw [← Fin.succ_last, Fin.cons_succ]
      simp only [hl]
      have hiff : (∀ m : Fin (t + 1 + 2), m ≠ 0 → m ≠ Fin.last (t + 1 + 1) →
            (Fin.cons x ω : Fin (t + 3) → ℕ × ι) m ∉ T) ↔
          ω 0 ∉ T ∧ ∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ T := by
        constructor
        · intro h
          refine ⟨?_, fun m h0 h1 => ?_⟩
          · have := h (Fin.succ 0) (Fin.succ_ne_zero _) (by
              rw [Ne, ← Fin.succ_last, Fin.succ_inj]; exact (Fin.last_pos).ne)
            simpa using this
          · have := h m.succ (Fin.succ_ne_zero _) (by
              rw [Ne, ← Fin.succ_last, Fin.succ_inj]; exact h1)
            simpa using this
        · intro h m h0 h1
          obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr h0
          rw [Fin.cons_succ]
          have hj : j ≠ Fin.last (t + 1) := by
            rintro rfl; exact h1 (Fin.succ_last _)
          by_cases hj0 : j = 0
          · subst hj0; exact h.1
          · exact h.2 j hj0 hj
      by_cases hc : ω (Fin.last (t + 1)) = y ∧ y ∈ T ∧ ∀ m : Fin (t + 1 + 2), m ≠ 0 →
          m ≠ Fin.last (t + 1 + 1) → (Fin.cons x ω : Fin (t + 3) → ℕ × ι) m ∉ T
      · obtain ⟨h0, h1⟩ := hiff.mp hc.2.2
        rw [if_pos hc, if_neg h0, if_pos ⟨hc.1, hc.2.1, h1⟩]
      · rw [if_neg hc]
        by_cases h0 : ω 0 ∈ T
        · simp [h0]
        · have h1 : ¬ (ω (Fin.last (t + 1)) = y ∧ y ∈ T ∧
              ∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ T) :=
            fun h1 => hc ⟨h1.1, h1.2.1, hiff.mpr ⟨h0, h1.2.2⟩⟩
          rw [if_neg h0, if_neg h1]; simp
    · intro z hz
      by_cases hzT : z ∈ T
      · simp [hzT]
      · simp [hzT, Ne.symm hz]
  · intro v hv
    simp [Fin.consEquiv, hv]

end passage

section diag

def Dg (M : Fin 2 → Fin 2 → ℝ≥0∞) : Prop := ∀ i j, i ≠ j → M i j = 0
def Off (M : Fin 2 → Fin 2 → ℝ≥0∞) : Prop := ∀ i, M i i = 0

theorem other (i j k : Fin 2) (hij : i ≠ j) (hk : k ≠ i) : k = j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all

theorem Dg_mul {M N : Fin 2 → Fin 2 → ℝ≥0∞} (hM : Dg M) (hN : Dg N) : Dg (matMulE M N) := by
  intro i j hij
  simp only [matMulE, tsum_fintype]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k = i
  · subst hk; rw [hN k j hij, mul_zero]
  · rw [hM i k (Ne.symm hk), zero_mul]

theorem Off_mul {M N : Fin 2 → Fin 2 → ℝ≥0∞} (hM : Off M) (hN : Off N) :
    Dg (matMulE M N) := by
  intro i j hij
  simp only [matMulE, tsum_fintype]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k = i
  · subst hk; rw [hM k, zero_mul]
  · rw [other i j k hij hk, hN j, mul_zero]

theorem DgOff_mul {M N : Fin 2 → Fin 2 → ℝ≥0∞} (hM : Dg M) (hN : Off N) :
    Off (matMulE M N) := by
  intro i
  simp only [matMulE, tsum_fintype]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k = i
  · subst hk; rw [hN k, mul_zero]
  · rw [hM i k (Ne.symm hk), zero_mul]

theorem Dg_add {M N : Fin 2 → Fin 2 → ℝ≥0∞} (hM : Dg M) (hN : Dg N) : Dg (M + N) := by
  intro i j hij
  simp [hM i j hij, hN i j hij]

theorem Dg_one : Dg (matOneE : Fin 2 → Fin 2 → ℝ≥0∞) := by
  intro i j hij; simp [matOneE, hij]

theorem Dg_pow {M : Fin 2 → Fin 2 → ℝ≥0∞} (hM : Dg M) (n : ℕ) : Dg (matPowE M n) := by
  induction n with
  | zero => exact Dg_one
  | succ n ih => exact Dg_mul ih hM

theorem Dg_inv {M : Fin 2 → Fin 2 → ℝ≥0∞} (hM : Dg M) : Dg (seriesInvE M) := by
  intro i j hij
  simp only [seriesInvE]
  simp [Dg_pow hM _ i j hij]

theorem logHL_Dg (A₀ A₁ A₂ : Fin 2 → Fin 2 → ℝ) (h0 : Off (logH A₀ A₁ A₂ 0))
    (h2 : Off (logL A₀ A₁ A₂ 0)) (k : ℕ) :
    Dg (logH A₀ A₁ A₂ (k + 1)) ∧ Dg (logL A₀ A₁ A₂ (k + 1)) := by
  induction k with
  | zero =>
    have hU : Dg (matMulE (logH A₀ A₁ A₂ 0) (logL A₀ A₁ A₂ 0) +
        matMulE (logL A₀ A₁ A₂ 0) (logH A₀ A₁ A₂ 0)) :=
      Dg_add (Off_mul h0 h2) (Off_mul h2 h0)
    exact ⟨Dg_mul (Dg_inv hU) (Off_mul h0 h0), Dg_mul (Dg_inv hU) (Off_mul h2 h2)⟩
  | succ k ih =>
    obtain ⟨ihH, ihL⟩ := ih
    have hU : Dg (matMulE (logH A₀ A₁ A₂ (k + 1)) (logL A₀ A₁ A₂ (k + 1)) +
        matMulE (logL A₀ A₁ A₂ (k + 1)) (logH A₀ A₁ A₂ (k + 1))) :=
      Dg_add (Dg_mul ihH ihL) (Dg_mul ihL ihH)
    exact ⟨Dg_mul (Dg_inv hU) (Dg_mul ihH ihH), Dg_mul (Dg_inv hU) (Dg_mul ihL ihL)⟩

end diag

section concrete

noncomputable def A0 : Fin 2 → Fin 2 → ℝ := fun i j => if i = j then 0 else 2 / 3
noncomputable def A1 : Fin 2 → Fin 2 → ℝ := fun _ _ => 0
noncomputable def A2 : Fin 2 → Fin 2 → ℝ := fun i j => if i = j then 0 else 1 / 3
noncomputable def B : Fin 2 → Fin 2 → ℝ := A2

noncomputable abbrev P : ℕ × Fin 2 → ℕ × Fin 2 → ℝ := qbdP B A0 A1 A2
noncomputable abbrev Q : ℕ × Fin 2 → ℕ × Fin 2 → ℝ := qbdP (fun _ _ => 0) A2 A1 A0

theorem ne_succ (j : Fin 2) : j ≠ j + 1 := by fin_cases j <;> decide
theorem succ_succ (j : Fin 2) : j + 1 + 1 = j := by fin_cases j <;> rfl
theorem eq_or (i b : Fin 2) : b = i ∨ b = i + 1 := by fin_cases i <;> fin_cases b <;> decide

theorem P_nonneg (x y : ℕ × Fin 2) : 0 ≤ P x y := by
  obtain ⟨m, i⟩ := x
  obtain ⟨n, j⟩ := y
  simp only [P, qbdP, B, A0, A1, A2]
  split_ifs <;> norm_num

theorem Q_nonneg (x y : ℕ × Fin 2) : 0 ≤ Q x y := by
  obtain ⟨m, i⟩ := x
  obtain ⟨n, j⟩ := y
  simp only [Q, qbdP, A0, A1, A2]
  split_ifs <;> norm_num

theorem P_far (x y : ℕ × Fin 2) (h : x.1 + 1 < y.1) : P x y = 0 := by
  obtain ⟨m, i⟩ := x
  obtain ⟨n, j⟩ := y
  simp only at h
  simp only [P, qbdP]
  split_ifs <;> first | rfl | omega | simp_all

theorem Pup (L : ℕ) (j : Fin 2) : P (L, j) (L + 1, j + 1) = 2 / 3 := by
  cases L <;> simp [P, qbdP, A0, ne_succ]
theorem Pdn (L : ℕ) (j : Fin 2) : P (L + 1, j) (L, j + 1) = 1 / 3 := by
  have : L ≠ L + 1 + 1 := by omega
  have : L ≠ L + 1 := by omega
  simp [P, qbdP, A2, ne_succ, *]
theorem P00 (j : Fin 2) : P (0, j) (0, j + 1) = 1 / 3 := by
  simp [P, qbdP, B, A2, ne_succ]

theorem P_hasSum (x : ℕ × Fin 2) : HasSum (P x) 1 := by
  obtain ⟨n, i⟩ := x
  cases n with
  | zero =>
    have : HasSum (P (0, i))
        (∑ b ∈ ({0, 1} : Finset ℕ) ×ˢ (Finset.univ : Finset (Fin 2)), P (0, i) b) :=
      hasSum_sum_of_ne_finset_zero (by
        rintro ⟨m, j⟩ hy
        simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton,
          Finset.mem_univ, and_true, not_or] at hy
        simp [P, qbdP, hy.1, hy.2])
    convert this using 1
    rw [Finset.sum_product]
    fin_cases i <;> simp [Fin.sum_univ_two, P, qbdP, B, A0, A2] <;> norm_num
  | succ n =>
    have : HasSum (P (n + 1, i))
        (∑ b ∈ ({n, n + 1, n + 2} : Finset ℕ) ×ˢ (Finset.univ : Finset (Fin 2)), P (n + 1, i) b) :=
      hasSum_sum_of_ne_finset_zero (by
        rintro ⟨m, j⟩ hy
        simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton,
          Finset.mem_univ, and_true, not_or] at hy
        obtain ⟨hy1, hy2, hy3⟩ := hy
        simp only [P, qbdP]
        split_ifs <;> first | rfl | omega | simp_all)
    convert this using 1
    rw [Finset.sum_product, Finset.sum_insert (by simp), Finset.sum_pair (by omega)]
    have h1 : n + 1 ≠ 0 := by omega
    have h2 : n ≠ n + 1 + 1 := by omega
    have h3 : n ≠ n + 1 := by omega
    have h4 : n + 1 ≠ n + 1 + 1 := by omega
    fin_cases i <;> simp [Fin.sum_univ_two, P, qbdP, A0, A1, A2, h1, h2, h3, h4] <;> norm_num

theorem P_stoch : IsStochasticC P := ⟨P_nonneg, P_hasSum⟩

/-! ### Irreducibility -/

theorem stepPow_succ' (t : ℕ) (x y : ℕ × Fin 2) :
    stepPow P (t + 1) x y = ∑' z, stepPow P t x z * P z y := rfl

theorem stepPow_nonneg (t : ℕ) (x y : ℕ × Fin 2) : 0 ≤ stepPow P t x y := by
  induction t generalizing y with
  | zero => simp only [stepPow]; split_ifs <;> norm_num
  | succ t ih =>
    rw [stepPow_succ']
    exact tsum_nonneg fun z => mul_nonneg (ih z) (P_nonneg z y)

theorem stepPow_supp (t : ℕ) (x z : ℕ × Fin 2) (h : x.1 + t < z.1) : stepPow P t x z = 0 := by
  induction t generalizing z with
  | zero =>
    simp only [stepPow]
    rw [if_neg]
    rintro rfl; omega
  | succ t ih =>
    rw [stepPow_succ']
    have : (fun w => stepPow P t x w * P w z) = fun _ => 0 := by
      funext w
      by_cases hw : x.1 + t < w.1
      · rw [ih w hw, zero_mul]
      · rw [P_far w z (by omega), mul_zero]
    rw [this, tsum_zero]

theorem step_pos (t : ℕ) (x z y : ℕ × Fin 2) (h1 : 0 < stepPow P t x z) (h2 : 0 < P z y) :
    0 < stepPow P (t + 1) x y := by
  rw [stepPow_succ']
  have hs : Summable fun w => stepPow P t x w * P w y := by
    apply summable_of_ne_finset_zero (s := (Finset.range (x.1 + t + 1)) ×ˢ Finset.univ)
    intro w hw
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true, not_lt] at hw
    rw [stepPow_supp t x w (by omega), zero_mul]
  exact hs.tsum_pos (fun w => mul_nonneg (stepPow_nonneg _ _ _) (P_nonneg _ _)) z
    (mul_pos h1 h2)

def R (x : ℕ × Fin 2) : Set (ℕ × Fin 2) := {y | ∃ t, 0 < stepPow P t x y}

theorem R_self (x : ℕ × Fin 2) : x ∈ R x := ⟨0, by simp [stepPow]⟩

theorem R_edge {x y z : ℕ × Fin 2} (hy : y ∈ R x) (h : 0 < P y z) : z ∈ R x := by
  obtain ⟨t, ht⟩ := hy
  exact ⟨t + 1, step_pos t x y z ht h⟩

theorem P_irr : IrreducibleC P := by
  intro x y
  have hdown : ∀ n (i : Fin 2), (n, i) ∈ R x → ∃ c, ((0 : ℕ), c) ∈ R x := by
    intro n
    induction n with
    | zero => exact fun i h => ⟨i, h⟩
    | succ n ih => exact fun i h => ih (i + 1) (R_edge h (by rw [Pdn]; norm_num))
  obtain ⟨c0, hc0⟩ := hdown x.1 x.2 (R_self x)
  have hall : ∀ c : Fin 2, ((0 : ℕ), c) ∈ R x := by
    intro c
    rcases eq_or c0 c with h | h
    · rw [h]; exact hc0
    · rw [h]; exact R_edge hc0 (by rw [P00]; norm_num)
  have hup : ∀ m (c : Fin 2), (m, c) ∈ R x := by
    intro m
    induction m with
    | zero => exact hall
    | succ m ih =>
      intro c
      have := R_edge (ih (c + 1)) (z := (m + 1, c + 1 + 1)) (by rw [Pup]; norm_num)
      rwa [succ_succ] at this
  exact hup y.1 y.2

/-! ### Transience of every state -/

open Classical in
theorem lower (n : ℕ) (i : Fin 2) (t k : ℕ) (j : Fin 2) :
    ENNReal.ofReal (1 - (1 / 2) ^ (k + 1)) ≤ E P {(n, i)} t (n + 1 + k, j) := by
  induction t generalizing k j with
  | zero => rw [E_zero]; exact ENNReal.ofReal_le_of_le_toReal (by simp)
  | succ t ih =>
    rw [E_succ P P_nonneg]
    cases k with
    | zero =>
      refine le_trans ?_ (ENNReal.le_tsum (n + 1 + 0 + 1, j + 1))
      have hn : (n + 1 + 0 + 1, j + 1) ∉ ({(n, i)} : Set (ℕ × Fin 2)) := by simp; omega
      rw [if_neg hn, Pup]
      calc ENNReal.ofReal (1 - (1 / 2) ^ (0 + 1))
          = ENNReal.ofReal (2 / 3) * ENNReal.ofReal (1 - (1 / 2) ^ (1 + 1)) := by
            rw [← ENNReal.ofReal_mul (by norm_num)]; norm_num
        _ ≤ ENNReal.ofReal (2 / 3) * E P {(n, i)} t (n + 1 + 1, j + 1) := by
            gcongr; exact ih 1 (j + 1)
    | succ l =>
      have hne : (n + 1 + (l + 1) + 1, j + 1) ≠ (n + 1 + l, j + 1) := by simp; omega
      refine le_trans ?_ (ENNReal.sum_le_tsum {(n + 1 + (l + 1) + 1, j + 1), (n + 1 + l, j + 1)})
      rw [Finset.sum_pair hne]
      have hn1 : (n + 1 + (l + 1) + 1, j + 1) ∉ ({(n, i)} : Set (ℕ × Fin 2)) := by simp; omega
      have hn2 : (n + 1 + l, j + 1) ∉ ({(n, i)} : Set (ℕ × Fin 2)) := by simp; omega
      rw [if_neg hn1, if_neg hn2, Pup, show n + 1 + (l + 1) = (n + 1 + l) + 1 from rfl, Pdn]
      calc ENNReal.ofReal (1 - (1 / 2) ^ (l + 1 + 1))
          = ENNReal.ofReal (2 / 3) * ENNReal.ofReal (1 - (1 / 2) ^ ((l + 2) + 1)) +
            ENNReal.ofReal (1 / 3) * ENNReal.ofReal (1 - (1 / 2) ^ (l + 1)) := by
            rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
              ← ENNReal.ofReal_add (by
                have : (1 / 2 : ℝ) ^ (l + 2 + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
                nlinarith) (by
                have : (1 / 2 : ℝ) ^ (l + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
                nlinarith)]
            congr 1; ring
        _ ≤ ENNReal.ofReal (2 / 3) * E P {(n, i)} t (n + 1 + l + 1 + 1, j + 1) +
            ENNReal.ofReal (1 / 3) * E P {(n, i)} t (n + 1 + l, j + 1) := by
            gcongr
            · exact ih (l + 2) (j + 1)
            · exact ih l (j + 1)

theorem P_trans (x : ℕ × Fin 2) : ¬ Recurrent P x := by
  obtain ⟨n, i⟩ := x
  intro h
  have hb : ∀ t, (1 / 3 : ℝ) ≤ returnTailC P (n, i) (t + 1) := by
    intro t
    classical
    unfold returnTailC
    rw [toReal_E P P_nonneg]
    rw [← ENNReal.ofReal_le_iff_le_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top
      (E_le_one P P_stoch _ _ _)), E_succ P P_nonneg]
    refine le_trans ?_ (ENNReal.le_tsum (n + 1 + 0, i + 1))
    have hn : (n + 1 + 0, i + 1) ∉ ({(n, i)} : Set (ℕ × Fin 2)) := by simp
    rw [if_neg hn, show n + 1 + 0 = n + 1 from rfl, Pup]
    calc ENNReal.ofReal (1 / 3)
        = ENNReal.ofReal (2 / 3) * ENNReal.ofReal (1 - (1 / 2) ^ (0 + 1)) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]; norm_num
      _ ≤ _ := by gcongr; exact lower n i t 0 (i + 1)
  have := ge_of_tendsto h (Filter.eventually_atTop.2 ⟨1, fun t ht => by
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    exact hb s⟩)
  norm_num at this

/-! ### The level-reversed chain and `Ĝ` -/

abbrev T0 : Set (ℕ × Fin 2) := level 0

theorem memT (z : ℕ × Fin 2) : z ∈ T0 ↔ z.1 = 0 := Iff.rfl

theorem Q_up (m : ℕ) (i : Fin 2) : Q (m + 1, i) (m + 2, i + 1) = 1 / 3 := by
  simp [Q, qbdP, A2, ne_succ]
theorem Q_dn (m : ℕ) (i : Fin 2) : Q (m + 1, i) (m, i + 1) = 2 / 3 := by
  have : m ≠ m + 1 + 1 := by omega
  have : m ≠ m + 1 := by omega
  simp [Q, qbdP, A0, ne_succ, *]

theorem Q_supp (m : ℕ) (i : Fin 2) (z : ℕ × Fin 2) (h1 : z ≠ (m + 2, i + 1))
    (h2 : z ≠ (m, i + 1)) : Q (m + 1, i) z = 0 := by
  obtain ⟨l, b⟩ := z
  rcases eq_or i b with hb | hb
  · subst hb
    simp only [Q, qbdP, A0, A1, A2]
    split_ifs <;> simp
  · subst hb
    have hl1 : l ≠ m + 2 := fun h => h1 (by rw [h])
    have hl2 : l ≠ m := fun h => h2 (by rw [h])
    simp only [Q, qbdP, A1]
    split_ifs <;> first | rfl | (exfalso; omega) | simp_all

theorem Q_par (x z : ℕ × Fin 2) (h : Q x z ≠ 0) :
    (x.1 + x.2.val) % 2 = (z.1 + z.2.val) % 2 := by
  obtain ⟨l, a⟩ := x
  obtain ⟨l', b⟩ := z
  simp only [Q, qbdP, A0, A1, A2] at h
  rcases eq_or a b with hb | hb
  · subst hb; split_ifs at h <;> simp_all
  · subst hb
    have hv : (a + 1).val = 1 - a.val := by fin_cases a <;> rfl
    have ha : a.val < 2 := a.isLt
    simp only [hv]
    split_ifs at h <;> first | omega | simp at h

theorem rowQ (m : ℕ) (i : Fin 2) (g : ℕ × Fin 2 → ℝ≥0∞) :
    ∑' z, ENNReal.ofReal (Q (m + 1, i) z) * g z =
      ENNReal.ofReal (1 / 3) * g (m + 2, i + 1) + ENNReal.ofReal (2 / 3) * g (m, i + 1) := by
  have hne : ((m + 2, i + 1) : ℕ × Fin 2) ≠ (m, i + 1) := by simp
  rw [tsum_eq_sum (s := {(m + 2, i + 1), (m, i + 1)}), Finset.sum_pair hne, Q_up, Q_dn]
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
  rw [Q_supp m i z hz.1 hz.2]; simp

open Classical in
theorem F_par (y : ℕ × Fin 2) (t : ℕ) (x : ℕ × Fin 2)
    (h : (x.1 + x.2.val) % 2 ≠ (y.1 + y.2.val) % 2) : F Q T0 y t x = 0 := by
  induction t generalizing x with
  | zero =>
    rw [F_zero]
    split_ifs
    · rw [show Q x y = 0 from by_contra fun hq => h (Q_par x y hq)]; simp
    · rfl
  | succ t ih =>
    rw [F_succ Q Q_nonneg]
    refine ENNReal.tsum_eq_zero.mpr fun z => ?_
    by_cases hq : Q x z = 0
    · simp [hq]
    · have := Q_par x z hq
      split_ifs
      · simp
      · rw [ih z (by omega), mul_zero]

open Classical in
theorem split_level (f : ℕ × Fin 2 → ℝ≥0∞) :
    ∑' z, f z * (if z ∈ T0 then 0 else 1) + ∑ j, f (0, j) = ∑' z, f z := by
  have : ∑ j, f (0, j) = ∑' z, f z * (if z ∈ T0 then 1 else 0) := by
    rw [ENNReal.tsum_prod', tsum_eq_single 0]
    · simp [memT, tsum_fintype]
    · intro n hn; simp [memT, hn]
  rw [this, ← ENNReal.tsum_add]
  refine tsum_congr fun z => ?_
  split_ifs <;> simp

open Classical in
theorem identity (t m : ℕ) (i : Fin 2) :
    E Q T0 (t + 1) (m + 1, i) + ∑ j, F Q T0 (0, j) t (m + 1, i) = E Q T0 t (m + 1, i) := by
  induction t generalizing m i with
  | zero =>
    rw [E_succ Q Q_nonneg, E_zero]
    simp only [F_zero, memT, if_true]
    have h1 : ∑' z, ENNReal.ofReal (Q (m + 1, i) z) = 1 := by
      have := rowQ m i (fun _ => 1)
      simp only [mul_one] at this
      rw [this, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
    rw [← h1, ← split_level (fun z => ENNReal.ofReal (Q (m + 1, i) z))]
    congr 1
    refine tsum_congr fun z => ?_
    split_ifs <;> simp_all [E_zero, memT]
  | succ t ih =>
    rw [E_succ Q Q_nonneg (t := t + 1), E_succ Q Q_nonneg (t := t)]
    simp only [F_succ Q Q_nonneg, Fin.sum_univ_two]
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
    refine tsum_congr fun z => ?_
    by_cases hz : z ∈ T0
    · simp [hz]
    · simp only [hz, if_false, ← mul_add]
      obtain ⟨l, b⟩ := z
      obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by
        have : l ≠ 0 := hz; omega⟩
      have := ih l' b
      rw [Fin.sum_univ_two] at this
      rw [this]

theorem rho_le : (17 / 18 : ℝ) ≤ 1 := by norm_num

open Classical in
theorem N_bound (t m : ℕ) (i : Fin 2) :
    E Q T0 t (m + 1, i) ≤ ENNReal.ofReal ((17 / 18) ^ t * (3 / 2) ^ m) := by
  induction t generalizing m i with
  | zero =>
    rw [E_zero, ENNReal.one_le_ofReal]
    simp only [pow_zero, one_mul]; exact one_le_pow₀ (by norm_num)
  | succ t ih =>
    rw [E_succ Q Q_nonneg, rowQ]
    have hT1 : ((m + 2 : ℕ), i + 1) ∉ T0 := by simp [memT]
    rw [if_neg hT1]
    cases m with
    | zero =>
      have hT2 : ((0 : ℕ), i + 1) ∈ T0 := by simp [memT]
      rw [if_pos hT2, mul_zero, add_zero]
      calc ENNReal.ofReal (1 / 3) * E Q T0 t (0 + 2, i + 1)
          ≤ ENNReal.ofReal (1 / 3) * ENNReal.ofReal ((17 / 18) ^ t * (3 / 2) ^ 1) := by
            gcongr; exact ih 1 (i + 1)
        _ ≤ _ := by
            rw [← ENNReal.ofReal_mul (by norm_num)]
            apply ENNReal.ofReal_le_ofReal
            have : (0 : ℝ) ≤ (17 / 18) ^ t := by positivity
            have h' : (17 / 18 : ℝ) ^ (t + 1) = (17 / 18) ^ t * (17 / 18) := pow_succ _ _
            simp only [pow_zero, mul_one, pow_one]
            rw [h']; nlinarith
    | succ k =>
      have hT2 : ((k + 1 : ℕ), i + 1) ∉ T0 := by simp [memT]
      rw [if_neg hT2]
      calc ENNReal.ofReal (1 / 3) * E Q T0 t (k + 1 + 2, i + 1) +
            ENNReal.ofReal (2 / 3) * E Q T0 t (k + 1, i + 1)
          ≤ ENNReal.ofReal (1 / 3) * ENNReal.ofReal ((17 / 18) ^ t * (3 / 2) ^ (k + 2)) +
            ENNReal.ofReal (2 / 3) * ENNReal.ofReal ((17 / 18) ^ t * (3 / 2) ^ k) := by
            gcongr
            · exact ih (k + 2) (i + 1)
            · exact ih k (i + 1)
        _ = _ := by
            rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1; ring

theorem total (i : Fin 2) : ∑' s, ∑ j, F Q T0 (0, j) s (1, i) = 1 := by
  have hpart : ∀ t, (∑ s ∈ Finset.range t, ∑ j, F Q T0 (0, j) s (0 + 1, i)) +
      E Q T0 t (0 + 1, i) = 1 := by
    intro t
    induction t with
    | zero => simp [E_zero]
    | succ t ih =>
      rw [Finset.sum_range_succ, add_assoc, add_comm (∑ j, _), identity, ih]
  have h1 := ENNReal.tendsto_nat_tsum (fun s => ∑ j, F Q T0 (0, j) s (0 + 1, i))
  have h0 : Tendsto (fun t => ENNReal.ofReal ((17 / 18 : ℝ) ^ t * (3 / 2) ^ 0)) atTop (𝓝 0) := by
    simp only [pow_zero, mul_one]
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
      (by norm_num))
  have h2 : Tendsto (fun t => E Q T0 t (0 + 1, i)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => zero_le)
      (fun t => N_bound t 0 i)
  have h3 := h1.add h2
  simp only [hpart, add_zero] at h3
  exact (tendsto_nhds_unique h3 tendsto_const_nhds)

theorem Ghat_val (i j : Fin 2) : matGhat A0 A1 A2 i j = if i = j then 0 else 1 := by
  have hG : ∀ i j, matGhat A0 A1 A2 i j = ∑' t, F Q T0 (0, j) t (1, i) := fun _ _ => rfl
  have hii : ∀ i, matGhat A0 A1 A2 i i = 0 := by
    intro i
    rw [hG]
    exact ENNReal.tsum_eq_zero.mpr fun t => F_par _ _ _ (by simp; omega)
  have hsum : ∀ i, matGhat A0 A1 A2 i 0 + matGhat A0 A1 A2 i 1 = 1 := by
    intro i
    rw [hG, hG, ← ENNReal.tsum_add, ← total i]
    simp [Fin.sum_univ_two]
  have hs' : ∀ i : Fin 2, matGhat A0 A1 A2 i (i + 1) = 1 := by
    intro i
    have hs : matGhat A0 A1 A2 i i + matGhat A0 A1 A2 i (i + 1) = 1 := by
      fin_cases i
      · exact hsum 0
      · rw [add_comm]; exact hsum 1
    rwa [hii, zero_add] at hs
  split_ifs with h
  · subst h; exact hii i
  · rcases eq_or i j with h' | h'
    · exact absurd h'.symm h
    · rw [h']; exact hs' i

theorem ghat_stat : IsStationaryVec (matGhat A0 A1 A2) (fun _ => (1 / 2 : ℝ)) := by
  refine ⟨fun _ => by norm_num, ?_, fun j => ?_⟩
  · convert hasSum_fintype (fun _ : Fin 2 => (1 / 2 : ℝ)) using 1
    norm_num
  · convert hasSum_fintype (fun i : Fin 2 => (1 / 2 : ℝ) * (matGhat A0 A1 A2 i j).toReal)
      using 1
    simp only [Fin.sum_univ_two, Ghat_val]
    fin_cases j <;> simp

theorem ghat_unique (g' : Fin 2 → ℝ) (h : IsStationaryVec (matGhat A0 A1 A2) g') :
    g' = fun _ => (1 / 2 : ℝ) := by
  obtain ⟨_, hs, hst⟩ := h
  have e1 := hs.unique (hasSum_fintype g')
  have e2 := (hst 0).unique (hasSum_fintype _)
  simp only [Fin.sum_univ_two, Ghat_val] at e1 e2
  simp at e2
  funext i
  fin_cases i <;> simp <;> linarith

theorem logH_01 (k : ℕ) : logH A0 A1 A2 (k + 1) 0 1 = 0 := by
  have hA1 : Dg (ennMat A1) := by intro i j _; simp [ennMat, A1]
  have hA0 : Off (ennMat A0) := by intro i; simp [ennMat, A0]
  have hA2 : Off (ennMat A2) := by intro i; simp [ennMat, A2]
  have h0 : Off (logH A0 A1 A2 0) := DgOff_mul (Dg_inv hA1) hA0
  have h2 : Off (logL A0 A1 A2 0) := DgOff_mul (Dg_inv hA1) hA2
  exact (logHL_Dg A0 A1 A2 h0 h2 k).1 0 1 (by decide)

end concrete

end MatrixAnalytic.LogReduction.A3HL

open MatrixAnalytic.LogReduction in
open Filter Topology in
theorem solution : ¬ (∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)),
    ((∀ x : ℕ × ι, PositiveRecurrent (qbdP B A₀ A₁ A₂) x) →
      ∀ g : ι → ℝ, IsStationaryVec (matG (qbdP B A₀ A₁ A₂)) g →
        (∀ g' : ι → ℝ, IsStationaryVec (matG (qbdP B A₀ A₁ A₂)) g' → g' = g) →
        (∀ i j : ι, Tendsto (fun k => logH A₀ A₁ A₂ k i j) atTop (𝓝 0)) ∧
        (∀ i j : ι, Tendsto (fun k => logL A₀ A₁ A₂ k i j) atTop (𝓝 (ENNReal.ofReal (g j)))) ∧
        (∀ i j : ι, Tendsto (fun k => logU A₀ A₁ A₂ k i j) atTop (𝓝 0))) ∧
    ((∀ x : ℕ × ι, ¬ Recurrent (qbdP B A₀ A₁ A₂) x) →
      ∀ ĝ : ι → ℝ, IsStationaryVec (matGhat A₀ A₁ A₂) ĝ →
        (∀ g' : ι → ℝ, IsStationaryVec (matGhat A₀ A₁ A₂) g' → g' = ĝ) →
        (∀ i j : ι, Tendsto (fun k => logH A₀ A₁ A₂ k i j) atTop (𝓝 (ENNReal.ofReal (ĝ j)))) ∧
        (∀ i j : ι, Tendsto (fun k => logL A₀ A₁ A₂ k i j) atTop (𝓝 0)) ∧
        (∀ i j : ι, Tendsto (fun k => logU A₀ A₁ A₂ k i j) atTop (𝓝 0)))) := by
  intro h
  have hl := ((h (ι := Fin 2) A3HL.B A3HL.A0 A3HL.A1 A3HL.A2 A3HL.P_stoch A3HL.P_irr).2
    A3HL.P_trans _ A3HL.ghat_stat A3HL.ghat_unique).1 0 1
  have h1 := hl.comp (tendsto_add_atTop_nat 1)
  have h2 : (fun k => logH A3HL.A0 A3HL.A1 A3HL.A2 k 0 1) ∘ (fun k => k + 1) = fun _ => 0 :=
    funext fun k => A3HL.logH_01 k
  rw [h2] at h1
  have := tendsto_nhds_unique h1 tendsto_const_nhds
  norm_num at this

#print axioms solution
