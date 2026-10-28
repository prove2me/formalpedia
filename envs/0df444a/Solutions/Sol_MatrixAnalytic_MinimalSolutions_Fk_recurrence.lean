-- Prove2me | solution 1 for MatrixAnalytic.MinimalSolutions.Fk_recurrence
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-26T13:20:35.60646+00:00
-- url     : https://prove2.me/submissions/700f41a9-a1d2-4e83-91ff-aa0bbb44e3f8

import Mathlib
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Chain
import Definitions.Def_MatrixAnalytic_MinimalSolutions_QBD
import Definitions.Def_MatrixAnalytic_MinimalSolutions_Passage

open scoped ENNReal

namespace MatrixAnalytic.MinimalSolutions.A3FK

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

section concrete

noncomputable def A0 : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = j then (if i = 0 then 2 / 3 else 1 / 3) else 0
noncomputable def A1 : Fin 2 → Fin 2 → ℝ := fun _ _ => 0
noncomputable def A2 : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = j then (if i = 0 then 1 / 3 else 2 / 3) else 0
noncomputable def B : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = j then 0 else (if i = 0 then 1 / 3 else 2 / 3)
noncomputable def Y : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = j then (if i = 0 then 1 else 1 / 2) else 0

noncomputable abbrev P : ℕ × Fin 2 → ℕ × Fin 2 → ℝ := qbdP B A0 A1 A2

theorem ne_succ (j : Fin 2) : j ≠ j + 1 := by fin_cases j <;> decide
theorem eq_or (i b : Fin 2) : b = i ∨ b = i + 1 := by fin_cases i <;> fin_cases b <;> decide

theorem P_nonneg (x y : ℕ × Fin 2) : 0 ≤ P x y := by
  obtain ⟨m, i⟩ := x
  obtain ⟨n, j⟩ := y
  simp only [P, qbdP, B, A0, A1, A2]
  split_ifs <;> norm_num

theorem P_far (x y : ℕ × Fin 2) (h : x.1 + 1 < y.1) : P x y = 0 := by
  obtain ⟨m, i⟩ := x
  obtain ⟨n, j⟩ := y
  simp only at h
  simp only [P, qbdP]
  split_ifs <;> first | rfl | omega | simp_all

theorem Pup_pos (L : ℕ) (j : Fin 2) : 0 < P (L, j) (L + 1, j) := by
  cases L <;> fin_cases j <;> simp [P, qbdP, A0] <;> norm_num
theorem Pdn_pos (L : ℕ) (j : Fin 2) : 0 < P (L + 1, j) (L, j) := by
  have : L ≠ L + 1 + 1 := by omega
  have : L ≠ L + 1 := by omega
  fin_cases j <;> simp [P, qbdP, A2, *] <;> norm_num
theorem P00_pos (j : Fin 2) : 0 < P (0, j) (0, j + 1) := by
  fin_cases j <;> simp [P, qbdP, B] <;> norm_num

theorem Pup0 (L : ℕ) : P (L, 0) (L + 1, 0) = 2 / 3 := by
  cases L <;> simp [P, qbdP, A0]
theorem Pdn0 (L : ℕ) : P (L + 1, 0) (L, 0) = 1 / 3 := by
  have : L ≠ L + 1 + 1 := by omega
  have : L ≠ L + 1 := by omega
  simp [P, qbdP, A2, *]

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
  have hdown : ∀ n (i : Fin 2), (n, i) ∈ R x → ((0 : ℕ), i) ∈ R x := by
    intro n
    induction n with
    | zero => exact fun i h => h
    | succ n ih => exact fun i h => ih i (R_edge h (Pdn_pos n i))
  have hc0 := hdown x.1 x.2 (R_self x)
  have hall : ∀ c : Fin 2, ((0 : ℕ), c) ∈ R x := by
    intro c
    rcases eq_or x.2 c with h | h
    · rw [h]; exact hc0
    · rw [h]; exact R_edge hc0 (P00_pos _)
  have hup : ∀ m (c : Fin 2), (m, c) ∈ R x := by
    intro m
    induction m with
    | zero => exact hall
    | succ m ih => exact fun c => R_edge (ih c) (Pup_pos m c)
  exact hup y.1 y.2

/-! ### Transience of `(0, 0)` -/

open Classical in
theorem lower (t k : ℕ) :
    ENNReal.ofReal (1 - (1 / 2) ^ (k + 1)) ≤ E P {((0 : ℕ), (0 : Fin 2))} t (1 + k, 0) := by
  induction t generalizing k with
  | zero => rw [E_zero]; exact ENNReal.ofReal_le_of_le_toReal (by simp)
  | succ t ih =>
    rw [E_succ P P_nonneg]
    cases k with
    | zero =>
      refine le_trans ?_ (ENNReal.le_tsum (1 + 0 + 1, 0))
      have hn : ((1 + 0 + 1 : ℕ), (0 : Fin 2)) ∉ ({(0, 0)} : Set (ℕ × Fin 2)) := by simp
      rw [if_neg hn, Pup0]
      calc ENNReal.ofReal (1 - (1 / 2) ^ (0 + 1))
          = ENNReal.ofReal (2 / 3) * ENNReal.ofReal (1 - (1 / 2) ^ (1 + 1)) := by
            rw [← ENNReal.ofReal_mul (by norm_num)]; norm_num
        _ ≤ ENNReal.ofReal (2 / 3) * E P {(0, 0)} t (1 + 1, 0) := by
            gcongr; exact ih 1
    | succ l =>
      have hne : ((1 + (l + 1) + 1 : ℕ), (0 : Fin 2)) ≠ (1 + l, 0) := by simp; omega
      refine le_trans ?_ (ENNReal.sum_le_tsum {(1 + (l + 1) + 1, 0), (1 + l, 0)})
      rw [Finset.sum_pair hne]
      have hn1 : ((1 + (l + 1) + 1 : ℕ), (0 : Fin 2)) ∉ ({(0, 0)} : Set (ℕ × Fin 2)) := by
        simp
      have hn2 : ((1 + l : ℕ), (0 : Fin 2)) ∉ ({(0, 0)} : Set (ℕ × Fin 2)) := by simp
      rw [if_neg hn1, if_neg hn2, Pup0, show 1 + (l + 1) = (1 + l) + 1 from rfl, Pdn0]
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
        _ ≤ ENNReal.ofReal (2 / 3) * E P {(0, 0)} t (1 + l + 1 + 1, 0) +
            ENNReal.ofReal (1 / 3) * E P {(0, 0)} t (1 + l, 0) := by
            gcongr
            · exact ih (l + 2)
            · exact ih l

theorem P_notPR : ¬ PositiveRecurrent P ((0 : ℕ), (0 : Fin 2)) := by
  intro h
  have h' : Recurrent P ((0 : ℕ), (0 : Fin 2)) := h.tendsto_atTop_zero
  have hb : ∀ t, (1 / 3 : ℝ) ≤ returnTailC P ((0 : ℕ), (0 : Fin 2)) (t + 1) := by
    intro t
    classical
    unfold returnTailC
    rw [toReal_E P P_nonneg]
    rw [← ENNReal.ofReal_le_iff_le_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top
      (E_le_one P P_stoch _ _ _)), E_succ P P_nonneg]
    refine le_trans ?_ (ENNReal.le_tsum (1 + 0, 0))
    have hn : ((1 + 0 : ℕ), (0 : Fin 2)) ∉ ({(0, 0)} : Set (ℕ × Fin 2)) := by simp
    rw [if_neg hn, show 1 + 0 = 0 + 1 from rfl, Pup0]
    calc ENNReal.ofReal (1 / 3)
        = ENNReal.ofReal (2 / 3) * ENNReal.ofReal (1 - (1 / 2) ^ (0 + 1)) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]; norm_num
      _ ≤ _ := by gcongr; exact lower t 0
  have := ge_of_tendsto h' (Filter.eventually_atTop.2 ⟨1, fun t ht => by
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    exact hb s⟩)
  norm_num at this

/-! ### The solution `Y` -/

theorem Y_nonneg (i j : Fin 2) : 0 ≤ Y i j := by
  simp only [Y]; split_ifs <;> norm_num

theorem Y_sol : ennMat Y = ennMat A0 + matMulE (ennMat A1) (ennMat Y) +
    matMulE (ennMat A2) (matMulE (ennMat Y) (ennMat Y)) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp only [matMulE, ennMat, Y, A0, A1, A2, tsum_fintype, Fin.sum_univ_two, Fin.isValue,
      Fin.zero_eta, Fin.mk_one, Pi.add_apply, if_true, if_false,
      (by decide : ((0 : Fin 2) = 1) = False), (by decide : ((1 : Fin 2) = 0) = False),
      ENNReal.ofReal_zero, zero_mul, mul_zero, add_zero, zero_add, eq_self_iff_true] <;>
    simp (disch := norm_num) only [← ENNReal.ofReal_mul, ← ENNReal.ofReal_add] <;>
    norm_num

end concrete

end MatrixAnalytic.MinimalSolutions.A3FK

open MatrixAnalytic.MinimalSolutions in
theorem solution : ¬ (∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (Bhat : ι → ι → ℝ),
    -- (8.26)
    ((∀ i j, seriesInvE (ennMat A₁) i j ≠ ⊤) ∧
      matF (qbdP B A₀ A₁ A₂) 1 = matMulE (seriesInvE (ennMat A₁)) (ennMat A₀)) ∧
    -- (8.27)
    (∀ k : ℕ, 1 ≤ k →
      (∀ i j, seriesInvE (ennMat A₁ + matMulE (ennMat A₂) (matF (qbdP B A₀ A₁ A₂) k)) i j ≠ ⊤) ∧
        matF (qbdP B A₀ A₁ A₂) (k + 1) =
          matMulE (seriesInvE (ennMat A₁ + matMulE (ennMat A₂) (matF (qbdP B A₀ A₁ A₂) k)))
            (ennMat A₀)) ∧
    -- monotone convergence to `Ĝ`
    (∀ k : ℕ, 1 ≤ k → ∀ i j, matF (qbdP B A₀ A₁ A₂) k i j ≤ matF (qbdP B A₀ A₁ A₂) (k + 1) i j) ∧
    (∀ i j, Filter.Tendsto (fun k => matF (qbdP B A₀ A₁ A₂) k i j) Filter.atTop
      (nhds (matG (qbdP Bhat A₂ A₁ A₀) i j))) ∧
    -- positive recurrent: `Ĝ` substochastic
    ((∀ x : ℕ × ι, PositiveRecurrent (qbdP B A₀ A₁ A₂) x) →
      (∀ i, ∑' j, matG (qbdP Bhat A₂ A₁ A₀) i j ≤ 1) ∧ ∃ i, ∑' j, matG (qbdP Bhat A₂ A₁ A₀) i j < 1) ∧
    -- null recurrent or transient: `Ĝ` stochastic
    (¬ (∀ x : ℕ × ι, PositiveRecurrent (qbdP B A₀ A₁ A₂) x) →
      ∀ i, ∑' j, matG (qbdP Bhat A₂ A₁ A₀) i j = 1) ∧
    -- (8.28): `Ĝ` is a nonnegative solution and is minimal
    ((∀ i j, matG (qbdP Bhat A₂ A₁ A₀) i j ≠ ⊤) ∧
      matG (qbdP Bhat A₂ A₁ A₀) = ennMat A₀ + matMulE (ennMat A₁) (matG (qbdP Bhat A₂ A₁ A₀)) +
        matMulE (ennMat A₂) (matMulE (matG (qbdP Bhat A₂ A₁ A₀)) (matG (qbdP Bhat A₂ A₁ A₀))) ∧
      ∀ Y : ι → ι → ℝ, (∀ i j, 0 ≤ Y i j) →
        ennMat Y = ennMat A₀ + matMulE (ennMat A₁) (ennMat Y) +
          matMulE (ennMat A₂) (matMulE (ennMat Y) (ennMat Y)) →
        ∀ i j, matG (qbdP Bhat A₂ A₁ A₀) i j ≤ ennMat Y i j) ∧
    -- the spectral radius of `Ĝ` is strictly positive
    0 < spectralRadius ℂ
      (Matrix.of fun i j => (((matG (qbdP Bhat A₂ A₁ A₀) i j).toReal : ℝ) : ℂ))) := by
  intro h
  have H := h (ι := Fin 2) A3FK.B A3FK.A0 A3FK.A1 A3FK.A2 A3FK.P_stoch A3FK.P_irr (fun _ _ => 0)
  have hs := H.2.2.2.2.2.1 (fun hall => A3FK.P_notPR (hall _)) 1
  have hm := H.2.2.2.2.2.2.1.2.2 A3FK.Y A3FK.Y_nonneg A3FK.Y_sol
  rw [tsum_fintype, Fin.sum_univ_two] at hs
  have h0 := hm 1 0
  have h1 := hm 1 1
  simp [ennMat, A3FK.Y] at h0 h1
  rw [h0, zero_add] at hs
  rw [hs] at h1
  norm_num at h1

#print axioms solution
