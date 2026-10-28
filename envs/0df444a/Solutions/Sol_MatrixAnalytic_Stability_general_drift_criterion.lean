-- Prove2me | solution 1 for MatrixAnalytic.Stability.general_drift_criterion
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-26T12:27:49.491863+00:00
-- url     : https://prove2.me/submissions/143a7ea8-3d29-4143-b6b8-cee89e4de6b7

import Mathlib
import Definitions.Def_MatrixAnalytic_Stability_Chain
import Definitions.Def_MatrixAnalytic_Stability_QBD
import Definitions.Def_MatrixAnalytic_Stability_Reducible

open scoped ENNReal

namespace MatrixAnalytic.Stability.A3GD

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

noncomputable def B : Fin 3 → Fin 3 → ℝ := ![![1/3, 1/3, 1/3], ![1/3, 0, 0], ![1/2, 0, 0]]
noncomputable def A0 : Fin 3 → Fin 3 → ℝ := ![![0, 0, 0], ![0, 2/3, 0], ![0, 0, 1/2]]
noncomputable def A1 : Fin 3 → Fin 3 → ℝ := ![![0, 0, 0], ![0, 0, 0], ![1/2, 0, 0]]
noncomputable def A2 : Fin 3 → Fin 3 → ℝ := ![![1, 0, 0], ![0, 1/3, 0], ![0, 0, 0]]

noncomputable abbrev P : ℕ × Fin 3 → ℕ × Fin 3 → ℝ := qbdP B A0 A1 A2

theorem P_nonneg (x y : ℕ × Fin 3) : 0 ≤ P x y := by
  obtain ⟨m, i⟩ := x
  obtain ⟨n, j⟩ := y
  simp only [P, qbdP]
  split_ifs <;> fin_cases i <;> fin_cases j <;> norm_num [B, A0, A1, A2]

theorem P_far (x y : ℕ × Fin 3) (h : x.1 + 1 < y.1) : P x y = 0 := by
  obtain ⟨m, i⟩ := x
  obtain ⟨n, j⟩ := y
  simp only at h
  simp only [P, qbdP]
  split_ifs <;> first | rfl | omega

theorem P_hasSum (x : ℕ × Fin 3) : HasSum (P x) 1 := by
  obtain ⟨n, i⟩ := x
  cases n with
  | zero =>
    have : HasSum (P (0, i))
        (∑ b ∈ ({0, 1} : Finset ℕ) ×ˢ (Finset.univ : Finset (Fin 3)), P (0, i) b) :=
      hasSum_sum_of_ne_finset_zero (by
        rintro ⟨m, j⟩ hy
        simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton,
          Finset.mem_univ, and_true, not_or] at hy
        simp [P, qbdP, hy.1, hy.2])
    convert this using 1
    rw [Finset.sum_product]
    fin_cases i <;> simp [Fin.sum_univ_three, P, qbdP, B, A0] <;> norm_num
  | succ n =>
    have : HasSum (P (n + 1, i))
        (∑ b ∈ ({n, n + 1, n + 2} : Finset ℕ) ×ˢ (Finset.univ : Finset (Fin 3)), P (n + 1, i) b) :=
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
    fin_cases i <;> simp [Fin.sum_univ_three, P, qbdP, A0, A1, A2, h1, h2, h3, h4] <;> norm_num

theorem P_stoch : IsStochasticC P := ⟨P_nonneg, P_hasSum⟩

/-! ### Irreducibility -/

theorem stepPow_succ' (t : ℕ) (x y : ℕ × Fin 3) :
    stepPow P (t + 1) x y = ∑' z, stepPow P t x z * P z y := rfl

theorem stepPow_nonneg (t : ℕ) (x y : ℕ × Fin 3) : 0 ≤ stepPow P t x y := by
  induction t generalizing y with
  | zero => simp only [stepPow]; split_ifs <;> norm_num
  | succ t ih =>
    rw [stepPow_succ']
    exact tsum_nonneg fun z => mul_nonneg (ih z) (P_nonneg z y)

theorem stepPow_supp (t : ℕ) (x z : ℕ × Fin 3) (h : x.1 + t < z.1) : stepPow P t x z = 0 := by
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

theorem step_pos (t : ℕ) (x z y : ℕ × Fin 3) (h1 : 0 < stepPow P t x z) (h2 : 0 < P z y) :
    0 < stepPow P (t + 1) x y := by
  rw [stepPow_succ']
  have hs : Summable fun w => stepPow P t x w * P w y := by
    apply summable_of_ne_finset_zero (s := (Finset.range (x.1 + t + 1)) ×ˢ Finset.univ)
    intro w hw
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true, not_lt] at hw
    rw [stepPow_supp t x w (by omega), zero_mul]
  exact hs.tsum_pos (fun w => mul_nonneg (stepPow_nonneg _ _ _) (P_nonneg _ _)) z
    (mul_pos h1 h2)

def R (x : ℕ × Fin 3) : Set (ℕ × Fin 3) := {y | ∃ t, 0 < stepPow P t x y}

theorem R_self (x : ℕ × Fin 3) : x ∈ R x := ⟨0, by simp [stepPow]⟩

theorem R_edge {x y z : ℕ × Fin 3} (hy : y ∈ R x) (h : 0 < P y z) : z ∈ R x := by
  obtain ⟨t, ht⟩ := hy
  exact ⟨t + 1, step_pos t x y z ht h⟩

theorem R_down {x : ℕ × Fin 3} (i : Fin 3) (he : ∀ k, 0 < P (k + 1, i) (k, i)) :
    ∀ k, (k, i) ∈ R x → ((0 : ℕ), i) ∈ R x := by
  intro k
  induction k with
  | zero => exact id
  | succ k ih => exact fun h => ih (R_edge h (he k))

theorem R_up {x : ℕ × Fin 3} (i : Fin 3) (he : ∀ k, 0 < P (k, i) (k + 1, i)) :
    ((0 : ℕ), i) ∈ R x → ∀ k, (k, i) ∈ R x := by
  intro h k
  induction k with
  | zero => exact h
  | succ k ih => exact R_edge ih (he k)

theorem e1 (k : ℕ) : 0 < P (k + 1, 0) (k, 0) := by
  have : k ≠ k + 1 + 1 := by omega
  have : k ≠ k + 1 := by omega
  simp [P, qbdP, A2, *]
theorem e2 (k : ℕ) : 0 < P (k + 1, 1) (k, 1) := by
  have : k ≠ k + 1 + 1 := by omega
  have : k ≠ k + 1 := by omega
  simp [P, qbdP, A2, *]
theorem e3 (k : ℕ) : 0 < P (k + 1, 2) (k + 1, 0) := by
  have : k + 1 ≠ k + 1 + 1 := by omega
  simp [P, qbdP, A1, *]
theorem e4 : 0 < P (0, 1) (0, 0) := by simp [P, qbdP, B]
theorem e5 : 0 < P (0, 2) (0, 0) := by simp [P, qbdP, B]
theorem e6 : 0 < P (0, 0) (0, 1) := by simp [P, qbdP, B]
theorem e7 : 0 < P (0, 0) (0, 2) := by simp [P, qbdP, B]
theorem e8 (k : ℕ) : 0 < P (k, 1) (k + 1, 1) := by
  cases k <;> simp [P, qbdP, A0]
theorem e9 (k : ℕ) : 0 < P (k, 2) (k + 1, 2) := by
  cases k <;> simp [P, qbdP, A0]

theorem P_irr : IrreducibleC P := by
  intro x y
  have h0 : ((0 : ℕ), (0 : Fin 3)) ∈ R x := by
    obtain ⟨n, i⟩ := x
    fin_cases i
    · exact R_down 0 e1 n (R_self _)
    · exact R_edge (R_down 1 e2 n (R_self _)) e4
    · cases n with
      | zero => exact R_edge (R_self _) e5
      | succ n => exact R_down 0 e1 (n + 1) (R_edge (R_self _) (e3 n))
  show y ∈ R x
  obtain ⟨m, j⟩ := y
  fin_cases j
  · cases m with
    | zero => exact h0
    | succ m => exact R_edge (R_up 2 e9 (R_edge h0 e7) (m + 1)) (e3 m)
  · exact R_up 1 e8 (R_edge h0 e6) m
  · exact R_up 2 e9 (R_edge h0 e7) m

/-! ### Transience of the phase-1 escape -/

def x0 : ℕ × Fin 3 := (0, 1)

theorem memA (k : ℕ) (i : Fin 3) : (k, i) ∈ ({x0} : Set (ℕ × Fin 3)) ↔ k = 0 ∧ i = 1 := by
  simp [x0]

theorem Pup (k : ℕ) : P (k + 1, 1) (k + 2, 1) = 2 / 3 := by
  simp [P, qbdP, A0]
theorem Pdn (j : ℕ) : P (j + 2, 1) (j + 1, 1) = 1 / 3 := by
  have : j + 1 ≠ j + 2 + 1 := by omega
  have : j + 1 ≠ j + 2 := by omega
  simp [P, qbdP, A2, *]
theorem P0 : P x0 (1, 1) = 2 / 3 := by simp [P, qbdP, A0, x0]

open Classical in
theorem lower (t k : ℕ) :
    ENNReal.ofReal (1 - (1 / 2) ^ (k + 1)) ≤ E P {x0} t (k + 1, 1) := by
  induction t generalizing k with
  | zero => rw [E_zero]; exact ENNReal.ofReal_le_of_le_toReal (by simp)
  | succ t ih =>
    rw [E_succ P P_nonneg]
    cases k with
    | zero =>
      refine le_trans ?_ (ENNReal.le_tsum ((2 : ℕ), (1 : Fin 3)))
      have hn : ((2 : ℕ), (1 : Fin 3)) ∉ ({x0} : Set (ℕ × Fin 3)) := by simp [x0]
      rw [if_neg hn, show ((0 : ℕ) + 1, (1 : Fin 3)) = (0 + 1, 1) from rfl, Pup 0]
      calc ENNReal.ofReal (1 - (1 / 2) ^ (0 + 1))
          = ENNReal.ofReal (2 / 3) * ENNReal.ofReal (1 - (1 / 2) ^ (1 + 1)) := by
            rw [← ENNReal.ofReal_mul (by norm_num)]; norm_num
        _ ≤ ENNReal.ofReal (2 / 3) * E P {x0} t (1 + 1, 1) := by gcongr; exact ih 1
    | succ j =>
      have hne : ((j + 3 : ℕ), (1 : Fin 3)) ≠ (j + 1, 1) := by simp
      refine le_trans ?_ (ENNReal.sum_le_tsum {((j + 3 : ℕ), (1 : Fin 3)), (j + 1, 1)})
      rw [Finset.sum_pair hne]
      have hn1 : ((j + 3 : ℕ), (1 : Fin 3)) ∉ ({x0} : Set (ℕ × Fin 3)) := by simp [x0]
      have hn2 : ((j + 1 : ℕ), (1 : Fin 3)) ∉ ({x0} : Set (ℕ × Fin 3)) := by simp [x0]
      rw [if_neg hn1, if_neg hn2, show j + 3 = (j + 1) + 2 from rfl, Pup (j + 1), Pdn j]
      calc ENNReal.ofReal (1 - (1 / 2) ^ (j + 1 + 1))
          = ENNReal.ofReal (2 / 3) * ENNReal.ofReal (1 - (1 / 2) ^ ((j + 2) + 1)) +
            ENNReal.ofReal (1 / 3) * ENNReal.ofReal (1 - (1 / 2) ^ (j + 1)) := by
            rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
              ← ENNReal.ofReal_add (by
                have : (1 / 2 : ℝ) ^ (j + 2 + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
                nlinarith) (by
                have : (1 / 2 : ℝ) ^ (j + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
                nlinarith)]
            congr 1; ring
        _ ≤ ENNReal.ofReal (2 / 3) * E P {x0} t (j + 1 + 2, 1) +
            ENNReal.ofReal (1 / 3) * E P {x0} t (j + 1, 1) := by
            gcongr
            · exact ih (j + 2)
            · exact ih j

theorem not_rec : ¬ Recurrent P x0 := by
  intro h
  have hb : ∀ t, (1 / 3 : ℝ) ≤ returnTailC P x0 (t + 1) := by
    intro t
    classical
    unfold returnTailC
    rw [toReal_E P P_nonneg]
    rw [← ENNReal.ofReal_le_iff_le_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top
      (E_le_one P P_stoch _ _ _)), E_succ P P_nonneg]
    refine le_trans ?_ (ENNReal.le_tsum ((1 : ℕ), (1 : Fin 3)))
    have hn : ((1 : ℕ), (1 : Fin 3)) ∉ ({x0} : Set (ℕ × Fin 3)) := by simp [x0]
    rw [if_neg hn, P0]
    calc ENNReal.ofReal (1 / 3)
        = ENNReal.ofReal (2 / 3) * ENNReal.ofReal (1 - (1 / 2) ^ (0 + 1)) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]; norm_num
      _ ≤ _ := by gcongr; exact lower t 0
  have := ge_of_tendsto h (Filter.eventually_atTop.2 ⟨1, fun t ht => by
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    exact hb s⟩)
  norm_num at this

def φ : Fin 3 → Option (Fin 1) := fun i => if i = 0 then some 0 else none

def γ : Fin 1 → Fin 3 → ℝ := fun _ i => if i = 0 then 1 else 0

theorem φ_some (i : Fin 3) (k : Fin 1) : φ i = some k ↔ i = 0 := by
  fin_cases i <;> fin_cases k <;> simp [φ]

theorem hform : IsBlockForm711 (matA A0 A1 A2) φ := by
  refine ⟨fun k => ⟨0, by fin_cases k; simp [φ]⟩, ?_, ?_⟩
  · intro k i j hi hj
    rw [φ_some] at hi
    rw [Ne, φ_some] at hj
    subst hi
    fin_cases j
    · exact absurd rfl hj
    · simp [matA, A0, A1, A2]
    · simp [matA, A0, A1, A2]
  · intro k x y
    refine ⟨0, ?_⟩
    have hx := (φ_some _ _).mp x.2
    have hy := (φ_some _ _).mp y.2
    have : y = x := Subtype.ext (hy.trans hx.symm)
    simp [stepPow, this]

theorem hD : (∃ i : Fin 3, φ i = none) →
    ∃ i : Fin 3, φ i = none ∧
      ∑ j ∈ Finset.univ.filter (fun j => φ j = none), matA A0 A1 A2 i j < 1 := by
  intro _
  refine ⟨2, by simp [φ], ?_⟩
  rw [Finset.sum_filter]
  simp [Fin.sum_univ_three, φ, matA, A0, A1, A2]
  norm_num

theorem hγ : ∀ k : Fin 1, IsClassStationary (matA A0 A1 A2) φ k (γ k) := by
  intro k
  fin_cases k
  refine ⟨fun i hi => ?_, fun i => ?_, ?_, fun j hj => ?_⟩
  · have : i ≠ 0 := fun h => hi ((φ_some i 0).mpr h)
    simp [γ, this]
  · simp only [γ]; split_ifs <;> norm_num
  · simp [γ, Fin.sum_univ_three]
  · have hj' := (φ_some j 0).mp hj
    subst hj'
    rw [Finset.sum_filter]
    simp [Fin.sum_univ_three, φ, γ, matA, A0, A1, A2]

theorem rates : ∀ k : Fin 1, classRate A0 φ k (γ k) ≤ classRate A2 φ k (γ k) := by
  intro k
  fin_cases k
  simp only [classRate, Finset.sum_filter]
  simp [Fin.sum_univ_three, φ, γ, A0, A2]

end concrete

end MatrixAnalytic.Stability.A3GD

open MatrixAnalytic.Stability in
theorem solution : ¬ (∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (K : ℕ) (hK : 1 ≤ K) (φ : ι → Option (Fin K))
    (hform : IsBlockForm711 (matA A₀ A₁ A₂) φ)
    (hD : (∃ i : ι, φ i = none) →
      ∃ i : ι, φ i = none ∧
        ∑ j ∈ Finset.univ.filter (fun j => φ j = none), matA A₀ A₁ A₂ i j < 1)
    (γ : Fin K → ι → ℝ) (hγ : ∀ k : Fin K, IsClassStationary (matA A₀ A₁ A₂) φ k (γ k)),
    (IsRecurrentChain (qbdP B A₀ A₁ A₂) ↔
      ∀ k : Fin K, classRate A₀ φ k (γ k) ≤ classRate A₂ φ k (γ k)) ∧
    (IsPositiveRecurrentChain (qbdP B A₀ A₁ A₂) ↔
      ∀ k : Fin K, classRate A₀ φ k (γ k) < classRate A₂ φ k (γ k)) ∧
    (IsTransientChain (qbdP B A₀ A₁ A₂) ↔
      ∃ k : Fin K, classRate A₂ φ k (γ k) < classRate A₀ φ k (γ k))) := by
  intro h
  have := (h (ι := Fin 3) A3GD.B A3GD.A0 A3GD.A1 A3GD.A2 A3GD.P_stoch A3GD.P_irr 1 le_rfl
    A3GD.φ A3GD.hform A3GD.hD A3GD.γ A3GD.hγ).1.mpr A3GD.rates
  exact A3GD.not_rec (this A3GD.x0)

