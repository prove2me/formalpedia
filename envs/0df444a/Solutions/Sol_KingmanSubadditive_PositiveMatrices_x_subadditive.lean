-- Prove2me | solution 1 for KingmanSubadditive.PositiveMatrices.x_subadditive
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:11:06.501319+00:00
-- url     : https://prove2.me/submissions/48056de8-7978-498e-a29a-5ff42fd8f520

import Mathlib
import Definitions.Def_KingmanSubadditive_PositiveMatrices_Model
open MeasureTheory Filter Topology


namespace KingmanSubadditive.PositiveMatrices

/-! ### Elementary matrix facts -/

theorem pm_supermult_nonneg {k : ℕ} [NeZero k] (A B : Matrix (Fin k) (Fin k) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) :
    A 0 0 * B 0 0 ≤ (A * B) 0 0 := by
  rw [Matrix.mul_apply]
  have := Finset.single_le_sum (f := fun l => A 0 l * B l 0)
    (fun l _ => mul_nonneg (hA 0 l) (hB l 0)) (Finset.mem_univ (0 : Fin k))
  simpa using this

theorem pm_mul_nonneg {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) : ∀ i j, 0 ≤ (A * B) i j := by
  intro i j
  rw [Matrix.mul_apply]
  exact Finset.sum_nonneg (fun l _ => mul_nonneg (hA i l) (hB l j))

theorem pm_mul_pos {k : ℕ} [NeZero k] (A B : Matrix (Fin k) (Fin k) ℝ)
    (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) : ∀ i j, 0 < (A * B) i j := by
  intro i j
  rw [Matrix.mul_apply]
  exact Finset.sum_pos (fun l _ => mul_pos (hA i l) (hB l j)) Finset.univ_nonempty

theorem pm_one_nonneg {k : ℕ} : ∀ i j, (0 : ℝ) ≤ (1 : Matrix (Fin k) (Fin k) ℝ) i j := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs <;> norm_num

/-- `Bf A = ∑ |log A i j|`. -/
noncomputable def Bf {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  ∑ i, ∑ j, |Real.log (A i j)|

theorem Bf_nonneg {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) : 0 ≤ Bf A :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))

theorem abs_log_le_Bf {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (i j : Fin k) :
    |Real.log (A i j)| ≤ Bf A := by
  unfold Bf
  calc |Real.log (A i j)| ≤ ∑ j', |Real.log (A i j')| :=
        Finset.single_le_sum (f := fun j' => |Real.log (A i j')|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', |Real.log (A i' j')| :=
        Finset.single_le_sum (f := fun i' => ∑ j', |Real.log (A i' j')|)
          (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ i)

theorem entry_le_exp_Bf {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (hA : ∀ i j, 0 < A i j)
    (i j : Fin k) : A i j ≤ Real.exp (Bf A) := by
  rw [← Real.exp_log (hA i j)]
  exact Real.exp_le_exp.2 ((le_abs_self _).trans (abs_log_le_Bf A i j))

theorem exp_neg_Bf_le_entry {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (hA : ∀ i j, 0 < A i j)
    (i j : Fin k) : Real.exp (-Bf A) ≤ A i j := by
  rw [← Real.exp_log (hA i j)]
  apply Real.exp_le_exp.2
  have := abs_log_le_Bf A i j
  rw [abs_le] at this
  linarith [this.1]

/-! ### The row-sum norm -/

theorem rowSumNorm_nonneg {k : ℕ} [NeZero k] (A : Matrix (Fin k) (Fin k) ℝ) :
    0 ≤ rowSumNorm A := by
  unfold rowSumNorm
  exact le_trans (Finset.sum_nonneg (fun j _ => abs_nonneg (A 0 j)))
    (Finset.le_sup' (fun i => ∑ j, |A i j|) (Finset.mem_univ (0 : Fin k)))

theorem entry_le_rowSumNorm {k : ℕ} [NeZero k] (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (i j : Fin k) : A i j ≤ rowSumNorm A := by
  unfold rowSumNorm
  calc A i j = |A i j| := (abs_of_nonneg (hA i j)).symm
    _ ≤ ∑ j', |A i j'| := Finset.single_le_sum (f := fun j' => |A i j'|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ _ := Finset.le_sup' (fun i => ∑ j, |A i j|) (Finset.mem_univ i)

theorem rowSum_le_rowSumNorm {k : ℕ} [NeZero k] (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (i : Fin k) : ∑ j, A i j ≤ rowSumNorm A := by
  unfold rowSumNorm
  calc ∑ j, A i j = ∑ j, |A i j| := Finset.sum_congr rfl (fun j _ => (abs_of_nonneg (hA i j)).symm)
    _ ≤ _ := Finset.le_sup' (fun i => ∑ j, |A i j|) (Finset.mem_univ i)

theorem rowSumNorm_mul_le {k : ℕ} [NeZero k] (A B : Matrix (Fin k) (Fin k) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) :
    rowSumNorm (A * B) ≤ rowSumNorm A * rowSumNorm B := by
  unfold rowSumNorm
  apply Finset.sup'_le
  intro i _
  have hAB := pm_mul_nonneg A B hA hB
  calc ∑ j, |(A * B) i j| = ∑ j, ∑ l, A i l * B l j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_of_nonneg (hAB i j), Matrix.mul_apply]
    _ = ∑ l, A i l * ∑ j, B l j := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro l _
        rw [Finset.mul_sum]
    _ ≤ ∑ l, A i l * rowSumNorm B := by
        apply Finset.sum_le_sum
        intro l _
        exact mul_le_mul_of_nonneg_left (rowSum_le_rowSumNorm B hB l) (hA i l)
    _ = (∑ l, A i l) * rowSumNorm B := by rw [Finset.sum_mul]
    _ ≤ rowSumNorm A * rowSumNorm B :=
        mul_le_mul_of_nonneg_right (rowSum_le_rowSumNorm A hA i) (rowSumNorm_nonneg B)

theorem rowSumNorm_pos {k : ℕ} [NeZero k] (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : ∀ i j, 0 < A i j) : 0 < rowSumNorm A :=
  lt_of_lt_of_le (hA 0 0) (entry_le_rowSumNorm A (fun i j => (hA i j).le) 0 0)

theorem log_rowSumNorm_le {k : ℕ} [NeZero k] (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : ∀ i j, 0 < A i j) :
    Real.log (rowSumNorm A) ≤ Real.log ((k : ℝ) * k) + Bf A := by
  have hk : (0 : ℝ) < k := by
    have := NeZero.pos k
    exact_mod_cast this
  have h1 : rowSumNorm A ≤ ∑ i, ∑ j, A i j := by
    unfold rowSumNorm
    apply Finset.sup'_le
    intro i _
    calc ∑ j, |A i j| = ∑ j, A i j :=
          Finset.sum_congr rfl (fun j _ => abs_of_nonneg (hA i j).le)
      _ ≤ ∑ i, ∑ j, A i j := Finset.single_le_sum (f := fun i => ∑ j, A i j)
          (fun _ _ => Finset.sum_nonneg (fun _ _ => (hA _ _).le)) (Finset.mem_univ i)
  have h2 : ∑ i, ∑ j, A i j ≤ (k : ℝ) * k * Real.exp (Bf A) := by
    calc ∑ i, ∑ j, A i j ≤ ∑ i : Fin k, ∑ j : Fin k, Real.exp (Bf A) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => entry_le_exp_Bf A hA i j))
      _ = (k : ℝ) * k * Real.exp (Bf A) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          ring
  calc Real.log (rowSumNorm A) ≤ Real.log ((k : ℝ) * k * Real.exp (Bf A)) :=
        Real.log_le_log (rowSumNorm_pos A hA) (h1.trans h2)
    _ = Real.log ((k : ℝ) * k) + Bf A := by
        rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]

theorem neg_Bf_le_log_rowSumNorm {k : ℕ} [NeZero k] (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : ∀ i j, 0 < A i j) : -Bf A ≤ Real.log (rowSumNorm A) := by
  have h1 := abs_log_le_Bf A 0 0
  rw [abs_le] at h1
  have h2 : Real.log (A 0 0) ≤ Real.log (rowSumNorm A) :=
    Real.log_le_log (hA 0 0) (entry_le_rowSumNorm A (fun i j => (hA i j).le) 0 0)
  linarith [h1.1]

theorem abs_log_rowSumNorm_le {k : ℕ} [NeZero k] (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : ∀ i j, 0 < A i j) :
    |Real.log (rowSumNorm A)| ≤ Real.log ((k : ℝ) * k) + Bf A := by
  have hk : (1 : ℝ) ≤ (k : ℝ) * k := by
    have := NeZero.pos k
    have : (1 : ℝ) ≤ k := by exact_mod_cast this
    nlinarith
  have hlog : 0 ≤ Real.log ((k : ℝ) * k) := Real.log_nonneg hk
  rw [abs_le]
  constructor
  · linarith [neg_Bf_le_log_rowSumNorm A hA]
  · exact log_rowSumNorm_le A hA

/-! ### List products of matrices -/

theorem listProd_nonneg {k : ℕ} (M : List (Matrix (Fin k) (Fin k) ℝ))
    (hM : ∀ A ∈ M, ∀ i j, 0 ≤ A i j) : ∀ i j, 0 ≤ M.prod i j := by
  induction M with
  | nil => simpa using pm_one_nonneg
  | cons A L ih =>
    rw [List.prod_cons]
    exact pm_mul_nonneg A L.prod (hM A (by simp))
      (ih (fun C hC => hM C (List.mem_cons_of_mem _ hC)))

theorem listProd_pos {k : ℕ} [NeZero k] (M : List (Matrix (Fin k) (Fin k) ℝ))
    (hM : ∀ A ∈ M, ∀ i j, 0 < A i j) (hne : M ≠ []) : ∀ i j, 0 < M.prod i j := by
  induction M with
  | nil => exact absurd rfl hne
  | cons A L ih =>
    rcases L with _ | ⟨B, L'⟩
    · simpa using hM A (by simp)
    · rw [List.prod_cons]
      exact pm_mul_pos A _ (hM A (by simp))
        (ih (fun C hC => hM C (List.mem_cons_of_mem _ hC)) (by simp))

theorem listProd_00_ge {k : ℕ} [NeZero k] (M : List (Matrix (Fin k) (Fin k) ℝ))
    (hM : ∀ A ∈ M, ∀ i j, 0 ≤ A i j) : (M.map (fun A => A 0 0)).prod ≤ M.prod 0 0 := by
  induction M with
  | nil => simp
  | cons A L ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons]
    have ih' := ih (fun C hC => hM C (List.mem_cons_of_mem _ hC))
    calc A 0 0 * (L.map (fun A => A 0 0)).prod ≤ A 0 0 * L.prod 0 0 :=
          mul_le_mul_of_nonneg_left ih' (hM A (by simp) 0 0)
      _ ≤ (A * L.prod) 0 0 := pm_supermult_nonneg A L.prod (hM A (by simp))
          (listProd_nonneg L (fun C hC => hM C (List.mem_cons_of_mem _ hC)))

theorem log_rowSumNorm_listProd_le {k : ℕ} [NeZero k] (M : List (Matrix (Fin k) (Fin k) ℝ))
    (hM : ∀ A ∈ M, ∀ i j, 0 < A i j) (hne : M ≠ []) :
    Real.log (rowSumNorm M.prod) ≤ (M.map (fun A => Real.log (rowSumNorm A))).sum := by
  induction M with
  | nil => exact absurd rfl hne
  | cons A L ih =>
    rcases L with _ | ⟨B, L'⟩
    · simp
    · rw [List.prod_cons, List.map_cons, List.sum_cons]
      have hL : ∀ C ∈ B :: L', ∀ i j, 0 < C i j := fun C hC => hM C (List.mem_cons_of_mem _ hC)
      have ih' := ih hL (by simp)
      have hP := listProd_pos (B :: L') hL (by simp)
      have hA := hM A (by simp)
      calc Real.log (rowSumNorm (A * (B :: L').prod))
          ≤ Real.log (rowSumNorm A * rowSumNorm (B :: L').prod) :=
            Real.log_le_log (rowSumNorm_pos _ (pm_mul_pos A _ hA hP))
              (rowSumNorm_mul_le A _ (fun i j => (hA i j).le) (fun i j => (hP i j).le))
        _ = Real.log (rowSumNorm A) + Real.log (rowSumNorm (B :: L').prod) :=
            Real.log_mul (rowSumNorm_pos A hA).ne' (rowSumNorm_pos _ hP).ne'
        _ ≤ _ := by linarith

theorem neg_sum_Bf_le_log_listProd_00 {k : ℕ} [NeZero k] (M : List (Matrix (Fin k) (Fin k) ℝ))
    (hM : ∀ A ∈ M, ∀ i j, 0 < A i j) (hne : M ≠ []) :
    -(M.map Bf).sum ≤ Real.log (M.prod 0 0) := by
  induction M with
  | nil => exact absurd rfl hne
  | cons A L ih =>
    rcases L with _ | ⟨B, L'⟩
    · simp only [List.prod_cons, List.prod_nil, mul_one, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]
      have := abs_log_le_Bf A 0 0
      rw [abs_le] at this
      linarith [this.1]
    · rw [List.prod_cons, List.map_cons, List.sum_cons]
      have hL : ∀ C ∈ B :: L', ∀ i j, 0 < C i j := fun C hC => hM C (List.mem_cons_of_mem _ hC)
      have ih' := ih hL (by simp)
      have hP := listProd_pos (B :: L') hL (by simp)
      have hA := hM A (by simp)
      have h1 := abs_log_le_Bf A 0 0
      rw [abs_le] at h1
      calc -(Bf A + ((B :: L').map Bf).sum) = -Bf A + -((B :: L').map Bf).sum := by ring
        _ ≤ Real.log (A 0 0) + Real.log ((B :: L').prod 0 0) := by linarith [h1.1]
        _ = Real.log (A 0 0 * (B :: L').prod 0 0) :=
            (Real.log_mul (hA 0 0).ne' (hP 0 0).ne').symm
        _ ≤ Real.log ((A * (B :: L').prod) 0 0) :=
            Real.log_le_log (mul_pos (hA 0 0) (hP 0 0))
              (pm_supermult_nonneg A _ (fun i j => (hA i j).le) (fun i j => (hP i j).le))

/-! ### Block products -/

theorem blockProd_eq_list {Ω : Type*} {k : ℕ} (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ)
    (s t : ℕ) (ω : Ω) :
    blockProd Y s t ω = ((List.range' (s + 1) (t - s)).map (fun r => Y r ω)).prod := rfl

theorem blockProd_split {Ω : Type*} {k : ℕ} (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ)
    {s t u : ℕ} (hst : s ≤ t) (htu : t ≤ u) (ω : Ω) :
    blockProd Y s u ω = blockProd Y s t ω * blockProd Y t u ω := by
  simp only [blockProd_eq_list]
  rw [← List.prod_append, ← List.map_append]
  congr 2
  have h1 : u - s = (t - s) + (u - t) := by omega
  have h2 : t + 1 = s + 1 + (t - s) := by omega
  rw [h1]
  conv_rhs => rw [h2]
  exact List.range'_append_1.symm

theorem blockProd_succ_left {Ω : Type*} {k : ℕ} (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ)
    {s t : ℕ} (hst : s < t) (ω : Ω) :
    blockProd Y s t ω = Y (s + 1) ω * blockProd Y (s + 1) t ω := by
  simp only [blockProd_eq_list]
  have h : t - s = (t - (s + 1)) + 1 := by omega
  rw [h, List.range'_succ, List.map_cons, List.prod_cons]

theorem blockProd_self {Ω : Type*} {k : ℕ} (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ)
    (s : ℕ) (ω : Ω) : blockProd Y s s ω = 1 := by
  simp [blockProd_eq_list]

theorem blockProd_succ_right {Ω : Type*} {k : ℕ} (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ)
    {s t : ℕ} (hst : s < t) (ω : Ω) :
    blockProd Y s t ω = blockProd Y s (t - 1) ω * Y t ω := by
  rw [blockProd_split Y (show s ≤ t - 1 by omega) (show t - 1 ≤ t by omega),
    blockProd_succ_left Y (show t - 1 < t by omega), show t - 1 + 1 = t by omega,
    blockProd_self, mul_one]

theorem blockProd_pos {Ω : Type*} {k : ℕ} [NeZero k] (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ)
    (hY : ∀ n, 1 ≤ n → ∀ ω i j, 0 < Y n ω i j) {s t : ℕ} (hst : s < t) (ω : Ω) :
    ∀ i j, 0 < blockProd Y s t ω i j := by
  rw [blockProd_eq_list]
  apply listProd_pos
  · intro A hA
    rw [List.mem_map] at hA
    obtain ⟨r, hr, rfl⟩ := hA
    rw [List.mem_range'_1] at hr
    exact hY r (by omega) ω
  · intro h
    have := congrArg List.length h
    simp at this
    omega

theorem blockProd_nonneg {Ω : Type*} {k : ℕ} [NeZero k] (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ)
    (hY : ∀ n, 1 ≤ n → ∀ ω i j, 0 < Y n ω i j) (s t : ℕ) (ω : Ω) :
    ∀ i j, 0 ≤ blockProd Y s t ω i j := by
  rcases lt_or_ge s t with h | h
  · exact fun i j => (blockProd_pos Y hY h ω i j).le
  · rw [blockProd_eq_list, show t - s = 0 by omega]
    simpa using pm_one_nonneg

/-! ### Measurability of entries of list products -/

theorem measurable_listProd_entry {α : Type*} [MeasurableSpace α] {k : ℕ}
    (M : ℕ → α → Matrix (Fin k) (Fin k) ℝ) (L : List ℕ)
    (hM : ∀ r ∈ L, ∀ i j, Measurable (fun a => M r a i j)) :
    ∀ i j, Measurable (fun a => ((L.map (fun r => M r a)).prod) i j) := by
  induction L with
  | nil => intro i j; simp only [List.map_nil, List.prod_nil]; exact measurable_const
  | cons r L ih =>
    intro i j
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
    apply Finset.measurable_sum
    intro l _
    exact (hM r (by simp) i l).mul (ih (fun r' hr' => hM r' (List.mem_cons_of_mem _ hr')) l j)

theorem measurable_Bf {k : ℕ} : Measurable (fun A : Fin k → Fin k → ℝ => Bf A) := by
  unfold Bf
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  exact (Real.measurable_log.comp ((measurable_pi_apply j).comp (measurable_pi_apply i))).abs

theorem measurable_rowSumNorm {k : ℕ} [NeZero k] :
    Measurable (fun A : Fin k → Fin k → ℝ => rowSumNorm A) := by
  have : (fun A : Fin k → Fin k → ℝ => rowSumNorm A) =
      Finset.univ.sup' Finset.univ_nonempty (fun i (A : Fin k → Fin k → ℝ) => ∑ j, |A i j|) := by
    funext A
    rw [Finset.sup'_apply]
    rfl
  rw [this]
  apply Finset.measurable_sup'
  intro i _
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_pi_apply j).comp (measurable_pi_apply i)).abs

/-! ### The sequence-space picture -/

/-- The matrix sequence on path space: `Yσ r σ = σ (r-1)`. -/
def Yσ (k : ℕ) : ℕ → (ℕ → Fin k → Fin k → ℝ) → Matrix (Fin k) (Fin k) ℝ :=
  fun r σ => (σ (r - 1) : Matrix (Fin k) (Fin k) ℝ)

/-- `seq Y m ω n = Y (n+1+m) ω`. -/
def seq {Ω : Type*} {k : ℕ} (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (m : ℕ) (ω : Ω) :
    ℕ → Fin k → Fin k → ℝ :=
  fun n i j => Y (n + 1 + m) ω i j

theorem blockProd_shift {Ω : Type*} {k : ℕ} (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ)
    (m s t : ℕ) (ω : Ω) :
    blockProd Y (s + m) (t + m) ω = blockProd (Yσ k) s t (seq Y m ω) := by
  simp only [blockProd_eq_list]
  rw [Nat.add_sub_add_right, show s + m + 1 = m + (s + 1) by omega, ← List.map_add_range',
    List.map_map]
  congr 1
  apply List.map_congr_left
  intro r hr
  rw [List.mem_range'_1] at hr
  ext i j
  simp only [Function.comp, Yσ, seq]
  rw [show r - 1 + 1 + m = m + r by omega]

theorem x_shift {Ω : Type*} {k : ℕ} [NeZero k] (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ)
    (m s t : ℕ) (ω : Ω) :
    x Y (s + m) (t + m) ω = x (Yσ k) s t (seq Y m ω) := by
  unfold x z
  rw [blockProd_shift]

theorem measurable_seq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {k : ℕ}
    (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (hY : Hypotheses P Y) (m : ℕ) :
    Measurable (seq Y m) :=
  measurable_pi_lambda _ (fun n => hY.1 (n + 1 + m) (by omega))

theorem measurable_Yσ_entry {k : ℕ} (r : ℕ) (i j : Fin k) :
    Measurable (fun σ : ℕ → Fin k → Fin k → ℝ => Yσ k r σ i j) :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (measurable_pi_apply (r - 1)))

theorem measurable_x_Yσ {k : ℕ} [NeZero k] (s t : ℕ) :
    Measurable (fun σ : ℕ → Fin k → Fin k → ℝ => x (Yσ k) s t σ) := by
  unfold x z
  apply Measurable.neg
  apply Real.measurable_log.comp
  simp only [blockProd_eq_list]
  exact measurable_listProd_entry (Yσ k) _ (fun r _ i j => measurable_Yσ_entry r i j) 0 0

theorem measurable_path_Yσ {k : ℕ} [NeZero k] :
    Measurable (KingmanSubadditive.Ergodic.path (x (Yσ k))) :=
  measurable_pi_lambda _ (fun p => measurable_x_Yσ p.1.1 p.1.2)

theorem stat_shift {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {k : ℕ}
    (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (hY : Hypotheses P Y) (m : ℕ) :
    Measure.map (seq Y m) P = Measure.map (seq Y 0) P := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hst : Measure.map (seq Y 1) P = Measure.map (seq Y 0) P := hY.2.2.2
    let sh : (ℕ → Fin k → Fin k → ℝ) → (ℕ → Fin k → Fin k → ℝ) := fun σ n => σ (n + m)
    have hsh : Measurable sh := measurable_pi_lambda _ (fun n => measurable_pi_apply (n + m))
    have e1 : seq Y (m + 1) = sh ∘ seq Y 1 := by
      funext ω n i j
      simp only [Function.comp, seq, sh]
      rw [show n + 1 + (m + 1) = n + m + 1 + 1 by omega]
    have e2 : seq Y m = sh ∘ seq Y 0 := by
      funext ω n i j
      simp only [Function.comp, seq, sh]
      rw [show n + 1 + m = n + m + 1 + 0 by omega]
    rw [e1, ← Measure.map_map hsh (measurable_seq P Y hY 1), hst,
      Measure.map_map hsh (measurable_seq P Y hY 0), ← e2, ih]

theorem ident_dist {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {k : ℕ}
    (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (hY : Hypotheses P Y) {n : ℕ} (hn : 1 ≤ n) :
    Measure.map (fun ω (i j : Fin k) => Y n ω i j) P =
      Measure.map (fun ω (i j : Fin k) => Y 1 ω i j) P := by
  have h := stat_shift P Y hY (n - 1)
  have h2 := congrArg (Measure.map (fun σ : ℕ → Fin k → Fin k → ℝ => σ 0)) h
  rw [Measure.map_map (measurable_pi_apply 0) (measurable_seq P Y hY _),
    Measure.map_map (measurable_pi_apply 0) (measurable_seq P Y hY _)] at h2
  have e1 : (fun σ : ℕ → Fin k → Fin k → ℝ => σ 0) ∘ seq Y (n - 1) =
      fun ω (i j : Fin k) => Y n ω i j := by
    funext ω i j
    simp only [Function.comp, seq]
    rw [show 0 + 1 + (n - 1) = n by omega]
  have e2 : (fun σ : ℕ → Fin k → Fin k → ℝ => σ 0) ∘ seq Y 0 =
      fun ω (i j : Fin k) => Y 1 ω i j := by
    funext ω i j
    simp only [Function.comp, seq]
  rwa [e1, e2] at h2

theorem path_eq {Ω : Type*} {k : ℕ} [NeZero k] (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) :
    KingmanSubadditive.Ergodic.path (x Y) =
      KingmanSubadditive.Ergodic.path (x (Yσ k)) ∘ seq Y 0 := by
  funext ω p
  simp only [Function.comp, KingmanSubadditive.Ergodic.path]
  simpa using x_shift Y 0 p.1.1 p.1.2 ω

theorem shiftedPath_eq {Ω : Type*} {k : ℕ} [NeZero k] (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) :
    KingmanSubadditive.Ergodic.shiftedPath (x Y) =
      KingmanSubadditive.Ergodic.path (x (Yσ k)) ∘ seq Y 1 := by
  funext ω p
  simp only [Function.comp, KingmanSubadditive.Ergodic.path,
    KingmanSubadditive.Ergodic.shiftedPath, KingmanSubadditive.Ergodic.shift]
  exact x_shift Y 1 p.1.1 p.1.2 ω

theorem S2_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {k : ℕ} [NeZero k]
    (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (hY : Hypotheses P Y) :
    KingmanSubadditive.Ergodic.S2 P (x Y) := by
  unfold KingmanSubadditive.Ergodic.S2
  rw [path_eq, shiftedPath_eq, ← Measure.map_map measurable_path_Yσ (measurable_seq P Y hY 1),
    ← Measure.map_map measurable_path_Yσ (measurable_seq P Y hY 0), stat_shift P Y hY 1]

/-! ### Measurability and S1 of `x` -/

theorem measurable_x {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {k : ℕ} [NeZero k]
    (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (hY : Hypotheses P Y) (s t : ℕ) :
    Measurable (x Y s t) := by
  unfold x z
  apply Measurable.neg
  apply Real.measurable_log.comp
  simp only [blockProd_eq_list]
  apply measurable_listProd_entry Y _ _ 0 0
  intro r hr i j
  rw [List.mem_range'_1] at hr
  exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (hY.1 r (by omega)))

theorem S1_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {k : ℕ} [NeZero k]
    (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (hY : Hypotheses P Y) :
    KingmanSubadditive.Ergodic.S1 (x Y) := by
  intro s t u ω hst htu
  unfold x z
  have hpos := hY.2.1
  have h1 := blockProd_pos Y hpos hst ω 0 0
  have h2 := blockProd_pos Y hpos htu ω 0 0
  have h3 : blockProd Y s t ω 0 0 * blockProd Y t u ω 0 0 ≤ blockProd Y s u ω 0 0 := by
    rw [blockProd_split Y hst.le htu.le]
    exact pm_supermult_nonneg _ _ (blockProd_nonneg Y hpos s t ω) (blockProd_nonneg Y hpos t u ω)
  have h4 := Real.log_le_log (mul_pos h1 h2) h3
  rw [Real.log_mul h1.ne' h2.ne'] at h4
  linarith

/-! ### Integrability of `x` -/

theorem abs_x_le {Ω : Type*} {k : ℕ} [NeZero k] (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ)
    (hpos : ∀ n, 1 ≤ n → ∀ ω i j, 0 < Y n ω i j) {s t : ℕ} (hst : s < t) (ω : Ω) :
    |x Y s t ω| ≤ ((List.range' (s + 1) (t - s)).map
      (fun r => Real.log ((k : ℝ) * k) + Bf (Y r ω))).sum := by
  have hk : (1 : ℝ) ≤ (k : ℝ) * k := by
    have := NeZero.pos k
    have : (1 : ℝ) ≤ k := by exact_mod_cast this
    nlinarith
  have hlog : 0 ≤ Real.log ((k : ℝ) * k) := Real.log_nonneg hk
  set L := List.range' (s + 1) (t - s) with hL
  have hM : ∀ A ∈ L.map (fun r => Y r ω), ∀ i j, 0 < A i j := by
    intro A hA
    rw [List.mem_map] at hA
    obtain ⟨r, hr, rfl⟩ := hA
    rw [hL, List.mem_range'_1] at hr
    exact hpos r (by omega) ω
  have hne : L.map (fun r => Y r ω) ≠ [] := by
    intro h
    have := congrArg List.length h
    simp [hL] at this
    omega
  have hP := listProd_pos _ hM hne
  have hup := log_rowSumNorm_listProd_le _ hM hne
  have hlo := neg_sum_Bf_le_log_listProd_00 _ hM hne
  have hentry : Real.log ((L.map (fun r => Y r ω)).prod 0 0) ≤
      Real.log (rowSumNorm (L.map (fun r => Y r ω)).prod) :=
    Real.log_le_log (hP 0 0) (entry_le_rowSumNorm _ (fun i j => (hP i j).le) 0 0)
  have hsum1 : ((L.map (fun r => Y r ω)).map (fun A => Real.log (rowSumNorm A))).sum ≤
      (L.map (fun r => Real.log ((k : ℝ) * k) + Bf (Y r ω))).sum := by
    rw [List.map_map]
    apply List.sum_le_sum
    intro r hr
    rw [hL, List.mem_range'_1] at hr
    exact log_rowSumNorm_le _ (hpos r (by omega) ω)
  have hsum2 : ((L.map (fun r => Y r ω)).map Bf).sum ≤
      (L.map (fun r => Real.log ((k : ℝ) * k) + Bf (Y r ω))).sum := by
    rw [List.map_map]
    apply List.sum_le_sum
    intro r hr
    simp only [Function.comp]
    linarith
  unfold x z
  rw [blockProd_eq_list, abs_neg, abs_le]
  constructor
  · linarith
  · linarith

theorem integrable_Bf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {k : ℕ}
    (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (hY : Hypotheses P Y) {n : ℕ} (hn : 1 ≤ n) :
    Integrable (fun ω => Bf (Y n ω)) P := by
  unfold Bf
  apply integrable_finset_sum
  intro i _
  apply integrable_finset_sum
  intro j _
  exact (hY.2.2.1 n hn i j).abs

theorem integrable_list_sum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ) (L : List ℕ) (hf : ∀ r ∈ L, Integrable (f r) P) :
    Integrable (fun ω => (L.map (fun r => f r ω)).sum) P := by
  induction L with
  | nil => simp only [List.map_nil, List.sum_nil]; exact integrable_zero _ _ _
  | cons r L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hf r (by simp)).add (ih (fun r' hr' => hf r' (List.mem_cons_of_mem _ hr')))

theorem integral_list_sum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ) (L : List ℕ) (hf : ∀ r ∈ L, Integrable (f r) P) :
    ∫ ω, (L.map (fun r => f r ω)).sum ∂P = (L.map (fun r => ∫ ω, f r ω ∂P)).sum := by
  induction L with
  | nil => simp
  | cons r L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add (hf r (by simp))
      (integrable_list_sum P f L (fun r' hr' => hf r' (List.mem_cons_of_mem _ hr'))),
      ih (fun r' hr' => hf r' (List.mem_cons_of_mem _ hr'))]

theorem integrable_x {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} [NeZero k] (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (hY : Hypotheses P Y)
    {s t : ℕ} (hst : s < t) : Integrable (x Y s t) P := by
  have hb : Integrable (fun ω => ((List.range' (s + 1) (t - s)).map
      (fun r => Real.log ((k : ℝ) * k) + Bf (Y r ω))).sum) P := by
    apply integrable_list_sum P (fun r ω => Real.log ((k : ℝ) * k) + Bf (Y r ω))
    intro r hr
    rw [List.mem_range'_1] at hr
    exact (integrable_const _).add (integrable_Bf P Y hY (by omega))
  refine hb.mono' (measurable_x P Y hY s t).aestronglyMeasurable ?_
  exact ae_of_all _ (fun ω => by
    rw [Real.norm_eq_abs]
    exact abs_x_le Y hY.2.1 hst ω)

theorem integral_x_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} [NeZero k] (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (hY : Hypotheses P Y)
    {s t : ℕ} (hst : s < t) : ∫ ω, x Y s t ω ∂P = g P (x Y) (t - s) := by
  unfold g
  have e1 : x Y s t = fun ω => x (Yσ k) 0 (t - s) (seq Y s ω) := by
    funext ω
    have := x_shift Y s 0 (t - s) ω
    rwa [zero_add, Nat.sub_add_cancel hst.le] at this
  have e2 : x Y 0 (t - s) = fun ω => x (Yσ k) 0 (t - s) (seq Y 0 ω) := by
    funext ω
    have := x_shift Y 0 0 (t - s) ω
    simpa using this
  rw [e1, e2, ← integral_map (measurable_seq P Y hY s).aemeasurable
      (measurable_x_Yσ 0 (t - s)).aestronglyMeasurable,
    ← integral_map (measurable_seq P Y hY 0).aemeasurable
      (measurable_x_Yσ 0 (t - s)).aestronglyMeasurable, stat_shift P Y hY s]

theorem x_subadditive_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} [NeZero k] (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (hY : Hypotheses P Y) :
    (∀ s t : ℕ, s < t → Measurable (x Y s t)) ∧ KingmanSubadditive.Ergodic.S1 (x Y) ∧
    KingmanSubadditive.Ergodic.S2 P (x Y) ∧
    (∀ s t : ℕ, s < t → Integrable (x Y s t) P ∧ ∫ ω, x Y s t ω ∂P = g P (x Y) (t - s)) :=
  ⟨fun s t _ => measurable_x P Y hY s t, S1_core P Y hY, S2_core P Y hY,
    fun s t hst => ⟨integrable_x P Y hY hst, integral_x_eq P Y hY hst⟩⟩

end KingmanSubadditive.PositiveMatrices

open KingmanSubadditive.PositiveMatrices


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} [NeZero k] (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (hY : Hypotheses P Y) :
    (∀ s t : ℕ, s < t → Measurable (x Y s t)) ∧ KingmanSubadditive.Ergodic.S1 (x Y) ∧ KingmanSubadditive.Ergodic.S2 P (x Y) ∧
    (∀ s t : ℕ, s < t → Integrable (x Y s t) P ∧ ∫ ω, x Y s t ω ∂P = g P (x Y) (t - s)) := by
  exact x_subadditive_core P Y hY
