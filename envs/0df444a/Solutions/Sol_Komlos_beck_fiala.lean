-- Prove2me | solution 1 for Komlos.beck_fiala
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:08:28.50028+00:00
-- url     : https://prove2.me/submissions/61661b6f-30c8-4f10-a962-2eb48efa7796

import Mathlib
import Definitions.Def_Komlos_model

/-!
# Beck–Fiala 1981 — skeleton for the Prove2me target `Komlos.beck_fiala`

Target (verbatim from the platform; `IsSignVector` is `Komlos.IsSignVector` from `Definitions.Def_Komlos_model`):

  theorem beck_fiala (t n m : ℕ) (ht : 1 ≤ t) (A : Fin m → Fin n → ℝ)
      (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
      (hdeg : ∀ j, ({i | A i j = 1} : Finset (Fin m)).card ≤ t) :
      ∃ ε : Fin n → ℝ, IsSignVector ε ∧
        ∀ i, |∑ j, A i j * ε j| ≤ 2 * (t : ℝ) - 1

## The argument (floating colours), made state-only

Maintain `x : Fin n → ℝ` with `|x j| ≤ 1`.  Coordinate `j` is *floating* if `|x j| < 1`, else *fixed*.
For a row `i`, `rowFloat A x i` is the set of floating `j` with `A i j = 1`, and `fixedSum A x i` is the
sum of the fixed `x j` with `A i j = 1`.  Row `i` is *active* if it has more than `t` floating entries.

Invariant `Inv t A x`:
  (bound)    ∀ j, |x j| ≤ 1
  (active)   ∀ i, t < #(rowFloat A x i) → ∑ j, A i j * x j = 0
  (inactive) ∀ i, #(rowFloat A x i) ≤ t → |fixedSum A x i| < 2t - #(rowFloat A x i)

* `x = 0` satisfies `Inv` (`inv_zero`).
* Step (`inv_step`): if some coordinate floats, there is `x'` with `Inv t A x'` and strictly fewer floating
  coordinates.  Proof: with `F` = floating set and `R` = active rows, double counting gives
  `#R * (t+1) ≤ #F * t`, hence `#R < #F` (`card_active_lt`).  So the linear map `y ↦ (∑ j∈F, A i j * y j)_{i∈R}`
  has a nonzero kernel element `y` supported on `F` (`exists_kernel_vector`).  Moving along `y` until the
  first floating coordinate hits `±1` (`exists_line_hit`) gives `x' = x + λ • y`, and `inv_preserved` checks
  the invariant.
* Induction on the number of floating coordinates (`exists_sign_of_inv`) ends with a sign vector `ε`; every
  row is then inactive with no floating entries, so `|∑ j, A i j * ε j| < 2t`; the sum is an integer
  (`row_sum_is_int`), hence `≤ 2t - 1`.
-/

namespace Komlos

noncomputable section

open Finset

variable {m n : ℕ}

/-- Floating coordinates of `x`. -/
def floating (x : Fin n → ℝ) : Finset (Fin n) := univ.filter (fun j => |x j| < 1)

/-- Floating coordinates lying in row `i` (where `A i j = 1`). -/
def rowFloat (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin m) : Finset (Fin n) :=
  univ.filter (fun j => A i j = 1 ∧ |x j| < 1)

/-- Sum of the fixed coordinates in row `i`. -/
def fixedSum (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin m) : ℝ :=
  ∑ j ∈ univ.filter (fun j => A i j = 1 ∧ ¬ |x j| < 1), x j

/-- Active rows: more than `t` floating entries. -/
def activeRows (t : ℕ) (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Finset (Fin m) :=
  univ.filter (fun i => t < (rowFloat A x i).card)

/-- The invariant of the floating-colours process. -/
structure Inv (t : ℕ) (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : Prop where
  bound : ∀ j, |x j| ≤ 1
  active : ∀ i, t < (rowFloat A x i).card → ∑ j, A i j * x j = 0
  inactive : ∀ i, (rowFloat A x i).card ≤ t →
    |fixedSum A x i| < 2 * (t : ℝ) - ((rowFloat A x i).card : ℝ)

/-! ### Basic bookkeeping -/

/-- With 0/1 entries, a row sum splits into its fixed part and its floating part. -/
lemma row_sum_split (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (i : Fin m) :
    ∑ j, A i j * x j = fixedSum A x i + ∑ j ∈ rowFloat A x i, x j := by
  unfold fixedSum rowFloat
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rcases h01 i j with h | h
  · simp [h]
  · by_cases hx : |x j| < 1
    · simp [h, hx]
    · simp [h, hx]

/-- The floating set of row `i` is `#(rowFloat A x i) = ∑ j ∈ floating x, A i j` when entries are 0/1. -/
lemma card_rowFloat_eq_sum (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) (i : Fin m) :
    ((rowFloat A x i).card : ℝ) = ∑ j ∈ floating x, A i j := by
  unfold rowFloat floating
  rw [Finset.card_filter, Finset.sum_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rcases h01 i j with h | h
  · by_cases hx : |x j| < 1 <;> simp [h, hx]
  · by_cases hx : |x j| < 1 <;> simp [h, hx]

/-! ### L1: the initial state -/

lemma inv_zero (t : ℕ) (ht : 1 ≤ t) (A : Fin m → Fin n → ℝ) : Inv t A (fun _ => 0) := by
  refine ⟨fun j => ?_, fun i _ => ?_, fun i hi => ?_⟩
  · simp
  · simp
  · have h1 : fixedSum A (fun _ => 0) i = 0 := by simp [fixedSum]
    have hcard : ((rowFloat A (fun _ => 0) i).card : ℝ) ≤ (t : ℝ) := by exact_mod_cast hi
    have ht' : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    rw [h1, abs_zero]
    linarith

/-! ### L2: counting — fewer active rows than floating coordinates -/

lemma card_active_lt (t : ℕ) (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hdeg : ∀ j, ({i | A i j = 1} : Finset (Fin m)).card ≤ t)
    (hne : (floating x).Nonempty) :
    (activeRows t A x).card < (floating x).card := by
  -- Step 1: each active row has at least `t + 1` floating entries.
  have h1 : ((activeRows t A x).card : ℝ) * ((t : ℝ) + 1)
      ≤ ∑ i ∈ activeRows t A x, ((rowFloat A x i).card : ℝ) := by
    have hrow : ∀ i ∈ activeRows t A x, ((t : ℝ) + 1) ≤ ((rowFloat A x i).card : ℝ) := by
      intro i hi
      simp only [activeRows, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have hi' : t + 1 ≤ (rowFloat A x i).card := hi
      exact_mod_cast hi'
    calc ((activeRows t A x).card : ℝ) * ((t : ℝ) + 1)
        = ∑ _i ∈ activeRows t A x, ((t : ℝ) + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ activeRows t A x, ((rowFloat A x i).card : ℝ) := Finset.sum_le_sum hrow
  -- Step 2: double counting.
  have h2 : ∑ i ∈ activeRows t A x, ((rowFloat A x i).card : ℝ)
      = ∑ j ∈ floating x, ∑ i ∈ activeRows t A x, A i j := by
    calc ∑ i ∈ activeRows t A x, ((rowFloat A x i).card : ℝ)
        = ∑ i ∈ activeRows t A x, ∑ j ∈ floating x, A i j :=
          Finset.sum_congr rfl (fun i _ => card_rowFloat_eq_sum A x h01 i)
      _ = ∑ j ∈ floating x, ∑ i ∈ activeRows t A x, A i j := Finset.sum_comm
  -- Step 3: entries are nonnegative, so a partial column sum is at most the full column sum.
  have h3 : ∀ j, ∑ i ∈ activeRows t A x, A i j ≤ ∑ i, A i j := by
    intro j
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro i _ _
    rcases h01 i j with h | h <;> linarith
  -- Step 4: a full column sum is the number of ones in that column.
  have h4 : ∀ j, ∑ i, A i j = (({i | A i j = 1} : Finset (Fin m)).card : ℝ) := by
    intro j
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rcases h01 i j with h | h <;> simp [h]
  -- Step 5: combine into `#R * (t + 1) ≤ #F * t`.
  have h5 : ((activeRows t A x).card : ℝ) * ((t : ℝ) + 1) ≤ ((floating x).card : ℝ) * t := by
    calc ((activeRows t A x).card : ℝ) * ((t : ℝ) + 1)
        ≤ ∑ i ∈ activeRows t A x, ((rowFloat A x i).card : ℝ) := h1
      _ = ∑ j ∈ floating x, ∑ i ∈ activeRows t A x, A i j := h2
      _ ≤ ∑ j ∈ floating x, ∑ i, A i j := Finset.sum_le_sum (fun j _ => h3 j)
      _ = ∑ j ∈ floating x, (({i | A i j = 1} : Finset (Fin m)).card : ℝ) :=
          Finset.sum_congr rfl (fun j _ => h4 j)
      _ ≤ ∑ _j ∈ floating x, (t : ℝ) := Finset.sum_le_sum (fun j _ => by exact_mod_cast hdeg j)
      _ = ((floating x).card : ℝ) * t := by rw [Finset.sum_const, nsmul_eq_mul]
  -- Step 6: conclude in ℕ.
  have h5' : (activeRows t A x).card * (t + 1) ≤ (floating x).card * t := by exact_mod_cast h5
  have hFpos : 0 < (floating x).card := hne.card_pos
  have h6 : (activeRows t A x).card * (t + 1) < (floating x).card * (t + 1) := by
    calc (activeRows t A x).card * (t + 1) ≤ (floating x).card * t := h5'
      _ < (floating x).card * t + (floating x).card := Nat.lt_add_of_pos_right hFpos
      _ = (floating x).card * (t + 1) := by ring
  exact lt_of_mul_lt_mul_right h6 (Nat.zero_le _)

/-! ### L3: linear algebra — a nonzero vector supported on `F` killed by the rows in `R` -/

lemma exists_kernel_vector (A : Fin m → Fin n → ℝ) (F : Finset (Fin n)) (R : Finset (Fin m))
    (hlt : R.card < F.card) :
    ∃ y : Fin n → ℝ, y ≠ 0 ∧ (∀ j, j ∉ F → y j = 0) ∧ ∀ i ∈ R, ∑ j, A i j * y j = 0 := by
  classical
  -- the submatrix indexed by `R × F` and the associated linear map `(F → ℝ) → (R → ℝ)`
  let M : Matrix (↥R) (↥F) ℝ := Matrix.of fun (i : ↥R) (j : ↥F) => A i j
  let f : (↥F → ℝ) →ₗ[ℝ] (↥R → ℝ) := Matrix.mulVecLin M
  have hrank : Module.finrank ℝ (↥R → ℝ) < Module.finrank ℝ (↥F → ℝ) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe, Fintype.card_coe]
    exact hlt
  have hker : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hrank
  obtain ⟨y₀, hy₀mem, hy₀ne⟩ := (Submodule.ne_bot_iff _).mp hker
  have hy₀ : M.mulVec y₀ = 0 := LinearMap.mem_ker.mp hy₀mem
  refine ⟨fun j => if h : j ∈ F then y₀ ⟨j, h⟩ else 0, ?_, ?_, ?_⟩
  · -- nonzero
    intro hy
    apply hy₀ne
    funext ⟨j, hj⟩
    have h2 := congrFun hy j
    simpa [hj] using h2
  · -- support in `F`
    intro j hj
    simp [hj]
  · -- killed by the rows of `R`
    intro i hi
    have h1 : ∑ j : ↥F, A i j * y₀ j = 0 := by
      have h2 := congrFun hy₀ ⟨i, hi⟩
      simpa [M, Matrix.mulVec, dotProduct] using h2
    calc ∑ j, A i j * (if h : j ∈ F then y₀ ⟨j, h⟩ else 0)
        = ∑ j ∈ F, A i j * (if h : j ∈ F then y₀ ⟨j, h⟩ else 0) := by
          symm
          apply Finset.sum_subset (Finset.subset_univ F)
          intro j _ hj
          simp [hj]
      _ = ∑ j : ↥F, A i j * (if h : (j : Fin n) ∈ F then y₀ ⟨j, h⟩ else 0) := by
          rw [Finset.sum_coe_sort F (fun j => A i j * (if h : j ∈ F then y₀ ⟨j, h⟩ else 0))]
      _ = ∑ j : ↥F, A i j * y₀ j := by
          apply Finset.sum_congr rfl
          intro j _
          simp [j.2]
      _ = 0 := h1

/-! ### L4: line search — move along `y` until a floating coordinate hits `±1` -/

lemma exists_line_hit (x y : Fin n → ℝ) (hx : ∀ j, |x j| ≤ 1) (hy : y ≠ 0)
    (hsupp : ∀ j, y j ≠ 0 → |x j| < 1) :
    ∃ l : ℝ, (∀ j, |x j + l * y j| ≤ 1) ∧ ∃ j, y j ≠ 0 ∧ |x j + l * y j| = 1 := by
  classical
  -- the support of `y`
  set S : Finset (Fin n) := univ.filter (fun j => y j ≠ 0) with hS_def
  have hmemS : ∀ j, j ∈ S ↔ y j ≠ 0 := by
    intro j
    simp [hS_def]
  have hS : S.Nonempty := by
    obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := Function.ne_iff.mp hy
    exact ⟨j, (hmemS j).2 hj⟩
  -- the step at which coordinate `j` hits `±1`
  set r : Fin n → ℝ := fun j => if 0 < y j then (1 - x j) / y j else (-1 - x j) / y j with hr_def
  have hr_pos : ∀ j ∈ S, 0 < r j := by
    intro j hj
    have hyj : y j ≠ 0 := (hmemS j).1 hj
    have hxj := hsupp j hyj
    rw [abs_lt] at hxj
    simp only [hr_def]
    split_ifs with h
    · exact div_pos (by linarith) h
    · have hneg : y j < 0 := lt_of_le_of_ne (not_lt.mp h) hyj
      exact div_pos_of_neg_of_neg (by linarith) hneg
  obtain ⟨j₀, hj₀S, hj₀⟩ := Finset.exists_mem_eq_inf' hS r
  set l : ℝ := S.inf' hS r with hl_def
  have hl_pos : 0 < l := by
    rw [hj₀]
    exact hr_pos j₀ hj₀S
  have hl_le : ∀ j ∈ S, l ≤ r j := fun j hj => Finset.inf'_le r hj
  refine ⟨l, ?_, ?_⟩
  · intro j
    by_cases hyj : y j = 0
    · rw [hyj, mul_zero, add_zero]
      exact hx j
    · have hjS : j ∈ S := (hmemS j).2 hyj
      have hxj := hsupp j hyj
      rw [abs_lt] at hxj
      have hle := hl_le j hjS
      simp only [hr_def] at hle
      rw [abs_le]
      split_ifs at hle with h
      · rw [le_div_iff₀ h] at hle
        have hpos : 0 < l * y j := mul_pos hl_pos h
        constructor
        · linarith
        · linarith
      · have hneg : y j < 0 := lt_of_le_of_ne (not_lt.mp h) hyj
        rw [le_div_iff_of_neg hneg] at hle
        have hneg' : l * y j < 0 := mul_neg_of_pos_of_neg hl_pos hneg
        constructor
        · linarith
        · linarith
  · refine ⟨j₀, (hmemS j₀).1 hj₀S, ?_⟩
    have hyj : y j₀ ≠ 0 := (hmemS j₀).1 hj₀S
    rw [hj₀]
    simp only [hr_def]
    split_ifs with h
    · have : (1 - x j₀) / y j₀ * y j₀ = 1 - x j₀ := div_mul_cancel₀ _ (ne_of_gt h)
      rw [this]
      simp
    · have : (-1 - x j₀) / y j₀ * y j₀ = -1 - x j₀ := div_mul_cancel₀ _ hyj
      rw [this]
      norm_num

/-! ### L5: the invariant is preserved by one step -/

private lemma bf4_mem_floating (x : Fin n → ℝ) (j : Fin n) : j ∈ floating x ↔ |x j| < 1 := by
  simp only [floating, Finset.mem_filter, Finset.mem_univ, true_and]

private lemma bf4_mem_rowFloat (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin m) (j : Fin n) :
    j ∈ rowFloat A x i ↔ A i j = 1 ∧ |x j| < 1 := by
  simp only [rowFloat, Finset.mem_filter, Finset.mem_univ, true_and]

/-- (F1) Off the floating set the step does nothing. -/
private lemma bf4_eq_of_not_floating (x y : Fin n → ℝ) (l : ℝ)
    (hsupp : ∀ j, j ∉ floating x → y j = 0) (j : Fin n) (hj : ¬ |x j| < 1) :
    x j + l * y j = x j := by
  have hy : y j = 0 := hsupp j (fun h => hj ((bf4_mem_floating x j).mp h))
  rw [hy, mul_zero, add_zero]

private lemma bf4_floating_subset (x y : Fin n → ℝ) (l : ℝ)
    (hsupp : ∀ j, j ∉ floating x → y j = 0) :
    floating (fun j => x j + l * y j) ⊆ floating x := by
  intro j hj
  simp only [bf4_mem_floating] at hj ⊢
  by_contra h
  rw [bf4_eq_of_not_floating x y l hsupp j h] at hj
  exact h hj

private lemma bf4_rowFloat_subset (A : Fin m → Fin n → ℝ) (x y : Fin n → ℝ) (l : ℝ)
    (hsupp : ∀ j, j ∉ floating x → y j = 0) (i : Fin m) :
    rowFloat A (fun j => x j + l * y j) i ⊆ rowFloat A x i := by
  intro j hj
  simp only [bf4_mem_rowFloat] at hj ⊢
  refine ⟨hj.1, ?_⟩
  by_contra h
  rw [bf4_eq_of_not_floating x y l hsupp j h] at hj
  exact h hj.2

/-- The fixed set of row `i` at `x'` is the old fixed set together with the newly fixed part. -/
private lemma bf4_fixed_eq (A : Fin m → Fin n → ℝ) (x y : Fin n → ℝ) (l : ℝ)
    (hsupp : ∀ j, j ∉ floating x → y j = 0) (i : Fin m) :
    univ.filter (fun j => A i j = 1 ∧ ¬ |x j + l * y j| < 1) =
      univ.filter (fun j => A i j = 1 ∧ ¬ |x j| < 1) ∪
        (rowFloat A x i \ rowFloat A (fun j => x j + l * y j) i) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_sdiff,
    bf4_mem_rowFloat]
  by_cases hx : |x j| < 1
  · constructor
    · rintro ⟨hA, hx'⟩
      exact Or.inr ⟨⟨hA, hx⟩, fun h => hx' h.2⟩
    · rintro (⟨hA, hnx⟩ | ⟨⟨hA, _⟩, hn⟩)
      · exact absurd hx hnx
      · exact ⟨hA, fun h => hn ⟨hA, h⟩⟩
  · rw [bf4_eq_of_not_floating x y l hsupp j hx]
    constructor
    · rintro ⟨hA, hx'⟩
      exact Or.inl ⟨hA, hx'⟩
    · rintro (⟨hA, hnx⟩ | ⟨⟨_, hx2⟩, _⟩)
      · exact ⟨hA, hnx⟩
      · exact absurd hx2 hx

private lemma bf4_fixedSum_eq (A : Fin m → Fin n → ℝ) (x y : Fin n → ℝ) (l : ℝ)
    (hsupp : ∀ j, j ∉ floating x → y j = 0) (i : Fin m) :
    fixedSum A (fun j => x j + l * y j) i =
      fixedSum A x i +
        ∑ j ∈ rowFloat A x i \ rowFloat A (fun j => x j + l * y j) i, (x j + l * y j) := by
  have hdisj : Disjoint (univ.filter (fun j => A i j = 1 ∧ ¬ |x j| < 1))
      (rowFloat A x i \ rowFloat A (fun j => x j + l * y j) i) := by
    rw [Finset.disjoint_left]
    intro j hj hj'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [Finset.mem_sdiff, bf4_mem_rowFloat] at hj'
    exact hj.2 hj'.1.2
  simp only [fixedSum]
  rw [bf4_fixed_eq A x y l hsupp i, Finset.sum_union hdisj]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  exact bf4_eq_of_not_floating x y l hsupp j hj.2

lemma inv_preserved (t : ℕ) (ht : 1 ≤ t) (A : Fin m → Fin n → ℝ) (x y : Fin n → ℝ) (l : ℝ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hinv : Inv t A x)
    (hsupp : ∀ j, j ∉ floating x → y j = 0)
    (hker : ∀ i ∈ activeRows t A x, ∑ j, A i j * y j = 0)
    (hl : ∀ j, |x j + l * y j| ≤ 1)
    (hhit : ∃ j, y j ≠ 0 ∧ |x j + l * y j| = 1) :
    Inv t A (fun j => x j + l * y j) ∧
      floating (fun j => x j + l * y j) ⊂ floating x := by
  -- (F1) monotonicity of the floating sets
  have hsub_fl : floating (fun j => x j + l * y j) ⊆ floating x := bf4_floating_subset x y l hsupp
  have hsub_row : ∀ i, rowFloat A (fun j => x j + l * y j) i ⊆ rowFloat A x i :=
    bf4_rowFloat_subset A x y l hsupp
  have hcard : ∀ i, (rowFloat A (fun j => x j + l * y j) i).card ≤ (rowFloat A x i).card :=
    fun i => Finset.card_le_card (hsub_row i)
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  -- the row sum at `x'` splits linearly
  have hrow : ∀ i, ∑ j, A i j * (x j + l * y j) = ∑ j, A i j * x j + l * ∑ j, A i j * y j := by
    intro i
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  -- rows active at `x` have zero row sum at `x'`
  have hzero : ∀ i, t < (rowFloat A x i).card → ∑ j, A i j * (x j + l * y j) = 0 := by
    intro i hi
    have hmem : i ∈ activeRows t A x := by
      simp only [activeRows, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hi
    rw [hrow i, hinv.active i hi, hker i hmem, mul_zero, add_zero]
  -- (F2) strictness
  have hssub : floating (fun j => x j + l * y j) ⊂ floating x := by
    obtain ⟨j0, hy0, hx0⟩ := hhit
    rw [Finset.ssubset_iff_of_subset hsub_fl]
    have hj0 : j0 ∈ floating x := by
      by_contra h
      exact hy0 (hsupp j0 h)
    refine ⟨j0, hj0, ?_⟩
    have hnot : ¬ |x j0 + l * y j0| < 1 := by
      rw [hx0]
      exact lt_irrefl 1
    exact fun h => hnot ((bf4_mem_floating _ j0).mp h)
  -- (F4) active rows at `x'`
  have hactive' : ∀ i, t < (rowFloat A (fun j => x j + l * y j) i).card →
      ∑ j, A i j * (x j + l * y j) = 0 := by
    intro i hi
    exact hzero i (lt_of_lt_of_le hi (hcard i))
  -- (F5) inactive rows at `x'`
  have hinactive' : ∀ i, (rowFloat A (fun j => x j + l * y j) i).card ≤ t →
      |fixedSum A (fun j => x j + l * y j) i| <
        2 * (t : ℝ) - ((rowFloat A (fun j => x j + l * y j) i).card : ℝ) := by
    intro i hi
    by_cases hact : t < (rowFloat A x i).card
    · -- case (a): the row was active at `x`
      have hcardle : ((rowFloat A (fun j => x j + l * y j) i).card : ℝ) ≤ t := by
        exact_mod_cast hi
      have hsum0 : ∑ j, A i j * (x j + l * y j) = 0 := hzero i hact
      have hsplit : ∑ j, A i j * (x j + l * y j) =
          fixedSum A (fun j => x j + l * y j) i +
            ∑ j ∈ rowFloat A (fun j => x j + l * y j) i, (x j + l * y j) :=
        row_sum_split A (fun j => x j + l * y j) h01 i
      rw [hsum0] at hsplit
      have hfs : fixedSum A (fun j => x j + l * y j) i =
          -(∑ j ∈ rowFloat A (fun j => x j + l * y j) i, (x j + l * y j)) := by
        linarith
      have hbound : |∑ j ∈ rowFloat A (fun j => x j + l * y j) i, (x j + l * y j)| ≤
          ∑ j ∈ rowFloat A (fun j => x j + l * y j) i, |x j + l * y j| :=
        Finset.abs_sum_le_sum_abs _ _
      rw [hfs, abs_neg]
      rcases (rowFloat A (fun j => x j + l * y j) i).eq_empty_or_nonempty with hemp | hne
      · rw [hemp]
        simp only [Finset.sum_empty, abs_zero, Finset.card_empty, Nat.cast_zero, sub_zero]
        linarith
      · have hlt : ∑ j ∈ rowFloat A (fun j => x j + l * y j) i, |x j + l * y j| <
            ∑ j ∈ rowFloat A (fun j => x j + l * y j) i, (1 : ℝ) := by
          apply Finset.sum_lt_sum_of_nonempty hne
          intro j hj
          rw [bf4_mem_rowFloat] at hj
          exact hj.2
        rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hlt
        linarith
    · -- case (b): the row was already inactive at `x`
      rw [not_lt] at hact
      have hold := hinv.inactive i hact
      rw [bf4_fixedSum_eq A x y l hsupp i]
      have hN : |∑ j ∈ rowFloat A x i \ rowFloat A (fun j => x j + l * y j) i, (x j + l * y j)| ≤
          ((rowFloat A x i).card : ℝ) - ((rowFloat A (fun j => x j + l * y j) i).card : ℝ) := by
        calc |∑ j ∈ rowFloat A x i \ rowFloat A (fun j => x j + l * y j) i, (x j + l * y j)|
            ≤ ∑ j ∈ rowFloat A x i \ rowFloat A (fun j => x j + l * y j) i, |x j + l * y j| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j ∈ rowFloat A x i \ rowFloat A (fun j => x j + l * y j) i, (1 : ℝ) :=
              Finset.sum_le_sum (fun j _ => hl j)
          _ = ((rowFloat A x i \ rowFloat A (fun j => x j + l * y j) i).card : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          _ = ((rowFloat A x i).card : ℝ) - ((rowFloat A (fun j => x j + l * y j) i).card : ℝ) := by
              rw [Finset.card_sdiff_of_subset (hsub_row i), Nat.cast_sub (hcard i)]
      calc |fixedSum A x i +
              ∑ j ∈ rowFloat A x i \ rowFloat A (fun j => x j + l * y j) i, (x j + l * y j)|
          ≤ |fixedSum A x i| +
              |∑ j ∈ rowFloat A x i \ rowFloat A (fun j => x j + l * y j) i, (x j + l * y j)| :=
            abs_add_le _ _
        _ < 2 * (t : ℝ) - ((rowFloat A (fun j => x j + l * y j) i).card : ℝ) := by linarith
  exact ⟨⟨hl, hactive', hinactive'⟩, hssub⟩

/-- One step of the process: strictly fewer floating coordinates, invariant kept. -/
lemma inv_step (t : ℕ) (ht : 1 ≤ t) (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hdeg : ∀ j, ({i | A i j = 1} : Finset (Fin m)).card ≤ t)
    (hinv : Inv t A x) (hne : (floating x).Nonempty) :
    ∃ x' : Fin n → ℝ, Inv t A x' ∧ floating x' ⊂ floating x := by
  have hlt := card_active_lt t A x h01 hdeg hne
  obtain ⟨y, hy₀, hsupp, hker⟩ := exists_kernel_vector A (floating x) (activeRows t A x) hlt
  have hsupp' : ∀ j, y j ≠ 0 → |x j| < 1 := by
    intro j hj
    by_contra h
    apply hj
    apply hsupp
    intro hmem
    rw [floating, Finset.mem_filter] at hmem
    exact h hmem.2
  obtain ⟨l, hl, hhit⟩ := exists_line_hit x y hinv.bound hy₀ hsupp'
  obtain ⟨hinv', hsub⟩ := inv_preserved t ht A x y l h01 hinv hsupp hker hl hhit
  exact ⟨fun j => x j + l * y j, hinv', hsub⟩

/-! ### L6/L7: the end of the process -/

/-- A 0/1-weighted sum of `±1`'s is an integer. -/
lemma row_sum_is_int (A : Fin m → Fin n → ℝ) (ε : Fin n → ℝ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) (hε : IsSignVector ε) (i : Fin m) :
    ∃ z : ℤ, ∑ j, A i j * ε j = z := by
  have key : ∀ j, A i j * ε j =
      ((if A i j = 1 then (if ε j = 1 then (1 : ℤ) else -1) else 0 : ℤ) : ℝ) := by
    intro j
    rcases h01 i j with h | h <;> rcases hε j with h' | h' <;> norm_num [h, h']
  refine ⟨∑ j, (if A i j = 1 then (if ε j = 1 then (1 : ℤ) else -1) else 0 : ℤ), ?_⟩
  rw [Int.cast_sum]
  exact Finset.sum_congr rfl (fun j _ => key j)

/-- Once nothing floats, the invariant yields the Beck–Fiala bound. -/
lemma final_bound (t : ℕ) (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hinv : Inv t A x) (hempty : floating x = ∅) :
    IsSignVector x ∧ ∀ i, |∑ j, A i j * x j| ≤ 2 * (t : ℝ) - 1 := by
  have hnf : ∀ j, ¬ |x j| < 1 := by
    intro j
    have h := hempty
    rw [floating, Finset.filter_eq_empty_iff] at h
    exact h (Finset.mem_univ j)
  have habs : ∀ j, |x j| = 1 := fun j => le_antisymm (hinv.bound j) (not_lt.mp (hnf j))
  have hsign : IsSignVector x := fun j => eq_or_eq_neg_of_abs_eq (habs j)
  refine ⟨hsign, fun i => ?_⟩
  have hrow : rowFloat A x i = ∅ := by
    rw [rowFloat, Finset.filter_eq_empty_iff]
    intro j _ hj
    exact hnf j hj.2
  have hcard : (rowFloat A x i).card = 0 := by rw [hrow]; exact Finset.card_empty
  have hinact := hinv.inactive i (by rw [hcard]; exact Nat.zero_le t)
  rw [hcard] at hinact
  simp only [Nat.cast_zero, sub_zero] at hinact
  have hsum : ∑ j, A i j * x j = fixedSum A x i := by
    rw [row_sum_split A x h01 i, hrow, Finset.sum_empty, add_zero]
  obtain ⟨z, hz⟩ := row_sum_is_int A x h01 hsign i
  have h1 : |(z : ℝ)| < 2 * (t : ℝ) := by
    have hzf : (z : ℝ) = fixedSum A x i := by rw [← hz, hsum]
    rw [hzf]
    exact hinact
  have h2 : |z| < 2 * (t : ℤ) := by exact_mod_cast h1
  have h3 : |z| ≤ 2 * (t : ℤ) - 1 := by omega
  have h4 : (|z| : ℝ) ≤ 2 * (t : ℝ) - 1 := by exact_mod_cast h3
  rw [hz]
  exact h4

/-- Induction on the number of floating coordinates. -/
lemma exists_sign_of_inv (t : ℕ) (ht : 1 ≤ t) (A : Fin m → Fin n → ℝ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hdeg : ∀ j, ({i | A i j = 1} : Finset (Fin m)).card ≤ t) :
    ∀ (k : ℕ) (x : Fin n → ℝ), Inv t A x → (floating x).card = k →
      ∃ ε : Fin n → ℝ, IsSignVector ε ∧ ∀ i, |∑ j, A i j * ε j| ≤ 2 * (t : ℝ) - 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hinv hk
    by_cases hemp : floating x = ∅
    · obtain ⟨hs, hb⟩ := final_bound t A x h01 hinv hemp
      exact ⟨x, hs, hb⟩
    · have hne : (floating x).Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
      obtain ⟨x', hinv', hsub⟩ := inv_step t ht A x h01 hdeg hinv hne
      have hlt : (floating x').card < k := by
        rw [← hk]
        exact Finset.card_lt_card hsub
      exact ih _ hlt x' hinv' rfl

end

end Komlos

open Komlos

/-- **Beck–Fiala (1981).** A `0/1` matrix whose columns each contain at most `t ≥ 1` ones admits a
`±1` signing of the columns with every row sum bounded by `2t - 1` in absolute value. -/
theorem solution (t n m : ℕ) (ht : 1 ≤ t) (A : Fin m → Fin n → ℝ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hdeg : ∀ j, ({i | A i j = 1} : Finset (Fin m)).card ≤ t) :
    ∃ ε : Fin n → ℝ, IsSignVector ε ∧
      ∀ i, |∑ j, A i j * ε j| ≤ 2 * (t : ℝ) - 1 :=
  exists_sign_of_inv t ht A h01 hdeg _ (fun _ => 0) (inv_zero t ht A) rfl
