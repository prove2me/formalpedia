-- Prove2me | solution 1 for OAI.Problem348.no_polynomial_removal_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T12:35:57.996627+00:00
-- url     : https://prove2.me/submissions/64befd63-25f1-4741-9e8c-4c78b278e580

import Mathlib
import Definitions.Def_MatrixRemoval

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434

universe uI uJ uT uR uC uG uK uL uRho uBeta uAlpha uM uV uO uKR uKC uOmega uCell uValue uX uY uZ

section
section
namespace OAI

noncomputable section



namespace Problem348

end Problem348

end

end OAI
end
end

section
section
namespace OAI

/-!
The raw finite host; row and column orders are supplied separately.
The second coordinate in a variable class is uniform on `Fin (2^h)`;
its quotient by the block size is the node index.
-/
noncomputable section
namespace Problem348.Construction

abbrev VariablePosition (h : ℕ) := Fin (2 * h + 1) × Fin (2 ^ h)
abbrev AnchorPosition (h : ℕ) := Fin (6 * h) × Fin 64 × Fin (2 ^ h)
abbrev Position (h : ℕ) := AnchorPosition h ⊕ (VariablePosition h ⊕ Fin (2 ^ h))
abbrev Mode (h : ℕ) := Fin (6 * h)

def depth {h : ℕ} (x : VariablePosition h) : ℕ := x.1.val / 2
def node {h : ℕ} (x : VariablePosition h) : ℕ := x.2.val / 2 ^ (h - depth x)
def plus {h : ℕ} (x : VariablePosition h) : Bool := decide (x.1.val % 2 = 0)
def level {h : ℕ} (t : Mode h) : ℕ := t.val / 6 + 1
def kind {h : ℕ} (t : Mode h) : ℕ := t.val % 6

def AtLevel {h : ℕ} (i : ℕ) (s : Bool) (x : VariablePosition h) : Prop :=
  depth x = i ∧ (i = h ∨ plus x = s)

def rowRole {h : ℕ} (t : Mode h) (j : Fin 2) (x : Position h) : Prop :=
  match x with
  | Sum.inl _ => False
  | Sum.inr (Sum.inr _) => 2 ≤ kind t ∧ j.val = 1
  | Sum.inr (Sum.inl v) =>
    if kind t = 0 then
      AtLevel (if j.val = 0 then level t else level t - 1) true v
    else if kind t = 1 then
      AtLevel (if j.val = 0 then level t - 1 else level t) false v
    else
      j.val = 0 ∧ AtLevel (level t) (decide (kind t < 4)) v ∧
        node v % 2 = (kind t % 2)

def colRole {h : ℕ} (t : Mode h) (j : Fin 2) (x : Position h) : Prop :=
  match x with
  | Sum.inl _ => False
  | Sum.inr (Sum.inr _) => kind t < 2 ∧ j.val = 0
  | Sum.inr (Sum.inl v) =>
    if kind t < 2 then
      j.val = 1 ∧ AtLevel (level t - 1) (decide (kind t = 0)) v
    else if kind t < 4 then
      if j.val = 0 then AtLevel (level t - 1) true v
      else AtLevel (level t) true v ∧ node v % 2 = kind t % 2
    else
      if j.val = 0 then AtLevel (level t) false v ∧ node v % 2 = kind t % 2
      else AtLevel (level t - 1) false v

instance {h : ℕ} (i : ℕ) (s : Bool) (v : VariablePosition h) :
    Decidable (AtLevel i s v) := inferInstanceAs (Decidable (_ ∧ _))
instance {h : ℕ} (t : Mode h) (j : Fin 2) (x : Position h) :
    Decidable (rowRole t j x) := by unfold rowRole; split <;> infer_instance
instance {h : ℕ} (t : Mode h) (j : Fin 2) (x : Position h) :
    Decidable (colRole t j x) := by unfold colRole; split <;> infer_instance

def variableEntry {h : ℕ} (r c : VariablePosition h) : Bool :=
  if depth r = depth c then
    if depth r = h then decide (node r ≤ node c)
    else if plus r = plus c then
      if plus r then decide (node r ≤ node c) else decide (node r < node c)
    else false
  else if depth r = depth c + 1 ∧ depth c < h ∧
      (depth r = h ∨ plus r = plus c) then
    if plus c then decide (node r / 2 ≤ node c) else decide (node r / 2 < node c)
  else false

def host {h : ℕ} (r c : Position h) : Bool :=
  match r, c with
  | Sum.inl (t, u, _), Sum.inl (t', v, _) =>
      if t = t' then Problem348.anchor64 u v else false
  | Sum.inl (t, u, _), Sum.inr _ =>
      decide ((u.val = 0 ∧ colRole t 0 c) ∨ (u.val = 1 ∧ colRole t 1 c))
  | Sum.inr _, Sum.inl (t, v, _) =>
      decide ((v.val = 0 ∧ rowRole t 0 r) ∨ (v.val = 1 ∧ rowRole t 1 r))
  | Sum.inr (Sum.inl v), Sum.inr (Sum.inl w) => variableEntry v w
  | Sum.inr _, Sum.inr _ => true

theorem depth_le {h : ℕ} (x : VariablePosition h) : depth x ≤ h := by
  have hx := x.1.isLt
  unfold depth
  omega

theorem level_pos {h : ℕ} (t : Mode h) : 1 ≤ level t := by
  unfold level
  omega

theorem level_le {h : ℕ} (t : Mode h) : level t ≤ h := by
  have ht := t.isLt
  unfold level
  omega

theorem kind_lt {h : ℕ} (t : Mode h) : kind t < 6 := by
  exact Nat.mod_lt _ (by decide)

theorem card_variablePosition (h : ℕ) :
    Fintype.card (VariablePosition h) = (2 * h + 1) * 2 ^ h := by
  simp [VariablePosition]

theorem card_position (h : ℕ) :
    Fintype.card (Position h) = (386 * h + 2) * 2 ^ h := by
  simp only [Position, AnchorPosition, VariablePosition, Fintype.card_sum,
    Fintype.card_prod, Fintype.card_fin]
  ring

@[simp] theorem host_anchor_same {h : ℕ} (t : Mode h) (u v : Fin 64)
    (x y : Fin (2 ^ h)) :
    host (Sum.inl (t, u, x)) (Sum.inl (t, v, y)) = anchor64 u v := by
  simp [host]

@[simp] theorem host_anchor_different {h : ℕ} (t t' : Mode h) (ht : t ≠ t')
    (u v : Fin 64) (x y : Fin (2 ^ h)) :
    host (Sum.inl (t, u, x)) (Sum.inl (t', v, y)) = false := by
  simp [host, ht]

@[simp] theorem host_variable_variable {h : ℕ} (v w : VariablePosition h) :
    host (Sum.inr (Sum.inl v)) (Sum.inr (Sum.inl w)) = variableEntry v w := rfl

@[simp] theorem host_dummy_variable {h : ℕ} (x : Fin (2 ^ h))
    (v : VariablePosition h) :
    host (Sum.inr (Sum.inr x)) (Sum.inr (Sum.inl v)) = true := rfl

@[simp] theorem host_variable_dummy {h : ℕ} (x : Fin (2 ^ h))
    (v : VariablePosition h) :
    host (Sum.inr (Sum.inl v)) (Sum.inr (Sum.inr x)) = true := rfl

theorem rowRole_disjoint {h : ℕ} (t : Mode h) (x : Position h) :
    ¬ (rowRole t 0 x ∧ rowRole t 1 x) := by
  have hp := level_pos t
  have hk := kind_lt t
  rcases x with a | (v | d)
  · simp [rowRole]
  · interval_cases e : kind t <;>
      simp [rowRole, e, AtLevel] <;> omega
  · simp [rowRole]

theorem colRole_disjoint {h : ℕ} (t : Mode h) (x : Position h) :
    ¬ (colRole t 0 x ∧ colRole t 1 x) := by
  have hp := level_pos t
  have hk := kind_lt t
  rcases x with a | (v | d)
  · simp [colRole]
  · interval_cases e : kind t <;>
      simp [colRole, e, AtLevel] <;> omega
  · simp [colRole]

end Problem348.Construction

end

end OAI
end
end

section
section
namespace OAI

namespace Problem348

/-- The anchor is off-diagonal one outside its modified bit rectangle. -/
theorem anchor64_eq_decide_ne (u v : Fin 64)
    (h : u.val < 32 ∨ v.val < 59) :
    anchor64 u v = decide (u.val ≠ v.val) := by
  unfold anchor64
  split_ifs with hmod
  · rcases h with h | h <;> omega
  · rfl

/-- In the dense prefix, every column has at most one zero. -/
theorem anchor64_first32_zero_iff (u v : Fin 64) (hu : u.val < 32) :
    anchor64 u v = false ↔ u = v := by
  rw [anchor64_eq_decide_ne u v (Or.inl hu)]
  simp [Fin.ext_iff]

/-- In the dense prefix, every row has at most one zero. -/
theorem anchor64_first32_column_zero_iff (u v : Fin 64) (hv : v.val < 32) :
    anchor64 u v = false ↔ u = v := by
  rw [anchor64_eq_decide_ne u v (Or.inr (by omega))]
  simp [Fin.ext_iff]

/-- Every anchor row contains at least 58 ones. -/
theorem anchor64_row_ones : ∀ u : Fin 64,
    58 ≤ (Finset.univ.filter (fun v => anchor64 u v = true)).card := by
  decide

/-- Every anchor column contains at least 48 ones. -/
theorem anchor64_column_ones : ∀ v : Fin 64,
    48 ≤ (Finset.univ.filter (fun u => anchor64 u v = true)).card := by
  decide

/-- The five bit-coordinate columns of the anchor. -/
def anchorLastCol (b : Fin 5) : Fin 64 := ⟨b.val + 59, by omega⟩

/-- Distinct rows have distinct complete anchor words. -/
theorem anchor64_rows_injective : Function.Injective anchor64 := by
  intro u v huv
  by_cases hu : u.val < 59
  · have h := congrFun huv u
    rw [anchor64_eq_decide_ne u u (Or.inr hu),
      anchor64_eq_decide_ne v u (Or.inr hu)] at h
    apply Fin.ext
    have hvu : v.val = u.val := by simpa using h
    exact hvu.symm
  by_cases hv : v.val < 59
  · have h := congrFun huv v
    rw [anchor64_eq_decide_ne u v (Or.inr hv),
      anchor64_eq_decide_ne v v (Or.inr hv)] at h
    simpa [Fin.ext_iff] using h
  have hlast : ∀ a b : Fin 64, 59 ≤ a.val → 59 ≤ b.val →
      (∀ j : Fin 5, anchor64 a (anchorLastCol j) =
        anchor64 b (anchorLastCol j)) → a = b := by
    decide
  exact hlast u v (by omega) (by omega) (fun j => congrFun huv _)

/-- Distinct columns have distinct complete anchor words. -/
theorem anchor64_columns_injective :
    Function.Injective (fun v : Fin 64 => fun u : Fin 64 => anchor64 u v) := by
  decide

/-- All five-bit words, in the order used by the replacement rectangle. -/
def anchorWord (a : Fin 32) (b : Fin 5) : Bool :=
  anchor64 ⟨a.val + 32, by omega⟩ ⟨b.val + 59, by omega⟩

/-- The 32 lower anchor rows realize all binary words on the last five columns. -/
theorem anchorWord_bijective : Function.Bijective anchorWord := by
  decide

/-- Inclusion of the dense 32-position prefix. -/
def anchorFirst32 (i : Fin 32) : Fin 64 := ⟨i.val, by omega⟩

/-- First-prefix column density, used to exclude variable columns. -/
theorem anchor64_first32_column_ones : ∀ v : Fin 64,
    31 ≤ (Finset.univ.filter (fun u : Fin 32 =>
      anchor64 (anchorFirst32 u) v = true)).card := by
  decide

/-- First-prefix row density, used to exclude variable rows. -/
theorem anchor64_first32_row_ones : ∀ u : Fin 64,
    31 ≤ (Finset.univ.filter (fun v : Fin 32 =>
      anchor64 u (anchorFirst32 v) = true)).card := by
  decide

/-- Any two columns share a one in the first 32 rows. -/
theorem anchor64_columns_common_one : ∀ v w : Fin 64,
    ∃ u : Fin 32, anchor64 (anchorFirst32 u) v = true ∧
      anchor64 (anchorFirst32 u) w = true := by
  intro v w
  by_cases h0 : v.val ≠ 0 ∧ w.val ≠ 0
  · exact ⟨0, by simpa [anchorFirst32, anchor64, ne_comm] using h0⟩
  by_cases h1 : v.val ≠ 1 ∧ w.val ≠ 1
  · exact ⟨1, by simpa [anchorFirst32, anchor64, ne_comm] using h1⟩
  have h2 : v.val ≠ 2 ∧ w.val ≠ 2 := by omega
  exact ⟨2, by simpa [anchorFirst32, anchor64, ne_comm] using h2⟩

/-- Any two rows share a one in the first 32 columns. -/
theorem anchor64_rows_common_one : ∀ u w : Fin 64,
    ∃ v : Fin 32, anchor64 u (anchorFirst32 v) = true ∧
      anchor64 w (anchorFirst32 v) = true := by
  intro u w
  by_cases h0 : u.val ≠ 0 ∧ w.val ≠ 0
  · exact ⟨0, by simpa [anchorFirst32, anchor64] using h0⟩
  by_cases h1 : u.val ≠ 1 ∧ w.val ≠ 1
  · exact ⟨1, by simpa [anchorFirst32, anchor64] using h1⟩
  have h2 : u.val ≠ 2 ∧ w.val ≠ 2 := by omega
  exact ⟨2, by simp [anchorFirst32, anchor64, h2.1, h2.2]⟩

end Problem348

end OAI
end
end

section
section
namespace OAI

/-!
Finite combinatorial anchor rigidity under explicit density, sparsity,
and mode-incidence hypotheses.
-/


namespace Problem348.AnchorRigidity

/-- At most one zero leaves all but at most one position equal to one. -/
theorem card_le_true_card_add_one {I : Type uI} [DecidableEq I]
    (s : Finset I) (f : I → Bool)
    (hz : (s.filter fun i => f i = false).card ≤ 1) :
    s.card ≤ (s.filter fun i => f i = true).card + 1 := by
  classical
  have hp := Finset.card_filter_add_card_filter_not (s := s)
    (p := fun i => f i = true)
  have hn : (s.filter fun i => ¬ f i = true).card ≤ 1 := by
    simpa only [Bool.not_eq_true] using hz
  omega

/-- Two columns with at most one zero share a one on any core of size at least three. -/
theorem exists_common_true {I : Type uI} [DecidableEq I]
    (s : Finset I) (f g : I → Bool) (hs : 3 ≤ s.card)
    (hf : (s.filter fun i => f i = false).card ≤ 1)
    (hg : (s.filter fun i => g i = false).card ≤ 1) :
    ∃ i ∈ s, f i = true ∧ g i = true := by
  classical
  by_contra h
  have hsub : (s.filter fun i => f i = true) ⊆
      (s.filter fun i => g i = false) := by
    intro i hi
    obtain ⟨his, hif⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨his, ?_⟩
    cases hgi : g i with
    | false => rfl
    | true => exact False.elim (h ⟨i, his, hif, hgi⟩)
  have hcard := Finset.card_le_card hsub
  have hpos := card_le_true_card_add_one s f hf
  omega

/-- One-sided rigidity.  A dense anchor core on the row axis forces both axes
into one mode.  The dummy predicate is only needed to permit one exceptional
non-anchor column before the common mode has been identified. -/
theorem one_sided
    {I : Type uI} {J : Type uJ} {T : Type uT} [Fintype I] [Fintype J]
    (B : I → J → Bool) (rowMode : I → Option T) (colMode : J → Option T)
    (dummyCol : J → Prop) (core : Finset I)
    (hcore : 6 ≤ core.card)
    (core_anchor : ∀ i ∈ core, ∃ t, rowMode i = some t)
    (core_zeros : ∀ j, (core.filter fun i => B i j = false).card ≤ 1)
    (variable_sparse : ∀ j, colMode j = none → ¬ dummyCol j →
      (core.filter fun i => B i j = true).card ≤ 4)
    (dummy_unique : ∀ j k, dummyCol j → dummyCol k → j = k)
    (cross_mode : ∀ i j t u, rowMode i = some t → colMode j = some u →
      B i j = true → t = u)
    (nonanchor_row_unit : ∀ i, rowMode i = none → ∀ j k t,
      colMode j = some t → colMode k = some t →
      B i j = true → B i k = true → j = k)
    (nonanchor_col_unit : ∀ j, colMode j = none → ∀ i k t,
      rowMode i = some t → rowMode k = some t →
      B i j = true → B k j = true → i = k)
    (row_dense : ∀ i, 2 ≤ (Finset.univ.filter fun j => B i j = true).card) :
    ∃ t, (∀ i, rowMode i = some t) ∧ (∀ j, colMode j = some t) := by
  classical
  have core_positive (j : J) : 5 ≤ (core.filter fun i => B i j = true).card := by
    have h := card_le_true_card_add_one core (fun i => B i j) (core_zeros j)
    omega
  have nonanchor_dummy (j : J) (hj : colMode j = none) : dummyCol j := by
    by_contra hd
    have hs := variable_sparse j hj hd
    have hp := core_positive j
    omega
  have nonanchor_unique (j k : J) (hj : colMode j = none)
      (hk : colMode k = none) : j = k :=
    dummy_unique j k (nonanchor_dummy j hj) (nonanchor_dummy k hk)
  have two_ones (i : I) : ∃ j k, B i j = true ∧ B i k = true ∧ j ≠ k := by
    have hd := row_dense i
    obtain ⟨j, hj, k, hk, hne⟩ := Finset.one_lt_card.mp (show
      1 < (Finset.univ.filter fun j => B i j = true).card by omega)
    exact ⟨j, k, (Finset.mem_filter.mp hj).2, (Finset.mem_filter.mp hk).2, hne⟩
  have row_anchor_one (i : I) : ∃ j t, colMode j = some t ∧ B i j = true := by
    obtain ⟨j, k, hj, hk, hne⟩ := two_ones i
    cases hmj : colMode j with
    | some t => exact ⟨j, t, hmj, hj⟩
    | none =>
      cases hmk : colMode k with
      | some t => exact ⟨k, t, hmk, hk⟩
      | none => exact False.elim (hne (nonanchor_unique j k hmj hmk))
  obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (show 0 < core.card by omega)
  obtain ⟨j₀, t, hj₀, _⟩ := row_anchor_one i₀
  have anchor_columns (j : J) (u : T) (hj : colMode j = some u) : u = t := by
    obtain ⟨i, hi, hij, hij₀⟩ := exists_common_true core
      (fun i => B i j) (fun i => B i j₀) (by omega) (core_zeros j) (core_zeros j₀)
    obtain ⟨v, hiv⟩ := core_anchor i hi
    exact (cross_mode i j v u hiv hj hij).symm.trans
      (cross_mode i j₀ v t hiv hj₀ hij₀)
  have anchor_rows (i : I) (u : T) (hi : rowMode i = some u) : u = t := by
    obtain ⟨j, v, hj, hij⟩ := row_anchor_one i
    exact (cross_mode i j u v hi hj hij).trans (anchor_columns j v hj)
  have core_same (i : I) (hi : i ∈ core) : rowMode i = some t := by
    obtain ⟨u, hu⟩ := core_anchor i hi
    simpa only [anchor_rows i u hu] using hu
  have all_columns (j : J) : colMode j = some t := by
    cases hj : colMode j with
    | some u => simp only [anchor_columns j u hj]
    | none =>
      have hs : (core.filter fun i => B i j = true).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro i hi k hk
        obtain ⟨hic, hij⟩ := Finset.mem_filter.mp hi
        obtain ⟨hkc, hkj⟩ := Finset.mem_filter.mp hk
        exact nonanchor_col_unit j hj i k t (core_same i hic) (core_same k hkc) hij hkj
      have hp := core_positive j
      omega
  refine ⟨t, ?_, all_columns⟩
  intro i
  cases hi : rowMode i with
  | some u => simp only [anchor_rows i u hi]
  | none =>
    obtain ⟨j, k, hj, hk, hne⟩ := two_ones i
    exact False.elim (hne (nonanchor_row_unit i hi j k t
      (all_columns j) (all_columns k) hj hk))

/-- A dense core consists of at least six selected anchor positions.  Every
opposite position has at most one zero on it, while a variable opposite
position would have at most four ones. -/
def DenseAnchorCore {I : Type uI} {J : Type uJ} {T : Type uT}
    (B : I → J → Bool) (rowMode : I → Option T) (colMode : J → Option T)
    (dummyCol : J → Prop) : Prop :=
  ∃ core : Finset I, 6 ≤ core.card ∧
    (∀ i ∈ core, ∃ t, rowMode i = some t) ∧
    (∀ j, (core.filter fun i => B i j = false).card ≤ 1) ∧
    (∀ j, colMode j = none → ¬ dummyCol j →
      (core.filter fun i => B i j = true).card ≤ 4)

/-- Symmetric form of anchor rigidity: a dense anchor core on either axis
suffices.  The no-shattering/order argument supplies this disjunction in the
application to the 64 by 64 pattern. -/
theorem rigidity
    {I : Type uI} {J : Type uJ} {T : Type uT} [Fintype I] [Fintype J]
    (B : I → J → Bool) (rowMode : I → Option T) (colMode : J → Option T)
    (dummyRow : I → Prop) (dummyCol : J → Prop)
    (hcore : DenseAnchorCore B rowMode colMode dummyCol ∨
      DenseAnchorCore (fun j i => B i j) colMode rowMode dummyRow)
    (dummy_row_unique : ∀ i k, dummyRow i → dummyRow k → i = k)
    (dummy_col_unique : ∀ j k, dummyCol j → dummyCol k → j = k)
    (cross_mode : ∀ i j t u, rowMode i = some t → colMode j = some u →
      B i j = true → t = u)
    (nonanchor_row_unit : ∀ i, rowMode i = none → ∀ j k t,
      colMode j = some t → colMode k = some t →
      B i j = true → B i k = true → j = k)
    (nonanchor_col_unit : ∀ j, colMode j = none → ∀ i k t,
      rowMode i = some t → rowMode k = some t →
      B i j = true → B k j = true → i = k)
    (row_dense : ∀ i, 2 ≤ (Finset.univ.filter fun j => B i j = true).card)
    (col_dense : ∀ j, 2 ≤ (Finset.univ.filter fun i => B i j = true).card) :
    ∃ t, (∀ i, rowMode i = some t) ∧ (∀ j, colMode j = some t) := by
  rcases hcore with hcore | hcore
  · obtain ⟨core, hc, ha, hz, hs⟩ := hcore
    exact one_sided B rowMode colMode dummyCol core hc ha hz hs
      dummy_col_unique cross_mode nonanchor_row_unit nonanchor_col_unit row_dense
  · obtain ⟨core, hc, ha, hz, hs⟩ := hcore
    obtain ⟨t, hcol, hrow⟩ := one_sided (fun j i => B i j) colMode rowMode
      dummyRow core hc ha hz hs dummy_row_unique
      (fun j i u t hj hi hb => (cross_mode i j t u hi hj hb).symm)
      nonanchor_col_unit nonanchor_row_unit col_dense
    exact ⟨t, hrow, hcol⟩

end Problem348.AnchorRigidity

end OAI
end
end

section
section
namespace OAI


namespace Problem348.AnchorRigidity

/-- The actual first 32 positions of the fixed anchor. -/
def firstCore : Finset (Fin 64) := Finset.univ.filter fun i => i.val < 32

@[simp] theorem mem_firstCore (i : Fin 64) : i ∈ firstCore ↔ i.val < 32 := by
  simp [firstCore]

theorem firstCore_card : firstCore.card = 32 := by decide

theorem firstCore_column_zeros (j : Fin 64) :
    (firstCore.filter fun i => anchor64 i j = false).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi k hk
  obtain ⟨hic, hij⟩ := Finset.mem_filter.mp hi
  obtain ⟨hkc, hkj⟩ := Finset.mem_filter.mp hk
  exact ((anchor64_first32_zero_iff i j ((mem_firstCore i).mp hic)).mp hij).trans
    ((anchor64_first32_zero_iff k j ((mem_firstCore k).mp hkc)).mp hkj).symm

theorem firstCore_row_zeros (i : Fin 64) :
    (firstCore.filter fun j => anchor64 i j = false).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro j hj k hk
  obtain ⟨hjc, hij⟩ := Finset.mem_filter.mp hj
  obtain ⟨hkc, hik⟩ := Finset.mem_filter.mp hk
  exact ((anchor64_first32_column_zero_iff i j ((mem_firstCore j).mp hjc)).mp hij).symm.trans
    ((anchor64_first32_column_zero_iff i k ((mem_firstCore k).mp hkc)).mp hik)

/-- A majority of anchor labels in an initial segment contains the dense prefix.
This is the small order/cardinality bridge from the no-shattering majority
argument to the finite rigidity theorem. -/
theorem prefix_of_majority {T : Type uT} (mode : Fin 64 → Option T)
    (initial : ∀ i j, i ≤ j → mode j ≠ none → mode i ≠ none)
    (majority : 32 < (Finset.univ.filter fun i => (mode i).isSome).card) :
    ∀ i : Fin 64, i.val < 32 → ∃ t, mode i = some t := by
  intro i hi
  cases hmi : mode i with
  | some t => exact ⟨t, rfl⟩
  | none =>
    have hsub : (Finset.univ.filter fun j => (mode j).isSome) ⊆ Finset.Iio i := by
      intro j hj
      have hjs := (Finset.mem_filter.mp hj).2
      have hjn : mode j ≠ none := by
        intro hnone
        simp [hnone] at hjs
      apply Finset.mem_Iio.mpr
      by_contra hnot
      exact initial i j (le_of_not_gt hnot) hjn hmi
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hcard
    omega

/-- The majority conclusion on either axis provides the prefix alternative
required by `anchor64_rigidity_of_prefix`. -/
theorem prefix_alternative_of_majority {T : Type uT}
    (rowMode colMode : Fin 64 → Option T)
    (row_initial : ∀ i j, i ≤ j → rowMode j ≠ none → rowMode i ≠ none)
    (col_initial : ∀ i j, i ≤ j → colMode j ≠ none → colMode i ≠ none)
    (majority : 32 < (Finset.univ.filter fun i => (rowMode i).isSome).card ∨
      32 < (Finset.univ.filter fun j => (colMode j).isSome).card) :
    (∀ i : Fin 64, i.val < 32 → ∃ t, rowMode i = some t) ∨
      (∀ j : Fin 64, j.val < 32 → ∃ t, colMode j = some t) := by
  exact majority.imp (prefix_of_majority rowMode row_initial)
    (prefix_of_majority colMode col_initial)

/-- Same-mode conclusion for the exact anchor after prefix pinning. -/
theorem anchor64_rigidity_of_prefix {T : Type uT}
    (rowMode colMode : Fin 64 → Option T)
    (dummyRow dummyCol : Fin 64 → Prop)
    (hprefix : (∀ i : Fin 64, i.val < 32 → ∃ t, rowMode i = some t) ∨
      (∀ j : Fin 64, j.val < 32 → ∃ t, colMode j = some t))
    (variable_col_sparse : ∀ j, colMode j = none → ¬ dummyCol j →
      (∀ i ∈ firstCore, ∃ t, rowMode i = some t) →
      (firstCore.filter fun i => anchor64 i j = true).card ≤ 4)
    (variable_row_sparse : ∀ i, rowMode i = none → ¬ dummyRow i →
      (∀ j ∈ firstCore, ∃ t, colMode j = some t) →
      (firstCore.filter fun j => anchor64 i j = true).card ≤ 4)
    (dummy_row_unique : ∀ i k, dummyRow i → dummyRow k → i = k)
    (dummy_col_unique : ∀ j k, dummyCol j → dummyCol k → j = k)
    (cross_mode : ∀ i j t u, rowMode i = some t → colMode j = some u →
      anchor64 i j = true → t = u)
    (nonanchor_row_unit : ∀ i, rowMode i = none → ∀ j k t,
      colMode j = some t → colMode k = some t →
      anchor64 i j = true → anchor64 i k = true → j = k)
    (nonanchor_col_unit : ∀ j, colMode j = none → ∀ i k t,
      rowMode i = some t → rowMode k = some t →
      anchor64 i j = true → anchor64 k j = true → i = k) :
    ∃ t, (∀ i, rowMode i = some t) ∧ (∀ j, colMode j = some t) := by
  apply rigidity anchor64 rowMode colMode dummyRow dummyCol
    (dummy_row_unique := dummy_row_unique) (dummy_col_unique := dummy_col_unique)
    (cross_mode := cross_mode) (nonanchor_row_unit := nonanchor_row_unit)
    (nonanchor_col_unit := nonanchor_col_unit)
  · rcases hprefix with hr | hc
    · left
      have ha : ∀ i ∈ firstCore, ∃ t, rowMode i = some t :=
        fun i hi => hr i ((mem_firstCore i).mp hi)
      exact ⟨firstCore, by rw [firstCore_card]; omega, ha,
        firstCore_column_zeros, fun j hj hd => variable_col_sparse j hj hd ha⟩
    · right
      have ha : ∀ j ∈ firstCore, ∃ t, colMode j = some t :=
        fun j hj => hc j ((mem_firstCore j).mp hj)
      exact ⟨firstCore, by rw [firstCore_card]; omega, ha,
        firstCore_row_zeros, fun i hi hd => variable_row_sparse i hi hd ha⟩
  · intro i
    exact (by omega : 2 ≤ 58).trans (anchor64_row_ones i)
  · intro j
    exact (by omega : 2 ≤ 48).trans (anchor64_column_ones j)

end Problem348.AnchorRigidity

end OAI
end
end

section
section
namespace OAI

/-!
Concrete twin-position facts for anchor rigidity in the flat-class host.
-/

namespace Problem348.Construction

/-- Changing the representative inside an anchor row group changes no entry. -/
theorem host_anchor_row_twin {h : ℕ} (t : Mode h) (u : Fin 64)
    (x y : Fin (2 ^ h)) (c : Position h) :
    host (Sum.inl (t,u,x)) c = host (Sum.inl (t,u,y)) c := by
  rcases c with a | (v | d) <;> rfl

/-- Changing the representative inside an anchor column group changes no entry. -/
theorem host_anchor_column_twin {h : ℕ} (t : Mode h) (v : Fin 64)
    (x y : Fin (2 ^ h)) (r : Position h) :
    host r (Sum.inl (t,v,x)) = host r (Sum.inl (t,v,y)) := by
  rcases r with a | (v | d) <;> rfl

/-- All dummy rows, including their anchor incidences, have equal signatures. -/
theorem host_dummy_row_twin {h : ℕ} (x y : Fin (2 ^ h)) (c : Position h) :
    host (Sum.inr (Sum.inr x)) c = host (Sum.inr (Sum.inr y)) c := by
  rcases c with a | (v | d) <;> rfl

/-- All dummy columns, including their anchor incidences, have equal signatures. -/
theorem host_dummy_column_twin {h : ℕ} (x y : Fin (2 ^ h)) (r : Position h) :
    host r (Sum.inr (Sum.inr x)) = host r (Sum.inr (Sum.inr y)) := by
  rcases r with a | (v | d) <;> rfl

/-- The anchor-group label forgets only the coordinate within a group. -/
def anchorGroup {h : ℕ} : Position h → Option (Mode h × Fin 64)
  | Sum.inl (t,u,_) => some (t,u)
  | Sum.inr _ => none

/-- A group-label equality is enough to prove that two full row signatures agree. -/
theorem host_rows_eq_of_anchorGroup {h : ℕ} {r r' : Position h}
    {t : Mode h} {u : Fin 64}
    (hr : anchorGroup r = some (t,u)) (hr' : anchorGroup r' = some (t,u)) :
    ∀ c, host r c = host r' c := by
  rcases r with ⟨t₁,u₁,x⟩ | r
  · rcases r' with ⟨t₂,u₂,y⟩ | r'
    · simp only [anchorGroup, Option.some.injEq, Prod.mk.injEq] at hr hr'
      rcases hr with ⟨rfl,rfl⟩
      rcases hr' with ⟨rfl,rfl⟩
      exact host_anchor_row_twin _ _ x y
    · simp [anchorGroup] at hr'
  · simp [anchorGroup] at hr

/-- The same group-label criterion on the column axis. -/
theorem host_columns_eq_of_anchorGroup {h : ℕ} {c c' : Position h}
    {t : Mode h} {u : Fin 64}
    (hc : anchorGroup c = some (t,u)) (hc' : anchorGroup c' = some (t,u)) :
    ∀ r, host r c = host r c' := by
  rcases c with ⟨t₁,u₁,x⟩ | c
  · rcases c' with ⟨t₂,u₂,y⟩ | c'
    · simp only [anchorGroup, Option.some.injEq, Prod.mk.injEq] at hc hc'
      rcases hc with ⟨rfl,rfl⟩
      rcases hc' with ⟨rfl,rfl⟩
      exact host_anchor_column_twin _ _ x y
    · simp [anchorGroup] at hc'
  · simp [anchorGroup] at hc

/-- A true anchor--anchor entry forces the two modes to coincide. -/
theorem mode_eq_of_host_anchor_true {h : ℕ} {t t' : Mode h}
    {u v : Fin 64} {x y : Fin (2 ^ h)}
    (he : host (Sum.inl (t,u,x)) (Sum.inl (t',v,y)) = true) : t = t' := by
  by_contra hne
  simp [host, hne] at he

/-- In any one mode a non-anchor row can be one in at most one anchor group. -/
theorem nonanchor_row_one_group_unique {h : ℕ}
    (r : VariablePosition h ⊕ Fin (2 ^ h)) (t : Mode h)
    (u v : Fin 64) (x y : Fin (2 ^ h))
    (hu : host (Sum.inr r) (Sum.inl (t,u,x)) = true)
    (hv : host (Sum.inr r) (Sum.inl (t,v,y)) = true) : u = v := by
  have hu' : (u.val = 0 ∧ rowRole t 0 (Sum.inr r)) ∨
      (u.val = 1 ∧ rowRole t 1 (Sum.inr r)) := by
    simpa only [host, decide_eq_true_eq] using hu
  have hv' : (v.val = 0 ∧ rowRole t 0 (Sum.inr r)) ∨
      (v.val = 1 ∧ rowRole t 1 (Sum.inr r)) := by
    simpa only [host, decide_eq_true_eq] using hv
  rcases hu' with ⟨hu₀, hr₀⟩ | ⟨hu₁, hr₁⟩ <;>
    rcases hv' with ⟨hv₀, hs₀⟩ | ⟨hv₁, hs₁⟩
  · exact Fin.ext (hu₀.trans hv₀.symm)
  · exact False.elim (rowRole_disjoint t (Sum.inr r) ⟨hr₀, hs₁⟩)
  · exact False.elim (rowRole_disjoint t (Sum.inr r) ⟨hs₀, hr₁⟩)
  · exact Fin.ext (hu₁.trans hv₁.symm)

/-- In any one mode a non-anchor column can be one in at most one anchor group. -/
theorem nonanchor_column_one_group_unique {h : ℕ}
    (c : VariablePosition h ⊕ Fin (2 ^ h)) (t : Mode h)
    (u v : Fin 64) (x y : Fin (2 ^ h))
    (hu : host (Sum.inl (t,u,x)) (Sum.inr c) = true)
    (hv : host (Sum.inl (t,v,y)) (Sum.inr c) = true) : u = v := by
  have hu' : (u.val = 0 ∧ colRole t 0 (Sum.inr c)) ∨
      (u.val = 1 ∧ colRole t 1 (Sum.inr c)) := by
    simpa only [host, decide_eq_true_eq] using hu
  have hv' : (v.val = 0 ∧ colRole t 0 (Sum.inr c)) ∨
      (v.val = 1 ∧ colRole t 1 (Sum.inr c)) := by
    simpa only [host, decide_eq_true_eq] using hv
  rcases hu' with ⟨hu₀, hr₀⟩ | ⟨hu₁, hr₁⟩ <;>
    rcases hv' with ⟨hv₀, hs₀⟩ | ⟨hv₁, hs₁⟩
  · exact Fin.ext (hu₀.trans hv₀.symm)
  · exact False.elim (colRole_disjoint t (Sum.inr c) ⟨hr₀, hs₁⟩)
  · exact False.elim (colRole_disjoint t (Sum.inr c) ⟨hs₀, hr₁⟩)
  · exact Fin.ext (hu₁.trans hv₁.symm)

end Problem348.Construction

end OAI
end
end

section
section
namespace OAI


/-! Concrete cross-mode and single-mode incidence facts for the canonical host.
These discharge the corresponding premises of abstract anchor rigidity once
an anchor copy has distinct selected anchor groups. -/

namespace Problem348.AnchorRigidity

open Construction

/-- The mode label of a raw anchor position, and `none` off the anchors. -/
def positionMode {h : ℕ} : Position h → Option (Mode h)
  | Sum.inl (t, _, _) => some t
  | Sum.inr _ => none

/-- Group label, ignoring the within-group coordinate. -/
def positionGroup {h : ℕ} : Position h → Option (Mode h × Fin 64)
  | Sum.inl (t, u, _) => some (t, u)
  | Sum.inr _ => none

/-- A selected family uses each anchor group at most once. -/
def DistinctAnchorGroups {h : ℕ} {I : Type uI} (r : I → Position h) : Prop :=
  ∀ i j g, positionGroup (r i) = some g → positionGroup (r j) = some g → i = j

/-- A true entry between anchors forces their modes to agree. -/
theorem host_cross_mode {h : ℕ} (r c : Position h) (t u : Mode h)
    (hr : positionMode r = some t) (hc : positionMode c = some u)
    (hb : host r c = true) : t = u := by
  rcases r with ⟨tr, ur, xr⟩ | r
  · rcases c with ⟨tc, vc, yc⟩ | c
    · simp only [positionMode, Option.some.injEq] at hr hc
      subst tr
      subst tc
      by_contra hne
      simp [host, hne] at hb
    · simp [positionMode] at hc
  · simp [positionMode] at hr

/-- On the columns of one mode, a nonanchor row has ones in only one group. -/
theorem host_nonanchor_row_one_group {h : ℕ}
    (r : VariablePosition h ⊕ Fin (2 ^ h)) (t : Mode h)
    (u v : Fin 64) (x y : Fin (2 ^ h))
    (hu : host (Sum.inr r) (Sum.inl (t, u, x)) = true)
    (hv : host (Sum.inr r) (Sum.inl (t, v, y)) = true) : u = v := by
  change decide ((u.val = 0 ∧ rowRole t 0 (Sum.inr r)) ∨
    (u.val = 1 ∧ rowRole t 1 (Sum.inr r))) = true at hu
  change decide ((v.val = 0 ∧ rowRole t 0 (Sum.inr r)) ∨
    (v.val = 1 ∧ rowRole t 1 (Sum.inr r))) = true at hv
  have hu' := of_decide_eq_true hu
  have hv' := of_decide_eq_true hv
  rcases hu' with ⟨hu0, hr0⟩ | ⟨hu1, hr1⟩
  · rcases hv' with ⟨hv0, _⟩ | ⟨_, hr1⟩
    · exact Fin.ext (hu0.trans hv0.symm)
    · exact False.elim (rowRole_disjoint t (Sum.inr r) ⟨hr0, hr1⟩)
  · rcases hv' with ⟨_, hr0⟩ | ⟨hv1, _⟩
    · exact False.elim (rowRole_disjoint t (Sum.inr r) ⟨hr0, hr1⟩)
    · exact Fin.ext (hu1.trans hv1.symm)

/-- On the rows of one mode, a nonanchor column has ones in only one group. -/
theorem host_nonanchor_col_one_group {h : ℕ}
    (c : VariablePosition h ⊕ Fin (2 ^ h)) (t : Mode h)
    (u v : Fin 64) (x y : Fin (2 ^ h))
    (hu : host (Sum.inl (t, u, x)) (Sum.inr c) = true)
    (hv : host (Sum.inl (t, v, y)) (Sum.inr c) = true) : u = v := by
  change decide ((u.val = 0 ∧ colRole t 0 (Sum.inr c)) ∨
    (u.val = 1 ∧ colRole t 1 (Sum.inr c))) = true at hu
  change decide ((v.val = 0 ∧ colRole t 0 (Sum.inr c)) ∨
    (v.val = 1 ∧ colRole t 1 (Sum.inr c))) = true at hv
  have hu' := of_decide_eq_true hu
  have hv' := of_decide_eq_true hv
  rcases hu' with ⟨hu0, hc0⟩ | ⟨hu1, hc1⟩
  · rcases hv' with ⟨hv0, _⟩ | ⟨_, hc1⟩
    · exact Fin.ext (hu0.trans hv0.symm)
    · exact False.elim (colRole_disjoint t (Sum.inr c) ⟨hc0, hc1⟩)
  · rcases hv' with ⟨_, hc0⟩ | ⟨hv1, _⟩
    · exact False.elim (colRole_disjoint t (Sum.inr c) ⟨hc0, hc1⟩)
    · exact Fin.ext (hu1.trans hv1.symm)

/-- Unit-incidence premise for a selected family of columns with no repeated group. -/
theorem host_nonanchor_row_unit {h : ℕ} {J : Type uJ}
    (r : Position h) (c : J → Position h) (hcgroup : DistinctAnchorGroups c)
    (hr : positionMode r = none) (j k : J) (t : Mode h)
    (hj : positionMode (c j) = some t) (hk : positionMode (c k) = some t)
    (hbj : host r (c j) = true) (hbk : host r (c k) = true) : j = k := by
  rcases r with a | r
  · simp [positionMode] at hr
  rcases hjc : c j with ⟨tj, uj, xj⟩ | cj
  · rcases hkc : c k with ⟨tk, uk, xk⟩ | ck
    · simp only [hjc, hkc, positionMode, Option.some.injEq] at hj hk
      subst tj
      subst tk
      rw [hjc] at hbj
      rw [hkc] at hbk
      have hu := host_nonanchor_row_one_group r t uj uk xj xk hbj hbk
      apply hcgroup j k (t, uj)
      · simp [hjc, positionGroup]
      · simp [hkc, positionGroup, hu]
    · simp [hkc, positionMode] at hk
  · simp [hjc, positionMode] at hj

/-- Unit-incidence premise for a selected family of rows with no repeated group. -/
theorem host_nonanchor_col_unit {h : ℕ} {I : Type uI}
    (r : I → Position h) (c : Position h) (hrgroup : DistinctAnchorGroups r)
    (hc : positionMode c = none) (i k : I) (t : Mode h)
    (hi : positionMode (r i) = some t) (hk : positionMode (r k) = some t)
    (hbi : host (r i) c = true) (hbk : host (r k) c = true) : i = k := by
  rcases c with a | c
  · simp [positionMode] at hc
  rcases hir : r i with ⟨ti, ui, xi⟩ | ri
  · rcases hkr : r k with ⟨tk, uk, xk⟩ | rk
    · simp only [hir, hkr, positionMode, Option.some.injEq] at hi hk
      subst ti
      subst tk
      rw [hir] at hbi
      rw [hkr] at hbk
      have hu := host_nonanchor_col_one_group c t ui uk xi xk hbi hbk
      apply hrgroup i k (t, ui)
      · simp [hir, positionGroup]
      · simp [hkr, positionGroup, hu]
    · simp [hkr, positionMode] at hk
  · simp [hir, positionMode] at hi

end Problem348.AnchorRigidity


/-!
# Concrete canonical-host specialization of anchor rigidity

For `Construction.host`, a dense core forces one common anchor mode.
The twin, signature, density, and cross-mode properties follow from the
canonical entry table.
-/

namespace Problem348.HostAnchorRigidity

open Construction

/-- The mode label of an anchor, and `none` for a non-anchor. -/
def modeLabel {h : ℕ} : Position h → Option (Mode h)
  | Sum.inl (t, _, _) => some t
  | Sum.inr _ => none

/-- The actual dummy positions on either raw axis. -/
def Dummy {h : ℕ} (x : Position h) : Prop :=
  ∃ z, x = Sum.inr (Sum.inr z)

theorem exists_anchor_of_mode {h : ℕ} {x : Position h} {t : Mode h}
    (hx : modeLabel x = some t) :
    ∃ u z, x = Sum.inl (t, u, z) := by
  rcases x with ⟨t', u, z⟩ | a
  · simp only [modeLabel, Option.some.injEq] at hx
    subst t'
    exact ⟨u, z, rfl⟩
  · simp [modeLabel] at hx

theorem exists_nonanchor_of_mode_none {h : ℕ} {x : Position h}
    (hx : modeLabel x = none) :
    ∃ a, x = Sum.inr a := by
  rcases x with a | a
  · simp [modeLabel] at hx
  · exact ⟨a, rfl⟩

theorem exists_dummy_of_dummy {h : ℕ} {x : Position h} (hx : Dummy x) :
    ∃ z, x = Sum.inr (Sum.inr z) := hx

/-- Distinct selected anchor rows cannot have the same mode and group. -/
theorem selected_anchor_rows_unique {h : ℕ}
    (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    {i k : Fin 64} {t : Mode h} {u : Fin 64} {x y : Fin (2 ^ h)}
    (hi : r i = Sum.inl (t, u, x))
    (hk : r k = Sum.inl (t, u, y)) : i = k := by
  apply anchor64_rows_injective
  funext j
  rw [← hcopy i j, ← hcopy k j, hi, hk]
  exact host_anchor_row_twin t u x y (c j)

/-- Distinct selected anchor columns cannot have the same mode and group. -/
theorem selected_anchor_columns_unique {h : ℕ}
    (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    {j k : Fin 64} {t : Mode h} {v : Fin 64} {x y : Fin (2 ^ h)}
    (hj : c j = Sum.inl (t, v, x))
    (hk : c k = Sum.inl (t, v, y)) : j = k := by
  apply anchor64_columns_injective
  funext i
  change anchor64 i j = anchor64 i k
  rw [← hcopy i j, ← hcopy i k, hj, hk]
  exact host_anchor_column_twin t v x y (r i)

/-- At most one selected row can be dummy, because all dummy rows are twins. -/
theorem selected_dummy_rows_unique {h : ℕ}
    (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    {i k : Fin 64} (hi : Dummy (r i)) (hk : Dummy (r k)) : i = k := by
  obtain ⟨x, hx⟩ := exists_dummy_of_dummy hi
  obtain ⟨y, hy⟩ := exists_dummy_of_dummy hk
  apply anchor64_rows_injective
  funext j
  rw [← hcopy i j, ← hcopy k j, hx, hy]
  exact host_dummy_row_twin x y (c j)

/-- At most one selected column can be dummy. -/
theorem selected_dummy_columns_unique {h : ℕ}
    (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    {j k : Fin 64} (hj : Dummy (c j)) (hk : Dummy (c k)) : j = k := by
  obtain ⟨x, hx⟩ := exists_dummy_of_dummy hj
  obtain ⟨y, hy⟩ := exists_dummy_of_dummy hk
  apply anchor64_columns_injective
  funext i
  change anchor64 i j = anchor64 i k
  rw [← hcopy i j, ← hcopy i k, hx, hy]
  exact host_dummy_column_twin x y (r i)

/-- A one between two anchors forces their modes to coincide. -/
theorem selected_cross_mode {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    (i j : Fin 64) (t u : Mode h)
    (hi : modeLabel (r i) = some t) (hj : modeLabel (c j) = some u)
    (hij : anchor64 i j = true) : t = u := by
  obtain ⟨v, x, hx⟩ := exists_anchor_of_mode hi
  obtain ⟨w, y, hy⟩ := exists_anchor_of_mode hj
  rw [← hcopy i j, hx, hy] at hij
  by_contra hne
  simp [host, hne] at hij

/-- On the selected anchors of a fixed mode a non-anchor row has at most one one. -/
theorem selected_nonanchor_row_unit {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    (i : Fin 64) (hi : modeLabel (r i) = none) (j k : Fin 64) (t : Mode h)
    (hj : modeLabel (c j) = some t) (hk : modeLabel (c k) = some t)
    (hij : anchor64 i j = true) (hik : anchor64 i k = true) : j = k := by
  obtain ⟨a, hx⟩ := exists_nonanchor_of_mode_none hi
  obtain ⟨v, y, hy⟩ := exists_anchor_of_mode hj
  obtain ⟨w, z, hz⟩ := exists_anchor_of_mode hk
  rw [← hcopy i j, hx, hy] at hij
  rw [← hcopy i k, hx, hz] at hik
  have hvw : v = w := nonanchor_row_one_group_unique a t v w y z hij hik
  subst w
  exact selected_anchor_columns_unique r c hcopy hy hz

/-- On the selected anchors of a fixed mode a non-anchor column has at most one one. -/
theorem selected_nonanchor_column_unit {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    (j : Fin 64) (hj : modeLabel (c j) = none) (i k : Fin 64) (t : Mode h)
    (hi : modeLabel (r i) = some t) (hk : modeLabel (r k) = some t)
    (hij : anchor64 i j = true) (hkj : anchor64 k j = true) : i = k := by
  obtain ⟨a, hx⟩ := exists_nonanchor_of_mode_none hj
  obtain ⟨u, y, hy⟩ := exists_anchor_of_mode hi
  obtain ⟨v, z, hz⟩ := exists_anchor_of_mode hk
  rw [← hcopy i j, hy, hx] at hij
  rw [← hcopy k j, hz, hx] at hkj
  have huv : u = v := nonanchor_column_one_group_unique a t u v y z hij hkj
  subst v
  exact selected_anchor_rows_unique r c hcopy hy hz

/-- Concrete host rigidity assuming a dense core, with twin, signature,
density, and cross-mode properties following from the host entries. -/
theorem mode_constant_of_dense_core {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    (hcore :
      AnchorRigidity.DenseAnchorCore anchor64 (modeLabel ∘ r) (modeLabel ∘ c) (Dummy ∘ c) ∨
      AnchorRigidity.DenseAnchorCore (fun j i => anchor64 i j)
        (modeLabel ∘ c) (modeLabel ∘ r) (Dummy ∘ r)) :
    ∃ t : Mode h, (∀ i, modeLabel (r i) = some t) ∧
      (∀ j, modeLabel (c j) = some t) := by
  apply AnchorRigidity.rigidity anchor64 (modeLabel ∘ r) (modeLabel ∘ c)
    (Dummy ∘ r) (Dummy ∘ c) hcore
  · intro i k hi hk
    exact selected_dummy_rows_unique r c hcopy hi hk
  · intro j k hj hk
    exact selected_dummy_columns_unique r c hcopy hj hk
  · exact selected_cross_mode r c hcopy
  · exact selected_nonanchor_row_unit r c hcopy
  · exact selected_nonanchor_column_unit r c hcopy
  · intro i
    exact (by decide : 2 ≤ 58).trans (anchor64_row_ones i)
  · intro j
    exact (by decide : 2 ≤ 48).trans (anchor64_column_ones j)

end Problem348.HostAnchorRigidity

end OAI
end
end

section
section
namespace OAI

/-!
# Structural bridges for anchor pinning

Group uniqueness and no-shattering give pinning criteria independent of
the host construction.
-/


namespace Problem348.AnchorBridge

/-- Distinct pattern rows prevent a copy from repeating any host row class
whose members have identical entries. -/
theorem row_labels_injective {I : Type uI} {J : Type uJ} {R : Type uR} {C : Type uC} {G : Type uG}
    (H : I → J → Bool) (A : R → C → Bool)
    (row : I → R) (col : J → C) (label : R → G)
    (hcopy : ∀ i j, A (row i) (col j) = H i j)
    (hrows : Function.Injective H)
    (hlabel : ∀ r s, label r = label s → A r = A s) :
    Function.Injective (fun i => label (row i)) := by
  intro i j hij
  apply hrows
  funext c
  rw [← hcopy, ← hcopy]
  exact congrFun (hlabel (row i) (row j) hij) (col c)

/-- The column version of `row_labels_injective`. -/
theorem col_labels_injective {I : Type uI} {J : Type uJ} {R : Type uR} {C : Type uC} {G : Type uG}
    (H : I → J → Bool) (A : R → C → Bool)
    (row : I → R) (col : J → C) (label : C → G)
    (hcopy : ∀ i j, A (row i) (col j) = H i j)
    (hcols : Function.Injective (fun j => fun i => H i j))
    (hlabel : ∀ c d, label c = label d → ∀ r, A r c = A r d) :
    Function.Injective (fun j => label (col j)) := by
  intro i j hij
  apply hcols
  funext r
  change H r i = H r j
  rw [← hcopy, ← hcopy]
  exact hlabel (col i) (col j) hij (row r)

/-- The 32 rows carrying all binary words in the fixed anchor. -/
def wordRow (a : Fin 32) : Fin 64 := ⟨32 + a.val, by omega⟩

/-- The five columns carrying the word coordinates in the fixed anchor. -/
def wordCol (b : Fin 5) : Fin 64 := ⟨59 + b.val, by omega⟩

@[simp] theorem wordCol_injective : Function.Injective wordCol := by
  intro a b hab
  apply Fin.ext
  have := congrArg Fin.val hab
  simp only [wordCol] at this
  omega

/-- If both axes had at most 32 initial anchor positions, the complete-word
submatrix would shatter five non-anchor columns.  Thus the position at index
32 is an anchor on at least one axis. -/
theorem anchor_at_32_or_anchor_at_32 {R : Type uR} {C : Type uC}
    (H : Fin 64 → Fin 64 → Bool) (A : R → C → Bool)
    (row : Fin 64 → R) (col : Fin 64 → C)
    (anchorR : R → Prop) (anchorC : C → Prop)
    (hcopy : ∀ i j, A (row i) (col j) = H i j)
    (hcol : Function.Injective col)
    (hprefixR : ∀ i j, i ≤ j → anchorR (row j) → anchorR (row i))
    (hprefixC : ∀ i j, i ≤ j → anchorC (col j) → anchorC (col i))
    (hwords : ∀ w : Fin 5 → Bool, ∃ a : Fin 32,
      ∀ b : Fin 5, H (wordRow a) (wordCol b) = w b)
    (hnoshatter : ∀ cs : Fin 5 → C, Function.Injective cs →
      (∀ b, ¬ anchorC (cs b)) → ∃ w : Fin 5 → Bool,
        ∀ r, ¬ anchorR r → ∃ b, A r (cs b) ≠ w b) :
    anchorR (row ⟨32, by decide⟩) ∨ anchorC (col ⟨32, by decide⟩) := by
  classical
  by_contra h
  push Not at h
  have hr : ∀ a : Fin 32, ¬ anchorR (row (wordRow a)) := by
    intro a ha
    apply h.1
    exact hprefixR _ _ (by simp only [wordRow, Fin.le_iff_val_le_val]; omega) ha
  have hc : ∀ b : Fin 5, ¬ anchorC (col (wordCol b)) := by
    intro b hb
    apply h.2
    exact hprefixC _ _ (by simp only [wordCol, Fin.le_iff_val_le_val]; omega) hb
  obtain ⟨w, hw⟩ := hnoshatter (fun b => col (wordCol b))
    (hcol.comp wordCol_injective) hc
  obtain ⟨a, ha⟩ := hwords w
  obtain ⟨b, hb⟩ := hw (row (wordRow a)) (hr a)
  exact hb ((hcopy _ _).trans (ha b))

/-- A downward-closed predicate holding at index `m` holds at at least
`m+1` indices. -/
theorem prefix_card_lower_bound {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (m : Fin n) (hprefix : ∀ i j, i ≤ j → P j → P i) (hm : P m) :
    m.val + 1 ≤ (Finset.univ.filter P).card := by
  classical
  calc
    m.val + 1 = (Finset.Iic m).card := by simp
    _ ≤ (Finset.univ.filter P).card := by
      apply Finset.card_le_card
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,
        hprefix i m (Finset.mem_Iic.mp hi) hm⟩

/-- An increasing self-map of a finite ordered interval uses every label
in the prescribed order. -/
theorem increasing_labels_eq_id {n : ℕ} (f : Fin n → Fin n)
    (hf : StrictMono f) : f = id := by
  funext i
  exact le_antisymm (hf.le_id i) (hf.id_le i)

/-- Any class of host rows with identical entries is used at most once
in a copy with distinct pattern rows. In particular this applies to the
dummy row class. -/
theorem card_selected_row_class_le_one {I : Type uI} {J : Type uJ} {R : Type uR} {C : Type uC}
    [Fintype I] (H : I → J → Bool) (A : R → C → Bool)
    (row : I → R) (col : J → C) (P : R → Prop) [DecidablePred P]
    (hcopy : ∀ i j, A (row i) (col j) = H i j)
    (hrows : Function.Injective H)
    (hclass : ∀ r s, P r → P s → A r = A s) :
    (Finset.univ.filter (fun i => P (row i))).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  apply hrows
  funext c
  rw [← hcopy, ← hcopy]
  exact congrFun (hclass (row i) (row j)
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2) (col c)

/-- Column version of the single-use class bound. -/
theorem card_selected_col_class_le_one {I : Type uI} {J : Type uJ} {R : Type uR} {C : Type uC}
    [Fintype J] (H : I → J → Bool) (A : R → C → Bool)
    (row : I → R) (col : J → C) (P : C → Prop) [DecidablePred P]
    (hcopy : ∀ i j, A (row i) (col j) = H i j)
    (hcols : Function.Injective (fun j => fun i => H i j))
    (hclass : ∀ c d, P c → P d → ∀ r, A r c = A r d) :
    (Finset.univ.filter (fun j => P (col j))).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  apply hcols
  funext r
  change H r i = H r j
  rw [← hcopy, ← hcopy]
  exact hclass (col i) (col j)
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 (row r)

end Problem348.AnchorBridge

end OAI
end
end

section
section
namespace OAI

/-!
# Structural anchor bridges for the fixed pattern

The generic bridges are specialized to the explicit `anchor64` definition.
-/


namespace Problem348.AnchorBridge

/-- The exact anchor realizes every five-bit word on the specified suffix. -/
theorem anchor64_word_block_complete (w : Fin 5 → Bool) :
    ∃ a : Fin 32, ∀ b : Fin 5,
      anchor64 (wordRow a) (wordCol b) = w b := by
  obtain ⟨a, ha⟩ := anchorWord_bijective.2 w
  refine ⟨a, fun b => ?_⟩
  have hb := congrFun ha b
  simpa only [anchorWord, wordRow, wordCol, Nat.add_comm] using hb

/-- An exact anchor copy has at least 33 anchors on one of its two axes,
provided anchors form prefixes and non-anchor rows do not shatter five
non-anchor columns. -/
theorem anchor64_anchor_majority {R : Type uR} {C : Type uC}
    (A : R → C → Bool) (row : Fin 64 → R) (col : Fin 64 → C)
    (anchorR : R → Prop) (anchorC : C → Prop)
    [DecidablePred anchorR] [DecidablePred anchorC]
    (hcopy : ∀ i j, A (row i) (col j) = anchor64 i j)
    (hcol : Function.Injective col)
    (hprefixR : ∀ i j, i ≤ j → anchorR (row j) → anchorR (row i))
    (hprefixC : ∀ i j, i ≤ j → anchorC (col j) → anchorC (col i))
    (hnoshatter : ∀ cs : Fin 5 → C, Function.Injective cs →
      (∀ b, ¬ anchorC (cs b)) → ∃ w : Fin 5 → Bool,
        ∀ r, ¬ anchorR r → ∃ b, A r (cs b) ≠ w b) :
    33 ≤ (Finset.univ.filter (fun i => anchorR (row i))).card ∨
    33 ≤ (Finset.univ.filter (fun j => anchorC (col j))).card := by
  rcases anchor_at_32_or_anchor_at_32 anchor64 A row col anchorR anchorC
    hcopy hcol hprefixR hprefixC anchor64_word_block_complete hnoshatter with hr | hc
  · exact Or.inl (prefix_card_lower_bound _ ⟨32, by decide⟩ hprefixR hr)
  · exact Or.inr (prefix_card_lower_bound _ ⟨32, by decide⟩ hprefixC hc)

/-- A row class of equal host rows occurs at most once in an anchor copy. -/
theorem anchor64_row_class_single_use {R : Type uR} {C : Type uC}
    (A : R → C → Bool) (row : Fin 64 → R) (col : Fin 64 → C)
    (P : R → Prop) [DecidablePred P]
    (hcopy : ∀ i j, A (row i) (col j) = anchor64 i j)
    (hclass : ∀ r s, P r → P s → A r = A s) :
    (Finset.univ.filter (fun i => P (row i))).card ≤ 1 :=
  card_selected_row_class_le_one anchor64 A row col P hcopy
    anchor64_rows_injective hclass

/-- A column class of equal host columns occurs at most once in an anchor copy. -/
theorem anchor64_col_class_single_use {R : Type uR} {C : Type uC}
    (A : R → C → Bool) (row : Fin 64 → R) (col : Fin 64 → C)
    (P : C → Prop) [DecidablePred P]
    (hcopy : ∀ i j, A (row i) (col j) = anchor64 i j)
    (hclass : ∀ c d, P c → P d → ∀ r, A r c = A r d) :
    (Finset.univ.filter (fun j => P (col j))).card ≤ 1 :=
  card_selected_col_class_le_one anchor64 A row col P hcopy
    anchor64_columns_injective hclass

end Problem348.AnchorBridge

end OAI
end
end

section
section
namespace OAI

/-!
A direct qualitative proof of the non-anchor trace obstruction.
No enumeration of suffix generators is needed.

If all binary words occur, any two selected columns in the same class can be
separated by a singleton word, contradicting their suffix monotonicity.
Thus all five classes are distinct. The word 11110 then uses four classes,
while a variable row uses at most three and a dummy row is all ones.
-/


namespace Problem348.DirectNonshattering

open Finset

/-- A surjective family of class-monotone words separates the column classes. -/
theorem class_injective_of_surjective
    {R : Type uR} {C : Type uC} {K : Type uK} [DecidableEq C] [LinearOrder K]
    {L : Type uL} (classOf : C → L) (key : C → K) (A : R → C → Bool)
    (hmono : ∀ r i j, classOf i = classOf j → key i ≤ key j →
      A r i = true → A r j = true)
    (hsurj : Function.Surjective A) : Function.Injective classOf := by
  intro i j hij
  by_contra hne
  rcases le_total (key i) (key j) with hle | hle
  · obtain ⟨r, hr⟩ := hsurj (fun x => decide (x = i))
    have hi : A r i = true := by rw [hr]; simp
    have hj : A r j = true := hmono r i j hij hle hi
    rw [hr] at hj
    simp [Ne.symm hne] at hj
  · obtain ⟨r, hr⟩ := hsurj (fun x => decide (x = j))
    have hj : A r j = true := by rw [hr]; simp
    have hi : A r i = true := hmono r j i hij.symm hle hj
    rw [hr] at hi
    simp [hne] at hi

/-- General form: `q + 2` columns cannot be shattered by classwise suffix
rows supported on at most `q` classes, together with all-one rows. -/
theorem not_surjective_of_card
    {R : Type uR} {C : Type uC} {L : Type uL} {K : Type uK} [Fintype C] [DecidableEq C] [DecidableEq L]
    [LinearOrder K] (q : ℕ) (hcard : q + 2 ≤ Fintype.card C)
    (classOf : C → L) (key : C → K) (A : R → C → Bool)
    (hmono : ∀ r i j, classOf i = classOf j → key i ≤ key j →
      A r i = true → A r j = true)
    (hsupport : ∀ r,
      ((univ.filter (fun i => A r i = true)).image classOf).card ≤ q ∨
      (∀ i, A r i = true)) :
    ¬ Function.Surjective A := by
  classical
  intro hsurj
  have hinj := class_injective_of_surjective classOf key A hmono hsurj
  have : Nonempty C := Fintype.card_pos_iff.mp (by omega)
  let j : C := Classical.arbitrary C
  obtain ⟨r, hr⟩ := hsurj (fun i => decide (i ≠ j))
  rcases hsupport r with hs | hd
  · rw [hr, card_image_of_injective _ hinj] at hs
    change (univ.filter (fun i : C => decide (i ≠ j) = true)).card ≤ q at hs
    have hfilter : (univ.filter (fun i : C => decide (i ≠ j) = true)) =
        univ.erase j := by
      ext i
      simp
    rw [hfilter, card_erase_of_mem (mem_univ j), card_univ] at hs
    omega
  · have hj := hd j
    rw [hr] at hj
    simp at hj

/-- No family with suffixes in at most three classes, plus all-one rows,
realizes every binary word on five columns. -/
theorem not_surjective_five
    {R : Type uR} {L : Type uL} {K : Type uK} [DecidableEq L] [LinearOrder K]
    (classOf : Fin 5 → L) (key : Fin 5 → K) (A : R → Fin 5 → Bool)
    (hmono : ∀ r i j, classOf i = classOf j → key i ≤ key j →
      A r i = true → A r j = true)
    (hsupport : ∀ r,
      ((univ.filter (fun i => A r i = true)).image classOf).card ≤ 3 ∨
      (∀ i, A r i = true)) :
    ¬ Function.Surjective A :=
  not_surjective_of_card 3 (by simp) classOf key A hmono hsupport

/-- The conclusion in a form convenient for a five-column shattering test. -/
theorem exists_missing_word
    {R : Type uR} {L : Type uL} {K : Type uK} [DecidableEq L] [LinearOrder K]
    (classOf : Fin 5 → L) (key : Fin 5 → K) (A : R → Fin 5 → Bool)
    (hmono : ∀ r i j, classOf i = classOf j → key i ≤ key j →
      A r i = true → A r j = true)
    (hsupport : ∀ r,
      ((univ.filter (fun i => A r i = true)).image classOf).card ≤ 3 ∨
      (∀ i, A r i = true)) :
    ∃ w : Fin 5 → Bool, ∀ r, A r ≠ w := by
  simpa only [Function.Surjective, not_forall, not_exists] using
    not_surjective_five classOf key A hmono hsupport

/-- A column equal to one in every row also rules out shattering immediately. -/
theorem not_surjective_of_constant_column
    {R : Type uR} {C : Type uC} (A : R → C → Bool) (j : C)
    (hj : ∀ r, A r j = true) : ¬ Function.Surjective A := by
  intro hsurj
  obtain ⟨r, hr⟩ := hsurj (fun _ => false)
  have h := hj r
  rw [hr] at h
  cases h

/-- Whole-host version.  Dummy columns are all ones, and every non-dummy row
has at most three active classes among the non-dummy columns.  The chosen five
columns need not be ordered or even assumed distinct. -/
theorem not_surjective_selected_columns
    {R : Type uR} {C : Type uC} {L : Type uL} {K : Type uK} [Fintype C] [DecidableEq C] [DecidableEq L]
    [LinearOrder K]
    (A : R → C → Bool) (dummyRow : R → Prop) (dummyColumn : C → Prop)
    [DecidablePred dummyColumn]
    (classOf : C → L) (key : C → K)
    (hrow : ∀ r, dummyRow r → ∀ c, A r c = true)
    (hcolumn : ∀ c, dummyColumn c → ∀ r, A r c = true)
    (hmono : ∀ r, ¬ dummyRow r → ∀ c d,
      ¬ dummyColumn c → ¬ dummyColumn d → classOf c = classOf d →
      key c ≤ key d → A r c = true → A r d = true)
    (hsupport : ∀ r, ¬ dummyRow r →
      ((univ.filter (fun c => ¬ dummyColumn c ∧ A r c = true)).image classOf).card ≤ 3)
    (selected : Fin 5 → C) :
    ¬ Function.Surjective (fun r i => A r (selected i)) := by
  classical
  by_cases hdummy : ∃ i, dummyColumn (selected i)
  · obtain ⟨i, hi⟩ := hdummy
    exact not_surjective_of_constant_column (fun r j => A r (selected j)) i
      (hcolumn (selected i) hi)
  · have hnondummy : ∀ i, ¬ dummyColumn (selected i) := by
      simpa only [not_exists] using hdummy
    apply not_surjective_five (classOf ∘ selected) (key ∘ selected)
      (fun r i => A r (selected i))
    · intro r i j hij hle hi
      by_cases hr : dummyRow r
      · exact hrow r hr (selected j)
      · exact hmono r hr (selected i) (selected j)
          (hnondummy i) (hnondummy j) hij hle hi
    · intro r
      by_cases hr : dummyRow r
      · exact Or.inr (fun i => hrow r hr (selected i))
      · left
        refine (card_le_card (show
          (univ.filter (fun i => A r (selected i) = true)).image (classOf ∘ selected) ⊆
          (univ.filter (fun c => ¬ dummyColumn c ∧ A r c = true)).image classOf
          from ?_)).trans (hsupport r hr)
        intro l hl
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hl
        exact mem_image.mpr ⟨selected i,
          mem_filter.mpr ⟨mem_univ _, hnondummy i, (mem_filter.mp hi).2⟩, rfl⟩


/-- On `k+2` coordinates, classwise monotone traces with at most `k`
active classes, allowing also the constant-one trace, omit a Boolean word.
The rank need not be injective within a class. -/
theorem exists_missing_word_with_zero {ρ : Type uRho} {β : Type uBeta} [DecidableEq β] (k : ℕ)
    (cls : Fin (k + 2) → β) (key : Fin (k + 2) → ℕ)
    (trace : ρ → Fin (k + 2) → Bool)
    (hup : ∀ r a b, cls a = cls b → key a ≤ key b →
      trace r a = true → trace r b = true)
    (hsupport : ∀ r, (∀ j, trace r j = true) ∨
      ((Finset.univ.filter (fun j => trace r j = true)).image cls).card ≤ k) :
    ∃ word : Fin (k + 2) → Bool,
      (∃ j, word j = false) ∧ ∀ r, trace r ≠ word := by
  classical
  by_cases hinj : Function.Injective cls
  · let word : Fin (k + 2) → Bool := fun j => decide (j ≠ 0)
    refine ⟨word, ⟨0, by simp [word]⟩, ?_⟩
    intro r heq
    rcases hsupport r with hall | hsmall
    · have hzero := hall 0
      rw [heq] at hzero
      simp [word] at hzero
    · rw [heq] at hsmall
      rw [Finset.card_image_of_injective _ hinj] at hsmall
      have hset : Finset.univ.filter (fun j : Fin (k + 2) => word j = true) =
          Finset.univ.erase 0 := by
        ext j
        simp [word]
      rw [hset] at hsmall
      simp at hsmall
  · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hinj
    have hp : ∃ a b : Fin (k + 2),
        a ≠ b ∧ cls a = cls b ∧ key a ≤ key b := by
      rcases le_total (key a) (key b) with h | h
      · exact ⟨a, b, hne, hab, h⟩
      · exact ⟨b, a, hne.symm, hab.symm, h⟩
    obtain ⟨a, b, hne, hab, hkey⟩ := hp
    let word : Fin (k + 2) → Bool := fun j => decide (j = a)
    refine ⟨word, ⟨b, by simp [word, hne.symm]⟩, ?_⟩
    intro r heq
    have ha : trace r a = true := by simp [heq, word]
    have hb := hup r a b hab hkey ha
    simp [heq, word, hne.symm] at hb

/-- Coordinatewise form of the missing-word theorem. -/
theorem exists_missing_word_pointwise {ρ : Type uRho} {β : Type uBeta} [DecidableEq β] (k : ℕ)
    (cls : Fin (k + 2) → β) (key : Fin (k + 2) → ℕ)
    (trace : ρ → Fin (k + 2) → Bool)
    (hup : ∀ r a b, cls a = cls b → key a ≤ key b →
      trace r a = true → trace r b = true)
    (hsupport : ∀ r, (∀ j, trace r j = true) ∨
      ((Finset.univ.filter (fun j => trace r j = true)).image cls).card ≤ k) :
    ∃ word : Fin (k + 2) → Bool, ∀ r, ∃ j, trace r j ≠ word j := by
  classical
  obtain ⟨word, _, hw⟩ := exists_missing_word_with_zero k cls key trace hup hsupport
  refine ⟨word, fun r => ?_⟩
  by_contra h
  push Not at h
  exact hw r (funext h)

/-- Matrix-facing form, handling both dummy columns and dummy rows.
No injectivity assumption on the selected columns is needed. -/
theorem matrix_missing_word {R : Type uR} {C : Type uC} {β : Type uBeta} [DecidableEq β] (k : ℕ)
    (A : R → C → Bool) (cols : Fin (k + 2) → C)
    (cls : C → β) (key : C → ℕ) (dummyRow : R → Prop) (dummyCol : C → Prop)
    (hdummyRow : ∀ r, dummyRow r → ∀ c, A r c = true)
    (hdummyCol : ∀ c, dummyCol c → ∀ r, A r c = true)
    (hup : ∀ r, ¬ dummyRow r → ∀ a b,
      ¬ dummyCol a → ¬ dummyCol b → cls a = cls b → key a ≤ key b →
      A r a = true → A r b = true)
    (hsupport : ∀ r, ¬ dummyRow r →
      (∀ j, ¬ dummyCol (cols j)) →
      ((Finset.univ.filter (fun j => A r (cols j) = true)).image
        (cls ∘ cols)).card ≤ k) :
    ∃ word : Fin (k + 2) → Bool, ∀ r, ∃ j, A r (cols j) ≠ word j := by
  classical
  by_cases hd : ∃ j, dummyCol (cols j)
  · obtain ⟨j, hj⟩ := hd
    refine ⟨fun _ => false, fun r => ⟨j, ?_⟩⟩
    simp [hdummyCol (cols j) hj r]
  · push Not at hd
    apply exists_missing_word_pointwise k (cls ∘ cols) (key ∘ cols)
      (fun r j => A r (cols j))
    · intro r a b hab hkey ha
      by_cases hr : dummyRow r
      · exact hdummyRow r hr (cols b)
      · exact hup r hr (cols a) (cols b) (hd a) (hd b) hab hkey ha
    · intro r
      by_cases hr : dummyRow r
      · exact Or.inl (fun j => hdummyRow r hr (cols j))
      · exact Or.inr (hsupport r hr hd)

/-- An explicit cover by at most `k` column classes is enough for the
support premise. This form avoids cardinal computations on selected columns. -/
theorem matrix_missing_word_of_class_cover {R : Type uR} {C : Type uC} {β : Type uBeta} [DecidableEq β] (k : ℕ)
    (A : R → C → Bool) (cols : Fin (k + 2) → C)
    (cls : C → β) (key : C → ℕ) (dummyRow : R → Prop) (dummyCol : C → Prop)
    (hdummyRow : ∀ r, dummyRow r → ∀ c, A r c = true)
    (hdummyCol : ∀ c, dummyCol c → ∀ r, A r c = true)
    (hup : ∀ r, ¬ dummyRow r → ∀ a b,
      ¬ dummyCol a → ¬ dummyCol b → cls a = cls b → key a ≤ key b →
      A r a = true → A r b = true)
    (hcover : ∀ r, ¬ dummyRow r → ∃ S : Finset β, S.card ≤ k ∧
      ∀ c, ¬ dummyCol c → A r c = true → cls c ∈ S) :
    ∃ word : Fin (k + 2) → Bool, ∀ r, ∃ j, A r (cols j) ≠ word j := by
  classical
  apply matrix_missing_word k A cols cls key dummyRow dummyCol hdummyRow hdummyCol hup
  intro r hr hcols
  obtain ⟨S, hS, hmem⟩ := hcover r hr
  apply le_trans (Finset.card_le_card ?_) hS
  intro c hc
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
  exact hmem (cols j) (hcols j) (Finset.mem_filter.mp hj).2

end Problem348.DirectNonshattering

end OAI
end
end

section
section
namespace OAI

/-!
# Nonshattering for the concrete canonical host

This is a direct application of the qualitative five-column obstruction to
`Problem348.Construction.host`. It needs no axis order and no injectivity
assumption on the five selected non-anchor columns.
-/


namespace Problem348.Construction

open Finset

noncomputable section

/-- The two kinds of non-anchor positions, without their outer sum tag. -/
abbrev NonanchorPosition (h : ℕ) := VariablePosition h ⊕ Fin (2 ^ h)

/-- Column-class labels for the non-anchor induced submatrix. The dummy label
is irrelevant because dummy columns are treated separately. -/
def nonanchorClass {h : ℕ} : NonanchorPosition h → ℕ
  | Sum.inl v => v.1.val
  | Sum.inr _ => 0

def nonanchorKey {h : ℕ} : NonanchorPosition h → ℕ
  | Sum.inl v => node v
  | Sum.inr _ => 0

def nonanchorDummy {h : ℕ} : NonanchorPosition h → Prop
  | Sum.inl _ => False
  | Sum.inr _ => True

instance {h : ℕ} (x : NonanchorPosition h) : Decidable (nonanchorDummy x) := by
  cases x <;> simp only [nonanchorDummy] <;> infer_instance

/-- The three class labels that can contain ones in a variable row. -/
def variableSupportLabels {h : ℕ} (r : VariablePosition h) : Finset ℕ :=
  {r.1.val, 2 * (depth r - 1), 2 * (depth r - 1) + 1}

theorem variableSupportLabels_card_le {h : ℕ} (r : VariablePosition h) :
    (variableSupportLabels r).card ≤ 3 := by
  exact Finset.card_le_three

/-- The constant-class suffix property, stated for the actual host kernel. -/
theorem variableEntry_mono_class {h : ℕ} (r c d : VariablePosition h)
    (hclass : c.1.val = d.1.val) (hnode : node c ≤ node d)
    (hc : variableEntry r c = true) : variableEntry r d = true := by
  have hd : depth c = depth d := by simp only [depth, hclass]
  have hp : plus c = plus d := by simp only [plus, hclass]
  unfold variableEntry at hc ⊢
  simp only [hd, hp] at hc
  split_ifs at hc ⊢ <;> simp_all <;> omega

/-- A true variable entry has one of the three possible column-class labels. -/
theorem variableEntry_mem_support {h : ℕ} (r c : VariablePosition h)
    (hc : variableEntry r c = true) : c.1.val ∈ variableSupportLabels r := by
  have hr := r.1.isLt
  have hcv := c.1.isLt
  simp only [variableSupportLabels, Finset.mem_insert, Finset.mem_singleton]
  unfold variableEntry at hc
  simp only [depth, plus, decide_eq_true_eq] at hc ⊢
  split_ifs at hc <;> simp_all <;> omega

/-- The induced matrix on all non-anchor positions misses a five-bit word. -/
theorem nonanchor_host_not_surjective (h : ℕ)
    (selected : Fin 5 → NonanchorPosition h) :
    ¬ Function.Surjective
      (fun r : NonanchorPosition h =>
        fun i => host (Sum.inr r) (Sum.inr (selected i))) := by
  apply DirectNonshattering.not_surjective_selected_columns
    (fun r c : NonanchorPosition h => host (Sum.inr r) (Sum.inr c))
    nonanchorDummy nonanchorDummy nonanchorClass nonanchorKey
  · intro r hr c
    cases r with
    | inl r => exact False.elim hr
    | inr r => cases c <;> rfl
  · intro c hc r
    cases c with
    | inl c => exact False.elim hc
    | inr c => cases r <;> rfl
  · intro r hr c d hc hd hclass hnode he
    cases r with
    | inr r => exact False.elim (hr trivial)
    | inl r =>
      cases c with
      | inr c => exact False.elim (hc trivial)
      | inl c =>
        cases d with
        | inr d => exact False.elim (hd trivial)
        | inl d => exact variableEntry_mono_class r c d hclass hnode he
  · intro r hr
    cases r with
    | inr r => exact False.elim (hr trivial)
    | inl r =>
      apply (Finset.card_le_card ?_).trans (variableSupportLabels_card_le r)
      intro a ha
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨_, hnd, he⟩ := Finset.mem_filter.mp hc
      cases c with
      | inr c => exact False.elim (hnd trivial)
      | inl c => exact variableEntry_mem_support r c he

/-- The actual host, stated using its outer position type. This avoids any
choice of a separate non-anchor enumeration in anchor-rigidity applications. -/
theorem host_nonanchor_missing_word {h : ℕ} (columns : Fin 5 → Position h)
    (hcolumns : ∀ i, ∃ c : NonanchorPosition h, columns i = Sum.inr c) :
    ∃ w : Fin 5 → Bool, ∀ r : Position h,
      (∃ a : NonanchorPosition h, r = Sum.inr a) →
      (fun i => host r (columns i)) ≠ w := by
  classical
  choose selected hselected using hcolumns
  obtain ⟨w, hw⟩ : ∃ w : Fin 5 → Bool, ∀ r : NonanchorPosition h,
      (fun i => host (Sum.inr r) (Sum.inr (selected i))) ≠ w := by
    simpa only [Function.Surjective, not_forall, not_exists] using
      nonanchor_host_not_surjective h selected
  refine ⟨w, ?_⟩
  rintro r ⟨a, rfl⟩
  simpa only [hselected] using hw a

/-- Restricting to any collection of non-anchor rows still misses a word.
This is the form used for the final 32 rows of an alleged anchor copy. -/
theorem host_nonanchor_submatrix_not_surjective {h : ℕ} {R : Type uR}
    (rows : R → Position h) (columns : Fin 5 → Position h)
    (hrows : ∀ r, ∃ a : NonanchorPosition h, rows r = Sum.inr a)
    (hcolumns : ∀ i, ∃ c : NonanchorPosition h, columns i = Sum.inr c) :
    ¬ Function.Surjective (fun r i => host (rows r) (columns i)) := by
  obtain ⟨w, hw⟩ := host_nonanchor_missing_word columns hcolumns
  intro hsurj
  obtain ⟨r, hr⟩ := hsurj w
  exact hw (rows r) (hrows r) hr

/-- The outer sum tag gives a convenient intrinsic non-anchor predicate. -/
@[simp] theorem exists_nonanchor_iff_not_isLeft {h : ℕ} (x : Position h) :
    (∃ a : NonanchorPosition h, x = Sum.inr a) ↔ ¬ x.isLeft := by
  cases x <;> simp

/-- Pointwise missing-word property for concrete anchor rigidity. -/
theorem host_nonanchor_missing_entry {h : ℕ} (columns : Fin 5 → Position h)
    (hcolumns : ∀ i, ¬ (columns i).isLeft) :
    ∃ w : Fin 5 → Bool, ∀ r : Position h, ¬ r.isLeft →
      ∃ i, host r (columns i) ≠ w i := by
  obtain ⟨w, hw⟩ := host_nonanchor_missing_word columns
    (fun i => (exists_nonanchor_iff_not_isLeft (columns i)).mpr (hcolumns i))
  refine ⟨w, ?_⟩
  intro r hr
  have hne := hw r ((exists_nonanchor_iff_not_isLeft r).mpr hr)
  exact not_forall.mp (fun he => hne (funext he))

/-- The subtype formulation also avoids making any non-anchor choices. -/
theorem host_nonanchor_subtype_not_surjective {h : ℕ}
    (columns : Fin 5 → Position h) (hcolumns : ∀ i, ¬ (columns i).isLeft) :
    ¬ Function.Surjective
      (fun r : {x : Position h // ¬ x.isLeft} => fun i => host r.val (columns i)) := by
  apply host_nonanchor_submatrix_not_surjective
    (fun r : {x : Position h // ¬ x.isLeft} => r.val) columns
  · intro r
    exact (exists_nonanchor_iff_not_isLeft r.val).mpr r.property
  · intro i
    exact (exists_nonanchor_iff_not_isLeft (columns i)).mpr (hcolumns i)

end
end Problem348.Construction

end OAI
end
end

section
section
namespace OAI

/-! Assembly of the exact anchor-majority and concrete-host rigidity steps. -/
namespace Problem348.HostAnchorRigidity

open Construction AnchorRigidity

/-- An exact anchor copy is automatically injective on the column axis. -/
theorem selected_columns_injective {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j) : Function.Injective c := by
  intro j k hjk
  apply anchor64_columns_injective
  funext i
  change anchor64 i j = anchor64 i k
  rw [← hcopy i j, ← hcopy i k, hjk]

/-- An exact anchor copy is automatically injective on the row axis. -/
theorem selected_rows_injective {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j) : Function.Injective r := by
  intro i k hik
  apply anchor64_rows_injective
  funext j
  rw [← hcopy i j, ← hcopy k j, hik]

/-- Variable-column sparseness on a selected prefix. -/
def ColumnSparse {h : ℕ} (r c : Fin 64 → Position h) : Prop :=
  ∀ j, modeLabel (c j) = none → ¬ Dummy (c j) →
    (∀ i ∈ firstCore, ∃ t, modeLabel (r i) = some t) →
    (firstCore.filter fun i => anchor64 i j = true).card ≤ 4

/-- Variable-row sparseness on a selected prefix. -/
def RowSparse {h : ℕ} (r c : Fin 64 → Position h) : Prop :=
  ∀ i, modeLabel (r i) = none → ¬ Dummy (r i) →
    (∀ j ∈ firstCore, ∃ t, modeLabel (c j) = some t) →
    (firstCore.filter fun j => anchor64 i j = true).card ≤ 4

/-- Prefix anchoring plus actual variable sparseness pins all positions to one mode. -/
theorem mode_constant_of_prefix {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    (hprefix : (∀ i : Fin 64, i.val < 32 → ∃ t, modeLabel (r i) = some t) ∨
      (∀ j : Fin 64, j.val < 32 → ∃ t, modeLabel (c j) = some t))
    (hcs : ColumnSparse r c) (hrs : RowSparse r c) :
    ∃ t : Mode h, (∀ i, modeLabel (r i) = some t) ∧
      (∀ j, modeLabel (c j) = some t) := by
  apply anchor64_rigidity_of_prefix (modeLabel ∘ r) (modeLabel ∘ c)
    (Dummy ∘ r) (Dummy ∘ c) hprefix hcs hrs
  · intro i k hi hk
    exact selected_dummy_rows_unique r c hcopy hi hk
  · intro j k hj hk
    exact selected_dummy_columns_unique r c hcopy hj hk
  · exact selected_cross_mode r c hcopy
  · exact selected_nonanchor_row_unit r c hcopy
  · exact selected_nonanchor_column_unit r c hcopy

/-- No five-column shattering and the anchor-before-nonanchor order give a
majority; prefix rigidity then yields one common mode. -/
theorem mode_constant_of_no_shattering {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    (row_initial : ∀ i j, i ≤ j → modeLabel (r j) ≠ none → modeLabel (r i) ≠ none)
    (col_initial : ∀ i j, i ≤ j → modeLabel (c j) ≠ none → modeLabel (c i) ≠ none)
    (hnoshatter : ∀ cs : Fin 5 → Position h, Function.Injective cs →
      (∀ b, modeLabel (cs b) = none) → ∃ w : Fin 5 → Bool,
        ∀ x, modeLabel x = none → ∃ b, host x (cs b) ≠ w b)
    (hcs : ColumnSparse r c) (hrs : RowSparse r c) :
    ∃ t : Mode h, (∀ i, modeLabel (r i) = some t) ∧
      (∀ j, modeLabel (c j) = some t) := by
  classical
  have hm := AnchorBridge.anchor64_anchor_majority host r c
    (fun x => modeLabel x ≠ none) (fun x => modeLabel x ≠ none)
    hcopy (selected_columns_injective r c hcopy) row_initial col_initial
    (by
      intro cs hcs hnone
      obtain ⟨w, hw⟩ := hnoshatter cs hcs (fun b => not_not.mp (hnone b))
      exact ⟨w, fun x hx => hw x (not_not.mp hx)⟩)
  have hm' :
      32 < (Finset.univ.filter fun i => (modeLabel (r i)).isSome).card ∨
      32 < (Finset.univ.filter fun j => (modeLabel (c j)).isSome).card := by
    simpa only [Option.isSome_iff_ne_none, Nat.lt_iff_add_one_le] using hm
  have hp := prefix_alternative_of_majority (modeLabel ∘ r) (modeLabel ∘ c)
    row_initial col_initial hm'
  exact mode_constant_of_prefix r c hcopy hp hcs hrs

/-- The within-mode group order enjoyed by an increasingly selected axis. -/
def GroupsMonotone {h : ℕ} (r : Fin 64 → Position h) : Prop :=
  ∀ (i j : Fin 64), i ≤ j → ∀ (t : Mode h) (u v : Fin 64)
    (x y : Fin (2 ^ h)), r i = Sum.inl (t, u, x) →
      r j = Sum.inl (t, v, y) → u ≤ v

/-- Once one common mode is known, group uniqueness and the actual group
order identify its representatives in the exact pattern order. -/
theorem representatives_of_mode_constant {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    (hrow : GroupsMonotone r) (hcol : GroupsMonotone c)
    {t : Mode h} (hmr : ∀ i, modeLabel (r i) = some t)
    (hmc : ∀ j, modeLabel (c j) = some t) :
    ∃ a b : Fin 64 → Fin (2 ^ h),
      (∀ i, r i = Sum.inl (t, i, a i)) ∧
      (∀ j, c j = Sum.inl (t, j, b j)) := by
  classical
  choose u a ha using fun i => exists_anchor_of_mode (hmr i)
  choose v b hb using fun j => exists_anchor_of_mode (hmc j)
  have hu : Monotone u := by
    intro i j hij
    exact hrow i j hij t (u i) (u j) (a i) (a j) (ha i) (ha j)
  have hv : Monotone v := by
    intro i j hij
    exact hcol i j hij t (v i) (v j) (b i) (b j) (hb i) (hb j)
  have hui : Function.Injective u := by
    intro i j hij
    apply selected_anchor_rows_unique r c hcopy (ha i)
    simpa only [hij] using ha j
  have hvi : Function.Injective v := by
    intro i j hij
    apply selected_anchor_columns_unique r c hcopy (hb i)
    simpa only [hij] using hb j
  have hu_id : ∀ i, u i = i := by
    intro i
    have hs := hu.strictMono_of_injective hui
    exact le_antisymm (hs.le_id i) (hs.id_le i)
  have hv_id : ∀ i, v i = i := by
    intro i
    have hs := hv.strictMono_of_injective hvi
    exact le_antisymm (hs.le_id i) (hs.id_le i)
  refine ⟨a, b, ?_, ?_⟩
  · intro i
    simpa only [hu_id i] using ha i
  · intro j
    simpa only [hv_id j] using hb j

/-- Full anchor representative conclusion assuming initial anchor segments,
nonshattering, variable sparseness, and within-mode group order. -/
theorem representatives_of_no_shattering {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    (row_initial : ∀ i j, i ≤ j → modeLabel (r j) ≠ none → modeLabel (r i) ≠ none)
    (col_initial : ∀ i j, i ≤ j → modeLabel (c j) ≠ none → modeLabel (c i) ≠ none)
    (hnoshatter : ∀ cs : Fin 5 → Position h, Function.Injective cs →
      (∀ b, modeLabel (cs b) = none) → ∃ w : Fin 5 → Bool,
        ∀ x, modeLabel x = none → ∃ b, host x (cs b) ≠ w b)
    (hcs : ColumnSparse r c) (hrs : RowSparse r c)
    (hrow : GroupsMonotone r) (hcol : GroupsMonotone c) :
    ∃ (t : Mode h) (a b : Fin 64 → Fin (2 ^ h)),
      (∀ i, r i = Sum.inl (t, i, a i)) ∧
      (∀ j, c j = Sum.inl (t, j, b j)) := by
  obtain ⟨t, hmr, hmc⟩ := mode_constant_of_no_shattering r c hcopy
    row_initial col_initial hnoshatter hcs hrs
  obtain ⟨a, b, ha, hb⟩ := representatives_of_mode_constant r c hcopy hrow hcol hmr hmc
  exact ⟨t, a, b, ha, hb⟩

/-- The concrete canonical host supplies the missing-word hypothesis,
without any ordering or injectivity condition on the five columns. -/
theorem actual_nonshattering {h : ℕ} (cs : Fin 5 → Position h)
    (hcs : ∀ b, modeLabel (cs b) = none) :
    ∃ w : Fin 5 → Bool, ∀ x, modeLabel x = none →
      ∃ b, host x (cs b) ≠ w b := by
  classical
  obtain ⟨w, hw⟩ := host_nonanchor_missing_word cs
    (fun b => exists_nonanchor_of_mode_none (hcs b))
  refine ⟨w, ?_⟩
  intro x hx
  have hne := hw x (exists_nonanchor_of_mode_none hx)
  by_contra heq
  push Not at heq
  exact hne (funext heq)

/-- Concrete-host anchor pinning assuming axis-order and sparse-core
conditions; nonshattering follows from the host entries. -/
theorem representatives_of_sparse {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    (row_initial : ∀ i j, i ≤ j → modeLabel (r j) ≠ none → modeLabel (r i) ≠ none)
    (col_initial : ∀ i j, i ≤ j → modeLabel (c j) ≠ none → modeLabel (c i) ≠ none)
    (hcs : ColumnSparse r c) (hrs : RowSparse r c)
    (hrow : GroupsMonotone r) (hcol : GroupsMonotone c) :
    ∃ (t : Mode h) (a b : Fin 64 → Fin (2 ^ h)),
      (∀ i, r i = Sum.inl (t, i, a i)) ∧
      (∀ j, c j = Sum.inl (t, j, b j)) := by
  exact representatives_of_no_shattering r c hcopy row_initial col_initial
    (fun cs _ hin => actual_nonshattering cs hin) hcs hrs hrow hcol

end Problem348.HostAnchorRigidity

end OAI
end
end

section
section
namespace OAI

/-!
Mode-incidence bounds. Active modes have levels 1 through h, while
variable positions have levels 0 through h. At level h the plus and minus
blocks coincide.
-/


namespace Problem348.ModeIncidence

inductive Kind where
  | vertical (sign : Bool)
  | horizontal (sign parity : Bool)
  deriving DecidableEq, Fintype

abbrev Mode := ℕ × Kind

/-- Leaf positions have both sign names; other positions have their own sign. -/
def hasSign (h depth : ℕ) (own requested : Bool) : Prop :=
  depth = h ∨ own = requested

/-- Incidence with either row role of a mode. -/
def rowIncident (h depth : ℕ) (sign parity : Bool) (t : Mode) : Prop :=
  1 ≤ t.1 ∧ t.1 ≤ h ∧
    match t.2 with
    | .vertical s => (depth = t.1 ∨ depth + 1 = t.1) ∧ hasSign h depth sign s
    | .horizontal s p => depth = t.1 ∧ hasSign h depth sign s ∧ parity = p

/-- Incidence with either column role of a mode. -/
def colIncident (h depth : ℕ) (sign parity : Bool) (t : Mode) : Prop :=
  1 ≤ t.1 ∧ t.1 ≤ h ∧
    match t.2 with
    | .vertical s => depth + 1 = t.1 ∧ hasSign h depth sign s
    | .horizontal s p => hasSign h depth sign s ∧
        (depth + 1 = t.1 ∨ (depth = t.1 ∧ parity = p))

/-- Three possible modes for an internal variable row. Boundary levels may
remove some of these modes. -/
def internalRowModes (depth : ℕ) (sign parity : Bool) : Finset Mode :=
  {(depth, .vertical sign), (depth + 1, .vertical sign),
    (depth, .horizontal sign parity)}

/-- The four possible modes for a shared leaf row. -/
def leafRowModes (h : ℕ) (parity : Bool) : Finset Mode :=
  {(h, .vertical false), (h, .vertical true),
    (h, .horizontal false parity), (h, .horizontal true parity)}

/-- Four possible modes for an internal variable column. -/
def internalColModes (depth : ℕ) (sign parity : Bool) : Finset Mode :=
  {(depth + 1, .vertical sign), (depth + 1, .horizontal sign false),
    (depth + 1, .horizontal sign true), (depth, .horizontal sign parity)}

/-- The two possible modes for a shared leaf column. -/
def leafColModes (h : ℕ) (parity : Bool) : Finset Mode :=
  {(h, .horizontal false parity), (h, .horizontal true parity)}

theorem rowIncident_internal {h depth : ℕ} {sign parity : Bool} {t : Mode}
    (hd : depth < h) (ht : rowIncident h depth sign parity t) :
    t ∈ internalRowModes depth sign parity := by
  rcases t with ⟨level, kind⟩
  rcases kind with s | ⟨s, p⟩ <;> dsimp [rowIncident] at ht
  · rcases ht with ⟨_, _, hlevel, hsign⟩
    have hs : sign = s := hsign.resolve_left (Nat.ne_of_lt hd)
    subst s
    rcases hlevel with rfl | rfl <;> simp [internalRowModes]
  · rcases ht with ⟨_, _, hlevel, hsign, hp⟩
    have hs : sign = s := hsign.resolve_left (Nat.ne_of_lt hd)
    subst s
    subst p
    subst level
    simp [internalRowModes]

theorem rowIncident_leaf {h : ℕ} {sign parity : Bool} {t : Mode}
    (ht : rowIncident h h sign parity t) : t ∈ leafRowModes h parity := by
  rcases t with ⟨level, kind⟩
  rcases kind with s | ⟨s, p⟩ <;> dsimp [rowIncident] at ht
  · rcases ht with ⟨_, hbound, hlevel, _⟩
    have heq : level = h := by omega
    subst level
    cases s <;> simp [leafRowModes]
  · rcases ht with ⟨_, _, hlevel, _, hp⟩
    subst level
    subst p
    cases s <;> simp [leafRowModes]

theorem colIncident_internal {h depth : ℕ} {sign parity : Bool} {t : Mode}
    (hd : depth < h) (ht : colIncident h depth sign parity t) :
    t ∈ internalColModes depth sign parity := by
  rcases t with ⟨level, kind⟩
  rcases kind with s | ⟨s, p⟩ <;> dsimp [colIncident] at ht
  · rcases ht with ⟨_, _, hlevel, hsign⟩
    have hs : sign = s := hsign.resolve_left (Nat.ne_of_lt hd)
    subst s
    subst level
    simp [internalColModes]
  · rcases ht with ⟨_, _, hsign, hlevel⟩
    have hs : sign = s := hsign.resolve_left (Nat.ne_of_lt hd)
    subst s
    rcases hlevel with hlevel | ⟨hlevel, hp⟩
    · subst level
      cases p <;> simp [internalColModes]
    · subst level
      subst p
      simp [internalColModes]

theorem colIncident_leaf {h : ℕ} {sign parity : Bool} {t : Mode}
    (ht : colIncident h h sign parity t) : t ∈ leafColModes h parity := by
  rcases t with ⟨level, kind⟩
  rcases kind with s | ⟨s, p⟩ <;> dsimp [colIncident] at ht
  · rcases ht with ⟨_, hbound, hlevel, _⟩
    omega
  · rcases ht with ⟨_, hbound, _, hlevel⟩
    rcases hlevel with hbad | ⟨heq, hp⟩
    · omega
    · subst level
      subst p
      cases s <;> simp [leafColModes]

/-- An internal row participates in at most three modes. -/
theorem card_internalRowModes_le (depth : ℕ) (sign parity : Bool) :
    (internalRowModes depth sign parity).card ≤ 3 := by
  simp only [internalRowModes]
  exact Finset.card_insert_le _ _ |>.trans (Nat.succ_le_succ
    (Finset.card_insert_le _ _ |>.trans (by simp)))

/-- A leaf row participates in at most four modes. -/
theorem card_leafRowModes_le (h : ℕ) (parity : Bool) :
    (leafRowModes h parity).card ≤ 4 := by
  simp [leafRowModes]

/-- A variable column below the leaf level participates in at most four modes. -/
theorem card_internalColModes_le (depth : ℕ) (sign parity : Bool) :
    (internalColModes depth sign parity).card ≤ 4 := by
  unfold internalColModes
  exact Finset.card_insert_le _ _ |>.trans (Nat.succ_le_succ
    (Finset.card_insert_le _ _ |>.trans (Nat.succ_le_succ
      (Finset.card_insert_le _ _ |>.trans (by simp)))))

/-- A leaf column participates in at most two modes. -/
theorem card_leafColModes_le (h : ℕ) (parity : Bool) :
    (leafColModes h parity).card ≤ 2 := by
  simp [leafColModes]

/-- Formulation independent of the particular finite enumeration of valid modes. -/
theorem card_row_incident_le_four {h depth : ℕ} {sign parity : Bool}
    (hd : depth ≤ h) (modes : Finset Mode)
    (hmodes : ∀ t ∈ modes, rowIncident h depth sign parity t) :
    modes.card ≤ 4 := by
  rcases lt_or_eq_of_le hd with hd | rfl
  · have hsub : modes ⊆ internalRowModes depth sign parity := by
      intro t ht
      exact rowIncident_internal hd (hmodes t ht)
    exact (Finset.card_le_card hsub).trans
      ((card_internalRowModes_le depth sign parity).trans (by decide))
  · have hsub : modes ⊆ leafRowModes depth parity := by
      intro t ht
      exact rowIncident_leaf (hmodes t ht)
    exact (Finset.card_le_card hsub).trans (card_leafRowModes_le depth parity)

/-- Formulation independent of the particular finite enumeration of valid modes. -/
theorem card_col_incident_le_four {h depth : ℕ} {sign parity : Bool}
    (hd : depth ≤ h) (modes : Finset Mode)
    (hmodes : ∀ t ∈ modes, colIncident h depth sign parity t) :
    modes.card ≤ 4 := by
  rcases lt_or_eq_of_le hd with hd | rfl
  · have hsub : modes ⊆ internalColModes depth sign parity := by
      intro t ht
      exact colIncident_internal hd (hmodes t ht)
    exact (Finset.card_le_card hsub).trans (card_internalColModes_le depth sign parity)
  · have hsub : modes ⊆ leafColModes depth parity := by
      intro t ht
      exact colIncident_leaf (hmodes t ht)
    exact (Finset.card_le_card hsub).trans
      ((card_leafColModes_le depth parity).trans (by decide))

/-- A generic sparse-trace transfer: at most one chosen one-entry per mode. -/
theorem card_ones_le_of_mode_bound {α : Type uAlpha} [DecidableEq α]
    (positions : Finset α) (mode : α → Mode) (entry : α → Bool)
    (incident : Mode → Prop) (bound : ℕ)
    (hbound : ∀ modes : Finset Mode,
      (∀ t ∈ modes, incident t) → modes.card ≤ bound)
    (hincident : ∀ x ∈ positions, entry x = true → incident (mode x))
    (hunique : ∀ x ∈ positions, ∀ y ∈ positions,
      entry x = true → entry y = true → mode x = mode y → x = y) :
    (positions.filter (fun x => entry x = true)).card ≤ bound := by
  have hinjective : Set.InjOn mode
      (↑(positions.filter (fun x => entry x = true)) : Set α) := by
    intro x hx y hy heq
    obtain ⟨hx, hxe⟩ := Finset.mem_filter.mp hx
    obtain ⟨hy, hye⟩ := Finset.mem_filter.mp hy
    exact hunique x hx y hy hxe hye heq
  rw [← Finset.card_image_of_injOn hinjective]
  apply hbound
  intro t ht
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨hx, hxe⟩ := Finset.mem_filter.mp hx
  exact hincident x hx hxe

/-- Against anchor representatives, a variable row has at most four ones,
provided one-entries in the same mode use the same representative. -/
theorem card_row_ones_le_four {α : Type uAlpha} [DecidableEq α]
    {h depth : ℕ} {sign parity : Bool} (hd : depth ≤ h)
    (positions : Finset α) (mode : α → Mode) (entry : α → Bool)
    (hincident : ∀ x ∈ positions, entry x = true →
      rowIncident h depth sign parity (mode x))
    (hunique : ∀ x ∈ positions, ∀ y ∈ positions,
      entry x = true → entry y = true → mode x = mode y → x = y) :
    (positions.filter (fun x => entry x = true)).card ≤ 4 :=
  card_ones_le_of_mode_bound positions mode entry
    (rowIncident h depth sign parity) 4
    (card_row_incident_le_four hd) hincident hunique

/-- The symmetric sparse-trace statement for variable columns. -/
theorem card_col_ones_le_four {α : Type uAlpha} [DecidableEq α]
    {h depth : ℕ} {sign parity : Bool} (hd : depth ≤ h)
    (positions : Finset α) (mode : α → Mode) (entry : α → Bool)
    (hincident : ∀ x ∈ positions, entry x = true →
      colIncident h depth sign parity (mode x))
    (hunique : ∀ x ∈ positions, ∀ y ∈ positions,
      entry x = true → entry y = true → mode x = mode y → x = y) :
    (positions.filter (fun x => entry x = true)).card ≤ 4 :=
  card_ones_le_of_mode_bound positions mode entry
    (colIncident h depth sign parity) 4
    (card_col_incident_le_four hd) hincident hunique

end Problem348.ModeIncidence

end OAI
end
end

section
section
namespace OAI

/-!
The mode-incidence count bounds sparse anchor traces for the actual
finite host.
-/


namespace Problem348.Construction

private def incidenceKind (k : ℕ) : ModeIncidence.Kind :=
  if k < 2 then .vertical (decide (k = 0))
  else .horizontal (decide (k < 4)) (decide (k % 2 = 1))

/-- Decode the canonical six-mode enumeration into the incidence labels. -/
def incidenceMode {h : ℕ} (t : Mode h) : ModeIncidence.Mode :=
  (level t, incidenceKind (kind t))

/-- Boolean parity, in the convention used by ModeIncidence. -/
def nodeParity {h : ℕ} (v : VariablePosition h) : Bool :=
  decide (node v % 2 = 1)

private theorem incidenceKind_injective {a b : ℕ} (ha : a < 6) (hb : b < 6)
    (hab : incidenceKind a = incidenceKind b) : a = b := by
  interval_cases a <;> interval_cases b <;> simp_all [incidenceKind]

 theorem incidenceMode_injective (h : ℕ) :
    Function.Injective (@incidenceMode h) := by
  intro t u htu
  have hl : level t = level u := congrArg Prod.fst htu
  have hk := incidenceKind_injective (kind_lt t) (kind_lt u)
    (congrArg Prod.snd htu)
  apply Fin.ext
  dsimp [level] at hl
  dsimp [kind] at hk
  omega

 theorem rowRole_incident {h : ℕ} (t : Mode h) (j : Fin 2)
    (v : VariablePosition h) (hv : rowRole t j (.inr (.inl v))) :
    ModeIncidence.rowIncident h (depth v) (plus v) (nodeParity v)
      (incidenceMode t) := by
  have hp := level_pos t
  have hl := level_le t
  have hk := kind_lt t
  interval_cases e : kind t <;> fin_cases j <;>
    simp_all [rowRole, incidenceMode, incidenceKind, ModeIncidence.rowIncident,
      ModeIncidence.hasSign, AtLevel, nodeParity]

 theorem colRole_incident {h : ℕ} (t : Mode h) (j : Fin 2)
    (v : VariablePosition h) (hv : colRole t j (.inr (.inl v))) :
    ModeIncidence.colIncident h (depth v) (plus v) (nodeParity v)
      (incidenceMode t) := by
  have hp := level_pos t
  have hl := level_le t
  have hk := kind_lt t
  interval_cases e : kind t <;> fin_cases j <;>
    simp_all [colRole, incidenceMode, incidenceKind, ModeIncidence.colIncident,
      ModeIncidence.hasSign, AtLevel, nodeParity]

/-- The actual canonical variable row meets at most four modes. -/
theorem card_rowRole_modes_le_four {h : ℕ} (v : VariablePosition h)
    (s : Finset (Mode h))
    (hs : ∀ t ∈ s, ∃ j, rowRole t j (.inr (.inl v))) : s.card ≤ 4 := by
  rw [← Finset.card_image_of_injective s (incidenceMode_injective h)]
  apply ModeIncidence.card_row_incident_le_four (depth_le v)
  intro t ht
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨j, hj⟩ := hs u hu
  exact rowRole_incident u j v hj

/-- The actual canonical variable column meets at most four modes. -/
theorem card_colRole_modes_le_four {h : ℕ} (v : VariablePosition h)
    (s : Finset (Mode h))
    (hs : ∀ t ∈ s, ∃ j, colRole t j (.inr (.inl v))) : s.card ≤ 4 := by
  rw [← Finset.card_image_of_injective s (incidenceMode_injective h)]
  apply ModeIncidence.card_col_incident_le_four (depth_le v)
  intro t ht
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨j, hj⟩ := hs u hu
  exact colRole_incident u j v hj

/-- A nonanchor row has at most one one-bearing anchor group in each mode. -/
theorem row_anchor_ones_unique_group {h : ℕ}
    (x : VariablePosition h ⊕ Fin (2 ^ h))
    (a b : AnchorPosition h)
    (ha : host (.inr x) (.inl a) = true)
    (hb : host (.inr x) (.inl b) = true)
    (hm : a.1 = b.1) : a.2.1 = b.2.1 := by
  rcases a with ⟨t, u, ax⟩
  rcases b with ⟨t', v, bx⟩
  dsimp at hm ⊢
  subst t'
  simp only [host, decide_eq_true_eq] at ha hb
  rcases ha with ⟨hu, hr⟩ | ⟨hu, hr⟩ <;>
    rcases hb with ⟨hv, hs⟩ | ⟨hv, hs⟩
  · exact Fin.ext (by omega)
  · exact False.elim (rowRole_disjoint t (.inr x) ⟨hr, hs⟩)
  · exact False.elim (rowRole_disjoint t (.inr x) ⟨hs, hr⟩)
  · exact Fin.ext (by omega)

/-- The corresponding unit-signature fact for a nonanchor column. -/
theorem col_anchor_ones_unique_group {h : ℕ}
    (x : VariablePosition h ⊕ Fin (2 ^ h))
    (a b : AnchorPosition h)
    (ha : host (.inl a) (.inr x) = true)
    (hb : host (.inl b) (.inr x) = true)
    (hm : a.1 = b.1) : a.2.1 = b.2.1 := by
  rcases a with ⟨t, u, ax⟩
  rcases b with ⟨t', v, bx⟩
  dsimp at hm ⊢
  subst t'
  simp only [host, decide_eq_true_eq] at ha hb
  rcases ha with ⟨hu, hr⟩ | ⟨hu, hr⟩ <;>
    rcases hb with ⟨hv, hs⟩ | ⟨hv, hs⟩
  · exact Fin.ext (by omega)
  · exact False.elim (colRole_disjoint t (.inr x) ⟨hr, hs⟩)
  · exact False.elim (colRole_disjoint t (.inr x) ⟨hs, hr⟩)
  · exact Fin.ext (by omega)

/-- The concrete sparse-anchor-trace conclusion for arbitrary indexed anchor
representatives: no group is represented twice among the selected indices. -/
theorem card_variable_row_anchor_ones_le_four {h : ℕ} {α : Type uAlpha}
    [DecidableEq α] (v : VariablePosition h) (s : Finset α)
    (a : α → AnchorPosition h)
    (hgroups : Set.InjOn (fun x => ((a x).1, (a x).2.1)) (s : Set α)) :
    (s.filter (fun x => host (.inr (.inl v)) (.inl (a x)) = true)).card ≤ 4 := by
  classical
  apply ModeIncidence.card_row_ones_le_four
    (sign := plus v) (parity := nodeParity v) (depth_le v) s
    (fun x => incidenceMode (a x).1)
    (fun x => host (.inr (.inl v)) (.inl (a x)))
  · intro x hx hentry
    have hrole : ((a x).2.1.val = 0 ∧ rowRole (a x).1 0 (.inr (.inl v))) ∨
        ((a x).2.1.val = 1 ∧ rowRole (a x).1 1 (.inr (.inl v))) := by
      simpa only [host, decide_eq_true_eq] using hentry
    rcases hrole with ⟨_, hr⟩ | ⟨_, hr⟩
    · exact rowRole_incident (a x).1 0 v hr
    · exact rowRole_incident (a x).1 1 v hr
  · intro x hx y hy hxe hye hm
    have hm' : (a x).1 = (a y).1 := incidenceMode_injective h hm
    have hg : (a x).2.1 = (a y).2.1 :=
      row_anchor_ones_unique_group (.inl v) (a x) (a y) hxe hye hm'
    exact hgroups hx hy (Prod.ext hm' hg)

/-- The concrete sparse-anchor-trace conclusion for a variable column. -/
theorem card_variable_col_anchor_ones_le_four {h : ℕ} {α : Type uAlpha}
    [DecidableEq α] (v : VariablePosition h) (s : Finset α)
    (a : α → AnchorPosition h)
    (hgroups : Set.InjOn (fun x => ((a x).1, (a x).2.1)) (s : Set α)) :
    (s.filter (fun x => host (.inl (a x)) (.inr (.inl v)) = true)).card ≤ 4 := by
  classical
  apply ModeIncidence.card_col_ones_le_four
    (sign := plus v) (parity := nodeParity v) (depth_le v) s
    (fun x => incidenceMode (a x).1)
    (fun x => host (.inl (a x)) (.inr (.inl v)))
  · intro x hx hentry
    have hrole : ((a x).2.1.val = 0 ∧ colRole (a x).1 0 (.inr (.inl v))) ∨
        ((a x).2.1.val = 1 ∧ colRole (a x).1 1 (.inr (.inl v))) := by
      simpa only [host, decide_eq_true_eq] using hentry
    rcases hrole with ⟨_, hr⟩ | ⟨_, hr⟩
    · exact colRole_incident (a x).1 0 v hr
    · exact colRole_incident (a x).1 1 v hr
  · intro x hx y hy hxe hye hm
    have hm' : (a x).1 = (a y).1 := incidenceMode_injective h hm
    have hg : (a x).2.1 = (a y).2.1 :=
      col_anchor_ones_unique_group (.inl v) (a x) (a y) hxe hye hm'
    exact hgroups hx hy (Prod.ext hm' hg)

end Problem348.Construction

end OAI
end
end

section
section
namespace OAI

/-!
Sparsity for arbitrary selected raw host positions.
Only the selected core is assumed to consist of anchors; outside it the
selection may include variable and dummy positions.
-/

noncomputable section
namespace Problem348.Construction.SelectedAnchors

/-- Anchor mode and group, forgetting the irrelevant within-group offset. -/
def label {h : ℕ} : Position h → Option (Mode h × Fin 64)
  | .inl a => some (a.1, a.2.1)
  | .inr _ => none

/-- The mode classifier used by the abstract rigidity theorem. -/
def mode {h : ℕ} : Position h → Option (Mode h)
  | .inl a => some a.1
  | .inr _ => none

/-- Group uniqueness only concerns anchors, so it permits many nonanchors. -/
def GroupInjective {I : Type uI} {h : ℕ} (f : I → Position h) : Prop :=
  ∀ i j a b, f i = .inl a → f j = .inl b →
    a.1 = b.1 → a.2.1 = b.2.1 → i = j

/-- Restrict the actual sparse-row theorem to an arbitrary selected anchor core. -/
theorem variable_row_core_card_le_four {I : Type uI} [DecidableEq I] {h : ℕ}
    (f : I → Position h) (S : Finset I) (v : VariablePosition h)
    (hanchor : ∀ i ∈ S, ∃ a, f i = .inl a)
    (hgroups : Set.InjOn (fun i => label (f i)) (S : Set I)) :
    (S.filter (fun i => host (.inr (.inl v)) (f i) = true)).card ≤ 4 := by
  classical
  let a : S → AnchorPosition h := fun i => Classical.choose (hanchor i i.property)
  have ha (i : S) : f i = .inl (a i) := Classical.choose_spec (hanchor i i.property)
  have hg : Set.InjOn (fun i : S => ((a i).1, (a i).2.1)) S.attach := by
    intro i hi j hj hij
    apply Subtype.ext
    apply hgroups i.property j.property
    simp only [ha, label]
    exact congrArg some hij
  have hb := card_variable_row_anchor_ones_le_four v S.attach a hg
  simp only [← ha] at hb
  have he := congrArg Finset.card
    (Finset.filter_attach (fun i : I => host (.inr (.inl v)) (f i) = true) S)
  simp only [Finset.card_map, Finset.card_attach] at he
  exact he ▸ hb

/-- The transpose restriction to a selected anchor core. -/
theorem variable_col_core_card_le_four {I : Type uI} [DecidableEq I] {h : ℕ}
    (f : I → Position h) (S : Finset I) (v : VariablePosition h)
    (hanchor : ∀ i ∈ S, ∃ a, f i = .inl a)
    (hgroups : Set.InjOn (fun i => label (f i)) (S : Set I)) :
    (S.filter (fun i => host (f i) (.inr (.inl v)) = true)).card ≤ 4 := by
  classical
  let a : S → AnchorPosition h := fun i => Classical.choose (hanchor i i.property)
  have ha (i : S) : f i = .inl (a i) := Classical.choose_spec (hanchor i i.property)
  have hg : Set.InjOn (fun i : S => ((a i).1, (a i).2.1)) S.attach := by
    intro i hi j hj hij
    apply Subtype.ext
    apply hgroups i.property j.property
    simp only [ha, label]
    exact congrArg some hij
  have hb := card_variable_col_anchor_ones_le_four v S.attach a hg
  simp only [← ha] at hb
  have he := congrArg Finset.card
    (Finset.filter_attach (fun i : I => host (f i) (.inr (.inl v)) = true) S)
  simp only [Finset.card_map, Finset.card_attach] at he
  exact he ▸ hb

/-- The structural group-uniqueness property gives label injectivity on a core. -/
theorem GroupInjective.injOn {I : Type uI} {h : ℕ} {f : I → Position h}
    (hf : GroupInjective f) (S : Set I)
    (hanchor : ∀ i ∈ S, ∃ a, f i = .inl a) :
    Set.InjOn (fun i => label (f i)) S := by
  intro i hi j hj hij
  obtain ⟨a, ha⟩ := hanchor i hi
  obtain ⟨b, hb⟩ := hanchor j hj
  have hab : (a.1, a.2.1) = (b.1, b.2.1) := by
    simpa only [ha, hb, label, Option.some.injEq] using hij
  exact hf i j a b ha hb (congrArg (fun x : Mode h × Fin 64 => x.1) hab)
    (congrArg (fun x : Mode h × Fin 64 => x.2) hab)

/-- Exact nonanchor-row unit hypothesis of the abstract rigidity theorem. -/
theorem nonanchor_row_unit {I : Type uI} {h : ℕ}
    (f : I → Position h) (hf : GroupInjective f)
    (r : VariablePosition h ⊕ Fin (2 ^ h)) (i j : I) (t : Mode h)
    (hi : mode (f i) = some t) (hj : mode (f j) = some t)
    (hri : host (.inr r) (f i) = true)
    (hrj : host (.inr r) (f j) = true) : i = j := by
  cases hfi : f i with
  | inr x => simp [hfi, mode] at hi
  | inl a =>
    cases hfj : f j with
    | inr x => simp [hfj, mode] at hj
    | inl b =>
      have hm : a.1 = b.1 := by simpa [hfi, hfj, mode] using hi.trans hj.symm
      have hg : a.2.1 = b.2.1 := row_anchor_ones_unique_group r a b
        (by simpa [hfi] using hri) (by simpa [hfj] using hrj) hm
      exact hf i j a b hfi hfj hm hg

/-- Exact nonanchor-column unit hypothesis of the abstract rigidity theorem. -/
theorem nonanchor_col_unit {I : Type uI} {h : ℕ}
    (f : I → Position h) (hf : GroupInjective f)
    (c : VariablePosition h ⊕ Fin (2 ^ h)) (i j : I) (t : Mode h)
    (hi : mode (f i) = some t) (hj : mode (f j) = some t)
    (hci : host (f i) (.inr c) = true)
    (hcj : host (f j) (.inr c) = true) : i = j := by
  cases hfi : f i with
  | inr x => simp [hfi, mode] at hi
  | inl a =>
    cases hfj : f j with
    | inr x => simp [hfj, mode] at hj
    | inl b =>
      have hm : a.1 = b.1 := by simpa [hfi, hfj, mode] using hi.trans hj.symm
      have hg : a.2.1 = b.2.1 := col_anchor_ones_unique_group c a b
        (by simpa [hfi] using hci) (by simpa [hfj] using hcj) hm
      exact hf i j a b hfi hfj hm hg

/-- The raw dummy-position predicate. -/
def IsDummy {h : ℕ} (p : Position h) : Prop :=
  ∃ d, p = .inr (.inr d)

/-- A mode-free non-dummy position is a variable position. -/
theorem variable_of_mode_none_not_dummy {h : ℕ} (p : Position h)
    (hm : mode p = none) (hd : ¬ IsDummy p) :
    ∃ v, p = .inr (.inl v) := by
  rcases p with a | (v | d)
  · simp [mode] at hm
  · exact ⟨v, rfl⟩
  · exact False.elim (hd ⟨d, rfl⟩)

/-- The exact variable-column sparsity input of one-sided anchor rigidity. -/
theorem sparse_column_of_mode_none {I : Type uI} [DecidableEq I] {h : ℕ}
    (f : I → Position h) (S : Finset I) (p : Position h)
    (hanchor : ∀ i ∈ S, ∃ a, f i = .inl a)
    (hgroups : GroupInjective f)
    (hm : mode p = none) (hd : ¬ IsDummy p) :
    (S.filter (fun i => host (f i) p = true)).card ≤ 4 := by
  obtain ⟨v, rfl⟩ := variable_of_mode_none_not_dummy p hm hd
  exact variable_col_core_card_le_four f S v hanchor
    (hgroups.injOn S hanchor)

/-- The axis-transposed sparsity input. -/
theorem sparse_row_of_mode_none {I : Type uI} [DecidableEq I] {h : ℕ}
    (f : I → Position h) (S : Finset I) (p : Position h)
    (hanchor : ∀ i ∈ S, ∃ a, f i = .inl a)
    (hgroups : GroupInjective f)
    (hm : mode p = none) (hd : ¬ IsDummy p) :
    (S.filter (fun i => host p (f i) = true)).card ≤ 4 := by
  obtain ⟨v, rfl⟩ := variable_of_mode_none_not_dummy p hm hd
  exact variable_row_core_card_le_four f S v hanchor
    (hgroups.injOn S hanchor)

/-- An anchor-anchor one forces equality of the two mode labels. -/
theorem cross_mode {h : ℕ} (r c : Position h) (t u : Mode h)
    (hr : mode r = some t) (hc : mode c = some u)
    (hentry : host r c = true) : t = u := by
  rcases r with a | r
  · rcases c with b | c
    · have hat : a.1 = t := by simpa [mode] using hr
      have hbu : b.1 = u := by simpa [mode] using hc
      by_contra htu
      have hab : a.1 ≠ b.1 := by simpa [hat, hbu] using htu
      simp [host, hab] at hentry
    · simp [mode] at hc
  · simp [mode] at hr

/-- Raw-position form matching the abstract nonanchor-row unit hypothesis. -/
theorem nonanchor_row_unit_of_mode_none {I : Type uI} {h : ℕ}
    (f : I → Position h) (hf : GroupInjective f) (r : Position h)
    (hr : mode r = none) (i j : I) (t : Mode h)
    (hi : mode (f i) = some t) (hj : mode (f j) = some t)
    (hri : host r (f i) = true) (hrj : host r (f j) = true) : i = j := by
  rcases r with a | r
  · simp [mode] at hr
  · exact nonanchor_row_unit f hf r i j t hi hj hri hrj

/-- Raw-position form matching the abstract nonanchor-column unit hypothesis. -/
theorem nonanchor_col_unit_of_mode_none {I : Type uI} {h : ℕ}
    (f : I → Position h) (hf : GroupInjective f) (c : Position h)
    (hc : mode c = none) (i j : I) (t : Mode h)
    (hi : mode (f i) = some t) (hj : mode (f j) = some t)
    (hci : host (f i) c = true) (hcj : host (f j) c = true) : i = j := by
  rcases c with a | c
  · simp [mode] at hc
  · exact nonanchor_col_unit f hf c i j t hi hj hci hcj

end Problem348.Construction.SelectedAnchors

end

end OAI
end
end

section
section
namespace OAI

/-!
Concrete depth-first orders for variable positions.
Each class has 2^h positions. Classes 2*i and 2*i+1 are respectively
plus and minus at i<h; class 2*h is the shared leaf class.
The final two key components retain the original coordinates, making
injectivity immediate without uniqueness assumptions on dyadic data.
-/

namespace Problem348.TreePositions

abbrev VariablePosition (h : ℕ) := Fin (2 * h + 1) × Fin (2 ^ h)
abbrev OrderKey := ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ

def key (endpoint phase tie cls coordinate : ℕ) : OrderKey :=
  toLex (endpoint, toLex (phase, toLex (tie, toLex (cls, coordinate))))

def earlyKey (depth blockSize node cls coordinate : ℕ) : OrderKey :=
  key (2 * node * blockSize) 1 depth cls coordinate

def lateKey (remaining blockSize node cls coordinate : ℕ) : OrderKey :=
  key (2 * (node + 1) * blockSize) 0 remaining cls coordinate

def leafKey (h coordinate : ℕ) : OrderKey :=
  key (2 * coordinate + 1) 2 0 (2 * h) coordinate

/-- `column = false` gives row order; `true` reverses the signs. -/
def orderKey (column : Bool) (h : ℕ) (p : VariablePosition h) : OrderKey :=
  if p.1.val = 2 * h then leafKey h p.2.val
  else
    let depth := p.1.val / 2
    let size := 2 ^ (h - depth)
    let node := p.2.val / size
    if p.1.val % 2 = (if column then 0 else 1) then
      earlyKey depth size node p.1.val p.2.val
    else
      lateKey (h - depth) size node p.1.val p.2.val

abbrev rowKey (h : ℕ) := orderKey false h
abbrev columnKey (h : ℕ) := orderKey true h

def keyClass (k : OrderKey) : ℕ := (ofLex (ofLex (ofLex (ofLex k).2).2).2).1
def keyCoordinate (k : OrderKey) : ℕ := (ofLex (ofLex (ofLex (ofLex k).2).2).2).2

@[simp] theorem keyClass_key (a b c d e : ℕ) : keyClass (key a b c d e) = d := rfl
@[simp] theorem keyCoordinate_key (a b c d e : ℕ) :
    keyCoordinate (key a b c d e) = e := rfl

@[simp] theorem keyClass_orderKey (column : Bool) (h : ℕ) (p : VariablePosition h) :
    keyClass (orderKey column h p) = p.1.val := by
  simp only [orderKey]
  split_ifs <;> simp_all [leafKey, earlyKey, lateKey]

@[simp] theorem keyCoordinate_orderKey (column : Bool) (h : ℕ)
    (p : VariablePosition h) : keyCoordinate (orderKey column h p) = p.2.val := by
  simp only [orderKey]
  split_ifs <;> rfl

theorem orderKey_injective (column : Bool) (h : ℕ) :
    Function.Injective (orderKey column h) := by
  intro p q hpq
  apply Prod.ext
  · apply Fin.ext
    simpa using congrArg keyClass hpq
  · apply Fin.ext
    simpa using congrArg keyCoordinate hpq

/-- Explicit order structures, not global instances: the same raw positions
carry different row and column orders. -/
abbrev positionOrder (column : Bool) (h : ℕ) : LinearOrder (VariablePosition h) :=
  LinearOrder.lift' (orderKey column h) (orderKey_injective column h)

@[simp] theorem card_variablePosition (h : ℕ) :
    Fintype.card (VariablePosition h) = (2 * h + 1) * 2 ^ h := by
  simp [VariablePosition]

end Problem348.TreePositions

namespace Problem348.TreePositions

theorem key_lt_iff_endpoint_le_of_tie_lt
    (a b phase t u cls₁ cls₂ x y : ℕ) (htu : t < u) :
    key a phase t cls₁ x < key b phase u cls₂ y ↔ a ≤ b := by
  simp [key, Prod.Lex.lt_iff, htu, ne_of_lt htu, le_iff_lt_or_eq]

theorem lateKey_child_lt_parent (b r p a cls₁ cls₂ x y : ℕ) (hb : 0 < b) :
    lateKey r b p cls₁ x < lateKey (r + 1) (2 * b) a cls₂ y ↔ p / 2 ≤ a := by
  rw [lateKey, lateKey, key_lt_iff_endpoint_le_of_tie_lt _ _ _ _ _ _ _ _ _
    (Nat.lt_succ_self r)]
  have heq : 2 * (a + 1) * (2 * b) = (2 * (2 * a + 2)) * b := by ring
  rw [heq, mul_le_mul_iff_left₀ hb]
  omega

theorem earlyKey_parent_lt_child (b i p a cls₁ cls₂ x y : ℕ) (hb : 0 < b) :
    earlyKey i (2 * b) a cls₁ x < earlyKey (i + 1) b p cls₂ y ↔ a ≤ p / 2 := by
  rw [earlyKey, earlyKey, key_lt_iff_endpoint_le_of_tie_lt _ _ _ _ _ _ _ _ _
    (Nat.lt_succ_self i)]
  have heq : 2 * a * (2 * b) = (4 * a) * b := by ring
  rw [heq, mul_le_mul_iff_left₀ hb]
  omega

end Problem348.TreePositions

namespace Problem348.TreePositions

theorem leafKey_lt_lateKey_parent (h r p a cls y : ℕ) :
    leafKey h p < lateKey r 2 a cls y ↔ p / 2 ≤ a := by
  simp [leafKey, lateKey, key, Prod.Lex.lt_iff]
  omega

theorem earlyKey_parent_lt_leafKey (h i p a cls x : ℕ) :
    earlyKey i 2 a cls x < leafKey h p ↔ a ≤ p / 2 := by
  simp only [earlyKey, leafKey, key, Prod.Lex.lt_iff, ofLex_toLex,
    ]
  omega

/-- The plus class; at depth h this is the shared leaf class. -/
def plusPos {h : ℕ} (i : ℕ) (hi : i ≤ h) (x : Fin (2 ^ h)) : VariablePosition h :=
  (⟨2 * i, by omega⟩, x)

/-- The minus class, identified with the plus class exactly at the leaf. -/
def minusPos {h : ℕ} (i : ℕ) (hi : i ≤ h) (x : Fin (2 ^ h)) : VariablePosition h :=
  (⟨if i = h then 2 * h else 2 * i + 1, by split_ifs <;> omega⟩, x)

def node {h : ℕ} (i : ℕ) (x : Fin (2 ^ h)) : ℕ := x.val / 2 ^ (h - i)

@[simp] theorem minusPos_leaf (h : ℕ) (x : Fin (2 ^ h)) :
    minusPos h le_rfl x = plusPos h le_rfl x := by
  simp [minusPos, plusPos]

@[simp] theorem orderKey_leaf (column : Bool) (h : ℕ) (x : Fin (2 ^ h)) :
    orderKey column h (plusPos h le_rfl x) = leafKey h x.val := by
  simp [orderKey, plusPos]

@[simp] theorem rowKey_leaf (h : ℕ) (x : Fin (2 ^ h)) :
    rowKey h (plusPos h le_rfl x) = leafKey h x.val :=
  orderKey_leaf false h x

@[simp] theorem columnKey_leaf (h : ℕ) (x : Fin (2 ^ h)) :
    columnKey h (plusPos h le_rfl x) = leafKey h x.val :=
  orderKey_leaf true h x

theorem rowKey_plus_internal {h i : ℕ} (hi : i < h) (x : Fin (2 ^ h)) :
    rowKey h (plusPos i (Nat.le_of_lt hi) x) =
      lateKey (h - i) (2 ^ (h - i)) (node i x) (2 * i) x.val := by
  have hh : 2 * i ≠ 2 * h := by omega
  simp [rowKey, orderKey, plusPos, hh, node]

theorem columnKey_plus_internal {h i : ℕ} (hi : i < h) (x : Fin (2 ^ h)) :
    columnKey h (plusPos i (Nat.le_of_lt hi) x) =
      earlyKey i (2 ^ (h - i)) (node i x) (2 * i) x.val := by
  have hh : 2 * i ≠ 2 * h := by omega
  simp [columnKey, orderKey, plusPos, hh, node]

theorem rowKey_minus_internal {h i : ℕ} (hi : i < h) (x : Fin (2 ^ h)) :
    rowKey h (minusPos i (Nat.le_of_lt hi) x) =
      earlyKey i (2 ^ (h - i)) (node i x) (2 * i + 1) x.val := by
  have hh : 2 * i + 1 ≠ 2 * h := by omega
  have hd : (2 * i + 1) / 2 = i := by omega
  simp [rowKey, orderKey, minusPos, hh, hd, Nat.ne_of_lt hi, node]

theorem columnKey_minus_internal {h i : ℕ} (hi : i < h) (x : Fin (2 ^ h)) :
    columnKey h (minusPos i (Nat.le_of_lt hi) x) =
      lateKey (h - i) (2 ^ (h - i)) (node i x) (2 * i + 1) x.val := by
  have hh : 2 * i + 1 ≠ 2 * h := by omega
  have hd : (2 * i + 1) / 2 = i := by omega
  simp [columnKey, orderKey, minusPos, hh, hd, Nat.ne_of_lt hi, node]

end Problem348.TreePositions

namespace Problem348.TreePositions

/-- The plus row-order equivalence, including shared leaves. -/
theorem row_plus_child_lt_parent {h i : ℕ} (hi : i < h)
    (x y : Fin (2 ^ h)) :
    rowKey h (plusPos (i + 1) (by omega) x) <
        rowKey h (plusPos i (Nat.le_of_lt hi) y) ↔
      node (i + 1) x / 2 ≤ node i y := by
  by_cases he : i + 1 = h
  · subst h
    rw [rowKey_leaf, rowKey_plus_internal hi]
    have hs : i + 1 - i = 1 := by omega
    simp only [hs, pow_one]
    simpa [node] using leafKey_lt_lateKey_parent (i + 1) 1 x.val
      (node i y) (2 * i) y.val
  · have hic : i + 1 < h := by omega
    rw [rowKey_plus_internal hic, rowKey_plus_internal hi]
    have hr : h - i = h - (i + 1) + 1 := by omega
    have hb : 2 ^ (h - i) = 2 * 2 ^ (h - (i + 1)) := by
      rw [hr, pow_succ]
      omega
    rw [hb, hr]
    exact lateKey_child_lt_parent _ _ _ _ _ _ _ _ (by positivity)

/-- The minus row-order equivalence, including shared leaves. -/
theorem row_minus_parent_lt_child {h i : ℕ} (hi : i < h)
    (x y : Fin (2 ^ h)) :
    rowKey h (minusPos i (Nat.le_of_lt hi) y) <
        rowKey h (minusPos (i + 1) (by omega) x) ↔
      node i y ≤ node (i + 1) x / 2 := by
  by_cases he : i + 1 = h
  · subst h
    rw [minusPos_leaf, rowKey_leaf, rowKey_minus_internal hi]
    have hs : i + 1 - i = 1 := by omega
    simp only [hs, pow_one]
    simpa [node] using earlyKey_parent_lt_leafKey (i + 1) i x.val
      (node i y) (2 * i + 1) y.val
  · have hic : i + 1 < h := by omega
    rw [rowKey_minus_internal hic, rowKey_minus_internal hi]
    have hr : h - i = h - (i + 1) + 1 := by omega
    have hb : 2 ^ (h - i) = 2 * 2 ^ (h - (i + 1)) := by
      rw [hr, pow_succ]
      omega
    rw [hb]
    exact earlyKey_parent_lt_child _ _ _ _ _ _ _ _ (by positivity)

/-- The plus column-order equivalence, including shared leaves. -/
theorem column_plus_parent_lt_child {h i : ℕ} (hi : i < h)
    (x y : Fin (2 ^ h)) :
    columnKey h (plusPos i (Nat.le_of_lt hi) y) <
        columnKey h (plusPos (i + 1) (by omega) x) ↔
      node i y ≤ node (i + 1) x / 2 := by
  by_cases he : i + 1 = h
  · subst h
    rw [columnKey_leaf, columnKey_plus_internal hi]
    have hs : i + 1 - i = 1 := by omega
    simp only [hs, pow_one]
    simpa [node] using earlyKey_parent_lt_leafKey (i + 1) i x.val
      (node i y) (2 * i) y.val
  · have hic : i + 1 < h := by omega
    rw [columnKey_plus_internal hic, columnKey_plus_internal hi]
    have hr : h - i = h - (i + 1) + 1 := by omega
    have hb : 2 ^ (h - i) = 2 * 2 ^ (h - (i + 1)) := by
      rw [hr, pow_succ]
      omega
    rw [hb]
    exact earlyKey_parent_lt_child _ _ _ _ _ _ _ _ (by positivity)

/-- The minus column-order equivalence, including shared leaves. -/
theorem column_minus_child_lt_parent {h i : ℕ} (hi : i < h)
    (x y : Fin (2 ^ h)) :
    columnKey h (minusPos (i + 1) (by omega) x) <
        columnKey h (minusPos i (Nat.le_of_lt hi) y) ↔
      node (i + 1) x / 2 ≤ node i y := by
  by_cases he : i + 1 = h
  · subst h
    rw [minusPos_leaf, columnKey_leaf, columnKey_minus_internal hi]
    have hs : i + 1 - i = 1 := by omega
    simp only [hs, pow_one]
    simpa [node] using leafKey_lt_lateKey_parent (i + 1) 1 x.val
      (node i y) (2 * i + 1) y.val
  · have hic : i + 1 < h := by omega
    rw [columnKey_minus_internal hic, columnKey_minus_internal hi]
    have hr : h - i = h - (i + 1) + 1 := by omega
    have hb : 2 ^ (h - i) = 2 * 2 ^ (h - (i + 1)) := by
      rw [hr, pow_succ]
      omega
    rw [hb, hr]
    exact lateKey_child_lt_parent _ _ _ _ _ _ _ _ (by positivity)

end Problem348.TreePositions

end OAI
end
end

section
section
namespace OAI

/-!
Full row and column orders extending the variable order.
The raw carrier is the anchor / variable / dummy sum.
-/


namespace Problem348.AnchorFrames

abbrev Raw (M : Type uM) (V : Type uV) (O : Type uO) := (M × Fin 64 × O) ⊕ (V ⊕ O)
abbrev AnchorOrder (M : Type uM) (O : Type uO) := M ×ₗ Fin 64 ×ₗ O
abbrev RowOrder (M : Type uM) (V : Type uV) (O : Type uO) := AnchorOrder M O ⊕ₗ (V ⊕ₗ O)
abbrev ColOrder (M : Type uM) (V : Type uV) (O : Type uO) := AnchorOrder M O ⊕ₗ (O ⊕ₗ V)

/-- Coordinates for the row order: anchors, variables, dummy. -/
def rowKey {M : Type uM} {V : Type uV} {O : Type uO} : Raw M V O → RowOrder M V O
  | .inl (t, u, x) => .inlₗ (toLex (t, toLex (u, x)))
  | .inr (.inl v) => .inrₗ (.inlₗ v)
  | .inr (.inr x) => .inrₗ (.inrₗ x)

/-- Coordinates for the column order: anchors, dummy, variables. -/
def colKey {M : Type uM} {V : Type uV} {O : Type uO} : Raw M V O → ColOrder M V O
  | .inl (t, u, x) => .inlₗ (toLex (t, toLex (u, x)))
  | .inr (.inl v) => .inrₗ (.inrₗ v)
  | .inr (.inr x) => .inrₗ (.inlₗ x)

def rowEquiv (M : Type uM) (V : Type uV) (O : Type uO) : Raw M V O ≃ RowOrder M V O where
  toFun := rowKey
  invFun x := match ofLex x with
    | .inl a => .inl ((ofLex a).1, (ofLex (ofLex a).2).1, (ofLex (ofLex a).2).2)
    | .inr b => .inr (ofLex b)
  left_inv := by rintro (⟨t,u,x⟩ | (v | x)) <;> rfl
  right_inv := by rintro (⟨t,u,x⟩ | (v | x)) <;> rfl

def colEquiv (M : Type uM) (V : Type uV) (O : Type uO) : Raw M V O ≃ ColOrder M V O where
  toFun := colKey
  invFun x := match ofLex x with
    | .inl a => .inl ((ofLex a).1, (ofLex (ofLex a).2).1, (ofLex (ofLex a).2).2)
    | .inr b => match ofLex b with
      | .inl x => .inr (.inr x)
      | .inr v => .inr (.inl v)
  left_inv := by rintro (⟨t,u,x⟩ | (v | x)) <;> rfl
  right_inv := by rintro (⟨t,u,x⟩ | (x | v)) <;> rfl

section Orders
variable {M : Type uM} {V : Type uV} {O : Type uO} [LinearOrder M] [LinearOrder V] [LinearOrder O]

/-- The full raw row order, suitable for local instance installation. -/
abbrev rowOrder : LinearOrder (Raw M V O) := LinearOrder.lift' rowKey (rowEquiv M V O).injective

/-- The full raw column order, suitable for local instance installation. -/
abbrev colOrder : LinearOrder (Raw M V O) := LinearOrder.lift' colKey (colEquiv M V O).injective

/-- Arbitrary offsets in successive groups give increasing selected anchors. -/
theorem row_anchor_strictMono (t : M) (a : Fin 64 → O) :
    StrictMono (fun u => rowKey (M := M) (V := V) (.inl (t, u, a u))) := by
  intro u v huv
  change Sum.Lex _ _ _ _
  apply Sum.Lex.inl
  apply Prod.Lex.right
  exact Prod.Lex.left _ _ huv

theorem col_anchor_strictMono (t : M) (a : Fin 64 → O) :
    StrictMono (fun u => colKey (M := M) (V := V) (.inl (t, u, a u))) := by
  intro u v huv
  change Sum.Lex _ _ _ _
  apply Sum.Lex.inl
  apply Prod.Lex.right
  exact Prod.Lex.left _ _ huv

theorem row_anchor_lt_nonanchor (t : M) (u : Fin 64) (a : O) (x : V ⊕ O) :
    rowKey (.inl (t,u,a)) < rowKey (.inr x) := by
  cases x <;> exact Sum.Lex.sep _ _

theorem col_anchor_lt_nonanchor (t : M) (u : Fin 64) (a : O) (x : V ⊕ O) :
    colKey (.inl (t,u,a)) < colKey (.inr x) := by
  cases x <;> exact Sum.Lex.sep _ _

theorem row_variable_lt_dummy (v : V) (x : O) :
    rowKey (M := M) (.inr (.inl v)) < rowKey (.inr (.inr x)) :=
  Sum.Lex.inr (Sum.Lex.sep _ _)

theorem col_dummy_lt_variable (v : V) (x : O) :
    colKey (M := M) (.inr (.inr x)) < colKey (.inr (.inl v)) :=
  Sum.Lex.inr (Sum.Lex.sep _ _)

@[simp] theorem row_variable_lt_variable (v w : V) :
    rowKey (M := M) (O := O) (.inr (.inl v)) < rowKey (.inr (.inl w)) ↔ v < w := by
  simp [rowKey]

@[simp] theorem col_variable_lt_variable (v w : V) :
    colKey (M := M) (O := O) (.inr (.inl v)) < colKey (.inr (.inl w)) ↔ v < w := by
  simp [colKey]

/-- The anchor region is an initial segment of the complete row axis. -/
theorem row_not_nonanchor_lt_anchor (t : M) (u : Fin 64) (a : O) (x : V ⊕ O) :
    ¬ rowKey (.inr x) < rowKey (.inl (t,u,a)) :=
  not_lt_of_gt (row_anchor_lt_nonanchor t u a x)

/-- The anchor region is also an initial segment of the complete column axis. -/
theorem col_not_nonanchor_lt_anchor (t : M) (u : Fin 64) (a : O) (x : V ⊕ O) :
    ¬ colKey (.inr x) < colKey (.inl (t,u,a)) :=
  not_lt_of_gt (col_anchor_lt_nonanchor t u a x)

/-- Within one mode, increasing selected anchors have nondecreasing group labels. -/
theorem row_group_le_of_lt (t : M) (u v : Fin 64) (a b : O)
    (hab : rowKey (V := V) (.inl (t,u,a)) < rowKey (.inl (t,v,b))) : u ≤ v := by
  have h : toLex (u,a) < toLex (v,b) := by
    simpa [rowKey, Prod.Lex.lt_iff] using hab
  exact (Prod.Lex.monotone_fst_ofLex h.le)

theorem col_group_le_of_lt (t : M) (u v : Fin 64) (a b : O)
    (hab : colKey (V := V) (.inl (t,u,a)) < colKey (.inl (t,v,b))) : u ≤ v := by
  have h : toLex (u,a) < toLex (v,b) := by
    simpa [colKey, Prod.Lex.lt_iff] using hab
  exact (Prod.Lex.monotone_fst_ofLex h.le)

/-- Selected anchor rows after the full axis has been enumerated by `Fin n`. -/
def selectedRows {n : ℕ} (e : Fin n ≃o RowOrder M V O)
    (t : M) (a : Fin 64 → O) : Fin 64 → Fin n :=
  fun u => e.symm (rowKey (.inl (t, u, a u)))

/-- Selected anchor columns after the full axis has been enumerated by `Fin n`. -/
def selectedCols {n : ℕ} (e : Fin n ≃o ColOrder M V O)
    (t : M) (a : Fin 64 → O) : Fin 64 → Fin n :=
  fun u => e.symm (colKey (.inl (t, u, a u)))

theorem selectedRows_strictMono {n : ℕ} (e : Fin n ≃o RowOrder M V O)
    (t : M) (a : Fin 64 → O) : StrictMono (selectedRows e t a) :=
  e.symm.strictMono.comp (row_anchor_strictMono t a)

theorem selectedCols_strictMono {n : ℕ} (e : Fin n ≃o ColOrder M V O)
    (t : M) (a : Fin 64 → O) : StrictMono (selectedCols e t a) :=
  e.symm.strictMono.comp (col_anchor_strictMono t a)

theorem selectedRows_lt_nonanchor {n : ℕ} (e : Fin n ≃o RowOrder M V O)
    (t : M) (a : Fin 64 → O) (u : Fin 64) (x : V ⊕ O) :
    selectedRows e t a u < e.symm (rowKey (.inr x)) :=
  e.symm.strictMono (row_anchor_lt_nonanchor t u (a u) x)

theorem selectedCols_lt_nonanchor {n : ℕ} (e : Fin n ≃o ColOrder M V O)
    (t : M) (a : Fin 64 → O) (u : Fin 64) (x : V ⊕ O) :
    selectedCols e t a u < e.symm (colKey (.inr x)) :=
  e.symm.strictMono (col_anchor_lt_nonanchor t u (a u) x)

end Orders
end Problem348.AnchorFrames

end OAI
end
end

section
section
namespace OAI

/-!
# The canonical host with both full-axis orders

The raw host, variable depth-first orders, and anchor/dummy order extension
give two orders. They are not global instances on the same carrier. Their
increasing enumerations are independent equivalences to the matrix size.
-/

noncomputable section

namespace Problem348.OrderedHost

open Construction

abbrev size (h : ℕ) := (386 * h + 2) * 2 ^ h

/-- Rows: anchors first, then the minus/subtree/plus tree order, then dummy. -/
abbrev rowOrder (h : ℕ) : LinearOrder (Position h) := by
  exact @AnchorFrames.rowOrder (Mode h) (VariablePosition h) (Fin (2 ^ h))
    inferInstance (TreePositions.positionOrder false h) inferInstance

/-- Columns: anchors first, then dummy, then the plus/subtree/minus tree order. -/
abbrev columnOrder (h : ℕ) : LinearOrder (Position h) := by
  exact @AnchorFrames.colOrder (Mode h) (VariablePosition h) (Fin (2 ^ h))
    inferInstance (TreePositions.positionOrder true h) inferInstance

/-- The increasing row enumeration, from raw positions to actual indices. -/
def rowIndex (h : ℕ) : Position h ≃ Fin (size h) := by
  letI := rowOrder h
  exact (monoEquivOfFin (Position h) (card_position h)).toEquiv.symm

/-- The increasing column enumeration, independent of the row enumeration. -/
def columnIndex (h : ℕ) : Position h ≃ Fin (size h) := by
  letI := columnOrder h
  exact (monoEquivOfFin (Position h) (card_position h)).toEquiv.symm

theorem rowIndex_lt_iff (h : ℕ) (r s : Position h) :
    rowIndex h r < rowIndex h s ↔ @LT.lt _ (rowOrder h).toLT r s := by
  let := rowOrder h
  exact @OrderIso.lt_iff_lt _ _ (rowOrder h).toPreorder inferInstance
    (@OrderIso.symm _ _ inferInstance (rowOrder h).toLE
      (monoEquivOfFin (Position h) (card_position h))) r s

theorem columnIndex_lt_iff (h : ℕ) (r s : Position h) :
    columnIndex h r < columnIndex h s ↔ @LT.lt _ (columnOrder h).toLT r s := by
  let := columnOrder h
  exact @OrderIso.lt_iff_lt _ _ (columnOrder h).toPreorder inferInstance
    (@OrderIso.symm _ _ inferInstance (columnOrder h).toLE
      (monoEquivOfFin (Position h) (card_position h))) r s

/-- On variable positions the full row enumeration has exactly the tree-key order. -/
theorem rowIndex_variable_lt_iff {h : ℕ} (v w : VariablePosition h) :
    rowIndex h (Sum.inr (Sum.inl v)) < rowIndex h (Sum.inr (Sum.inl w)) ↔
      TreePositions.rowKey h v < TreePositions.rowKey h w := by
  rw [rowIndex_lt_iff]
  exact @AnchorFrames.row_variable_lt_variable (Mode h) (VariablePosition h)
    (Fin (2 ^ h)) inferInstance (TreePositions.positionOrder false h) inferInstance v w

/-- On variable positions the full column enumeration has exactly the tree-key order. -/
theorem columnIndex_variable_lt_iff {h : ℕ} (v w : VariablePosition h) :
    columnIndex h (Sum.inr (Sum.inl v)) < columnIndex h (Sum.inr (Sum.inl w)) ↔
      TreePositions.columnKey h v < TreePositions.columnKey h w := by
  rw [columnIndex_lt_iff]
  exact @AnchorFrames.col_variable_lt_variable (Mode h) (VariablePosition h)
    (Fin (2 ^ h)) inferInstance (TreePositions.positionOrder true h) inferInstance v w

/-- Any representatives of the 64 successive anchor groups are increasing rows. -/
theorem row_anchor_strictMono {h : ℕ} (t : Mode h)
    (a : Fin 64 → Fin (2 ^ h)) :
    StrictMono (fun u => rowIndex h (Sum.inl (t, u, a u))) := by
  intro u v huv
  rw [rowIndex_lt_iff]
  exact @AnchorFrames.row_anchor_strictMono (Mode h) (VariablePosition h)
    (Fin (2 ^ h)) inferInstance (TreePositions.positionOrder false h) inferInstance
    t a u v huv

/-- The analogous anchor representatives are increasing columns. -/
theorem column_anchor_strictMono {h : ℕ} (t : Mode h)
    (a : Fin 64 → Fin (2 ^ h)) :
    StrictMono (fun u => columnIndex h (Sum.inl (t, u, a u))) := by
  intro u v huv
  rw [columnIndex_lt_iff]
  exact @AnchorFrames.col_anchor_strictMono (Mode h) (VariablePosition h)
    (Fin (2 ^ h)) inferInstance (TreePositions.positionOrder true h) inferInstance
    t a u v huv

theorem row_anchor_lt_nonanchor {h : ℕ} (t : Mode h) (u : Fin 64)
    (a : Fin (2 ^ h)) (x : VariablePosition h ⊕ Fin (2 ^ h)) :
    rowIndex h (Sum.inl (t, u, a)) < rowIndex h (Sum.inr x) := by
  rw [rowIndex_lt_iff]
  exact @AnchorFrames.row_anchor_lt_nonanchor (Mode h) (VariablePosition h)
    (Fin (2 ^ h)) inferInstance (TreePositions.positionOrder false h) inferInstance
    t u a x

theorem column_anchor_lt_nonanchor {h : ℕ} (t : Mode h) (u : Fin 64)
    (a : Fin (2 ^ h)) (x : VariablePosition h ⊕ Fin (2 ^ h)) :
    columnIndex h (Sum.inl (t, u, a)) < columnIndex h (Sum.inr x) := by
  rw [columnIndex_lt_iff]
  exact @AnchorFrames.col_anchor_lt_nonanchor (Mode h) (VariablePosition h)
    (Fin (2 ^ h)) inferInstance (TreePositions.positionOrder true h) inferInstance
    t u a x

theorem row_variable_lt_dummy {h : ℕ} (v : VariablePosition h) (x : Fin (2 ^ h)) :
    rowIndex h (Sum.inr (Sum.inl v)) < rowIndex h (Sum.inr (Sum.inr x)) := by
  rw [rowIndex_lt_iff]
  exact @AnchorFrames.row_variable_lt_dummy (Mode h) (VariablePosition h)
    (Fin (2 ^ h)) inferInstance (TreePositions.positionOrder false h) inferInstance v x

theorem column_dummy_lt_variable {h : ℕ} (v : VariablePosition h) (x : Fin (2 ^ h)) :
    columnIndex h (Sum.inr (Sum.inr x)) < columnIndex h (Sum.inr (Sum.inl v)) := by
  rw [columnIndex_lt_iff]
  exact @AnchorFrames.col_dummy_lt_variable (Mode h) (VariablePosition h)
    (Fin (2 ^ h)) inferInstance (TreePositions.positionOrder true h) inferInstance v x

/-- Initial-segment property for anchors, stated without an extra host predicate. -/
theorem row_anchor_initial {h : ℕ} {r s : Position h}
    (hrs : rowIndex h r < rowIndex h s) (hs : ∃ a, s = Sum.inl a) :
    ∃ a, r = Sum.inl a := by
  obtain ⟨⟨t, u, x⟩, rfl⟩ := hs
  rcases r with a | v
  · exact ⟨a, rfl⟩
  · exact False.elim (lt_asymm hrs (row_anchor_lt_nonanchor t u x v))

theorem column_anchor_initial {h : ℕ} {r s : Position h}
    (hrs : columnIndex h r < columnIndex h s) (hs : ∃ a, s = Sum.inl a) :
    ∃ a, r = Sum.inl a := by
  obtain ⟨⟨t, u, x⟩, rfl⟩ := hs
  rcases r with a | v
  · exact ⟨a, rfl⟩
  · exact False.elim (lt_asymm hrs (column_anchor_lt_nonanchor t u x v))

/-- First tree-order equivalence, now for the actual row indices. -/
theorem row_plus_child_lt_parent {h i : ℕ} (hi : i < h) (x y : Fin (2 ^ h)) :
    rowIndex h (.inr (.inl (TreePositions.plusPos (i + 1) (by omega) x))) <
      rowIndex h (.inr (.inl (TreePositions.plusPos i (by omega) y))) ↔
      TreePositions.node (i + 1) x / 2 ≤ TreePositions.node i y := by
  rw [rowIndex_variable_lt_iff]
  exact TreePositions.row_plus_child_lt_parent hi x y

/-- Second tree-order equivalence, now for the actual row indices. -/
theorem row_minus_parent_lt_child {h i : ℕ} (hi : i < h) (x y : Fin (2 ^ h)) :
    rowIndex h (.inr (.inl (TreePositions.minusPos i (by omega) y))) <
      rowIndex h (.inr (.inl (TreePositions.minusPos (i + 1) (by omega) x))) ↔
      TreePositions.node i y ≤ TreePositions.node (i + 1) x / 2 := by
  rw [rowIndex_variable_lt_iff]
  exact TreePositions.row_minus_parent_lt_child hi x y

/-- Third tree-order equivalence, now for the actual column indices. -/
theorem column_plus_parent_lt_child {h i : ℕ} (hi : i < h) (x y : Fin (2 ^ h)) :
    columnIndex h (.inr (.inl (TreePositions.plusPos i (by omega) y))) <
      columnIndex h (.inr (.inl (TreePositions.plusPos (i + 1) (by omega) x))) ↔
      TreePositions.node i y ≤ TreePositions.node (i + 1) x / 2 := by
  rw [columnIndex_variable_lt_iff]
  exact TreePositions.column_plus_parent_lt_child hi x y

/-- Fourth tree-order equivalence, now for the actual column indices. -/
theorem column_minus_child_lt_parent {h i : ℕ} (hi : i < h) (x y : Fin (2 ^ h)) :
    columnIndex h (.inr (.inl (TreePositions.minusPos (i + 1) (by omega) x))) <
      columnIndex h (.inr (.inl (TreePositions.minusPos i (by omega) y))) ↔
      TreePositions.node (i + 1) x / 2 ≤ TreePositions.node i y := by
  rw [columnIndex_variable_lt_iff]
  exact TreePositions.column_minus_child_lt_parent hi x y

end Problem348.OrderedHost

end

end OAI
end
end

section
section
namespace OAI

/-!
# Ordered exhaustion of anchor groups

Once one mode is known, identical host rows within each group and distinct
pattern rows prevent repeated groups. The group order then forces the
selected group map to be the identity.
-/


namespace Problem348.AnchorGroups

/-- Distinct pattern rows force distinct selected group labels whenever equal
labels give identical rows against the selected columns. -/
theorem labels_injective {I : Type uI} {J : Type uJ} {R : Type uR} {C : Type uC} {G : Type uG}
    (S : I → J → Bool) (A : R → C → Bool)
    (r : I → R) (c : J → C) (g : I → G)
    (hrows : Function.Injective S)
    (hcopy : ∀ i j, A (r i) (c j) = S i j)
    (htwin : ∀ i i', g i = g i' → ∀ j,
      A (r i) (c j) = A (r i') (c j)) :
    Function.Injective g := by
  intro i i' h
  apply hrows
  funext j
  rw [← hcopy i j, ← hcopy i' j]
  exact htwin i i' h j

/-- Equal host rows belonging to a fixed twin class cannot both be selected
by a pattern with distinct rows. This applies both to anchor groups and to the
dummy block, even before a common mode has been established. -/
theorem same_twin_class_index_eq {I : Type uI} {J : Type uJ} {R : Type uR} {C : Type uC}
    (S : I → J → Bool) (A : R → C → Bool)
    (r : I → R) (c : J → C) (P : R → Prop)
    (hrows : Function.Injective S)
    (hcopy : ∀ i j, A (r i) (c j) = S i j)
    (htwin : ∀ x y, P x → P y → ∀ z, A x z = A y z)
    {i i' : I} (hi : P (r i)) (hi' : P (r i')) : i = i' := by
  apply hrows
  funext j
  rw [← hcopy i j, ← hcopy i' j]
  exact htwin (r i) (r i') hi hi' (c j)

/-- Before all selected positions are pinned, the partial anchor label is
already injective on the selected anchor positions. Nonanchor labels are not
required to be injective. -/
theorem partial_labels_injOn {I : Type uI} {J : Type uJ} {R : Type uR} {C : Type uC} {L : Type uL}
    (S : I → J → Bool) (A : R → C → Bool)
    (r : I → R) (c : J → C) (label : R → Option L)
    (hrows : Function.Injective S)
    (hcopy : ∀ i j, A (r i) (c j) = S i j)
    (htwin : ∀ x y l, label x = some l → label y = some l →
      ∀ z, A x z = A y z) :
    Set.InjOn (fun i => label (r i)) {i | ∃ l, label (r i) = some l} := by
  intro i hi i' _ heq
  obtain ⟨l, hl⟩ := hi
  have hl' : label (r i') = some l := heq.symm.trans hl
  apply hrows
  funext j
  rw [← hcopy i j, ← hcopy i' j]
  exact htwin (r i) (r i') l hl hl' (c j)

/-- At most one selected position belongs to any host row twin class. -/
theorem selected_twin_class_card_le_one {I : Type uI} {J : Type uJ} {R : Type uR} {C : Type uC} [Fintype I]
    (S : I → J → Bool) (A : R → C → Bool)
    (r : I → R) (c : J → C) (P : R → Prop) [DecidablePred P]
    (hrows : Function.Injective S)
    (hcopy : ∀ i j, A (r i) (c j) = S i j)
    (htwin : ∀ x y, P x → P y → ∀ z, A x z = A y z) :
    (Finset.univ.filter (fun i => P (r i))).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi i' hi'
  exact same_twin_class_index_eq S A r c P hrows hcopy htwin
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hi').2

/-- Unit-vector incidences contribute at most one true entry per participating
mode after selected anchor groups have been shown distinct. This is the
counting bridge from the concrete mode-support bound to rigidity's sparsity
hypothesis. -/
theorem true_entries_le_supported_modes {I : Type uI} {T : Type uT} {G : Type uG}
    (selected : Finset I) (mode : I → T) (group : I → G)
    (entry : I → Bool) (support : Finset T)
    (hgroups : Set.InjOn (fun i => (mode i, group i)) (↑selected : Set I))
    (hunit : ∀ i ∈ selected, ∀ j ∈ selected,
      entry i = true → entry j = true → mode i = mode j → group i = group j)
    (hsupport : ∀ i ∈ selected, entry i = true → mode i ∈ support) :
    (selected.filter (fun i => entry i = true)).card ≤ support.card := by
  classical
  apply Finset.card_le_card_of_injOn mode
  · intro i hi
    obtain ⟨his, hie⟩ := Finset.mem_filter.mp hi
    exact hsupport i his hie
  · intro i hi j hj hij
    obtain ⟨his, hie⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjs, hje⟩ := Finset.mem_filter.mp hj
    apply hgroups his hjs
    exact Prod.ext hij (hunit i his j hjs hie hje hij)

/-- An increasing injective enumeration of a finite ordered set is its
prescribed enumeration. -/
theorem monotone_injective_eq_id {I : Type uI} [LinearOrder I] [Finite I]
    (g : I → I) (hmono : Monotone g) (hinj : Function.Injective g) :
    ∀ i, g i = i := by
  let f : I →o I := ⟨g, hmono⟩
  have hf : f = OrderHom.id := OrderHom.eq_id_of_injective f hinj
  intro i
  exact congrArg (fun q : I →o I => q i) hf

/-- Ordered group exhaustion for a copied pattern with distinct rows. -/
theorem group_eq_index {I : Type uI} {J : Type uJ} {R : Type uR} {C : Type uC} [LinearOrder I] [Finite I]
    (S : I → J → Bool) (A : R → C → Bool)
    (r : I → R) (c : J → C) (g : I → I)
    (hrows : Function.Injective S)
    (hcopy : ∀ i j, A (r i) (c j) = S i j)
    (htwin : ∀ i i', g i = g i' → ∀ j,
      A (r i) (c j) = A (r i') (c j))
    (hmono : Monotone g) : ∀ i, g i = i :=
  monotone_injective_eq_id g hmono
    (labels_injective S A r c g hrows hcopy htwin)

/-- Host-facing formulation: anchor labels record a mode and a group. Once
all selected rows are anchors of one mode, their group labels equal their
pattern indices. The column version follows by transposition. -/
theorem row_labels_eq {k : ℕ} {J : Type uJ} {R : Type uR} {C : Type uC} {T : Type uT} [LinearOrder R]
    (S : Fin k → J → Bool) (A : R → C → Bool)
    (label : R → Option (T × Fin k))
    (r : Fin k → R) (c : J → C) (t : T)
    (hr : StrictMono r)
    (hrows : Function.Injective S)
    (hcopy : ∀ i j, A (r i) (c j) = S i j)
    (hmode : ∀ i, ∃ u, label (r i) = some (t, u))
    (htwin : ∀ x y u, label x = some (t, u) →
      label y = some (t, u) → ∀ z, A x z = A y z)
    (horder : ∀ x y u v, x < y → label x = some (t, u) →
      label y = some (t, v) → u ≤ v) :
    ∀ i, label (r i) = some (t, i) := by
  classical
  choose g hg using hmode
  have hmono : Monotone g := by
    intro i j hij
    rcases eq_or_lt_of_le hij with h | h
    · subst j
      exact le_rfl
    · exact horder (r i) (r j) (g i) (g j) (hr h) (hg i) (hg j)
  have heq : ∀ i, g i = i := group_eq_index S A r c g hrows hcopy
    (by
      intro i j hij z
      exact htwin (r i) (r j) (g i) (hg i) (hij ▸ hg j) (c z)) hmono
  intro i
  simpa only [heq i] using hg i

/-- Transposed host-facing formulation for the selected columns. -/
theorem column_labels_eq {k : ℕ} {I : Type uI} {R : Type uR} {C : Type uC} {T : Type uT} [LinearOrder C]
    (S : I → Fin k → Bool) (A : R → C → Bool)
    (label : C → Option (T × Fin k))
    (r : I → R) (c : Fin k → C) (t : T)
    (hc : StrictMono c)
    (hcols : Function.Injective (fun j i => S i j))
    (hcopy : ∀ i j, A (r i) (c j) = S i j)
    (hmode : ∀ j, ∃ v, label (c j) = some (t, v))
    (htwin : ∀ x y v, label x = some (t, v) →
      label y = some (t, v) → ∀ z, A z x = A z y)
    (horder : ∀ x y u v, x < y → label x = some (t, u) →
      label y = some (t, v) → u ≤ v) :
    ∀ j, label (c j) = some (t, j) := by
  exact row_labels_eq (fun j i => S i j) (fun y x => A x y)
    label c r t hc hcols (fun j i => hcopy i j) hmode htwin horder

end Problem348.AnchorGroups

end OAI
end
end

section
section
namespace OAI

/-!
# Group coordinates of a canonical host anchor copy

One-mode anchor rigidity, the entries of `Construction.host`, and distinct
rows and columns of `anchor64` force exhaustion of the anchor groups.
The two axes use independent key functions, with no global order instance
on the raw carrier.
-/


namespace Problem348.Construction.AnchorGroups

/-- The row groups of a one-mode anchor copy are exactly their pattern indices.
Only the within-mode comparison property of the chosen row order is needed. -/
theorem row_representatives {h : ℕ} {K : Type uK} [LinearOrder K]
    (key : Position h → K) (r c : Fin 64 → Position h) (t : Mode h)
    (hr : StrictMono (fun i => key (r i)))
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    (hmode : ∀ i, ∃ u x, r i = Sum.inl (t, u, x))
    (horder : ∀ u v : Fin 64, ∀ x y : Fin (2 ^ h),
      key (Sum.inl (t,u,x)) < key (Sum.inl (t,v,y)) → u ≤ v) :
    ∃ x : Fin 64 → Fin (2 ^ h), ∀ i, r i = Sum.inl (t,i,x i) := by
  classical
  choose g x hx using hmode
  have hmono : Monotone g := by
    intro i j hij
    rcases eq_or_lt_of_le hij with e | hij
    · subst j
      exact le_rfl
    · apply horder (g i) (g j) (x i) (x j)
      simpa only [hx i, hx j] using hr hij
  have heq : ∀ i, g i = i :=
    Problem348.AnchorGroups.group_eq_index anchor64 host r c g
      anchor64_rows_injective hcopy
      (by
        intro i j hij z
        rw [hx i, hx j, ← hij]
        exact host_anchor_row_twin t (g i) (x i) (x j) (c z)) hmono
  refine ⟨x, fun i => ?_⟩
  simpa only [heq i] using hx i

/-- The analogous conclusion for the independently ordered column axis. -/
theorem column_representatives {h : ℕ} {K : Type uK} [LinearOrder K]
    (key : Position h → K) (r c : Fin 64 → Position h) (t : Mode h)
    (hc : StrictMono (fun j => key (c j)))
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    (hmode : ∀ j, ∃ v y, c j = Sum.inl (t, v, y))
    (horder : ∀ u v : Fin 64, ∀ x y : Fin (2 ^ h),
      key (Sum.inl (t,u,x)) < key (Sum.inl (t,v,y)) → u ≤ v) :
    ∃ y : Fin 64 → Fin (2 ^ h), ∀ j, c j = Sum.inl (t,j,y j) := by
  classical
  choose g y hy using hmode
  have hmono : Monotone g := by
    intro i j hij
    rcases eq_or_lt_of_le hij with e | hij
    · subst j
      exact le_rfl
    · apply horder (g i) (g j) (y i) (y j)
      simpa only [hy i, hy j] using hc hij
  have heq : ∀ j, g j = j :=
    Problem348.AnchorGroups.group_eq_index (fun j i => anchor64 i j)
      (fun b a => host a b) c r g anchor64_columns_injective
      (fun j i => hcopy i j)
      (by
        intro i j hij z
        rw [hy i, hy j, ← hij]
        exact host_anchor_column_twin t (g i) (y i) (y j) (r z)) hmono
  refine ⟨y, fun j => ?_⟩
  simpa only [heq j] using hy j

/-- Both axes of the canonical anchor copy use every group in its prescribed
order, with independent choices of the within-group offsets. -/
theorem representatives {h : ℕ} {KR : Type uKR} {KC : Type uKC}
    [LinearOrder KR] [LinearOrder KC]
    (rowKey : Position h → KR) (colKey : Position h → KC)
    (r c : Fin 64 → Position h) (t : Mode h)
    (hr : StrictMono (fun i => rowKey (r i)))
    (hc : StrictMono (fun j => colKey (c j)))
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    (hrowmode : ∀ i, ∃ u x, r i = Sum.inl (t,u,x))
    (hcolmode : ∀ j, ∃ v y, c j = Sum.inl (t,v,y))
    (hroworder : ∀ u v : Fin 64, ∀ x y : Fin (2 ^ h),
      rowKey (Sum.inl (t,u,x)) < rowKey (Sum.inl (t,v,y)) → u ≤ v)
    (hcolorder : ∀ u v : Fin 64, ∀ x y : Fin (2 ^ h),
      colKey (Sum.inl (t,u,x)) < colKey (Sum.inl (t,v,y)) → u ≤ v) :
    ∃ x y : Fin 64 → Fin (2 ^ h),
      (∀ i, r i = Sum.inl (t,i,x i)) ∧ (∀ j, c j = Sum.inl (t,j,y j)) := by
  obtain ⟨x, hx⟩ := row_representatives rowKey r c t hr hcopy hrowmode hroworder
  obtain ⟨y, hy⟩ := column_representatives colKey r c t hc hcopy hcolmode hcolorder
  exact ⟨x, y, hx, hy⟩

end Problem348.Construction.AnchorGroups

end OAI
end
end

section
section
namespace OAI

/-!
# Prescribed anchor coordinates in the actual ordered host

The independent enumerations satisfy `OrderedHost.row_anchor_strictMono`
and `column_anchor_strictMono`, giving the order premises of one-mode group
exhaustion without a default order instance on the raw Position sum type.
-/


namespace Problem348.OrderedHost

open Construction

private theorem group_le_of_ordered_representatives
    {I : Type uI} {O : Type uO} {K : Type uK} [LinearOrder I] [LinearOrder K]
    (key : I → O → K)
    (hmono : ∀ f : I → O, StrictMono (fun i => key i (f i)))
    (u v : I) (x y : O) (hxy : key u x < key v y) : u ≤ v := by
  by_contra hnot
  have hvu : v < u := lt_of_not_ge hnot
  have hne : u ≠ v := ne_of_gt hvu
  have hback := hmono (fun i => if i = v then y else x) hvu
  simp only [ite_eq_right hne] at hback
  exact lt_asymm hxy hback

/-- Increasing rows in one mode have nondecreasing anchor group indices. -/
theorem row_anchor_group_le {h : ℕ} (t : Mode h) (u v : Fin 64)
    (x y : Fin (2 ^ h))
    (hxy : rowIndex h (Sum.inl (t,u,x)) < rowIndex h (Sum.inl (t,v,y))) :
    u ≤ v :=
  group_le_of_ordered_representatives
    (fun i a => rowIndex h (Sum.inl (t,i,a)))
    (row_anchor_strictMono t) u v x y hxy

/-- The analogous group-order implication for the actual column enumeration. -/
theorem column_anchor_group_le {h : ℕ} (t : Mode h) (u v : Fin 64)
    (x y : Fin (2 ^ h))
    (hxy : columnIndex h (Sum.inl (t,u,x)) < columnIndex h (Sum.inl (t,v,y))) :
    u ≤ v :=
  group_le_of_ordered_representatives
    (fun i a => columnIndex h (Sum.inl (t,i,a)))
    (column_anchor_strictMono t) u v x y hxy

/-- Mode rigidity locates the prefix in one mode, forcing its exact group
coordinates in the concrete ordered host. No additional group, twin, density,
or order hypotheses are required. -/
theorem anchor_representatives_of_one_mode {h : ℕ}
    (r c : Fin 64 → Position h) (t : Mode h)
    (hr : StrictMono (fun i => rowIndex h (r i)))
    (hc : StrictMono (fun j => columnIndex h (c j)))
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j)
    (hrowmode : ∀ i, ∃ u x, r i = Sum.inl (t,u,x))
    (hcolmode : ∀ j, ∃ v y, c j = Sum.inl (t,v,y)) :
    ∃ x y : Fin 64 → Fin (2 ^ h),
      (∀ i, r i = Sum.inl (t,i,x i)) ∧ (∀ j, c j = Sum.inl (t,j,y j)) := by
  exact Construction.AnchorGroups.representatives (rowIndex h) (columnIndex h)
    r c t hr hc hcopy hrowmode hcolmode
    (row_anchor_group_le t) (column_anchor_group_le t)

end Problem348.OrderedHost

end OAI
end
end

section
section
namespace OAI

/-!
# Anchor rigidity for the ordered canonical host

No-shattering, sparse anchor traces, twin classes, and the two independent
axis orders determine all anchor representatives.
-/
namespace Problem348.HostAnchorRigidity
open Construction AnchorRigidity

theorem modeLabel_eq_selectedMode {h : ℕ} (x : Position h) :
    modeLabel x = SelectedAnchors.mode x := by
  rcases x with ⟨t,u,z⟩ | a <;> rfl

theorem selected_rows_groupInjective {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j) :
    SelectedAnchors.GroupInjective r := by
  intro i j a b hi hj hm hg
  rcases a with ⟨t,u,x⟩
  rcases b with ⟨s,v,y⟩
  dsimp at hm hg
  subst s
  subst v
  exact selected_anchor_rows_unique r c hcopy hi hj

theorem selected_columns_groupInjective {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j) :
    SelectedAnchors.GroupInjective c := by
  intro i j a b hi hj hm hg
  rcases a with ⟨t,u,x⟩
  rcases b with ⟨s,v,y⟩
  dsimp at hm hg
  subst s
  subst v
  exact selected_anchor_columns_unique r c hcopy hi hj

/-- The sparse-column requirement follows from the actual host incidence bound. -/
theorem actual_columnSparse {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j) : ColumnSparse r c := by
  intro j hm hd ha
  have hb := SelectedAnchors.sparse_column_of_mode_none r firstCore (c j)
    (by
      intro i hi
      obtain ⟨t, ht⟩ := ha i hi
      obtain ⟨u,x,hx⟩ := exists_anchor_of_mode ht
      exact ⟨(t,u,x),hx⟩)
    (selected_rows_groupInjective r c hcopy)
    (by simpa only [modeLabel_eq_selectedMode] using hm) hd
  simpa only [hcopy] using hb

/-- The transpose sparse-row requirement, with no assumptions left over. -/
theorem actual_rowSparse {h : ℕ} (r c : Fin 64 → Position h)
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j) : RowSparse r c := by
  intro i hm hd ha
  have hb := SelectedAnchors.sparse_row_of_mode_none c firstCore (r i)
    (by
      intro j hj
      obtain ⟨t, ht⟩ := ha j hj
      obtain ⟨u,x,hx⟩ := exists_anchor_of_mode ht
      exact ⟨(t,u,x),hx⟩)
    (selected_columns_groupInjective r c hcopy)
    (by simpa only [modeLabel_eq_selectedMode] using hm) hd
  simpa only [hcopy] using hb

private theorem mode_nonempty_iff_anchor {h : ℕ} (x : Position h) :
    modeLabel x ≠ none ↔ ∃ a, x = Sum.inl a := by
  rcases x with ⟨t,u,z⟩ | a <;> simp [modeLabel]

theorem row_initial_of_indices {h : ℕ} (r : Fin 64 → Position h)
    (hr : StrictMono (fun i => OrderedHost.rowIndex h (r i))) :
    ∀ i j, i ≤ j → modeLabel (r j) ≠ none → modeLabel (r i) ≠ none := by
  intro i j hij hj
  rcases eq_or_lt_of_le hij with he | hlt
  · simpa only [he] using hj
  · apply (mode_nonempty_iff_anchor (r i)).mpr
    exact OrderedHost.row_anchor_initial (hr hlt)
      ((mode_nonempty_iff_anchor (r j)).mp hj)

theorem col_initial_of_indices {h : ℕ} (c : Fin 64 → Position h)
    (hc : StrictMono (fun i => OrderedHost.columnIndex h (c i))) :
    ∀ i j, i ≤ j → modeLabel (c j) ≠ none → modeLabel (c i) ≠ none := by
  intro i j hij hj
  rcases eq_or_lt_of_le hij with he | hlt
  · simpa only [he] using hj
  · apply (mode_nonempty_iff_anchor (c i)).mpr
    exact OrderedHost.column_anchor_initial (hc hlt)
      ((mode_nonempty_iff_anchor (c j)).mp hj)

/-- Every ordered copy of the fixed 64-by-64 anchor in the canonical host
uses precisely one mode, with its groups in the prescribed order. There are
no sparsity, majority, nonshattering, twin, or abstract-order premises. -/
theorem representatives_of_indices {h : ℕ} (r c : Fin 64 → Position h)
    (hr : StrictMono (fun i => OrderedHost.rowIndex h (r i)))
    (hc : StrictMono (fun j => OrderedHost.columnIndex h (c j)))
    (hcopy : ∀ i j, host (r i) (c j) = anchor64 i j) :
    ∃ (t : Mode h) (a b : Fin 64 → Fin (2 ^ h)),
      (∀ i, r i = Sum.inl (t,i,a i)) ∧
      (∀ j, c j = Sum.inl (t,j,b j)) := by
  obtain ⟨t, hmr, hmc⟩ := mode_constant_of_no_shattering r c hcopy
    (row_initial_of_indices r hr) (col_initial_of_indices c hc)
    (fun cs _ hnone => actual_nonshattering cs hnone)
    (actual_columnSparse r c hcopy) (actual_rowSparse r c hcopy)
  obtain ⟨a,b,ha,hb⟩ := OrderedHost.anchor_representatives_of_one_mode
    r c t hr hc hcopy (fun i => exists_anchor_of_mode (hmr i))
    (fun j => exists_anchor_of_mode (hmc j))
  exact ⟨t,a,b,ha,hb⟩

end Problem348.HostAnchorRigidity

end OAI
end
end

section
section
namespace OAI

/-! Exact level-based entry formulas for the canonical flat-class host. -/
namespace Problem348.Construction

theorem variableEntry_same_plus {h i : ℕ} {r c : VariablePosition h}
    (hr : AtLevel i true r) (hc : AtLevel i true c) :
    variableEntry r c = decide (node r ≤ node c) := by
  by_cases hi : i = h
  · simp [variableEntry, hr.1, hc.1, hi]
  · have hpr := hr.2.resolve_left hi
    have hpc := hc.2.resolve_left hi
    simp [variableEntry, hr.1, hc.1, hi, hpr, hpc]

theorem variableEntry_same_minus {h i : ℕ} {r c : VariablePosition h}
    (hr : AtLevel i false r) (hc : AtLevel i false c) :
    variableEntry r c =
      if i = h then decide (node r ≤ node c) else decide (node r < node c) := by
  by_cases hi : i = h
  · simp [variableEntry, hr.1, hc.1, hi]
  · have hpr := hr.2.resolve_left hi
    have hpc := hc.2.resolve_left hi
    simp [variableEntry, hr.1, hc.1, hi, hpr, hpc]

theorem variableEntry_child_parent_plus {h i : ℕ} {r c : VariablePosition h}
    (hr : AtLevel (i + 1) true r) (hc : AtLevel i true c) :
    variableEntry r c = decide (node r / 2 ≤ node c) := by
  have hi : i < h := by have := depth_le r; have hrd := hr.1; omega
  have hpc := hc.2.resolve_left (Nat.ne_of_lt hi)
  simp [variableEntry, hr.1, hc.1, hi, hpc, hr.2]

theorem variableEntry_child_parent_minus {h i : ℕ} {r c : VariablePosition h}
    (hr : AtLevel (i + 1) false r) (hc : AtLevel i false c) :
    variableEntry r c = decide (node r / 2 < node c) := by
  have hi : i < h := by have := depth_le r; have hrd := hr.1; omega
  have hpc := hc.2.resolve_left (Nat.ne_of_lt hi)
  simp [variableEntry, hr.1, hc.1, hi, hpc, hr.2]

/-- Maximal depth is exactly the shared leaf class. -/
theorem class_eq_leaf_of_depth_eq {h : ℕ} {v : VariablePosition h}
    (hv : depth v = h) : v.1 = Fin.last (2 * h) := by
  apply Fin.ext
  have := v.1.isLt
  simp only [Fin.val_last]
  unfold depth at hv
  omega

/-- At leaf depth a node labels a unique position, since its block has size one. -/
theorem node_eq_index_of_depth_eq {h : ℕ} {v : VariablePosition h}
    (hv : depth v = h) : node v = v.2.val := by
  simp [node, hv]

theorem eq_leaf_of_depth_eq {h : ℕ} {v : VariablePosition h}
    (hv : depth v = h) : v = (Fin.last (2 * h), v.2) := by
  exact Prod.ext (class_eq_leaf_of_depth_eq hv) rfl

end Problem348.Construction

end OAI
end
end

section
section
namespace OAI

/-!
# Localization of the four body modes

The arithmetic case analysis assumes the stated order inequalities and entry
values, independently of the host-position encoding.
-/

namespace Problem348.ModeLocalization

/-- The four entries of the body pattern, in row-major order. -/
def IsP (a b c d : Bool) : Prop :=
  a = true ∧ b = false ∧ c = true ∧ d = true

/-- Within either parity class, taking the parent preserves and reflects order. -/
theorem le_iff_parent_le_of_same_parity {p q : ℕ}
    (hparity : p % 2 = q % 2) :
    p ≤ q ↔ p / 2 ≤ q / 2 := by
  omega

theorem eq_of_parent_eq_of_same_parity {p q : ℕ}
    (hparity : p % 2 = q % 2) (hparent : p / 2 = q / 2) : p = q := by
  omega

/-- A `V_i^+` body cannot match `P`: its row order forces the zero to be one. -/
theorem vPlus_not_isP (p a b : ℕ) (horder : p / 2 ≤ a) :
    ¬ IsP true (decide (p / 2 ≤ b)) true (decide (a ≤ b)) := by
  simp only [IsP, true_and, decide_eq_false_iff_not, decide_eq_true_eq]
  omega

/-- A `V_i^-` body cannot match `P`: its row order forces the last one to be zero. -/
theorem vMinus_not_isP (p a b : ℕ) (horder : a ≤ p / 2) :
    ¬ IsP true (decide (a < b)) true (decide (p / 2 < b)) := by
  simp only [IsP, true_and, decide_eq_false_iff_not, decide_eq_true_eq]
  omega

/-- A `W_{i,d}^+` body cannot match `P`, including at the shared leaf level. -/
theorem wPlus_not_isP (p q b : ℕ) (horder : b ≤ q / 2)
    (hparity : p % 2 = q % 2) :
    ¬ IsP (decide (p / 2 ≤ b)) (decide (p ≤ q)) true true := by
  simp only [IsP, and_true, decide_eq_false_iff_not, decide_eq_true_eq]
  omega

/-- In a minus `W` mode, a body match can occur only on a shared leaf diagonal. -/
theorem wMinus_isP_implies_leaf_diagonal
    (h i p q b : ℕ) (horder : q / 2 ≤ b)
    (hparity : p % 2 = q % 2)
    (hbody : IsP (if i = h then decide (p ≤ q) else decide (p < q))
      (decide (p / 2 < b)) true true) :
    i = h ∧ p = q := by
  by_cases hleaf : i = h
  · simp only [hleaf, ite_true, IsP, and_true,
      decide_eq_false_iff_not, decide_eq_true_eq] at hbody
    constructor
    · exact hleaf
    · omega
  · simp only [hleaf, ite_false, IsP, and_true,
      decide_eq_false_iff_not, decide_eq_true_eq] at hbody
    omega

/-- Conversely, the diagonal leaf choice with its parent column gives `P`. -/
theorem wMinus_leaf_diagonal_isP (h p : ℕ) :
    IsP (if h = h then decide (p ≤ p) else decide (p < p))
      (decide (p / 2 < p / 2)) true true := by
  simp [IsP]

end Problem348.ModeLocalization

end OAI
end
end

section
section
namespace OAI

/-! Horizontal body localization for the canonical host entry table. -/
namespace Problem348.Construction
open ModeLocalization

theorem horizontal_plus_entries_impossible {h i : ℕ} {r c₀ c₁ : VariablePosition h}
    (hr : AtLevel (i + 1) true r) (hc₀ : AtLevel i true c₀)
    (hc₁ : AtLevel (i + 1) true c₁)
    (horder : node c₀ ≤ node c₁ / 2) (hparity : node r % 2 = node c₁ % 2)
    (h₀ : variableEntry r c₀ = true) (h₁ : variableEntry r c₁ = false) : False := by
  apply wPlus_not_isP (node r) (node c₁) (node c₀) horder hparity
  exact ⟨by simpa only [variableEntry_child_parent_plus hr hc₀] using h₀,
    by simpa only [variableEntry_same_plus hr hc₁] using h₁, rfl, rfl⟩

/-- A W- body forces the shared leaf diagonal, as literal variable positions. -/
theorem horizontal_minus_entries_localize {h i : ℕ} {r c₀ c₁ : VariablePosition h}
    (hr : AtLevel (i + 1) false r) (hc₀ : AtLevel (i + 1) false c₀)
    (hc₁ : AtLevel i false c₁)
    (horder : node c₀ / 2 ≤ node c₁) (hparity : node r % 2 = node c₀ % 2)
    (h₀ : variableEntry r c₀ = true) (h₁ : variableEntry r c₁ = false) :
    i + 1 = h ∧ ∃ z : Fin (2 ^ h),
      r = (Fin.last (2 * h), z) ∧ c₀ = (Fin.last (2 * h), z) := by
  have hb : IsP
      (if i + 1 = h then decide (node r ≤ node c₀) else decide (node r < node c₀))
      (decide (node r / 2 < node c₁)) true true := by
    exact ⟨by simpa only [variableEntry_same_minus hr hc₀] using h₀,
      by simpa only [variableEntry_child_parent_minus hr hc₁] using h₁, rfl, rfl⟩
  obtain ⟨hi, heq⟩ := wMinus_isP_implies_leaf_diagonal h (i + 1) (node r) (node c₀) (node c₁) horder hparity hb
  have hrd : depth r = h := hr.1.trans hi
  have hcd : depth c₀ = h := hc₀.1.trans hi
  have hz : r.2 = c₀.2 := by
    apply Fin.ext
    simpa only [node_eq_index_of_depth_eq hrd, node_eq_index_of_depth_eq hcd] using heq
  exact ⟨hi, r.2, eq_leaf_of_depth_eq hrd, by simpa only [hz] using eq_leaf_of_depth_eq hcd⟩

end Problem348.Construction

end OAI
end
end

section
section
namespace OAI

/-!
# Vertical-mode localization for the concrete host

The only additional input to the exclusion theorems is the node inequality
provided by the tree order. All entry values and role memberships follow
from the host definitions.
-/

namespace Problem348.Construction

/-- Extend the variable node index to all positions. -/
def positionNode {h : ℕ} : Position h → ℕ
  | Sum.inr (Sum.inl v) => node v
  | _ => 0

@[simp] theorem positionNode_variable {h : ℕ} (v : VariablePosition h) :
    positionNode (Sum.inr (Sum.inl v)) = node v := rfl

theorem variableEntry_same_level {h i : ℕ} {r c : VariablePosition h}
    (s : Bool) (hr : AtLevel i s r) (hc : AtLevel i s c) :
    variableEntry r c =
      if i = h then decide (node r ≤ node c)
      else if s then decide (node r ≤ node c) else decide (node r < node c) := by
  rcases hr with ⟨hrd, hrs⟩
  rcases hc with ⟨hcd, hcs⟩
  by_cases hi : i = h
  · simp [variableEntry, hrd, hcd, hi]
  · have hrp : plus r = s := hrs.resolve_left hi
    have hcp : plus c = s := hcs.resolve_left hi
    simp [variableEntry, hrd, hcd, hi, hrp, hcp]

theorem variableEntry_child_parent {h i : ℕ} {r c : VariablePosition h}
    (s : Bool) (hr : AtLevel (i + 1) s r) (hc : AtLevel i s c) :
    variableEntry r c =
      if s then decide (node r / 2 ≤ node c) else decide (node r / 2 < node c) := by
  rcases hr with ⟨hrd, hrs⟩
  rcases hc with ⟨hcd, hcs⟩
  have hih : i < h := by have := depth_le r; omega
  have hcp : plus c = s := hcs.resolve_left (by omega)
  have hsign : i + 1 = h ∨ plus r = s := hrs
  simp [variableEntry, hrd, hcd, hih, hcp, hsign]

theorem rowRole_vertical_variable {h : ℕ} {t : Mode h} {j : Fin 2}
    {x : Position h} (hk : kind t < 2) (hx : rowRole t j x) :
    ∃ v : VariablePosition h, x = Sum.inr (Sum.inl v) := by
  rcases x with a | (v | d)
  · simp [rowRole] at hx
  · exact ⟨v, rfl⟩
  · simp [rowRole] at hx
    omega

theorem colRole_vertical_first_dummy {h : ℕ} {t : Mode h}
    {x : Position h} (hk : kind t < 2) (hx : colRole t 0 x) :
    ∃ d : Fin (2 ^ h), x = Sum.inr (Sum.inr d) := by
  rcases x with a | (v | d)
  · simp [colRole] at hx
  · simp [colRole, hk] at hx
  · exact ⟨d, rfl⟩

theorem colRole_vertical_second_variable {h : ℕ} {t : Mode h}
    {x : Position h} (_hk : kind t < 2) (hx : colRole t 1 x) :
    ∃ v : VariablePosition h, x = Sum.inr (Sum.inl v) := by
  rcases x with a | (v | d)
  · simp [colRole] at hx
  · exact ⟨v, rfl⟩
  · simp [colRole] at hx

/-- An actual vertical plus mode of the host cannot contain the body. -/
theorem host_vertical_plus_not_body {h : ℕ} {t : Mode h}
    (hk : kind t = 0) {r₀ r₁ c₀ c₁ : Position h}
    (hr₀ : rowRole t 0 r₀) (hr₁ : rowRole t 1 r₁)
    (hc₀ : colRole t 0 c₀) (hc₁ : colRole t 1 c₁)
    (horder : positionNode r₀ / 2 ≤ positionNode r₁) :
    ¬ ModeLocalization.IsP (host r₀ c₀) (host r₀ c₁)
      (host r₁ c₀) (host r₁ c₁) := by
  have hkt : kind t < 2 := by omega
  obtain ⟨x, rfl⟩ := rowRole_vertical_variable hkt hr₀
  obtain ⟨y, rfl⟩ := rowRole_vertical_variable hkt hr₁
  obtain ⟨d, rfl⟩ := colRole_vertical_first_dummy hkt hc₀
  obtain ⟨z, rfl⟩ := colRole_vertical_second_variable hkt hc₁
  have hx : AtLevel (level t) true x := by simpa [rowRole, hk] using hr₀
  have hy : AtLevel (level t - 1) true y := by simpa [rowRole, hk] using hr₁
  have hz : AtLevel (level t - 1) true z := by simpa [colRole, hk] using hc₁
  have hl : level t - 1 + 1 = level t := by have := level_pos t; omega
  have hparent := variableEntry_child_parent true (hl ▸ hx) hz
  have hsame := variableEntry_same_level true hy hz
  have hnotleaf : level t - 1 ≠ h := by
    have := level_le t
    have := level_pos t
    omega
  simpa [host, hparent, hsame, hnotleaf, positionNode] using
    ModeLocalization.vPlus_not_isP (node x) (node y) (node z) horder

/-- An actual vertical minus mode of the host cannot contain the body. -/
theorem host_vertical_minus_not_body {h : ℕ} {t : Mode h}
    (hk : kind t = 1) {r₀ r₁ c₀ c₁ : Position h}
    (hr₀ : rowRole t 0 r₀) (hr₁ : rowRole t 1 r₁)
    (hc₀ : colRole t 0 c₀) (hc₁ : colRole t 1 c₁)
    (horder : positionNode r₀ ≤ positionNode r₁ / 2) :
    ¬ ModeLocalization.IsP (host r₀ c₀) (host r₀ c₁)
      (host r₁ c₀) (host r₁ c₁) := by
  have hkt : kind t < 2 := by omega
  obtain ⟨x, rfl⟩ := rowRole_vertical_variable hkt hr₀
  obtain ⟨y, rfl⟩ := rowRole_vertical_variable hkt hr₁
  obtain ⟨d, rfl⟩ := colRole_vertical_first_dummy hkt hc₀
  obtain ⟨z, rfl⟩ := colRole_vertical_second_variable hkt hc₁
  have hx : AtLevel (level t - 1) false x := by simpa [rowRole, hk] using hr₀
  have hy : AtLevel (level t) false y := by simpa [rowRole, hk] using hr₁
  have hz : AtLevel (level t - 1) false z := by simpa [colRole, hk] using hc₁
  have hl : level t - 1 + 1 = level t := by have := level_pos t; omega
  have hparent := variableEntry_child_parent false (hl ▸ hy) hz
  have hsame := variableEntry_same_level false hx hz
  have hnotleaf : level t - 1 ≠ h := by
    have := level_le t
    have := level_pos t
    omega
  simpa [host, hparent, hsame, hnotleaf, positionNode] using
    ModeLocalization.vMinus_not_isP (node y) (node x) (node z) horder

end Problem348.Construction

end OAI
end
end

section
section
namespace OAI

/-!
# Exhaustive localization of bodies in canonical host modes

All entry and role hypotheses refer to the actual canonical host. The numerical
order premise is exactly the four parent comparisons supplied by the two tree
orders.
-/
namespace Problem348.Construction
open ModeLocalization

/-- The necessary parent comparison for an ordered body in each of the six modes. -/
def BodyNodeOrder {h : ℕ} (t : Mode h) (r₀ r₁ c₀ c₁ : Position h) : Prop :=
  if kind t = 0 then positionNode r₀ / 2 ≤ positionNode r₁
  else if kind t = 1 then positionNode r₀ ≤ positionNode r₁ / 2
  else if kind t < 4 then positionNode c₀ ≤ positionNode c₁ / 2
  else positionNode c₀ / 2 ≤ positionNode c₁

theorem rowRole_first_variable {h : ℕ} {t : Mode h} {x : Position h}
    (hx : rowRole t 0 x) : ∃ v : VariablePosition h, x = Sum.inr (Sum.inl v) := by
  rcases x with a | (v | d)
  · simp [rowRole] at hx
  · exact ⟨v, rfl⟩
  · simp [rowRole] at hx

theorem colRole_horizontal_variable {h : ℕ} {t : Mode h} {j : Fin 2}
    {x : Position h} (hk : 2 ≤ kind t) (hx : colRole t j x) :
    ∃ v : VariablePosition h, x = Sum.inr (Sum.inl v) := by
  rcases x with a | (v | d)
  · simp [colRole] at hx
  · exact ⟨v, rfl⟩
  · simp [colRole] at hx
    omega

/-- The horizontal plus roles cannot realize the body's top row. -/
theorem host_horizontal_plus_not_body {h : ℕ} {t : Mode h}
    (hklo : 2 ≤ kind t) (hkhi : kind t < 4) {r₀ r₁ c₀ c₁ : Position h}
    (hr₀ : rowRole t 0 r₀) (hc₀ : colRole t 0 c₀) (hc₁ : colRole t 1 c₁)
    (horder : positionNode c₀ ≤ positionNode c₁ / 2) :
    ¬ IsP (host r₀ c₀) (host r₀ c₁) (host r₁ c₀) (host r₁ c₁) := by
  obtain ⟨r, rfl⟩ := rowRole_first_variable hr₀
  obtain ⟨c, rfl⟩ := colRole_horizontal_variable hklo hc₀
  obtain ⟨d, rfl⟩ := colRole_horizontal_variable hklo hc₁
  have hk0 : kind t ≠ 0 := by omega
  have hk1 : kind t ≠ 1 := by omega
  have hk2 : ¬ kind t < 2 := by omega
  have hr : AtLevel (level t) true r ∧ node r % 2 = kind t % 2 := by
    simpa [rowRole, hk0, hk1, hkhi] using hr₀
  have hc : AtLevel (level t - 1) true c := by
    simpa [colRole, hk2, hkhi] using hc₀
  have hd : AtLevel (level t) true d ∧ node d % 2 = kind t % 2 := by
    simpa [colRole, hk2, hkhi] using hc₁
  have hl : level t - 1 + 1 = level t := by have := level_pos t; omega
  intro hb
  exact horizontal_plus_entries_impossible (hl ▸ hr.1) hc (hl ▸ hd.1)
    horder (hr.2.trans hd.2.symm) hb.1 hb.2.1

/-- The horizontal minus roles force the body's top-left entry onto a shared leaf. -/
theorem host_horizontal_minus_leaf_diagonal {h : ℕ} {t : Mode h}
    (hklo : 4 ≤ kind t) {r₀ r₁ c₀ c₁ : Position h}
    (hr₀ : rowRole t 0 r₀) (hc₀ : colRole t 0 c₀) (hc₁ : colRole t 1 c₁)
    (horder : positionNode c₀ / 2 ≤ positionNode c₁)
    (hb : IsP (host r₀ c₀) (host r₀ c₁) (host r₁ c₀) (host r₁ c₁)) :
    ∃ z : Fin (2 ^ h),
      r₀ = Sum.inr (Sum.inl (Fin.last (2 * h), z)) ∧
      c₀ = Sum.inr (Sum.inl (Fin.last (2 * h), z)) := by
  obtain ⟨r, rfl⟩ := rowRole_first_variable hr₀
  obtain ⟨c, rfl⟩ := colRole_horizontal_variable (by omega) hc₀
  obtain ⟨d, rfl⟩ := colRole_horizontal_variable (by omega) hc₁
  have hk0 : kind t ≠ 0 := by omega
  have hk1 : kind t ≠ 1 := by omega
  have hk2 : ¬ kind t < 2 := by omega
  have hk4 : ¬ kind t < 4 := by omega
  have hr : AtLevel (level t) false r ∧ node r % 2 = kind t % 2 := by
    simpa [rowRole, hk0, hk1, hk4] using hr₀
  have hc : AtLevel (level t) false c ∧ node c % 2 = kind t % 2 := by
    simpa [colRole, hk2, hk4] using hc₀
  have hd : AtLevel (level t - 1) false d := by
    simpa [colRole, hk2, hk4] using hc₁
  have hl : level t - 1 + 1 = level t := by have := level_pos t; omega
  obtain ⟨_, z, hz, hcz⟩ := horizontal_minus_entries_localize
    (hl ▸ hr.1) (hl ▸ hc.1) hd horder (hr.2.trans hc.2.symm) hb.1 hb.2.1
  exact ⟨z, congrArg (fun v => Sum.inr (Sum.inl v)) hz,
    congrArg (fun v => Sum.inr (Sum.inl v)) hcz⟩

/-- Under `BodyNodeOrder`, every ordered body in any canonical mode has its
top-left cell on the shared leaf diagonal. -/
theorem host_body_leaf_diagonal {h : ℕ} {t : Mode h} {r₀ r₁ c₀ c₁ : Position h}
    (hr₀ : rowRole t 0 r₀) (hr₁ : rowRole t 1 r₁)
    (hc₀ : colRole t 0 c₀) (hc₁ : colRole t 1 c₁)
    (horder : BodyNodeOrder t r₀ r₁ c₀ c₁)
    (hb : IsP (host r₀ c₀) (host r₀ c₁) (host r₁ c₀) (host r₁ c₁)) :
    ∃ z : Fin (2 ^ h),
      r₀ = Sum.inr (Sum.inl (Fin.last (2 * h), z)) ∧
      c₀ = Sum.inr (Sum.inl (Fin.last (2 * h), z)) := by
  by_cases hk0 : kind t = 0
  · exact False.elim (host_vertical_plus_not_body hk0 hr₀ hr₁ hc₀ hc₁
      (by simpa [BodyNodeOrder, hk0] using horder) hb)
  by_cases hk1 : kind t = 1
  · exact False.elim (host_vertical_minus_not_body hk1 hr₀ hr₁ hc₀ hc₁
      (by simpa [BodyNodeOrder, hk0, hk1] using horder) hb)
  by_cases hk4 : kind t < 4
  · exact False.elim (host_horizontal_plus_not_body (by omega) hk4 hr₀ hc₀ hc₁
      (by simpa [BodyNodeOrder, hk0, hk1, hk4] using horder) hb)
  · exact host_horizontal_minus_leaf_diagonal (by omega) hr₀ hc₀ hc₁
      (by simpa [BodyNodeOrder, hk0, hk1, hk4] using horder) hb

end Problem348.Construction

end OAI
end
end

section
section
namespace OAI

/-!
Comparison lemmas for the concrete depth-first tree orders used in
mode localization.
-/

namespace Problem348.Construction

open TreePositions

theorem eq_plusPos_of_atLevel {h i : ℕ} {v : VariablePosition h}
    (hv : AtLevel i true v) :
    v = TreePositions.plusPos i (hv.1 ▸ depth_le v) v.2 := by
  apply Prod.ext
  · apply Fin.ext
    have hc := v.1.isLt
    obtain ⟨hd, hs⟩ := hv
    simp only [depth] at hd
    change v.1.val = 2 * i
    rcases hs with hi | hs
    · omega
    · simp only [plus, decide_eq_true_eq] at hs
      omega
  · rfl

theorem eq_minusPos_of_atLevel {h i : ℕ} {v : VariablePosition h}
    (hv : AtLevel i false v) :
    v = TreePositions.minusPos i (hv.1 ▸ depth_le v) v.2 := by
  apply Prod.ext
  · apply Fin.ext
    have hc := v.1.isLt
    obtain ⟨hd, hs⟩ := hv
    simp only [depth] at hd
    change v.1.val = if i = h then 2 * h else 2 * i + 1
    split_ifs with hi
    · omega
    · rcases hs with hs | hs
      · exact (hi hs).elim
      · simp only [plus, decide_eq_false_iff_not] at hs
        omega
  · rfl

theorem node_eq_level_node {h i : ℕ} {v : VariablePosition h}
    (hv : depth v = i) : node v = TreePositions.node i v.2 := by
  simp [node, TreePositions.node, hv]

/-- Row plus child precedes row plus parent exactly for the stated parent-node inequality. -/
theorem row_plus_lt_iff {h i : ℕ} {child parent : VariablePosition h}
    (hc : AtLevel (i + 1) true child) (hp : AtLevel i true parent) :
    TreePositions.rowKey h child < TreePositions.rowKey h parent ↔
      node child / 2 ≤ node parent := by
  have hi : i < h := by have := hc.1 ▸ depth_le child; omega
  have hn₁ := node_eq_level_node hc.1
  have hn₂ := node_eq_level_node hp.1
  rw [hn₁, hn₂, eq_plusPos_of_atLevel hc, eq_plusPos_of_atLevel hp]
  exact TreePositions.row_plus_child_lt_parent hi child.2 parent.2

/-- Row minus parent precedes row minus child exactly for the parent-node inequality. -/
theorem row_minus_lt_iff {h i : ℕ} {child parent : VariablePosition h}
    (hc : AtLevel (i + 1) false child) (hp : AtLevel i false parent) :
    TreePositions.rowKey h parent < TreePositions.rowKey h child ↔
      node parent ≤ node child / 2 := by
  have hi : i < h := by have := hc.1 ▸ depth_le child; omega
  have hn₁ := node_eq_level_node hc.1
  have hn₂ := node_eq_level_node hp.1
  rw [hn₁, hn₂, eq_minusPos_of_atLevel hc, eq_minusPos_of_atLevel hp]
  exact TreePositions.row_minus_parent_lt_child hi child.2 parent.2

/-- Column plus parent precedes column plus child exactly for the parent-node inequality. -/
theorem column_plus_lt_iff {h i : ℕ} {child parent : VariablePosition h}
    (hc : AtLevel (i + 1) true child) (hp : AtLevel i true parent) :
    TreePositions.columnKey h parent < TreePositions.columnKey h child ↔
      node parent ≤ node child / 2 := by
  have hi : i < h := by have := hc.1 ▸ depth_le child; omega
  have hn₁ := node_eq_level_node hc.1
  have hn₂ := node_eq_level_node hp.1
  rw [hn₁, hn₂, eq_plusPos_of_atLevel hc, eq_plusPos_of_atLevel hp]
  exact TreePositions.column_plus_parent_lt_child hi child.2 parent.2

/-- Column minus child precedes column minus parent exactly for the parent-node inequality. -/
theorem column_minus_lt_iff {h i : ℕ} {child parent : VariablePosition h}
    (hc : AtLevel (i + 1) false child) (hp : AtLevel i false parent) :
    TreePositions.columnKey h child < TreePositions.columnKey h parent ↔
      node child / 2 ≤ node parent := by
  have hi : i < h := by have := hc.1 ▸ depth_le child; omega
  have hn₁ := node_eq_level_node hc.1
  have hn₂ := node_eq_level_node hp.1
  rw [hn₁, hn₂, eq_minusPos_of_atLevel hc, eq_minusPos_of_atLevel hp]
  exact TreePositions.column_minus_child_lt_parent hi child.2 parent.2

end Problem348.Construction

end OAI
end
end

section
section
namespace OAI

/-!
# From increasing body positions to the four node-order inequalities

These lemmas use the actual host roles and tree keys. Each independent
coordinate map reflects the corresponding tree-key order on variable
positions; no mode-specific ordering is assumed.
-/


namespace Problem348.Construction

theorem vertical_plus_node_order {h : ℕ} {α : Type uAlpha} [Preorder α]
    (rowIndex : Position h → α)
    (hkey : ∀ v w : VariablePosition h,
      rowIndex (Sum.inr (Sum.inl v)) < rowIndex (Sum.inr (Sum.inl w)) →
        TreePositions.rowKey h v < TreePositions.rowKey h w)
    {t : Mode h} (hk : kind t = 0) {r₀ r₁ : Position h}
    (hr₀ : rowRole t 0 r₀) (hr₁ : rowRole t 1 r₁)
    (hrow : rowIndex r₀ < rowIndex r₁) :
    positionNode r₀ / 2 ≤ positionNode r₁ := by
  have hkt : kind t < 2 := by omega
  obtain ⟨x, rfl⟩ := rowRole_vertical_variable hkt hr₀
  obtain ⟨y, rfl⟩ := rowRole_vertical_variable hkt hr₁
  have hx : AtLevel (level t) true x := by simpa [rowRole, hk] using hr₀
  have hy : AtLevel (level t - 1) true y := by simpa [rowRole, hk] using hr₁
  have hl : level t - 1 + 1 = level t := by have := level_pos t; omega
  exact (row_plus_lt_iff (hl ▸ hx) hy).mp (hkey x y hrow)

theorem vertical_minus_node_order {h : ℕ} {α : Type uAlpha} [Preorder α]
    (rowIndex : Position h → α)
    (hkey : ∀ v w : VariablePosition h,
      rowIndex (Sum.inr (Sum.inl v)) < rowIndex (Sum.inr (Sum.inl w)) →
        TreePositions.rowKey h v < TreePositions.rowKey h w)
    {t : Mode h} (hk : kind t = 1) {r₀ r₁ : Position h}
    (hr₀ : rowRole t 0 r₀) (hr₁ : rowRole t 1 r₁)
    (hrow : rowIndex r₀ < rowIndex r₁) :
    positionNode r₀ ≤ positionNode r₁ / 2 := by
  have hkt : kind t < 2 := by omega
  obtain ⟨x, rfl⟩ := rowRole_vertical_variable hkt hr₀
  obtain ⟨y, rfl⟩ := rowRole_vertical_variable hkt hr₁
  have hx : AtLevel (level t - 1) false x := by simpa [rowRole, hk] using hr₀
  have hy : AtLevel (level t) false y := by simpa [rowRole, hk] using hr₁
  have hl : level t - 1 + 1 = level t := by have := level_pos t; omega
  exact (row_minus_lt_iff (hl ▸ hy) hx).mp (hkey x y hrow)

theorem horizontal_plus_node_order {h : ℕ} {α : Type uAlpha} [Preorder α]
    (colIndex : Position h → α)
    (hkey : ∀ v w : VariablePosition h,
      colIndex (Sum.inr (Sum.inl v)) < colIndex (Sum.inr (Sum.inl w)) →
        TreePositions.columnKey h v < TreePositions.columnKey h w)
    {t : Mode h} (hklo : 2 ≤ kind t) (hkhi : kind t < 4)
    {c₀ c₁ : Position h} (hc₀ : colRole t 0 c₀) (hc₁ : colRole t 1 c₁)
    (hcol : colIndex c₀ < colIndex c₁) :
    positionNode c₀ ≤ positionNode c₁ / 2 := by
  obtain ⟨x, rfl⟩ := colRole_horizontal_variable hklo hc₀
  obtain ⟨y, rfl⟩ := colRole_horizontal_variable hklo hc₁
  have hkn : ¬ kind t < 2 := by omega
  have hx : AtLevel (level t - 1) true x := by
    simpa [colRole, hkn, hkhi] using hc₀
  have hy : AtLevel (level t) true y := by
    have hy' : AtLevel (level t) true y ∧ node y % 2 = kind t % 2 := by
      simpa [colRole, hkn, hkhi] using hc₁
    exact hy'.1
  have hl : level t - 1 + 1 = level t := by have := level_pos t; omega
  exact (column_plus_lt_iff (hl ▸ hy) hx).mp (hkey x y hcol)

theorem horizontal_minus_node_order {h : ℕ} {α : Type uAlpha} [Preorder α]
    (colIndex : Position h → α)
    (hkey : ∀ v w : VariablePosition h,
      colIndex (Sum.inr (Sum.inl v)) < colIndex (Sum.inr (Sum.inl w)) →
        TreePositions.columnKey h v < TreePositions.columnKey h w)
    {t : Mode h} (hk : 4 ≤ kind t)
    {c₀ c₁ : Position h} (hc₀ : colRole t 0 c₀) (hc₁ : colRole t 1 c₁)
    (hcol : colIndex c₀ < colIndex c₁) :
    positionNode c₀ / 2 ≤ positionNode c₁ := by
  have hklo : 2 ≤ kind t := by omega
  obtain ⟨x, rfl⟩ := colRole_horizontal_variable hklo hc₀
  obtain ⟨y, rfl⟩ := colRole_horizontal_variable hklo hc₁
  have hkn : ¬ kind t < 2 := by omega
  have hkhi : ¬ kind t < 4 := by omega
  have hx : AtLevel (level t) false x := by
    have hx' : AtLevel (level t) false x ∧ node x % 2 = kind t % 2 := by
      simpa [colRole, hkn, hkhi] using hc₀
    exact hx'.1
  have hy : AtLevel (level t - 1) false y := by
    simpa [colRole, hkn, hkhi] using hc₁
  have hl : level t - 1 + 1 = level t := by have := level_pos t; omega
  exact (column_minus_lt_iff (hl ▸ hx) hy).mp (hkey x y hcol)

/-- Increasing positions in the actual two tree orders satisfy precisely the
node-order premise of the exhaustive six-mode localization theorem. -/
theorem bodyNodeOrder_of_ordered {h : ℕ} {R : Type uR} {C : Type uC} [Preorder R] [Preorder C]
    (rowIndex : Position h → R) (colIndex : Position h → C)
    (hrowKey : ∀ v w : VariablePosition h,
      rowIndex (Sum.inr (Sum.inl v)) < rowIndex (Sum.inr (Sum.inl w)) →
        TreePositions.rowKey h v < TreePositions.rowKey h w)
    (hcolKey : ∀ v w : VariablePosition h,
      colIndex (Sum.inr (Sum.inl v)) < colIndex (Sum.inr (Sum.inl w)) →
        TreePositions.columnKey h v < TreePositions.columnKey h w)
    {t : Mode h} {r₀ r₁ c₀ c₁ : Position h}
    (hr₀ : rowRole t 0 r₀) (hr₁ : rowRole t 1 r₁)
    (hc₀ : colRole t 0 c₀) (hc₁ : colRole t 1 c₁)
    (hrow : rowIndex r₀ < rowIndex r₁) (hcol : colIndex c₀ < colIndex c₁) :
    BodyNodeOrder t r₀ r₁ c₀ c₁ := by
  unfold BodyNodeOrder
  split_ifs with hk₀ hk₁ hk₄
  · exact vertical_plus_node_order rowIndex hrowKey hk₀ hr₀ hr₁ hrow
  · exact vertical_minus_node_order rowIndex hrowKey hk₁ hr₀ hr₁ hrow
  · exact horizontal_plus_node_order colIndex hcolKey (by omega) hk₄ hc₀ hc₁ hcol
  · exact horizontal_minus_node_order colIndex hcolKey (by omega) hc₀ hc₁ hcol

/-- The concrete host localization conclusion, with the numerical mode-order
certificate discharged by the constructed key orders and increasing coordinates. -/
theorem host_ordered_body_leaf_diagonal {h : ℕ} {R : Type uR} {C : Type uC}
    [Preorder R] [Preorder C]
    (rowIndex : Position h → R) (colIndex : Position h → C)
    (hrowKey : ∀ v w : VariablePosition h,
      rowIndex (Sum.inr (Sum.inl v)) < rowIndex (Sum.inr (Sum.inl w)) →
        TreePositions.rowKey h v < TreePositions.rowKey h w)
    (hcolKey : ∀ v w : VariablePosition h,
      colIndex (Sum.inr (Sum.inl v)) < colIndex (Sum.inr (Sum.inl w)) →
        TreePositions.columnKey h v < TreePositions.columnKey h w)
    {t : Mode h} {r₀ r₁ c₀ c₁ : Position h}
    (hr₀ : rowRole t 0 r₀) (hr₁ : rowRole t 1 r₁)
    (hc₀ : colRole t 0 c₀) (hc₁ : colRole t 1 c₁)
    (hrow : rowIndex r₀ < rowIndex r₁) (hcol : colIndex c₀ < colIndex c₁)
    (hb : ModeLocalization.IsP (host r₀ c₀) (host r₀ c₁)
      (host r₁ c₀) (host r₁ c₁)) :
    ∃ z : Fin (2 ^ h),
      r₀ = Sum.inr (Sum.inl (Fin.last (2 * h), z)) ∧
      c₀ = Sum.inr (Sum.inl (Fin.last (2 * h), z)) := by
  exact host_body_leaf_diagonal hr₀ hr₁ hc₀ hc₁
    (bodyNodeOrder_of_ordered rowIndex colIndex hrowKey hcolKey hr₀ hr₁ hc₀ hc₁ hrow hcol) hb

end Problem348.Construction

end OAI
end
end

section
section
namespace OAI

/-!
# Body localization for the independent host enumerations

The canonical full-axis enumeration gives exhaustive body-mode localization.
All comparisons use the actual row and column indices; no order-reflection
certificate remains as an assumption.
-/

namespace Problem348.OrderedHost

open Construction

theorem rowIndex_reflects_variable_order {h : ℕ} (v w : VariablePosition h)
    (hvw : rowIndex h (.inr (.inl v)) < rowIndex h (.inr (.inl w))) :
    TreePositions.rowKey h v < TreePositions.rowKey h w :=
  (rowIndex_variable_lt_iff v w).mp hvw

theorem columnIndex_reflects_variable_order {h : ℕ} (v w : VariablePosition h)
    (hvw : columnIndex h (.inr (.inl v)) < columnIndex h (.inr (.inl w))) :
    TreePositions.columnKey h v < TreePositions.columnKey h w :=
  (columnIndex_variable_lt_iff v w).mp hvw

/-- The actual independent enumerations discharge all four numerical mode orders. -/
theorem bodyNodeOrder_of_indices {h : ℕ} {t : Mode h}
    {r₀ r₁ c₀ c₁ : Position h}
    (hr₀ : rowRole t 0 r₀) (hr₁ : rowRole t 1 r₁)
    (hc₀ : colRole t 0 c₀) (hc₁ : colRole t 1 c₁)
    (hrow : rowIndex h r₀ < rowIndex h r₁)
    (hcol : columnIndex h c₀ < columnIndex h c₁) :
    BodyNodeOrder t r₀ r₁ c₀ c₁ :=
  bodyNodeOrder_of_ordered (rowIndex h) (columnIndex h)
    rowIndex_reflects_variable_order columnIndex_reflects_variable_order
    hr₀ hr₁ hc₀ hc₁ hrow hcol

/-- Every correctly assigned ordered body in the canonical host has its
top-left cell on the shared leaf diagonal. -/
theorem body_leaf_diagonal {h : ℕ} {t : Mode h}
    {r₀ r₁ c₀ c₁ : Position h}
    (hr₀ : rowRole t 0 r₀) (hr₁ : rowRole t 1 r₁)
    (hc₀ : colRole t 0 c₀) (hc₁ : colRole t 1 c₁)
    (hrow : rowIndex h r₀ < rowIndex h r₁)
    (hcol : columnIndex h c₀ < columnIndex h c₁)
    (hb : ModeLocalization.IsP (host r₀ c₀) (host r₀ c₁)
      (host r₁ c₀) (host r₁ c₁)) :
    ∃ z : Fin (2 ^ h),
      r₀ = Sum.inr (Sum.inl (Fin.last (2 * h), z)) ∧
      c₀ = Sum.inr (Sum.inl (Fin.last (2 * h), z)) :=
  host_ordered_body_leaf_diagonal (rowIndex h) (columnIndex h)
    rowIndex_reflects_variable_order columnIndex_reflects_variable_order
    hr₀ hr₁ hc₀ hc₁ hrow hcol hb

end Problem348.OrderedHost

end OAI
end
end

section
section
namespace OAI

/-!
# Exact body signatures and extraction of body roles

All signatures refer to `fixedH`, including its zero entries.
-/

namespace Problem348.BodySignatures52

def anchorIndex (u : Fin 64) : Fin 66 := ⟨u.val, by omega⟩

def bodyIndex (b : Fin 2) : Fin 66 := ⟨64 + b.val, by omega⟩

theorem fixedH_anchor_anchor (u v : Fin 64) :
    fixedH (anchorIndex u) (anchorIndex v) = anchor64 u v := by
  simp [fixedH, anchorIndex, u.isLt, v.isLt]

theorem fixedH_body_anchor (b : Fin 2) (v : Fin 64) :
    fixedH (bodyIndex b) (anchorIndex v) = decide (v.val = b.val) := by
  fin_cases b <;> simp [fixedH, bodyIndex, anchorIndex, v.isLt]

theorem fixedH_anchor_body (u : Fin 64) (b : Fin 2) :
    fixedH (anchorIndex u) (bodyIndex b) = decide (u.val = b.val) := by
  fin_cases b <;> simp [fixedH, bodyIndex, anchorIndex, u.isLt]

theorem fixedH_body_body (b c : Fin 2) :
    fixedH (bodyIndex b) (bodyIndex c) = decide (b.val = 1 ∨ c.val = 0) := by
  fin_cases b <;> fin_cases c <;> rfl

/-- No anchor row has either of the two body-row signatures. -/
theorem anchor64_row_ne_body_signature (u : Fin 64) (b : Fin 2) :
    (fun v => anchor64 u v) ≠ (fun v : Fin 64 => decide (v.val = b.val)) := by
  intro h
  have h2 := congrFun h (2 : Fin 64)
  have h3 := congrFun h (3 : Fin 64)
  fin_cases b <;> simp [anchor64] at h2 h3 <;> omega

/-- No anchor column has either of the two body-column signatures. -/
theorem anchor64_col_ne_body_signature (v : Fin 64) (b : Fin 2) :
    (fun u => anchor64 u v) ≠ (fun u : Fin 64 => decide (u.val = b.val)) := by
  intro h
  have h2 := congrFun h (2 : Fin 64)
  have h3 := congrFun h (3 : Fin 64)
  fin_cases b <;> simp [anchor64] at h2 h3 <;> omega

theorem zero_ne_body_signature (b : Fin 2) :
    (fun _ : Fin 64 => false) ≠ (fun v : Fin 64 => decide (v.val = b.val)) := by
  intro h
  have hb := congrFun h (⟨b.val, by omega⟩ : Fin 64)
  simp at hb

theorem copy_body_row_signature {n : ℕ} {A : BinaryMatrix n}
    {rc : IncreasingMap 66 n × IncreasingMap 66 n}
    (hcopy : rc ∈ orderedCopies fixedH A) (b : Fin 2) (v : Fin 64) :
    A (rc.1.val (bodyIndex b)) (rc.2.val (anchorIndex v)) =
      decide (v.val = b.val) := by
  classical
  have hm := (Finset.mem_filter.mp hcopy).2 (bodyIndex b) (anchorIndex v)
  exact hm.trans (fixedH_body_anchor b v)

theorem copy_body_col_signature {n : ℕ} {A : BinaryMatrix n}
    {rc : IncreasingMap 66 n × IncreasingMap 66 n}
    (hcopy : rc ∈ orderedCopies fixedH A) (b : Fin 2) (u : Fin 64) :
    A (rc.1.val (anchorIndex u)) (rc.2.val (bodyIndex b)) =
      decide (u.val = b.val) := by
  classical
  have hm := (Finset.mem_filter.mp hcopy).2 (anchorIndex u) (bodyIndex b)
  exact hm.trans (fixedH_anchor_body u b)

end Problem348.BodySignatures52

end OAI
end
end

section
section
namespace OAI

/-!
# Body-role extraction for the canonical host

Anchor traces determine body roles in the actual `Construction.host` table.
-/

namespace Problem348.Construction

theorem rowRole_of_anchor_trace {h : ℕ} (t : Mode h) (r : Position h)
    (z : Fin 64 → Fin (2 ^ h)) (b : Fin 2)
    (hsig : ∀ v : Fin 64,
      host r (Sum.inl (t, v, z v)) = decide (v.val = b.val)) :
    rowRole t b r := by
  rcases r with ⟨t', u, a⟩ | r
  · by_cases ht : t' = t
    · subst t'
      have heq : (fun v => anchor64 u v) =
          (fun v : Fin 64 => decide (v.val = b.val)) := by
        funext v
        simpa [host] using hsig v
      exact False.elim (BodySignatures52.anchor64_row_ne_body_signature u b heq)
    · have heq : (fun _ : Fin 64 => false) =
          (fun v : Fin 64 => decide (v.val = b.val)) := by
        funext v
        simpa [host, ht] using hsig v
      exact False.elim (BodySignatures52.zero_ne_body_signature b heq)
  · fin_cases b
    · have hv := hsig (0 : Fin 64)
      simpa [host] using hv
    · have hv := hsig (1 : Fin 64)
      simpa [host] using hv

theorem colRole_of_anchor_trace {h : ℕ} (t : Mode h) (c : Position h)
    (z : Fin 64 → Fin (2 ^ h)) (b : Fin 2)
    (hsig : ∀ u : Fin 64,
      host (Sum.inl (t, u, z u)) c = decide (u.val = b.val)) :
    colRole t b c := by
  rcases c with ⟨t', v, a⟩ | c
  · by_cases ht : t = t'
    · subst t'
      have heq : (fun u => anchor64 u v) =
          (fun u : Fin 64 => decide (u.val = b.val)) := by
        funext u
        simpa [host] using hsig u
      exact False.elim (BodySignatures52.anchor64_col_ne_body_signature v b heq)
    · have heq : (fun _ : Fin 64 => false) =
          (fun u : Fin 64 => decide (u.val = b.val)) := by
        funext u
        simpa [host, ht] using hsig u
      exact False.elim (BodySignatures52.zero_ne_body_signature b heq)
  · fin_cases b
    · have hu := hsig (0 : Fin 64)
      simpa [host] using hu
    · have hu := hsig (1 : Fin 64)
      simpa [host] using hu

/-- Exact converse, useful also when constructing a guarded anchor frame. -/
theorem anchor_trace_of_rowRole {h : ℕ} (t : Mode h) (r : Position h)
    (z : Fin 64 → Fin (2 ^ h)) (b : Fin 2) (hr : rowRole t b r) :
    ∀ v : Fin 64, host r (Sum.inl (t, v, z v)) = decide (v.val = b.val) := by
  have hd := rowRole_disjoint t r
  rcases r with a | r
  · simp [rowRole] at hr
  · fin_cases b
    · have hn : ¬ rowRole t 1 (Sum.inr r) := fun h1 => hd ⟨hr, h1⟩
      intro v
      simp [host, hn]
      exact fun _ => hr
    · have hn : ¬ rowRole t 0 (Sum.inr r) := fun h0 => hd ⟨h0, hr⟩
      intro v
      simp [host, hn]
      exact fun _ => hr

theorem anchor_trace_of_colRole {h : ℕ} (t : Mode h) (c : Position h)
    (z : Fin 64 → Fin (2 ^ h)) (b : Fin 2) (hc : colRole t b c) :
    ∀ u : Fin 64, host (Sum.inl (t, u, z u)) c = decide (u.val = b.val) := by
  have hd := colRole_disjoint t c
  rcases c with a | c
  · simp [colRole] at hc
  · fin_cases b
    · have hn : ¬ colRole t 1 (Sum.inr c) := fun h1 => hd ⟨hc, h1⟩
      intro u
      simp [host, hn]
      exact fun _ => hc
    · have hn : ¬ colRole t 0 (Sum.inr c) := fun h0 => hd ⟨h0, hc⟩
      intro u
      simp [host, hn]
      exact fun _ => hc

/-- Raw matching version, independent of any enumeration or order on the axes. -/
theorem host_body_roles_of_matching {h : ℕ}
    (r c : Fin 66 → Position h)
    (hmatch : ∀ i j, host (r i) (c j) = fixedH i j)
    (t : Mode h) (zr zc : Fin 64 → Fin (2 ^ h))
    (hrows : ∀ u, r (BodySignatures52.anchorIndex u) = Sum.inl (t, u, zr u))
    (hcols : ∀ v, c (BodySignatures52.anchorIndex v) = Sum.inl (t, v, zc v))
    (b : Fin 2) :
    rowRole t b (r (BodySignatures52.bodyIndex b)) ∧
      colRole t b (c (BodySignatures52.bodyIndex b)) := by
  constructor
  · apply rowRole_of_anchor_trace t _ zc b
    intro v
    rw [← hcols v]
    exact (hmatch _ _).trans (BodySignatures52.fixedH_body_anchor b v)
  · apply colRole_of_anchor_trace t _ zr b
    intro u
    rw [← hrows u]
    exact (hmatch _ _).trans (BodySignatures52.fixedH_anchor_body u b)

/-- The lower-right four cells of any raw matching copy form exactly P. -/
theorem host_body_entries_of_matching {h : ℕ}
    (r c : Fin 66 → Position h)
    (hmatch : ∀ i j, host (r i) (c j) = fixedH i j) :
    host (r (BodySignatures52.bodyIndex 0)) (c (BodySignatures52.bodyIndex 0)) = true ∧
    host (r (BodySignatures52.bodyIndex 0)) (c (BodySignatures52.bodyIndex 1)) = false ∧
    host (r (BodySignatures52.bodyIndex 1)) (c (BodySignatures52.bodyIndex 0)) = true ∧
    host (r (BodySignatures52.bodyIndex 1)) (c (BodySignatures52.bodyIndex 1)) = true := by
  simp only [hmatch, BodySignatures52.fixedH_body_body]
  decide

/-- An actual ordered copy in a transported canonical host has the
two prescribed body roles, once anchor rigidity pins its prefix. -/
theorem host_body_roles_of_copy {h n : ℕ} {A : BinaryMatrix n}
    (row col : Fin n → Position h)
    (hA : ∀ i j, A i j = host (row i) (col j))
    {rc : IncreasingMap 66 n × IncreasingMap 66 n}
    (hcopy : rc ∈ orderedCopies fixedH A)
    (t : Mode h) (zr zc : Fin 64 → Fin (2 ^ h))
    (hrows : ∀ u, row (rc.1.val (BodySignatures52.anchorIndex u)) =
      Sum.inl (t, u, zr u))
    (hcols : ∀ v, col (rc.2.val (BodySignatures52.anchorIndex v)) =
      Sum.inl (t, v, zc v))
    (b : Fin 2) :
    rowRole t b (row (rc.1.val (BodySignatures52.bodyIndex b))) ∧
      colRole t b (col (rc.2.val (BodySignatures52.bodyIndex b))) := by
  constructor
  · apply rowRole_of_anchor_trace t _ zc b
    intro v
    rw [← hcols v, ← hA]
    exact BodySignatures52.copy_body_row_signature hcopy b v
  · apply colRole_of_anchor_trace t _ zr b
    intro u
    rw [← hrows u, ← hA]
    exact BodySignatures52.copy_body_col_signature hcopy b u

end Problem348.Construction

end OAI
end
end

section
section
namespace OAI

/-!
# Counting ordered matrix copies through a constrained cell

The counting injection is independent of the host construction.
-/

namespace Problem348.CopyBound

/-- If one specified row-column pair in every member of a finite family belongs
 to `L`, the family is encoded by that cell and all remaining coordinates. -/
theorem card_le_card_mul_pow {k n : ℕ}
    (S : Finset
      ({f : Fin (k + 1) → Fin n // StrictMono f} ×
       {f : Fin (k + 1) → Fin n // StrictMono f}))
    (i j : Fin (k + 1)) (L : Finset (Fin n × Fin n))
    (hL : ∀ rc ∈ S, (rc.1.val i, rc.2.val j) ∈ L) :
    S.card ≤ L.card * n ^ (2 * k) := by
  classical
  let encode : S → L × ((Fin k → Fin n) × (Fin k → Fin n)) :=
    fun rc =>
      (⟨(rc.val.1.val i, rc.val.2.val j), hL rc.val rc.property⟩,
       (fun a => rc.val.1.val (i.succAbove a),
        fun b => rc.val.2.val (j.succAbove b)))
  have hinj : Function.Injective encode := by
    intro x y hxy
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      funext a
      rcases Fin.eq_self_or_eq_succAbove i a with ha | ⟨b, hb⟩
      · subst a
        exact congrArg (fun z => z.1.val.1) hxy
      · subst a
        exact congrArg (fun z => z.2.1 b) hxy
    · apply Subtype.ext
      funext a
      rcases Fin.eq_self_or_eq_succAbove j a with ha | ⟨b, hb⟩
      · subst a
        exact congrArg (fun z => z.1.val.2) hxy
      · subst a
        exact congrArg (fun z => z.2.2 b) hxy
  have hc := Fintype.card_le_of_injective encode hinj
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, two_mul, pow_add, mul_assoc] using hc

/-- Normalize the integer count bound from the leaf-diagonal argument. -/
theorem normalized_count_le {count d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (hcount : count ≤ m * (d * m) ^ 130) :
    (count : ℝ) / (((d * m : ℕ) : ℝ) ^ 132) ≤
      (1 / ((d : ℝ) ^ 2)) * (1 / (m : ℝ)) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hcount' : (count : ℝ) ≤ (m : ℝ) * ((d : ℝ) * (m : ℝ)) ^ 130 := by
    exact_mod_cast hcount
  push_cast
  calc
    (count : ℝ) / ((d : ℝ) * (m : ℝ)) ^ 132 ≤
        ((m : ℝ) * ((d : ℝ) * (m : ℝ)) ^ 130) /
          ((d : ℝ) * (m : ℝ)) ^ 132 :=
      div_le_div_of_nonneg_right hcount' (by positivity)
    _ = (1 / ((d : ℝ) ^ 2)) * (1 / (m : ℝ)) := by
      field_simp

end Problem348.CopyBound

end OAI
end
end

section
section
namespace OAI

namespace Problem348

/-- Ordered-copy specialization of the generic constrained-cell bound. -/
theorem copyCount_le_of_cell_mem {k n : ℕ}
    (H : BinaryMatrix (k + 1)) (A : BinaryMatrix n)
    (i j : Fin (k + 1)) (L : Finset (Fin n × Fin n))
    (hL : ∀ rc ∈ orderedCopies H A, (rc.1.val i, rc.2.val j) ∈ L) :
    copyCount H A ≤ L.card * n ^ (2 * k) :=
  CopyBound.card_le_card_mul_pow (orderedCopies H A) i j L hL

/-- Locate the top-left body entry (zero-based index 64) to count fixed-H copies. -/
theorem fixedCopyCount_le_of_body_cell_mem {n : ℕ}
    (A : BinaryMatrix n) (L : Finset (Fin n × Fin n))
    (hL : ∀ rc ∈ orderedCopies fixedH A, (rc.1.val 64, rc.2.val 64) ∈ L) :
    copyCount fixedH A ≤ L.card * n ^ 130 :=
  copyCount_le_of_cell_mem fixedH A 64 64 L hL

/-- The copy bound reduced to concrete leaf localization. -/
theorem fixedCopyDensity_le_of_body_cell_mem {d m : ℕ}
    (hd : 0 < d) (hm : 0 < m) (A : BinaryMatrix (d * m))
    (L : Finset (Fin (d * m) × Fin (d * m))) (hcard : L.card ≤ m)
    (hL : ∀ rc ∈ orderedCopies fixedH A, (rc.1.val 64, rc.2.val 64) ∈ L) :
    (copyCount fixedH A : ℝ) / (((d * m : ℕ) : ℝ) ^ 132) ≤
      (1 / ((d : ℝ) ^ 2)) * (1 / (m : ℝ)) := by
  apply CopyBound.normalized_count_le hd hm
  exact (fixedCopyCount_le_of_body_cell_mem A L hL).trans
    (Nat.mul_le_mul_right _ hcard)

/-- The exact numerical upper bound appearing in counterexample_sequence. -/
theorem sequenceCopyDensity_le_of_body_cell_mem (h : ℕ)
    (A : BinaryMatrix ((386 * h + 2) * 2 ^ h))
    (L : Finset
      (Fin ((386 * h + 2) * 2 ^ h) × Fin ((386 * h + 2) * 2 ^ h)))
    (hcard : L.card ≤ 2 ^ h)
    (hL : ∀ rc ∈ orderedCopies fixedH A, (rc.1.val 64, rc.2.val 64) ∈ L) :
    (copyCount fixedH A : ℝ) / ((((386 * h + 2) * 2 ^ h : ℕ) : ℝ) ^ 132) ≤
      (1 / (((386 * h + 2 : ℕ) : ℝ) ^ 2)) * (1 / ((2 : ℝ) ^ h)) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    fixedCopyDensity_le_of_body_cell_mem (by omega : 0 < 386 * h + 2)
      (by positivity : 0 < 2 ^ h) A L hcard hL

/-- A localization witness is enough; no separate leaf-cell set or injectivity
proof is required for the upper bound.  Images can only decrease cardinality. -/
theorem sequenceCopyDensity_le_of_leaf_witness (h : ℕ)
    (A : BinaryMatrix ((386 * h + 2) * 2 ^ h))
    (rowLeaf colLeaf : Fin (2 ^ h) → Fin ((386 * h + 2) * 2 ^ h))
    (hloc : ∀ r c : IncreasingMap 66 ((386 * h + 2) * 2 ^ h),
      (∀ i j, A (r.val i) (c.val j) = fixedH i j) →
      ∃ z, r.val 64 = rowLeaf z ∧ c.val 64 = colLeaf z) :
    (copyCount fixedH A : ℝ) / ((((386 * h + 2) * 2 ^ h : ℕ) : ℝ) ^ 132) ≤
      (1 / (((386 * h + 2 : ℕ) : ℝ) ^ 2)) * (1 / ((2 : ℝ) ^ h)) := by
  classical
  let L := Finset.univ.image (fun z => (rowLeaf z, colLeaf z))
  apply sequenceCopyDensity_le_of_body_cell_mem h A L
  · exact Finset.card_image_le.trans (by simp)
  · intro rc hrc
    have hentries : ∀ i j, A (rc.1.val i) (rc.2.val j) = fixedH i j :=
      (Finset.mem_filter.mp hrc).2
    obtain ⟨z, hrow, hcol⟩ := hloc rc.1 rc.2 hentries
    exact Finset.mem_image.mpr ⟨z, Finset.mem_univ _, by simp [hrow, hcol]⟩

end Problem348

end OAI
end
end

section
section
namespace OAI

/-!
# Transfer raw-host copy localization to the fixed counting target

The row and column enumerations are independent.  This adapter does not assume
that either enumeration preserves an ambient order on the sum type: the raw
localization hypothesis uses exactly the two induced finite orders.
-/

noncomputable section
namespace Problem348.Construction

/-- The canonical host viewed through independent row/column enumerations. -/
def hostMatrix {h n : ℕ} (er ec : Position h ≃ Fin n) : BinaryMatrix n :=
  fun i j => host (er.symm i) (ec.symm j)

/-- A raw leaf is shared by the plus and minus names on both axes. -/
def countedLeaf {h : ℕ} (z : Fin (2 ^ h)) : Position h :=
  Sum.inr (Sum.inl (Fin.last (2 * h), z))

/-- The depth/node conclusion of the mode analysis is exactly a leaf-diagonal
witness in the raw-position type, including the shared leaf class. -/
theorem exists_countedLeaf_of_depth_node {h : ℕ} (r c : VariablePosition h)
    (hr : depth r = h) (hc : depth c = h) (hnode : node r = node c) :
    ∃ z, (Sum.inr (Sum.inl r) : Position h) = countedLeaf z ∧
      (Sum.inr (Sum.inl c) : Position h) = countedLeaf z := by
  have hrclass : r.1 = Fin.last (2 * h) := by
    apply Fin.ext
    have hb := r.1.isLt
    have hr' : r.1.val / 2 = h := hr
    simp only [Fin.val_last]
    omega
  have hcclass : c.1 = Fin.last (2 * h) := by
    apply Fin.ext
    have hb := c.1.isLt
    have hc' : c.1.val / 2 = h := hc
    simp only [Fin.val_last]
    omega
  have hoffset : r.2 = c.2 := by
    apply Fin.ext
    simpa [node, hr, hc] using hnode
  refine ⟨r.2, ?_, ?_⟩
  · simp only [countedLeaf, Sum.inr.injEq, Sum.inl.injEq]
    exact Prod.ext hrclass rfl
  · simp only [countedLeaf, Sum.inr.injEq, Sum.inl.injEq]
    exact Prod.ext hcclass hoffset.symm

/-- Exact localization of a raw copy transports without any count-equivalence
machinery.  The increasing-map hypotheses refer to the supplied enumerations. -/
theorem localization_on_fin {h n : ℕ} (er ec : Position h ≃ Fin n)
    (hloc : ∀ r c : Fin 66 → Position h,
      StrictMono (fun i => er (r i)) → StrictMono (fun j => ec (c j)) →
      (∀ i j, host (r i) (c j) = fixedH i j) →
      ∃ z, r 64 = countedLeaf z ∧ c 64 = countedLeaf z)
    (r c : IncreasingMap 66 n)
    (hentries : ∀ i j, hostMatrix er ec (r.val i) (c.val j) = fixedH i j) :
    ∃ z, r.val 64 = er (countedLeaf z) ∧ c.val 64 = ec (countedLeaf z) := by
  obtain ⟨z, hr, hc⟩ := hloc (fun i => er.symm (r.val i))
    (fun j => ec.symm (c.val j)) (by simpa using r.property)
    (by simpa using c.property) hentries
  refine ⟨z, ?_, ?_⟩
  · simpa using congrArg er hr
  · simpa using congrArg ec hc

/-- Integer bound used by the sequence assembly, from raw-host localization. -/
theorem host_copyCount_le {h n : ℕ} (er ec : Position h ≃ Fin n)
    (hloc : ∀ r c : Fin 66 → Position h,
      StrictMono (fun i => er (r i)) → StrictMono (fun j => ec (c j)) →
      (∀ i j, host (r i) (c j) = fixedH i j) →
      ∃ z, r 64 = countedLeaf z ∧ c 64 = countedLeaf z) :
    copyCount fixedH (hostMatrix er ec) ≤ 2 ^ h * n ^ 130 := by
  classical
  let L := Finset.univ.image (fun z : Fin (2 ^ h) =>
    (er (countedLeaf z), ec (countedLeaf z)))
  have hcard : L.card ≤ 2 ^ h := Finset.card_image_le.trans (by simp)
  apply (fixedCopyCount_le_of_body_cell_mem (hostMatrix er ec) L ?_).trans
    (Nat.mul_le_mul_right _ hcard)
  intro rc hrc
  obtain ⟨z, hr, hc⟩ := localization_on_fin er ec hloc rc.1 rc.2
    (Finset.mem_filter.mp hrc).2
  exact Finset.mem_image.mpr ⟨z, Finset.mem_univ _, by simp [hr, hc]⟩

/-- The exact density upper bound of counterexample_sequence for this raw host. -/
theorem host_copyDensity_le (h : ℕ)
    (er ec : Position h ≃ Fin ((386 * h + 2) * 2 ^ h))
    (hloc : ∀ r c : Fin 66 → Position h,
      StrictMono (fun i => er (r i)) → StrictMono (fun j => ec (c j)) →
      (∀ i j, host (r i) (c j) = fixedH i j) →
      ∃ z, r 64 = countedLeaf z ∧ c 64 = countedLeaf z) :
    (copyCount fixedH (hostMatrix er ec) : ℝ) /
        ((((386 * h + 2) * 2 ^ h : ℕ) : ℝ) ^ 132) ≤
      (1 / (((386 * h + 2 : ℕ) : ℝ) ^ 2)) * (1 / ((2 : ℝ) ^ h)) := by
  apply sequenceCopyDensity_le_of_leaf_witness h (hostMatrix er ec)
    (fun z => er (countedLeaf z)) (fun z => ec (countedLeaf z))
  exact localization_on_fin er ec hloc

end Problem348.Construction

end

end OAI
end
end

section
section
namespace OAI

/-!
# From anchor rigidity and body localization to the copy-count bound

The independent row and column orders are represented by `er` and `ec`.
The geometric hypotheses are rigidity of every ordered `anchor64` copy and
localization of ordered bodies in their actual host roles.
-/

namespace Problem348.Construction

/-- The precise form of anchor rigidity needed for counting: every ordered
anchor copy contains one representative of each group of one common mode. -/
def Anchor64Pinned {h n : ℕ} (er ec : Position h ≃ Fin n) : Prop :=
  ∀ r c : Fin 64 → Position h,
    StrictMono (fun u => er (r u)) → StrictMono (fun v => ec (c v)) →
    (∀ u v, host (r u) (c v) = anchor64 u v) →
    ∃ (t : Mode h) (zr zc : Fin 64 → Fin (2 ^ h)),
      (∀ u, r u = Sum.inl (t, u, zr u)) ∧
      (∀ v, c v = Sum.inl (t, v, zc v))

/-- Localization of bodies in the six actual host modes, using the two
orders induced by the chosen enumerations. -/
def OrderedBodyLocalizes {h n : ℕ} (er ec : Position h ≃ Fin n) : Prop :=
  ∀ (t : Mode h) (r₀ r₁ c₀ c₁ : Position h),
    rowRole t 0 r₀ → rowRole t 1 r₁ →
    colRole t 0 c₀ → colRole t 1 c₁ →
    er r₀ < er r₁ → ec c₀ < ec c₁ →
    ModeLocalization.IsP (host r₀ c₀) (host r₀ c₁)
      (host r₁ c₀) (host r₁ c₁) →
    ∃ z : Fin (2 ^ h), r₀ = countedLeaf z ∧ c₀ = countedLeaf z

/-- The anchor coordinates form an increasing initial segment of the pattern. -/
theorem strictMono_anchorIndex52 : StrictMono BodySignatures52.anchorIndex := by
  intro u v huv
  exact huv

/-- Once the prefix of a particular matching copy has been pinned, its body
roles and the exact four entries supply the leaf witness. -/
theorem pinned_matching_copy_leaf {h n : ℕ} (er ec : Position h ≃ Fin n)
    (hbody : OrderedBodyLocalizes er ec)
    (r c : Fin 66 → Position h)
    (hr : StrictMono (fun i => er (r i)))
    (hc : StrictMono (fun j => ec (c j)))
    (hmatch : ∀ i j, host (r i) (c j) = fixedH i j)
    (t : Mode h) (zr zc : Fin 64 → Fin (2 ^ h))
    (hrows : ∀ u, r (BodySignatures52.anchorIndex u) = Sum.inl (t, u, zr u))
    (hcols : ∀ v, c (BodySignatures52.anchorIndex v) = Sum.inl (t, v, zc v)) :
    ∃ z, r 64 = countedLeaf z ∧ c 64 = countedLeaf z := by
  have hroles₀ := host_body_roles_of_matching r c hmatch t zr zc hrows hcols 0
  have hroles₁ := host_body_roles_of_matching r c hmatch t zr zc hrows hcols 1
  have hentries := host_body_entries_of_matching r c hmatch
  have hindex : BodySignatures52.bodyIndex 0 < BodySignatures52.bodyIndex 1 := by
    decide
  exact hbody t _ _ _ _ hroles₀.1 hroles₁.1 hroles₀.2 hroles₁.2
    (hr hindex) (hc hindex) hentries

/-- Restrict a fixed-H copy to its genuine anchor64 prefix, apply rigidity,
and then use body localization. This is the raw localization premise consumed
by `host_copyCount_le`, with no counting or order-transplant assumptions lost. -/
theorem host_raw_localization_of_anchor_pinning {h n : ℕ}
    (er ec : Position h ≃ Fin n)
    (hpin : Anchor64Pinned er ec) (hbody : OrderedBodyLocalizes er ec)
    (r c : Fin 66 → Position h)
    (hr : StrictMono (fun i => er (r i)))
    (hc : StrictMono (fun j => ec (c j)))
    (hmatch : ∀ i j, host (r i) (c j) = fixedH i j) :
    ∃ z, r 64 = countedLeaf z ∧ c 64 = countedLeaf z := by
  obtain ⟨t, zr, zc, hrows, hcols⟩ := hpin
    (fun u => r (BodySignatures52.anchorIndex u))
    (fun v => c (BodySignatures52.anchorIndex v))
    (hr.comp strictMono_anchorIndex52) (hc.comp strictMono_anchorIndex52)
    (fun u v => (hmatch _ _).trans (BodySignatures52.fixedH_anchor_anchor u v))
  exact pinned_matching_copy_leaf er ec hbody r c hr hc hmatch t zr zc hrows hcols

/-- Anchor rigidity and body localization imply the integer copy bound. -/
theorem host_copyCount_le_of_pinning {h n : ℕ}
    (er ec : Position h ≃ Fin n)
    (hpin : Anchor64Pinned er ec) (hbody : OrderedBodyLocalizes er ec) :
    copyCount fixedH (hostMatrix er ec) ≤ 2 ^ h * n ^ 130 :=
  host_copyCount_le er ec (host_raw_localization_of_anchor_pinning er ec hpin hbody)

/-- The normalized upper bound for the counterexample sequence. -/
theorem host_copyDensity_le_of_pinning (h : ℕ)
    (er ec : Position h ≃ Fin ((386 * h + 2) * 2 ^ h))
    (hpin : Anchor64Pinned er ec) (hbody : OrderedBodyLocalizes er ec) :
    (copyCount fixedH (hostMatrix er ec) : ℝ) /
        ((((386 * h + 2) * 2 ^ h : ℕ) : ℝ) ^ 132) ≤
      (1 / (((386 * h + 2 : ℕ) : ℝ) ^ 2)) * (1 / ((2 : ℝ) ^ h)) :=
  host_copyDensity_le h er ec (host_raw_localization_of_anchor_pinning er ec hpin hbody)

end Problem348.Construction

end OAI
end
end

section
section
namespace OAI

/-!
# Ordered-copy localization and counting

The six-mode body theorem places the distinguished cell at a shared leaf.
The count needs only anchor pinning, not a further order certificate.
-/

namespace Problem348.OrderedHost

open Construction

/-- The six-mode theorem supplies the exact body-localization counting input. -/
theorem orderedBodyLocalizes (h : ℕ) :
    OrderedBodyLocalizes (rowIndex h) (columnIndex h) := by
  intro t r₀ r₁ c₀ c₁ hr₀ hr₁ hc₀ hc₁ hrow hcol hb
  exact body_leaf_diagonal hr₀ hr₁ hc₀ hc₁ hrow hcol hb

/-- Every matching ordered copy has its top-left body cell at a shared leaf. -/
theorem matching_copy_leaf_of_pinning (h : ℕ)
    (hpin : Anchor64Pinned (rowIndex h) (columnIndex h))
    (r c : Fin 66 → Position h)
    (hr : StrictMono (fun i => rowIndex h (r i)))
    (hc : StrictMono (fun j => columnIndex h (c j)))
    (hmatch : ∀ i j, host (r i) (c j) = fixedH i j) :
    ∃ z, r 64 = countedLeaf z ∧ c 64 = countedLeaf z :=
  host_raw_localization_of_anchor_pinning (rowIndex h) (columnIndex h)
    hpin (orderedBodyLocalizes h) r c hr hc hmatch

/-- Integer copy bound for the actual two-axis enumeration. -/
theorem copyCount_le_of_pinning (h : ℕ)
    (hpin : Anchor64Pinned (rowIndex h) (columnIndex h)) :
    copyCount fixedH (hostMatrix (rowIndex h) (columnIndex h)) ≤
      2 ^ h * (size h) ^ 130 :=
  host_copyCount_le_of_pinning (rowIndex h) (columnIndex h)
    hpin (orderedBodyLocalizes h)

/-- The normalized copy bound, conditional only on anchor pinning. -/
theorem copyDensity_le_of_pinning (h : ℕ)
    (hpin : Anchor64Pinned (rowIndex h) (columnIndex h)) :
    (copyCount fixedH (hostMatrix (rowIndex h) (columnIndex h)) : ℝ) /
        ((size h : ℝ) ^ 132) ≤
      (1 / (((386 * h + 2 : ℕ) : ℝ) ^ 2)) * (1 / ((2 : ℝ) ^ h)) :=
  host_copyDensity_le_of_pinning h (rowIndex h) (columnIndex h)
    hpin (orderedBodyLocalizes h)

end Problem348.OrderedHost

end OAI
end
end

section
section
namespace OAI

/-!
# Unconditional copy bound for the canonical host

Concrete anchor rigidity and six-mode body localization imply the integer
copy bound and its normalized form.
-/

namespace Problem348.OrderedHost

open Construction

theorem anchor64Pinned (h : ℕ) :
    Anchor64Pinned (rowIndex h) (columnIndex h) :=
  HostAnchorRigidity.representatives_of_indices

theorem matching_copy_leaf (h : ℕ) (r c : Fin 66 → Position h)
    (hr : StrictMono (fun i => rowIndex h (r i)))
    (hc : StrictMono (fun j => columnIndex h (c j)))
    (hmatch : ∀ i j, host (r i) (c j) = fixedH i j) :
    ∃ z, r 64 = countedLeaf z ∧ c 64 = countedLeaf z :=
  matching_copy_leaf_of_pinning h (anchor64Pinned h) r c hr hc hmatch

theorem canonical_copyCount_le (h : ℕ) :
    copyCount fixedH (hostMatrix (rowIndex h) (columnIndex h)) ≤
      2 ^ h * (size h) ^ 130 :=
  copyCount_le_of_pinning h (anchor64Pinned h)

theorem canonical_copyDensity_le (h : ℕ) :
    (copyCount fixedH (hostMatrix (rowIndex h) (columnIndex h)) : ℝ) /
        ((size h : ℝ) ^ 132) ≤
      (1 / (((386 * h + 2 : ℕ) : ℝ) ^ 2)) * (1 / ((2 : ℝ) ^ h)) :=
  copyDensity_le_of_pinning h (anchor64Pinned h)

end Problem348.OrderedHost

end OAI
end
end

section
section
namespace OAI

/-!
The anchor/body extension step for arbitrary repairs.
The finite-order gluing lemma is independent of the host construction.
-/


noncomputable section

namespace Problem348

/-- Append two values to a function on a finite initial segment. -/
def appendTwo {α : Type uAlpha} {k : ℕ} (f : Fin k → α) (a b : α) :
    Fin (k + 2) → α := fun i =>
  if hi : i.val < k then f ⟨i.val, hi⟩ else if i.val = k then a else b

@[simp] theorem appendTwo_initial {α : Type uAlpha} {k : ℕ}
    (f : Fin k → α) (a b : α) (i : Fin k) :
    appendTwo f a b ⟨i.val, by omega⟩ = f i := by
  simp [appendTwo, i.isLt]

@[simp] theorem appendTwo_first {α : Type uAlpha} {k : ℕ}
    (f : Fin k → α) (a b : α) :
    appendTwo f a b ⟨k, by omega⟩ = a := by
  simp [appendTwo]

@[simp] theorem appendTwo_second {α : Type uAlpha} {k : ℕ}
    (f : Fin k → α) (a b : α) :
    appendTwo f a b ⟨k + 1, by omega⟩ = b := by
  simp [appendTwo]

theorem strictMono_appendTwo {α : Type uAlpha} [Preorder α] {k : ℕ}
    (f : Fin k → α) (a b : α) (hf : StrictMono f)
    (ha : ∀ i, f i < a) (hab : a < b) :
    StrictMono (appendTwo f a b) := by
  intro i j hij
  have hij' : i.val < j.val := hij
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · simpa [appendTwo, hi, hj] using
        hf (show (⟨i.val, hi⟩ : Fin k) < ⟨j.val, hj⟩ from hij')
    · by_cases hjk : j.val = k
      · simpa [appendTwo, hi, hj, hjk] using ha ⟨i.val, hi⟩
      · simpa [appendTwo, hi, hj, hjk] using lt_trans (ha ⟨i.val, hi⟩) hab
  · have hik : i.val = k := by omega
    have hjk : j.val = k + 1 := by omega
    simpa [appendTwo, hik, hjk] using hab

/-- The increasing map obtained by appending two positions after an anchor. -/
def appendTwoIncreasing {k n : ℕ} (r : IncreasingMap k n)
    (a b : Fin n) (ha : ∀ i, r.val i < a) (hab : a < b) :
    IncreasingMap (k + 2) n :=
  ⟨appendTwo r.val a b, strictMono_appendTwo r.val a b r.property ha hab⟩

/-- An anchor and the four body entries reproduce every entry of the fixed pattern. -/
theorem appendTwo_matches_fixedH {n : ℕ} (B : BinaryMatrix n)
    (r c : IncreasingMap 64 n) (r₀ r₁ c₀ c₁ : Fin n)
    (hanchor : ∀ u v, B (r.val u) (c.val v) = anchor64 u v)
    (hrow₀ : ∀ v, B r₀ (c.val v) = decide (v.val = 0))
    (hrow₁ : ∀ v, B r₁ (c.val v) = decide (v.val = 1))
    (hcol₀ : ∀ u, B (r.val u) c₀ = decide (u.val = 0))
    (hcol₁ : ∀ u, B (r.val u) c₁ = decide (u.val = 1))
    (h₀₀ : B r₀ c₀ = true) (h₀₁ : B r₀ c₁ = false)
    (h₁₀ : B r₁ c₀ = true) (h₁₁ : B r₁ c₁ = true) :
    ∀ i j : Fin 66,
      B (appendTwo r.val r₀ r₁ i) (appendTwo c.val c₀ c₁ j) = fixedH i j := by
  intro i j
  by_cases hi : i.val < 64
  · by_cases hj : j.val < 64
    · simpa [appendTwo, fixedH, hi, hj] using
        hanchor ⟨i.val, hi⟩ ⟨j.val, hj⟩
    · have hjcases : j.val = 64 ∨ j.val = 65 := by omega
      rcases hjcases with hj₀ | hj₁
      · simpa [appendTwo, fixedH, hi, hj, hj₀] using hcol₀ ⟨i.val, hi⟩
      · simpa [appendTwo, fixedH, hi, hj, hj₁] using hcol₁ ⟨i.val, hi⟩
  · have hicases : i.val = 64 ∨ i.val = 65 := by omega
    by_cases hj : j.val < 64
    · rcases hicases with hi₀ | hi₁
      · simpa [appendTwo, fixedH, hi, hj, hi₀] using hrow₀ ⟨j.val, hj⟩
      · simpa [appendTwo, fixedH, hi, hj, hi₁] using hrow₁ ⟨j.val, hj⟩
    · have hjcases : j.val = 64 ∨ j.val = 65 := by omega
      rcases hicases with hi₀ | hi₁ <;> rcases hjcases with hj₀ | hj₁ <;>
        simp [appendTwo, fixedH, *]

/-- The exact anchor-extension bridge needed by arbitrary-repair propagation. -/
theorem not_HFree_of_anchor_body {n : ℕ} (B : BinaryMatrix n)
    (r c : IncreasingMap 64 n) (r₀ r₁ c₀ c₁ : Fin n)
    (hr : ∀ i, r.val i < r₀) (hr₀₁ : r₀ < r₁)
    (hc : ∀ j, c.val j < c₀) (hc₀₁ : c₀ < c₁)
    (hanchor : ∀ u v, B (r.val u) (c.val v) = anchor64 u v)
    (hrow₀ : ∀ v, B r₀ (c.val v) = decide (v.val = 0))
    (hrow₁ : ∀ v, B r₁ (c.val v) = decide (v.val = 1))
    (hcol₀ : ∀ u, B (r.val u) c₀ = decide (u.val = 0))
    (hcol₁ : ∀ u, B (r.val u) c₁ = decide (u.val = 1))
    (h₀₀ : B r₀ c₀ = true) (h₀₁ : B r₀ c₁ = false)
    (h₁₀ : B r₁ c₀ = true) (h₁₁ : B r₁ c₁ = true) :
    ¬ HFree fixedH B := by
  classical
  let rr := appendTwoIncreasing r r₀ r₁ hr hr₀₁
  let cc := appendTwoIncreasing c c₀ c₁ hc hc₀₁
  have hmem : (rr, cc) ∈ orderedCopies fixedH B := by
    simp only [orderedCopies, Finset.mem_filter, Finset.mem_univ, true_and]
    exact appendTwo_matches_fixedH B r c r₀ r₁ c₀ c₁ hanchor hrow₀ hrow₁
      hcol₀ hcol₁ h₀₀ h₀₁ h₁₀ h₁₁
  have hpos : 0 < copyCount fixedH B :=
    Finset.card_pos.mpr ⟨(rr, cc), hmem⟩
  exact Nat.ne_of_gt hpos

end Problem348

end

end OAI
end
end

section
section
namespace OAI

/-!
Boolean propagation independent of the host construction.
No entry between variable positions is assumed to remain unchanged. Only
the dummy incidences, root bits, and identification of the two leaves
are hypotheses.
-/


namespace Problem348.PathPropagation

variable {R : Type uR} {C : Type uC}

/-- The lower-right two-by-two pattern of the fixed matrix `fixedH`. -/
def Body (B : R → C → Bool) (r₁ r₂ : R) (c₁ c₂ : C) : Prop :=
  B r₁ c₁ = true ∧ B r₁ c₂ = false ∧
    B r₂ c₁ = true ∧ B r₂ c₂ = true

/-- Avoiding the body propagates a one upwards across a column of dummy ones. -/
theorem vertical_plus {B : R → C → Bool} {r₁ r₂ : R} {c₁ c₂ : C}
    (havoid : ¬ Body B r₁ r₂ c₁ c₂)
    (h₁ : B r₁ c₁ = true) (h₂ : B r₂ c₁ = true)
    (h₃ : B r₂ c₂ = true) : B r₁ c₂ = true := by
  apply Bool.eq_true_of_not_eq_false
  intro h
  exact havoid ⟨h₁, h, h₂, h₃⟩

/-- Avoiding the body propagates a zero downwards across dummy ones. -/
theorem vertical_minus {B : R → C → Bool} {r₁ r₂ : R} {c₁ c₂ : C}
    (havoid : ¬ Body B r₁ r₂ c₁ c₂)
    (h₁ : B r₁ c₁ = true) (h₂ : B r₂ c₁ = true)
    (h₃ : B r₁ c₂ = false) : B r₂ c₂ = false := by
  apply Bool.eq_false_of_not_eq_true
  intro h
  exact havoid ⟨h₁, h₃, h₂, h⟩

/-- Avoiding the body propagates a one rightwards above a dummy row. -/
theorem horizontal_plus {B : R → C → Bool} {r₁ r₂ : R} {c₁ c₂ : C}
    (havoid : ¬ Body B r₁ r₂ c₁ c₂)
    (h₁ : B r₁ c₁ = true) (h₂ : B r₂ c₁ = true)
    (h₃ : B r₂ c₂ = true) : B r₁ c₂ = true :=
  vertical_plus havoid h₁ h₂ h₃

/-- Avoiding the body propagates a zero leftwards above a dummy row. -/
theorem horizontal_minus {B : R → C → Bool} {r₁ r₂ : R} {c₁ c₂ : C}
    (havoid : ¬ Body B r₁ r₂ c₁ c₂)
    (h₁ : B r₁ c₂ = false) (h₂ : B r₂ c₁ = true)
    (h₃ : B r₂ c₂ = true) : B r₁ c₁ = false := by
  apply Bool.eq_false_of_not_eq_true
  intro h
  exact havoid ⟨h, h₁, h₂, h₃⟩

/-- One of the four mode bodies encountered at the edge from level `i`
to level `i + 1` of the selected path. -/
def ModeBody (B : R → C → Bool)
    (xp xm : ℕ → R) (yp ym : ℕ → C) (xd : R) (yd : C) (i : ℕ) : Prop :=
  Body B (xp (i + 1)) (xp i) yd (yp i) ∨
  Body B (xm i) (xm (i + 1)) yd (ym i) ∨
  Body B (xp (i + 1)) xd (yp i) (yp (i + 1)) ∨
  Body B (xm (i + 1)) xd (ym (i + 1)) (ym i)

/-- The induction invariant: absence of all four mode bodies preserves the
opposite plus and minus bits at every level of the selected path. -/
theorem propagate {B : R → C → Bool}
    {xp xm : ℕ → R} {yp ym : ℕ → C} {xd : R} {yd : C} {h : ℕ}
    (hrootp : B (xp 0) (yp 0) = true)
    (hrootm : B (xm 0) (ym 0) = false)
    (hdcol : ∀ i, i ≤ h → B (xp i) yd = true ∧ B (xm i) yd = true)
    (hdrow : ∀ i, i ≤ h → B xd (yp i) = true ∧ B xd (ym i) = true)
    (havoid : ∀ i, i < h → ¬ ModeBody B xp xm yp ym xd yd i) :
    ∀ i, i ≤ h → B (xp i) (yp i) = true ∧ B (xm i) (ym i) = false := by
  intro i
  induction i with
  | zero => exact fun _ => ⟨hrootp, hrootm⟩
  | succ i ih =>
      intro hi
      have hil : i ≤ h := by omega
      have hit : i < h := by omega
      obtain ⟨hp, hm⟩ := ih hil
      have hvp : ¬ Body B (xp (i + 1)) (xp i) yd (yp i) :=
        fun hb => havoid i hit (Or.inl hb)
      have hvm : ¬ Body B (xm i) (xm (i + 1)) yd (ym i) :=
        fun hb => havoid i hit (Or.inr (Or.inl hb))
      have hwp : ¬ Body B (xp (i + 1)) xd (yp i) (yp (i + 1)) :=
        fun hb => havoid i hit (Or.inr (Or.inr (Or.inl hb)))
      have hwm : ¬ Body B (xm (i + 1)) xd (ym (i + 1)) (ym i) :=
        fun hb => havoid i hit (Or.inr (Or.inr (Or.inr hb)))
      have hcrossp : B (xp (i + 1)) (yp i) = true :=
        vertical_plus hvp (hdcol (i + 1) hi).1 (hdcol i hil).1 hp
      have hcrossm : B (xm (i + 1)) (ym i) = false :=
        vertical_minus hvm (hdcol i hil).2 (hdcol (i + 1) hi).2 hm
      exact ⟨horizontal_plus hwp hcrossp (hdrow i hil).1 (hdrow (i + 1) hi).1,
        horizontal_minus hwm hcrossm (hdrow (i + 1) hi).2 (hdrow i hil).2⟩

/-- Opposite root entries and shared leaves force some mode body. Arbitrary
changes to every other variable-variable entry are explicitly allowed. -/
theorem exists_modeBody {B : R → C → Bool}
    {xp xm : ℕ → R} {yp ym : ℕ → C} {xd : R} {yd : C} {h : ℕ}
    (hrootp : B (xp 0) (yp 0) = true)
    (hrootm : B (xm 0) (ym 0) = false)
    (hdcol : ∀ i, i ≤ h → B (xp i) yd = true ∧ B (xm i) yd = true)
    (hdrow : ∀ i, i ≤ h → B xd (yp i) = true ∧ B xd (ym i) = true)
    (hleafr : xp h = xm h) (hleafc : yp h = ym h) :
    ∃ i, i < h ∧ ModeBody B xp xm yp ym xd yd i := by
  by_contra hnone
  have havoid : ∀ i, i < h → ¬ ModeBody B xp xm yp ym xd yd i := by
    intro i hi hb
    exact hnone ⟨i, hi, hb⟩
  obtain ⟨hp, hm⟩ := propagate hrootp hrootm hdcol hdrow havoid h le_rfl
  rw [hleafr, hleafc, hm] at hp
  cases hp

end Problem348.PathPropagation

end OAI
end
end

section
section
namespace OAI

/-! Exact selected-anchor frames and their protected cells.
The frame does not constrain any of the four body entries. -/

noncomputable section
namespace Problem348.GuardedPath

structure AnchorFrame (n : ℕ) where
  rows : IncreasingMap 64 n
  cols : IncreasingMap 64 n

namespace AnchorFrame

variable {n : ℕ}

/-- All data needed to extend a body, except the body entries themselves. -/
structure Valid (F : AnchorFrame n) (A : BinaryMatrix n)
    (r₀ r₁ c₀ c₁ : Fin n) : Prop where
  row_before : ∀ u, F.rows.val u < r₀
  row_lt : r₀ < r₁
  col_before : ∀ v, F.cols.val v < c₀
  col_lt : c₀ < c₁
  anchor : ∀ u v, A (F.rows.val u) (F.cols.val v) = anchor64 u v
  row_zero : ∀ v, A r₀ (F.cols.val v) = decide (v.val = 0)
  row_one : ∀ v, A r₁ (F.cols.val v) = decide (v.val = 1)
  col_zero : ∀ u, A (F.rows.val u) c₀ = decide (u.val = 0)
  col_one : ∀ u, A (F.rows.val u) c₁ = decide (u.val = 1)

/-- Precisely the anchor and signature cells of one selected frame. -/
def Cell (F : AnchorFrame n) (r₀ r₁ c₀ c₁ : Fin n)
    (rc : Fin n × Fin n) : Prop :=
  (∃ u v, rc = (F.rows.val u, F.cols.val v)) ∨
  (∃ v, rc = (r₀, F.cols.val v) ∨ rc = (r₁, F.cols.val v)) ∨
  (∃ u, rc = (F.rows.val u, c₀) ∨ rc = (F.rows.val u, c₁))

/-- Agreement only on frame cells preserves anchor and signature validity. -/
theorem Valid.transfer {F : AnchorFrame n} {A B : BinaryMatrix n}
    {r₀ r₁ c₀ c₁ : Fin n} (hF : F.Valid A r₀ r₁ c₀ c₁)
    (hag : ∀ rc, F.Cell r₀ r₁ c₀ c₁ rc → A rc.1 rc.2 = B rc.1 rc.2) :
    F.Valid B r₀ r₁ c₀ c₁ := by
  refine ⟨hF.row_before, hF.row_lt, hF.col_before, hF.col_lt, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v
    exact (hag _ (Or.inl ⟨u, v, rfl⟩)).symm.trans (hF.anchor u v)
  · intro v
    exact (hag _ (Or.inr (Or.inl ⟨v, Or.inl rfl⟩))).symm.trans (hF.row_zero v)
  · intro v
    exact (hag _ (Or.inr (Or.inl ⟨v, Or.inr rfl⟩))).symm.trans (hF.row_one v)
  · intro u
    exact (hag _ (Or.inr (Or.inr ⟨u, Or.inl rfl⟩))).symm.trans (hF.col_zero u)
  · intro u
    exact (hag _ (Or.inr (Or.inr ⟨u, Or.inr rfl⟩))).symm.trans (hF.col_one u)

/-- A valid frame and the body give a genuine ordered copy of the fixed H. -/
theorem Valid.not_HFree {F : AnchorFrame n} {B : BinaryMatrix n}
    {r₀ r₁ c₀ c₁ : Fin n} (hF : F.Valid B r₀ r₁ c₀ c₁)
    (hbody : PathPropagation.Body B r₀ r₁ c₀ c₁) : ¬ HFree fixedH B := by
  exact not_HFree_of_anchor_body B F.rows F.cols r₀ r₁ c₀ c₁
    hF.row_before hF.row_lt hF.col_before hF.col_lt
    hF.anchor hF.row_zero hF.row_one hF.col_zero hF.col_one
    hbody.1 hbody.2.1 hbody.2.2.1 hbody.2.2.2

end AnchorFrame
end Problem348.GuardedPath

end

end OAI
end
end

section
section
namespace OAI

/-!
Concrete selected-anchor frames for the canonical host.
The frame signatures follow from the actual host entry definition.
-/

noncomputable section
namespace Problem348.Construction

/-- A true first row role gives the exact first unit signature. -/
theorem host_row_role_zero {h : ℕ} (t : Mode h) (r : Position h)
    (hr : rowRole t 0 r) (v : Fin 64) (y : Fin (2 ^ h)) :
    host r (.inl (t,v,y)) = decide (v.val = 0) := by
  have hn : ¬ rowRole t 1 r := fun h₁ => rowRole_disjoint t r ⟨hr,h₁⟩
  cases r with
  | inl a => simp [rowRole] at hr
  | inr r => simp [host, hr, hn]

/-- A true second row role gives the exact second unit signature. -/
theorem host_row_role_one {h : ℕ} (t : Mode h) (r : Position h)
    (hr : rowRole t 1 r) (v : Fin 64) (y : Fin (2 ^ h)) :
    host r (.inl (t,v,y)) = decide (v.val = 1) := by
  have hn : ¬ rowRole t 0 r := fun h₀ => rowRole_disjoint t r ⟨h₀,hr⟩
  cases r with
  | inl a => simp [rowRole] at hr
  | inr r => simp [host, hr, hn]

/-- A true first column role gives the exact first unit signature. -/
theorem host_col_role_zero {h : ℕ} (t : Mode h) (c : Position h)
    (hc : colRole t 0 c) (u : Fin 64) (x : Fin (2 ^ h)) :
    host (.inl (t,u,x)) c = decide (u.val = 0) := by
  have hn : ¬ colRole t 1 c := fun h₁ => colRole_disjoint t c ⟨hc,h₁⟩
  cases c with
  | inl a => simp [colRole] at hc
  | inr c => simp [host, hc, hn]

/-- A true second column role gives the exact second unit signature. -/
theorem host_col_role_one {h : ℕ} (t : Mode h) (c : Position h)
    (hc : colRole t 1 c) (u : Fin 64) (x : Fin (2 ^ h)) :
    host (.inl (t,u,x)) c = decide (u.val = 1) := by
  have hn : ¬ colRole t 0 c := fun h₀ => colRole_disjoint t c ⟨h₀,hc⟩
  cases c with
  | inl a => simp [colRole] at hc
  | inr c => simp [host, hc, hn]

namespace SelectedAnchor

/-- Independent reindexings of the exact canonical raw host. -/
def matrix {h n : ℕ} (er ec : Position h ≃ Fin n) : BinaryMatrix n :=
  fun r c => host (er.symm r) (ec.symm c)

@[simp] theorem matrix_apply {h n : ℕ} (er ec : Position h ≃ Fin n)
    (r c : Position h) : matrix er ec (er r) (ec c) = host r c := by
  simp [matrix]

/-- One selected representative from each anchor group of a fixed mode. -/
def frame {h n : ℕ} (er ec : Position h ≃ Fin n) (t : Mode h)
    (a b : Fin 64 → Fin (2 ^ h))
    (hr : StrictMono (fun u => er (.inl (t,u,a u))))
    (hc : StrictMono (fun v => ec (.inl (t,v,b v)))) :
    GuardedPath.AnchorFrame n where
  rows := ⟨fun u => er (.inl (t,u,a u)), hr⟩
  cols := ⟨fun v => ec (.inl (t,v,b v)), hc⟩

/-- The actual host roles and the row/column order comparisons give a valid
selected frame. No body entry is required or constrained. -/
theorem frame_valid {h n : ℕ} (er ec : Position h ≃ Fin n) (t : Mode h)
    (a b : Fin 64 → Fin (2 ^ h))
    (hr : StrictMono (fun u => er (.inl (t,u,a u))))
    (hc : StrictMono (fun v => ec (.inl (t,v,b v))))
    (r₀ r₁ c₀ c₁ : Position h)
    (hr₀ : rowRole t 0 r₀) (hr₁ : rowRole t 1 r₁)
    (hc₀ : colRole t 0 c₀) (hc₁ : colRole t 1 c₁)
    (hbeforeR : ∀ u, er (.inl (t,u,a u)) < er r₀)
    (hrows : er r₀ < er r₁)
    (hbeforeC : ∀ v, ec (.inl (t,v,b v)) < ec c₀)
    (hcols : ec c₀ < ec c₁) :
    (frame er ec t a b hr hc).Valid (matrix er ec)
      (er r₀) (er r₁) (ec c₀) (ec c₁) := by
  refine ⟨hbeforeR, hrows, hbeforeC, hcols, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v
    exact (matrix_apply er ec _ _).trans (host_anchor_same t u v (a u) (b v))
  · intro v
    exact (matrix_apply er ec _ _).trans (host_row_role_zero t r₀ hr₀ v (b v))
  · intro v
    exact (matrix_apply er ec _ _).trans (host_row_role_one t r₁ hr₁ v (b v))
  · intro u
    exact (matrix_apply er ec _ _).trans (host_col_role_zero t c₀ hc₀ u (a u))
  · intro u
    exact (matrix_apply er ec _ _).trans (host_col_role_one t c₁ hc₁ u (a u))

end SelectedAnchor
end Problem348.Construction

end

end OAI
end
end

section
section
namespace OAI

/-!
Concrete common-leaf path positions.
The variable-position type is `Fin (2*h+1) × Fin (2^h)`: even classes are
plus, odd classes are minus, and class `2*h` is the shared leaf class.
-/

namespace Problem348.SampledPath

abbrev VariablePosition (h : ℕ) := Fin (2 * h + 1) × Fin (2 ^ h)

def blockSize (h i : ℕ) : ℕ := 2 ^ (h - i)

theorem blockSize_pos (h i : ℕ) : 0 < blockSize h i := by
  exact pow_pos (by decide) _

theorem blockSize_mul_nodes {h i : ℕ} (hi : i ≤ h) :
    blockSize h i * 2 ^ i = 2 ^ h :=
  Nat.pow_sub_mul_pow 2 hi

/-- Retain the sampled leaf's node but choose the within-node offset from `u`. -/
def mix (b z u : ℕ) : ℕ := z / b * b + u % b

theorem mix_lt {b n z u : ℕ} (hb : 0 < b) (hz : z < n * b) :
    mix b z u < n * b := by
  have hq : z / b < n := (Nat.div_lt_iff_lt_mul hb).2 hz
  have hr : u % b < b := Nat.mod_lt u hb
  unfold mix
  nlinarith

theorem mix_div {b : ℕ} (hb : 0 < b) (z u : ℕ) :
    mix b z u / b = z / b := by
  unfold mix
  rw [Nat.mul_comm (z / b) b, Nat.mul_add_div hb]
  simp [Nat.div_eq_of_lt (Nat.mod_lt u hb)]

theorem mix_mod {b : ℕ} (hb : 0 < b) (z u : ℕ) :
    mix b z u % b = u % b := by
  calc
    mix b z u % b = (u % b) % b := by simp [mix, Nat.add_mod]
    _ = u % b := Nat.mod_eq_of_lt (Nat.mod_lt u hb)

def mixFin (h i : ℕ) (hi : i ≤ h) (z u : Fin (2 ^ h)) : Fin (2 ^ h) :=
  ⟨mix (blockSize h i) z.val u.val, by
    have hm : 2 ^ h = 2 ^ i * blockSize h i := by
      rw [Nat.mul_comm, blockSize_mul_nodes hi]
    calc
      mix (blockSize h i) z.val u.val < 2 ^ i * blockSize h i :=
        mix_lt (blockSize_pos h i) (lt_of_lt_of_eq z.isLt hm)
      _ = 2 ^ h := hm.symm⟩

@[simp] theorem mixFin_node (h i : ℕ) (hi : i ≤ h) (z u : Fin (2 ^ h)) :
    (mixFin h i hi z u).val / blockSize h i = z.val / blockSize h i :=
  mix_div (blockSize_pos h i) z.val u.val

@[simp] theorem mixFin_root (h : ℕ) (z u : Fin (2 ^ h)) :
    mixFin h 0 (Nat.zero_le h) z u = u := by
  apply Fin.ext
  simp [mixFin, mix, blockSize, Nat.div_eq_of_lt z.isLt, Nat.mod_eq_of_lt u.isLt]

@[simp] theorem mixFin_leaf (h : ℕ) (z u : Fin (2 ^ h)) :
    mixFin h h le_rfl z u = z := by
  apply Fin.ext
  simp [mixFin, mix, blockSize, Nat.mod_one]

/-- The plus and minus names coincide precisely at the leaf level. -/
def classAt (h i : ℕ) (hi : i ≤ h) (plus : Bool) : Fin (2 * h + 1) :=
  ⟨if i = h then 2 * h else 2 * i + (!plus).toNat, by
    split_ifs with heq
    · omega
    · cases plus <;> simp <;> omega⟩

@[simp] theorem classAt_depth (h i : ℕ) (hi : i ≤ h) (plus : Bool) :
    (classAt h i hi plus).val / 2 = i := by
  unfold classAt
  split_ifs with heq
  · subst i
    change 2 * h / 2 = h
    omega
  · cases plus <;> simp; omega

@[simp] theorem classAt_leaf (h : ℕ) (plus : Bool) :
    (classAt h h le_rfl plus).val = 2 * h := by
  simp [classAt]

theorem classAt_internal (h i : ℕ) (hi : i < h) (plus : Bool) :
    (classAt h i hi.le plus).val = 2 * i + (!plus).toNat := by
  simp [classAt, Nat.ne_of_lt hi]

theorem classAt_leaf_iff (h i : ℕ) (hi : i ≤ h) (plus : Bool) :
    (classAt h i hi plus).val = 2 * h ↔ i = h := by
  constructor
  · intro heq
    have hd := classAt_depth h i hi plus
    rw [heq] at hd
    omega
  · rintro rfl
    simp

theorem classAt_signs_eq_iff (h i : ℕ) (hi : i ≤ h) :
    classAt h i hi true = classAt h i hi false ↔ i = h := by
  by_cases heq : i = h
  · subst i
    simp [classAt]
  · simp [classAt, heq, Fin.ext_iff]

def sample (h i : ℕ) (hi : i ≤ h) (plus : Bool)
    (z u : Fin (2 ^ h)) : VariablePosition h :=
  (classAt h i hi plus, mixFin h i hi z u)

def depth {h : ℕ} (p : VariablePosition h) : ℕ := p.1.val / 2

def node {h : ℕ} (p : VariablePosition h) : ℕ :=
  p.2.val / blockSize h (depth p)

@[simp] theorem sample_depth (h i : ℕ) (hi : i ≤ h) (plus : Bool)
    (z u : Fin (2 ^ h)) : depth (sample h i hi plus z u) = i :=
  classAt_depth h i hi plus

@[simp] theorem sample_node (h i : ℕ) (hi : i ≤ h) (plus : Bool)
    (z u : Fin (2 ^ h)) :
    node (sample h i hi plus z u) = z.val / blockSize h i := by
  unfold node
  rw [sample_depth]
  exact mixFin_node h i hi z u

theorem sample_node_lt (h i : ℕ) (hi : i ≤ h) (plus : Bool)
    (z u : Fin (2 ^ h)) : node (sample h i hi plus z u) < 2 ^ i := by
  rw [sample_node]
  apply (Nat.div_lt_iff_lt_mul (blockSize_pos h i)).2
  rw [Nat.mul_comm, blockSize_mul_nodes hi]
  exact z.isLt

/-- The two axes may use different offset seeds and still follow one common path. -/
theorem sample_nodes_eq (h i : ℕ) (hi : i ≤ h) (s t : Bool)
    (z u v : Fin (2 ^ h)) :
    node (sample h i hi s z u) = node (sample h i hi t z v) := by
  simp

theorem ancestor_parent (h i z : ℕ) (hi : i + 1 ≤ h) :
    z / blockSize h (i + 1) / 2 = z / blockSize h i := by
  have he : h - i = h - (i + 1) + 1 := by omega
  simp only [blockSize, Nat.div_div_eq_div_mul]
  rw [he, pow_succ]

theorem sample_parent (h i : ℕ) (hi : i + 1 ≤ h) (s t : Bool)
    (z u v : Fin (2 ^ h)) :
    node (sample h (i + 1) hi s z u) / 2 =
      node (sample h i (by omega) t z v) := by
  simp only [sample_node]
  exact ancestor_parent h i z.val hi

@[simp] theorem sample_shared_leaf (h : ℕ) (s t : Bool)
    (z u v : Fin (2 ^ h)) :
    sample h h le_rfl s z u = sample h h le_rfl t z v := by
  simp [sample, classAt]

@[simp] theorem sample_leaf_offset (h : ℕ) (s : Bool) (z u : Fin (2 ^ h)) :
    (sample h h le_rfl s z u).2 = z := by
  simp [sample]

@[simp] theorem sample_root_offset (h : ℕ) (s : Bool) (z u : Fin (2 ^ h)) :
    (sample h 0 (Nat.zero_le h) s z u).2 = u := by
  simp [sample]

@[simp] theorem sample_root_node (h : ℕ) (s : Bool) (z u : Fin (2 ^ h)) :
    node (sample h 0 (Nat.zero_le h) s z u) = 0 := by
  simp [blockSize, Nat.div_eq_of_lt z.isLt]

end Problem348.SampledPath

end OAI
end
end

section
section
namespace OAI

/-!
Concrete sampled-path role membership for the canonical host.
The input is one common leaf seed and arbitrary within-class offset seeds.
-/
namespace Problem348.HostSampledPath

open SampledPath

/-- The variable-position sample, injected into the full host axis. -/
def position (h i : ℕ) (hi : i ≤ h) (plus : Bool)
    (z u : Fin (2 ^ h)) : Construction.Position h :=
  Sum.inr (Sum.inl (sample h i hi plus z u))

/-- A sampled dummy position. -/
def dummy (h : ℕ) (u : Fin (2 ^ h)) : Construction.Position h :=
  Sum.inr (Sum.inr u)

@[simp] theorem sample_atLevel (h i : ℕ) (hi : i ≤ h) (s : Bool)
    (z u : Fin (2 ^ h)) : Construction.AtLevel i s (sample h i hi s z u) := by
  constructor
  · exact sample_depth h i hi s z u
  · by_cases heq : i = h
    · exact Or.inl heq
    · right
      cases s <;>
        simp [Construction.plus, sample, classAt, heq]

@[simp] theorem sample_hostNode (h i : ℕ) (hi : i ≤ h) (s : Bool)
    (z u : Fin (2 ^ h)) :
    Construction.node (sample h i hi s z u) = z.val / blockSize h i :=
  sample_node h i hi s z u

@[simp] theorem position_shared_leaf (h : ℕ) (s t : Bool)
    (z u v : Fin (2 ^ h)) :
    position h h le_rfl s z u = position h h le_rfl t z v := by
  exact congrArg (fun p : Construction.VariablePosition h =>
    (Sum.inr (Sum.inl p) : Construction.Position h))
    (sample_shared_leaf h s t z u v)

/-- Encode the mode at the edge from depth `i` to depth `i+1`. -/
def mode {h : ℕ} (i : Fin h) (k : Fin 6) : Construction.Mode h :=
  ⟨6 * i.val + k.val, by have := i.isLt; have := k.isLt; omega⟩

@[simp] theorem mode_level {h : ℕ} (i : Fin h) (k : Fin 6) :
    Construction.level (mode i k) = i.val + 1 := by
  have := k.isLt
  unfold Construction.level mode
  dsimp
  omega

@[simp] theorem mode_kind {h : ℕ} (i : Fin h) (k : Fin 6) :
    Construction.kind (mode i k) = k.val := by
  have := k.isLt
  unfold Construction.kind mode
  dsimp
  omega

def verticalKind : Bool → Fin 6
  | true => 0
  | false => 1

def horizontalKind : Bool → Bool → Fin 6
  | true, false => 2
  | true, true => 3
  | false, false => 4
  | false, true => 5

def vertical {h : ℕ} (i : Fin h) (s : Bool) : Construction.Mode h :=
  mode i (verticalKind s)
def horizontal {h : ℕ} (i : Fin h) (s d : Bool) : Construction.Mode h :=
  mode i (horizontalKind s d)

def parity (n : ℕ) : Bool := decide (n % 2 = 1)

@[simp] theorem parity_eq_false (n : ℕ) : parity n = false ↔ n % 2 = 0 := by
  simp only [parity, decide_eq_false_iff_not]
  omega

@[simp] theorem parity_eq_true (n : ℕ) : parity n = true ↔ n % 2 = 1 := by
  simp [parity]

 theorem vertical_plus_row_first {h : ℕ} (i : Fin h) (z u : Fin (2 ^ h)) :
    Construction.rowRole (vertical i true) 0
      (position h (i.val + 1) (by omega) true z u) := by
  simp [vertical, verticalKind, Construction.rowRole, position]

 theorem vertical_plus_row_second {h : ℕ} (i : Fin h) (z u : Fin (2 ^ h)) :
    Construction.rowRole (vertical i true) 1
      (position h i.val (by omega) true z u) := by
  simp [vertical, verticalKind, Construction.rowRole, position]

 theorem vertical_minus_row_first {h : ℕ} (i : Fin h) (z u : Fin (2 ^ h)) :
    Construction.rowRole (vertical i false) 0
      (position h i.val (by omega) false z u) := by
  simp [vertical, verticalKind, Construction.rowRole, position]

 theorem vertical_minus_row_second {h : ℕ} (i : Fin h) (z u : Fin (2 ^ h)) :
    Construction.rowRole (vertical i false) 1
      (position h (i.val + 1) (by omega) false z u) := by
  simp [vertical, verticalKind, Construction.rowRole, position]

 theorem vertical_col_first {h : ℕ} (i : Fin h) (s : Bool) (u : Fin (2 ^ h)) :
    Construction.colRole (vertical i s) 0 (dummy h u) := by
  cases s <;> simp [vertical, verticalKind, Construction.colRole, dummy]

 theorem vertical_col_second {h : ℕ} (i : Fin h) (s : Bool) (z u : Fin (2 ^ h)) :
    Construction.colRole (vertical i s) 1 (position h i.val (by omega) s z u) := by
  cases s <;> simp [vertical, verticalKind, Construction.colRole, position]

 theorem horizontal_row_second {h : ℕ} (i : Fin h) (s d : Bool)
    (u : Fin (2 ^ h)) : Construction.rowRole (horizontal i s d) 1 (dummy h u) := by
  cases s <;> cases d <;> simp [horizontal, horizontalKind, Construction.rowRole, dummy]

 theorem horizontal_row_first {h : ℕ} (i : Fin h) (s : Bool)
    (z u : Fin (2 ^ h)) :
    Construction.rowRole (horizontal i s (parity (z.val / blockSize h (i.val + 1)))) 0
      (position h (i.val + 1) (by omega) s z u) := by
  have hp := Nat.mod_lt (z.val / blockSize h (i.val + 1)) (by decide : 0 < 2)
  cases s <;> by_cases hd : (z.val / blockSize h (i.val + 1)) % 2 = 1 <;>
    simp_all [horizontal, horizontalKind, Construction.rowRole, position, parity]

 theorem horizontal_plus_col_first {h : ℕ} (i : Fin h) (d : Bool)
    (z u : Fin (2 ^ h)) :
    Construction.colRole (horizontal i true d) 0 (position h i.val (by omega) true z u) := by
  cases d <;> simp [horizontal, horizontalKind, Construction.colRole, position]

 theorem horizontal_plus_col_second {h : ℕ} (i : Fin h) (z u : Fin (2 ^ h)) :
    Construction.colRole (horizontal i true (parity (z.val / blockSize h (i.val + 1)))) 1
      (position h (i.val + 1) (by omega) true z u) := by
  have hp := Nat.mod_lt (z.val / blockSize h (i.val + 1)) (by decide : 0 < 2)
  by_cases hd : (z.val / blockSize h (i.val + 1)) % 2 = 1 <;>
    simp_all [horizontal, horizontalKind, Construction.colRole, position, parity]

 theorem horizontal_minus_col_first {h : ℕ} (i : Fin h) (z u : Fin (2 ^ h)) :
    Construction.colRole (horizontal i false (parity (z.val / blockSize h (i.val + 1)))) 0
      (position h (i.val + 1) (by omega) false z u) := by
  have hp := Nat.mod_lt (z.val / blockSize h (i.val + 1)) (by decide : 0 < 2)
  by_cases hd : (z.val / blockSize h (i.val + 1)) % 2 = 1 <;>
    simp_all [horizontal, horizontalKind, Construction.colRole, position, parity]

 theorem horizontal_minus_col_second {h : ℕ} (i : Fin h) (d : Bool)
    (z u : Fin (2 ^ h)) :
    Construction.colRole (horizontal i false d) 1 (position h i.val (by omega) false z u) := by
  cases d <;> simp [horizontal, horizontalKind, Construction.colRole, position]

end Problem348.HostSampledPath

end OAI
end
end

section
section
namespace OAI

/-! Root bits and shared-leaf entries of the exact canonical construction. -/

namespace Problem348.Construction

/-- At the root, all uniform coordinates name node zero. -/
theorem node_eq_zero_of_depth_zero {h : ℕ} (v : VariablePosition h)
    (hv : depth v = 0) : node v = 0 := by
  unfold node
  rw [hv, Nat.sub_zero]
  exact Nat.div_eq_of_lt v.2.isLt

/-- The even class zero is the plus root. -/
@[simp] theorem depth_root_plus {h : ℕ} (x : Fin (2 ^ h)) :
    depth ((0 : Fin (2 * h + 1)), x) = 0 := by
  simp [depth]

@[simp] theorem plus_root_plus {h : ℕ} (x : Fin (2 ^ h)) :
    plus ((0 : Fin (2 * h + 1)), x) = true := by
  simp [plus]

/-- All entries between the two plus-root blocks are one. -/
theorem variableEntry_root_plus {h : ℕ} (x y : Fin (2 ^ h)) :
    variableEntry ((0 : Fin (2 * h + 1)), x)
      ((0 : Fin (2 * h + 1)), y) = true := by
  have hx := node_eq_zero_of_depth_zero ((0 : Fin (2 * h + 1)), x)
    (depth_root_plus x)
  have hy := node_eq_zero_of_depth_zero ((0 : Fin (2 * h + 1)), y)
    (depth_root_plus y)
  simp [variableEntry, hx, hy]

/-- Class one is the minus root when the tree has positive height. -/
@[simp] theorem depth_root_minus {h : ℕ} (hh : 1 ≤ h) (x : Fin (2 ^ h)) :
    depth ((⟨1, by omega⟩ : Fin (2 * h + 1)), x) = 0 := by
  simp [depth]

@[simp] theorem plus_root_minus {h : ℕ} (hh : 1 ≤ h) (x : Fin (2 ^ h)) :
    plus ((⟨1, by omega⟩ : Fin (2 * h + 1)), x) = false := by
  simp [plus]

/-- All entries between the minus-root blocks are zero. -/
theorem variableEntry_root_minus {h : ℕ} (hh : 1 ≤ h) (x y : Fin (2 ^ h)) :
    variableEntry ((⟨1, by omega⟩ : Fin (2 * h + 1)), x)
      ((⟨1, by omega⟩ : Fin (2 * h + 1)), y) = false := by
  have hx := node_eq_zero_of_depth_zero
    ((⟨1, by omega⟩ : Fin (2 * h + 1)), x) (depth_root_minus hh x)
  have hy := node_eq_zero_of_depth_zero
    ((⟨1, by omega⟩ : Fin (2 * h + 1)), y) (depth_root_minus hh y)
  simp [variableEntry, depth, plus, hx, hy, show 0 ≠ h by omega]

/-- The last class is the single shared leaf class. -/
@[simp] theorem depth_shared_leaf {h : ℕ} (x : Fin (2 ^ h)) :
    depth (Fin.last (2 * h), x) = h := by
  simp [depth]

@[simp] theorem node_shared_leaf {h : ℕ} (x : Fin (2 ^ h)) :
    node (Fin.last (2 * h), x) = x.val := by
  simp [node]

/-- Entry values at shared leaves, including the minus diagonal. -/
theorem variableEntry_shared_leaf {h : ℕ} (x y : Fin (2 ^ h)) :
    variableEntry (Fin.last (2 * h), x) (Fin.last (2 * h), y) =
      decide (x.val ≤ y.val) := by
  simp [variableEntry]

/-- Exact unchanged plus root bit on the full host. -/
theorem host_root_plus {h : ℕ} (x y : Fin (2 ^ h)) :
    host (Sum.inr (Sum.inl ((0 : Fin (2 * h + 1)), x)))
      (Sum.inr (Sum.inl ((0 : Fin (2 * h + 1)), y))) = true :=
  variableEntry_root_plus x y

/-- Exact unchanged minus root bit on the full host. -/
theorem host_root_minus {h : ℕ} (hh : 1 ≤ h) (x y : Fin (2 ^ h)) :
    host (Sum.inr (Sum.inl ((⟨1, by omega⟩ : Fin (2 * h + 1)), x)))
      (Sum.inr (Sum.inl ((⟨1, by omega⟩ : Fin (2 * h + 1)), y))) = false :=
  variableEntry_root_minus hh x y

/-- The shared-leaf diagonal consists of ones. -/
theorem host_shared_leaf_diagonal {h : ℕ} (x : Fin (2 ^ h)) :
    host (Sum.inr (Sum.inl (Fin.last (2 * h), x)))
      (Sum.inr (Sum.inl (Fin.last (2 * h), x))) = true := by
  simp [host, variableEntry_shared_leaf]

/-- Constructor-free form of the positive root entry. -/
theorem variableEntry_root_plus_of_atLevel {h : ℕ} (hh : 1 ≤ h)
    (r c : VariablePosition h) (hr : AtLevel 0 true r) (hc : AtLevel 0 true c) :
    variableEntry r c = true := by
  have hrp : plus r = true := hr.2.resolve_left (by omega)
  have hcp : plus c = true := hc.2.resolve_left (by omega)
  have hrn := node_eq_zero_of_depth_zero r hr.1
  have hcn := node_eq_zero_of_depth_zero c hc.1
  simp [variableEntry, hr.1, hc.1, hrp, hcp, hrn, hcn]

/-- Constructor-free form of the negative root entry. -/
theorem variableEntry_root_minus_of_atLevel {h : ℕ} (hh : 1 ≤ h)
    (r c : VariablePosition h) (hr : AtLevel 0 false r) (hc : AtLevel 0 false c) :
    variableEntry r c = false := by
  have hrp : plus r = false := hr.2.resolve_left (by omega)
  have hcp : plus c = false := hc.2.resolve_left (by omega)
  have hrn := node_eq_zero_of_depth_zero r hr.1
  have hcn := node_eq_zero_of_depth_zero c hc.1
  simp [variableEntry, hr.1, hc.1, hrp, hcp, hrn, hcn, show 0 ≠ h by omega]

/-- Every shared-leaf node is its coordinate. -/
theorem node_eq_coordinate_of_leaf {h : ℕ} (r : VariablePosition h)
    (hr : depth r = h) : node r = r.2.val := by
  simp [node, hr]

/-- Constructor-free shared-leaf threshold formula. -/
theorem variableEntry_leaf_of_depth {h : ℕ} (r c : VariablePosition h)
    (hr : depth r = h) (hc : depth c = h) :
    variableEntry r c = decide (r.2.val ≤ c.2.val) := by
  simp [variableEntry, hr, hc, node_eq_coordinate_of_leaf r hr,
    node_eq_coordinate_of_leaf c hc]

end Problem348.Construction

end OAI
end
end

section
section
namespace OAI

/-!
A deterministic arbitrary-repair obstruction for the fixed binary pattern.
A selection records one common tree path, dummy positions, and four selected
anchor frames per edge. Its guards contain only root, dummy, anchor, and
anchor/body signature cells -- never the unconstrained variable body cells.
-/

noncomputable section
namespace Problem348.GuardedPath

/-- Selected positions; no host construction or matching assumptions are hidden
in this data structure. Values past the chosen depth are irrelevant. -/
structure Selection (n : ℕ) where
  xp : ℕ → Fin n
  xm : ℕ → Fin n
  yp : ℕ → Fin n
  ym : ℕ → Fin n
  xd : Fin n
  yd : Fin n
  vPlus : ℕ → AnchorFrame n
  vMinus : ℕ → AnchorFrame n
  wPlus : ℕ → AnchorFrame n
  wMinus : ℕ → AnchorFrame n

namespace Selection
variable {n : ℕ}

/-- Root and dummy cells needed for Boolean propagation. -/
def CoreCell (P : Selection n) (h : ℕ) (rc : Fin n × Fin n) : Prop :=
  rc = (P.xp 0, P.yp 0) ∨ rc = (P.xm 0, P.ym 0) ∨
  ∃ i, i ≤ h ∧ (rc = (P.xp i, P.yd) ∨ rc = (P.xm i, P.yd) ∨
    rc = (P.xd, P.yp i) ∨ rc = (P.xd, P.ym i))

/-- Anchor and signature cells for the four modes at one edge. -/
def EdgeCell (P : Selection n) (i : ℕ) (rc : Fin n × Fin n) : Prop :=
  (P.vPlus i).Cell (P.xp (i + 1)) (P.xp i) P.yd (P.yp i) rc ∨
  (P.vMinus i).Cell (P.xm i) (P.xm (i + 1)) P.yd (P.ym i) rc ∨
  (P.wPlus i).Cell (P.xp (i + 1)) P.xd (P.yp i) (P.yp (i + 1)) rc ∨
  (P.wMinus i).Cell (P.xm (i + 1)) P.xd (P.ym (i + 1)) (P.ym i) rc

/-- The protected cells of the whole selected path. -/
def GuardCell (P : Selection n) (h : ℕ) (rc : Fin n × Fin n) : Prop :=
  P.CoreCell h rc ∨ ∃ i, i < h ∧ P.EdgeCell i rc

def guards (P : Selection n) (h : ℕ) : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter (P.GuardCell h)

@[simp] theorem mem_guards (P : Selection n) (h : ℕ) (rc : Fin n × Fin n) :
    rc ∈ P.guards h ↔ P.GuardCell h rc := by
  classical
  simp [guards]

/-- Explicit original-matrix conditions on a selected path. The frame validity
contains all required order comparisons and all 64-anchor signatures. -/
structure Valid (P : Selection n) (A : BinaryMatrix n) (h : ℕ) : Prop where
  root_plus : A (P.xp 0) (P.yp 0) = true
  root_minus : A (P.xm 0) (P.ym 0) = false
  dummy_col : ∀ i, i ≤ h → A (P.xp i) P.yd = true ∧ A (P.xm i) P.yd = true
  dummy_row : ∀ i, i ≤ h → A P.xd (P.yp i) = true ∧ A P.xd (P.ym i) = true
  leaf_row : P.xp h = P.xm h
  leaf_col : P.yp h = P.ym h
  vertical_plus : ∀ i, i < h →
    (P.vPlus i).Valid A (P.xp (i + 1)) (P.xp i) P.yd (P.yp i)
  vertical_minus : ∀ i, i < h →
    (P.vMinus i).Valid A (P.xm i) (P.xm (i + 1)) P.yd (P.ym i)
  horizontal_plus : ∀ i, i < h →
    (P.wPlus i).Valid A (P.xp (i + 1)) P.xd (P.yp i) (P.yp (i + 1))
  horizontal_minus : ∀ i, i < h →
    (P.wMinus i).Valid A (P.xm (i + 1)) P.xd (P.ym (i + 1)) (P.ym i)

/-- If no guard cell was edited, every condition needed for path propagation
and exact anchor completion survives. -/
theorem Valid.transfer {P : Selection n} {A B : BinaryMatrix n} {h : ℕ}
    (hv : P.Valid A h)
    (hag : ∀ rc ∈ P.guards h, A rc.1 rc.2 = B rc.1 rc.2) :
    P.Valid B h := by
  have hc : ∀ rc, P.CoreCell h rc → A rc.1 rc.2 = B rc.1 rc.2 := by
    intro rc hrc
    exact hag rc ((mem_guards P h rc).mpr (Or.inl hrc))
  have he : ∀ i, i < h → ∀ rc, P.EdgeCell i rc → A rc.1 rc.2 = B rc.1 rc.2 := by
    intro i hi rc hrc
    exact hag rc ((mem_guards P h rc).mpr (Or.inr ⟨i, hi, hrc⟩))
  refine ⟨?_, ?_, ?_, ?_, hv.leaf_row, hv.leaf_col, ?_, ?_, ?_, ?_⟩
  · exact (hc _ (Or.inl rfl)).symm.trans hv.root_plus
  · exact (hc _ (Or.inr (Or.inl rfl))).symm.trans hv.root_minus
  · intro i hi
    constructor
    · exact (hc _ (Or.inr (Or.inr ⟨i, hi, Or.inl rfl⟩))).symm.trans
        (hv.dummy_col i hi).1
    · exact (hc _ (Or.inr (Or.inr ⟨i, hi, Or.inr (Or.inl rfl)⟩))).symm.trans
        (hv.dummy_col i hi).2
  · intro i hi
    constructor
    · exact (hc _ (Or.inr (Or.inr ⟨i, hi, Or.inr (Or.inr (Or.inl rfl))⟩))).symm.trans
        (hv.dummy_row i hi).1
    · exact (hc _ (Or.inr (Or.inr ⟨i, hi, Or.inr (Or.inr (Or.inr rfl))⟩))).symm.trans
        (hv.dummy_row i hi).2
  · intro i hi
    exact (hv.vertical_plus i hi).transfer (fun rc hrc => he i hi rc (Or.inl hrc))
  · intro i hi
    exact (hv.vertical_minus i hi).transfer
      (fun rc hrc => he i hi rc (Or.inr (Or.inl hrc)))
  · intro i hi
    exact (hv.horizontal_plus i hi).transfer
      (fun rc hrc => he i hi rc (Or.inr (Or.inr (Or.inl hrc))))
  · intro i hi
    exact (hv.horizontal_minus i hi).transfer
      (fun rc hrc => he i hi rc (Or.inr (Or.inr (Or.inr hrc))))

/-- Every valid selected path gives a copy of the exact fixed H. -/
theorem Valid.not_HFree {P : Selection n} {B : BinaryMatrix n} {h : ℕ}
    (hv : P.Valid B h) : ¬ HFree fixedH B := by
  obtain ⟨i, hi, hb⟩ := PathPropagation.exists_modeBody hv.root_plus hv.root_minus
    hv.dummy_col hv.dummy_row hv.leaf_row hv.leaf_col
  rcases hb with hb | hb | hb | hb
  · exact (hv.vertical_plus i hi).not_HFree hb
  · exact (hv.vertical_minus i hi).not_HFree hb
  · exact (hv.horizontal_plus i hi).not_HFree hb
  · exact (hv.horizontal_minus i hi).not_HFree hb

/-- Arbitrary edits outside the finite guard set cannot destroy all copies. -/
theorem not_HFree_of_agree {P : Selection n} {A B : BinaryMatrix n} {h : ℕ}
    (hv : P.Valid A h)
    (hag : ∀ rc ∈ P.guards h, A rc.1 rc.2 = B rc.1 rc.2) :
    ¬ HFree fixedH B :=
  (hv.transfer hag).not_HFree

/-- Every H-free repair must hit the guard set of each valid selected path.
This is a statement about all repairs, not just destroying original copies. -/
theorem repair_hits_guards {P : Selection n} {A B : BinaryMatrix n} {h : ℕ}
    (hv : P.Valid A h) (hfree : HFree fixedH B) :
    ∃ rc ∈ P.guards h, A rc.1 rc.2 ≠ B rc.1 rc.2 := by
  classical
  by_contra hn
  push Not at hn
  exact not_HFree_of_agree hv hn hfree

end Selection
end Problem348.GuardedPath

end

end OAI
end
end

section
section
namespace OAI


/-!
# Avoiding a finite family of events by counting

The cardinality of a finite union is bounded by the sum of the individual
cardinalities. A strict bound below the size of the ambient finite type
therefore supplies an element outside every event. The rational corollary
uses normalized cardinalities and requires no independence assumption.
-/


namespace Problem348.Sampling

open scoped BigOperators

/-- A family of finite bad events whose summed cardinality is smaller than the
ambient finite type has an element avoiding every event in the family. -/
theorem exists_avoiding_of_sum_card_lt {Ω : Type uOmega} {I : Type uI} [Fintype Ω]
    (events : Finset I) (bad : I → Finset Ω)
    (hsmall : (∑ i ∈ events, (bad i).card) < Fintype.card Ω) :
    ∃ ω, ∀ i ∈ events, ω ∉ bad i := by
  classical
  have hUnion : (events.biUnion bad).card < (Finset.univ : Finset Ω).card := by
    rw [Finset.card_univ]
    exact lt_of_le_of_lt Finset.card_biUnion_le hsmall
  obtain ⟨ω, _, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card hUnion
  refine ⟨ω, ?_⟩
  intro i hi hbad
  exact hω (Finset.mem_biUnion.mpr ⟨i, hi, hbad⟩)

/-- Uniform rational bounds on the normalized bad-event cardinalities give an
avoiding element when the number of events times the bound is less than one.
The events may overlap arbitrarily. -/
theorem exists_avoiding_of_uniform_ratio_lt {Ω : Type uOmega} {I : Type uI} [Fintype Ω]
    (events : Finset I) (bad : I → Finset Ω) (r : ℚ)
    (hΩ : 0 < Fintype.card Ω)
    (hbound : ∀ i ∈ events, ((bad i).card : ℚ) / (Fintype.card Ω : ℚ) ≤ r)
    (hsmall : (events.card : ℚ) * r < 1) :
    ∃ ω, ∀ i ∈ events, ω ∉ bad i := by
  have hpos : (0 : ℚ) < (Fintype.card Ω : ℚ) := Nat.cast_pos.mpr hΩ
  have hsum : (∑ i ∈ events, ((bad i).card : ℚ)) < (Fintype.card Ω : ℚ) := by
    calc
      (∑ i ∈ events, ((bad i).card : ℚ))
          ≤ ∑ i ∈ events, r * (Fintype.card Ω : ℚ) :=
        Finset.sum_le_sum fun i hi => (div_le_iff₀ hpos).mp (hbound i hi)
      _ = (events.card : ℚ) * r * (Fintype.card Ω : ℚ) := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ < 1 * (Fintype.card Ω : ℚ) := mul_lt_mul_of_pos_right hsmall hpos
      _ = (Fintype.card Ω : ℚ) := one_mul _
  apply exists_avoiding_of_sum_card_lt events bad
  apply (Nat.cast_lt (α := ℚ)).mp
  simpa only [Nat.cast_sum] using hsum

/-- A fraction-free uniform union bound.  Every bad event occupies at most
`1 / q` of the finite sample space; fewer than `q` bad events can be avoided.
No independence between the bad events is required. -/
theorem exists_avoiding_of_card_mul_le {Ω : Type uOmega} {I : Type uI} [Fintype Ω]
    (events : Finset I) (bad : I → Finset Ω) (q : ℕ)
    (hΩ : 0 < Fintype.card Ω)
    (hbound : ∀ i ∈ events, (bad i).card * q ≤ Fintype.card Ω)
    (hsmall : events.card < q) :
    ∃ ω, ∀ i ∈ events, ω ∉ bad i := by
  have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le _) hsmall
  apply exists_avoiding_of_sum_card_lt events bad
  apply (Nat.mul_lt_mul_right hq).mp
  calc
    (∑ i ∈ events, (bad i).card) * q
        = ∑ i ∈ events, (bad i).card * q := Finset.sum_mul _ _ _
    _ ≤ ∑ _i ∈ events, Fintype.card Ω := Finset.sum_le_sum hbound
    _ = events.card * Fintype.card Ω := by simp
    _ < q * Fintype.card Ω := Nat.mul_lt_mul_of_pos_right hsmall hΩ
    _ = Fintype.card Ω * q := Nat.mul_comm _ _

/-- The cellwise counting form of sampling avoidance.
The relation `selected ω e` means that sample `ω` uses the relevant cell `e`.
The budget is the square of the common size of the axis classes. -/
theorem exists_selection_avoiding {Ω : Type uOmega} {Cell : Type uCell} [Fintype Ω]
    (changed : Finset Cell) (selected : Ω → Cell → Prop) (m : ℕ)
    [DecidableRel selected]
    (hΩ : 0 < Fintype.card Ω)
    (hbound : ∀ e ∈ changed,
      (Finset.univ.filter (fun ω => selected ω e)).card * m ^ 2 ≤ Fintype.card Ω)
    (hsmall : changed.card < m ^ 2) :
    ∃ ω, ∀ e ∈ changed, ¬ selected ω e := by
  obtain ⟨ω, hω⟩ := exists_avoiding_of_card_mul_le changed
    (fun e => Finset.univ.filter (fun ω => selected ω e)) (m ^ 2) hΩ hbound hsmall
  exact ⟨ω, fun e he hs => hω e he (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)⟩

/-- Agreement on every protected selected cell follows from the cellwise
sampling estimate.  Unprotected cells are allowed to change arbitrarily. -/
theorem exists_agreement_of_changed_card_lt
    {Ω : Type uOmega} {Cell : Type uCell} {Value : Type uValue} [Fintype Ω] [Fintype Cell] [DecidableEq Value]
    (A B : Cell → Value) (selected : Ω → Cell → Prop)
    (relevant : Cell → Prop) [DecidableRel selected] [DecidablePred relevant]
    (m : ℕ) (hΩ : 0 < Fintype.card Ω)
    (hbound : ∀ e, relevant e →
      (Finset.univ.filter (fun ω => selected ω e)).card * m ^ 2 ≤ Fintype.card Ω)
    (hsmall : (Finset.univ.filter (fun e => A e ≠ B e)).card < m ^ 2) :
    ∃ ω, ∀ e, relevant e → selected ω e → A e = B e := by
  classical
  let changed := Finset.univ.filter (fun e => A e ≠ B e)
  let events := changed.filter relevant
  have hsmall' : events.card < m ^ 2 :=
    lt_of_le_of_lt (Finset.card_filter_le _ _) hsmall
  obtain ⟨ω, hω⟩ := exists_selection_avoiding events selected m hΩ
    (fun e he => hbound e (Finset.mem_filter.mp he).2) hsmall'
  refine ⟨ω, ?_⟩
  intro e he hs
  by_contra hne
  exact hω e (by simp [events, changed, he, hne]) hs

/-- Version for the three-seed sample space used in the tree construction.
There are `m³` samples, and a protected cell occurs in at most `m` of them. -/
theorem exists_agreement_three_seed
    {Cell : Type uCell} {Value : Type uValue} [Fintype Cell] [DecidableEq Value]
    (m : ℕ) (hm : 0 < m) (A B : Cell → Value)
    (selected : (Fin m × Fin m × Fin m) → Cell → Prop)
    (relevant : Cell → Prop) [DecidableRel selected] [DecidablePred relevant]
    (hbound : ∀ e, relevant e →
      (Finset.univ.filter (fun ω => selected ω e)).card ≤ m)
    (hsmall : (Finset.univ.filter (fun e => A e ≠ B e)).card < m ^ 2) :
    ∃ ω, ∀ e, relevant e → selected ω e → A e = B e := by
  apply exists_agreement_of_changed_card_lt A B selected relevant m
  · simpa using Nat.mul_pos hm (Nat.mul_pos hm hm)
  · intro e he
    calc
      (Finset.univ.filter (fun ω => selected ω e)).card * m ^ 2
          ≤ m * m ^ 2 := Nat.mul_le_mul_right _ (hbound e he)
      _ = Fintype.card (Fin m × Fin m × Fin m) := by
        simp [pow_two]
  · exact hsmall

/-- Contrapositive form: if every sample forces a changed protected cell,
then at least `m²` entries have changed. -/
theorem sq_le_changed_card_of_forcing
    {Ω : Type uOmega} {Cell : Type uCell} {Value : Type uValue} [Fintype Ω] [Fintype Cell] [DecidableEq Value]
    (A B : Cell → Value) (selected : Ω → Cell → Prop)
    (relevant : Cell → Prop) [DecidableRel selected] [DecidablePred relevant]
    (m : ℕ) (hΩ : 0 < Fintype.card Ω)
    (hbound : ∀ e, relevant e →
      (Finset.univ.filter (fun ω => selected ω e)).card * m ^ 2 ≤ Fintype.card Ω)
    (hforcing : ∀ ω, ∃ e, relevant e ∧ selected ω e ∧ A e ≠ B e) :
    m ^ 2 ≤ (Finset.univ.filter (fun e => A e ≠ B e)).card := by
  by_contra h
  obtain ⟨ω, hω⟩ := exists_agreement_of_changed_card_lt A B selected relevant m
    hΩ hbound (Nat.lt_of_not_ge h)
  obtain ⟨e, he, hs, hne⟩ := hforcing ω
  exact hne (hω e he hs)

end Problem348.Sampling

end OAI
end
end

section
section
namespace OAI

/-!
# From sampled protected cells to arbitrary-repair distance

The guard sets comprise only cells that the path proof requires to stay
unchanged. The hypotheses do not require preservation of every
variable-variable entry or of an original copy of the pattern.
-/


noncomputable section

namespace Problem348.Sampling

/-- A sparse family of guards with a deterministic obstruction forces a lower
bound on every repair to an `H`-free matrix.  The pattern may be arbitrary. -/
theorem hammingDistance_ge_of_guard_sampling
    {k n : ℕ} {Ω : Type uOmega} [Fintype Ω]
    (H : BinaryMatrix k) (A B : BinaryMatrix n)
    (guard : Ω → Finset (Fin n × Fin n)) (m : ℕ)
    (hΩ : 0 < Fintype.card Ω)
    (hbound : ∀ e,
      (Finset.univ.filter (fun ω => e ∈ guard ω)).card * m ^ 2 ≤ Fintype.card Ω)
    (hforce : ∀ ω,
      (∀ e ∈ guard ω, A e.1 e.2 = B e.1 e.2) → ¬ HFree H B)
    (hfree : HFree H B) : m ^ 2 ≤ hammingDistance A B := by
  classical
  by_contra h
  have hsmall :
      (Finset.univ.filter (fun e : Fin n × Fin n => A e.1 e.2 ≠ B e.1 e.2)).card
        < m ^ 2 := by
    simpa only [hammingDistance] using Nat.lt_of_not_ge h
  obtain ⟨ω, hω⟩ := exists_agreement_of_changed_card_lt
    (fun e : Fin n × Fin n => A e.1 e.2)
    (fun e : Fin n × Fin n => B e.1 e.2)
    (fun ω e => e ∈ guard ω) (fun _ => True) m hΩ
    (fun e _ => hbound e) hsmall
  exact hforce ω (fun e he => hω e True.intro he) hfree

/-- The three-seed specialization: a guard uses each cell in at most `m`
of the `m³` samples.  Therefore no `H`-free repair changes fewer than `m²`
entries. -/
theorem hammingDistance_ge_of_three_seed_guards
    {k n : ℕ} (m : ℕ) (hm : 0 < m)
    (H : BinaryMatrix k) (A B : BinaryMatrix n)
    (guard : (Fin m × Fin m × Fin m) → Finset (Fin n × Fin n))
    (hbound : ∀ e, (Finset.univ.filter (fun ω => e ∈ guard ω)).card ≤ m)
    (hforce : ∀ ω,
      (∀ e ∈ guard ω, A e.1 e.2 = B e.1 e.2) → ¬ HFree H B)
    (hfree : HFree H B) : m ^ 2 ≤ hammingDistance A B := by
  apply hammingDistance_ge_of_guard_sampling H A B guard m
  · simpa using Nat.mul_pos hm (Nat.mul_pos hm hm)
  · intro e
    calc
      (Finset.univ.filter (fun ω => e ∈ guard ω)).card * m ^ 2
          ≤ m * m ^ 2 := Nat.mul_le_mul_right _ (hbound e)
      _ = Fintype.card (Fin m × Fin m × Fin m) := by simp [pow_two]
  · exact hforce
  · exact hfree

/-- A guard-frequency estimate can be obtained from a larger set of protected
selected cells.  This is useful when the deterministic path proof uses just a
subset of all selected anchor, dummy, and root incidences. -/
theorem guard_frequency_le {Ω : Type uOmega} {Cell : Type uCell} [Fintype Ω] [DecidableEq Cell]
    (guard : Ω → Finset Cell) (selected : Ω → Cell → Prop)
    [DecidableRel selected]
    (hsub : ∀ ω e, e ∈ guard ω → selected ω e) (e : Cell) :
    (Finset.univ.filter (fun ω => e ∈ guard ω)).card ≤
      (Finset.univ.filter (fun ω => selected ω e)).card := by
  classical
  apply Finset.card_le_card
  intro ω hω
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub ω e (Finset.mem_filter.mp hω).2⟩

end Problem348.Sampling

end

end OAI
end
end

section
section
namespace OAI

/-!
# The concrete common-leaf selection in the canonical host

The row/column enumerations are independent. `AxisConditions` records only the
order properties required of those enumerations; entries, role memberships,
root values, shared leaves, and the resulting guarded-path validity are proved
from the actual canonical host and the concrete sampled positions.
-/

noncomputable section
namespace Problem348.Construction.SampledSelection

open HostSampledPath

/-- The ten order facts used by the sampled-path construction.  These are
separate from matrix entries and can be supplied by any correct enumeration
of the two recursively ordered axes. -/
structure AxisConditions {h n : ℕ} (er ec : Position h ≃ Fin n) : Prop where
  anchor_rows : ∀ (t : Mode h) (a : Fin (2 ^ h)),
    StrictMono (fun u : Fin 64 => er (.inl (t, u, a)))
  anchor_cols : ∀ (t : Mode h) (a : Fin (2 ^ h)),
    StrictMono (fun u : Fin 64 => ec (.inl (t, u, a)))
  anchor_before_rows : ∀ (t : Mode h) (u : Fin 64) (a : Fin (2 ^ h))
    (x : VariablePosition h ⊕ Fin (2 ^ h)), er (.inl (t, u, a)) < er (.inr x)
  anchor_before_cols : ∀ (t : Mode h) (u : Fin 64) (a : Fin (2 ^ h))
    (x : VariablePosition h ⊕ Fin (2 ^ h)), ec (.inl (t, u, a)) < ec (.inr x)
  variable_before_dummy : ∀ (x : VariablePosition h) (a : Fin (2 ^ h)),
    er (.inr (.inl x)) < er (dummy h a)
  dummy_before_variable : ∀ (x : VariablePosition h) (a : Fin (2 ^ h)),
    ec (dummy h a) < ec (.inr (.inl x))
  row_plus : ∀ (i : Fin h) (z u : Fin (2 ^ h)),
    er (position h (i.val + 1) (by omega) true z u) <
      er (position h i.val (by omega) true z u)
  row_minus : ∀ (i : Fin h) (z u : Fin (2 ^ h)),
    er (position h i.val (by omega) false z u) <
      er (position h (i.val + 1) (by omega) false z u)
  col_plus : ∀ (i : Fin h) (z u : Fin (2 ^ h)),
    ec (position h i.val (by omega) true z u) <
      ec (position h (i.val + 1) (by omega) true z u)
  col_minus : ∀ (i : Fin h) (z u : Fin (2 ^ h)),
    ec (position h (i.val + 1) (by omega) false z u) <
      ec (position h i.val (by omega) false z u)

/-- A total path; indices beyond the tree depth repeat the common leaf. -/
def path (h i : ℕ) (s : Bool) (z u : Fin (2 ^ h)) : Position h :=
  position h (min i h) (Nat.min_le_right i h) s z u

@[simp] theorem path_of_le {h i : ℕ} (hi : i ≤ h) (s : Bool)
    (z u : Fin (2 ^ h)) : path h i s z u = position h i hi s z u := by
  simp [path, Nat.min_eq_left hi]

/-- A harmless total extension of the edge index; it equals `i` for `i<h`. -/
def edge {h : ℕ} (hh : 1 ≤ h) (i : ℕ) : Fin h :=
  ⟨i % h, Nat.mod_lt _ (by omega)⟩

@[simp] theorem edge_of_lt {h i : ℕ} (hh : 1 ≤ h) (hi : i < h) :
    edge hh i = (⟨i, hi⟩ : Fin h) := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt hi

/-- The anchor mode for one of the horizontal propagation steps. -/
def horizontalMode {h : ℕ} (hh : 1 ≤ h) (z : Fin (2 ^ h))
    (i : ℕ) (s : Bool) : Mode h :=
  horizontal (edge hh i) s
    (parity (z.val / SampledPath.blockSize h ((edge hh i).val + 1)))

/-- The selected anchor representatives use the same row/column seed in every
anchor group. This correlation does not affect the cellwise sampling proof. -/
def frame {h n : ℕ} (er ec : Position h ≃ Fin n)
    (ha : AxisConditions er ec) (t : Mode h) (u v : Fin (2 ^ h)) :
    GuardedPath.AnchorFrame n :=
  SelectedAnchor.frame er ec t (fun _ => u) (fun _ => v)
    (ha.anchor_rows t u) (ha.anchor_cols t v)

/-- The actual selected path and four anchor frames at each edge. -/
def selection {h n : ℕ} (hh : 1 ≤ h) (er ec : Position h ≃ Fin n)
    (ha : AxisConditions er ec) (z u v : Fin (2 ^ h)) : GuardedPath.Selection n where
  xp i := er (path h i true z u)
  xm i := er (path h i false z u)
  yp i := ec (path h i true z v)
  ym i := ec (path h i false z v)
  xd := er (dummy h u)
  yd := ec (dummy h v)
  vPlus i := frame er ec ha (vertical (edge hh i) true) u v
  vMinus i := frame er ec ha (vertical (edge hh i) false) u v
  wPlus i := frame er ec ha (horizontalMode hh z i true) u v
  wMinus i := frame er ec ha (horizontalMode hh z i false) u v

/-- For named body roles, all anchor/signature data follow from the host;
only the two body order inequalities need to be supplied. -/
theorem frame_valid {h n : ℕ} (er ec : Position h ≃ Fin n)
    (ha : AxisConditions er ec) (t : Mode h) (u v : Fin (2 ^ h))
    (r₀ r₁ c₀ c₁ : Position h)
    (hr₀ : rowRole t 0 r₀) (hr₁ : rowRole t 1 r₁)
    (hc₀ : colRole t 0 c₀) (hc₁ : colRole t 1 c₁)
    (hrs : er r₀ < er r₁) (hcs : ec c₀ < ec c₁) :
    (frame er ec ha t u v).Valid (SelectedAnchor.matrix er ec)
      (er r₀) (er r₁) (ec c₀) (ec c₁) := by
  apply SelectedAnchor.frame_valid er ec t (fun _ => u) (fun _ => v)
    (ha.anchor_rows t u) (ha.anchor_cols t v) r₀ r₁ c₀ c₁ hr₀ hr₁ hc₀ hc₁
  · intro j
    cases r₀ with
    | inl a => simp [rowRole] at hr₀
    | inr x => exact ha.anchor_before_rows t j u x
  · exact hrs
  · intro j
    cases c₀ with
    | inl a => simp [colRole] at hc₀
    | inr x => exact ha.anchor_before_cols t j v x
  · exact hcs

theorem vertical_plus_valid {h n : ℕ} (er ec : Position h ≃ Fin n)
    (ha : AxisConditions er ec) (i : Fin h) (z u v : Fin (2 ^ h)) :
    (frame er ec ha (vertical i true) u v).Valid (SelectedAnchor.matrix er ec)
      (er (position h (i.val + 1) (by omega) true z u))
      (er (position h i.val (by omega) true z u))
      (ec (dummy h v)) (ec (position h i.val (by omega) true z v)) := by
  apply frame_valid er ec ha
  · exact vertical_plus_row_first i z u
  · exact vertical_plus_row_second i z u
  · exact vertical_col_first i true v
  · exact vertical_col_second i true z v
  · exact ha.row_plus i z u
  · exact ha.dummy_before_variable _ v

theorem vertical_minus_valid {h n : ℕ} (er ec : Position h ≃ Fin n)
    (ha : AxisConditions er ec) (i : Fin h) (z u v : Fin (2 ^ h)) :
    (frame er ec ha (vertical i false) u v).Valid (SelectedAnchor.matrix er ec)
      (er (position h i.val (by omega) false z u))
      (er (position h (i.val + 1) (by omega) false z u))
      (ec (dummy h v)) (ec (position h i.val (by omega) false z v)) := by
  apply frame_valid er ec ha
  · exact vertical_minus_row_first i z u
  · exact vertical_minus_row_second i z u
  · exact vertical_col_first i false v
  · exact vertical_col_second i false z v
  · exact ha.row_minus i z u
  · exact ha.dummy_before_variable _ v

theorem horizontal_plus_valid {h n : ℕ} (er ec : Position h ≃ Fin n)
    (ha : AxisConditions er ec) (i : Fin h) (z u v : Fin (2 ^ h)) :
    (frame er ec ha
      (horizontal i true (parity (z.val / SampledPath.blockSize h (i.val + 1)))) u v).Valid
      (SelectedAnchor.matrix er ec)
      (er (position h (i.val + 1) (by omega) true z u)) (er (dummy h u))
      (ec (position h i.val (by omega) true z v))
      (ec (position h (i.val + 1) (by omega) true z v)) := by
  apply frame_valid er ec ha
  · exact horizontal_row_first i true z u
  · exact horizontal_row_second i true _ u
  · exact horizontal_plus_col_first i _ z v
  · exact horizontal_plus_col_second i z v
  · exact ha.variable_before_dummy _ u
  · exact ha.col_plus i z v

theorem horizontal_minus_valid {h n : ℕ} (er ec : Position h ≃ Fin n)
    (ha : AxisConditions er ec) (i : Fin h) (z u v : Fin (2 ^ h)) :
    (frame er ec ha
      (horizontal i false (parity (z.val / SampledPath.blockSize h (i.val + 1)))) u v).Valid
      (SelectedAnchor.matrix er ec)
      (er (position h (i.val + 1) (by omega) false z u)) (er (dummy h u))
      (ec (position h (i.val + 1) (by omega) false z v))
      (ec (position h i.val (by omega) false z v)) := by
  apply frame_valid er ec ha
  · exact horizontal_row_first i false z u
  · exact horizontal_row_second i false _ u
  · exact horizontal_minus_col_first i z v
  · exact horizontal_minus_col_second i _ z v
  · exact ha.variable_before_dummy _ u
  · exact ha.col_minus i z v

/-- Every concrete three-seed selection satisfies all guarded-path hypotheses.
Only the axis order laws were assumed; the entire original-matrix certificate
is derived from the exact host entries and the sampled common-leaf path. -/
theorem selection_valid {h n : ℕ} (hh : 1 ≤ h) (er ec : Position h ≃ Fin n)
    (ha : AxisConditions er ec) (z u v : Fin (2 ^ h)) :
    (selection hh er ec ha z u v).Valid (SelectedAnchor.matrix er ec) h := by
  constructor
  · simp only [selection, SelectedAnchor.matrix_apply,
      path_of_le (Nat.zero_le h)]
    exact variableEntry_root_plus_of_atLevel hh _ _
      (sample_atLevel h 0 (Nat.zero_le h) true z u)
      (sample_atLevel h 0 (Nat.zero_le h) true z v)
  · simp only [selection, SelectedAnchor.matrix_apply,
      path_of_le (Nat.zero_le h)]
    exact variableEntry_root_minus_of_atLevel hh _ _
      (sample_atLevel h 0 (Nat.zero_le h) false z u)
      (sample_atLevel h 0 (Nat.zero_le h) false z v)
  · intro i hi
    simp [selection, SelectedAnchor.matrix_apply, path, position, dummy, host]
  · intro i hi
    simp [selection, SelectedAnchor.matrix_apply, path, position, dummy, host]
  · simp only [selection, path_of_le (Nat.le_refl h)]
    exact congrArg er (position_shared_leaf h true false z u u)
  · simp only [selection, path_of_le (Nat.le_refl h)]
    exact congrArg ec (position_shared_leaf h true false z v v)
  · intro i hi
    simpa only [selection, edge_of_lt hh hi, path_of_le hi.le,
      path_of_le (show i + 1 ≤ h by omega)] using
      vertical_plus_valid er ec ha ⟨i, hi⟩ z u v
  · intro i hi
    simpa only [selection, edge_of_lt hh hi, path_of_le hi.le,
      path_of_le (show i + 1 ≤ h by omega)] using
      vertical_minus_valid er ec ha ⟨i, hi⟩ z u v
  · intro i hi
    simpa only [selection, horizontalMode, edge_of_lt hh hi, path_of_le hi.le,
      path_of_le (show i + 1 ≤ h by omega)] using
      horizontal_plus_valid er ec ha ⟨i, hi⟩ z u v
  · intro i hi
    simpa only [selection, horizontalMode, edge_of_lt hh hi, path_of_le hi.le,
      path_of_le (show i + 1 ≤ h by omega)] using
      horizontal_minus_valid er ec ha ⟨i, hi⟩ z u v

end Problem348.Construction.SampledSelection

end

end OAI
end
end

section
section
namespace OAI

/-! The four sampled body orders, including the shared-leaf edge. -/

namespace Problem348.HostSampledPath

open SampledPath

 theorem sample_plus_eq (h i : ℕ) (hi : i ≤ h) (z u : Fin (2 ^ h)) :
    sample h i hi true z u = TreePositions.plusPos i hi (mixFin h i hi z u) := by
  apply Prod.ext
  · apply Fin.ext
    simp [sample, classAt, TreePositions.plusPos]
    omega
  · rfl

 theorem sample_minus_eq (h i : ℕ) (hi : i ≤ h) (z u : Fin (2 ^ h)) :
    sample h i hi false z u = TreePositions.minusPos i hi (mixFin h i hi z u) := by
  simp [sample, classAt, TreePositions.minusPos]

@[simp] theorem treeNode_mixFin (h i : ℕ) (hi : i ≤ h) (z u : Fin (2 ^ h)) :
    TreePositions.node i (mixFin h i hi z u) = z.val / blockSize h i :=
  mixFin_node h i hi z u

 theorem row_plus_sample_child_lt_parent {h : ℕ} (i : Fin h)
    (z u v : Fin (2 ^ h)) :
    TreePositions.rowKey h (sample h (i.val + 1) (by omega) true z u) <
      TreePositions.rowKey h (sample h i.val (by omega) true z v) := by
  rw [sample_plus_eq, sample_plus_eq,
    TreePositions.row_plus_child_lt_parent i.isLt]
  simp only [treeNode_mixFin]
  rw [ancestor_parent h i.val z.val (by omega)]

 theorem row_minus_sample_parent_lt_child {h : ℕ} (i : Fin h)
    (z u v : Fin (2 ^ h)) :
    TreePositions.rowKey h (sample h i.val (by omega) false z v) <
      TreePositions.rowKey h (sample h (i.val + 1) (by omega) false z u) := by
  rw [sample_minus_eq, sample_minus_eq,
    TreePositions.row_minus_parent_lt_child i.isLt]
  simp only [treeNode_mixFin]
  rw [ancestor_parent h i.val z.val (by omega)]

 theorem column_plus_sample_parent_lt_child {h : ℕ} (i : Fin h)
    (z u v : Fin (2 ^ h)) :
    TreePositions.columnKey h (sample h i.val (by omega) true z v) <
      TreePositions.columnKey h (sample h (i.val + 1) (by omega) true z u) := by
  rw [sample_plus_eq, sample_plus_eq,
    TreePositions.column_plus_parent_lt_child i.isLt]
  simp only [treeNode_mixFin]
  rw [ancestor_parent h i.val z.val (by omega)]

 theorem column_minus_sample_child_lt_parent {h : ℕ} (i : Fin h)
    (z u v : Fin (2 ^ h)) :
    TreePositions.columnKey h (sample h (i.val + 1) (by omega) false z u) <
      TreePositions.columnKey h (sample h i.val (by omega) false z v) := by
  rw [sample_minus_eq, sample_minus_eq,
    TreePositions.column_minus_child_lt_parent i.isLt]
  simp only [treeNode_mixFin]
  rw [ancestor_parent h i.val z.val (by omega)]

/-- Consequence after transporting the canonical row key into any ordered axis. -/
theorem row_plus_sample_order {h : ℕ} {R : Type uR} [Preorder R]
    (r : Construction.Position h → R)
    (hr : ∀ p q : Construction.VariablePosition h,
      TreePositions.rowKey h p < TreePositions.rowKey h q →
        r (Sum.inr (Sum.inl p)) < r (Sum.inr (Sum.inl q)))
    (i : Fin h) (z u v : Fin (2 ^ h)) :
    r (position h (i.val + 1) (by omega) true z u) <
      r (position h i.val (by omega) true z v) :=
  hr _ _ (row_plus_sample_child_lt_parent i z u v)

 theorem row_minus_sample_order {h : ℕ} {R : Type uR} [Preorder R]
    (r : Construction.Position h → R)
    (hr : ∀ p q : Construction.VariablePosition h,
      TreePositions.rowKey h p < TreePositions.rowKey h q →
        r (Sum.inr (Sum.inl p)) < r (Sum.inr (Sum.inl q)))
    (i : Fin h) (z u v : Fin (2 ^ h)) :
    r (position h i.val (by omega) false z v) <
      r (position h (i.val + 1) (by omega) false z u) :=
  hr _ _ (row_minus_sample_parent_lt_child i z u v)

 theorem column_plus_sample_order {h : ℕ} {C : Type uC} [Preorder C]
    (c : Construction.Position h → C)
    (hc : ∀ p q : Construction.VariablePosition h,
      TreePositions.columnKey h p < TreePositions.columnKey h q →
        c (Sum.inr (Sum.inl p)) < c (Sum.inr (Sum.inl q)))
    (i : Fin h) (z u v : Fin (2 ^ h)) :
    c (position h i.val (by omega) true z v) <
      c (position h (i.val + 1) (by omega) true z u) :=
  hc _ _ (column_plus_sample_parent_lt_child i z u v)

 theorem column_minus_sample_order {h : ℕ} {C : Type uC} [Preorder C]
    (c : Construction.Position h → C)
    (hc : ∀ p q : Construction.VariablePosition h,
      TreePositions.columnKey h p < TreePositions.columnKey h q →
        c (Sum.inr (Sum.inl p)) < c (Sum.inr (Sum.inl q)))
    (i : Fin h) (z u v : Fin (2 ^ h)) :
    c (position h (i.val + 1) (by omega) false z u) <
      c (position h i.val (by omega) false z v) :=
  hc _ _ (column_minus_sample_child_lt_parent i z u v)

end Problem348.HostSampledPath

end OAI
end
end

section
section
namespace OAI

/-!
# The sampled selection on increasing host enumerations

The ten order assumptions of the concrete sampler follow from the independent
row and column enumerations. No order or entry certificate remains as a
hypothesis of `sampledSelection_valid`.
-/

noncomputable section
namespace Problem348.OrderedHost

open Construction

/-- The actual row and column enumerations meet every sampler order condition. -/
theorem sampledAxisConditions (h : ℕ) :
    SampledSelection.AxisConditions (rowIndex h) (columnIndex h) := by
  constructor
  · intro t a
    exact row_anchor_strictMono t (fun _ => a)
  · intro t a
    exact column_anchor_strictMono t (fun _ => a)
  · exact row_anchor_lt_nonanchor
  · exact column_anchor_lt_nonanchor
  · exact row_variable_lt_dummy
  · exact column_dummy_lt_variable
  · intro i z u
    exact HostSampledPath.row_plus_sample_order (rowIndex h)
      (fun p q hpq => (rowIndex_variable_lt_iff p q).mpr hpq) i z u u
  · intro i z u
    exact HostSampledPath.row_minus_sample_order (rowIndex h)
      (fun p q hpq => (rowIndex_variable_lt_iff p q).mpr hpq) i z u u
  · intro i z u
    exact HostSampledPath.column_plus_sample_order (columnIndex h)
      (fun p q hpq => (columnIndex_variable_lt_iff p q).mpr hpq) i z u u
  · intro i z u
    exact HostSampledPath.column_minus_sample_order (columnIndex h)
      (fun p q hpq => (columnIndex_variable_lt_iff p q).mpr hpq) i z u u

/-- The three-seed selection in the concrete matrix of the prescribed size. -/
def sampledSelection {h : ℕ} (hh : 1 ≤ h) (z u v : Fin (2 ^ h)) :
    GuardedPath.Selection (size h) :=
  SampledSelection.selection hh (rowIndex h) (columnIndex h)
    (sampledAxisConditions h) z u v

/-- The actual sampled path and anchor frames are valid without extra inputs. -/
theorem sampledSelection_valid {h : ℕ} (hh : 1 ≤ h) (z u v : Fin (2 ^ h)) :
    (sampledSelection hh z u v).Valid
      (SelectedAnchor.matrix (rowIndex h) (columnIndex h)) h :=
  SampledSelection.selection_valid hh (rowIndex h) (columnIndex h)
    (sampledAxisConditions h) z u v

end Problem348.OrderedHost

end

end OAI
end
end

section
section
namespace OAI

/-!
# Three-seed sampling for the tree-matrix repair argument

Choices in different groups on the same axis need not be independent.
Three uniform seeds suffice: a common leaf, a row seed and a column seed.
The equal-fiber calculation gives uniform marginals.
-/


namespace Problem348.TreeSampling

/-- Replace the within-block coordinate of a leaf by that of a second seed. -/
def mix {a b : ℕ} (z u : Fin (a * b)) : Fin (a * b) :=
  finProdFinEquiv ((finProdFinEquiv.symm z).1,
    (finProdFinEquiv.symm u).2)

@[simp] theorem mix_div {a b : ℕ} (z u : Fin (a * b)) :
    (finProdFinEquiv.symm (mix z u)).1 =
      (finProdFinEquiv.symm z).1 := by
  simp [mix]

@[simp] theorem mix_mod {a b : ℕ} (z u : Fin (a * b)) :
    (finProdFinEquiv.symm (mix z u)).2 =
      (finProdFinEquiv.symm u).2 := by
  simp [mix]

/-- The output of the mixer and the two unused coordinates determine both seeds. -/
def splitMix {a b : ℕ} :
    (Fin (a * b) × Fin (a * b)) ≃
      (Fin (a * b) × (Fin b × Fin a)) where
  toFun p := (mix p.1 p.2,
    ((finProdFinEquiv.symm p.1).2, (finProdFinEquiv.symm p.2).1))
  invFun p :=
    (finProdFinEquiv ((finProdFinEquiv.symm p.1).1, p.2.1),
      finProdFinEquiv (p.2.2, (finProdFinEquiv.symm p.1).2))
  left_inv p := by
    rcases p with ⟨z,u⟩
    simp only [mix, Equiv.symm_apply_apply]
    exact Prod.ext (finProdFinEquiv.apply_symm_apply z)
      (finProdFinEquiv.apply_symm_apply u)
  right_inv p := by
    rcases p with ⟨x,r,s⟩
    simp only [mix, Equiv.symm_apply_apply]
    exact Prod.ext (finProdFinEquiv.apply_symm_apply x) rfl

/-- A first-coordinate fiber of a product decomposition is the second factor. -/
def fiberOfEquiv {X : Type uX} {Y : Type uY} {Z : Type uZ} (e : X ≃ Y × Z) (y : Y) :
    {x : X // (e x).1 = y} ≃ Z where
  toFun x := (e x.1).2
  invFun z := ⟨e.symm (y, z), by simp⟩
  left_inv x := by
    apply Subtype.ext
    apply e.injective
    simp only [Equiv.apply_symm_apply]
    exact Prod.ext x.property.symm rfl
  right_inv z := by simp

/-- Every level-class position occurs equally often in the pair of seeds. -/
theorem card_mix_fiber {a b : ℕ} (x : Fin (a * b)) :
    Fintype.card {p : Fin (a * b) × Fin (a * b) // mix p.1 p.2 = x} =
      a * b := by
  classical
  calc
    _ = Fintype.card (Fin b × Fin a) :=
      Fintype.card_congr (fiberOfEquiv (splitMix (a := a) (b := b)) x)
    _ = _ := by simp [Nat.mul_comm]

/-- The three seeds are the common leaf, an axis-one seed and an axis-two seed. -/
abbrev Seeds (m : ℕ) := Fin m × (Fin m × Fin m)

/-- A variable row and an anchor/dummy column, together with unused coordinates. -/
def splitRow {a b : ℕ} :
    Seeds (a * b) ≃ (Fin (a * b) × Fin (a * b)) × (Fin b × Fin a) where
  toFun s := ((mix s.1 s.2.1, s.2.2),
    ((finProdFinEquiv.symm s.1).2, (finProdFinEquiv.symm s.2.1).1))
  invFun p := (finProdFinEquiv ((finProdFinEquiv.symm p.1.1).1, p.2.1),
    (finProdFinEquiv (p.2.2, (finProdFinEquiv.symm p.1.1).2), p.1.2))
  left_inv s := by
    rcases s with ⟨z,u,v⟩
    simp only [mix, Equiv.symm_apply_apply]
    exact Prod.ext (finProdFinEquiv.apply_symm_apply z)
      (Prod.ext (finProdFinEquiv.apply_symm_apply u) rfl)
  right_inv p := by
    rcases p with ⟨⟨x,y⟩,r,t⟩
    simp only [mix, Equiv.symm_apply_apply]
    exact Prod.ext (Prod.ext (finProdFinEquiv.apply_symm_apply x) rfl) rfl

/-- An anchor/dummy row and a variable column, with the unused coordinates. -/
def splitColumn {a b : ℕ} :
    Seeds (a * b) ≃ (Fin (a * b) × Fin (a * b)) × (Fin b × Fin a) where
  toFun s := ((s.2.1, mix s.1 s.2.2),
    ((finProdFinEquiv.symm s.1).2, (finProdFinEquiv.symm s.2.2).1))
  invFun p := (finProdFinEquiv ((finProdFinEquiv.symm p.1.2).1, p.2.1),
    (p.1.1, finProdFinEquiv (p.2.2, (finProdFinEquiv.symm p.1.2).2)))
  left_inv s := by
    rcases s with ⟨z,u,v⟩
    simp only [mix, Equiv.symm_apply_apply]
    exact Prod.ext (finProdFinEquiv.apply_symm_apply z)
      (Prod.ext rfl (finProdFinEquiv.apply_symm_apply v))
  right_inv p := by
    rcases p with ⟨⟨x,y⟩,r,t⟩
    simp only [mix, Equiv.symm_apply_apply]
    exact Prod.ext (Prod.ext rfl (finProdFinEquiv.apply_symm_apply y)) rfl

/-- Two independent axis seeds, with the common-leaf coordinate unused. -/
def splitBoth {m : ℕ} : Seeds m ≃ (Fin m × Fin m) × Fin m where
  toFun s := (s.2, s.1)
  invFun p := (p.2, p.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact protected-cell multiplicity when the row is variable. -/
theorem card_row_fiber {a b : ℕ} (x y : Fin (a * b)) :
    Fintype.card {s : Seeds (a * b) // (mix s.1 s.2.1, s.2.2) = (x,y)} =
      a * b := by
  classical
  calc
    _ = Fintype.card (Fin b × Fin a) :=
      Fintype.card_congr (fiberOfEquiv (splitRow (a := a) (b := b)) (x,y))
    _ = _ := by simp [Nat.mul_comm]

/-- Exact protected-cell multiplicity when the column is variable. -/
theorem card_column_fiber {a b : ℕ} (x y : Fin (a * b)) :
    Fintype.card {s : Seeds (a * b) // (s.2.1, mix s.1 s.2.2) = (x,y)} =
      a * b := by
  classical
  calc
    _ = Fintype.card (Fin b × Fin a) :=
      Fintype.card_congr (fiberOfEquiv (splitColumn (a := a) (b := b)) (x,y))
    _ = _ := by simp [Nat.mul_comm]

/-- Exact multiplicity for two anchor/dummy positions or two root positions. -/
theorem card_both_fiber {m : ℕ} (x y : Fin m) :
    Fintype.card {s : Seeds m // s.2 = (x,y)} = m := by
  classical
  calc
    _ = Fintype.card (Fin m) :=
      Fintype.card_congr (fiberOfEquiv (splitBoth (m := m)) (x,y))
    _ = _ := Fintype.card_fin m

@[simp] theorem card_seeds (m : ℕ) : Fintype.card (Seeds m) = m ^ 3 := by
  simp [Seeds, pow_succ, Nat.mul_assoc]

@[simp] theorem mix_val {a b : ℕ} (z u : Fin (a * b)) :
    (mix z u).val = u.val % b + b * (z.val / b) := rfl

/-- The two coordinates of a depth-i level class multiply to the leaf count. -/
theorem level_factor {h i : ℕ} (hi : i ≤ h) :
    2 ^ i * 2 ^ (h-i) = 2 ^ h := by
  rw [← pow_add, Nat.add_sub_of_le hi]

/-- Transport the mixer to a size presented by an equality rather than a product. -/
def mixCast {a b m : ℕ} (hm : a * b = m) (z u : Fin m) : Fin m :=
  Fin.cast hm (mix (Fin.cast hm.symm z) (Fin.cast hm.symm u))

@[simp] theorem card_mixCast_row_fiber {a b m : ℕ} (hm : a*b=m) (x y : Fin m) :
    Fintype.card {s : Seeds m // (mixCast hm s.1 s.2.1, s.2.2) = (x,y)} = m := by
  subst m
  exact card_row_fiber x y

@[simp] theorem card_mixCast_column_fiber {a b m : ℕ} (hm : a*b=m) (x y : Fin m) :
    Fintype.card {s : Seeds m // (s.2.1, mixCast hm s.1 s.2.2) = (x,y)} = m := by
  subst m
  exact card_column_fiber x y

/-- The class-coordinate selected at depth i by a common leaf and an axis seed. -/
def atLevel (h i : ℕ) (hi : i ≤ h) (z u : Fin (2 ^ h)) : Fin (2 ^ h) :=
  mixCast (level_factor hi) z u

@[simp] theorem atLevel_val (h i : ℕ) (hi : i ≤ h) (z u : Fin (2 ^ h)) :
    (atLevel h i hi z u).val =
      u.val % (2 ^ (h-i)) + (2 ^ (h-i)) * (z.val / (2 ^ (h-i))) := rfl

/-- Root selections depend only on the corresponding axis seed. -/
@[simp] theorem atLevel_root (h : ℕ) (z u : Fin (2 ^ h)) :
    atLevel h 0 (Nat.zero_le h) z u = u := by
  apply Fin.ext
  simp [Nat.mod_eq_of_lt u.isLt, Nat.div_eq_of_lt z.isLt]

/-- Both signs at the leaf select the same common leaf, regardless of axis seed. -/
@[simp] theorem atLevel_leaf (h : ℕ) (z u : Fin (2 ^ h)) :
    atLevel h h le_rfl z u = z := by
  apply Fin.ext
  simp [Nat.mod_one]

/-- Every selected position lies in the ancestor block of the common leaf. -/
theorem atLevel_node (h i : ℕ) (hi : i ≤ h) (z u : Fin (2 ^ h)) :
    (atLevel h i hi z u).val / (2 ^ (h-i)) = z.val / (2 ^ (h-i)) := by
  rw [atLevel_val, Nat.add_mul_div_left _ _ (by positivity)]
  rw [Nat.div_eq_of_lt (Nat.mod_lt _ (by positivity)), Nat.zero_add]

/-- The sampler's node at a child level has the prescribed parent. -/
theorem ancestor_parent (h i z : ℕ) (hi : i < h) :
    (z / 2 ^ (h - (i+1))) / 2 = z / 2 ^ (h-i) := by
  rw [Nat.div_div_eq_div_mul]
  congr 1
  have he : h-i = (h-(i+1))+1 := by omega
  rw [he, pow_succ]

/-- Every variable-row / anchor-column cell has exactly m seed preimages. -/
theorem card_atLevel_row_fiber (h i : ℕ) (hi : i ≤ h) (x y : Fin (2^h)) :
    Fintype.card {s : Seeds (2^h) //
      (atLevel h i hi s.1 s.2.1, s.2.2) = (x,y)} = 2^h :=
  card_mixCast_row_fiber (level_factor hi) x y

/-- Every anchor-row / variable-column cell has exactly m seed preimages. -/
theorem card_atLevel_column_fiber (h i : ℕ) (hi : i ≤ h) (x y : Fin (2^h)) :
    Fintype.card {s : Seeds (2^h) //
      (s.2.1, atLevel h i hi s.1 s.2.2) = (x,y)} = 2^h :=
  card_mixCast_column_fiber (level_factor hi) x y

end Problem348.TreeSampling

end OAI
end
end

section
section
namespace OAI

/-!
The canonical host projections and protected-cell sampling bridge.
Three seeds give the cellwise sampling bound.
-/

namespace Problem348.Construction.HostSampling

open Problem348.TreeSampling

/-- Anchor and dummy positions use their independent axis seed. -/
def sampleDepth {h : ℕ} : Position h → Option (Fin (h + 1))
  | Sum.inl _ => none
  | Sum.inr (Sum.inl v) => some ⟨depth v, Nat.lt_succ_of_le (depth_le v)⟩
  | Sum.inr (Sum.inr _) => none

/-- The coordinate within the size-`2^h` class of a raw host position. -/
def offset {h : ℕ} : Position h → Fin (2 ^ h)
  | Sum.inl (_, _, x) => x
  | Sum.inr (Sum.inl v) => v.2
  | Sum.inr (Sum.inr x) => x

/-- The selected coordinate in the class containing a given position. -/
def coordinate {h : ℕ} (z u : Fin (2 ^ h)) : Position h → Fin (2 ^ h)
  | Sum.inl _ => u
  | Sum.inr (Sum.inl v) => atLevel h (depth v) (depth_le v) z u
  | Sum.inr (Sum.inr _) => u

/-- Whether both positions of a fixed raw cell are selected. -/
def Selected {h : ℕ} (s : Seeds (2 ^ h)) (r c : Position h) : Prop :=
  (coordinate s.1 s.2.1 r, coordinate s.1 s.2.2 c) = (offset r, offset c)

instance {h : ℕ} (s : Seeds (2 ^ h)) (r c : Position h) :
    Decidable (Selected s r c) := inferInstanceAs (Decidable (_ = _))

/-- Protected cells: at least one anchor/dummy position, or two root positions. -/
def Protected {h : ℕ} (r c : Position h) : Prop :=
  sampleDepth r = none ∨ sampleDepth c = none ∨
    sampleDepth r = some ⟨0, by omega⟩ ∧ sampleDepth c = some ⟨0, by omega⟩

@[simp] theorem protected_anchor_left {h : ℕ} (a : AnchorPosition h)
    (c : Position h) : Protected (Sum.inl a) c := by
  simp [Protected, sampleDepth]

@[simp] theorem protected_anchor_right {h : ℕ} (r : Position h)
    (a : AnchorPosition h) : Protected r (Sum.inl a) := by
  simp [Protected, sampleDepth]

@[simp] theorem protected_dummy_left {h : ℕ} (x : Fin (2 ^ h))
    (c : Position h) : Protected (Sum.inr (Sum.inr x)) c := by
  simp [Protected, sampleDepth]

@[simp] theorem protected_dummy_right {h : ℕ} (r : Position h)
    (x : Fin (2 ^ h)) : Protected r (Sum.inr (Sum.inr x)) := by
  simp [Protected, sampleDepth]

 theorem protected_roots {h : ℕ} (v w : VariablePosition h)
    (hv : depth v = 0) (hw : depth w = 0) :
    Protected (Sum.inr (Sum.inl v)) (Sum.inr (Sum.inl w)) := by
  simp [Protected, sampleDepth, hv, hw]

/-- Concrete host protected-cell events all have exactly `2^h` seed preimages. -/
theorem selected_fiber_card {h : ℕ} (r c : Position h) (hp : Protected r c) :
    Fintype.card {s : Seeds (2 ^ h) // Selected s r c} = 2 ^ h := by
  rcases r with ⟨t, u, x⟩ | (v | x) <;>
    rcases c with ⟨t', u', y⟩ | (w | y)
  · exact card_both_fiber x y
  · exact card_atLevel_column_fiber h (depth w) (depth_le w) x w.2
  · exact card_both_fiber x y
  · exact card_atLevel_row_fiber h (depth v) (depth_le v) v.2 y
  · have hd : depth v = 0 ∧ depth w = 0 := by
      simpa [Protected, sampleDepth, Fin.ext_iff] using hp
    have he : ∀ s : Seeds (2 ^ h), Selected s (Sum.inr (Sum.inl v))
        (Sum.inr (Sum.inl w)) ↔ s.2 = (v.2, w.2) := by
      intro s
      simp [Selected, coordinate, offset, hd.1, hd.2]
    calc
      _ = Fintype.card {s : Seeds (2 ^ h) // s.2 = (v.2, w.2)} :=
        Fintype.card_congr (Equiv.subtypeEquivRight he)
      _ = _ := card_both_fiber v.2 w.2
  · exact card_atLevel_row_fiber h (depth v) (depth_le v) v.2 y
  · exact card_both_fiber x y
  · exact card_atLevel_column_fiber h (depth w) (depth_le w) x w.2
  · exact card_both_fiber x y

/-- Fraction-free marginal equality, directly consumable by finite avoidance. -/
theorem selected_fiber_card_mul {h : ℕ} (r c : Position h) (hp : Protected r c) :
    Fintype.card {s : Seeds (2 ^ h) // Selected s r c} * (2 ^ h) ^ 2 =
      Fintype.card (Seeds (2 ^ h)) := by
  rw [selected_fiber_card r c hp, card_seeds]
  ring

/-- The same marginal in the `Finset.filter` form used by the union bound. -/
theorem selected_filter_card {h : ℕ} (r c : Position h) (hp : Protected r c) :
    (Finset.univ.filter fun s : Seeds (2 ^ h) => Selected s r c).card = 2 ^ h := by
  simpa only [Fintype.card_subtype] using selected_fiber_card r c hp

/-- A subset of the protected event has at most the same frequency. -/
theorem protected_event_card_le {h : ℕ} (r c : Position h)
    (event : Finset (Seeds (2 ^ h)))
    (hevent : ∀ s ∈ event, Protected r c ∧ Selected s r c) :
    event.card ≤ 2 ^ h := by
  classical
  rcases event.eq_empty_or_nonempty with hempty | ⟨s, hs⟩
  · simp [hempty]
  · have hp := (hevent s hs).1
    calc
      event.card ≤ (Finset.univ.filter fun s => Selected s r c).card := by
        apply Finset.card_le_card
        intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (hevent t ht).2
      _ = _ := selected_filter_card r c hp

/-- Guard-cell containment in the protected selected-cell event implies
the union-bound frequency estimate for each fixed raw cell. -/
theorem guard_frequency {h : ℕ}
    (guards : Seeds (2 ^ h) → Finset (Position h × Position h))
    (hguards : ∀ s rc, rc ∈ guards s →
      Protected rc.1 rc.2 ∧ Selected s rc.1 rc.2)
    (rc : Position h × Position h) :
    (Finset.univ.filter fun s => rc ∈ guards s).card * (2 ^ h) ^ 2 ≤
      Fintype.card (Seeds (2 ^ h)) := by
  classical
  have hb := protected_event_card_le rc.1 rc.2
    (Finset.univ.filter fun s => rc ∈ guards s)
    (fun s hs => hguards s rc (Finset.mem_filter.mp hs).2)
  rw [card_seeds]
  calc
    _ ≤ 2 ^ h * (2 ^ h) ^ 2 := Nat.mul_le_mul_right _ hb
    _ = (2 ^ h) ^ 3 := by ring

/-- Independent row and column reindexings preserve the protected-cell bound. -/
theorem transported_guard_frequency {h n : ℕ}
    (row col : Position h ≃ Fin n)
    (guards : Seeds (2 ^ h) → Finset (Fin n × Fin n))
    (hguards : ∀ s rc, rc ∈ guards s →
      Protected (row.symm rc.1) (col.symm rc.2) ∧
      Selected s (row.symm rc.1) (col.symm rc.2))
    (rc : Fin n × Fin n) :
    (Finset.univ.filter fun s => rc ∈ guards s).card * (2 ^ h) ^ 2 ≤
      Fintype.card (Seeds (2 ^ h)) := by
  classical
  have hb := protected_event_card_le (row.symm rc.1) (col.symm rc.2)
    (Finset.univ.filter fun s => rc ∈ guards s)
    (fun s hs => hguards s rc (Finset.mem_filter.mp hs).2)
  rw [card_seeds]
  calc
    _ ≤ 2 ^ h * (2 ^ h) ^ 2 := Nat.mul_le_mul_right _ hb
    _ = (2 ^ h) ^ 3 := by ring

end Problem348.Construction.HostSampling

end OAI
end
end

section
section
namespace OAI

/-!
Containment of guarded-path cells in the protected sampling set.
The geometric validity of a selection and the cellwise counting bound
are separate requirements.
-/

namespace Problem348.Construction.HostSampling

open Problem348.TreeSampling Problem348.GuardedPath

variable {h n : ℕ}

/-- A selected row after the independent row reindexing. -/
def RowChosen (row : Position h ≃ Fin n) (s : Seeds (2 ^ h)) (r : Fin n) : Prop :=
  coordinate s.1 s.2.1 (row.symm r) = offset (row.symm r)

/-- A selected column after the independent column reindexing. -/
def ColChosen (col : Position h ≃ Fin n) (s : Seeds (2 ^ h)) (c : Fin n) : Prop :=
  coordinate s.1 s.2.2 (col.symm c) = offset (col.symm c)

/-- The exact cell predicate needed by `transported_guard_frequency`. -/
def GoodCell (row col : Position h ≃ Fin n) (s : Seeds (2 ^ h))
    (rc : Fin n × Fin n) : Prop :=
  Protected (row.symm rc.1) (col.symm rc.2) ∧
    Selected s (row.symm rc.1) (col.symm rc.2)

 theorem goodCell_of_chosen {row col : Position h ≃ Fin n} {s : Seeds (2 ^ h)}
    {r c : Fin n} (hp : Protected (row.symm r) (col.symm c))
    (hr : RowChosen row s r) (hc : ColChosen col s c) :
    GoodCell row col s (r, c) :=
  ⟨hp, Prod.ext hr hc⟩

/-- A selected anchor frame, considered only as a family of protected positions. -/
structure FrameChosen (row col : Position h ≃ Fin n) (s : Seeds (2 ^ h))
    (F : AnchorFrame n) : Prop where
  row_independent : ∀ u, sampleDepth (row.symm (F.rows.val u)) = none
  col_independent : ∀ v, sampleDepth (col.symm (F.cols.val v)) = none
  row_chosen : ∀ u, RowChosen row s (F.rows.val u)
  col_chosen : ∀ v, ColChosen col s (F.cols.val v)

/-- All anchor and signature cells of a chosen frame are protected and selected. -/
theorem FrameChosen.cell_good {row col : Position h ≃ Fin n} {s : Seeds (2 ^ h)}
    {F : AnchorFrame n} (hF : FrameChosen row col s F)
    {r₀ r₁ c₀ c₁ : Fin n}
    (hr₀ : RowChosen row s r₀) (hr₁ : RowChosen row s r₁)
    (hc₀ : ColChosen col s c₀) (hc₁ : ColChosen col s c₁)
    {rc : Fin n × Fin n} (hcell : F.Cell r₀ r₁ c₀ c₁ rc) :
    GoodCell row col s rc := by
  rcases hcell with ⟨u, v, rfl⟩ | ⟨v, rfl | rfl⟩ | ⟨u, rfl | rfl⟩
  · exact goodCell_of_chosen (Or.inl (hF.row_independent u))
      (hF.row_chosen u) (hF.col_chosen v)
  · exact goodCell_of_chosen (Or.inr (Or.inl (hF.col_independent v)))
      hr₀ (hF.col_chosen v)
  · exact goodCell_of_chosen (Or.inr (Or.inl (hF.col_independent v)))
      hr₁ (hF.col_chosen v)
  · exact goodCell_of_chosen (Or.inl (hF.row_independent u))
      (hF.row_chosen u) hc₀
  · exact goodCell_of_chosen (Or.inl (hF.row_independent u))
      (hF.row_chosen u) hc₁

/-- Purely geometric sampling facts, separate from the host's matrix values. -/
structure PathChosen (row col : Position h ≃ Fin n) (s : Seeds (2 ^ h))
    (P : Selection n) : Prop where
  xp_chosen : ∀ i, i ≤ h → RowChosen row s (P.xp i)
  xm_chosen : ∀ i, i ≤ h → RowChosen row s (P.xm i)
  yp_chosen : ∀ i, i ≤ h → ColChosen col s (P.yp i)
  ym_chosen : ∀ i, i ≤ h → ColChosen col s (P.ym i)
  xd_chosen : RowChosen row s P.xd
  yd_chosen : ColChosen col s P.yd
  xd_independent : sampleDepth (row.symm P.xd) = none
  yd_independent : sampleDepth (col.symm P.yd) = none
  root_plus : Protected (row.symm (P.xp 0)) (col.symm (P.yp 0))
  root_minus : Protected (row.symm (P.xm 0)) (col.symm (P.ym 0))
  vertical_plus : ∀ i, i < h → FrameChosen row col s (P.vPlus i)
  vertical_minus : ∀ i, i < h → FrameChosen row col s (P.vMinus i)
  horizontal_plus : ∀ i, i < h → FrameChosen row col s (P.wPlus i)
  horizontal_minus : ∀ i, i < h → FrameChosen row col s (P.wMinus i)

 theorem PathChosen.core_good {row col : Position h ≃ Fin n} {s : Seeds (2 ^ h)}
    {P : Selection n} (hP : PathChosen row col s P)
    {rc : Fin n × Fin n} (hc : P.CoreCell h rc) : GoodCell row col s rc := by
  rcases hc with rfl | rfl | ⟨i, hi, rfl | rfl | rfl | rfl⟩
  · exact goodCell_of_chosen hP.root_plus
      (hP.xp_chosen 0 (Nat.zero_le _)) (hP.yp_chosen 0 (Nat.zero_le _))
  · exact goodCell_of_chosen hP.root_minus
      (hP.xm_chosen 0 (Nat.zero_le _)) (hP.ym_chosen 0 (Nat.zero_le _))
  · exact goodCell_of_chosen (Or.inr (Or.inl hP.yd_independent))
      (hP.xp_chosen i hi) hP.yd_chosen
  · exact goodCell_of_chosen (Or.inr (Or.inl hP.yd_independent))
      (hP.xm_chosen i hi) hP.yd_chosen
  · exact goodCell_of_chosen (Or.inl hP.xd_independent)
      hP.xd_chosen (hP.yp_chosen i hi)
  · exact goodCell_of_chosen (Or.inl hP.xd_independent)
      hP.xd_chosen (hP.ym_chosen i hi)

 theorem PathChosen.edge_good {row col : Position h ≃ Fin n} {s : Seeds (2 ^ h)}
    {P : Selection n} (hP : PathChosen row col s P) {i : ℕ} (hi : i < h)
    {rc : Fin n × Fin n} (hc : P.EdgeCell i rc) : GoodCell row col s rc := by
  have hil : i ≤ h := Nat.le_of_lt hi
  have his : i + 1 ≤ h := hi
  rcases hc with hc | hc | hc | hc
  · exact (hP.vertical_plus i hi).cell_good
      (hP.xp_chosen (i + 1) his) (hP.xp_chosen i hil)
      hP.yd_chosen (hP.yp_chosen i hil) hc
  · exact (hP.vertical_minus i hi).cell_good
      (hP.xm_chosen i hil) (hP.xm_chosen (i + 1) his)
      hP.yd_chosen (hP.ym_chosen i hil) hc
  · exact (hP.horizontal_plus i hi).cell_good
      (hP.xp_chosen (i + 1) his) hP.xd_chosen
      (hP.yp_chosen i hil) (hP.yp_chosen (i + 1) his) hc
  · exact (hP.horizontal_minus i hi).cell_good
      (hP.xm_chosen (i + 1) his) hP.xd_chosen
      (hP.ym_chosen (i + 1) his) (hP.ym_chosen i hil) hc

/-- Every actual guarded-path cell is in the protected selected-cell event. -/
theorem PathChosen.guard_good {row col : Position h ≃ Fin n} {s : Seeds (2 ^ h)}
    {P : Selection n} (hP : PathChosen row col s P)
    {rc : Fin n × Fin n} (hc : rc ∈ P.guards h) : GoodCell row col s rc := by
  rw [Selection.mem_guards] at hc
  rcases hc with hc | ⟨i, hi, hc⟩
  · exact hP.core_good hc
  · exact hP.edge_good hi hc

/-- The frequency bound for any concretely chosen family of paths. -/
theorem path_guard_frequency (row col : Position h ≃ Fin n)
    (P : Seeds (2 ^ h) → Selection n)
    (hP : ∀ s, PathChosen row col s (P s)) (rc : Fin n × Fin n) :
    (Finset.univ.filter fun s => rc ∈ (P s).guards h).card * (2 ^ h) ^ 2 ≤
      Fintype.card (Seeds (2 ^ h)) := by
  classical
  exact transported_guard_frequency row col (fun s => (P s).guards h)
    (fun s _ hc => (hP s).guard_good hc) rc

end Problem348.Construction.HostSampling

end OAI
end
end

section
section
namespace OAI

/-!
# Compatibility of the path sampler and protected-cell sampler

The quotient/remainder formula and `finProdFinEquiv` select the same
coordinate, identifying path samples with the uniform-fiber sampler.
-/

namespace Problem348.TreeSampling

/-- The equivalence-based and arithmetic mixers select identical coordinates. -/
theorem atLevel_eq_mixFin (h i : ℕ) (hi : i ≤ h) (z u : Fin (2 ^ h)) :
    atLevel h i hi z u = SampledPath.mixFin h i hi z u := by
  apply Fin.ext
  change u.val % (2 ^ (h - i)) + (2 ^ (h - i)) * (z.val / (2 ^ (h - i))) =
    z.val / (2 ^ (h - i)) * (2 ^ (h - i)) + u.val % (2 ^ (h - i))
  ac_rfl

end Problem348.TreeSampling

namespace Problem348.Construction.HostSampling

/-- An actual sampled variable path point is selected by the marginal sampler. -/
theorem coordinate_path_position (h i : ℕ) (hi : i ≤ h) (sign : Bool)
    (z u : Fin (2 ^ h)) :
    coordinate z u (HostSampledPath.position h i hi sign z u) =
      offset (HostSampledPath.position h i hi sign z u) := by
  change TreeSampling.atLevel h (depth (SampledPath.sample h i hi sign z u))
    (depth_le _) z u =
    (SampledPath.sample h i hi sign z u).2
  have hd : depth (SampledPath.sample h i hi sign z u) = i :=
    (HostSampledPath.sample_atLevel h i hi sign z u).1
  simp only [hd]
  exact TreeSampling.atLevel_eq_mixFin h i hi z u

/-- Anchor representatives use the corresponding independent axis seed. -/
@[simp] theorem coordinate_anchor (h : ℕ) (t : Mode h) (v : Fin 64)
    (z u : Fin (2 ^ h)) :
    coordinate z u (Sum.inl (t, v, u)) = offset (Sum.inl (t, v, u)) := rfl

/-- The selected dummy position uses the same independent axis seed. -/
@[simp] theorem coordinate_path_dummy (h : ℕ) (z u : Fin (2 ^ h)) :
    coordinate z u (HostSampledPath.dummy h u) =
      offset (HostSampledPath.dummy h u) := rfl

/-- Every pair of path samples, not just the protected pairs, is selected.
The two axes use different offset seeds but the same leaf seed. -/
theorem selected_path_positions (h i j : ℕ) (hi : i ≤ h) (hj : j ≤ h)
    (s t : Bool) (z u v : Fin (2 ^ h)) :
    Selected (z, u, v) (HostSampledPath.position h i hi s z u)
      (HostSampledPath.position h j hj t z v) := by
  exact Prod.ext (coordinate_path_position h i hi s z u)
    (coordinate_path_position h j hj t z v)

/-- A path-row / selected-anchor-column pair is a selected protected cell. -/
theorem protected_selected_path_anchor (h i : ℕ) (hi : i ≤ h) (sign : Bool)
    (t : Mode h) (a : Fin 64) (z u v : Fin (2 ^ h)) :
    Protected (HostSampledPath.position h i hi sign z u) (Sum.inl (t, a, v)) ∧
      Selected (z, u, v) (HostSampledPath.position h i hi sign z u)
        (Sum.inl (t, a, v)) := by
  exact ⟨protected_anchor_right _ _,
    Prod.ext (coordinate_path_position h i hi sign z u) rfl⟩

/-- A selected-anchor-row / path-column pair is a selected protected cell. -/
theorem protected_selected_anchor_path (h i : ℕ) (hi : i ≤ h) (sign : Bool)
    (t : Mode h) (a : Fin 64) (z u v : Fin (2 ^ h)) :
    Protected (Sum.inl (t, a, u)) (HostSampledPath.position h i hi sign z v) ∧
      Selected (z, u, v) (Sum.inl (t, a, u))
        (HostSampledPath.position h i hi sign z v) := by
  exact ⟨protected_anchor_left _ _,
    Prod.ext rfl (coordinate_path_position h i hi sign z v)⟩

/-- Direct row-field adapter for the geometric guarded-path certificate. -/
theorem rowChosen_path {h n : ℕ} (er : Position h ≃ Fin n)
    (i : ℕ) (hi : i ≤ h) (sign : Bool) (s : TreeSampling.Seeds (2 ^ h)) :
    RowChosen er s (er (HostSampledPath.position h i hi sign s.1 s.2.1)) := by
  simp only [RowChosen, Equiv.symm_apply_apply]
  exact coordinate_path_position h i hi sign s.1 s.2.1

/-- Direct column-field adapter for the geometric guarded-path certificate. -/
theorem colChosen_path {h n : ℕ} (ec : Position h ≃ Fin n)
    (i : ℕ) (hi : i ≤ h) (sign : Bool) (s : TreeSampling.Seeds (2 ^ h)) :
    ColChosen ec s (ec (HostSampledPath.position h i hi sign s.1 s.2.2)) := by
  simp only [ColChosen, Equiv.symm_apply_apply]
  exact coordinate_path_position h i hi sign s.1 s.2.2

@[simp] theorem rowChosen_path_dummy {h n : ℕ} (er : Position h ≃ Fin n)
    (s : TreeSampling.Seeds (2 ^ h)) :
    RowChosen er s (er (HostSampledPath.dummy h s.2.1)) := by
  simp only [RowChosen, Equiv.symm_apply_apply]
  rfl

@[simp] theorem colChosen_path_dummy {h n : ℕ} (ec : Position h ≃ Fin n)
    (s : TreeSampling.Seeds (2 ^ h)) :
    ColChosen ec s (ec (HostSampledPath.dummy h s.2.2)) := by
  simp only [ColChosen, Equiv.symm_apply_apply]
  rfl

@[simp] theorem rowChosen_path_anchor {h n : ℕ} (er : Position h ≃ Fin n)
    (s : TreeSampling.Seeds (2 ^ h)) (t : Mode h) (a : Fin 64) :
    RowChosen er s (er (Sum.inl (t, a, s.2.1))) := by
  simp only [RowChosen, Equiv.symm_apply_apply]
  rfl

@[simp] theorem colChosen_path_anchor {h n : ℕ} (ec : Position h ≃ Fin n)
    (s : TreeSampling.Seeds (2 ^ h)) (t : Mode h) (a : Fin 64) :
    ColChosen ec s (ec (Sum.inl (t, a, s.2.2))) := by
  simp only [ColChosen, Equiv.symm_apply_apply]
  rfl

/-- Both sampled roots belong to protected classes, regardless of sign. -/
theorem protected_path_roots (h : ℕ) (s t : Bool) (z u v : Fin (2 ^ h)) :
    Protected (HostSampledPath.position h 0 (Nat.zero_le h) s z u)
      (HostSampledPath.position h 0 (Nat.zero_le h) t z v) := by
  apply protected_roots
  · exact (HostSampledPath.sample_atLevel h 0 (Nat.zero_le h) s z u).1
  · exact (HostSampledPath.sample_atLevel h 0 (Nat.zero_le h) t z v).1

end Problem348.Construction.HostSampling

end OAI
end
end

section
section
namespace OAI

/-!
# Arbitrary-repair lower bound for the actual canonical host

The concrete common-leaf selection satisfies both independent certificates:
its guarded path is valid, and its chosen coordinates bound each guard cell's
sampling multiplicity.
Together these prove the integer repair lower bound. No assumption
about preservation of arbitrary variable-variable cells is made.
-/

noncomputable section
namespace Problem348.Construction.SampledSelection

open HostSampledPath HostSampling TreeSampling

/-- The actual constant-offset anchor frame is chosen by its row/column seeds. -/
theorem frame_chosen {h n : ℕ} (er ec : Position h ≃ Fin n)
    (ha : AxisConditions er ec) (s : Seeds (2 ^ h)) (t : Mode h) :
    FrameChosen er ec s (frame er ec ha t s.2.1 s.2.2) := by
  constructor
  · intro u
    simp [frame, SelectedAnchor.frame, sampleDepth]
  · intro v
    simp [frame, SelectedAnchor.frame, sampleDepth]
  · intro u
    exact rowChosen_path_anchor er s t u
  · intro v
    exact colChosen_path_anchor ec s t v

/-- Every actual path point and anchor frame obeys the uniform sampler's
coordinate equations. This is separate from all matrix-entry claims. -/
theorem selection_chosen {h n : ℕ} (hh : 1 ≤ h) (er ec : Position h ≃ Fin n)
    (ha : AxisConditions er ec) (s : Seeds (2 ^ h)) :
    PathChosen er ec s (selection hh er ec ha s.1 s.2.1 s.2.2) := by
  constructor
  · intro i hi
    simpa only [selection, path_of_le hi] using rowChosen_path er i hi true s
  · intro i hi
    simpa only [selection, path_of_le hi] using rowChosen_path er i hi false s
  · intro i hi
    simpa only [selection, path_of_le hi] using colChosen_path ec i hi true s
  · intro i hi
    simpa only [selection, path_of_le hi] using colChosen_path ec i hi false s
  · exact rowChosen_path_dummy er s
  · exact colChosen_path_dummy ec s
  · simp [selection, HostSampledPath.dummy, sampleDepth]
  · simp [selection, HostSampledPath.dummy, sampleDepth]
  · simpa only [selection, Equiv.symm_apply_apply, path_of_le (Nat.zero_le h)] using
      protected_path_roots h true true s.1 s.2.1 s.2.2
  · simpa only [selection, Equiv.symm_apply_apply, path_of_le (Nat.zero_le h)] using
      protected_path_roots h false false s.1 s.2.1 s.2.2
  · intro i hi
    exact frame_chosen er ec ha s _
  · intro i hi
    exact frame_chosen er ec ha s _
  · intro i hi
    exact frame_chosen er ec ha s _
  · intro i hi
    exact frame_chosen er ec ha s _

/-- Each fixed guarded cell occupies at most the prescribed `1/m²` fraction
of the three-seed sample space, for the actual selected paths. -/
theorem selection_guard_frequency {h n : ℕ} (hh : 1 ≤ h)
    (er ec : Position h ≃ Fin n) (ha : AxisConditions er ec)
    (rc : Fin n × Fin n) :
    (Finset.univ.filter fun s : Seeds (2 ^ h) =>
      rc ∈ (selection hh er ec ha s.1 s.2.1 s.2.2).guards h).card * (2 ^ h) ^ 2 ≤
        Fintype.card (Seeds (2 ^ h)) :=
  path_guard_frequency er ec
    (fun s => selection hh er ec ha s.1 s.2.1 s.2.2)
    (fun s => selection_chosen hh er ec ha s) rc

/-- The arbitrary-repair lower bound for the literal canonical host.
The independent axis enumerations satisfy `AxisConditions`: increasing anchor
groups precede all nonanchors, variable rows precede dummy rows, dummy columns
precede variable columns, and sampled parent/child pairs obey the four signed
tree-order inequalities. No entry-preservation condition is imposed on repairs. -/
theorem hammingDistance_ge {h n : ℕ} (hh : 1 ≤ h)
    (er ec : Position h ≃ Fin n) (ha : AxisConditions er ec)
    (B : BinaryMatrix n) (hfree : HFree fixedH B) :
    (2 ^ h) ^ 2 ≤ hammingDistance (SelectedAnchor.matrix er ec) B := by
  classical
  apply Sampling.hammingDistance_ge_of_guard_sampling fixedH
    (SelectedAnchor.matrix er ec) B
    (fun s : Seeds (2 ^ h) => (selection hh er ec ha s.1 s.2.1 s.2.2).guards h)
    (2 ^ h)
  · rw [card_seeds]
    positivity
  · exact selection_guard_frequency hh er ec ha
  · intro s hag
    exact GuardedPath.Selection.not_HFree_of_agree
      (selection_valid hh er ec ha s.1 s.2.1 s.2.2) hag
  · exact hfree

end Problem348.Construction.SampledSelection

end

end OAI
end
end

section
section
namespace OAI

/-!
# Unconditional repair lower bound for the ordered canonical host

The sampler order certificate follows from the independent increasing
row and column enumerations, giving the arbitrary-repair lower bound.
-/

noncomputable section
namespace Problem348.OrderedHost

open Construction

/-- Every fixedH-free repair of the actual ordered host changes at least m²
cells. In particular no pinning premise or preservation condition is assumed. -/
theorem hammingDistance_ge {h : ℕ} (hh : 1 ≤ h)
    (B : BinaryMatrix (size h)) (hfree : HFree fixedH B) :
    (2 ^ h) ^ 2 ≤
      hammingDistance (SelectedAnchor.matrix (rowIndex h) (columnIndex h)) B :=
  SampledSelection.hammingDistance_ge hh (rowIndex h) (columnIndex h)
    (sampledAxisConditions h) B hfree

/-- The concrete three-seed sampler has the exact uniform guard bound. -/
theorem sampledSelection_guard_frequency {h : ℕ} (hh : 1 ≤ h)
    (rc : Fin (size h) × Fin (size h)) :
    (Finset.univ.filter fun s : TreeSampling.Seeds (2 ^ h) =>
      rc ∈ (sampledSelection hh s.1 s.2.1 s.2.2).guards h).card * (2 ^ h) ^ 2 ≤
        Fintype.card (TreeSampling.Seeds (2 ^ h)) :=
  SampledSelection.selection_guard_frequency hh (rowIndex h) (columnIndex h)
    (sampledAxisConditions h) rc

end Problem348.OrderedHost

end

end OAI
end
end

section
section
namespace OAI

/-!
Assembly of the counterexample sequence from two integer bounds.
The existence of a host satisfying both bounds is an explicit hypothesis.
-/

noncomputable section

namespace Problem348.SequenceAssembly

/-- Integer certificates for one candidate host. This does not assert existence. -/
def HostBounds {n : ℕ} (A : BinaryMatrix n) (m : ℕ) : Prop :=
  (∀ B : BinaryMatrix n, HFree fixedH B → m ^ 2 ≤ hammingDistance A B) ∧
    copyCount fixedH A ≤ m * n ^ 130

/-- The sentinel value in `fixedMinEdits` respects every lower bound at most n². -/
theorem fixedMinEdits_ge_of_repairs {n q : ℕ} (A : BinaryMatrix n)
    (hq : q ≤ n * n)
    (hrep : ∀ B : BinaryMatrix n, HFree fixedH B → q ≤ hammingDistance A B) :
    q ≤ fixedMinEdits A := by
  classical
  unfold fixedMinEdits
  apply Finset.le_min'
  intro k hk
  obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp hk
  split_ifs with hB
  · exact hrep B hB
  · omega

/-- Normalize an arbitrary-repair certificate at order n=d*m. -/
theorem fixedDistance_ge_of_integer_bound {d m : ℕ}
    (hd : 0 < d) (hm : 0 < m) (A : BinaryMatrix (d * m))
    (hrep : ∀ B : BinaryMatrix (d * m), HFree fixedH B →
      m ^ 2 ≤ hammingDistance A B) :
    1 / ((d : ℝ) ^ 2) ≤ fixedDistance A := by
  have hmn : m ≤ d * m := by nlinarith
  have hq : m ^ 2 ≤ (d * m) * (d * m) := by nlinarith
  have hmin := fixedMinEdits_ge_of_repairs A hq hrep
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hminR : (m : ℝ) ^ 2 ≤ (fixedMinEdits A : ℝ) := by exact_mod_cast hmin
  unfold fixedDistance
  push_cast
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < ((d : ℝ) * m) ^ 2)).2
  calc
    1 / ((d : ℝ) ^ 2) * ((d : ℝ) * m) ^ 2 = (m : ℝ) ^ 2 := by
      field_simp
    _ ≤ (fixedMinEdits A : ℝ) := hminR

/-- Normalize the localized-copy integer estimate at order n=d*m. -/
theorem copyDensity_le_of_integer_bound {d m : ℕ}
    (hd : 0 < d) (hm : 0 < m) (A : BinaryMatrix (d * m))
    (hcount : copyCount fixedH A ≤ m * (d * m) ^ 130) :
    (copyCount fixedH A : ℝ) / (((d * m : ℕ) : ℝ) ^ 132) ≤
      (1 / ((d : ℝ) ^ 2)) * (1 / (m : ℝ)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hcountR : (copyCount fixedH A : ℝ) ≤
      (m : ℝ) * ((d : ℝ) * m) ^ 130 := by exact_mod_cast hcount
  push_cast
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((d : ℝ) * m) ^ 132)).2
  calc
    (copyCount fixedH A : ℝ) ≤ (m : ℝ) * ((d : ℝ) * m) ^ 130 := hcountR
    _ = (1 / ((d : ℝ) ^ 2)) * (1 / (m : ℝ)) * ((d : ℝ) * m) ^ 132 := by
      field_simp

/-- The counterexample sequence follows from the integer bounds. -/
theorem counterexample_sequence_of_integer_bounds
    (hcert : ∀ h : ℕ, 1 ≤ h →
      let d : ℕ := 386 * h + 2
      let n : ℕ := d * 2 ^ h
      ∃ A : BinaryMatrix n, HostBounds A (2 ^ h)) :
    ∀ h : ℕ, 1 ≤ h →
      let d : ℕ := 386 * h + 2
      let n : ℕ := d * 2 ^ h
      ∃ A : BinaryMatrix n,
        fixedDistance A ≥ 1 / ((d : ℝ) ^ 2) ∧
        (copyCount fixedH A : ℝ) / ((n : ℝ) ^ 132) ≤
          (1 / ((d : ℝ) ^ 2)) * (1 / ((2 : ℝ) ^ h)) := by
  intro h hh
  obtain ⟨A, hrep, hcount⟩ := hcert h hh
  refine ⟨A, fixedDistance_ge_of_integer_bound (by omega)
    (pow_pos (by decide) _) A hrep, ?_⟩
  simpa using copyDensity_le_of_integer_bound (by omega)
    (pow_pos (by decide) _) A hcount

end Problem348.SequenceAssembly

end

end OAI
end
end

section
section
namespace OAI

/-!
Analytic conclusion of the ordered-matrix construction.
The polynomial/geometric comparison uses
`tendsto_pow_const_div_const_pow_of_one_lt`.
-/

noncomputable section

namespace Problem348

open Filter
open scoped Topology


/-- Exponential decay beats the inverse-polynomial distance parameter. -/
theorem exists_depth_polynomial_decay (c C : ℝ) (hc : 0 < c) :
    ∃ h : ℕ, 1 ≤ h ∧
      (1 / ((386 * (h : ℝ) + 2) ^ 2)) * (1 / ((2 : ℝ) ^ h)) <
        c * Real.rpow (1 / ((386 * (h : ℝ) + 2) ^ 2)) C := by
  obtain ⟨k, hk⟩ := exists_nat_ge C
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt (2 * k)
    (by norm_num : (1 : ℝ) < 2)).const_mul ((388 : ℝ) ^ (2 * k))
  have hev : ∀ᶠ h : ℕ in atTop,
      (388 : ℝ) ^ (2 * k) * ((h : ℝ) ^ (2 * k) / (2 : ℝ) ^ h) < c := by
    exact ht.eventually (gt_mem_nhds (by simpa using hc))
  obtain ⟨h, hh, hsmall⟩ := (eventually_ge_atTop 1 |>.and hev).exists
  refine ⟨h, hh, ?_⟩
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hd : 0 < 386 * (h : ℝ) + 2 := by positivity
  have hd1 : (1 : ℝ) < 386 * (h : ℝ) + 2 := by linarith
  have htwo : 0 < (2 : ℝ) ^ h := by positivity
  have hpoly : (386 * (h : ℝ) + 2) ^ (2 * k) ≤
      (388 : ℝ) ^ (2 * k) * (h : ℝ) ^ (2 * k) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hd.le (by linarith) _
  have hratio : (386 * (h : ℝ) + 2) ^ (2 * k) / (2 : ℝ) ^ h < c := by
    calc
      _ ≤ ((388 : ℝ) ^ (2 * k) * (h : ℝ) ^ (2 * k)) / (2 : ℝ) ^ h :=
        div_le_div_of_nonneg_right hpoly htwo.le
      _ = (388 : ℝ) ^ (2 * k) * ((h : ℝ) ^ (2 * k) / (2 : ℝ) ^ h) := by ring
      _ < c := hsmall
  have hepspos : 0 < 1 / ((386 * (h : ℝ) + 2) ^ 2) := by positivity
  have hepsle : 1 / ((386 * (h : ℝ) + 2) ^ 2) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    nlinarith
  have hexponent : (1 / ((386 * (h : ℝ) + 2) ^ 2)) ^ k ≤
      Real.rpow (1 / ((386 * (h : ℝ) + 2) ^ 2)) C := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hepspos hepsle hk
  have hsmall' : 1 / ((2 : ℝ) ^ h) <
      c * (1 / ((386 * (h : ℝ) + 2) ^ 2)) ^ k := by
    rw [div_pow, one_pow, ← pow_mul, mul_one_div]
    apply (lt_div_iff₀ (pow_pos hd (2 * k))).2
    simpa [div_eq_mul_inv, mul_comm] using hratio
  calc
    _ ≤ 1 / ((2 : ℝ) ^ h) := by
      exact mul_le_of_le_one_left (by positivity) hepsle
    _ < c * (1 / ((386 * (h : ℝ) + 2) ^ 2)) ^ k := hsmall'
    _ ≤ c * Real.rpow (1 / ((386 * (h : ℝ) + 2) ^ 2)) C :=
      mul_le_mul_of_nonneg_left hexponent hc.le

end Problem348

end

end OAI
end
end

section
section
namespace OAI

/-!
The sequence of matrix counterexamples rules out every polynomial
removal bound.
-/

noncomputable section

namespace Problem348

/-- Exponential decay of the copy density rules out polynomial removal bounds. -/
theorem no_polynomial_removal_bound_of_sequence
    (hseq : ∀ h : ℕ, 1 ≤ h →
      let d : ℕ := 386 * h + 2
      let n : ℕ := d * 2 ^ h
      ∃ A : BinaryMatrix n,
        fixedDistance A ≥ 1 / ((d : ℝ) ^ 2) ∧
        (copyCount fixedH A : ℝ) / ((n : ℝ) ^ 132) ≤
          (1 / ((d : ℝ) ^ 2)) * (1 / ((2 : ℝ) ^ h))) :
    ∀ c C : ℝ, 0 < c → 0 < C →
      ∃ n : ℕ, 1 ≤ n ∧
        ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
          ∃ A : BinaryMatrix n,
            fixedDistance A ≥ ε ∧
            (copyCount fixedH A : ℝ) <
              c * Real.rpow ε C * ((n : ℝ) ^ 132) := by
  intro c C hc _hC
  obtain ⟨h, hh, hdecay⟩ := exists_depth_polynomial_decay c C hc
  let d : ℕ := 386 * h + 2
  let n : ℕ := d * 2 ^ h
  have hd : 1 < d := by dsimp [d]; omega
  have hdR : (1 : ℝ) < d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hn : 0 < n := Nat.mul_pos (by omega) (pow_pos (by decide) _)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨A, hdist, hcopies⟩ := hseq h hh
  refine ⟨n, hn, 1 / ((d : ℝ) ^ 2), by positivity, ?_, A, hdist, ?_⟩
  · apply (div_lt_one (by positivity)).2
    nlinarith
  · have hdecay' : (1 / ((d : ℝ) ^ 2)) * (1 / ((2 : ℝ) ^ h)) <
        c * Real.rpow (1 / ((d : ℝ) ^ 2)) C := by
      simpa [d] using hdecay
    exact (div_lt_iff₀ (pow_pos hnR 132)).mp (hcopies.trans_lt hdecay')

end Problem348

end

end OAI
end
end

section
section
namespace OAI

noncomputable section
namespace Problem348

theorem counterexample_sequence :
    ∀ h : ℕ, 1 ≤ h →
  let d : ℕ := 386 * h + 2
  let n : ℕ := d * 2 ^ h
  ∃ A : BinaryMatrix n,
    fixedDistance A ≥ 1 / ((d : ℝ) ^ 2) ∧
    (copyCount fixedH A : ℝ) / ((n : ℝ) ^ 132) ≤
      (1 / ((d : ℝ) ^ 2)) * (1 / ((2 : ℝ) ^ h)) := by
  apply SequenceAssembly.counterexample_sequence_of_integer_bounds
  intro h hh
  refine ⟨Construction.hostMatrix (OrderedHost.rowIndex h) (OrderedHost.columnIndex h), ?_,
    OrderedHost.canonical_copyCount_le h⟩
  intro B hfree
  exact OrderedHost.hammingDistance_ge hh B hfree

theorem no_polynomial_removal_bound_oai :
    ∀ c C : ℝ, 0 < c → 0 < C →
  ∃ n : ℕ, 1 ≤ n ∧
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∃ A : BinaryMatrix n,
        fixedDistance A ≥ ε ∧
        (copyCount fixedH A : ℝ) <
          c * Real.rpow ε C * ((n : ℝ) ^ 132) := by
  exact no_polynomial_removal_bound_of_sequence counterexample_sequence

end Problem348

end

end OAI
end
end

theorem solution : type_of% @OAI.Problem348.no_polynomial_removal_bound_oai := @OAI.Problem348.no_polynomial_removal_bound_oai
