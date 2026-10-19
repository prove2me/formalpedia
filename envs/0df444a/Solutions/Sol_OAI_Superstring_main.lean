-- Prove2me | solution 1 for OAI.Superstring.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T16:11:14.644665+00:00
-- url     : https://prove2.me/submissions/3ceb35d3-3db5-4593-bace-bdf646add745

import Mathlib
import Definitions.Def_Superstring

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
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
alias Finset.prod_le_prod₀ := Finset.prod_le_prod
end OAICompat434

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring

end Superstring

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring

namespace Hierarchical

variable {α : Type}


def SubstringClosed (V : Set (List α)) : Prop :=
  ∀ ⦃s⦄, s ∈ V → ∀ ⦃t⦄, t <:+: s → t ∈ V

/-- An explicit hierarchical-graph walk. Up edges append one symbol and down
edges delete the first symbol. Transitivity retains every edge of both walks. -/
inductive Path (V : Set (List α)) : List α → List α → Type
  | nil (s) (hs : s ∈ V) : Path V s s
  | up (s) (a) (hs : s ∈ V) (ht : s ++ [a] ∈ V) : Path V s (s ++ [a])
  | down (a) (s) (hs : a :: s ∈ V) (ht : s ∈ V) : Path V (a :: s) s
  | trans {s t u} : Path V s t → Path V t u → Path V s u

namespace Path

variable {V : Set (List α)} {s t u : List α}

def cost : {s t : List α} → Path V s t → ℕ
  | _, _, .nil _ _ => 0
  | _, _, .up _ _ _ _ => 1
  | _, _, .down _ _ _ _ => 0
  | _, _, .trans P Q => P.cost + Q.cost

/-- Vertices, including both endpoints, with no quotient of the edge data. -/
def Visits (w : List α) : {s t : List α} → Path V s t → Prop
  | _, _, .nil s _ => w = s
  | _, _, .up s a _ _ => w = s ∨ w = s ++ [a]
  | _, _, .down a s _ _ => w = a :: s ∨ w = s
  | _, _, .trans P Q => P.Visits w ∨ Q.Visits w

@[simp] theorem cost_trans (P : Path V s t) (Q : Path V t u) :
    (P.trans Q).cost = P.cost + Q.cost := rfl

@[simp] theorem visits_start (P : Path V s t) : P.Visits s := by
  induction P with
  | nil => rfl
  | up => exact Or.inl rfl
  | down => exact Or.inl rfl
  | trans P Q ih _ => exact Or.inl ih

@[simp] theorem visits_end (P : Path V s t) : P.Visits t := by
  induction P with
  | nil => rfl
  | up => exact Or.inr rfl
  | down => exact Or.inr rfl
  | trans P Q _ ih => exact Or.inr ih

theorem mem_of_visits (P : Path V s t) {w} (h : P.Visits w) : w ∈ V := by
  induction P with
  | nil s hs => exact h ▸ hs
  | up s a hs ht => rcases h with rfl | rfl <;> assumption
  | down a s hs ht => rcases h with rfl | rfl <;> assumption
  | trans P Q ihP ihQ => exact h.elim ihP ihQ

/-- Reindex an explicit walk along equality of its endpoint words. -/
def copy (P : Path V s t) {s' t' : List α} (hs : s = s') (ht : t = t') :
    Path V s' t' := hs ▸ ht ▸ P

@[simp] theorem cost_copy (P : Path V s t) {s' t' : List α}
    (hs : s = s') (ht : t = t') : (P.copy hs ht).cost = P.cost := by
  subst s'; subst t'; rfl

@[simp] theorem visits_copy (P : Path V s t) {s' t' : List α}
    (hs : s = s') (ht : t = t') (w : List α) : (P.copy hs ht).Visits w ↔ P.Visits w := by
  subst s'; subst t'; rfl

/-- Delete an arbitrary prefix, costing zero. -/
def deletePrefix (closed : SubstringClosed V) (a b : List α) (h : a ++ b ∈ V) :
    Path V (a ++ b) b :=
  match a with
  | [] => .nil b h
  | x :: xs =>
    let htail : xs ++ b ∈ V := closed h (List.infix_cons List.infix_rfl)
    (Path.down x (xs ++ b) h htail).trans (deletePrefix closed xs b htail)

@[simp] theorem cost_deletePrefix (closed : SubstringClosed V) (a b : List α)
    (h : a ++ b ∈ V) : (deletePrefix closed a b h).cost = 0 := by
  induction a with
  | nil => rfl
  | cons x xs ih => simpa [deletePrefix, cost] using ih _

/-- Append an arbitrary suffix, staying within prefixes of the final word. -/
def appendSuffix (closed : SubstringClosed V) (a b : List α) (h : a ++ b ∈ V) :
    Path V a (a ++ b) :=
  match b with
  | [] => (Path.nil a (by simpa using h)).copy rfl (by simp)
  | x :: xs =>
    let ha : a ∈ V := closed h List.infix_append_left
    let he : a ++ [x] ∈ V := closed h ⟨[], xs, by simp⟩
    let ht : (a ++ [x]) ++ xs ∈ V := by simpa using h
    ((Path.up a x ha he).trans (appendSuffix closed (a ++ [x]) xs ht)).copy rfl (by simp)

@[simp] theorem cost_appendSuffix (closed : SubstringClosed V) (a b : List α)
    (h : a ++ b ∈ V) : (appendSuffix closed a b h).cost = b.length := by
  induction b generalizing a with
  | nil => simp [appendSuffix, cost]
  | cons x xs ih => simp [appendSuffix, cost, ih, Nat.add_comm]

/-- A path that reads a word one letter at a time, always returning to empty.
This supplies the gap case of ordered windows without adding non-substring words. -/
def readGap (h0 : ([] : List α) ∈ V) (w : List α)
    (h : ∀ a ∈ w, [a] ∈ V) : Path V [] [] :=
  match w with
  | [] => .nil [] h0
  | a :: as =>
    ((Path.up [] a h0 (h a (by simp))).trans
      (Path.down a [] (h a (by simp)) h0)).trans
        (readGap h0 as (fun b hb => h b (by simp [hb])))

@[simp] theorem cost_readGap (h0 : ([] : List α) ∈ V) (w : List α)
    (h : ∀ a ∈ w, [a] ∈ V) : (readGap h0 w h).cost = w.length := by
  induction w with
  | nil => rfl
  | cons a as ih =>
    simp only [readGap, cost]
    rw [ih, List.length_cons]
    omega

end Path

/-- The finite integer window of a two-sided text. -/
def textWord (A : ℤ → α) (a b : ℤ) : List α :=
  List.ofFn (fun i : Fin (b - a).toNat => A (a + (i.val : ℤ)))

@[simp] theorem length_textWord (A : ℤ → α) (a b : ℤ) :
    (textWord A a b).length = (b - a).toNat := by
  simp [textWord]

@[simp] theorem textWord_self (A : ℤ → α) (a : ℤ) : textWord A a a = [] := by
  simp [textWord]

theorem textWord_append (A : ℤ → α) {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    textWord A a b ++ textWord A b c = textWord A a c := by
  apply List.ext_getElem
  · simp only [List.length_append, length_textWord]
    omega
  · intro i hi hj
    by_cases hit : i < (b - a).toNat
    · rw [List.getElem_append_left (by simpa using hit)]
      simp [textWord]
    · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hit)]
      simp only [textWord, List.getElem_ofFn, List.length_ofFn]
      congr 1
      omega

theorem textWord_infix (A : ℤ → α) {a b c d : ℤ}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    textWord A c d <:+: textWord A a b := by
  refine ⟨textWord A a c, textWord A d b, ?_⟩
  rw [textWord_append A hac hcd, textWord_append A (le_trans hac hcd) hdb]

theorem mem_textWord (A : ℤ → α) {a b : ℤ} {c : α} (hc : c ∈ textWord A a b) :
    ∃ i : ℤ, a ≤ i ∧ i < b ∧ A i = c := by
  simp only [textWord, List.mem_ofFn] at hc
  obtain ⟨i, hi⟩ := hc
  refine ⟨a + i.val, ?_, ?_, hi⟩ <;> omega

/-- Translate a window by a period of its text, preserving the graph vertex. -/
theorem textWord_translate (A : ℤ → α) (h : ℤ) (per : ∀ x, A (x + h) = A x)
    (a b : ℤ) : textWord A (a + h) (b + h) = textWord A a b := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [textWord, List.getElem_ofFn]
    rw [show a + h + (i : ℤ) = (a + i) + h by omega, per]


theorem ordered_windows {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V)
    {a b c d : ℤ} (_hab : a ≤ b) (hcd : c ≤ d) (hac : a ≤ c) (hbd : b ≤ d)
    (h₁ : textWord A a b ∈ V) (h₂ : textWord A c d ∈ V) :
    ∃ P : Path V (textWord A a b) (textWord A c d),
      P.cost = (d - b).toNat ∧
      ∃ w, P.Visits w ∧ (w.length : ℤ) ≤ max 0 (b - c) := by
  by_cases hcb : c ≤ b
  · have hm : textWord A c b ∈ V := closed h₁ (textWord_infix A hac hcb le_rfl)
    have heq₁ := textWord_append A hac hcb
    have heq₂ := textWord_append A hcb hbd
    have hd : textWord A a c ++ textWord A c b ∈ V := by simpa [heq₁] using h₁
    have hu : textWord A c b ++ textWord A b d ∈ V := by simpa [heq₂] using h₂
    let D := Path.deletePrefix closed (textWord A a c) (textWord A c b) hd
    let U := Path.appendSuffix closed (textWord A c b) (textWord A b d) hu
    have : ∃ P : Path V (textWord A a c ++ textWord A c b)
        (textWord A c b ++ textWord A b d),
        P.cost = (d - b).toNat ∧
        ∃ w, P.Visits w ∧ (w.length : ℤ) ≤ max 0 (b - c) := by
      refine ⟨D.trans U, ?_, textWord A c b, Or.inl (Path.visits_end D), ?_⟩
      · simp [D, U]
      · simp only [length_textWord]
        omega
    obtain ⟨P, hP, w, hw, hl⟩ := this
    exact ⟨P.copy heq₁ heq₂, by simpa using hP, w, by simpa using hw, hl⟩
  · have hbc : b ≤ c := by omega
    have h0 : ([] : List α) ∈ V := closed h₁ List.nil_infix
    let D := Path.deletePrefix closed (textWord A a b) [] (by simpa using h₁)
    let G := Path.readGap h0 (textWord A b c) (by
      intro x hx
      obtain ⟨i, _, _, rfl⟩ := mem_textWord A hx
      exact letters i)
    let U := Path.appendSuffix closed [] (textWord A c d) (by simpa using h₂)
    have : ∃ P : Path V (textWord A a b ++ []) ([] ++ textWord A c d),
        P.cost = (d - b).toNat ∧
        ∃ w, P.Visits w ∧ (w.length : ℤ) ≤ max 0 (b - c) := by
      refine ⟨(D.trans G).trans U, ?_, [], Or.inl (Or.inl (Path.visits_end D)), ?_⟩
      · simp only [Path.cost_trans, D, G, U, Path.cost_deletePrefix,
          Path.cost_readGap, Path.cost_appendSuffix, length_textWord]
        omega
      · simp
    obtain ⟨P, hP, w, hw, hl⟩ := this
    exact ⟨P.copy (by simp) (by simp), by simpa using hP, w, by simpa using hw, hl⟩


namespace Path

variable {V : Set (List α)}

theorem deletePrefix_visits (closed : SubstringClosed V) (a b c : List α)
    (h : (a ++ b) ++ c ∈ V) :
    (deletePrefix closed (a ++ b) c h).Visits (b ++ c) := by
  induction a with
  | nil => exact visits_start _
  | cons x xs ih =>
    exact Or.inr (ih _)

theorem appendSuffix_visits (closed : SubstringClosed V) (a b c : List α)
    (h : a ++ (b ++ c) ∈ V) :
    (appendSuffix closed a (b ++ c) h).Visits (a ++ b) := by
  induction b generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, appendSuffix, visits_copy, Visits]
    right
    simpa only [List.append_assoc, List.singleton_append] using ih (a ++ [x]) _

end Path

/-- Delete through a range of starting coordinates, visiting every suffix. -/
theorem window_delete {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) {a b c : ℤ} (hac : a ≤ c) (hcb : c ≤ b)
    (hw : textWord A a b ∈ V) :
    ∃ P : Path V (textWord A a b) (textWord A c b), P.cost = 0 ∧
      ∀ x, a ≤ x → x ≤ c → P.Visits (textWord A x b) := by
  have heq := textWord_append A hac hcb
  let D := Path.deletePrefix closed (textWord A a c) (textWord A c b) (heq.symm ▸ hw)
  refine ⟨D.copy heq rfl, by simp [D], ?_⟩
  intro x hax hxc
  simp only [Path.visits_copy]
  have heq' := textWord_append A hax hxc
  have hv := Path.deletePrefix_visits closed (textWord A a x) (textWord A x c)
    (textWord A c b) (show (textWord A a x ++ textWord A x c) ++ textWord A c b ∈ V by
      rw [heq', heq]; exact hw)
  dsimp [D]
  have hh : ∀ (a' : List α) (h : a' ++ textWord A c b ∈ V),
      a' = textWord A a c →
      (Path.deletePrefix closed a' (textWord A c b) h).Visits (textWord A x b) →
      (Path.deletePrefix closed (textWord A a c) (textWord A c b) (heq.symm ▸ hw)).Visits
        (textWord A x b) := by
    intro a' h e hv'; subst a'; exact hv'
  apply hh _ _ heq'
  simpa only [textWord_append A hxc hcb] using hv

/-- Append through a range of ends, visiting every prefix. -/
theorem window_append {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) {a b d : ℤ} (hab : a ≤ b) (hbd : b ≤ d)
    (hw : textWord A a d ∈ V) :
    ∃ P : Path V (textWord A a b) (textWord A a d),
      P.cost = (d - b).toNat ∧
      ∀ y, b ≤ y → y ≤ d → P.Visits (textWord A a y) := by
  have heq := textWord_append A hab hbd
  let U := Path.appendSuffix closed (textWord A a b) (textWord A b d) (heq.symm ▸ hw)
  refine ⟨U.copy rfl heq, by simp [U], ?_⟩
  intro y hby hyd
  simp only [Path.visits_copy]
  have heq' := textWord_append A hby hyd
  have hv := Path.appendSuffix_visits closed (textWord A a b) (textWord A b y)
    (textWord A y d) (show textWord A a b ++ (textWord A b y ++ textWord A y d) ∈ V by
      rw [heq', heq]; exact hw)
  have hh : ∀ (b' : List α) (h : textWord A a b ++ b' ∈ V),
      b' = textWord A b d →
      (Path.appendSuffix closed (textWord A a b) b' h).Visits (textWord A a y) →
      U.Visits (textWord A a y) := by
    intro b' h e hv'; subst b'; exact hv'
  apply hh _ _ heq'
  simpa only [textWord_append A hab hby] using hv

/-- An ordered-window transition can be chosen to contain every overlap suffix
up to its next start. This strengthens the contact assertion used for links. -/
theorem ordered_windows_suffixes {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V)
    {a b c d : ℤ} (hab : a ≤ b) (hcd : c ≤ d) (hac : a ≤ c) (hbd : b ≤ d)
    (h₁ : textWord A a b ∈ V) (h₂ : textWord A c d ∈ V) :
    ∃ P : Path V (textWord A a b) (textWord A c d),
      P.cost = (d - b).toNat ∧
      (∀ x, a ≤ x → x ≤ c → x ≤ b → P.Visits (textWord A x b)) ∧
      ∃ w, P.Visits w ∧ (w.length : ℤ) ≤ max 0 (b - c) := by
  let m := min b c
  have ham : a ≤ m := le_min hab hac
  have hmb : m ≤ b := min_le_left _ _
  obtain ⟨D, hDc, hDv⟩ := window_delete closed A ham hmb h₁
  have hmid : textWord A m b ∈ V := closed h₁ (textWord_infix A ham hmb le_rfl)
  obtain ⟨Q, hQc, w, hw, hl⟩ := ordered_windows closed A letters hmb hcd
    (min_le_right _ _) hbd hmid h₂
  refine ⟨D.trans Q, by simp [hDc, hQc], ?_, w, Or.inr hw, hl⟩
  intro x hax hxc hxb
  exact Or.inl (hDv x hax (le_min hxb hxc))


structure Layer (V : Set (List α)) (A : ℤ → α) (p : ℕ) where
  z : ℤ → ℤ
  mono : Monotone z
  lower : ∀ x, x ≤ z (x - 1)
  shift : ∀ x, z (x + p) = z x + p
  actual : ∀ x e, z (x - 1) ≤ e → e ≤ z x → textWord A x e ∈ V

namespace Layer

variable {V : Set (List α)} {A : ℤ → α} {p : ℕ}

def first (D : Layer V A p) (x : ℤ) : ℤ := D.z (x - 1)
def last (D : Layer V A p) (x : ℤ) : ℤ := D.z x

theorem first_le_last (D : Layer V A p) (x : ℤ) : D.first x ≤ D.last x :=
  D.mono (by omega)

theorem start_le_first (D : Layer V A p) (x : ℤ) : x ≤ D.first x := D.lower x

theorem first_actual (D : Layer V A p) (x : ℤ) : textWord A x (D.first x) ∈ V :=
  D.actual x _ le_rfl (D.first_le_last x)

theorem last_actual (D : Layer V A p) (x : ℤ) : textWord A x (D.last x) ∈ V :=
  D.actual x _ (D.first_le_last x) le_rfl

theorem shift_mul (D : Layer V A p) (k : ℕ) (x : ℤ) :
    D.z (x + (k * p : ℕ)) = D.z x + (k * p : ℕ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Nat.cast_add, ← add_assoc, D.shift, ih, add_assoc]

/-- An actual height crossing in any finite horizontal range. -/
theorem meets_height (D : Layer V A p) (a Y : ℤ) (K : ℕ)
    (hfirst : D.first a ≤ Y) (hlast : Y ≤ D.last (a + K)) :
    ∃ x : ℤ, a ≤ x ∧ x ≤ a + K ∧ D.first x ≤ Y ∧ Y ≤ D.last x := by
  let test : ℕ → Prop := fun n => n ≤ K ∧ Y ≤ D.z (a + n)
  have hex : ∃ n, test n := ⟨K, le_rfl, hlast⟩
  let n := Nat.find hex
  have hn : n ≤ K ∧ Y ≤ D.z (a + n) := Nat.find_spec hex
  refine ⟨a + n, by omega, by omega, ?_, hn.2⟩
  by_cases h0 : n = 0
  · simpa [h0] using hfirst
  · have hmin : ¬ test (n - 1) := Nat.find_min hex (by omega)
    have hz : D.z (a + ((n - 1 : ℕ) : ℤ)) < Y := by
      simp only [test, not_and, not_le] at hmin
      exact hmin (by omega)
    have heq : a + (n : ℤ) - 1 = a + ((n - 1 : ℕ) : ℤ) := by omega
    exact le_of_lt (by simpa [first, heq] using hz)


def TouchedBy (D : Layer V A p) {s t} (P : Path V s t) : Prop :=
  ∃ x e, D.first x ≤ e ∧ e ≤ D.last x ∧ P.Visits (textWord A x e)

end Layer

/-- Periods can be multiplied without assuming they are least. -/
theorem periodic_mul (A : ℤ → α) (p : ℕ) (per : ∀ x, A (x + p) = A x)
    (k : ℕ) (x : ℤ) : A (x + (k * p : ℕ)) = A x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Nat.cast_add, ← add_assoc, per, ih]


theorem collective_link {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (p k : ℕ)
    (per : ∀ x, A (x + p) = A x)
    {ι : Type} (L : ι → Layer V A p) (lo hi : ι)
    (hlo : ∀ i x, (L lo).z x ≤ (L i).z x)
    (hhi : ∀ i x, (L i).z x ≤ (L hi).z x)
    {a b : ℤ} (hab : a ≤ b) (hR : textWord A a b ∈ V)
    (h₁ : (L hi).first a ≤ b + (k * p : ℕ))
    (h₂ : (L hi).first a - (L lo).last a ≤ (k * p : ℕ))
    (h₃ : b ≤ (L lo).last a + (k * p : ℕ)) :
    ∃ P : Path V (textWord A a b) (textWord A a b),
      P.cost = k * p ∧ ∀ i, (L i).TouchedBy P := by
  let K : ℕ := k * p
  let Y := max b ((L hi).first a)
  have hbY : b ≤ Y := le_max_left _ _
  have hHY : (L hi).first a ≤ Y := le_max_right _ _
  have hYK : Y ≤ b + K := by dsimp [Y, K]; omega
  have haY : a ≤ Y := le_trans hab hbY
  have hYV : textWord A a Y ∈ V := by
    by_cases h : b ≤ (L hi).first a
    · simpa only [Y, max_eq_right h] using (L hi).first_actual a
    · simpa only [Y, max_eq_left (le_of_not_ge h)] using hR
  have perK : ∀ x, A (x + K) = A x := periodic_mul A p per k
  have heqR := textWord_translate A (K : ℤ) perK a b
  have hRV : textWord A (a + K) (b + K) ∈ V := heqR.symm ▸ hR
  obtain ⟨U, hUc, hUv⟩ := window_append closed A hab hbY hYV
  obtain ⟨Q, hQc, hQv, _⟩ := ordered_windows_suffixes closed A letters haY
    (show a + K ≤ b + K by omega) (show a ≤ a + K by omega) hYK hYV hRV
  refine ⟨(U.trans Q).copy rfl heqR, ?_, ?_⟩
  · simp only [Path.cost_copy, Path.cost_trans, hUc, hQc]
    dsimp [K] at *
    omega
  · intro i
    have hf : (L i).first a ≤ Y := le_trans (hhi i (a - 1)) hHY
    have hz : Y ≤ (L i).last (a + K) := by
      have heq := (L i).shift_mul k a
      have hlo' := hlo i a
      dsimp [Layer.last, K] at *
      rw [heq]
      dsimp [Y]
      omega
    obtain ⟨x, hax, hxK, hfx, hxl⟩ := (L i).meets_height a Y K hf hz
    refine ⟨x, Y, hfx, hxl, ?_⟩
    simp only [Path.visits_copy, Path.Visits]
    exact Or.inr (hQv x hax hxK (le_trans ((L i).start_le_first x) hfx))


theorem join_band {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (p k : ℕ)
    (per : ∀ x, A (x + p) = A x)
    {ι : Type} (L : ι → Layer V A p) (lo hi : ι)
    (hlo : ∀ i x, (L lo).z x ≤ (L i).z x)
    (hhi : ∀ i x, (L i).z x ≤ (L hi).z x)
    (t : ℤ) (hband : (L hi).first t - (L lo).last t ≤ (k * p : ℕ)) :
    ∃ P : Path V (textWord A t ((L lo).last t)) (textWord A t ((L lo).last t)),
      P.cost ≤ k * p ∧ ∀ i, (L i).TouchedBy P := by
  let E := (L lo).last t
  let H := (L hi).first t
  let K := k * p
  have hE : textWord A t E ∈ V := (L lo).last_actual t
  have hH : textWord A t H ∈ V := (L hi).first_actual t
  have htE : t ≤ E := le_trans ((L lo).start_le_first t) ((L lo).first_le_last t)
  have htH : t ≤ H := (L hi).start_le_first t
  by_cases hHE : H ≤ E
  · refine ⟨Path.nil _ hE, Nat.zero_le _, ?_⟩
    intro i
    refine ⟨t, E, le_trans (hhi i (t - 1)) hHE, hlo i t, rfl⟩
  · have hEH : E ≤ H := by omega
    have hHK : H ≤ E + K := by dsimp [H, E, K]; omega
    have perK : ∀ x, A (x + K) = A x := periodic_mul A p per k
    have heqE := textWord_translate A (K : ℤ) perK t E
    obtain ⟨U, hUc, hUv⟩ := window_append closed A htE hEH hH
    obtain ⟨Q, hQc, _⟩ := ordered_windows closed A letters htH
      (show t + K ≤ E + K by omega) (show t ≤ t + K by omega) hHK hH
      (heqE.symm ▸ hE)
    refine ⟨(U.trans Q).copy rfl heqE, ?_, ?_⟩
    · simp only [Path.cost_copy, Path.cost_trans, hUc, hQc]
      dsimp [K] at *
      omega
    · intro i
      let e := max E ((L i).first t)
      have hfe : (L i).first t ≤ e := le_max_right _ _
      have heE : E ≤ e := le_max_left _ _
      have hel : e ≤ (L i).last t := max_le (hlo i t) ((L i).first_le_last t)
      have heH : e ≤ H := max_le hEH (hhi i (t - 1))
      refine ⟨t, e, hfe, hel, ?_⟩
      simp only [Path.visits_copy, Path.Visits]
      exact Or.inl (hUv e heE heH)

/-- Forward rotations carry the usual lexicographic order, not a coordinatewise
order on streams. -/
def forward (A : ℤ → α) (t : ℤ) : Lex (ℕ → α) :=
  toLex (fun n => A (t + n))

theorem lex_at_le [LinearOrder α] {s t : Lex (ℕ → α)} (h : s ≤ t) (n : ℕ)
    (heq : ∀ j < n, s j = t j) : s n ≤ t n := by
  by_contra hn
  have hlt : t < s := ⟨n, fun j hj => (heq j hj).symm, lt_of_not_ge hn⟩
  exact (not_lt_of_ge h) hlt

/-- If a stream dominates its shift by q, then no smaller q-periodic stream
can have its first q letters. This is the first-difference argument in the
maximal-rotation lemma, expressed as strong induction. -/
theorem stream_eq_of_max [LinearOrder α] (s d : Lex (ℕ → α)) (q : ℕ)
    (hq : 0 < q) (hd : ∀ n, d (n + q) = d n)
    (hshift : toLex (fun n => s (n + q)) ≤ s) (hle : d ≤ s)
    (hprefix : ∀ n < q, s n = d n) : s = d := by
  apply funext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < q
    · exact hprefix n hn
    have hqn : q ≤ n := Nat.le_of_not_gt hn
    have hnq : n - q < n := by omega
    have heqn : n - q + q = n := Nat.sub_add_cancel hqn
    have hd' : d n = d (n - q) := by simpa only [heqn] using hd (n - q)
    have hsn : s n ≤ s (n - q) := by
      have hh := lex_at_le hshift (n - q) (fun j hj => ?_)
      · simpa only [Pi.toLex_apply, heqn] using hh
      · change s (j + q) = s j
        rw [ih (j + q) (by omega), hd j, ih j (by omega)]
    have hds : d n ≤ s n := lex_at_le hle n (fun j hj => (ih j hj).symm)
    apply le_antisymm _ hds
    rw [ih (n - q) hnq, ← hd'] at hsn
    exact hsn

/-- Integer periodic functions can be evaluated at their Euclidean residue. -/
theorem periodic_emod (A : ℤ → α) (p : ℤ) (per : ∀ x, A (x + p) = A x)
    (x : ℤ) : A (x % p) = A x := by
  have hp : Function.Periodic A p := per
  have h := hp.int_mul (x / p) (x % p)
  simpa only [Int.cast_id, Int.emod_add_ediv_mul] using h.symm

/-- Two periodic, two-sided texts are determined by their forward words. -/
theorem periodic_eq_of_forward_eq (A D : ℤ → α) (p q : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hA : ∀ x, A (x + p) = A x)
    (hD : ∀ x, D (x + q) = D x) (t : ℤ) (heq : forward A t = forward D t) :
    A = D := by
  have hAp := periodic_mul A p hA q
  have hDq := periodic_mul D q hD p
  have hc : (0 : ℤ) < p * q := by positivity
  have hAc : ∀ x, A (x + (p * q : ℤ)) = A x := by
    simpa only [Nat.cast_mul, mul_comm] using hAp
  have hDc : ∀ x, D (x + (p * q : ℤ)) = D x := by
    simpa only [Nat.cast_mul] using hDq
  funext x
  let r := (x - t) % (p * q : ℤ)
  have hr : 0 ≤ r := Int.emod_nonneg _ (ne_of_gt hc)
  have hperA : ∀ y, A (t + y + (p * q : ℤ)) = A (t + y) := fun y => hAc (t + y)
  have hperD : ∀ y, D (t + y + (p * q : ℤ)) = D (t + y) := fun y => hDc (t + y)
  have ha := periodic_emod (fun y => A (t + y)) (p * q) (by
    intro y; simpa only [add_assoc] using hperA y) (x - t)
  have hd := periodic_emod (fun y => D (t + y)) (p * q) (by
    intro y; simpa only [add_assoc] using hperD y) (x - t)
  simp only [add_sub_cancel] at ha hd
  rw [← ha, ← hd]
  have h := congrFun heq r.toNat
  simpa only [forward, Pi.toLex_apply, Int.toNat_of_nonneg hr] using h


theorem maximal_rotation [LinearOrder α] (A D : ℤ → α) (p q : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hA : ∀ x, A (x + p) = A x)
    (hD : ∀ x, D (x + q) = D x) (t : ℤ)
    (hmax : ∀ x, forward A x ≤ forward A t)
    (hbelow : ∀ x, forward D x ≤ forward A t) (hne : A ≠ D) :
    ∃ n < q, A (t + n) ≠ D (t + n) := by
  by_contra! h
  apply hne
  apply periodic_eq_of_forward_eq A D p q hp hq hA hD t
  apply stream_eq_of_max (forward A t) (forward D t) q hq
  · intro n
    simpa only [forward, Pi.toLex_apply, Nat.cast_add, add_assoc] using hD (t + n)
  · convert hmax (t + q) using 1
    congr 1
    funext n
    simp only [forward, Pi.toLex_apply]
    congr 1
    omega
  · exact hbelow t
  · exact h

/-- Agreement on the half-open integer interval [a,b). -/
def AgreeOn (A D : ℤ → α) (a b : ℤ) : Prop :=
  ∀ x, a ≤ x → x < b → A x = D x

theorem textWord_eq_of_agree {A D : ℤ → α} {a b : ℤ} (h : AgreeOn A D a b) :
    textWord A a b = textWord D a b := by
  apply congrArg List.ofFn
  funext i
  apply h
  · omega
  · have := i.isLt
    omega

theorem periodic_mod_at (A : ℤ → α) (p a x : ℤ)
    (per : ∀ y, A (y + p) = A y) : A (a + (x - a) % p) = A x := by
  have h := periodic_emod (fun y => A (a + y)) p (fun y => by
    simpa only [add_assoc] using per (a + y)) (x - a)
  simpa only [add_sub_cancel] using h

/-- Agreement for one period determines an aligned periodic text. -/
theorem same_period_eq (A D : ℤ → α) (p : ℕ) (hp : 0 < p)
    (hA : ∀ x, A (x + p) = A x) (hD : ∀ x, D (x + p) = D x)
    (a : ℤ) (h : AgreeOn A D a (a + p)) : A = D := by
  funext x
  rw [← periodic_mod_at A p a x hA, ← periodic_mod_at D p a x hD]
  apply h
  · have := Int.emod_nonneg (x - a) (show (p : ℤ) ≠ 0 by omega)
    omega
  · have := Int.emod_lt_of_pos (x - a) (show (0 : ℤ) < p by omega)
    omega


theorem eq_of_long_agreement (A D : ℤ → α) (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hA : ∀ x, A (x + p) = A x) (hD : ∀ x, D (x + q) = D x)
    (a : ℤ) (h : AgreeOn A D a (a + p + q)) : A = D := by
  have hDp : ∀ x, D (x + p) = D x := by
    intro x
    let y := a + (x - a) % (q : ℤ)
    have hay : a ≤ y := by
      have := Int.emod_nonneg (x - a) (show (q : ℤ) ≠ 0 by omega)
      dsimp [y]; omega
    have hyq : y < a + q := by
      have := Int.emod_lt_of_pos (x - a) (show (0 : ℤ) < q by omega)
      dsimp [y]; omega
    have hdyp : D (y + p) = D (x + p) :=
      periodic_mod_at (fun z => D (z + p)) q a x (fun z => by
        simpa only [add_right_comm] using hD (z + p))
    have hdy : D y = D x := periodic_mod_at D q a x hD
    rw [← hdyp, ← hdy, ← h (y + p) (by omega) (by omega),
      ← h y hay (by omega), hA y]
  apply same_period_eq A D p hp hA hDp a
  intro x hax hxb
  exact h x hax (by omega)

theorem agreement_bound (A D : ℤ → α) (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hA : ∀ x, A (x + p) = A x) (hD : ∀ x, D (x + q) = D x)
    (hne : A ≠ D) (a b : ℤ) (h : AgreeOn A D a b) : b - a < p + q := by
  by_contra hn
  apply hne
  apply eq_of_long_agreement A D p q hp hq hA hD a
  intro x hx hy
  exact h x hx (by omega)

theorem same_period_agreement_bound (A D : ℤ → α) (p : ℕ) (hp : 0 < p)
    (hA : ∀ x, A (x + p) = A x) (hD : ∀ x, D (x + p) = D x)
    (hne : A ≠ D) (a b : ℤ) (h : AgreeOn A D a b) : b - a < p := by
  by_contra hn
  apply hne
  apply same_period_eq A D p hp hA hD a
  intro x hx hy
  exact h x hx (by omega)

namespace Layer

variable {V : Set (List α)} {A : ℤ → α} {p : ℕ}

theorem first_mono (D : Layer V A p) : Monotone D.first :=
  fun _ _ h => D.mono (by omega)

theorem last_mono (D : Layer V A p) : Monotone D.last := D.mono

@[simp] theorem first_shift (D : Layer V A p) (x : ℤ) :
    D.first (x + p) = D.first x + p := by
  simpa only [first, add_sub_right_comm] using D.shift (x - 1)

@[simp] theorem last_shift (D : Layer V A p) (x : ℤ) :
    D.last (x + p) = D.last x + p := D.shift x

/-- An actual vertex of a layer whose symbol length is at most the allowance. -/
def HasShort (D : Layer V A p) (q : ℕ) : Prop :=
  ∃ x e, D.first x ≤ e ∧ e ≤ D.last x ∧ (textWord A x e).length ≤ q

theorem first_long_of_not_short (D : Layer V A p) (q : ℕ) (h : ¬ D.HasShort q)
    (x : ℤ) : (q : ℤ) < D.first x - x := by
  have hx : x ≤ D.first x := D.start_le_first x
  have hlen : ¬ (textWord A x (D.first x)).length ≤ q :=
    fun hc => h ⟨x, D.first x, le_rfl, D.first_le_last x, hc⟩
  simp only [length_textWord] at hlen
  omega

end Layer


theorem collective_short_sweep {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (p k q : ℕ)
    (hk : 1 ≤ k) (per : ∀ x, A (x + p) = A x)
    {ι : Type} (L : ι → Layer V A p) (hi : ι)
    (hhi : ∀ i x, (L i).z x ≤ (L hi).z x)
    (hlong : ∀ i, ¬ (L i).HasShort q)
    {a b t : ℤ} (hat : a ≤ t) (htb : t < b)
    (hR : textWord A a b ∈ V)
    (hH : (L hi).first t ≤ b + (k * p : ℕ))
    (hlen : b - a < p + q) (hagr : b - t < q) :
    ∃ P : Path V (textWord A a b) (textWord A a b),
      P.cost = k * p ∧ (∀ i, (L i).TouchedBy P) ∧
      ∃ w, P.Visits w ∧ w.length ≤ q := by
  let K := k * p
  let x := min t (a + K)
  let F := (L hi).first x
  have hpK : (p : ℤ) ≤ K := by
    have := Nat.mul_le_mul_right p hk
    simp only [one_mul] at this
    exact_mod_cast this
  have hax : a ≤ x := le_min hat (by omega)
  have hxt : x ≤ t := min_le_left _ _
  have hxK : x ≤ a + K := min_le_right _ _
  have hxb : x ≤ b := by omega
  have hshort : b - x < q := by
    by_cases h : t ≤ a + K
    · dsimp [x]; rw [min_eq_left h]; exact hagr
    · have heq : x = a + K := min_eq_right (by omega)
      rw [heq]
      omega
  have hbfirst : ∀ i, b ≤ (L i).first x := by
    intro i
    have := (L i).first_long_of_not_short q (hlong i) x
    omega
  have hbF : b ≤ F := hbfirst hi
  have hFK : F ≤ b + K := le_trans ((L hi).first_mono hxt) hH
  have hFV : textWord A x F ∈ V := (L hi).first_actual x
  have heqR := textWord_translate A (K : ℤ) (periodic_mul A p per k) a b
  obtain ⟨D, hDc, _⟩ := window_delete closed A hax hxb hR
  obtain ⟨U, hUc, hUv⟩ := window_append closed A hxb hbF hFV
  obtain ⟨Q, hQc, _⟩ := ordered_windows closed A letters (le_trans hxb hbF)
    (show a + K ≤ b + K by omega) hxK hFK hFV (heqR.symm ▸ hR)
  refine ⟨((D.trans U).trans Q).copy rfl heqR, ?_, ?_, ?_⟩
  · simp only [Path.cost_copy, Path.cost_trans, hDc, hUc, hQc]
    dsimp [K] at *
    omega
  · intro i
    refine ⟨x, (L i).first x, le_rfl, (L i).first_le_last x, ?_⟩
    simp only [Path.visits_copy, Path.Visits]
    exact Or.inl (Or.inr (hUv _ (hbfirst i) (hhi i (x - 1))))
  · refine ⟨textWord A x b, ?_, ?_⟩
    · simp only [Path.visits_copy, Path.Visits]
      exact Or.inl (Or.inl (Path.visits_end D))
    · simp only [length_textWord]
      omega


theorem cycle_collective_contact [LinearOrder α]
    {V : Set (List α)} (closed : SubstringClosed V)
    (A D : ℤ → α) (letters : ∀ x, [A x] ∈ V) (p k q : ℕ)
    (hp : 0 < p) (hk : 1 ≤ k) (hq : 0 < q)
    (per : ∀ x, A (x + p) = A x) (perD : ∀ x, D (x + q) = D x)
    {ι : Type} (L : ι → Layer V A p) (lo hi : ι)
    (hlo : ∀ i x, (L lo).z x ≤ (L i).z x)
    (hhi : ∀ i x, (L i).z x ≤ (L hi).z x)
    {a b t : ℤ} (hat : a ≤ t) (htb : t < b)
    (hR : textWord A a b ∈ V) (hagree : AgreeOn A D a b) (hne : A ≠ D)
    (hmax : ∀ x, forward A x ≤ forward A t)
    (hbelow : ∀ x, forward D x ≤ forward A t)
    (hH : (L hi).first t ≤ b + (k * p : ℕ))
    (hband : (L hi).first a - (L lo).last a ≤ (k * p : ℕ))
    (hlast : b ≤ (L lo).last a + (k * p : ℕ)) :
    ∃ P : Path V (textWord A a b) (textWord A a b),
      P.cost = k * p ∧ (∀ i, (L i).TouchedBy P) ∧
      ((∃ i, (L i).HasShort q) ∨ ∃ w, P.Visits w ∧ w.length ≤ q) := by
  classical
  by_cases hs : ∃ i, (L i).HasShort q
  · obtain ⟨P, hPc, hPv⟩ := collective_link closed A letters p k per L lo hi hlo hhi
      (show a ≤ b by omega) hR (le_trans ((L hi).first_mono hat) hH) hband hlast
    exact ⟨P, hPc, hPv, Or.inl hs⟩
  · have hlen := agreement_bound A D p q hp hq per perD hne a b hagree
    have hagr : b - t < q := by
      obtain ⟨n, hn, hne'⟩ := maximal_rotation A D p q hp hq per perD t hmax hbelow hne
      by_contra h
      exact hne' (hagree (t + n) (by omega) (by omega))
    obtain ⟨P, hPc, hPv, hc⟩ := collective_short_sweep closed A letters p k q hk per
      L hi hhi (by simpa only [not_exists] using hs) hat htb hR hH hlen hagr
    exact ⟨P, hPc, hPv, Or.inr hc⟩

namespace Path

variable {V : Set (List α)} {s t u : List α}

/-- The word written by a hierarchical walk: exactly one symbol per up edge. -/
def written : {s t : List α} → Path V s t → List α
  | _, _, .nil _ _ => []
  | _, _, .up _ a _ _ => [a]
  | _, _, .down _ _ _ _ => []
  | _, _, .trans P Q => P.written ++ Q.written

@[simp] theorem length_written (P : Path V s t) : P.written.length = P.cost := by
  induction P <;> simp_all [written, cost]

theorem end_suffix_written (P : Path V s t) : t <:+ s ++ P.written := by
  induction P with
  | nil => simp [written]
  | up => simp [written]
  | down a s _ _ => simp [written]
  | trans P Q ihP ihQ =>
    simpa only [written, List.append_assoc] using ihQ.trans (List.suffix_append_self_iff.mpr ihP)

/-- The exact output invariant in the main_oai proof: every visited vertex occurs
contiguously in the starting word followed by the appended letters. -/
theorem visited_infix_written (P : Path V s t) {w : List α} (hw : P.Visits w) :
    w <:+: s ++ P.written := by
  induction P with
  | nil => subst w; simp [written]
  | up s a _ _ =>
    rcases hw with rfl | rfl
    · simpa only [written] using List.infix_append_left
    · simp [written]
  | down a s _ _ =>
    rcases hw with rfl | rfl
    · simp [written]
    · simp only [written, List.append_nil]
      exact List.infix_cons List.infix_rfl
  | trans P Q ihP ihQ =>
    rcases hw with hw | hw
    · simpa only [written, List.append_assoc] using
        (ihP hw).trans (List.infix_append_left (l₂ := Q.written))
    · have h := (List.suffix_append_self_iff.mpr (P.end_suffix_written) : _ ++ Q.written <:+ _).isInfix
      simpa only [written, List.append_assoc] using (ihQ hw).trans h

/-- Split at an actual visited vertex, preserving costs and every visit. -/
theorem split (P : Path V s t) {w : List α} (hw : P.Visits w) :
    ∃ (U : Path V s w) (D : Path V w t),
      U.cost + D.cost = P.cost ∧
      ∀ v, P.Visits v ↔ U.Visits v ∨ D.Visits v := by
  induction P with
  | nil s hs =>
    subst w
    exact ⟨.nil s hs, .nil s hs, rfl, fun _ => by simp [Visits]⟩
  | up s a hs ht =>
    rcases hw with h | h
    · subst w
      refine ⟨.nil s hs, .up s a hs ht, by simp [cost], ?_⟩
      intro v; simp only [Visits]; tauto
    · subst w
      refine ⟨.up s a hs ht, .nil (s ++ [a]) ht, by simp [cost], ?_⟩
      intro v; simp only [Visits]; tauto
  | down a s hs ht =>
    rcases hw with h | h
    · subst w
      refine ⟨.nil (a :: s) hs, .down a s hs ht, by simp [cost], ?_⟩
      intro v; simp only [Visits]; tauto
    · subst w
      refine ⟨.down a s hs ht, .nil s ht, by simp [cost], ?_⟩
      intro v; simp only [Visits]; tauto
  | trans P Q ihP ihQ =>
    rcases hw with hw | hw
    · obtain ⟨U, D, hc, hv⟩ := ihP hw
      refine ⟨U, D.trans Q, ?_, ?_⟩
      · simp only [cost_trans]; omega
      · intro v; simp only [Visits, hv, or_assoc]
    · obtain ⟨U, D, hc, hv⟩ := ihQ hw
      refine ⟨P.trans U, D, ?_, ?_⟩
      · simp only [cost_trans]; omega
      · intro v; simp only [Visits, hv, or_assoc]

/-- Rotate a closed walk to any of its visited vertices without adding edges. -/
theorem rotate (P : Path V s s) {w : List α} (hw : P.Visits w) :
    ∃ Q : Path V w w, Q.cost = P.cost ∧ ∀ v, Q.Visits v ↔ P.Visits v := by
  obtain ⟨U, D, hc, hv⟩ := P.split hw
  refine ⟨D.trans U, by simp only [cost_trans]; omega, ?_⟩
  intro v
  simp only [Visits, hv, or_comm]

/-- Euler splicing in its exact needed form: edge-disjointness is unnecessary
because edge copies remain distinct in the path data. -/
theorem splice (P : Path V s s) (Q : Path V t t) (w : List α)
    (hP : P.Visits w) (hQ : Q.Visits w) :
    ∃ R : Path V s s, R.cost = P.cost + Q.cost ∧
      ∀ v, R.Visits v ↔ P.Visits v ∨ Q.Visits v := by
  obtain ⟨U, D, hc, hv⟩ := P.split hP
  obtain ⟨Q', hQc, hQv⟩ := Q.rotate hQ
  refine ⟨(U.trans Q').trans D, ?_, ?_⟩
  · simp only [cost_trans]; omega
  · intro v
    simp only [Visits, hQv, hv]
    tauto

/-- Rooting at a short vertex costs exactly its symbol length. -/
theorem root_loop (closed : SubstringClosed V) (w : List α) (hw : w ∈ V) :
    ∃ P : Path V [] [], P.cost = w.length ∧ P.Visits w := by
  let U := (appendSuffix closed [] w (by simpa using hw))
  let D := (deletePrefix closed w [] (by simpa using hw))
  refine ⟨(U.copy (t' := w) rfl (by simp)).trans (D.copy (s' := w) (by simp) rfl), ?_, ?_⟩
  · simp [U, D]
  · exact Or.inl (visits_end _)

end Path

/-- Concatenate any finite ordered list of actual windows. -/
theorem ordered_chain {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V)
    (a b : ℕ → ℤ) (ha : Monotone a) (hb : Monotone b) (n : ℕ)
    (hab : ∀ i ≤ n, a i ≤ b i) (hV : ∀ i ≤ n, textWord A (a i) (b i) ∈ V) :
    ∃ P : Path V (textWord A (a 0) (b 0)) (textWord A (a n) (b n)),
      P.cost = (b n - b 0).toNat ∧
      ∀ i ≤ n, P.Visits (textWord A (a i) (b i)) := by
  induction n with
  | zero =>
    refine ⟨.nil _ (hV 0 le_rfl), by simp [Path.cost], ?_⟩
    intro i hi
    have : i = 0 := by omega
    subst i
    rfl
  | succ n ih =>
    obtain ⟨P, hPc, hPv⟩ := ih (fun i hi => hab i (by omega))
      (fun i hi => hV i (by omega))
    obtain ⟨Q, hQc, _⟩ := ordered_windows closed A letters (hab n (by omega))
      (hab (n + 1) le_rfl) (ha (by omega)) (hb (by omega))
      (hV n (by omega)) (hV (n + 1) le_rfl)
    refine ⟨P.trans Q, ?_, ?_⟩
    · simp only [Path.cost_trans, hPc, hQc]
      have := hb (show 0 ≤ n by omega)
      have := hb (show n ≤ n + 1 by omega)
      omega
    · intro i hi
      by_cases h : i ≤ n
      · exact Or.inl (hPv i h)
      · have : i = n + 1 := by omega
        subst i
        exact Or.inr (Path.visits_end Q)


theorem individual_link {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (p q : ℕ)
    (per : ∀ x, A (x + p) = A x) (L : Layer V A p)
    {a b : ℤ} (hab : a ≤ b) (hR : textWord A a b ∈ V)
    (hfirst : L.first a ≤ b) (hlast : b ≤ L.last a + p)
    (hlen : b - a < p + q) :
    ∃ P : Path V (textWord A a b) (textWord A a b),
      P.cost = p ∧ L.TouchedBy P ∧ ∃ w, P.Visits w ∧ w.length ≤ q := by
  let e := max b (L.first (a + p))
  have hbe : b ≤ e := le_max_left _ _
  have hfe : L.first (a + p) ≤ e := le_max_right _ _
  have heL : e ≤ L.last (a + p) := by
    apply max_le
    · simpa only [Layer.last_shift] using hlast
    · exact L.first_le_last _
  have hebp : e ≤ b + p := by
    apply max_le
    · omega
    · rw [Layer.first_shift]
      omega
  have hapse : a + p ≤ e := le_trans (L.start_le_first _) hfe
  have heV : textWord A (a + p) e ∈ V := L.actual _ _ hfe heL
  have heq := textWord_translate A p per a b
  obtain ⟨Q, hQc, w, hQw, hwlen⟩ := ordered_windows closed A letters hab hapse
    (by omega) hbe hR heV
  obtain ⟨U, hUc, _⟩ := window_append closed A hapse hebp (heq.symm ▸ hR)
  refine ⟨(Q.trans U).copy rfl heq, ?_, ?_, w, ?_, ?_⟩
  · simp only [Path.cost_copy, Path.cost_trans, hQc, hUc]
    omega
  · refine ⟨a + p, e, hfe, heL, ?_⟩
    simp only [Path.visits_copy, Path.Visits]
    exact Or.inl (Path.visits_end Q)
  · simpa only [Path.visits_copy, Path.Visits] using (Or.inl hQw : Q.Visits w ∨ U.Visits w)
  · omega


theorem one_free_period {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (p k : ℕ)
    (per : ∀ x, A (x + p) = A x)
    {ι : Type} (L : ι → Layer V A p) (lo hi : ι)
    (hlo : ∀ i x, (L lo).z x ≤ (L i).z x)
    (hhi : ∀ i x, (L i).z x ≤ (L hi).z x)
    (t : ℤ) (hband : (L hi).first t - (L lo).last t ≤ ((k - 1) * p : ℕ)) :
    ∃ P : Path V (textWord A t ((L lo).last t)) (textWord A t ((L lo).last t)),
      P.cost ≤ (k - 1) * p ∧ ∀ i, (L i).TouchedBy P :=
  join_band closed A letters p (k - 1) per L lo hi hlo hhi t hband

namespace Layer

variable {V : Set (List α)} {A : ℤ → α} {p : ℕ}

/-- Realize one entire vertical passage and its following down step. -/
theorem passage (L : Layer V A p) (closed : SubstringClosed V) (x : ℤ) :
    ∃ P : Path V (textWord A x (L.first x))
        (textWord A (x + 1) (L.first (x + 1))),
      P.cost = (L.first (x + 1) - L.first x).toNat ∧
      ∀ e, L.first x ≤ e → e ≤ L.last x → P.Visits (textWord A x e) := by
  have heq : L.first (x + 1) = L.last x := by simp [first, last]
  have hbound : x + 1 ≤ L.last x := by simpa only [heq] using L.start_le_first (x + 1)
  obtain ⟨U, hUc, hUv⟩ := window_append closed A (L.start_le_first x)
    (L.first_le_last x) (L.last_actual x)
  obtain ⟨D, hDc, _⟩ := window_delete closed A (show x ≤ x + 1 by omega)
    hbound (L.last_actual x)
  refine ⟨(U.trans D).copy rfl (by rw [heq]), ?_, ?_⟩
  · simp only [Path.cost_copy, Path.cost_trans, hUc, hDc, Nat.add_zero, heq]
  · intro e hfe hel
    simpa only [Path.visits_copy, Path.Visits] using
      (Or.inl (hUv e hfe hel) : U.Visits (textWord A x e) ∨ D.Visits (textWord A x e))

/-- A finite segment of a layer, including every window at its traversed starts. -/
theorem segment (L : Layer V A p) (closed : SubstringClosed V) (t : ℤ) (n : ℕ) :
    ∃ P : Path V (textWord A t (L.first t))
        (textWord A (t + n) (L.first (t + n))),
      P.cost = (L.first (t + n) - L.first t).toNat ∧
      ∀ x e, t ≤ x → x < t + n → L.first x ≤ e → e ≤ L.last x →
        P.Visits (textWord A x e) := by
  induction n with
  | zero =>
    refine ⟨(Path.nil _ (L.first_actual t)).copy rfl (by simp), by simp [Path.cost], ?_⟩
    intro x e htx hxt
    omega
  | succ n ih =>
    obtain ⟨P, hPc, hPv⟩ := ih
    obtain ⟨Q, hQc, hQv⟩ := L.passage closed (t + n)
    have hend : t + (n : ℤ) + 1 = t + (n + 1 : ℕ) := by omega
    refine ⟨(P.trans Q).copy rfl (by rw [hend]), ?_, ?_⟩
    · simp only [Path.cost_copy, Path.cost_trans, hPc, hQc]
      have h₁ := L.first_mono (show t ≤ t + (n : ℤ) by omega)
      have h₂ := L.first_mono (show t + (n : ℤ) ≤ t + n + 1 by omega)
      rw [hend] at *
      omega
    · intro x e htx hxt hfe hel
      simp only [Path.visits_copy, Path.Visits]
      by_cases h : x < t + n
      · exact Or.inl (hPv x e htx h hfe hel)
      · have hx : x = t + n := by omega
        subst x
        exact Or.inr (hQv e hfe hel)

/-- One primitive turn is an explicit closed walk of exactly the period cost. -/
theorem turn (L : Layer V A p) (closed : SubstringClosed V)
    (per : ∀ x, A (x + p) = A x) (t : ℤ) :
    ∃ P : Path V (textWord A t (L.first t)) (textWord A t (L.first t)),
      P.cost = p ∧
      ∀ x e, t ≤ x → x < t + p → L.first x ≤ e → e ≤ L.last x →
        P.Visits (textWord A x e) := by
  obtain ⟨P, hPc, hPv⟩ := L.segment closed t p
  have heq : textWord A (t + p) (L.first (t + p)) = textWord A t (L.first t) := by
    rw [L.first_shift]
    exact textWord_translate A p per t (L.first t)
  refine ⟨P.copy rfl heq, ?_, ?_⟩
  · simp only [Path.cost_copy, hPc, L.first_shift]
    omega
  · intro x e htx hxt hfe hel
    exact (Path.visits_copy ..).mpr (hPv x e htx hxt hfe hel)

end Layer

namespace Layer

variable {V : Set (List α)} {A : ℤ → α} {p : ℕ}

theorem shift_int (L : Layer V A p) (m x : ℤ) :
    L.z (x + m * p) = L.z x + m * p := by
  have h : Function.Periodic (fun y => L.z y - y) (p : ℤ) := by
    intro y
    change L.z (y + p) - (y + p) = L.z y - y
    rw [L.shift]
    omega
  have hh := h.int_mul m x
  simp only [Int.cast_id] at hh
  omega

theorem first_shift_int (L : Layer V A p) (m x : ℤ) :
    L.first (x + m * p) = L.first x + m * p := by
  simpa only [first, add_sub_right_comm] using L.shift_int m (x - 1)

/-- An entire layer is covered by one turn, because every actual window is a
period translate of a window in that turn. -/
theorem full_turn (L : Layer V A p) (closed : SubstringClosed V) (hp : 0 < p)
    (per : ∀ x, A (x + p) = A x) (t : ℤ) :
    ∃ P : Path V (textWord A t (L.first t)) (textWord A t (L.first t)),
      P.cost = p ∧ ∀ x e, L.first x ≤ e → e ≤ L.last x →
        P.Visits (textWord A x e) := by
  obtain ⟨P, hPc, hPv⟩ := L.turn closed per t
  refine ⟨P, hPc, ?_⟩
  intro x e hfe hel
  let r := t + (x - t) % (p : ℤ)
  let m := (x - t) / (p : ℤ)
  have htr : t ≤ r := by
    have := Int.emod_nonneg (x - t) (show (p : ℤ) ≠ 0 by omega)
    dsimp [r]; omega
  have hrt : r < t + p := by
    have := Int.emod_lt_of_pos (x - t) (show (0 : ℤ) < p by omega)
    dsimp [r]; omega
  have hrx : r + m * p = x := by
    have := Int.emod_add_ediv_mul (x - t) (p : ℤ)
    dsimp [r, m]; omega
  have hf : L.first r ≤ e - m * p := by
    have hh := L.first_shift_int m r
    rw [hrx] at hh
    omega
  have hl : e - m * p ≤ L.last r := by
    have hh := L.shift_int m r
    rw [hrx] at hh
    change e ≤ L.z x at hel
    change e - m * p ≤ L.z r
    omega
  have hpA : Function.Periodic A (p : ℤ) := per
  have heq := textWord_translate A (m * p) (hpA.int_mul m) r (e - m * p)
  rw [hrx, sub_add_cancel] at heq
  rw [heq]
  exact hPv r (e - m * p) htr hrt hf hl

end Layer

/-- A closed walk with its base vertex retained as explicit data. -/
structure Loop (V : Set (List α)) where
  base : List α
  path : Path V base base

namespace Loop

variable {V : Set (List α)}

def cost (P : Loop V) : ℕ := P.path.cost
def Visits (P : Loop V) (w : List α) : Prop := P.path.Visits w

def Meets (P Q : Loop V) : Prop := ∃ w, P.Visits w ∧ Q.Visits w

/-- Saturate a closed walk by splicing every accessible loop from a finite
collection. The resulting visited set is closed under that collection, and no
loop budget is spent twice. -/
theorem saturate {ι : Type} (F : ι → Loop V) (I : Finset ι) (P : Loop V) :
    ∃ Q : Loop V, Q.base = P.base ∧ Q.cost ≤ P.cost + ∑ i ∈ I, (F i).cost ∧
      (∀ w, P.Visits w → Q.Visits w) ∧
      (∀ i ∈ I, Q.Meets (F i) → ∀ w, (F i).Visits w → Q.Visits w) ∧
      (∀ w, Q.Visits w → P.Visits w ∨ ∃ i ∈ I, (F i).Visits w) := by
  classical
  induction I using Finset.strongInductionOn generalizing P
  rename_i I ih
  by_cases hex : ∃ i ∈ I, P.Meets (F i)
  · obtain ⟨i, hi, w, hPw, hFw⟩ := hex
    obtain ⟨R, hRc, hRv⟩ := P.path.splice (F i).path w hPw hFw
    let P' : Loop V := ⟨P.base, R⟩
    obtain ⟨Q, hQb, hQc, hPQ, hclosed, hsupport⟩ :=
      ih (I.erase i) (Finset.erase_ssubset hi) P'
    refine ⟨Q, hQb, ?_, ?_, ?_, ?_⟩
    · have hsum := Finset.sum_erase_add I (fun j => (F j).cost) hi
      change R.cost = P.cost + (F i).cost at hRc
      change Q.cost ≤ R.cost + _ at hQc
      omega
    · intro v hv
      apply hPQ v
      exact (hRv v).mpr (Or.inl hv)
    · intro j hj hmeet v hv
      by_cases hji : j = i
      · subst j
        apply hPQ v
        exact (hRv v).mpr (Or.inr hv)
      · exact hclosed j (Finset.mem_erase.mpr ⟨hji, hj⟩) hmeet v hv
    · intro v hv
      rcases hsupport v hv with h | ⟨j, hj, hv⟩
      · rcases (hRv v).mp h with hp | hf
        · exact Or.inl hp
        · exact Or.inr ⟨i, hi, hf⟩
      · exact Or.inr ⟨j, Finset.mem_of_mem_erase hj, hv⟩
  · refine ⟨P, rfl, Nat.le_add_right _ _, fun _ h => h, ?_, fun _ h => Or.inl h⟩
    intro i hi hmeet
    exact False.elim (hex ⟨i, hi, hmeet⟩)

/-- Used-support connectivity in a form that exactly expresses closure under
closed walks. It ignores incidental isolated vertices and records a root. -/
def Connected {ι : Type} (F : ι → Loop V) (I : Finset ι) (root : List α) : Prop :=
  ∀ U : Set (List α), root ∈ U →
    (∀ i ∈ I, (∃ w, w ∈ U ∧ (F i).Visits w) → ∀ w, (F i).Visits w → w ∈ U) →
    ∀ i ∈ I, ∀ w, (F i).Visits w → w ∈ U


theorem of_connected {ι : Type} (F : ι → Loop V) (I : Finset ι) (root : List α)
    (hroot : root ∈ V) (hconn : Connected F I root) :
    ∃ P : Path V root root, P.cost ≤ ∑ i ∈ I, (F i).cost ∧
      ∀ i ∈ I, ∀ w, (F i).Visits w → P.Visits w := by
  let P : Loop V := ⟨root, Path.nil root hroot⟩
  obtain ⟨Q, hQb, hQc, hPQ, hclosed, _⟩ := saturate F I P
  have hbase : Q.base = root := hQb
  refine ⟨Q.path.copy hbase hbase, ?_, ?_⟩
  · simpa only [Path.cost_copy, P, cost, Path.cost, Nat.zero_add] using hQc
  · have h := hconn {w | Q.Visits w} (hPQ root rfl) (fun i hi hmeet => hclosed i hi hmeet)
    intro i hi w hw
    exact (Path.visits_copy ..).mpr (h i hi w hw)

end Loop

/-- The host proof's modified target remains inside its recorded host window,
and lies within one child period of the prescribed requester window. -/
theorem host_target_bounds (a₀ b₀ a b e T : ℤ) (p₀ p : ℕ)
    (hmin : p₀ ≤ p) (horderA : a₀ ≤ a) (horderT : a ≤ T)
    (horderB : b₀ ≤ b)
    (hreq₁ : a + p < e) (hreq₂ : e ≤ b - p)
    (hleft : b₀ - a < p₀ + p) (hright : b - T < p + p₀)
    (hbase : b₀ < T + p₀) :
    let s := min (a + p) T
    let h := max e b₀
    a ≤ s ∧ s ≤ a + p ∧ s ≤ h ∧ h ≤ b ∧ e ≤ h ∧ h ≤ e + p ∧
      a₀ ≤ s ∧ s ≤ T ∧ b₀ ≤ h ∧ h < T + p₀ := by
  dsimp only
  have hs₁ : a ≤ min (a + p) T := le_min (by omega) horderT
  have hs₂ := min_le_left (a + (p : ℤ)) T
  have hs₃ := min_le_right (a + (p : ℤ)) T
  have hh₁ := le_max_left e b₀
  have hh₂ := le_max_right e b₀
  constructor
  · exact hs₁
  constructor
  · exact hs₂
  constructor
  · omega
  constructor
  · exact max_le (by omega) horderB
  constructor
  · exact hh₁
  constructor
  · exact max_le (by omega) (by omega)
  constructor
  · omega
  constructor
  · exact hs₃
  constructor
  · exact hh₂
  · exact max_lt (by omega) hbase

/-- The child-period loop used to attach each later requester at its modified
target; no recipient budget is consumed by this operation. -/
theorem request_attachment {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (p : ℕ)
    (per : ∀ x, A (x + p) = A x)
    {a e s h : ℤ} (hae : a ≤ e) (hsh : s ≤ h)
    (has : a ≤ s) (hsa : s ≤ a + p) (heh : e ≤ h) (hhe : h ≤ e + p)
    (hR : textWord A a e ∈ V) (hQ : textWord A s h ∈ V) :
    ∃ P : Path V (textWord A s h) (textWord A s h),
      P.cost = p ∧ P.Visits (textWord A a e) := by
  have heqR := textWord_translate A p per a e
  have heqQ := textWord_translate A p per s h
  obtain ⟨U, hUc, _⟩ := ordered_windows closed A letters hsh
    (show a + p ≤ e + p by omega) hsa hhe hQ (heqR.symm ▸ hR)
  obtain ⟨D, hDc, _⟩ := ordered_windows closed A letters
    (show a + p ≤ e + p by omega) (show s + p ≤ h + p by omega)
    (show a + p ≤ s + p by omega) (show e + p ≤ h + p by omega)
    (heqR.symm ▸ hR) (heqQ.symm ▸ hQ)
  refine ⟨(U.trans D).copy rfl heqQ, ?_, ?_⟩
  · simp only [Path.cost_copy, Path.cost_trans, hUc, hDc]
    omega
  · rw [← heqR]
    simp only [Path.visits_copy, Path.Visits]
    exact Or.inl (Path.visits_end U)

/-- The central cost-q excursion in the host text, for a nonempty ordered
list of later targets. It includes the initial requesters' whole vertical range
and ends with a contact shorter than the minimum child period. -/
theorem host_excursion {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (q p₀ : ℕ)
    (hp₀ : 0 < p₀) (per : ∀ x, A (x + q) = A x)
    (a₀ b₀ e₀ : ℤ) (he₀ : a₀ + p₀ < e₀) (heb : e₀ ≤ b₀)
    (hR : textWord A a₀ b₀ ∈ V)
    (s h : ℕ → ℤ) (hs : Monotone s) (hh : Monotone h) (n : ℕ)
    (hbounds : ∀ i ≤ n, a₀ ≤ s i ∧ s i ≤ a₀ + q ∧ s i ≤ h i ∧
      b₀ ≤ h i ∧ h i < a₀ + q + p₀)
    (hQ : ∀ i ≤ n, textWord A (s i) (h i) ∈ V) :
    ∃ P : Path V (textWord A a₀ e₀) (textWord A a₀ e₀),
      P.cost = q ∧ P.Visits (textWord A a₀ b₀) ∧
      (∀ e, e₀ ≤ e → e ≤ b₀ → P.Visits (textWord A a₀ e)) ∧
      (∀ i ≤ n, P.Visits (textWord A (s i) (h i))) ∧
      ∃ w, P.Visits w ∧ w.length < p₀ := by
  have hae : a₀ ≤ e₀ := by omega
  have hE : textWord A a₀ e₀ ∈ V := closed hR (textWord_infix A le_rfl hae heb)
  have heqE := textWord_translate A q per a₀ e₀
  obtain ⟨U, hUc, hUv⟩ := window_append closed A hae heb hR
  obtain ⟨B, hBc, _⟩ := ordered_windows closed A letters (le_trans hae heb)
    (hbounds 0 (by omega)).2.2.1 (hbounds 0 (by omega)).1
    (hbounds 0 (by omega)).2.2.2.1 hR (hQ 0 (by omega))
  obtain ⟨C, hCc, hCv⟩ := ordered_chain closed A letters s h hs hh n
    (fun i hi => (hbounds i hi).2.2.1) hQ
  obtain ⟨D, hDc, w, hDw, hwlen⟩ := ordered_windows closed A letters
    (hbounds n le_rfl).2.2.1 (show a₀ + q ≤ e₀ + q by omega)
    (hbounds n le_rfl).2.1 (show h n ≤ e₀ + q by
      have := (hbounds n le_rfl).2.2.2.2; omega) (hQ n le_rfl) (heqE.symm ▸ hE)
  refine ⟨(((U.trans B).trans C).trans D).copy rfl heqE, ?_, ?_, ?_, ?_, w, ?_, ?_⟩
  · simp only [Path.cost_copy, Path.cost_trans, hUc, hBc, hCc, hDc]
    have := hh (show 0 ≤ n by omega)
    have := (hbounds 0 (by omega)).2.2.2.1
    have := (hbounds n le_rfl).2.2.2.2
    omega
  · simp only [Path.visits_copy, Path.Visits]
    exact Or.inl (Or.inl (Or.inl (Path.visits_end U)))
  · intro e he he'
    simp only [Path.visits_copy, Path.Visits]
    exact Or.inl (Or.inl (Or.inl (hUv e he he')))
  · intro i hi
    simp only [Path.visits_copy, Path.Visits]
    exact Or.inl (Or.inr (hCv i hi))
  · simp only [Path.visits_copy, Path.Visits]
    exact Or.inr hDw
  · have := (hbounds n le_rfl).2.2.2.2
    omega

/-- The no-later-record case of the same host excursion. -/
theorem host_excursion_single {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (q p₀ : ℕ)
    (hp₀ : 0 < p₀) (per : ∀ x, A (x + q) = A x)
    (a₀ b₀ e₀ : ℤ) (he₀ : a₀ + p₀ < e₀) (heb : e₀ ≤ b₀)
    (hshort : b₀ < a₀ + q + p₀) (hR : textWord A a₀ b₀ ∈ V) :
    ∃ P : Path V (textWord A a₀ e₀) (textWord A a₀ e₀),
      P.cost = q ∧ P.Visits (textWord A a₀ b₀) ∧
      (∀ e, e₀ ≤ e → e ≤ b₀ → P.Visits (textWord A a₀ e)) ∧
      ∃ w, P.Visits w ∧ w.length < p₀ := by
  obtain ⟨P, hc, hr, hv, _, hs⟩ := host_excursion closed A letters q p₀ hp₀ per
    a₀ b₀ e₀ he₀ heb hR (fun _ => a₀) (fun _ => b₀)
    monotone_const monotone_const 0 (fun _ _ => ⟨le_rfl, by omega, by omega, le_rfl, hshort⟩)
    (fun _ _ => hR)
  exact ⟨P, hc, hr, hv, hs⟩

namespace Loop

variable {V : Set (List α)}

/-- Splice a family of request attachments into its host excursion. -/
theorem attach {ι : Type} (F : ι → Loop V) (I : Finset ι) (P : Loop V)
    (hmeet : ∀ i ∈ I, P.Meets (F i)) :
    ∃ Q : Loop V, Q.base = P.base ∧ Q.cost ≤ P.cost + ∑ i ∈ I, (F i).cost ∧
      (∀ w, P.Visits w → Q.Visits w) ∧
      (∀ i ∈ I, ∀ w, (F i).Visits w → Q.Visits w) := by
  obtain ⟨Q, hb, hc, hp, hclosed, _⟩ := saturate F I P
  refine ⟨Q, hb, hc, hp, ?_⟩
  intro i hi
  obtain ⟨w, hPw, hFw⟩ := hmeet i hi
  exact hclosed i hi ⟨w, hp w hPw, hFw⟩

/-- A short contact roots the whole closed excursion for its length. -/
theorem root_at (closed : SubstringClosed V) (P : Loop V) (w : List α)
    (hw : P.Visits w) :
    ∃ Q : Path V [] [], Q.cost = P.cost + w.length ∧
      ∀ v, P.Visits v → Q.Visits v := by
  obtain ⟨R, hRc, hRw⟩ := Path.root_loop closed w (P.path.mem_of_visits hw)
  obtain ⟨Q, hQc, hQv⟩ := R.splice P.path w hRw hw
  refine ⟨Q, ?_, fun v hv => (hQv v).mpr (Or.inr hv)⟩
  change Q.cost = R.cost + P.cost at hQc
  omega

/-- Host requests consume the host cost, the later attachments' costs, and
one unused minimum-child budget. The initial requesters remain visited. -/
theorem root_attachments {ι : Type} (closed : SubstringClosed V)
    (P : Loop V) (F : ι → Loop V) (I : Finset ι) (p₀ : ℕ)
    (hmeet : ∀ i ∈ I, P.Meets (F i))
    (hshort : ∃ w, P.Visits w ∧ w.length ≤ p₀) :
    ∃ Q : Path V [] [], Q.cost ≤ P.cost + (∑ i ∈ I, (F i).cost) + p₀ ∧
      (∀ w, P.Visits w → Q.Visits w) ∧
      (∀ i ∈ I, ∀ w, (F i).Visits w → Q.Visits w) := by
  obtain ⟨R, _, hRc, hp, hf⟩ := attach F I P hmeet
  obtain ⟨w, hw, hlen⟩ := hshort
  obtain ⟨Q, hQc, hQv⟩ := R.root_at closed w (hp w hw)
  exact ⟨Q, by omega, fun v hv => hQv v (hp v hv),
    fun i hi v hv => hQv v (hf i hi v hv)⟩

end Loop

end Hierarchical

end Superstring

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring

namespace Counts

variable {α : Type}

/-- A substring occurrence retains its starting position, so overlapping
occurrences are counted separately. -/
def Occurs (T s : List α) (x : ℕ) : Prop :=
  x + s.length ≤ T.length ∧ ∀ i : Fin s.length, T[x + i.val]? = s[i.val]?

instance [DecidableEq α] (T s : List α) (x : ℕ) : Decidable (Occurs T s x) :=
  inferInstanceAs (Decidable (_ ∧ ∀ _i : Fin s.length, _))

abbrev Occurrence (T s : List α) := {x : Fin (T.length + 1) // Occurs T s x.val}

def number [DecidableEq α] (T s : List α) : ℕ := Fintype.card (Occurrence T s)

theorem Occurs.at {T s : List α} {x i : ℕ} (h : Occurs T s x) (hi : i < s.length) :
    T[x + i]? = s[i]? := h.2 ⟨i, hi⟩

theorem Occurs.refl (s : List α) : Occurs s s 0 := by
  simp [Occurs]

theorem Occurs.trans {T r s : List α} {x j : ℕ}
    (hT : Occurs T r x) (hr : Occurs r s j) : Occurs T s (x + j) := by
  refine ⟨by have := hT.1; have := hr.1; omega, ?_⟩
  intro i
  have hi := i.isLt
  have hj : j + i.val < r.length := by have := hr.1; omega
  simpa only [Nat.add_assoc] using (hT.at hj).trans (hr.at hi)

theorem Occurs.infix {T s : List α} {x : ℕ} (h : Occurs T s x) : s <:+: T := by
  have heq : (T.drop x).take s.length = s := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < s.length
    · simpa only [List.getElem?_take, ite_eq_left hi, List.getElem?_drop] using h.at hi
    · simp only [List.getElem?_take, ite_eq_right hi]
      exact (List.getElem?_eq_none_iff.mpr (by omega)).symm
  rw [← heq]
  exact (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix

theorem Occurs.unique {T r s : List α} {x : ℕ}
    (hr : Occurs T r x) (hs : Occurs T s x) (hlen : r.length = s.length) : r = s := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < r.length
  · exact (hr.at hi).symm.trans (hs.at (hlen ▸ hi))
  · rw [List.getElem?_eq_none_iff.mpr (by omega),
      List.getElem?_eq_none_iff.mpr (by omega)]

/-- The inner occurrence is strictly inside the two single-letter mismatches. -/
def Block (A : ℤ → α) (s r : List α) (j : ℕ) : Prop :=
  1 ≤ j ∧ j + s.length < r.length ∧ Occurs r s j ∧
    (∀ h : Fin r.length, 0 < h.val → h.val + 1 < r.length →
      r[h.val]? = some (A ((h.val : ℤ) - j))) ∧
    r[0]? ≠ some (A (-(j : ℤ))) ∧
    r[r.length - 1]? ≠ some (A (((r.length - 1 : ℕ) : ℤ) - j))

instance [DecidableEq α] (A : ℤ → α) (s r : List α) (j : ℕ) : Decidable (Block A s r j) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ (∀ _h : Fin r.length, _) ∧ _ ∧ _))

abbrev BlockPosition (A : ℤ → α) (s r : List α) :=
  {j : Fin (r.length + 1) // Block A s r j.val}

def coefficient [DecidableEq α] (A : ℤ → α) (s r : List α) : ℕ := Fintype.card (BlockPosition A s r)


def blocking [DecidableEq α] (V : Finset (List α)) (A : ℤ → α) (s : List α) (m : List α → ℕ) : ℕ :=
  ∑ r ∈ V, coefficient A s r * m r

namespace Block

variable {A : ℤ → α} {T s r : List α} {j x : ℕ}

theorem length_pos (h : Block A s r j) : 0 < r.length := by have := h.2.1; omega

theorem left (h : Block A s r j) (hT : Occurs T r x) :
    T[x]? ≠ some (A ((x : ℤ) - ((x + j : ℕ) : ℤ))) := by
  have hh := hT.at h.length_pos
  simp only [Nat.add_zero] at hh
  rw [hh]
  have heq : (x : ℤ) - ((x + j : ℕ) : ℤ) = -(j : ℤ) := by omega
  rw [heq]
  exact h.2.2.2.2.1

theorem right (h : Block A s r j) (hT : Occurs T r x) :
    T[x + r.length - 1]? ≠ some (A (((x + r.length - 1 : ℕ) : ℤ) - ((x + j : ℕ) : ℤ))) := by
  have hp := h.length_pos
  have hh := hT.at (i := r.length - 1) (by omega)
  have heq : x + (r.length - 1) = x + r.length - 1 := by omega
  rw [heq] at hh
  rw [hh]
  have heq : ((x + r.length - 1 : ℕ) : ℤ) - ((x + j : ℕ) : ℤ) =
      ((r.length - 1 : ℕ) : ℤ) - j := by omega
  rw [heq]
  exact h.2.2.2.2.2

theorem inside (h : Block A s r j) (hT : Occurs T r x) (t : ℕ)
    (hxt : x < t) (htr : t < x + r.length - 1) :
    T[t]? = some (A ((t : ℤ) - ((x + j : ℕ) : ℤ))) := by
  have hd : t - x < r.length := by omega
  have hh := h.2.2.2.1 ⟨t - x, hd⟩ (show 0 < t - x by omega)
    (show t - x + 1 < r.length by omega)
  change r[t - x]? = some (A (((t - x : ℕ) : ℤ) - j)) at hh
  have ht := hT.at hd
  have hx : x + (t - x) = t := by omega
  rw [hx] at ht
  rw [ht, hh]
  have heq : ((t - x : ℕ) : ℤ) - j = (t : ℤ) - ((x + j : ℕ) : ℤ) := by omega
  rw [heq]


theorem boundaries_unique {r' : List α} {j' x' : ℕ}
    (h : Block A s r j) (h' : Block A s r' j')
    (hT : Occurs T r x) (hT' : Occurs T r' x') (hx : x + j = x' + j') :
    x = x' ∧ r.length = r'.length := by
  have h₁ := h.1
  have h₂ := h.2.1
  have h₁' := h'.1
  have h₂' := h'.2.1
  have hstart : x = x' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hm := h'.left hT'
      have he := h.inside hT x' hlt (by omega)
      apply hm
      simpa only [hx] using he
    · have hm := h.left hT
      have he := h'.inside hT' x hgt (by omega)
      apply hm
      simpa only [hx] using he
  refine ⟨hstart, ?_⟩
  subst x'
  have hj : j = j' := by omega
  subst j'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact h.right hT (h'.inside hT' (x + r.length - 1) (by omega) (by omega))
  · exact h'.right hT' (h.inside hT (x + r'.length - 1) (by omega) (by omega))

end Block

/-- A recorded bracketing word occurrence, and a counted placement inside it. -/
abbrev BlockWitness (V : Finset (List α)) (T : List α) (A : ℤ → α) (s : List α) :=
  Σ r : V, Occurrence T r.val × BlockPosition A s r.val

/-- The blocked-occurrence map. -/
def blockedOccurrence (V : Finset (List α)) (T : List α) (A : ℤ → α) (s : List α)
    (w : BlockWitness V T A s) : Occurrence T s :=
  let h := w.2.1.property.trans w.2.2.property.2.2.1
  ⟨⟨w.2.1.val.val + w.2.2.val.val, by have := h.1; omega⟩, h⟩

theorem blockedOccurrence_injective (V : Finset (List α)) (T : List α)
    (A : ℤ → α) (s : List α) : Function.Injective (blockedOccurrence V T A s) := by
  intro w w' heq
  rcases w with ⟨⟨r, hr⟩, ⟨⟨x, hxb⟩, hT⟩, ⟨⟨j, hjb⟩, hB⟩⟩
  rcases w' with ⟨⟨r', hr'⟩, ⟨⟨x', hxb'⟩, hT'⟩, ⟨⟨j', hjb'⟩, hB'⟩⟩
  have hxj := congrArg (fun o : Occurrence T s => o.val.val) heq
  change x + j = x' + j' at hxj
  obtain ⟨hxx, hlen⟩ := hB.boundaries_unique hB' hT hT' hxj
  change x = x' at hxx
  subst x'
  have hrr := hT.unique hT' hlen
  change r = r' at hrr
  subst r'
  have hjj : j = j' := by omega
  subst j'
  rfl

theorem card_blockWitness [DecidableEq α] (V : Finset (List α)) (T : List α)
    (A : ℤ → α) (s : List α) :
    Fintype.card (BlockWitness V T A s) = blocking V A s (number T) := by
  rw [blocking, Finset.sum_subtype V (fun _ => Iff.rfl)]
  simp only [BlockWitness, Fintype.card_sigma, Fintype.card_prod, number, coefficient]
  apply Finset.sum_congr rfl
  intro r _
  exact Nat.mul_comm _ _


theorem blocking_le_number [DecidableEq α] (V : Finset (List α)) (T : List α)
    (A : ℤ → α) (s : List α) : blocking V A s (number T) ≤ number T s := by
  rw [← card_blockWitness]
  exact Fintype.card_le_of_injective _ (blockedOccurrence_injective V T A s)

/-- Positivity of a coefficient forces the strict length dependency used in
both the descending recursion and its occurrence-bound induction. -/
theorem coefficient_pos_length [DecidableEq α] {A : ℤ → α} {s r : List α}
    (h : 0 < coefficient A s r) : s.length + 2 ≤ r.length := by
  obtain ⟨j⟩ := Fintype.card_pos_iff.mp h
  have h₁ := j.property.1
  have h₂ := j.property.2.1
  omega

/-- Agreement with a template at origin zero, as in every count rule. -/
def Matches (A : ℤ → α) (s : List α) : Prop :=
  ∀ i : Fin s.length, s[i.val]? = some (A i.val)

theorem periodic_nat_add {A : ℤ → α} {p : ℕ} (per : Function.Periodic A (p : ℤ))
    (t : ℕ) (x : ℤ) : A (x + (t * p : ℕ)) = A x := by
  simpa only [Nat.cast_mul] using per.nat_mul t x

theorem periodic_nat_sub {A : ℤ → α} {p : ℕ} (per : Function.Periodic A (p : ℤ))
    (t : ℕ) (x : ℤ) : A (x - (t * p : ℕ)) = A x := by
  simpa only [Nat.cast_mul] using (per.nat_mul t).sub_eq x

/-- All period-spaced prefixes of a rule's longer word are genuine occurrences. -/
theorem period_prefix {A : ℤ → α} {p t : ℕ} {v w : List α}
    (per : Function.Periodic A (p : ℤ)) (hv : Matches A v) (hw : Matches A w)
    (hlen : t * p + w.length ≤ v.length) : Occurs v w (t * p) := by
  refine ⟨hlen, ?_⟩
  intro i
  have hi := i.isLt
  have hit : t * p + i.val < v.length := by omega
  rw [hv ⟨t * p + i.val, hit⟩, hw i]
  have heq : ((t * p + i.val : ℕ) : ℤ) = (i.val : ℤ) + (t * p : ℕ) := by omega
  rw [heq, periodic_nat_add per]

/-- A bracketing placement of the long word generates every period-spaced
placement of its short prefix in the SAME bracketing word. -/
theorem Block.shift {A : ℤ → α} {p t j : ℕ} {v w r : List α}
    (h : Block A v r j) (per : Function.Periodic A (p : ℤ))
    (hv : Matches A v) (hw : Matches A w) (hlen : t * p + w.length ≤ v.length) :
    Block A w r (j + t * p) := by
  refine ⟨by have := h.1; omega, by have := h.2.1; omega,
    h.2.2.1.trans (period_prefix per hv hw hlen), ?_, ?_, ?_⟩
  · intro i hi hi'
    rw [h.2.2.2.1 i hi hi']
    have heq : (i.val : ℤ) - ((j + t * p : ℕ) : ℤ) =
        ((i.val : ℤ) - j) - (t * p : ℕ) := by omega
    rw [heq, periodic_nat_sub per]
  · have heq : -((j + t * p : ℕ) : ℤ) = -(j : ℤ) - (t * p : ℕ) := by omega
    rw [heq, periodic_nat_sub per]
    exact h.2.2.2.2.1
  · have heq : ((r.length - 1 : ℕ) : ℤ) - ((j + t * p : ℕ) : ℤ) =
        (((r.length - 1 : ℕ) : ℤ) - j) - (t * p : ℕ) := by omega
    rw [heq, periodic_nat_sub per]
    exact h.2.2.2.2.2

/-- Coefficient amplification for occurrence counts. -/
theorem coefficient_amplification [DecidableEq α] {A : ℤ → α} {p k : ℕ}
    {v w r : List α} (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    (hv : Matches A v) (hw : Matches A w) (hlen : w.length + k * p = v.length)
    (hb : 0 < coefficient A v r) : k + 1 ≤ coefficient A w r := by
  obtain ⟨j⟩ := Fintype.card_pos_iff.mp hb
  have hbound (t : Fin (k + 1)) : t.val * p + w.length ≤ v.length := by
    have ht := Nat.mul_le_mul_right p (show t.val ≤ k by omega)
    omega
  let f : Fin (k + 1) → BlockPosition A w r := fun t =>
    ⟨⟨j.val.val + t.val * p, by have := j.property.2.1; have := hbound t; omega⟩,
      j.property.shift per hv hw (hbound t)⟩
  have hinj : Function.Injective f := by
    intro t u heq
    have hh := congrArg (fun b : BlockPosition A w r => b.val.val) heq
    change j.val.val + t.val * p = j.val.val + u.val * p at hh
    apply Fin.ext
    nlinarith
  simpa only [Fintype.card_fin, coefficient] using Fintype.card_le_of_injective f hinj

/-- Restrict an occurrence through another containing occurrence. -/
theorem Occurs.factor {T r v : List α} {x y : ℕ}
    (hr : Occurs T r y) (hv : Occurs T v x) (hyx : y ≤ x)
    (hend : x + v.length ≤ y + r.length) : Occurs r v (x - y) := by
  refine ⟨by omega, ?_⟩
  intro i
  have hi := i.isLt
  have hridx : x - y + i.val < r.length := by omega
  have hh := hr.at hridx
  have heq : y + (x - y + i.val) = x + i.val := by omega
  rw [heq] at hh
  exact hh.symm.trans (hv.at hi)

/-- Retarget a block by a whole number of template periods, when the enlarged
inner occurrence still lies strictly between the same mismatch letters. -/
theorem Block.expand {A : ℤ → α} {p t j j' : ℕ} {v w r : List α}
    (h : Block A w r j) (per : Function.Periodic A (p : ℤ)) (hj : j = j' + t * p)
    (hj' : 1 ≤ j') (hlen : j' + v.length < r.length) (hr : Occurs r v j') :
    Block A v r j' := by
  have phase (z : ℤ) : A (z - j) = A (z - j') := by
    have heq : z - j = (z - j') - (t * p : ℕ) := by omega
    rw [heq, periodic_nat_sub per]
  refine ⟨hj', hlen, hr, ?_, ?_, ?_⟩
  · intro i hi hi'
    exact (h.2.2.2.1 i hi hi').trans (congrArg some (phase i.val))
  · have he := phase 0
    simp only [zero_sub] at he
    rw [← he]
    exact h.2.2.2.2.1
  · rw [← phase (r.length - 1 : ℕ)]
    exact h.2.2.2.2.2

/-- A blocking pair around a period-spaced short occurrence inside a matching
long word must lie outside that entire long occurrence, and blocks it too. -/
theorem Block.encloses_matching {A : ℤ → α} {T v w r : List α} {p t x y j : ℕ}
    (h : Block A w r j) (hr : Occurs T r y) (hv : Occurs T v x)
    (hmatch : Matches A v) (per : Function.Periodic A (p : ℤ))
    (hlen : t * p + w.length ≤ v.length) (hpos : y + j = x + t * p) :
    ∃ j', Block A v r j' ∧ y + j' = x := by
  have hj := h.1
  have hend := h.2.1
  have hleft : y < x := by
    by_contra hnot
    have hxy : x ≤ y := by omega
    have hiy : y - x < v.length := by omega
    have ht := hv.at hiy
    have heq : x + (y - x) = y := by omega
    rw [heq] at ht
    have hm := h.left hr
    apply hm
    rw [ht, hmatch ⟨y - x, hiy⟩]
    have heq : (y : ℤ) - ((y + j : ℕ) : ℤ) =
        ((y - x : ℕ) : ℤ) - (t * p : ℕ) := by omega
    rw [heq, periodic_nat_sub per]
  have hright : x + v.length ≤ y + r.length - 1 := by
    by_contra hnot
    have hxe : x ≤ y + r.length - 1 := by omega
    have hie : y + r.length - 1 - x < v.length := by omega
    have ht := hv.at hie
    have heq : x + (y + r.length - 1 - x) = y + r.length - 1 := by omega
    rw [heq] at ht
    have hm := h.right hr
    apply hm
    rw [ht, hmatch ⟨y + r.length - 1 - x, hie⟩]
    have heq : ((y + r.length - 1 : ℕ) : ℤ) - ((y + j : ℕ) : ℤ) =
        ((y + r.length - 1 - x : ℕ) : ℤ) - (t * p : ℕ) := by omega
    rw [heq, periodic_nat_sub per]
  refine ⟨x - y, h.expand (t := t) per (by omega) (by omega) (by omega)
    (hr.factor hv (by omega) (by omega)), by omega⟩

/-- A period-spaced suboccurrence of a fixed long occurrence. -/
def periodOccurrence {A : ℤ → α} {T v w : List α} {p k : ℕ}
    (per : Function.Periodic A (p : ℤ)) (hv : Matches A v) (hw : Matches A w)
    (hlen : w.length + k * p = v.length) (o : Occurrence T v) (t : Fin (k + 1)) :
    Occurrence T w :=
  let ht : t.val * p + w.length ≤ v.length := by
    have := Nat.mul_le_mul_right p (show t.val ≤ k by omega)
    omega
  let h := o.property.trans (period_prefix per hv hw ht)
  ⟨⟨o.val.val + t.val * p, by have := h.1; omega⟩, h⟩

theorem periodOccurrence_injective {A : ℤ → α} {T v w : List α} {p k : ℕ}
    (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    (hv : Matches A v) (hw : Matches A w)
    (hlen : w.length + k * p = v.length) (o : Occurrence T v) :
    Function.Injective (periodOccurrence per hv hw hlen o) := by
  intro t u heq
  have hh := congrArg (fun b : Occurrence T w => b.val.val) heq
  change o.val.val + t.val * p = o.val.val + u.val * p at hh
  apply Fin.ext
  nlinarith


def Unblocked (V : Finset (List α)) (T : List α) (A : ℤ → α) (v : List α)
    (o : Occurrence T v) : Prop := ∀ b, blockedOccurrence V T A v b ≠ o

theorem Unblocked.period_prefix {V : Finset (List α)} {A : ℤ → α}
    {T v w : List α} {p k : ℕ} (per : Function.Periodic A (p : ℤ))
    (hv : Matches A v) (hw : Matches A w) (hlen : w.length + k * p = v.length)
    {o : Occurrence T v} (ho : Unblocked V T A v o) (t : Fin (k + 1)) :
    Unblocked V T A w (periodOccurrence per hv hw hlen o t) := by
  intro b heq
  have hh := congrArg (fun q : Occurrence T w => q.val.val) heq
  change b.2.1.val.val + b.2.2.val.val = o.val.val + t.val * p at hh
  have hbound : t.val * p + w.length ≤ v.length := by
    have := Nat.mul_le_mul_right p (show t.val ≤ k by omega)
    omega
  obtain ⟨j', hj', hpos⟩ := b.2.2.property.encloses_matching b.2.1.property
    o.property hv per hbound hh
  let b' : BlockWitness V T A v := ⟨b.1, b.2.1,
    ⟨⟨j', by have := hj'.2.1; omega⟩, hj'⟩⟩
  apply ho b'
  apply Subtype.ext
  apply Fin.ext
  exact hpos


theorem unblocked_count_growth [DecidableEq α] {V : Finset (List α)} {A : ℤ → α}
    {T v w : List α} {p k : ℕ} (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    (hv : Matches A v) (hw : Matches A w) (hlen : w.length + k * p = v.length)
    (hmore : blocking V A v (number T) < number T v) :
    blocking V A w (number T) + k + 1 ≤ number T w := by
  classical
  have hex : ∃ o : Occurrence T v, Unblocked V T A v o := by
    by_contra hnot
    simp only [Unblocked, not_exists, not_forall, ne_eq, not_not] at hnot
    have hc := Fintype.card_le_of_surjective (blockedOccurrence V T A v) hnot
    rw [card_blockWitness] at hc
    change number T v ≤ _ at hc
    omega
  obtain ⟨o, ho⟩ := hex
  have hi := (blockedOccurrence_injective V T A w).sumElim
    (periodOccurrence_injective hp per hv hw hlen o)
    (fun b t => ho.period_prefix per hv hw hlen t b)
  have hc := Fintype.card_le_of_injective _ hi
  simpa only [Fintype.card_sum, card_blockWitness, Fintype.card_fin, number,
    Nat.add_assoc] using hc

/-- The functional depends monotonically only on words STRICTLY longer than
its inner word, although the triggered count operator itself need not be monotone. -/
theorem blocking_mono [DecidableEq α] {V : Finset (List α)} {A : ℤ → α}
    {s : List α} {m n : List α → ℕ}
    (hmn : ∀ r ∈ V, s.length < r.length → m r ≤ n r) :
    blocking V A s m ≤ blocking V A s n := by
  apply Finset.sum_le_sum
  intro r hr
  by_cases hz : coefficient A s r = 0
  · simp only [hz, Nat.zero_mul, le_refl]
  · have hlen := coefficient_pos_length (Nat.pos_of_ne_zero hz)
    exact Nat.mul_le_mul_left _ (hmn r hr (by omega))

/-- Retaining the increase at one summand while all other summands increase. -/
theorem sum_increase {ι : Type} [DecidableEq ι] (I : Finset ι) (a b : ι → ℕ)
    (h : ∀ i ∈ I, a i ≤ b i) {r : ι} (hr : r ∈ I) :
    (∑ i ∈ I, a i) + (b r - a r) ≤ ∑ i ∈ I, b i := by
  have he : ∑ i ∈ I.erase r, a i ≤ ∑ i ∈ I.erase r, b i :=
    Finset.sum_le_sum (fun i hi => h i (Finset.mem_of_mem_erase hi))
  have ha := Finset.sum_erase_add I a hr
  have hb := Finset.sum_erase_add I b hr
  have hrr := h r hr
  omega


theorem period_rule_lower_bound [DecidableEq α] {V : Finset (List α)}
    {A : ℤ → α} {T v w : List α} {p k : ℕ} {m : List α → ℕ}
    (hp : 0 < p) (hk : 0 < k) (per : Function.Periodic A (p : ℤ))
    (hv : Matches A v) (hw : Matches A w) (hlen : w.length + k * p = v.length)
    (hvV : v ∈ V) (hm : ∀ r ∈ V, w.length < r.length → m r ≤ number T r)
    (htrigger : blocking V A v m < m v) :
    blocking V A w m + k + 1 ≤ number T w := by
  have hkpos : 0 < k * p := Nat.mul_pos hk hp
  have hmv := hm v hvV (by omega)
  have hbw := blocking_mono (A := A) hm
  by_cases hmore : blocking V A v (number T) < number T v
  · have hgrowth := unblocked_count_growth hp per hv hw hlen hmore
    omega
  · have hcount := blocking_le_number V T A v
    have hstrict : blocking V A v m < blocking V A v (number T) := by omega
    have hex : ∃ r ∈ V, coefficient A v r * m r < coefficient A v r * number T r := by
      by_contra hnot
      push Not at hnot
      have hsum := Finset.sum_le_sum (fun r hr => hnot r hr)
      change blocking V A v (number T) ≤ blocking V A v m at hsum
      omega
    obtain ⟨r, hr, hprod⟩ := hex
    have hcoef : 0 < coefficient A v r := by
      by_contra hnot
      have hz : coefficient A v r = 0 := by omega
      simp only [hz, Nat.zero_mul] at hprod
      omega
    have hinc : m r < number T r := by
      by_contra hnot
      have hn : number T r ≤ m r := by omega
      have := Nat.mul_le_mul_left (coefficient A v r) hn
      omega
    have hamp := coefficient_amplification hp per hv hw hlen hcoef
    have hdiff : k + 1 ≤ coefficient A w r * number T r - coefficient A w r * m r := by
      have hh : coefficient A w r * (m r + 1) ≤ coefficient A w r * number T r :=
        Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_add, Nat.mul_one] at hh
      omega
    have hterms (r : List α) (hr : r ∈ V) :
        coefficient A w r * m r ≤ coefficient A w r * number T r := by
      by_cases hz : coefficient A w r = 0
      · simp only [hz, Nat.zero_mul, le_refl]
      · have hl := coefficient_pos_length (Nat.pos_of_ne_zero hz)
        exact Nat.mul_le_mul_left _ (hm r hr (by omega))
    have hs := sum_increase V (fun r => coefficient A w r * m r)
      (fun r => coefficient A w r * number T r) hterms hr
    change blocking V A w m + _ ≤ blocking V A w (number T) at hs
    have hl := blocking_le_number V T A w
    omega

theorem exists_occurs_of_infix {T s : List α} (h : s <:+: T) : ∃ x, Occurs T s x := by
  rcases h with ⟨a, b, rfl⟩
  rw [List.append_assoc]
  refine ⟨a.length, ⟨by simp only [List.length_append]; omega, ?_⟩⟩
  intro i
  simp only [List.getElem?_append, ite_eq_right (show ¬a.length + i.val < a.length by omega),
    Nat.add_sub_cancel_left, ite_eq_left i.isLt]

theorem number_pos_of_infix [DecidableEq α] {T s : List α} (h : s <:+: T) :
    0 < number T s := by
  obtain ⟨x, hx⟩ := exists_occurs_of_infix h
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨⟨x, by have := hx.1; omega⟩, hx⟩⟩

theorem Occurs.cons_tail {T w : List α} {c : α} {x : ℕ}
    (h : Occurs T (c :: w) x) : Occurs T w (x + 1) := by
  refine ⟨by have := h.1; simp only [List.length_cons] at this; omega, ?_⟩
  intro i
  have ht := h.at (i := i.val + 1) (by simp only [List.length_cons]; omega)
  simpa only [List.getElem?_cons_succ, Nat.add_right_comm, Nat.add_assoc] using ht

theorem Occurs.append_init {T w : List α} {c : α} {x : ℕ}
    (h : Occurs T (w ++ [c]) x) : Occurs T w x := by
  refine ⟨by have := h.1; simp only [List.length_append, List.length_singleton] at this; omega, ?_⟩
  intro i
  have ht := h.at (i := i.val) (by simp only [List.length_append, List.length_singleton]; omega)
  simpa only [List.getElem?_append, ite_eq_left i.isLt] using ht

/-- Disjointness of preceding-letter occurrence classes gives the first
extension lower bound in the count recursion. -/
theorem left_extension_number [DecidableEq α] (alphabet : Finset α) (T w : List α) :
    (∑ c ∈ alphabet, number T (c :: w)) ≤ number T w := by
  let f : (Σ c : alphabet, Occurrence T (c.val :: w)) → Occurrence T w := fun b =>
    ⟨⟨b.2.val.val + 1, by have := b.2.property.1; simp only [List.length_cons] at this; omega⟩,
      b.2.property.cons_tail⟩
  have hf : Function.Injective f := by
    intro b b' heq
    rcases b with ⟨⟨c, hc⟩, ⟨⟨x, hxb⟩, hx⟩⟩
    rcases b' with ⟨⟨d, hd⟩, ⟨⟨y, hyb⟩, hy⟩⟩
    have hh := congrArg (fun o : Occurrence T w => o.val.val) heq
    change x + 1 = y + 1 at hh
    have hxy : x = y := by omega
    subst y
    have hx0 := hx.at (i := 0) (by simp)
    have hy0 := hy.at (i := 0) (by simp)
    have hcd : c = d := by simpa only [List.getElem?_cons_zero, Option.some.injEq] using hx0.symm.trans hy0
    subst d
    rfl
  have hh := Fintype.card_le_of_injective f hf
  rw [Finset.sum_subtype alphabet (fun _ => Iff.rfl)]
  simpa only [Fintype.card_sigma, number] using hh

/-- The analogous following-letter occurrence classes are disjoint too. -/
theorem right_extension_number [DecidableEq α] (alphabet : Finset α) (T w : List α) :
    (∑ c ∈ alphabet, number T (w ++ [c])) ≤ number T w := by
  let f : (Σ c : alphabet, Occurrence T (w ++ [c.val])) → Occurrence T w := fun b =>
    ⟨b.2.val, b.2.property.append_init⟩
  have hf : Function.Injective f := by
    intro b b' heq
    rcases b with ⟨⟨c, hc⟩, ⟨⟨x, hxb⟩, hx⟩⟩
    rcases b' with ⟨⟨d, hd⟩, ⟨⟨y, hyb⟩, hy⟩⟩
    have hh := congrArg (fun o : Occurrence T w => o.val.val) heq
    change x = y at hh
    subst y
    have hx0 := hx.at (i := w.length) (by simp)
    have hy0 := hy.at (i := w.length) (by simp)
    have hcd : c = d := by
      simpa only [List.getElem?_append, lt_self_iff_false, ite_false,
        Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] using hx0.symm.trans hy0
    subst d
    rfl
  have hh := Fintype.card_le_of_injective f hf
  rw [Finset.sum_subtype alphabet (fun _ => Iff.rfl)]
  simpa only [Fintype.card_sigma, number] using hh

/-- Finite data of the preprocessed instance; geometric hypotheses are proved
for the actual input construction below, not hidden in this record. -/
structure Data (α : Type) where
  vertices : Finset (List α)
  required : Finset (List α)
  alphabet : Finset α

/-- The unique period-p text determined by the first p letters of v. Fallback
values are never used in a valid rule, since there 0 < p < length v. -/
def finiteText [Inhabited α] (v : List α) (p : ℕ) (x : ℤ) : α :=
  v[(x % (p : ℤ)).toNat]!

theorem finiteText_periodic [Inhabited α] (v : List α) (p : ℕ) :
    Function.Periodic (finiteText v p) (p : ℤ) := by
  intro x
  simp only [finiteText, Int.add_emod, Int.emod_self, add_zero, Int.emod_emod]

instance [DecidableEq α] (A : ℤ → α) (w : List α) : Decidable (Matches A w) :=
  inferInstanceAs (Decidable (∀ _i : Fin w.length, _))

/-- Equality of the longer counts preserves a blocking functional. -/
theorem blocking_congr [DecidableEq α] {V : Finset (List α)} {A : ℤ → α}
    {s : List α} {m n : List α → ℕ}
    (hmn : ∀ r ∈ V, s.length < r.length → m r = n r) :
    blocking V A s m = blocking V A s n := by
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hz : coefficient A s r = 0
  · simp only [hz, Nat.zero_mul]
  · have hlen := coefficient_pos_length (Nat.pos_of_ne_zero hz)
    rw [hmn r hr (by omega)]

namespace Data

variable [DecidableEq α] [Inhabited α]


def rule (D : Data α) (m : List α → ℕ) (w v : List α) (p k : ℕ) : ℕ :=
  let A := finiteText v p
  if 0 < p ∧ 0 < k ∧ w ≠ [] ∧ w.length + k * p = v.length ∧
      Matches A v ∧ Matches A w then
    if blocking D.vertices A v m < m v then blocking D.vertices A w m + k + 1 else 0
  else 0

/-- Finite enumeration of ALL rules; no least-period restriction is imposed. -/
def rules (D : Data α) (m : List α → ℕ) (w : List α) : ℕ :=
  D.vertices.sup fun v => (Finset.range (v.length + 1)).sup fun p =>
    (Finset.range (v.length + 1)).sup fun k => D.rule m w v p k

def left (D : Data α) (m : List α → ℕ) (w : List α) : ℕ :=
  ∑ c ∈ D.alphabet, if c :: w ∈ D.vertices then m (c :: w) else 0

def right (D : Data α) (m : List α → ℕ) (w : List α) : ℕ :=
  ∑ c ∈ D.alphabet, if w ++ [c] ∈ D.vertices then m (w ++ [c]) else 0


def step (D : Data α) (m : List α → ℕ) (w : List α) : ℕ :=
  if w ∈ D.vertices ∧ w ≠ [] then
    max (if w ∈ D.required then 1 else 0) (max (D.left m w) (max (D.right m w) (D.rules m w)))
  else 0

/-- Parallel triangular evaluation; the stabilization proof below shows that
this computes the exact descending recursion, rather than a different fixed point. -/
def stage (D : Data α) : ℕ → List α → ℕ
  | 0 => fun _ => 0
  | n + 1 => D.step (D.stage n)

def depth (D : Data α) : ℕ := D.vertices.sup List.length

def count (D : Data α) : List α → ℕ := D.stage (D.depth + 1)

theorem step_le_number (D : Data α) (T : List α)
    (hinput : ∀ w ∈ D.required, w <:+: T)
    {m : List α → ℕ} (hm : ∀ r ∈ D.vertices, m r ≤ number T r) (w : List α) :
    D.step m w ≤ number T w := by
  unfold step
  split
  · apply max_le
    · split
      · exact number_pos_of_infix (hinput _ ‹_›)
      · exact Nat.zero_le _
    · apply max_le
      · apply le_trans (Finset.sum_le_sum (g := fun c => number T (c :: w)) ?_)
          (left_extension_number D.alphabet T w)
        intro c _
        split
        · exact hm _ ‹_›
        · exact Nat.zero_le _
      · apply max_le
        · apply le_trans (Finset.sum_le_sum (g := fun c => number T (w ++ [c])) ?_)
            (right_extension_number D.alphabet T w)
          intro c _
          split
          · exact hm _ ‹_›
          · exact Nat.zero_le _
        · apply Finset.sup_le
          intro v hvV
          apply Finset.sup_le
          intro p _
          apply Finset.sup_le
          intro k _
          unfold rule
          dsimp only
          split
          · rename_i h
            obtain ⟨hp, hk, _, hlen, hv, hw⟩ := h
            split
            · exact period_rule_lower_bound hp hk (finiteText_periodic v p) hv hw hlen hvV
                (fun r hr _ => hm r hr) ‹_›
            · exact Nat.zero_le _
          · exact Nat.zero_le _
  · exact Nat.zero_le _

/-- Every intermediate computational stage, not only the final counts, is bounded
by the occurrence counts of EVERY common superstring. -/
theorem stage_le_number (D : Data α) (T : List α)
    (hinput : ∀ w ∈ D.required, w <:+: T) (n : ℕ) (w : List α) :
    D.stage n w ≤ number T w := by
  induction n generalizing w with
  | zero => exact Nat.zero_le _
  | succ n ih => exact D.step_le_number T hinput (fun r _ => ih r) w

/-- A rule value depends only on strictly longer words. -/
theorem rule_congr (D : Data α) {m n : List α → ℕ} {w v : List α} (p k : ℕ)
    (hvV : v ∈ D.vertices)
    (hmn : ∀ r ∈ D.vertices, w.length < r.length → m r = n r) :
    D.rule m w v p k = D.rule n w v p k := by
  unfold rule
  dsimp only
  by_cases hvalid : 0 < p ∧ 0 < k ∧ w ≠ [] ∧ w.length + k * p = v.length ∧
      Matches (finiteText v p) v ∧ Matches (finiteText v p) w
  · rw [ite_eq_left hvalid, ite_eq_left hvalid]
    obtain ⟨hp, hk, _, hlen, _, _⟩ := hvalid
    have hkp : 0 < k * p := Nat.mul_pos hk hp
    have hlong : w.length < v.length := by omega
    have hmV := hmn v hvV hlong
    have hbV := blocking_congr (A := finiteText v p)
      (fun r hr hvr => hmn r hr (lt_trans hlong hvr))
    have hbW := blocking_congr (A := finiteText v p) hmn
    rw [hmV, hbV, hbW]
  · rw [ite_eq_right hvalid, ite_eq_right hvalid]

/-- Triangularity of the complete finite operator. -/
theorem step_congr (D : Data α) {m n : List α → ℕ} {w : List α}
    (hmn : ∀ r ∈ D.vertices, w.length < r.length → m r = n r) :
    D.step m w = D.step n w := by
  have hl : D.left m w = D.left n w := by
    apply Finset.sum_congr rfl
    intro c _
    split
    · rw [hmn _ ‹_› (by simp)]
    · rfl
  have hr : D.right m w = D.right n w := by
    apply Finset.sum_congr rfl
    intro c _
    split
    · rw [hmn _ ‹_› (by simp)]
    · rfl
  have hs : D.rules m w = D.rules n w := by
    apply Finset.sup_congr rfl
    intro v hv
    apply Finset.sup_congr rfl
    intro p _
    apply Finset.sup_congr rfl
    intro k _
    exact D.rule_congr p k hv hmn
  simp only [step, hl, hr, hs]

/-- After n stages every word less than n levels from the top has stabilized. -/
theorem stage_stable (D : Data α) (n : ℕ) (w : List α)
    (hdepth : D.depth < w.length + n) : D.stage (n + 1) w = D.stage n w := by
  induction n generalizing w with
  | zero =>
    have hnot : w ∉ D.vertices := by
      intro hw
      have hle : w.length ≤ D.depth := Finset.le_sup hw
      omega
    simp only [stage, step, hnot, false_and, ite_false]
  | succ n ih =>
    change D.step (D.stage (n + 1)) w = D.step (D.stage n) w
    apply D.step_congr
    intro r _ hwr
    exact ih r (by omega)

/-- The actual counts satisfy exactly the minimal-bound recursion. -/
theorem count_fixed (D : Data α) (w : List α) : D.step D.count w = D.count w := by
  exact D.stage_stable (D.depth + 1) w (by omega)


theorem count_le_number (D : Data α) (T : List α)
    (hinput : ∀ w ∈ D.required, w <:+: T) (w : List α) : D.count w ≤ number T w :=
  D.stage_le_number T hinput _ w

theorem count_zero (D : Data α) (w : List α)
    (hw : w ∉ D.vertices ∨ w = []) : D.count w = 0 := by
  rw [← D.count_fixed w]
  unfold step
  split
  · rename_i hvalid
    rcases hw with hw | hw
    · exact (hw hvalid.1).elim
    · exact (hvalid.2 hw).elim
  · rfl

theorem required_le_count (D : Data α) {w : List α}
    (hw : w ∈ D.vertices) (hne : w ≠ []) (hr : w ∈ D.required) :
    1 ≤ D.count w := by
  rw [← D.count_fixed w]
  rw [step, ite_eq_left ⟨hw, hne⟩, ite_eq_left hr]
  exact le_max_left _ _

theorem left_le_count (D : Data α) {w : List α}
    (hw : w ∈ D.vertices) (hne : w ≠ []) : D.left D.count w ≤ D.count w := by
  rw [← D.count_fixed w]
  rw [step, ite_eq_left ⟨hw, hne⟩]
  exact le_trans (le_max_left _ _) (le_max_right _ _)

theorem right_le_count (D : Data α) {w : List α}
    (hw : w ∈ D.vertices) (hne : w ≠ []) : D.right D.count w ≤ D.count w := by
  rw [← D.count_fixed w]
  rw [step, ite_eq_left ⟨hw, hne⟩]
  exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))

theorem left_count (D : Data α) (w : List α) :
    D.left D.count w = ∑ c ∈ D.alphabet, D.count (c :: w) := by
  apply Finset.sum_congr rfl
  intro c _
  split
  · rfl
  · exact (D.count_zero _ (Or.inl ‹_›)).symm

theorem right_count (D : Data α) (w : List α) :
    D.right D.count w = ∑ c ∈ D.alphabet, D.count (w ++ [c]) := by
  apply Finset.sum_congr rfl
  intro c _
  split
  · rfl
  · exact (D.count_zero _ (Or.inl ‹_›)).symm

theorem rule_le_count (D : Data α) {w v : List α} {p k : ℕ}
    (hw : w ∈ D.vertices) (hne : w ≠ [])
    (hv : v ∈ D.vertices) (hp : p ≤ v.length) (hk : k ≤ v.length) :
    D.rule D.count w v p k ≤ D.count w := by
  have hsup : D.rule D.count w v p k ≤ D.rules D.count w := by
    apply le_trans (Finset.le_sup (f := fun k => D.rule D.count w v p k)
      (show k ∈ Finset.range (v.length + 1) from Finset.mem_range.mpr (by omega)))
    apply le_trans (Finset.le_sup (f := fun p => (Finset.range (v.length + 1)).sup
      (fun k => D.rule D.count w v p k))
      (show p ∈ Finset.range (v.length + 1) from Finset.mem_range.mpr (by omega)))
    have h := Finset.le_sup (f := fun v => (Finset.range (v.length + 1)).sup
      (fun p => (Finset.range (v.length + 1)).sup (fun k => D.rule D.count w v p k))) hv
    exact h
  rw [← D.count_fixed w]
  rw [step, ite_eq_left ⟨hw, hne⟩]
  exact le_trans hsup
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))

end Data

/-- The finite rule representative is the original two-sided text, not merely
its forward restriction. -/
theorem finiteText_eq [Inhabited α] {A : ℤ → α} {v : List α} {p : ℕ}
    (hp : 0 < p) (hper : Function.Periodic A (p : ℤ))
    (hm : Matches A v) (hlen : p ≤ v.length) : finiteText v p = A := by
  funext x
  have hpz : (0 : ℤ) < p := by omega
  have hmod0 := Int.emod_nonneg x (show (p : ℤ) ≠ 0 by omega)
  have hmodlt := Int.emod_lt_of_pos x hpz
  have hi : (x % (p : ℤ)).toNat < v.length := by omega
  have hh := hm ⟨(x % (p : ℤ)).toNat, hi⟩
  have he : (((x % (p : ℤ)).toNat : ℕ) : ℤ) = x % p := by omega
  change v[(x % (p : ℤ)).toNat]? = some (A (((x % (p : ℤ)).toNat : ℕ) : ℤ)) at hh
  rw [he, Hierarchical.periodic_emod A (p : ℤ) hper x] at hh
  unfold finiteText
  exact List.getElem!_of_getElem? hh

namespace Data
variable [DecidableEq α] [Inhabited α]

/-- Every period rule holds for the computed counts. -/
theorem period_rule (D : Data α) {A : ℤ → α} {w v : List α} {p k : ℕ}
    (hp : 0 < p) (hk : 0 < k) (hper : Function.Periodic A (p : ℤ))
    (hw : w ∈ D.vertices) (hne : w ≠ []) (hv : v ∈ D.vertices)
    (hmv : Matches A v) (hmw : Matches A w)
    (hlen : w.length + k * p = v.length)
    (htrigger : blocking D.vertices A v D.count < D.count v) :
    blocking D.vertices A w D.count + k + 1 ≤ D.count w := by
  have hkp : p ≤ k * p := by nlinarith
  have hklen : k ≤ v.length := by nlinarith
  have hplen : p ≤ v.length := by omega
  have heq := finiteText_eq hp hper hmv hplen
  have hr := D.rule_le_count hw hne hv hplen hklen
  have hvalid : 0 < p ∧ 0 < k ∧ w ≠ [] ∧ w.length + k * p = v.length ∧
      Matches A v ∧ Matches A w := ⟨hp, hk, hne, hlen, hmv, hmw⟩
  simpa only [rule, heq, ite_eq_left hvalid, ite_eq_left htrigger] using hr

end Data

/-- Nonempty occurrences inject into the positions of the ambient word. -/
theorem number_le_length [DecidableEq α] {T s : List α} (hs : s ≠ []) : number T s ≤ T.length := by
  classical
  let f : Occurrence T s → Fin T.length := fun o =>
    ⟨o.val.val, by have := o.property.1; have := List.length_pos_iff.mpr hs; omega⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun z : Fin T.length => z.val) h
  simpa only [number, Fintype.card_fin] using Fintype.card_le_of_injective f hf

/-- Counts of one-letter occurrences, independently of how large the alphabet
of labels is, sum to at most the symbol length of the ambient word. -/
theorem singleton_number_sum [DecidableEq α] (C : Finset α) (T : List α) :
    (∑ c ∈ C, number T [c]) ≤ T.length := by
  let f : (Σ c : C, Occurrence T [c.val]) → Fin T.length := fun b =>
    ⟨b.2.val.val, by have := b.2.property.1; simp only [List.length_singleton] at this; omega⟩
  have hf : Function.Injective f := by
    intro b b' heq
    rcases b with ⟨⟨c, hc⟩, ⟨⟨x, hxb⟩, hx⟩⟩
    rcases b' with ⟨⟨d, hd⟩, ⟨⟨y, hyb⟩, hy⟩⟩
    have hh := congrArg Fin.val heq
    change x = y at hh
    subst y
    have hcd : c = d := by
      have hh := (hx.at (i := 0) (by simp)).symm.trans (hy.at (i := 0) (by simp))
      simpa only [List.getElem?_cons_zero, Option.some.injEq] using hh
    subst d
    rfl
  have hh := Fintype.card_le_of_injective f hf
  rw [Finset.sum_subtype C (fun _ => Iff.rfl)]
  simpa only [Fintype.card_sigma, number, Fintype.card_fin] using hh

namespace Data
variable [DecidableEq α] [Inhabited α]

def weight (D : Data α) : ℕ := ∑ c ∈ D.alphabet, D.count [c]

theorem weight_le_length (D : Data α) (T : List α)
    (hinput : ∀ w ∈ D.required, w <:+: T) : D.weight ≤ T.length :=
  le_trans (Finset.sum_le_sum (fun _ _ => D.count_le_number T hinput _))
    (singleton_number_sum D.alphabet T)

end Data

end Counts

end Superstring

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring

namespace Input

variable {α : Type} [DecidableEq α]

/-- Quadratic substring enumeration, with boundaries represented explicitly. -/
def subwords (s : List α) : Finset (List α) :=
  (Finset.range (s.length + 1)).biUnion fun i =>
    (Finset.range (s.length + 1)).image fun n => (s.drop i).take n

theorem mem_subwords {w s : List α} : w ∈ subwords s ↔ w <:+: s := by
  constructor
  · intro hw
    obtain ⟨i, _, hw⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hw
    exact (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix
  · rintro ⟨a, b, rfl⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨a.length, Finset.mem_range.mpr (by simp only [List.length_append]; omega), ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨w.length, Finset.mem_range.mpr (by simp only [List.length_append]; omega), ?_⟩
    simp

/-- Deleting empty, duplicate and properly contained input words. -/
def core (S : List (List α)) : Finset (List α) :=
  S.toFinset.filter fun s => s ≠ [] ∧ ∀ t ∈ S, s <:+: t → t = s

theorem mem_core {S : List (List α)} {s : List α} :
    s ∈ core S ↔ s ∈ S ∧ s ≠ [] ∧ ∀ t ∈ S, s <:+: t → t = s := by
  simp only [core, Finset.mem_filter, List.mem_toFinset]

theorem core_cover {S : List (List α)} {s : List α} (hs : s ∈ S) (hne : s ≠ []) :
    ∃ t ∈ core S, s <:+: t := by
  let F := S.toFinset.filter (fun t => s <:+: t)
  have hF : F.Nonempty := ⟨s, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hs, List.infix_refl s⟩⟩
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image F List.length hF
  obtain ⟨htS, hst⟩ := Finset.mem_filter.mp ht
  refine ⟨t, mem_core.mpr ⟨List.mem_toFinset.mp htS, ?_, ?_⟩, hst⟩
  · intro ht0
    subst t
    exact hne (List.eq_nil_of_length_eq_zero (by have := hst.length_le; simpa using this))
  · intro u hu htu
    apply (htu.eq_of_length_le ?_).symm
    exact hmax u (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hu, hst.trans htu⟩)

def vertices (S : List (List α)) : Finset (List α) :=
  insert [] (S.toFinset.biUnion subwords)

theorem mem_vertices {S : List (List α)} {w : List α} :
    w ∈ vertices S ↔ w = [] ∨ ∃ s ∈ S, w <:+: s := by
  simp only [vertices, Finset.mem_insert, Finset.mem_biUnion, List.mem_toFinset,
    mem_subwords]

def alphabet (S : List (List α)) : Finset α := S.flatten.toFinset

def data (S : List (List α)) : Counts.Data α := ⟨vertices S, core S, alphabet S⟩

theorem closed (S : List (List α)) : Hierarchical.SubstringClosed (vertices S : Set (List α)) := by
  intro s hs w hws
  rcases mem_vertices.mp hs with rfl | ⟨t, ht, hst⟩
  · apply mem_vertices.mpr
    left
    exact List.eq_nil_of_length_eq_zero (by have := hws.length_le; simpa using this)
  · exact mem_vertices.mpr (Or.inr ⟨t, ht, hws.trans hst⟩)

theorem letter_mem {S : List (List α)} {w : List α} (hw : w ∈ vertices S)
    {c : α} (hc : c ∈ w) : c ∈ alphabet S := by
  rcases mem_vertices.mp hw with rfl | ⟨s, hs, hws⟩
  · simp only [List.not_mem_nil] at hc
  · exact List.mem_toFinset.mpr (List.mem_flatten.mpr ⟨s, hs, hws.sublist.subset hc⟩)

theorem required_mem {S : List (List α)} {w : List α} (hw : w ∈ core S) :
    w ∈ vertices S := mem_vertices.mpr (Or.inr ⟨w, (mem_core.mp hw).1, List.infix_refl w⟩)

theorem core_superstring_iff (S : List (List α)) (T : List α) :
    (∀ s ∈ core S, s <:+: T) ↔ ∀ s ∈ S, s <:+: T := by
  constructor
  · intro h s hs
    by_cases hnil : s = []
    · subst s
      exact List.nil_infix
    · obtain ⟨t, ht, hst⟩ := core_cover hs hnil
      exact hst.trans (h t ht)
  · intro h s hs
    exact h s (mem_core.mp hs).1

end Input

theorem concatenation_superstring (S : Instance) : IsCommonSuperstring S S.flatten :=
  fun _ hs => List.infix_of_mem_flatten hs

theorem feasible_lengths_nonempty (S : Instance) :
    {n : ℕ | ∃ T : Word, IsCommonSuperstring S T ∧ T.length = n}.Nonempty :=
  ⟨S.flatten.length, S.flatten, concatenation_superstring S, rfl⟩

/-- The actual computed lower bound is bounded by the unrestricted optimum. -/
theorem weight_le_opt (S : Instance) : (Input.data S).weight ≤ opt S := by
  unfold opt
  apply le_csInf (feasible_lengths_nonempty S)
  rintro n ⟨T, hT, rfl⟩
  apply Counts.Data.weight_le_length
  exact (Input.core_superstring_iff S T).mpr hT


theorem input_count_le_total (S : Instance) {w : Word} (hw : w ≠ []) :
    (Input.data S).count w ≤ S.flatten.length :=
  le_trans ((Input.data S).count_le_number S.flatten
    ((Input.core_superstring_iff S S.flatten).mpr (concatenation_superstring S)) w)
    (Counts.number_le_length hw)

namespace Counts.Data
variable {α : Type} [DecidableEq α] [Inhabited α]

/-- The hypotheses supplied by the actual all-substrings input construction. -/
structure WellFormed (D : Counts.Data α) : Prop where
  empty_mem : [] ∈ D.vertices
  closed : Hierarchical.SubstringClosed (D.vertices : Set (List α))
  letters : ∀ s ∈ D.vertices, ∀ c ∈ s, c ∈ D.alphabet

omit [Inhabited α] in
theorem input_wellFormed (S : List (List α)) : (Input.data S).WellFormed :=
  ⟨Finset.mem_insert_self _ _, Input.closed S, fun _ hs _ hc => Input.letter_mem hs hc⟩

theorem mem_of_count_ne_zero (D : Data α) {s : List α} (hs : D.count s ≠ 0) :
    s ∈ D.vertices := by
  by_contra h
  exact hs (D.count_zero _ (Or.inl h))

theorem left_bound (D : Data α) (hD : D.WellFormed) {s : List α} (hs : s ≠ []) :
    (∑ c ∈ D.alphabet, D.count (c :: s)) ≤ D.count s := by
  by_cases hmem : s ∈ D.vertices
  · rw [← D.left_count]
    exact D.left_le_count hmem hs
  · have hz : ∀ c, D.count (c :: s) = 0 := by
      intro c
      apply D.count_zero
      left
      intro hcs
      exact hmem (hD.closed hcs (List.suffix_cons c s).isInfix)
    simp only [hz, Finset.sum_const_zero, Nat.zero_le]

theorem right_bound (D : Data α) (hD : D.WellFormed) {s : List α} (hs : s ≠ []) :
    (∑ c ∈ D.alphabet, D.count (s ++ [c])) ≤ D.count s := by
  by_cases hmem : s ∈ D.vertices
  · rw [← D.right_count]
    exact D.right_le_count hmem hs
  · have hz : ∀ c, D.count (s ++ [c]) = 0 := by
      intro c
      apply D.count_zero
      left
      intro hsc
      exact hmem (hD.closed hsc (List.prefix_append s [c]).isInfix)
    simp only [hz, Finset.sum_const_zero, Nat.zero_le]


def up (D : Data α) (s : List α) : ℕ :=
  D.count s - ∑ c ∈ D.alphabet, D.count (c :: s)

def down (D : Data α) (s : List α) : ℕ :=
  D.count s - ∑ c ∈ D.alphabet, D.count (s ++ [c])

theorem up_add (D : Data α) (hD : D.WellFormed) {s : List α} (hs : s ≠ []) :
    D.up s + ∑ c ∈ D.alphabet, D.count (c :: s) = D.count s :=
  Nat.sub_add_cancel (D.left_bound hD hs)

theorem down_add (D : Data α) (hD : D.WellFormed) {s : List α} (hs : s ≠ []) :
    D.down s + ∑ c ∈ D.alphabet, D.count (s ++ [c]) = D.count s :=
  Nat.sub_add_cancel (D.right_bound hD hs)

/-- Balance is an exact natural-number equality; no truncated subtraction is
silently cancelled without the extension inequalities. -/
theorem balanced (D : Data α) (hD : D.WellFormed) (s : List α) :
    D.up s + ∑ c ∈ D.alphabet, D.down (c :: s) =
      D.down s + ∑ c ∈ D.alphabet, D.up (s ++ [c]) := by
  have hd := Finset.sum_congr rfl (fun c (_hc : c ∈ D.alphabet) =>
    D.down_add hD (s := c :: s) (List.cons_ne_nil c s))
  have hu := Finset.sum_congr rfl (fun c (_hc : c ∈ D.alphabet) =>
    D.up_add hD (s := s ++ [c]) (by simp))
  rw [Finset.sum_add_distrib] at hd hu
  have heq : (∑ c ∈ D.alphabet, ∑ d ∈ D.alphabet, D.count ((c :: s) ++ [d])) =
      ∑ c ∈ D.alphabet, ∑ d ∈ D.alphabet, D.count (d :: (s ++ [c])) := by
    rw [Finset.sum_comm]
    rfl
  rw [heq] at hd
  by_cases hs : s = []
  · subst s
    have hz : D.count [] = 0 := D.count_zero _ (Or.inr rfl)
    have huz : D.up [] = 0 := by simp only [up, hz, Nat.zero_sub]
    have hdz : D.down [] = 0 := by simp only [down, hz, Nat.zero_sub]
    rw [huz, hdz]
    simp only [List.nil_append, zero_add] at hd hu ⊢
    omega
  · have hl := D.up_add hD hs
    have hr := D.down_add hD hs
    omega

/-- Reindex all left extensions by their unique first letter and suffix. -/
theorem sum_left_all (D : Data α) (hD : D.WellFormed) :
    (∑ s ∈ D.vertices, ∑ c ∈ D.alphabet, D.count (c :: s)) =
      ∑ r ∈ D.vertices, D.count r := by
  rw [← Finset.sum_product D.vertices D.alphabet (fun a => D.count (a.2 :: a.1))]
  apply Finset.sum_bij_ne_zero (fun a _ _ => a.2 :: a.1)
  · intro a _ ha
    exact D.mem_of_count_ne_zero ha
  · intro a _ _ b _ _ hab
    obtain ⟨hc, hs⟩ := List.cons.inj hab
    exact Prod.ext hs hc
  · intro r hr hz
    cases r with
    | nil => exact (hz (D.count_zero _ (Or.inr rfl))).elim
    | cons c s =>
      have hs : s ∈ D.vertices := hD.closed hr (List.suffix_cons c s).isInfix
      have hc : c ∈ D.alphabet := hD.letters _ hr c (List.mem_cons_self ..)
      exact ⟨(s, c), Finset.mem_product.mpr ⟨hs, hc⟩, hz, rfl⟩
  · intros
    rfl

/-- The dual reindexing by prefix and final letter. -/
theorem sum_right_all (D : Data α) (hD : D.WellFormed) :
    (∑ s ∈ D.vertices, ∑ c ∈ D.alphabet, D.count (s ++ [c])) =
      ∑ r ∈ D.vertices, D.count r := by
  rw [← Finset.sum_product D.vertices D.alphabet (fun a => D.count (a.1 ++ [a.2]))]
  apply Finset.sum_bij_ne_zero (fun a _ _ => a.1 ++ [a.2])
  · intro a _ ha
    exact D.mem_of_count_ne_zero ha
  · intro a _ _ b _ _ hab
    have hs := congrArg List.dropLast hab
    simp only [List.dropLast_concat] at hs
    have hc : a.2 = b.2 := by
      rw [hs] at hab
      simpa only [List.append_cancel_left_eq, List.cons.injEq, and_true] using hab
    exact Prod.ext hs hc
  · intro r hr hz
    have hne : r ≠ [] := by intro he; subst r; exact hz (D.count_zero _ (Or.inr rfl))
    let s := r.dropLast
    let c := r.getLast hne
    have hrsc : s ++ [c] = r := List.dropLast_append_getLast hne
    have hs : s ∈ D.vertices := hD.closed hr (hrsc ▸ (List.prefix_append s [c]).isInfix)
    have hc : c ∈ D.alphabet := hD.letters r hr c (hrsc ▸ (by simp))
    refine ⟨(s, c), Finset.mem_product.mpr ⟨hs, hc⟩, ?_, hrsc⟩
    simpa only [hrsc] using hz
  · intros
    rfl

/-- Telescoping of all actual up-edge multiplicities. -/
theorem total_up (D : Data α) (hD : D.WellFormed) :
    (∑ s ∈ D.vertices, D.up s) = D.weight := by
  have hm := Finset.sum_erase_add D.vertices D.count hD.empty_mem
  have hl := Finset.sum_erase_add D.vertices
    (fun s => ∑ c ∈ D.alphabet, D.count (c :: s)) hD.empty_mem
  have hu := Finset.sum_erase_add D.vertices D.up hD.empty_mem
  have hh := Finset.sum_congr rfl (fun s (hs : s ∈ D.vertices.erase []) =>
    D.up_add hD (Finset.mem_erase.mp hs).1)
  rw [Finset.sum_add_distrib] at hh
  have hz : D.count [] = 0 := D.count_zero _ (Or.inr rfl)
  have huz : D.up [] = 0 := by simp only [up, hz, Nat.zero_sub]
  rw [D.sum_left_all hD] at hl
  change _ + D.weight = _ at hl
  omega

theorem total_down (D : Data α) (hD : D.WellFormed) :
    (∑ s ∈ D.vertices, D.down s) = D.weight := by
  have hm := Finset.sum_erase_add D.vertices D.count hD.empty_mem
  have hl := Finset.sum_erase_add D.vertices
    (fun s => ∑ c ∈ D.alphabet, D.count (s ++ [c])) hD.empty_mem
  have hd := Finset.sum_erase_add D.vertices D.down hD.empty_mem
  have hh := Finset.sum_congr rfl (fun s (hs : s ∈ D.vertices.erase []) =>
    D.down_add hD (Finset.mem_erase.mp hs).1)
  rw [Finset.sum_add_distrib] at hh
  have hz : D.count [] = 0 := D.count_zero _ (Or.inr rfl)
  have hdz : D.down [] = 0 := by simp only [down, hz, Nat.zero_sub]
  rw [D.sum_right_all hD] at hl
  change _ + D.weight = _ at hl
  omega

end Counts.Data

end Superstring

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring

namespace Hierarchical

variable {α : Type}

/-- The least positive period is explicit, as required for primitive groups. -/
structure Primitive (A : ℤ → α) (p : ℕ) : Prop where
  positive : 0 < p
  periodic : Function.Periodic A (p : ℤ)
  least : ∀ n : ℕ, 0 < n → Function.Periodic A (n : ℤ) → p ≤ n

/-- Existence from any positive turn length. -/
theorem exists_primitive {A : ℤ → α} {P : ℕ} (hP : 0 < P)
    (hper : Function.Periodic A (P : ℤ)) : ∃ p, Primitive A p := by
  classical
  have hex : ∃ n : ℕ, 0 < n ∧ Function.Periodic A (n : ℤ) := ⟨P, hP, hper⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro n hn hnp
  exact Nat.find_min' hex ⟨hn, hnp⟩

/-- All translational symmetries, including negative ones, are precisely the
multiples of the primitive period. -/
theorem Primitive.period_iff_dvd {A : ℤ → α} {p : ℕ} (h : Primitive A p) (d : ℤ) :
    Function.Periodic A d ↔ (p : ℤ) ∣ d := by
  constructor
  · intro hd
    have hpz : (0 : ℤ) < p := by have := h.positive; omega
    have hm0 := Int.emod_nonneg d (show (p : ℤ) ≠ 0 by omega)
    have hml := Int.emod_lt_of_pos d hpz
    have hmod : Function.Periodic A (d % (p : ℤ)) := by
      have hh := hd.sub_period (h.periodic.int_mul (d / p))
      have he : d - (d / (p : ℤ)) * p = d % p := by
        have := Int.emod_add_ediv_mul d (p : ℤ)
        omega
      simpa only [Int.cast_id, he] using hh
    have hmz : d % (p : ℤ) = 0 := by
      by_contra hz
      have hnat : 0 < (d % (p : ℤ)).toNat := by omega
      have he : (((d % (p : ℤ)).toNat : ℕ) : ℤ) = d % p := by omega
      have hh := h.least _ hnat (he ▸ hmod)
      omega
    exact Int.dvd_of_emod_eq_zero hmz
  · rintro ⟨q, rfl⟩
    simpa only [Int.cast_id, mul_comm] using h.periodic.int_mul q

/-- There is exactly one identical full-text alignment in a primitive turn. -/
theorem Primitive.alignment_unique {A : ℤ → α} {p : ℕ} (h : Primitive A p)
    {i j : ℤ} (hi : 0 ≤ i) (hip : i < p) (hj : 0 ≤ j) (hjp : j < p)
    (heq : ∀ x, A (x + i) = A (x + j)) : i = j := by
  have hper : Function.Periodic A (i - j) := by
    intro x
    have hh := heq (x - j)
    convert hh using 1 <;> congr 1 <;> omega
  obtain ⟨q, hq⟩ := (h.period_iff_dvd _).mp hper
  have hpz : (0 : ℤ) < p := by have := h.positive; omega
  have h0 : q = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have : (p : ℤ) * q ≤ -(p : ℤ) := by nlinarith
      omega
    · have : (p : ℤ) ≤ (p : ℤ) * q := by nlinarith
      omega
  simp only [h0, mul_zero] at hq
  omega

end Hierarchical

namespace OrderStats

variable {β : Type} [LinearOrder β] {n : ℕ}

def sortedList (f : Fin n → β) : List β :=
  (List.ofFn f).mergeSort (fun a b => decide (a ≤ b))

@[simp] theorem sortedList_length (f : Fin n → β) : (sortedList f).length = n := by
  simp only [sortedList, List.length_mergeSort, List.length_ofFn]

def order (f : Fin n → β) (i : Fin n) : β :=
  (sortedList f).get ⟨i.val, by simpa only [sortedList_length] using i.isLt⟩

theorem monotone_order (f : Fin n → β) : Monotone (order f) := by
  intro i j hij
  exact List.sortedLE_mergeSort.monotone_get (show
    (⟨i.val, by simpa only [sortedList_length] using i.isLt⟩ : Fin (sortedList f).length) ≤
      ⟨j.val, by simpa only [sortedList_length] using j.isLt⟩ from hij)

theorem ofFn_order (f : Fin n → β) : List.ofFn (order f) = sortedList f := by
  apply List.ext_getElem (by simp only [List.length_ofFn, sortedList_length])
  intro i hi hi'
  simp only [List.getElem_ofFn, order, List.get_eq_getElem]

theorem order_mem (f : Fin n → β) (i : Fin n) : ∃ j, f j = order f i := by
  apply List.mem_ofFn.mp
  apply (List.mergeSort_perm (List.ofFn f) (fun a b => decide (a ≤ b))).mem_iff.mp
  exact List.get_mem ..

/-- Counting a finite function's values is the same on its explicit list. -/
theorem countP_ofFn {γ : Type} (P : γ → Bool) (f : Fin n → γ) :
    (List.ofFn f).countP P = ∑ i : Fin n, if P (f i) then 1 else 0 := by
  induction n with
  | zero => simp only [List.ofFn_zero, List.countP_nil, Fin.sum_univ_zero]
  | succ n ih =>
    rw [List.ofFn_succ, List.countP_cons, Fin.sum_univ_succ]
    rw [ih]
    omega

/-- Sorting preserves all value multiplicities, including repetitions. -/
theorem card_filter_order (f : Fin n → β) (P : β → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun i => P (order f i))).card =
      (Finset.univ.filter (fun i => P (f i))).card := by
  have hh := (List.mergeSort_perm (List.ofFn f) (fun a b => decide (a ≤ b))).countP_eq
    (fun a => decide (P a))
  change (sortedList f).countP (fun a => decide (P a)) = _ at hh
  rw [← ofFn_order f, countP_ofFn, countP_ofFn] at hh
  simpa only [Finset.card_filter, decide_eq_true_eq] using hh

/-- Order statistics characterized by cumulative counts. -/
theorem monotone_count_iff {f : Fin n → β} (hm : Monotone f) (i : Fin n) (t : β) :
    f i ≤ t ↔ i.val < (Finset.univ.filter (fun j => f j ≤ t)).card := by
  constructor
  · intro hit
    have hsub : Finset.Iic i ⊆ Finset.univ.filter (fun j => f j ≤ t) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hm (Finset.mem_Iic.mp hj)).trans hit⟩
    have hh := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hh
    omega
  · intro hcard
    by_contra hnot
    have hsub : (Finset.univ.filter (fun j => f j ≤ t)) ⊆ Finset.Iio i := by
      intro j hj
      apply Finset.mem_Iio.mpr
      by_contra hnotlt
      have hle : i ≤ j := le_of_not_gt hnotlt
      exact hnot ((hm hle).trans (Finset.mem_filter.mp hj).2)
    have hh := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hh
    omega

theorem order_le_iff (f : Fin n → β) (i : Fin n) (t : β) :
    order f i ≤ t ↔ i.val < (Finset.univ.filter (fun j => f j ≤ t)).card := by
  rw [monotone_count_iff (monotone_order f), card_filter_order f (fun a => a ≤ t)]

/-- A coordinatewise increasing matching remains increasing after sorting. -/
theorem order_le_order {f g : Fin n → β} (h : ∀ i, f i ≤ g i) (i : Fin n) :
    order f i ≤ order g i := by
  apply (order_le_iff f i _).mpr
  apply lt_of_lt_of_le ((order_le_iff g i _).mp le_rfl)
  apply Finset.card_le_card
  intro j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (h j).trans (Finset.mem_filter.mp hj).2⟩

theorem order_eq_of_counts {f g : Fin n → β}
    (h : ∀ t, (Finset.univ.filter (fun j => f j ≤ t)).card =
      (Finset.univ.filter (fun j => g j ≤ t)).card) (i : Fin n) : order f i = order g i := by
  have he : ∀ t, order f i ≤ t ↔ order g i ≤ t := by
    intro t
    rw [order_le_iff, order_le_iff, h t]
  exact le_antisymm ((he _).mpr le_rfl) ((he _).mp le_rfl)

theorem order_add (f : Fin n → ℤ) (c : ℤ) (i : Fin n) :
    order (fun j => f j + c) i = order f i + c := by
  have he : ∀ t, order (fun j => f j + c) i ≤ t ↔ order f i + c ≤ t := by
    intro t
    rw [← le_sub_iff_add_le, order_le_iff, order_le_iff]
    have hh : Finset.univ.filter (fun j => f j + c ≤ t) =
        Finset.univ.filter (fun j => f j ≤ t - c) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [hh]
  exact le_antisymm ((he _).mpr le_rfl) ((he _).mp le_rfl)

/-- No artificial window is introduced by sorting matched passages. -/
theorem sorted_window {entry exit : Fin n → β} (i : Fin n) {e : β}
    (hentry : order entry i ≤ e) (hexit : e ≤ order exit i) :
    ∃ j, entry j ≤ e ∧ e ≤ exit j := by
  by_contra hno
  push Not at hno
  have hsub : Finset.univ.filter (fun j => entry j ≤ e) ⊆
      Finset.univ.filter (fun j => exit j < e) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hno j (Finset.mem_filter.mp hj).2⟩
  have hc := Finset.card_le_card hsub
  have hl := (order_le_iff entry i e).mp hentry
  have hs : Finset.univ.filter (fun j => order exit j < e) ⊆ Finset.Iio i := by
    intro j hj
    apply Finset.mem_Iio.mpr
    by_contra hnot
    have hh := monotone_order exit (le_of_not_gt hnot)
    exact (not_lt_of_ge (hexit.trans hh)) (Finset.mem_filter.mp hj).2
  have hh := Finset.card_le_card hs
  rw [Fin.card_Iio, card_filter_order exit (fun a => a < e)] at hh
  omega

/-- Exact upward-unit-edge conservation. For each height, sorting preserves the
number of vertical intervals traversing it, not just the set of vertices. -/
theorem sorted_edge_count {entry exit : Fin n → ℤ} (h : ∀ j, entry j ≤ exit j) (e : ℤ) :
    (Finset.univ.filter (fun j => order entry j ≤ e ∧ e < order exit j)).card =
      (Finset.univ.filter (fun j => entry j ≤ e ∧ e < exit j)).card := by
  have count (a b : Fin n → ℤ) (hab : ∀ j, a j ≤ b j) :
      (Finset.univ.filter (fun j => a j ≤ e ∧ e < b j)).card +
        (Finset.univ.filter (fun j => b j ≤ e)).card =
          (Finset.univ.filter (fun j => a j ≤ e)).card := by
    have heq : Finset.univ.filter (fun j => a j ≤ e) =
        (Finset.univ.filter (fun j => a j ≤ e ∧ e < b j)) ∪
          (Finset.univ.filter (fun j => b j ≤ e)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · intro ha
        by_cases hb : e < b j
        · exact Or.inl ⟨ha, hb⟩
        · exact Or.inr (le_of_not_gt hb)
      · rintro (⟨ha, _⟩ | hb)
        · exact ha
        · exact (hab j).trans hb
    have hd : Disjoint (Finset.univ.filter (fun j => a j ≤ e ∧ e < b j))
        (Finset.univ.filter (fun j => b j ≤ e)) := by
      apply Finset.disjoint_left.mpr
      intro j hj hk
      exact (not_lt_of_ge (Finset.mem_filter.mp hk).2) (Finset.mem_filter.mp hj).2.2
    rw [heq, Finset.card_union_of_disjoint hd]
  have ha := count entry exit h
  have hb := count (order entry) (order exit) (order_le_order h)
  rw [card_filter_order exit (fun a => a ≤ e),
    card_filter_order entry (fun a => a ≤ e)] at hb
  omega

end OrderStats

namespace PrefixMatching

variable {α ι κ : Type} [DecidableEq α] [Fintype ι] [Fintype κ]

/-- A direct laminar Hall argument. Prefix requests can be assigned distinct
extensions precisely when every prefix subtree has enough capacity. -/
theorem hall (request : ι → List α) (supply : κ → List α)
    (hcapacity : ∀ w, (Finset.univ.filter (fun i => w <+: request i)).card ≤
      (Finset.univ.filter (fun j => w <+: supply j)).card) :
    ∃ f : ι → κ, Function.Injective f ∧ ∀ i, request i <+: supply (f i) := by
  classical
  let t : ι → Finset κ := fun i => Finset.univ.filter (fun j => request i <+: supply j)
  have hhall (s : Finset ι) : s.card ≤ (s.biUnion t).card := by
    induction s using Finset.strongInductionOn with
    | _ s ih =>
      by_cases hs : s.Nonempty
      · obtain ⟨i, hi, hmin⟩ := s.exists_min_image (fun i => (request i).length) hs
        let a := s.filter (fun j => request i <+: request j)
        let b := s.filter (fun j => ¬ request i <+: request j)
        have hbsub : b ⊂ s := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
          intro he
          have : i ∈ b := he.symm ▸ hi
          exact (Finset.mem_filter.mp this).2 (List.prefix_refl _)
        have hab : a ∪ b = s := by
          ext j
          simp only [a, b, Finset.mem_union, Finset.mem_filter]
          tauto
        have hd : Disjoint a b := by
          apply Finset.disjoint_left.mpr
          intro j hj hk
          exact (Finset.mem_filter.mp hk).2 (Finset.mem_filter.mp hj).2
        have hacap : a.card ≤ (t i).card := by
          apply le_trans (Finset.card_le_card ?_) (hcapacity (request i))
          intro j hj
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
        have htind : Disjoint (t i) (b.biUnion t) := by
          apply Finset.disjoint_left.mpr
          intro j hji hjb
          obtain ⟨k, hk, hjk⟩ := Finset.mem_biUnion.mp hjb
          have hprei : request i <+: supply j := (Finset.mem_filter.mp hji).2
          have hprek : request k <+: supply j := (Finset.mem_filter.mp hjk).2
          exact (Finset.mem_filter.mp hk).2
            (List.prefix_of_prefix_length_le hprei hprek
              (hmin k (Finset.mem_filter.mp hk).1))
        have hsupply : (t i) ∪ b.biUnion t ⊆ s.biUnion t := by
          intro j hj
          rcases Finset.mem_union.mp hj with hj | hj
          · exact Finset.mem_biUnion.mpr ⟨i, hi, hj⟩
          · obtain ⟨k, hk, hj⟩ := Finset.mem_biUnion.mp hj
            exact Finset.mem_biUnion.mpr ⟨k, (Finset.mem_filter.mp hk).1, hj⟩
        have hbc := ih b hbsub
        have hsc := Finset.card_le_card hsupply
        rw [Finset.card_union_of_disjoint htind] at hsc
        have hcard := Finset.card_union_of_disjoint hd
        rw [hab] at hcard
        omega
      · have : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        subst s
        simp only [Finset.card_empty, Nat.zero_le]
  obtain ⟨f, hf, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hhall
  exact ⟨f, hf, fun i => (Finset.mem_filter.mp (hmem i)).2⟩

/-- On equal finite token sets the matching is a permutation. -/
theorem permutation (request supply : ι → List α)
    (hcapacity : ∀ w, (Finset.univ.filter (fun i => w <+: request i)).card ≤
      (Finset.univ.filter (fun j => w <+: supply j)).card) :
    ∃ f : Equiv.Perm ι, ∀ i, request i <+: supply (f i) := by
  obtain ⟨f, hf, hp⟩ := hall request supply hcapacity
  exact ⟨Equiv.ofBijective f ⟨hf, (Finite.injective_iff_surjective).mp hf⟩, hp⟩

end PrefixMatching

end Superstring

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring

namespace Counts.Data

variable {α : Type} [DecidableEq α] [Inhabited α]

/-- Prefix-subtree telescoping, stronger than the total-cost identity. -/
theorem down_descendants (D : Data α) (hD : D.WellFormed) {s : List α} (hs : s ≠ []) :
    (∑ r ∈ D.vertices with s <+: r, D.down r) = D.count s := by
  classical
  by_cases hsm : s ∈ D.vertices
  · let T := D.vertices.filter (fun r => s <+: r)
    have hsT : s ∈ T := Finset.mem_filter.mpr ⟨hsm, List.prefix_refl s⟩
    have hext : (∑ r ∈ T, ∑ c ∈ D.alphabet, D.count (r ++ [c])) =
        ∑ r ∈ T.erase s, D.count r := by
      rw [← Finset.sum_product T D.alphabet (fun a => D.count (a.1 ++ [a.2]))]
      apply Finset.sum_bij_ne_zero (fun a _ _ => a.1 ++ [a.2])
      · intro a ha hz
        obtain ⟨haT, _⟩ := Finset.mem_product.mp ha
        have hpre := (Finset.mem_filter.mp haT).2
        have hlen := hpre.length_le
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr
          ⟨D.mem_of_count_ne_zero hz, hpre.trans (List.prefix_append _ _)⟩⟩
        intro he
        have := congrArg List.length he
        simp only [List.length_append, List.length_singleton] at this
        omega
      · intro a _ _ b _ _ hab
        have he := congrArg List.dropLast hab
        simp only [List.dropLast_concat] at he
        have hc : a.2 = b.2 := by
          rw [he] at hab
          simpa only [List.append_cancel_left_eq, List.cons.injEq, and_true] using hab
        exact Prod.ext he hc
      · intro r hr hz
        obtain ⟨hrs, hrT⟩ := Finset.mem_erase.mp hr
        obtain ⟨hrV, hpre⟩ := Finset.mem_filter.mp hrT
        have hrne : r ≠ [] := by
          intro he
          have := hpre.length_le
          have hslen : 0 < s.length := List.length_pos_iff.mpr hs
          simp only [he, List.length_nil] at this
          omega
        have hsl : s.length < r.length := by
          have := hpre.length_le
          by_contra hn
          exact hrs (hpre.eq_of_length (by omega)).symm
        have hpl : s <+: r.dropLast :=
          List.prefix_of_prefix_length_le hpre (List.dropLast_prefix r)
            (by simp only [List.length_dropLast]; omega)
        have heq := List.dropLast_append_getLast hrne
        have hpT : r.dropLast ∈ T := Finset.mem_filter.mpr
          ⟨hD.closed hrV (List.dropLast_prefix r).isInfix, hpl⟩
        have hc : r.getLast hrne ∈ D.alphabet := hD.letters r hrV _
          (List.getLast_mem hrne)
        refine ⟨(r.dropLast, r.getLast hrne), Finset.mem_product.mpr ⟨hpT, hc⟩, ?_, heq⟩
        simpa only [heq] using hz
      · intros
        rfl
    have hadd := Finset.sum_congr rfl (fun r (hr : r ∈ T) =>
      D.down_add hD (s := r) (by
        intro he
        have hh := (Finset.mem_filter.mp hr).2.length_le
        have hslen : 0 < s.length := List.length_pos_iff.mpr hs
        simp only [he, List.length_nil] at hh
        omega))
    rw [Finset.sum_add_distrib, hext] at hadd
    have hsum := Finset.sum_erase_add T D.count hsT
    change (∑ r ∈ T, D.down r) = D.count s
    rw [← hsum] at hadd
    exact Nat.add_right_cancel (hadd.trans (Nat.add_comm _ _))
  · have he : D.vertices.filter (fun r => s <+: r) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      obtain ⟨hr, hp⟩ := Finset.mem_filter.mp hr
      exact hsm (hD.closed hr hp.isInfix)
    rw [he, Finset.sum_empty, D.count_zero s (Or.inl hsm)]

/-- Each copy of an actual base down edge is a distinct token. -/
abbrev DownToken (D : Data α) := Σ s : D.vertices, Fin (D.down s.val)

namespace DownToken

variable (D : Data α)

def word (i : D.DownToken) : List α := i.1.val

theorem mem (i : D.DownToken) : word D i ∈ D.vertices := i.1.property

theorem nonempty (i : D.DownToken) : word D i ≠ [] := by
  intro he
  have hi := i.2.isLt
  change i.2.val < D.down (word D i) at hi
  rw [he] at hi
  have hz := D.count_zero [] (Or.inr rfl)
  simp only [down, hz, Nat.zero_sub, Nat.not_lt_zero] at hi

theorem histogram (P : List α → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun i : D.DownToken => P (word D i))).card =
      ∑ s ∈ D.vertices, if P s then D.down s else 0 := by
  classical
  rw [Finset.card_filter, Fintype.sum_sigma]
  change (∑ x : D.vertices, ∑ _ : Fin (D.down x.val), if P x.val then 1 else 0) = _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_ite, mul_one, mul_zero]
  exact Finset.sum_coe_sort D.vertices (fun s => if P s then D.down s else 0)

theorem card (hD : D.WellFormed) : Fintype.card D.DownToken = D.weight := by
  have hh := histogram D (fun _ => True)
  simpa only [Finset.filter_true, Finset.card_univ, ite_true, D.total_down hD] using hh

theorem prefix_count (hD : D.WellFormed) {s : List α} (hs : s ≠ []) :
    (Finset.univ.filter (fun i : D.DownToken => s <+: word D i)).card = D.count s := by
  rw [histogram, ← Finset.sum_filter]
  exact D.down_descendants hD hs

/-- The capacity condition needed to thread the down tokens into passages. -/
theorem capacity (hD : D.WellFormed) (s : List α) :
    (Finset.univ.filter (fun i : D.DownToken => s <+: (word D i).tail)).card ≤
      (Finset.univ.filter (fun i : D.DownToken => s <+: word D i)).card := by
  classical
  by_cases hs : s = []
  · subst s
    simp only [List.nil_prefix, Finset.filter_true, le_refl]
  · let U := Finset.univ.filter (fun i : D.DownToken => s <+: (word D i).tail)
    have hf := Finset.sum_card_fiberwise_eq_card_filter U D.alphabet
      (fun i => (word D i).head (nonempty D i))
    have he : U.filter (fun i => (word D i).head (nonempty D i) ∈ D.alphabet) = U := by
      apply Finset.filter_eq_self.mpr
      intro i _
      exact hD.letters _ (mem D i) _ (List.head_mem (nonempty D i))
    rw [he] at hf
    have hterm (c : α) : U.filter (fun i => (word D i).head (nonempty D i) = c) =
        Finset.univ.filter (fun i : D.DownToken => c :: s <+: word D i) := by
      ext i
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
      have hpref (w : List α) (hn : w ≠ []) :
          (s <+: w.tail ∧ w.head hn = c) ↔ c :: s <+: w := by
        cases w with
        | nil => exact (hn rfl).elim
        | cons a w => simp only [List.tail_cons, List.head_cons, List.cons_prefix_cons]
                      tauto
      exact hpref _ (nonempty D i)
    simp_rw [hterm, prefix_count D hD (List.cons_ne_nil _ _)] at hf
    rw [prefix_count D hD hs]
    exact hf ▸ D.left_bound hD hs

end DownToken


theorem down_permutation (D : Data α) (hD : D.WellFormed) :
    ∃ f : Equiv.Perm D.DownToken,
      ∀ i, (DownToken.word D i).tail <+: DownToken.word D (f i) :=
  PrefixMatching.permutation _ _ (DownToken.capacity D hD)

end Counts.Data

namespace Hierarchical

variable {α ι : Type}

/-- Down-edge tokens threaded through the acyclic up-edge runs. -/
structure Threading (V : Set (List α)) (ι : Type) where
  word : ι → List α
  nonempty : ∀ i, word i ≠ []
  mem : ∀ i, word i ∈ V
  next : Equiv.Perm ι
  follows : ∀ i, (word i).tail <+: word (next i)

namespace Threading

variable {V : Set (List α)} (C : Threading V ι)

/-- The letter removed by the down step at each integer start coordinate. -/
def text (i : ι) (x : ℤ) : α :=
  (C.word ((C.next ^ x) i)).head (C.nonempty _)

theorem text_zpow (i : ι) (d x : ℤ) :
    C.text ((C.next ^ d) i) x = C.text i (x + d) := by
  simp only [text, zpow_add, Equiv.Perm.mul_apply]

theorem text_next (i : ι) (x : ℤ) : C.text (C.next i) x = C.text i (x + 1) := by
  simpa only [zpow_one] using C.text_zpow i 1 x

theorem text_period [Fintype ι] (i : ι) :
    Function.Periodic (C.text i) (orderOf C.next : ℤ) := by
  intro x
  rw [← C.text_zpow, zpow_natCast, pow_orderOf_eq_one]
  rfl

theorem exists_primitive_text [Fintype ι] (i : ι) :
    ∃ p, Primitive (C.text i) p :=
  exists_primitive (orderOf_pos C.next) (C.text_period i)

/-- Following tails proves that every old vertex is spelled by the infinite
text, even if it is longer than an entire turn of the threaded circulation. -/
theorem word_spelled (i : ι) :
    C.word i = textWord (C.text i) 0 (C.word i).length := by
  have hget : ∀ k (j : ι) (hk : k < (C.word j).length),
      (C.word j)[k] = C.text j (k : ℤ) := by
    intro k
    induction k with
    | zero =>
      intro j hk
      simp only [text, Nat.cast_zero, zpow_zero, Equiv.Perm.one_apply]
      exact (List.head_eq_getElem (C.nonempty j)).symm
    | succ k ih =>
      intro j hk
      have hkt : k < (C.word j).tail.length := by
        rw [List.length_tail]
        omega
      have hkn : k < (C.word (C.next j)).length :=
        lt_of_lt_of_le hkt (C.follows j).length_le
      calc
        (C.word j)[k + 1] = (C.word j).tail[k] := (List.getElem_tail hkt).symm
        _ = (C.word (C.next j))[k] := (C.follows j).getElem hkt
        _ = C.text (C.next j) (k : ℤ) := ih _ hkn
        _ = C.text j ((k + 1 : ℕ) : ℤ) := by
          simpa only [Nat.cast_add, Nat.cast_one] using C.text_next j (k : ℤ)
  apply List.ext_getElem
  · simp only [length_textWord, sub_zero, Int.toNat_natCast]
  · intro k hk hk'
    simp only [textWord, List.getElem_ofFn, zero_add]
    exact hget k i hk

/-- The actual exit vertex seen at any translated token. -/
theorem translated_word (i : ι) (x : ℤ) :
    C.word ((C.next ^ x) i) =
      textWord (C.text i) x (x + (C.word ((C.next ^ x) i)).length) := by
  calc
    C.word ((C.next ^ x) i) =
        textWord (C.text ((C.next ^ x) i)) 0 (C.word ((C.next ^ x) i)).length :=
      C.word_spelled _
    _ = textWord (C.text i) x (x + (C.word ((C.next ^ x) i)).length) := by
      apply List.ext_getElem
      · simp only [length_textWord, sub_zero, add_sub_cancel_left]
      · intro k hk hk'
        simp only [textWord, List.getElem_ofFn, zero_add, C.text_zpow]
        congr 1
        omega

/-- Entry-exit monotonicity before sorting; all entry windows are nonnegative. -/
theorem exit_mono_one (i : ι) :
    (C.word i).length ≤ 1 + (C.word (C.next i)).length := by
  have hh := (C.follows i).length_le
  rw [List.length_tail] at hh
  omega

end Threading

end Hierarchical

namespace Counts.Data

variable {α : Type} [DecidableEq α] [Inhabited α]

/-- Realize the base down multiset as a periodic circulation on actual vertices. -/
noncomputable def threading (D : Data α) (hD : D.WellFormed) :
    Hierarchical.Threading (D.vertices : Set (List α)) D.DownToken where
  word := DownToken.word D
  nonempty := DownToken.nonempty D
  mem := DownToken.mem D
  next := Classical.choose (D.down_permutation hD)
  follows := Classical.choose_spec (D.down_permutation hD)

end Counts.Data

namespace OrderStats

variable {β : Type} [LinearOrder β] {n : ℕ}

omit [LinearOrder β] in
theorem card_filter_perm (f : Fin n → β) (e : Equiv.Perm (Fin n))
    (P : β → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun i => P (f (e i)))).card =
      (Finset.univ.filter (fun i => P (f i))).card := by
  rw [Finset.card_filter, Finset.card_filter]
  exact Equiv.sum_comp e (fun i => if P (f i) then 1 else 0)

theorem order_perm (f : Fin n → β) (e : Equiv.Perm (Fin n)) (i : Fin n) :
    order (fun j => f (e j)) i = order f i :=
  order_eq_of_counts (fun t => card_filter_perm f e (fun v => v ≤ t)) i

end OrderStats

namespace Hierarchical.Threading

variable {α ι : Type} {V : Set (List α)} [Fintype ι]

/-- Tokens with a specified full-text alignment, not just a matching finite word. -/
def Aligned (C : Threading V ι) (A : ℤ → α) := {i : ι // C.text i = A}

noncomputable instance (C : Threading V ι) (A : ℤ → α) : Fintype (C.Aligned A) := by
  classical
  exact inferInstanceAs (Fintype {i : ι // C.text i = A})

noncomputable def enumerate (C : Threading V ι) (A : ℤ → α) :
    Fin (Fintype.card (C.Aligned A)) ≃ C.Aligned A := (Fintype.equivFin _).symm

/-- A text period permutes, rather than fixes, the multiple aligned passages. -/
def periodPerm (C : Threading V ι) {A : ℤ → α} {p : ℕ}
    (hp : Function.Periodic A (p : ℤ)) : Equiv.Perm (C.Aligned A) :=
  (C.next ^ (p : ℤ)).subtypeEquiv (by
    intro i
    constructor
    · intro hi
      funext x
      rw [C.text_zpow, hi]
      exact hp x
    · intro hi
      funext x
      have hh := congrFun hi (x - p)
      rw [C.text_zpow, sub_add_cancel] at hh
      exact hh.trans (by simpa only [sub_eq_add_neg] using hp.neg x))

/-- Exit ends of the unsorted primitive passages. -/
noncomputable def exits (C : Threading V ι) (A : ℤ → α) (x : ℤ)
    (j : Fin (Fintype.card (C.Aligned A))) : ℤ :=
  x + (C.word ((C.next ^ x) (C.enumerate A j).val)).length

theorem exits_step (C : Threading V ι) (A : ℤ → α) (x : ℤ)
    (j : Fin (Fintype.card (C.Aligned A))) : C.exits A x j ≤ C.exits A (x + 1) j := by
  have he : (C.next ^ (x + 1)) (C.enumerate A j).val =
      C.next ((C.next ^ x) (C.enumerate A j).val) := by
    rw [show x + 1 = 1 + x by omega, zpow_add, zpow_one, Equiv.Perm.mul_apply]
  have hh := C.exit_mono_one ((C.next ^ x) (C.enumerate A j).val)
  simp only [exits, he]
  omega

theorem exits_lower (C : Threading V ι) (A : ℤ → α) (x : ℤ)
    (j : Fin (Fintype.card (C.Aligned A))) : x + 1 ≤ C.exits A x j := by
  have hh := List.length_pos_iff.mpr (C.nonempty ((C.next ^ x) (C.enumerate A j).val))
  simp only [exits]
  omega

/-- Sorting independently at every coordinate gives the monotone layer function. -/
noncomputable def sortedExit (C : Threading V ι) (A : ℤ → α)
    (j : Fin (Fintype.card (C.Aligned A))) (x : ℤ) : ℤ := OrderStats.order (C.exits A x) j

theorem sortedExit_mono (C : Threading V ι) (A : ℤ → α)
    (j : Fin (Fintype.card (C.Aligned A))) : Monotone (C.sortedExit A j) := by
  apply monotone_int_of_le_succ
  intro x
  exact OrderStats.order_le_order (C.exits_step A x) j

theorem sortedExit_lower (C : Threading V ι) (A : ℤ → α)
    (j : Fin (Fintype.card (C.Aligned A))) (x : ℤ) : x ≤ C.sortedExit A j (x - 1) := by
  obtain ⟨k, hk⟩ := OrderStats.order_mem (C.exits A (x - 1)) j
  change x ≤ OrderStats.order (C.exits A (x - 1)) j
  rw [← hk]
  have := C.exits_lower A (x - 1) k
  omega

theorem exits_period (C : Threading V ι) {A : ℤ → α} {p : ℕ}
    (hp : Function.Periodic A (p : ℤ)) (x : ℤ)
    (j : Fin (Fintype.card (C.Aligned A))) :
    C.exits A (x + p) j =
      C.exits A x ((C.enumerate A).symm (C.periodPerm hp (C.enumerate A j))) + p := by
  have he : (C.periodPerm hp (C.enumerate A j)).val =
      (C.next ^ (p : ℤ)) (C.enumerate A j).val := rfl
  simp only [exits, Equiv.apply_symm_apply, he, zpow_add, Equiv.Perm.mul_apply]
  omega

theorem sortedExit_shift (C : Threading V ι) {A : ℤ → α} {p : ℕ}
    (hp : Function.Periodic A (p : ℤ))
    (j : Fin (Fintype.card (C.Aligned A))) (x : ℤ) :
    C.sortedExit A j (x + p) = C.sortedExit A j x + p := by
  let e : Equiv.Perm (Fin (Fintype.card (C.Aligned A))) :=
    (C.enumerate A).trans ((C.periodPerm hp).trans (C.enumerate A).symm)
  have he : C.exits A (x + p) = fun k => C.exits A x (e k) + p := by
    funext k
    exact C.exits_period hp x k
  change OrderStats.order (C.exits A (x + p)) j =
    OrderStats.order (C.exits A x) j + (p : ℤ)
  rw [he, OrderStats.order_add, OrderStats.order_perm]

theorem exits_actual (C : Threading V ι) (A : ℤ → α) (x : ℤ)
    (j : Fin (Fintype.card (C.Aligned A))) : textWord A x (C.exits A x j) ∈ V := by
  have he := C.translated_word (C.enumerate A j).val x
  rw [(C.enumerate A j).property] at he
  exact he ▸ C.mem ((C.next ^ x) (C.enumerate A j).val)

/-- The sorted windows are genuine substring vertices. No abstract completion of
V or artificial layer windows are introduced. -/
theorem sortedExit_actual (C : Threading V ι) (closed : SubstringClosed V)
    (A : ℤ → α) (j : Fin (Fintype.card (C.Aligned A))) (x e : ℤ)
    (hlo : C.sortedExit A j (x - 1) ≤ e) (hhi : e ≤ C.sortedExit A j x) :
    textWord A x e ∈ V := by
  obtain ⟨k, hk⟩ := OrderStats.order_mem (C.exits A x) j
  have hh : e ≤ C.exits A x k := by
    change e ≤ OrderStats.order (C.exits A x) j at hhi
    rwa [hk]
  exact closed (C.exits_actual A x k)
    (textWord_infix A le_rfl ((C.sortedExit_lower A j x).trans hlo) hh)

/-- The ordered-layer construction for a specified primitive-text group. -/
noncomputable def layer (C : Threading V ι) (closed : SubstringClosed V)
    {A : ℤ → α} {p : ℕ} (hp : Function.Periodic A (p : ℤ))
    (j : Fin (Fintype.card (C.Aligned A))) : Layer V A p where
  z := C.sortedExit A j
  mono := C.sortedExit_mono A j
  lower := C.sortedExit_lower A j
  shift := C.sortedExit_shift hp j
  actual := C.sortedExit_actual closed A j

theorem layers_ordered (C : Threading V ι) (A : ℤ → α)
    (i j : Fin (Fintype.card (C.Aligned A))) (hij : i ≤ j) (x : ℤ) :
    C.sortedExit A i x ≤ C.sortedExit A j x := OrderStats.monotone_order _ hij

/-- Exact conservation of vertical unit edges under the sorting operation. -/
theorem sorted_edges (C : Threading V ι) (A : ℤ → α) (x e : ℤ) :
    (Finset.univ.filter (fun j => C.sortedExit A j (x - 1) ≤ e ∧
      e < C.sortedExit A j x)).card =
    (Finset.univ.filter (fun j => C.exits A (x - 1) j ≤ e ∧
      e < C.exits A x j)).card := by
  apply OrderStats.sorted_edge_count
  intro j
  have hh := C.exits_step A (x - 1) j
  simpa only [sub_add_cancel] using hh

end Hierarchical.Threading

end Superstring

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring

namespace Hierarchical.Threading

variable {α ι : Type} {V : Set (List α)} [Fintype ι]

/-- Full-text translation equivalence. Finite prefixes alone do not identify groups. -/
def SameText (C : Threading V ι) (i j : ι) : Prop :=
  ∃ d : ℤ, ∀ x : ℤ, C.text i (x + d) = C.text j x

def textSetoid (C : Threading V ι) : Setoid ι where
  r := C.SameText
  iseqv := by
    constructor
    · intro i
      exact ⟨0, by intro x; simp only [add_zero]⟩
    · rintro i j ⟨d, hd⟩
      refine ⟨-d, ?_⟩
      intro x
      simpa only [add_assoc, neg_add_cancel, add_zero] using (hd (x + -d)).symm
    · rintro i j k ⟨d, hd⟩ ⟨e, he⟩
      refine ⟨e + d, ?_⟩
      intro x
      rw [← add_assoc, hd, he]

def Groups (C : Threading V ι) := Quotient C.textSetoid

noncomputable instance (C : Threading V ι) : Fintype C.Groups := by
  classical
  exact inferInstanceAs (Fintype (Quotient C.textSetoid))

noncomputable instance (C : Threading V ι) : DecidableEq C.Groups := Classical.decEq _

def group (C : Threading V ι) (i : ι) : C.Groups := Quotient.mk C.textSetoid i

noncomputable def groupText (C : Threading V ι) (g : C.Groups) : ℤ → α :=
  C.text (Quotient.out g)

noncomputable def groupPeriod (C : Threading V ι) (g : C.Groups) : ℕ :=
  Classical.choose (C.exists_primitive_text (Quotient.out g))

theorem primitive_group (C : Threading V ι) (g : C.Groups) :
    Primitive (C.groupText g) (C.groupPeriod g) :=
  Classical.choose_spec (C.exists_primitive_text (Quotient.out g))

/-- Alignment with an arbitrary fixed two-sided primitive text. -/
def Compatible (C : Threading V ι) (A : ℤ → α) :=
  {i : ι // ∃ d : ℤ, ∀ x, C.text i x = A (x + d)}

noncomputable instance (C : Threading V ι) (A : ℤ → α) : Fintype (C.Compatible A) := by
  classical
  exact inferInstanceAs (Fintype {i : ι // ∃ d : ℤ, ∀ x, C.text i x = A (x + d)})

def phaseMap (C : Threading V ι) {A : ℤ → α} {p : ℕ}
    (j : Fin p × C.Aligned A) : C.Compatible A :=
  ⟨(C.next ^ (j.1.val : ℤ)) j.2.val, (j.1.val : ℤ), by
    intro x
    rw [C.text_zpow, j.2.property]⟩

omit [Fintype ι] in
theorem phaseMap_injective (C : Threading V ι) {A : ℤ → α} {p : ℕ}
    (hp : Primitive A p) : Function.Injective (C.phaseMap (A := A) (p := p)) := by
  rintro ⟨r, a⟩ ⟨s, b⟩ he
  have hval := congrArg Subtype.val he
  have hr : r = s := by
    apply Fin.ext
    have hh : (r.val : ℤ) = s.val := hp.alignment_unique
      (by omega) (by omega) (by omega) (by omega) (by
        intro x
        have ht := congrArg (fun i => C.text i x) hval
        change C.text ((C.next ^ (r.val : ℤ)) a.val) x =
          C.text ((C.next ^ (s.val : ℤ)) b.val) x at ht
        simpa only [C.text_zpow, a.property, b.property] using ht)
    omega
  subst s
  have hab : a = b := by
    apply Subtype.ext
    exact (C.next ^ (r.val : ℤ)).injective hval
  subst b
  rfl

omit [Fintype ι] in
theorem phaseMap_surjective (C : Threading V ι) {A : ℤ → α} {p : ℕ}
    (hp : Primitive A p) : Function.Surjective (C.phaseMap (A := A) (p := p)) := by
  rintro ⟨i, d, hd⟩
  have hpz : (0 : ℤ) < p := by have := hp.positive; omega
  have hm0 := Int.emod_nonneg d (show (p : ℤ) ≠ 0 by omega)
  have hml := Int.emod_lt_of_pos d hpz
  let r : Fin p := ⟨(d % (p : ℤ)).toNat, by omega⟩
  have hr : (r.val : ℤ) = d % (p : ℤ) := by dsimp only [r]; omega
  have he : d - r.val = (d / (p : ℤ)) * p := by
    have := Int.emod_add_ediv_mul d (p : ℤ)
    omega
  have hper : Function.Periodic A (d - r.val) := by
    rw [he]
    simpa only [Int.cast_id] using hp.periodic.int_mul (d / (p : ℤ))
  let a : C.Aligned A := ⟨(C.next ^ (-(r.val : ℤ))) i, by
    funext x
    rw [C.text_zpow, hd]
    have hh := hper x
    convert hh using 1
    congr 1
    omega⟩
  refine ⟨⟨r, a⟩, ?_⟩
  apply Subtype.ext
  change (C.next ^ (r.val : ℤ)) ((C.next ^ (-(r.val : ℤ))) i) = i
  rw [← Equiv.Perm.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero,
    Equiv.Perm.one_apply]

/-- Every primitive phase and aligned passage occurs exactly once. This is the
finite bookkeeping behind splitting a long turn into primitive layers. -/
noncomputable def phaseEquiv (C : Threading V ι) {A : ℤ → α} {p : ℕ}
    (hp : Primitive A p) : (Fin p × C.Aligned A) ≃ C.Compatible A :=
  Equiv.ofBijective C.phaseMap ⟨C.phaseMap_injective hp, C.phaseMap_surjective hp⟩

omit [Fintype ι] in
theorem compatible_group (C : Threading V ι) (g : C.Groups) (i : ι) :
    (∃ d : ℤ, ∀ x, C.text i x = C.groupText g (x + d)) ↔ C.group i = g := by
  have hq : C.group (Quotient.out g) = g := Quotient.out_eq g
  constructor
  · rintro ⟨d, hd⟩
    rw [← hq]
    apply Quotient.sound
    change C.SameText i (Quotient.out g)
    refine ⟨-d, ?_⟩
    intro x
    simpa only [add_assoc, neg_add_cancel, add_zero, groupText] using hd (x + -d)
  · intro hi
    have hh : C.SameText (Quotient.out g) i := Quotient.exact (hq.trans hi.symm)
    obtain ⟨d, hd⟩ := hh
    exact ⟨d, fun x => (hd x).symm⟩

noncomputable def groupFiberEquiv (C : Threading V ι) (g : C.Groups) :
    C.Compatible (C.groupText g) ≃ {i : ι // C.group i = g} :=
  Equiv.subtypeEquivRight (C.compatible_group g)

theorem group_card (C : Threading V ι) (g : C.Groups) :
    Fintype.card {i : ι // C.group i = g} =
      C.groupPeriod g * Fintype.card (C.Aligned (C.groupText g)) := by
  classical
  rw [← Fintype.card_congr (C.groupFiberEquiv g),
    ← Fintype.card_congr (C.phaseEquiv (C.primitive_group g)), Fintype.card_prod,
    Fintype.card_fin]

/-- The exact second budget: primitive period times the number of layers sums
to the original number of down steps, hence to W for the base multiplicities. -/
theorem sum_layer_periods (C : Threading V ι) :
    ∑ g : C.Groups, C.groupPeriod g * Fintype.card (C.Aligned (C.groupText g)) =
      Fintype.card ι := by
  classical
  simp_rw [← C.group_card]
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv C.group)

/-- Primitive phases with stable layer indices. -/
abbrev Phase (C : Threading V ι) :=
  Σ g : C.Groups, Fin (C.groupPeriod g) × Fin (Fintype.card (C.Aligned (C.groupText g)))

noncomputable instance (C : Threading V ι) : Fintype C.Phase :=
  inferInstanceAs (Fintype (Σ g : C.Groups,
    Fin (C.groupPeriod g) × Fin (Fintype.card (C.Aligned (C.groupText g)))))

noncomputable def groupPhaseEquiv (C : Threading V ι) (g : C.Groups) :
    (Fin (C.groupPeriod g) × Fin (Fintype.card (C.Aligned (C.groupText g)))) ≃
      {i : ι // C.group i = g} :=
  (Equiv.prodCongr (Equiv.refl _) (C.enumerate (C.groupText g))).trans
    ((C.phaseEquiv (C.primitive_group g)).trans (C.groupFiberEquiv g))

noncomputable def allPhaseEquiv (C : Threading V ι) : C.Phase ≃ ι :=
  (Equiv.sigmaCongrRight C.groupPhaseEquiv).trans (Equiv.sigmaFiberEquiv C.group)

theorem allPhaseEquiv_value (C : Threading V ι) (g : C.Groups)
    (r : Fin (C.groupPeriod g)) (j : Fin (Fintype.card (C.Aligned (C.groupText g)))) :
    C.allPhaseEquiv ⟨g, r, j⟩ =
      (C.next ^ (r.val : ℤ)) (C.enumerate (C.groupText g) j).val := rfl

/-- Exit window of a sorted layer at a specified primitive phase. -/
noncomputable def phaseWord (C : Threading V ι) (i : C.Phase) : List α :=
  textWord (C.groupText i.1) i.2.1.val
    (C.sortedExit (C.groupText i.1) i.2.2 i.2.1.val)

abbrev Recorded (C : Threading V ι) (s : List α) := {i : C.Phase // s <+: C.phaseWord i}

noncomputable instance (C : Threading V ι) (s : List α) : Fintype (C.Recorded s) := by
  classical
  exact inferInstanceAs (Fintype {i : C.Phase // s <+: C.phaseWord i})

/-- Sorting retains every prefix occurrence histogram, not just total edge cost. -/
theorem phase_prefix_count [DecidableEq α] (C : Threading V ι) (g : C.Groups)
    (r : Fin (C.groupPeriod g)) (s : List α) :
    (Finset.univ.filter (fun j => s <+: C.phaseWord ⟨g, r, j⟩)).card =
      (Finset.univ.filter (fun j => s <+: C.word (C.allPhaseEquiv ⟨g, r, j⟩))).card := by
  classical
  change (Finset.univ.filter (fun j =>
    s <+: textWord (C.groupText g) r.val
      (OrderStats.order (C.exits (C.groupText g) r.val) j))).card = _
  rw [OrderStats.card_filter_order (C.exits (C.groupText g) r.val)
    (fun e => s <+: textWord (C.groupText g) r.val e)]
  congr 1
  apply Finset.filter_congr
  intro j _
  have he := C.translated_word (C.enumerate (C.groupText g) j).val (r.val : ℤ)
  rw [(C.enumerate (C.groupText g) j).property] at he
  rw [C.allPhaseEquiv_value, he]
  rfl

/-- The recorded-occurrence identity for any threaded circulation. -/
theorem card_recorded [DecidableEq α] (C : Threading V ι) (s : List α) :
    Fintype.card (C.Recorded s) =
      (Finset.univ.filter (fun i => s <+: C.word i)).card := by
  classical
  simp only [Fintype.card_subtype, Finset.card_filter]
  rw [← C.allPhaseEquiv.sum_comp (fun i => if s <+: C.word i then 1 else 0)]
  rw [Fintype.sum_sigma, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro g _
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  simpa only [Finset.card_filter] using C.phase_prefix_count g r s

end Hierarchical.Threading

namespace Counts.Data

variable {α : Type} [DecidableEq α] [Inhabited α]

theorem recorded_count (D : Data α) (hD : D.WellFormed) {s : List α} (hs : s ≠ []) :
    Fintype.card ((D.threading hD).Recorded s) = D.count s := by
  rw [Hierarchical.Threading.card_recorded]
  exact DownToken.prefix_count D hD hs

theorem layer_budget (D : Data α) (hD : D.WellFormed) :
    ∑ g : (D.threading hD).Groups,
      (D.threading hD).groupPeriod g *
        Fintype.card ((D.threading hD).Aligned ((D.threading hD).groupText g)) = D.weight := by
  rw [Hierarchical.Threading.sum_layer_periods, DownToken.card D hD]

end Counts.Data

namespace Hierarchical

variable {α : Type}

/-- An occurrence in a two-sided text, retaining its integer origin. -/
def TextOccurs (A : ℤ → α) (s : List α) (x : ℤ) : Prop :=
  ∀ i : Fin s.length, s[i.val]? = some (A (x + i.val))

namespace TextOccurs

variable {A : ℤ → α} {s r : List α} {x d : ℤ}

theorem word (A : ℤ → α) (a b : ℤ) : TextOccurs A (textWord A a b) a := by
  intro i
  rw [List.getElem?_eq_getElem i.isLt]
  simp only [textWord, List.getElem_ofFn]

theorem eq_word (h : TextOccurs A s x) : s = textWord A x (x + s.length) := by
  apply List.ext_getElem
  · simp only [length_textWord, add_sub_cancel_left, Int.toNat_natCast]
  · intro i hi hi'
    have hh := h ⟨i, hi⟩
    simpa only [List.getElem?_eq_getElem hi, Option.some.injEq, textWord,
      List.getElem_ofFn] using hh

theorem get (h : TextOccurs A s x) {i : ℕ} (hi : i < s.length) :
    s[i]? = some (A (x + i)) := h ⟨i, hi⟩

theorem unique (hr : TextOccurs A r x) (hs : TextOccurs A s x)
    (hlen : r.length = s.length) : r = s := by
  rw [hr.eq_word, hs.eq_word, hlen]

theorem trans (hr : TextOccurs A r x) {j : ℕ} (h : Counts.Occurs r s j) :
    TextOccurs A s (x + j) := by
  intro i
  have hi : j + i.val < r.length := by have := h.1; have := i.isLt; omega
  rw [← h.at i.isLt, hr.get hi]
  congr 2
  omega

theorem shift (h : TextOccurs A s x) (hd : Function.Periodic A d) :
    TextOccurs A s (x + d) := by
  intro i
  rw [h i]
  congr 1
  have hh := hd (x + i.val)
  convert hh.symm using 1
  congr 1
  omega

theorem prefix_iff {b : ℤ} (hb : x ≤ b) :
    s <+: textWord A x b ↔ TextOccurs A s x ∧ x + s.length ≤ b := by
  constructor
  · intro hs
    have hlen := hs.length_le
    rw [length_textWord] at hlen
    refine ⟨?_, by omega⟩
    intro i
    have he := hs.getElem i.isLt
    have hw := word A x b ⟨i.val, i.isLt.trans_le hs.length_le⟩
    simpa only [List.getElem?_eq_getElem i.isLt,
      List.getElem?_eq_getElem (i.isLt.trans_le hs.length_le), he] using hw
  · rintro ⟨hs, hlen⟩
    rw [hs.eq_word]
    have he := textWord_append A (show x ≤ x + s.length by omega) hlen
    rw [← he]
    exact List.prefix_append _ _

end TextOccurs

namespace Layer

variable {V : Set (List α)} {A : ℤ → α} {p : ℕ}

/-- The entire recording criterion is the exit window at the occurrence start. -/
def Records (D : Layer V A p) (s : List α) (x : ℤ) : Prop :=
  TextOccurs A s x ∧ x + s.length ≤ D.z x

theorem records_iff_prefix (D : Layer V A p) (s : List α) (x : ℤ) :
    D.Records s x ↔ s <+: textWord A x (D.z x) := by
  have hh := D.lower (x + 1)
  simp only [add_sub_cancel_right] at hh
  exact (TextOccurs.prefix_iff (by omega : x ≤ D.z x)).symm

theorem records_shift (D : Layer V A p) (per : Function.Periodic A (p : ℤ))
    {s : List α} {x : ℤ} (h : D.Records s x) (k : ℤ) : D.Records s (x + k * p) := by
  refine ⟨h.1.shift (by simpa only [Int.cast_id] using per.int_mul k), ?_⟩
  rw [D.shift_int]
  have := h.2
  omega

def Occurrence (D : Layer V A p) (s : List α) :=
  {x : Fin p // D.Records s x.val}

noncomputable instance (D : Layer V A p) (s : List α) : Fintype (D.Occurrence s) := by
  classical
  exact inferInstanceAs (Fintype {x : Fin p // D.Records s x.val})

/-- Normalize an arbitrary lift of a recorded occurrence to its primitive phase. -/
def normalize (D : Layer V A p) (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    {s : List α} {x : ℤ} (h : D.Records s x) : D.Occurrence s := by
  have hpz : (0 : ℤ) < p := by omega
  have hm0 := Int.emod_nonneg x (show (p : ℤ) ≠ 0 by omega)
  have hml := Int.emod_lt_of_pos x hpz
  refine ⟨⟨(x % (p : ℤ)).toNat, by omega⟩, ?_⟩
  have hh := D.records_shift per h (-(x / (p : ℤ)))
  have he : x + -(x / (p : ℤ)) * p = (x % (p : ℤ)).toNat := by
    have := Int.emod_add_ediv_mul x (p : ℤ)
    rw [neg_mul]
    omega
  rwa [he] at hh

theorem normalize_val (D : Layer V A p) (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    {s : List α} {x : ℤ} (h : D.Records s x) :
    ((D.normalize hp per h).val.val : ℤ) = x % p := by
  change (((x % (p : ℤ)).toNat : ℕ) : ℤ) = x % p
  have := Int.emod_nonneg x (show (p : ℤ) ≠ 0 by omega)
  omega

/-- Every nonempty suboccurrence of a recorded interval is again recorded. -/
theorem records_suboccurrence (D : Layer V A p) {s r : List α} {x : ℤ} {j : ℕ}
    (hr : D.Records r x) (hs : Counts.Occurs r s j) : D.Records s (x + j) := by
  refine ⟨hr.1.trans hs, ?_⟩
  have hm : D.z x ≤ D.z (x + j) := D.mono (by omega)
  have := hr.2
  have := hs.1
  omega

end Layer
end Hierarchical

end Superstring

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring

namespace Hierarchical.TextOccurs

variable {α : Type} {B : ℤ → α} {s : List α} {t l u : ℤ}

theorem occurs_word (hs : TextOccurs B s t) (hlt : l ≤ t)
    (htu : t + s.length ≤ u) : Counts.Occurs (textWord B l u) s (t - l).toNat := by
  have hlen : (textWord B l u).length = (u - l).toNat := length_textWord B l u
  refine ⟨by omega, ?_⟩
  intro i
  have hi : (t - l).toNat + i.val < (textWord B l u).length := by
    have := i.isLt
    omega
  rw [(word B l u).get hi, hs i]
  congr 2
  omega

theorem agrees_template (hs : TextOccurs B s t) {A : ℤ → α}
    (hA : Counts.Matches A s) : AgreeOn B (fun x => A (x - t)) t (t + s.length) := by
  intro x htx hxe
  let k := (x - t).toNat
  have hk : k < s.length := by dsimp [k]; omega
  have he : t + (k : ℤ) = x := by dsimp [k]; omega
  have hh := (hs ⟨k, hk⟩).symm.trans (hA ⟨k, hk⟩)
  simp only [Option.some.injEq] at hh
  rw [he] at hh
  exact hh.trans (congrArg A (by omega))

end Hierarchical.TextOccurs

namespace Counts.Block

open Hierarchical

variable {α : Type} {A B : ℤ → α} {s r r' : List α} {j j' : ℕ} {x x' : ℤ}

theorem text_left (h : Block A s r j) (hr : TextOccurs B r x) : B x ≠ A (-(j : ℤ)) := by
  have hi : 0 < r.length := h.length_pos
  have hh := h.2.2.2.2.1
  rw [hr.get hi, Nat.cast_zero, add_zero] at hh
  exact fun he => hh (congrArg some he)

theorem text_right (h : Block A s r j) (hr : TextOccurs B r x) :
    B (x + r.length - 1) ≠ A (x + r.length - 1 - (x + j)) := by
  have hi : r.length - 1 < r.length := by have := h.length_pos; omega
  have hh := h.2.2.2.2.2
  rw [hr.get hi] at hh
  intro he
  apply hh
  congr 1
  convert he using 1 <;> congr 1 <;> omega

theorem text_inside (h : Block A s r j) (hr : TextOccurs B r x) (z : ℤ)
    (hzl : x < z) (hzr : z < x + r.length - 1) :
    B z = A (z - (x + j)) := by
  let k := (z - x).toNat
  have hk : k < r.length := by dsimp only [k]; omega
  have hk0 : 0 < k := by dsimp only [k]; omega
  have hkl : k + 1 < r.length := by dsimp only [k]; omega
  have hh := h.2.2.2.1 ⟨k, hk⟩ hk0 hkl
  rw [hr.get hk, Option.some.injEq] at hh
  convert hh using 1 <;> congr 1 <;> dsimp only [k] <;> omega

/-- Nearest-mismatch uniqueness on a bi-infinite lift; endpoints may be negative. -/
theorem text_boundaries_unique (h : Block A s r j) (h' : Block A s r' j')
    (hr : TextOccurs B r x) (hr' : TextOccurs B r' x') (he : x + j = x' + j') :
    x = x' ∧ r.length = r'.length := by
  have h₁ := h.1
  have h₂ := h.2.1
  have h₁' := h'.1
  have h₂' := h'.2.1
  have hstart : x = x' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hm := h'.text_left hr'
      have hh := h.text_inside hr x' hlt (by omega)
      apply hm
      convert hh using 1
      congr 1
      omega
    · have hm := h.text_left hr
      have hh := h'.text_inside hr' x hgt (by omega)
      apply hm
      convert hh using 1
      congr 1
      omega
  refine ⟨hstart, ?_⟩
  subst x'
  have hj : j = j' := by omega
  subst j'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact h.text_right hr (h'.text_inside hr' (x + r.length - 1) (by omega) (by omega))
  · exact h'.text_right hr' (h.text_inside hr (x + r'.length - 1) (by omega) (by omega))


theorem of_bounds {t l u : ℤ} (hs : TextOccurs B s t) (hlt : l < t)
    (htu : t + s.length ≤ u) (hl : B l ≠ A (l - t)) (hu : B u ≠ A (u - t))
    (hm : ∀ z : ℤ, l < z → z < u → B z = A (z - t)) :
    Block A s (textWord B l (u + 1)) (t - l).toNat := by
  have hlen : ((textWord B l (u + 1)).length : ℤ) = u + 1 - l := by
    rw [length_textWord]
    omega
  have hj : (((t - l).toNat : ℕ) : ℤ) = t - l := by omega
  refine ⟨by omega, by omega, hs.occurs_word (by omega) (by omega), ?_, ?_, ?_⟩
  · intro i hi hil
    rw [(TextOccurs.word B l (u + 1)).get i.isLt]
    congr 1
    have hh := hm (l + i.val) (by omega) (by omega)
    convert hh using 1
    congr 1
    omega
  · have hi : 0 < (textWord B l (u + 1)).length := by omega
    rw [(TextOccurs.word B l (u + 1)).get hi, Nat.cast_zero, add_zero]
    intro he
    apply hl
    injection he with he
    convert he using 1
    congr 1
    omega
  · have hi : (textWord B l (u + 1)).length - 1 < (textWord B l (u + 1)).length := by omega
    rw [(TextOccurs.word B l (u + 1)).get hi]
    intro he
    apply hu
    injection he with he
    convert he using 1 <;> congr 1 <;> omega

end Counts.Block

namespace Hierarchical.Layer

variable {α : Type} {V : Set (List α)} {B : ℤ → α} {p : ℕ}

/-- The first up crossing of an occurrence end is an actual containing window. -/
theorem first_containing (D : Layer V B p) (hp : 0 < p) {s : List α} {t : ℤ}
    (hr : D.Records s t) : ∃ a : ℤ,
      a ≤ t ∧ D.first a ≤ t + s.length ∧ t + s.length ≤ D.last a := by
  let k : ℕ := (D.z t - (t + s.length)).toNat + 1
  let K : ℕ := k * p
  have hk : D.z t - (t + s.length) < k := by dsimp only [k]; omega
  have hK : (k : ℤ) ≤ K := by dsimp only [K]; exact_mod_cast Nat.le_mul_of_pos_right k hp
  have he := D.shift_mul k (t - K)
  have hearg : t - (K : ℤ) + (k * p : ℕ) = t := by dsimp only [K]; omega
  rw [hearg] at he
  change D.z t = D.z (t - K) + (K : ℤ) at he
  have hfirst : D.first (t - K) ≤ t + s.length := by
    have hm : D.first (t - K) ≤ D.z (t - K) := D.first_le_last (t - K)
    omega
  have hlast : t + s.length ≤ D.last (t - K + K) := by
    simpa only [sub_add_cancel, last] using hr.2
  obtain ⟨a, _ha, hat, hfa, hla⟩ := D.meets_height (t - K) (t + s.length) K hfirst hlast
  exact ⟨a, by omega, hfa, hla⟩


theorem matching_or_block (D : Layer V B p) (closed : SubstringClosed V) (hp : 0 < p)
    {A : ℤ → α} {s : List α} {t : ℤ} (hr : D.Records s t) (hA : Counts.Matches A s) :
    (∃ a b : ℤ, a ≤ t ∧ t + s.length ≤ b ∧ D.first a ≤ b ∧ b ≤ D.last a ∧
      AgreeOn B (fun x => A (x - t)) a b) ∨
    ∃ r ∈ V, ∃ (y : ℤ) (j : ℕ), D.Records r y ∧ Counts.Block A s r j ∧ y + j = t := by
  classical
  obtain ⟨a, hat, hfa, hla⟩ := D.first_containing hp hr
  have hagree := hr.1.agrees_template hA
  let leftBad := (Finset.Ico a t).filter (fun x => B x ≠ A (x - t))
  by_cases hleft : leftBad.Nonempty
  · let l := leftBad.max' hleft
    have hlmem : l ∈ leftBad := Finset.max'_mem _ _
    have hal : a ≤ l := (Finset.mem_Ico.mp (Finset.mem_filter.mp hlmem).1).1
    have hlt : l < t := (Finset.mem_Ico.mp (Finset.mem_filter.mp hlmem).1).2
    have hlbad : B l ≠ A (l - t) := (Finset.mem_filter.mp hlmem).2
    have hleftgood (x : ℤ) (hlx : l < x) (hxt : x < t) : B x = A (x - t) := by
      by_contra hx
      have hxmem : x ∈ leftBad := Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨by omega, hxt⟩, hx⟩
      have hh : x ≤ l := Finset.le_max' _ _ hxmem
      omega
    have hend : t + s.length ≤ D.z l := hla.trans (D.mono hal)
    let rightBad := (Finset.Ico (t + s.length) (D.z l)).filter (fun x => B x ≠ A (x - t))
    by_cases hright : rightBad.Nonempty
    · let u := rightBad.min' hright
      have humem : u ∈ rightBad := Finset.min'_mem _ _
      have heu : t + s.length ≤ u := (Finset.mem_Ico.mp (Finset.mem_filter.mp humem).1).1
      have huz : u < D.z l := (Finset.mem_Ico.mp (Finset.mem_filter.mp humem).1).2
      have hubad : B u ≠ A (u - t) := (Finset.mem_filter.mp humem).2
      have hinside (x : ℤ) (hlx : l < x) (hxu : x < u) : B x = A (x - t) := by
        by_cases hxt : x < t
        · exact hleftgood x hlx hxt
        · by_cases hxe : x < t + s.length
          · exact hagree x (by omega) hxe
          · by_contra hx
            have hxmem : x ∈ rightBad := Finset.mem_filter.mpr
              ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hx⟩
            have hh : u ≤ x := Finset.min'_le _ _ hxmem
            omega
      let r := textWord B l (u + 1)
      have hrl : D.Records r l := by
        refine ⟨TextOccurs.word B l (u + 1), ?_⟩
        change l + ((textWord B l (u + 1)).length : ℤ) ≤ D.z l
        rw [length_textWord]
        omega
      have hrV : r ∈ V := closed (D.last_actual l)
        ((D.records_iff_prefix r l).mp hrl).isInfix
      refine Or.inr ⟨r, hrV, l, (t - l).toNat, hrl,
        Counts.Block.of_bounds hr.1 hlt heu hlbad hubad hinside, ?_⟩
      omega
    · refine Or.inl ⟨l + 1, D.z l, by omega, hend, ?_, ?_, ?_⟩
      · simp only [first, add_sub_cancel_right, le_refl]
      · exact D.mono (by omega)
      · intro x hlx hxe
        by_cases hxt : x < t
        · exact hleftgood x (by omega) hxt
        · by_cases hxend : x < t + s.length
          · exact hagree x (by omega) hxend
          · by_contra hx
            apply hright
            exact ⟨x, Finset.mem_filter.mpr
              ⟨Finset.mem_Ico.mpr ⟨by omega, hxe⟩, hx⟩⟩
  · refine Or.inl ⟨a, t + s.length, hat, le_rfl, hfa, hla, ?_⟩
    intro x hax hxe
    by_cases hxt : x < t
    · by_contra hx
      apply hleft
      exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hax, hxt⟩, hx⟩⟩
    · exact hagree x (by omega) hxe

/-- A recorded complete bracketing word and one of its eligible inner placements. -/
abbrev BlockWitness (D : Layer V B p) (F : Finset (List α)) (A : ℤ → α) (s : List α) :=
  Σ r : F, D.Occurrence r.val × Counts.BlockPosition A s r.val

def blockedOccurrence (D : Layer V B p) (hp : 0 < p) (per : Function.Periodic B (p : ℤ))
    (F : Finset (List α)) (A : ℤ → α) (s : List α) (w : D.BlockWitness F A s) :
    D.Occurrence s :=
  D.normalize hp per (D.records_suboccurrence w.2.1.property w.2.2.property.2.2.1)

/-- Injectivity holds modulo one primitive turn, even when a block spans many turns. -/
theorem blockedOccurrence_injective (D : Layer V B p) (hp : 0 < p)
    (per : Function.Periodic B (p : ℤ)) (F : Finset (List α)) (A : ℤ → α) (s : List α) :
    Function.Injective (D.blockedOccurrence hp per F A s) := by
  rintro ⟨⟨r, hr⟩, ⟨x, hx⟩, ⟨j, hj⟩⟩ ⟨⟨r', hr'⟩, ⟨x', hx'⟩, ⟨j', hj'⟩⟩ he
  have hemod := congrArg (fun o : D.Occurrence s => (o.val.val : ℤ)) he
  simp only [blockedOccurrence, normalize_val] at hemod
  let q : ℤ := ((x.val : ℤ) + j.val) / p
  let q' : ℤ := ((x'.val : ℤ) + j'.val) / p
  have hT := hx.1.shift (show Function.Periodic B (-q * p) by
    simpa only [Int.cast_id] using per.int_mul (-q))
  have hT' := hx'.1.shift (show Function.Periodic B (-q' * p) by
    simpa only [Int.cast_id] using per.int_mul (-q'))
  have heq : ((x.val : ℤ) + -q * p) + j.val =
      ((x'.val : ℤ) + -q' * p) + j'.val := by
    have h₁ := Int.emod_add_ediv_mul ((x.val : ℤ) + j.val) (p : ℤ)
    have h₂ := Int.emod_add_ediv_mul ((x'.val : ℤ) + j'.val) (p : ℤ)
    change ((x.val : ℤ) + j.val) % (p : ℤ) = ((x'.val : ℤ) + j'.val) % (p : ℤ) at hemod
    dsimp only [q, q']
    simp only [neg_mul]
    omega
  obtain ⟨hstart, hlen⟩ := hj.text_boundaries_unique hj' hT hT' heq
  have hpz : (0 : ℤ) < p := by omega
  have hq : q = q' := by
    have hxb := x.isLt
    have hxb' := x'.isLt
    have hx0 : (0 : ℤ) ≤ x.val := by omega
    have hx0' : (0 : ℤ) ≤ x'.val := by omega
    simp only [neg_mul] at hstart
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have hh : q + 1 ≤ q' := by omega
      have hmul := mul_le_mul_of_nonneg_right hh (le_of_lt hpz)
      linarith
    · have hh : q' + 1 ≤ q := by omega
      have hmul := mul_le_mul_of_nonneg_right hh (le_of_lt hpz)
      linarith
  have hxx : x = x' := by
    apply Fin.ext
    rw [hq] at hstart
    omega
  have hjj : j.val = j'.val := by omega
  have hrr : r = r' := by
    rw [hstart] at hT
    exact hT.unique hT' hlen
  subst r'
  subst x'
  have hjs : j = j' := Fin.ext hjj
  subst j'
  rfl

/-- The exact block count for one periodic layer. -/
theorem card_blockWitness [DecidableEq α] (D : Layer V B p) (F : Finset (List α))
    (A : ℤ → α) (s : List α) :
    Fintype.card (D.BlockWitness F A s) =
      Counts.blocking F A s (fun r => Fintype.card (D.Occurrence r)) := by
  rw [Counts.blocking, Finset.sum_subtype F (fun _ => Iff.rfl)]
  simp only [Fintype.card_sigma, Fintype.card_prod, Counts.coefficient]
  apply Finset.sum_congr rfl
  intro r _
  exact Nat.mul_comm _ _

/-- Normalization is compatible with moving to an inner occurrence. -/
theorem normalize_add (D : Layer V B p) (hp : 0 < p) (per : Function.Periodic B (p : ℤ))
    {r s : List α} {y : ℤ} (hy : D.Records r y) {j : ℕ} (hj : Counts.Occurs r s j) :
    D.normalize hp per (D.records_suboccurrence (D.normalize hp per hy).property hj) =
      D.normalize hp per (D.records_suboccurrence hy hj) := by
  apply Subtype.ext
  apply Fin.ext
  have he : (((D.normalize hp per hy).val.val : ℤ) + (j : ℤ)) % p =
      (y + (j : ℤ)) % p := by
    rw [D.normalize_val]
    simp only [Int.add_emod, Int.emod_emod]
  have h₁ := D.normalize_val hp per
    (D.records_suboccurrence (D.normalize hp per hy).property hj)
  have h₂ := D.normalize_val hp per (D.records_suboccurrence hy hj)
  omega

/-- Unblocked occurrences have actual matching windows; no matching-window
certificate is assumed in selecting an occurrence later in the algorithm. -/
theorem matching_of_not_blocked (D : Layer V B p) (F : Finset (List α))
    (hV : V = (F : Set (List α))) (closed : SubstringClosed V) (hp : 0 < p)
    (per : Function.Periodic B (p : ℤ)) {A : ℤ → α} {s : List α}
    (hA : Counts.Matches A s) (o : D.Occurrence s)
    (ho : ¬ ∃ w : D.BlockWitness F A s, D.blockedOccurrence hp per F A s w = o) :
    ∃ a b : ℤ, a ≤ o.val.val ∧ (o.val.val : ℤ) + s.length ≤ b ∧
      D.first a ≤ b ∧ b ≤ D.last a ∧ AgreeOn B (fun x => A (x - o.val.val)) a b := by
  rcases D.matching_or_block closed hp o.property hA with hm | ⟨r, hr, y, j, hy, hj, he⟩
  · exact hm
  · apply (ho ?_).elim
    have hrF : r ∈ F := by rw [hV] at hr; exact hr
    let w : D.BlockWitness F A s :=
      ⟨⟨r, hrF⟩, D.normalize hp per hy, ⟨⟨j, by change j < r.length + 1; have := hj.2.1; omega⟩, hj⟩⟩
    refine ⟨w, ?_⟩
    change D.normalize hp per
      (D.records_suboccurrence (D.normalize hp per hy).property hj.2.2.1) = o
    rw [D.normalize_add hp per hy hj.2.2.1]
    apply Subtype.ext
    apply Fin.ext
    have hh := D.normalize_val hp per (D.records_suboccurrence hy hj.2.2.1)
    have hm : (y + (j : ℤ)) % p = o.val.val := by
      rw [he, Int.emod_eq_of_lt (by omega) (by exact_mod_cast o.val.isLt)]
    exact_mod_cast hh.trans hm

/-- An occurrence whose full-text alignment equals the template is never blocked. -/
theorem aligned_not_blocked (D : Layer V B p) (hp : 0 < p)
    (per : Function.Periodic B (p : ℤ)) (F : Finset (List α)) {A : ℤ → α} {s : List α}
    (o : D.Occurrence s) (halign : ∀ x : ℤ, B (x + o.val.val) = A x) :
    ¬ ∃ w : D.BlockWitness F A s, D.blockedOccurrence hp per F A s w = o := by
  rintro ⟨⟨r, occ, pos⟩, he⟩
  have hm := congrArg (fun o : D.Occurrence s => (o.val.val : ℤ)) he
  simp only [blockedOccurrence, normalize_val] at hm
  have hleft := pos.property.text_left occ.property.1
  apply hleft
  have hed := Int.emod_add_ediv_mul ((occ.val.val : ℤ) + pos.val.val) (p : ℤ)
  have hper := per.int_mul (((occ.val.val : ℤ) + pos.val.val) / p)
    (-(pos.val.val : ℤ) + o.val.val)
  simp only [Int.cast_id] at hper
  have hecoord : -(pos.val.val : ℤ) + o.val.val +
      (((occ.val.val : ℤ) + pos.val.val) / p) * p = occ.val.val := by omega
  rw [hecoord] at hper
  exact hper.trans (halign (-(pos.val.val : ℤ)))

end Hierarchical.Layer

namespace Hierarchical.Family

variable {α ι : Type} [Fintype ι] {V : Set (List α)}
  {A : ι → ℤ → α} {p : ι → ℕ} (D : ∀ i, Layer V (A i) (p i))

/-- All recorded occurrences, retaining the actual original layer as their owner. -/
abbrev Occurrence (s : List α) := Σ i, (D i).Occurrence s

/-- Bracketing witnesses over the whole fixed family of layers. -/
abbrev BlockWitness (F : Finset (List α)) (B : ℤ → α) (s : List α) :=
  Σ i, (D i).BlockWitness F B s

def blockedOccurrence (hp : ∀ i, 0 < p i)
    (per : ∀ i, Function.Periodic (A i) (p i : ℤ))
    (F : Finset (List α)) (B : ℤ → α) (s : List α) :
    BlockWitness D F B s → Occurrence D s :=
  Sigma.map id (fun i => (D i).blockedOccurrence (hp i) (per i) F B s)

omit [Fintype ι] in
theorem blockedOccurrence_injective (hp : ∀ i, 0 < p i)
    (per : ∀ i, Function.Periodic (A i) (p i : ℤ))
    (F : Finset (List α)) (B : ℤ → α) (s : List α) :
    Function.Injective (blockedOccurrence D hp per F B s) :=
  Function.injective_id.sigma_map
    (fun i => (D i).blockedOccurrence_injective (hp i) (per i) F B s)


theorem card_blockWitness [DecidableEq α] (F : Finset (List α))
    (B : ℤ → α) (s : List α) :
    Fintype.card (BlockWitness D F B s) =
      Counts.blocking F B s (fun r => Fintype.card (Occurrence D r)) := by
  classical
  rw [Fintype.card_sigma]
  simp_rw [Layer.card_blockWitness]
  unfold Counts.blocking
  rw [Finset.sum_comm]
  simp only [Fintype.card_sigma, Finset.mul_sum]

/-- An actual finite pigeonhole argument used by the period-rule forcing step. -/
theorem outside_image_and_pred {X Y : Type} [Fintype X] [Fintype Y]
    (f : X → Y) (P : Y → Prop) [Fintype {y // P y}] (k : ℕ)
    (hX : Fintype.card X + k < Fintype.card Y)
    (hP : Fintype.card {y // P y} ≤ k) :
    ∃ y, (¬ ∃ x, f x = y) ∧ ¬ P y := by
  classical
  by_contra hn
  have cover : ∀ y, (∃ x, f x = y) ∨ P y := by
    intro y
    by_cases h : ∃ x, f x = y
    · exact Or.inl h
    · exact Or.inr (not_not.mp (fun hy => hn ⟨y, h, hy⟩))
  let g : X ⊕ {y // P y} → Y := Sum.elim f Subtype.val
  have hg : Function.Surjective g := by
    intro y
    rcases cover y with ⟨x, hx⟩ | hy
    · exact ⟨Sum.inl x, hx⟩
    · exact ⟨Sum.inr ⟨y, hy⟩, rfl⟩
  have hc := Fintype.card_le_of_surjective g hg
  simp only [Fintype.card_sum] at hc
  omega

omit [Fintype ι] in
/-- An aligned recorded occurrence is outside the global blocking image. -/
theorem aligned_not_blocked (hp : ∀ i, 0 < p i)
    (per : ∀ i, Function.Periodic (A i) (p i : ℤ))
    (F : Finset (List α)) {B : ℤ → α} {s : List α} (o : Occurrence D s)
    (halign : ∀ x : ℤ, A o.1 (x + o.2.val.val) = B x) :
    ¬ ∃ w : BlockWitness D F B s, blockedOccurrence D hp per F B s w = o := by
  rcases o with ⟨i, o⟩
  rintro ⟨⟨j, w⟩, he⟩
  have hij : j = i := congrArg Sigma.fst he
  subst j
  have he' : (D i).blockedOccurrence (hp i) (per i) F B s w = o :=
    eq_of_heq (Sigma.mk.inj_iff.mp he).2
  exact (D i).aligned_not_blocked (hp i) (per i) F o halign ⟨w, he'⟩


theorem blocking_lt_of_aligned [DecidableEq α] (hp : ∀ i, 0 < p i)
    (per : ∀ i, Function.Periodic (A i) (p i : ℤ))
    (F : Finset (List α)) {B : ℤ → α} {s : List α} (o : Occurrence D s)
    (halign : ∀ x : ℤ, A o.1 (x + o.2.val.val) = B x) :
    Counts.blocking F B s (fun r => Fintype.card (Occurrence D r)) <
      Fintype.card (Occurrence D s) := by
  rw [← card_blockWitness D F B s]
  apply Fintype.card_lt_of_injective_not_surjective
    (blockedOccurrence D hp per F B s)
    (blockedOccurrence_injective D hp per F B s)
  intro hsurj
  exact aligned_not_blocked D hp per F o halign (hsurj o)

/-- The excess forced by a period rule produces a matching actual window on a
DIFFERENT aligned text. The exceptional set must have the proved size bound k. -/
theorem matching_different [DecidableEq α] (hp : ∀ i, 0 < p i)
    (per : ∀ i, Function.Periodic (A i) (p i : ℤ))
    (F : Finset (List α)) (hV : V = (F : Set (List α)))
    (closed : SubstringClosed V) {B : ℤ → α} {s : List α}
    (hB : Counts.Matches B s) (k : ℕ)
    (hexcess : Counts.blocking F B s (fun r => Fintype.card (Occurrence D r)) + k <
      Fintype.card (Occurrence D s))
    (hfew : Nat.card {o : Occurrence D s //
      ∀ x : ℤ, A o.1 (x + o.2.val.val) = B x} ≤ k) :
    ∃ o : Occurrence D s, (¬ ∀ x : ℤ, A o.1 (x + o.2.val.val) = B x) ∧
      ∃ a b : ℤ, a ≤ o.2.val.val ∧ (o.2.val.val : ℤ) + s.length ≤ b ∧
        (D o.1).first a ≤ b ∧ b ≤ (D o.1).last a ∧
        AgreeOn (A o.1) (fun x => B (x - o.2.val.val)) a b := by
  classical
  rw [← card_blockWitness D F B s] at hexcess
  obtain ⟨o, ho, hdiff⟩ := outside_image_and_pred
    (blockedOccurrence D hp per F B s)
    (fun o => ∀ x : ℤ, A o.1 (x + o.2.val.val) = B x) k hexcess (by simpa only [Nat.card_eq_fintype_card] using hfew)
  refine ⟨o, hdiff, (D o.1).matching_of_not_blocked F hV closed (hp o.1) (per o.1)
    hB o.2 ?_⟩
  rintro ⟨w, hw⟩
  apply ho
  exact ⟨⟨o.1, w⟩, by cases o; exact congrArg (Sigma.mk _) hw⟩

end Hierarchical.Family

end Superstring

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring

namespace Hierarchical.Threading

variable {α ι : Type} [Fintype ι] {V : Set (List α)}

/-- Stable IDs for every sorted primitive layer of the exact base threading. -/
abbrev LayerId (C : Threading V ι) :=
  Σ g : C.Groups, Fin (Fintype.card (C.Aligned (C.groupText g)))

noncomputable def layerAt (C : Threading V ι) (closed : SubstringClosed V)
    (i : C.LayerId) : Layer V (C.groupText i.1) (C.groupPeriod i.1) :=
  C.layer closed (C.primitive_group i.1).periodic i.2

/-- Reordering a phase and a stable layer ID does not alter the recorded words. -/
noncomputable def occurrenceEquiv (C : Threading V ι) (closed : SubstringClosed V)
    (s : List α) : Family.Occurrence (C.layerAt closed) s ≃ C.Recorded s where
  toFun o := ⟨⟨o.1.1, o.2.val, o.1.2⟩,
    ((C.layerAt closed o.1).records_iff_prefix s o.2.val.val).mp o.2.property⟩
  invFun o := ⟨⟨o.val.1, o.val.2.2⟩, ⟨o.val.2.1,
    ((C.layerAt closed ⟨o.val.1, o.val.2.2⟩).records_iff_prefix s o.val.2.1.val).mpr
      o.property⟩⟩
  left_inv := by rintro ⟨⟨g, j⟩, ⟨r, hr⟩⟩; rfl
  right_inv := by rintro ⟨⟨g, r, j⟩, hr⟩; rfl

end Hierarchical.Threading

namespace Hierarchical.Layer

variable {α : Type} {V : Set (List α)} {A : ℤ → α} {p : ℕ}

/-- Moving a recorded occurrence to any identical full-text alignment preserves
its exact exit-end test. Primitivity, not just periodicity, is essential here. -/
theorem records_at_alignment (D : Layer V A p) (hp : Primitive A p)
    {s : List α} {r t : ℤ} (hr : D.Records s r)
    (halign : ∀ x, A (x + r) = A (x + t)) : D.Records s t := by
  have hper : Function.Periodic A (t - r) := by
    intro x
    have hh := (halign (x - r)).symm
    convert hh using 1 <;> congr 1 <;> omega
  obtain ⟨m, hm⟩ := (hp.period_iff_dvd (t - r)).mp hper
  have he : r + m * p = t := by rw [mul_comm]; omega
  exact he ▸ D.records_shift hp.periodic hr m

end Hierarchical.Layer

namespace Hierarchical.Threading

variable {α ι : Type} [Fintype ι] {V : Set (List α)}

omit [Fintype ι] in
/-- Identical aligned infinite texts necessarily belong to the same primitive
text group; no finite-word coincidence is substituted for this condition. -/
theorem group_eq_of_alignment (C : Threading V ι) (g h : C.Groups) (r t : ℤ)
    (halign : ∀ x, C.groupText h (x + r) = C.groupText g (x + t)) : h = g := by
  have he : C.group (Quotient.out h) = C.group (Quotient.out g) := by
    apply Quotient.sound
    refine ⟨r - t, ?_⟩
    intro x
    have hh := halign (x - t)
    convert hh using 1 <;> congr 1 <;> omega
  exact (Quotient.out_eq h).symm.trans (he.trans (Quotient.out_eq g))

abbrev AlignedOccurrence (C : Threading V ι) (closed : SubstringClosed V)
    (g : C.Groups) (t : ℤ) (s : List α) :=
  {o : Family.Occurrence (C.layerAt closed) s //
    ∀ x : ℤ, C.groupText o.1.1 (x + o.2.val.val) = C.groupText g (x + t)}

noncomputable instance (C : Threading V ι) (closed : SubstringClosed V)
    (g : C.Groups) (t : ℤ) (s : List α) : Fintype (C.AlignedOccurrence closed g t s) := by
  classical
  exact inferInstanceAs (Fintype {o : Family.Occurrence (C.layerAt closed) s //
    ∀ x : ℤ, C.groupText o.1.1 (x + o.2.val.val) = C.groupText g (x + t)})

/-- Forgetting the unique aligned residue retains a qualifying sorted layer. -/
noncomputable def qualifyingLayer (C : Threading V ι) (closed : SubstringClosed V)
    (g : C.Groups) (t : ℤ) (s : List α) (o : C.AlignedOccurrence closed g t s) :
    {j : Fin (Fintype.card (C.Aligned (C.groupText g))) //
      t + s.length ≤ C.sortedExit (C.groupText g) j t} := by
  rcases o with ⟨⟨⟨h, j⟩, r⟩, halign⟩
  have hg := C.group_eq_of_alignment g h r.val.val t halign
  subst h
  exact ⟨j, ((C.layerAt closed ⟨g, j⟩).records_at_alignment (C.primitive_group g)
    r.property halign).2⟩

theorem qualifyingLayer_injective (C : Threading V ι) (closed : SubstringClosed V)
    (g : C.Groups) (t : ℤ) (s : List α) :
    Function.Injective (C.qualifyingLayer closed g t s) := by
  rintro ⟨⟨⟨h, j⟩, r⟩, hr⟩ ⟨⟨⟨h', j'⟩, r'⟩, hr'⟩ he
  have hh := C.group_eq_of_alignment g h r.val.val t hr
  have hh' := C.group_eq_of_alignment g h' r'.val.val t hr'
  subst h
  subst h'
  have hj : j = j' := congrArg Subtype.val he
  subst j'
  have hphase : r.val = r'.val := by
    apply Fin.ext
    have hh := (C.primitive_group g).alignment_unique
      (by omega : 0 ≤ (r.val.val : ℤ)) (by exact_mod_cast r.val.isLt)
      (by omega : 0 ≤ (r'.val.val : ℤ)) (by exact_mod_cast r'.val.isLt)
      (fun x => (hr x).trans (hr' x).symm)
    omega
  have hre : r = r' := Subtype.ext hphase
  subst r'
  rfl


theorem aligned_card_le_qualifying (C : Threading V ι) (closed : SubstringClosed V)
    (g : C.Groups) (t : ℤ) (s : List α) :
    Nat.card (C.AlignedOccurrence closed g t s) ≤
      Nat.card {j : Fin (Fintype.card (C.Aligned (C.groupText g))) //
        t + s.length ≤ C.sortedExit (C.groupText g) j t} := by
  classical
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_le_of_injective (C.qualifyingLayer closed g t s)
      (C.qualifyingLayer_injective closed g t s)

end Hierarchical.Threading

namespace Hierarchical.Processing

/-- The occurrence count tested when choosing a layer. -/
def qualifying {m : ℕ} (z : Fin m → ℤ) (H : ℤ) (p k : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun j => H - (k * p : ℕ) ≤ z j)

theorem qualifying_bound {m : ℕ} (z : Fin m → ℤ) (hz : Monotone z)
    (H : ℤ) (p k : ℕ) (j : Fin m) (hj : z j < H - (k * p : ℕ)) :
    (qualifying z H p k).card ≤ m - 1 - j.val := by
  have hsub : qualifying z H p k ⊆ Finset.Ioi j := by
    intro i hi
    simp only [qualifying, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    apply Finset.mem_Ioi.mpr
    by_contra h
    have hh := hz (le_of_not_gt h)
    omega
  exact (Finset.card_le_card hsub).trans_eq (Fin.card_Ioi j)

/-- The first failed test exists by the number of still available upper layers;
the sharp-band bound comes from the previous, successful, integer test. -/
theorem choose_k {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (z : Fin m → ℤ) (hz : Monotone z) (H : ℤ) (p : ℕ)
    (hH : H ≤ z ⟨m - 1, by omega⟩)
    (hstop : (qualifying z H p n).card ≤ n) :
    ∃ (k : ℕ) (hk : 0 < k) (hkn : k ≤ n),
      (qualifying z H p k).card ≤ k ∧
      H - ((k - 1) * p : ℕ) ≤ z ⟨m - k, by omega⟩ := by
  classical
  have hex : ∃ k : ℕ, 0 < k ∧ (qualifying z H p k).card ≤ k := ⟨n, hn, hstop⟩
  let k := Nat.find hex
  have hspec : 0 < k ∧ (qualifying z H p k).card ≤ k := Nat.find_spec hex
  have hkn : k ≤ n := Nat.find_min' hex ⟨hn, hstop⟩
  refine ⟨k, hspec.1, hkn, hspec.2, ?_⟩
  by_cases hk1 : k = 1
  · simp only [hk1, Nat.sub_self, Nat.zero_mul, Nat.cast_zero, sub_zero]
    exact hH
  · have hprev : k - 1 < (qualifying z H p (k - 1)).card := by
      have hh := Nat.find_min hex (show k - 1 < k by omega)
      have hkprev : 0 < k - 1 := by omega
      exact lt_of_not_ge (fun he => hh ⟨hkprev, he⟩)
    by_contra hsharp
    have hh := qualifying_bound z hz H p (k - 1) ⟨m - k, by omega⟩
      (lt_of_not_ge hsharp)
    change (qualifying z H p (k - 1)).card ≤ m - 1 - (m - k) at hh
    omega


theorem wide_band {α : Type} {V : Set (List α)} {A : ℤ → α} {p k : ℕ}
    (H L : Layer V A p) (hp : 0 < p) (hk : 0 < k) (t : ℤ)
    (hsharp : H.first t - L.last t ≤ ((k - 1) * p : ℕ)) :
    ∀ x : ℤ, H.first x - L.last x ≤ (k * p : ℕ) := by
  intro x
  let r := (t - x) % (p : ℤ)
  let q := (t - x) / (p : ℤ)
  let y := t - r
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
  have hrp : r < p := Int.emod_lt_of_pos _ (by omega)
  have hyt : y ≤ t := by dsimp only [y]; omega
  have hty : t ≤ y + p := by dsimp only [y]; omega
  have he : x + q * p = y := by
    have hdiv := Int.emod_add_ediv_mul (t - x) (p : ℤ)
    dsimp only [r, q, y]
    omega
  have hH := H.first_mono hyt
  have hL := L.last_mono hty
  have hLshift : L.last (y + p) = L.last y + p := L.shift y
  rw [hLshift] at hL
  have hHx := H.first_shift_int q x
  have hLx := L.shift_int q x
  rw [he] at hHx hLx
  change L.last y = L.last x + q * p at hLx
  have hprod : ((k - 1) * p : ℕ) + p = k * p := by
    calc
      (k - 1) * p + p = (k - 1) * p + 1 * p := by rw [one_mul]
      _ = (k - 1 + 1) * p := (Nat.add_mul _ _ _).symm
      _ = k * p := by rw [Nat.sub_add_cancel hk]
  have hprod' : (((k - 1) * p : ℕ) : ℤ) + p = (k * p : ℕ) := by exact_mod_cast hprod
  omega

end Hierarchical.Processing

namespace Hierarchical.Layer

variable {α : Type} {V : Set (List α)} {A : ℤ → α} {p : ℕ}

theorem normalize_alignment (D : Layer V A p) (hp : 0 < p)
    (per : Function.Periodic A (p : ℤ)) {s : List α} {t : ℤ}
    (h : D.Records s t) :
    ∀ x, A (x + (D.normalize hp per h).val.val) = A (x + t) := by
  intro x
  rw [D.normalize_val hp per h]
  have hh := per.int_mul (t / (p : ℤ)) (x + t % (p : ℤ))
  have he := Int.emod_add_ediv_mul t (p : ℤ)
  simp only [Int.cast_id] at hh
  have he' : x + t % (p : ℤ) + t / (p : ℤ) * p = x + t := by omega
  rw [he'] at hh
  exact hh.symm

end Hierarchical.Layer

namespace Counts.Data

open Hierarchical
variable {α : Type} [DecidableEq α] [Inhabited α]

theorem family_occurrence_count (D : Data α) (hD : D.WellFormed) {s : List α}
    (hs : s ≠ []) :
    Fintype.card (Family.Occurrence ((D.threading hD).layerAt hD.closed) s) =
      D.count s := by
  rw [Fintype.card_congr ((D.threading hD).occurrenceEquiv hD.closed s)]
  exact D.recorded_count hD hs

/-- Empty recorded words do not disturb this identity: every positive blocking
coefficient has a strictly longer, hence nonempty, bracketing word. -/
theorem blocking_layer_count (D : Data α) (hD : D.WellFormed)
    (A : ℤ → α) (s : List α) :
    blocking D.vertices A s
      (fun r => Fintype.card (Family.Occurrence ((D.threading hD).layerAt hD.closed) r)) =
      blocking D.vertices A s D.count := by
  apply blocking_congr
  intro r _hr hlen
  apply D.family_occurrence_count hD
  intro he
  simp only [he, List.length_nil] at hlen
  omega

/-- The exact period rule plus the exact base-layer histogram forces a genuine
matching record with a different aligned bi-infinite text. -/
theorem period_forces_matching (D : Data α) (hD : D.WellFormed)
    {A : ℤ → α} {w v : List α} {p k : ℕ}
    (hp : 0 < p) (hk : 0 < k) (hper : Function.Periodic A (p : ℤ))
    (hw : w ∈ D.vertices) (hwne : w ≠ []) (hv : v ∈ D.vertices)
    (hmv : Matches A v) (hmw : Matches A w)
    (hlen : w.length + k * p = v.length)
    (ov : Family.Occurrence ((D.threading hD).layerAt hD.closed) v)
    (halign : ∀ x : ℤ, (D.threading hD).groupText ov.1.1 (x + ov.2.val.val) = A x)
    (hfew : Nat.card {o : Family.Occurrence ((D.threading hD).layerAt hD.closed) w //
      ∀ x : ℤ, (D.threading hD).groupText o.1.1 (x + o.2.val.val) = A x} ≤ k) :
    ∃ o : Family.Occurrence ((D.threading hD).layerAt hD.closed) w,
      (¬ ∀ x : ℤ, (D.threading hD).groupText o.1.1 (x + o.2.val.val) = A x) ∧
      ∃ a b : ℤ, a ≤ o.2.val.val ∧ (o.2.val.val : ℤ) + w.length ≤ b ∧
        ((D.threading hD).layerAt hD.closed o.1).first a ≤ b ∧
        b ≤ ((D.threading hD).layerAt hD.closed o.1).last a ∧
        AgreeOn ((D.threading hD).groupText o.1.1) (fun x => A (x - o.2.val.val)) a b := by
  have hvne : v ≠ [] := by
    intro he
    have hwpos := List.length_pos_iff.mpr hwne
    simp only [he, List.length_nil] at hlen
    omega
  have pos := fun i : (D.threading hD).LayerId =>
    ((D.threading hD).primitive_group i.1).positive
  have per := fun i : (D.threading hD).LayerId =>
    ((D.threading hD).primitive_group i.1).periodic
  have ht := Family.blocking_lt_of_aligned ((D.threading hD).layerAt hD.closed)
    pos per D.vertices ov halign
  rw [D.blocking_layer_count hD, D.family_occurrence_count hD hvne] at ht
  have hexcess := D.period_rule hp hk hper hw hwne hv hmv hmw hlen ht
  apply Family.matching_different ((D.threading hD).layerAt hD.closed)
    pos per D.vertices rfl hD.closed hmw k _ hfew
  rw [D.blocking_layer_count hD, D.family_occurrence_count hD hwne]
  omega

end Counts.Data

namespace Hierarchical

variable {α : Type}

/-- Reindexing a text changes coordinates, never the represented graph word. -/
theorem textWord_reindex (A : ℤ → α) (c a b : ℤ) :
    textWord (fun x => A (x + c)) a b = textWord A (a + c) (b + c) := by
  apply List.ext_getElem
  · simp only [length_textWord]
    congr 1
    omega
  · intro i hi hj
    simp only [textWord, List.getElem_ofFn]
    congr 1
    omega

namespace Layer

variable {V : Set (List α)} {A B : ℤ → α} {p q : ℕ}


structure Record (D : Layer V B q) (A : ℤ → α) where
  offset : ℤ
  start : ℤ
  stop : ℤ
  first_le : D.first (start + offset) ≤ stop + offset
  le_last : stop + offset ≤ D.last (start + offset)
  agree : AgreeOn A (fun x => B (x + offset)) start stop

namespace Record

variable {D : Layer V B q} (R : D.Record A)

theorem start_le_stop : R.start ≤ R.stop := by
  have hh := D.start_le_first (R.start + R.offset)
  have hh' := R.first_le
  omega

theorem word_eq : textWord A R.start R.stop =
    textWord B (R.start + R.offset) (R.stop + R.offset) :=
  (textWord_eq_of_agree R.agree).trans (textWord_reindex B R.offset R.start R.stop)

theorem word_mem : textWord A R.start R.stop ∈ V :=
  R.word_eq ▸ D.actual (R.start + R.offset) (R.stop + R.offset) R.first_le R.le_last

theorem touched {s t : List α} (P : Path V s t)
    (hv : P.Visits (textWord A R.start R.stop)) : D.TouchedBy P := by
  refine ⟨R.start + R.offset, R.stop + R.offset, R.first_le, R.le_last, ?_⟩
  rwa [R.word_eq] at hv

theorem length_lt (hp : 0 < p) (hq : 0 < q)
    (hA : Function.Periodic A (p : ℤ)) (hB : Function.Periodic B (q : ℤ))
    (hdiff : A ≠ fun x => B (x + R.offset)) : R.stop - R.start < p + q := by
  apply agreement_bound A (fun x => B (x + R.offset)) p q hp hq hA _ hdiff
    R.start R.stop R.agree
  intro x
  simpa only [add_right_comm] using hB (x + R.offset)

theorem same_period_length_lt (hp : 0 < p)
    (hA : Function.Periodic A (p : ℤ)) (hB : Function.Periodic B (p : ℤ))
    (hdiff : A ≠ fun x => B (x + R.offset)) : R.stop - R.start < p := by
  apply same_period_agreement_bound A (fun x => B (x + R.offset)) p hp hA _ hdiff
    R.start R.stop R.agree
  intro x
  simpa only [add_right_comm] using hB (x + R.offset)

end Record
end Layer
end Hierarchical

namespace Counts.Data

open Hierarchical
variable {α : Type} [DecidableEq α] [Inhabited α]


theorem hard_case_record (D : Data α) (hD : D.WellFormed)
    (g : (D.threading hD).Groups)
    (j : Fin (Fintype.card ((D.threading hD).Aligned ((D.threading hD).groupText g))))
    (t : ℤ) (k : ℕ) (hk : 0 < k)
    (hhard : t + (k * (D.threading hD).groupPeriod g : ℕ) <
      ((D.threading hD).layerAt hD.closed ⟨g, j⟩).first t)
    (hfew : (Processing.qualifying
      (fun l => (D.threading hD).sortedExit ((D.threading hD).groupText g) l t)
      (((D.threading hD).layerAt hD.closed ⟨g, j⟩).first t)
      ((D.threading hD).groupPeriod g) k).card ≤ k) :
    ∃ i : (D.threading hD).LayerId,
      ∃ R : ((D.threading hD).layerAt hD.closed i).Record ((D.threading hD).groupText g),
        R.start ≤ t ∧
        ((D.threading hD).layerAt hD.closed ⟨g, j⟩).first t -
          (k * (D.threading hD).groupPeriod g : ℕ) ≤ R.stop ∧
        ((D.threading hD).groupText g ≠
          fun x => (D.threading hD).groupText i.1 (x + R.offset)) ∧
        R.stop - R.start < (D.threading hD).groupPeriod g + (D.threading hD).groupPeriod i.1 ∧
        (i.1 = g → R.stop - R.start < (D.threading hD).groupPeriod g) := by
  classical
  let C := D.threading hD
  let A := C.groupText g
  let p := C.groupPeriod g
  let L := C.layerAt hD.closed ⟨g, j⟩
  let H := L.first t
  let v := textWord A t H
  let w := textWord A t (H - (k * p : ℕ))
  have hp : 0 < p := (C.primitive_group g).positive
  have per : Function.Periodic A (p : ℤ) := (C.primitive_group g).periodic
  change t + (k * p : ℕ) < H at hhard
  have hv : v ∈ D.vertices := L.first_actual t
  have hw : w ∈ D.vertices := hD.closed hv (textWord_infix A le_rfl
    (by omega : t ≤ H - (k * p : ℕ)) (by omega))
  have hwlen : t + (w.length : ℤ) = H - (k * p : ℕ) := by
    dsimp only [w]
    rw [length_textWord]
    omega
  have hvlen : t + (v.length : ℤ) = H := by
    dsimp only [v]
    rw [length_textWord]
    omega
  have hwne : w ≠ [] := by
    intro he
    simp only [he, List.length_nil, Nat.cast_zero, add_zero] at hwlen
    omega
  have hlen : w.length + k * p = v.length := by omega
  have hvrec : L.Records v t := ⟨TextOccurs.word A t H, by
    rw [hvlen]
    exact L.first_le_last t⟩
  let ov : Family.Occurrence (C.layerAt hD.closed) v :=
    ⟨⟨g, j⟩, L.normalize hp per hvrec⟩
  have halign : ∀ x, C.groupText ov.1.1 (x + ov.2.val.val) = A (x + t) :=
    L.normalize_alignment hp per hvrec
  have hmv : Matches (fun x => A (x + t)) v := by
    intro i
    simpa only [add_comm] using (TextOccurs.word A t H i)
  have hmw : Matches (fun x => A (x + t)) w := by
    intro i
    simpa only [add_comm] using (TextOccurs.word A t (H - (k * p : ℕ)) i)
  have hper : Function.Periodic (fun x => A (x + t)) (p : ℤ) := by
    intro x
    simpa only [add_right_comm] using per (x + t)
  have hcard : Nat.card {l : Fin (Fintype.card (C.Aligned A)) //
      t + w.length ≤ C.sortedExit A l t} ≤ k := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simpa only [hwlen, Processing.qualifying] using hfew
  have hAligned : Nat.card (C.AlignedOccurrence hD.closed g t w) ≤ k :=
    (C.aligned_card_le_qualifying hD.closed g t w).trans hcard
  obtain ⟨o, hdiff, a, b, har, hrb, hfa, hbl, hagree⟩ :=
    D.period_forces_matching hD hp hk hper hw hwne hv hmv hmw hlen ov halign hAligned
  let c : ℤ := o.2.val.val - t
  let R : (C.layerAt hD.closed o.1).Record A := {
    offset := c
    start := a - c
    stop := b - c
    first_le := by simpa only [sub_add_cancel] using hfa
    le_last := by simpa only [sub_add_cancel] using hbl
    agree := by
      intro x hax hxb
      have hh := hagree (x + c) (by omega) (by omega)
      change C.groupText o.1.1 (x + c) = A (x + c - o.2.val.val + t) at hh
      have he : x + c - (o.2.val.val : ℤ) + t = x := by dsimp only [c]; omega
      rw [he] at hh
      exact hh.symm }
  have hd : A ≠ fun x => C.groupText o.1.1 (x + R.offset) := by
    intro he
    apply hdiff
    intro x
    have hh := congrFun he (x + t)
    change A (x + t) = C.groupText o.1.1 (x + t + c) at hh
    have hc : x + t + c = x + (o.2.val.val : ℤ) := by dsimp only [c]; omega
    rw [hc] at hh
    exact hh.symm
  refine ⟨o.1, R, ?_, ?_, hd,
    R.length_lt hp (C.primitive_group o.1.1).positive per
      (C.primitive_group o.1.1).periodic hd, ?_⟩
  · change a - c ≤ t
    dsimp only [c]
    omega
  · change H - (k * p : ℕ) ≤ b - c
    dsimp only [c]
    omega
  · intro he
    apply R.same_period_length_lt hp per _ hd
    simpa only [he] using (C.primitive_group o.1.1).periodic

end Counts.Data

end Superstring

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.Hierarchical

variable {α : Type}

/-- A finite chain of windows has a simultaneous greatest start and end.
The sum is used only to choose a point of the already totally ordered chain. -/
theorem greatest_window {ι : Type} (I : Finset ι) (s h : ι → ℤ)
    (hne : I.Nonempty)
    (hchain : ∀ i ∈ I, ∀ j ∈ I,
      (s i ≤ s j ∧ h i ≤ h j) ∨ (s j ≤ s i ∧ h j ≤ h i)) :
    ∃ j ∈ I, ∀ i ∈ I, s i ≤ s j ∧ h i ≤ h j := by
  obtain ⟨j, hj, hmax⟩ := I.exists_max_image (fun i => s i + h i) hne
  refine ⟨j, hj, fun i hi => ?_⟩
  rcases hchain i hi j hj with hh | hh
  · exact hh
  · have := hmax i hi
    constructor <;> omega

/-- Finite ordered-window routing. Repeated windows and distinct requesters
at the same coordinates are allowed; this is not a disjointness assumption. -/
theorem finite_ordered_windows {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V)
    {ι : Type} (I : Finset ι) (s h : ι → ℤ)
    (hchain : ∀ i ∈ I, ∀ j ∈ I,
      (s i ≤ s j ∧ h i ≤ h j) ∨ (s j ≤ s i ∧ h j ≤ h i))
    (hvalid : ∀ i ∈ I, s i ≤ h i ∧ textWord A (s i) (h i) ∈ V)
    (a b c d : ℤ) (hab : a ≤ b) (hcd : c ≤ d) (hac : a ≤ c) (hbd : b ≤ d)
    (hstart : textWord A a b ∈ V) (hend : textWord A c d ∈ V)
    (hbounds : ∀ i ∈ I, a ≤ s i ∧ s i ≤ c ∧ b ≤ h i ∧ h i ≤ d) :
    ∃ P : Path V (textWord A a b) (textWord A c d),
      P.cost = (d - b).toNat ∧ ∀ i ∈ I, P.Visits (textWord A (s i) (h i)) := by
  classical
  induction I using Finset.strongInductionOn generalizing a b c d with
  | _ I ih =>
    by_cases hn : I.Nonempty
    · obtain ⟨j, hj, hmax⟩ := greatest_window I s h hn hchain
      have hsub : I.erase j ⊂ I := Finset.erase_ssubset hj
      have hmem {i} (hi : i ∈ I.erase j) : i ∈ I := Finset.mem_of_mem_erase hi
      obtain ⟨P, hcP, hvP⟩ := ih _ hsub
        (fun i hi k hk => hchain i (hmem hi) k (hmem hk))
        (fun i hi => hvalid i (hmem hi)) a b (s j) (h j) hab (hvalid j hj).1
        (hbounds j hj).1 (hbounds j hj).2.2.1 hstart (hvalid j hj).2
        (fun i hi => ⟨(hbounds i (hmem hi)).1, (hmax i (hmem hi)).1,
          (hbounds i (hmem hi)).2.2.1, (hmax i (hmem hi)).2⟩)
      obtain ⟨Q, hcQ, _⟩ := ordered_windows closed A letters (hvalid j hj).1 hcd
        (hbounds j hj).2.1 (hbounds j hj).2.2.2 (hvalid j hj).2 hend
      refine ⟨P.trans Q, ?_, ?_⟩
      · simp only [Path.cost_trans, hcP, hcQ]
        have := (hbounds j hj).2.2.1
        have := (hbounds j hj).2.2.2
        omega
      · intro i hi
        by_cases he : i = j
        · subst i
          exact Or.inl (Path.visits_end P)
        · exact Or.inl (hvP i (Finset.mem_erase.mpr ⟨he, hi⟩))
    · obtain ⟨P, hcP, _⟩ := ordered_windows closed A letters hab hcd hac hbd hstart hend
      exact ⟨P, hcP, fun i hi => (hn ⟨i, hi⟩).elim⟩

/-- Host excursion for any finite chain of later targets, including the empty
case. No enumeration/sorting oracle is assumed by the conclusion. -/
theorem host_excursion_finite {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (q p₀ : ℕ)
    (hp₀ : 0 < p₀) (per : Function.Periodic A (q : ℤ))
    (a₀ b₀ e₀ : ℤ) (he₀ : a₀ + p₀ < e₀) (heb : e₀ ≤ b₀)
    (hR : textWord A a₀ b₀ ∈ V) (hshort : b₀ < a₀ + q + p₀)
    {ι : Type} (I : Finset ι) (s h : ι → ℤ)
    (hchain : ∀ i ∈ I, ∀ j ∈ I,
      (s i ≤ s j ∧ h i ≤ h j) ∨ (s j ≤ s i ∧ h j ≤ h i))
    (hbounds : ∀ i ∈ I, a₀ ≤ s i ∧ s i ≤ a₀ + q ∧ s i ≤ h i ∧
      b₀ ≤ h i ∧ h i < a₀ + q + p₀)
    (hQ : ∀ i ∈ I, textWord A (s i) (h i) ∈ V) :
    ∃ P : Path V (textWord A a₀ e₀) (textWord A a₀ e₀),
      P.cost = q ∧ P.Visits (textWord A a₀ b₀) ∧
      (∀ e, e₀ ≤ e → e ≤ b₀ → P.Visits (textWord A a₀ e)) ∧
      (∀ i ∈ I, P.Visits (textWord A (s i) (h i))) ∧
      ∃ w, P.Visits w ∧ w.length < p₀ := by
  by_cases hn : I.Nonempty
  · obtain ⟨j, hj, hmax⟩ := greatest_window I s h hn hchain
    have hae : a₀ ≤ e₀ := by omega
    have hab : a₀ ≤ b₀ := by omega
    have hE : textWord A a₀ e₀ ∈ V := closed hR (textWord_infix A le_rfl hae heb)
    obtain ⟨U, hcU, hvU⟩ := window_append closed A hae heb hR
    obtain ⟨P, hcP, hvP⟩ := finite_ordered_windows closed A letters I s h hchain
      (fun i hi => ⟨(hbounds i hi).2.2.1, hQ i hi⟩) a₀ b₀ (s j) (h j)
      hab (hbounds j hj).2.2.1 (hbounds j hj).1 (hbounds j hj).2.2.2.1 hR (hQ j hj)
      (fun i hi => ⟨(hbounds i hi).1, (hmax i hi).1,
        (hbounds i hi).2.2.2.1, (hmax i hi).2⟩)
    have heqE := textWord_translate A q per a₀ e₀
    obtain ⟨D, hcD, w, hvD, hw⟩ := ordered_windows closed A letters
      (hbounds j hj).2.2.1 (show a₀ + q ≤ e₀ + q by omega)
      (hbounds j hj).2.1 (show h j ≤ e₀ + q by
        have := (hbounds j hj).2.2.2.2; omega) (hQ j hj) (heqE.symm ▸ hE)
    refine ⟨((U.trans P).trans D).copy rfl heqE, ?_, ?_, ?_, ?_, w, ?_, ?_⟩
    · simp only [Path.cost_copy, Path.cost_trans, hcU, hcP, hcD]
      have := (hbounds j hj).2.2.2.1
      have := (hbounds j hj).2.2.2.2
      omega
    · exact (Path.visits_copy ..).mpr (Or.inl (Or.inl (Path.visits_end U)))
    · intro e he he'
      exact (Path.visits_copy ..).mpr (Or.inl (Or.inl (hvU e he he')))
    · intro i hi
      exact (Path.visits_copy ..).mpr (Or.inl (Or.inr (hvP i hi)))
    · exact (Path.visits_copy ..).mpr (Or.inr hvD)
    · have := (hbounds j hj).2.2.2.2
      omega
  · obtain ⟨P, hc, hr, hv, hs⟩ := host_excursion_single closed A letters q p₀ hp₀ per
      a₀ b₀ e₀ he₀ heb hshort hR
    exact ⟨P, hc, hr, hv, fun i hi => (hn ⟨i, hi⟩).elim, hs⟩

end Superstring.Hierarchical

namespace Superstring.Hierarchical

variable {α β ρ : Type}


structure BlockPlan (V : Set (List α)) (β ρ : Type) [LE ρ] where
  content : β → Set (List α)
  reserve : β → ℕ
  free : β → ℕ
  rank : β → ρ
  target : β → Option β
  record : β → List α
  target_mem : ∀ i j, target i = some j → record i ∈ content j
  link : ∀ i, ∃ P : Loop V, P.cost ≤ reserve i ∧
    (∀ w ∈ content i, P.Visits w) ∧ P.Visits (record i)
  internal : ∀ i, ∃ P : Loop V, P.cost + free i ≤ reserve i ∧
    ∀ w ∈ content i, P.Visits w
  short : ∀ i j, target i = some j → i ≠ j → rank j ≤ rank i →
    ∃ P : Loop V, P.cost ≤ reserve i ∧
      (∀ w ∈ content i, P.Visits w) ∧ P.Visits (record i) ∧
      ∃ w, P.Visits w ∧ w.length ≤ free j
  self_short : ∀ i, target i = some i → ∃ w ∈ content i, w.length ≤ free i

namespace BlockPlan

variable {V : Set (List α)} [LinearOrder ρ] (B : BlockPlan V β ρ)


theorem connect (closed : SubstringClosed V) (I : Finset β) (P : Path V [] [])
    (hready : ∀ i ∈ I, match B.target i with
      | none => P.Visits (B.record i)
      | some j => j ∈ I ∨ P.Visits (B.record i)) :
    ∃ Q : Path V [] [], Q.cost ≤ P.cost + ∑ i ∈ I, B.reserve i ∧
      (∀ w, P.Visits w → Q.Visits w) ∧
      ∀ i ∈ I, ∀ w ∈ B.content i, Q.Visits w := by
  classical
  induction I using Finset.strongInductionOn generalizing P with
  | _ I ih =>
    have finish (J : Finset β) (hJI : J ⊆ I) (hJn : J.Nonempty)
        (Q : Path V [] []) (hQc : Q.cost ≤ P.cost + ∑ i ∈ J, B.reserve i)
        (hPQ : ∀ w, P.Visits w → Q.Visits w)
        (hQv : ∀ i ∈ J, ∀ w ∈ B.content i, Q.Visits w) :
        ∃ R : Path V [] [], R.cost ≤ P.cost + ∑ i ∈ I, B.reserve i ∧
          (∀ w, P.Visits w → R.Visits w) ∧
          ∀ i ∈ I, ∀ w ∈ B.content i, R.Visits w := by
      have hreadyQ : ∀ i ∈ I \ J, match B.target i with
          | none => Q.Visits (B.record i)
          | some j => j ∈ I \ J ∨ Q.Visits (B.record i) := by
        intro i hi
        have hr := hready i (Finset.mem_sdiff.mp hi).1
        cases ht : B.target i with
        | none => simpa only [ht] using hPQ _ (by simpa only [ht] using hr)
        | some j =>
          simp only [ht] at hr ⊢
          rcases hr with hj | hv
          · by_cases hjJ : j ∈ J
            · exact Or.inr (hQv j hjJ _ (B.target_mem i j ht))
            · exact Or.inl (Finset.mem_sdiff.mpr ⟨hj, hjJ⟩)
          · exact Or.inr (hPQ _ hv)
      obtain ⟨R, hRc, hQR, hRv⟩ := ih (I \ J) (Finset.sdiff_ssubset hJI hJn) Q hreadyQ
      refine ⟨R, ?_, fun w hw => hQR w (hPQ w hw), ?_⟩
      · have hs := Finset.sum_sdiff hJI (f := B.reserve)
        omega
      · intro i hi w hw
        by_cases hj : i ∈ J
        · exact hQR w (hQv i hj w hw)
        · exact hRv i (Finset.mem_sdiff.mpr ⟨hi, hj⟩) w hw
    by_cases hn : I.Nonempty
    · obtain ⟨i, hi, hmax⟩ := I.exists_max_image B.rank hn
      have ordinary (hv : P.Visits (B.record i)) :
          ∃ Q : Path V [] [], Q.cost ≤ P.cost + ∑ i ∈ I, B.reserve i ∧
            (∀ w, P.Visits w → Q.Visits w) ∧
            ∀ j ∈ I, ∀ w ∈ B.content j, Q.Visits w := by
        obtain ⟨L, hcL, hvL, hrL⟩ := B.link i
        obtain ⟨Q, hcQ, hvQ⟩ := P.splice L.path (B.record i) hv hrL
        apply finish {i} (Finset.singleton_subset_iff.mpr hi) (Finset.singleton_nonempty i) Q
        · simp only [Finset.sum_singleton]
          change Q.cost = P.cost + L.cost at hcQ
          omega
        · intro w hw
          exact (hvQ w).mpr (Or.inl hw)
        · intro j hj w hw
          have : j = i := Finset.mem_singleton.mp hj
          subst j
          exact (hvQ w).mpr (Or.inr (hvL w hw))
      cases ht : B.target i with
      | none =>
        exact ordinary (by simpa only [ht] using hready i hi)
      | some j =>
        have hr : j ∈ I ∨ P.Visits (B.record i) := by simpa only [ht] using hready i hi
        rcases hr with hj | hv
        · by_cases he : i = j
          · subst j
            obtain ⟨L, hcL, hvL⟩ := B.internal i
            obtain ⟨w, hw, hlen⟩ := B.self_short i ht
            obtain ⟨R, hcR, hvR⟩ := L.root_at closed w (hvL w hw)
            apply finish {i} (Finset.singleton_subset_iff.mpr hi) (Finset.singleton_nonempty i)
              (P.trans R)
            · simp only [Finset.sum_singleton, Path.cost_trans]
              omega
            · intro v hv
              exact Or.inl hv
            · intro k hk v hv
              have : k = i := Finset.mem_singleton.mp hk
              subst k
              exact Or.inr (hvR v (hvL v hv))
          · obtain ⟨L, hcL, hvL, hrL, w, hw, hlen⟩ := B.short i j ht he (hmax j hj)
            obtain ⟨D, hcD, hvD⟩ := B.internal j
            obtain ⟨A, hcA, hvA⟩ := L.path.splice D.path (B.record i) hrL
              (hvD _ (B.target_mem i j ht))
            let E : Loop V := ⟨L.base, A⟩
            have hew : E.Visits w := (hvA w).mpr (Or.inl hw)
            obtain ⟨R, hcR, hvR⟩ := E.root_at closed w hew
            have hcE : E.cost = L.cost + D.cost := hcA
            apply finish {i, j} (by simp only [Finset.insert_subset_iff,
              Finset.singleton_subset_iff]; exact ⟨hi, hj⟩) (Finset.insert_nonempty _ _)
              (P.trans R)
            · simp only [Finset.sum_pair he, Path.cost_trans]
              omega
            · intro v hv
              exact Or.inl hv
            · intro k hk v hv
              simp only [Finset.mem_insert, Finset.mem_singleton] at hk
              rcases hk with rfl | rfl
              · exact Or.inr (hvR v ((hvA v).mpr (Or.inl (hvL v hv))))
              · exact Or.inr (hvR v ((hvA v).mpr (Or.inr (hvD v hv))))
        · exact ordinary hv
    · have he : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      subst I
      exact ⟨P, by simp, fun _ h => h, by simp⟩

end BlockPlan
end Superstring.Hierarchical

namespace Superstring.Hierarchical

variable {α : Type} {V : Set (List α)} {A : ℤ → α} {q : ℕ}

namespace Layer

/-- Actual vertices on one monotone host path inherit the order of starts;
within a vertical run they are ordered by their ends. -/
theorem window_order (D : Layer V A q) {a b c d : ℤ}
    (hb : b ≤ D.last a) (hd : D.first c ≤ d) (hac : a < c) : b ≤ d := by
  exact hb.trans ((D.mono (by omega : a ≤ c - 1)).trans hd)

end Layer

/-- One child group's single recorded host window, in host coordinates.
This includes the actual recipient and full-window agreement, not just a common
substring or an assumed possibility of connecting it. -/
structure HostedGroup (D : Layer V A q) where
  text : ℤ → α
  period : ℕ
  positive : 0 < period
  periodic : Function.Periodic text (period : ℤ)
  start : ℤ
  stop : ℤ
  first_le : D.first start ≤ stop
  le_last : stop ≤ D.last start
  agree : AgreeOn text A start stop
  foreign : text ≠ A

namespace HostedGroup

variable {D : Layer V A q} (H : HostedGroup D)

theorem start_le_stop : H.start ≤ H.stop :=
  (D.start_le_first H.start).trans H.first_le

theorem host_mem : textWord A H.start H.stop ∈ V :=
  D.actual H.start H.stop H.first_le H.le_last

theorem child_mem : textWord H.text H.start H.stop ∈ V :=
  (textWord_eq_of_agree H.agree).symm ▸ H.host_mem

theorem length_lt (hq : 0 < q) (per : Function.Periodic A (q : ℤ)) :
    H.stop - H.start < H.period + q :=
  agreement_bound H.text A H.period q H.positive hq H.periodic per H.foreign
    H.start H.stop H.agree

/-- Cross-child overlaps cannot contain a full sum of their periods. -/
theorem overlap_lt (J : HostedGroup D)
    (hstart : H.start ≤ J.start) (hstop : H.stop ≤ J.stop)
    (hne : H.text ≠ J.text) : H.stop - J.start < H.period + J.period := by
  apply agreement_bound H.text J.text H.period J.period H.positive J.positive
    H.periodic J.periodic hne J.start H.stop
  intro x hx hy
  exact (H.agree x (hstart.trans hx) hy).trans (J.agree x hx (hy.trans_le hstop)).symm

/-- Overlap with the next q-translate of another record transports that
child's full text. -/
theorem next_overlap_lt (J : HostedGroup D) (per : Function.Periodic A (q : ℤ))
    (hstart : H.start ≤ J.start + q) (hstop : H.stop ≤ J.stop + q)
    (hne : H.text ≠ fun x => J.text (x - q)) :
    H.stop - (J.start + q) < H.period + J.period := by
  apply agreement_bound H.text (fun x => J.text (x - q)) H.period J.period
    H.positive J.positive H.periodic (fun x => by
      simpa only [add_sub_right_comm] using J.periodic (x - q)) hne
    (J.start + q) H.stop
  intro x hx hy
  have hp : A x = A (x - q) := by simpa only [sub_add_cancel] using per (x - q)
  exact (H.agree x (hstart.trans hx) hy).trans
    (hp.trans (J.agree (x - q) (by omega) (by omega)).symm)

/-- The primitive-layer requester uses an actual child vertex at this record. -/
structure Request (H : HostedGroup D) where
  layer : Layer V H.text H.period
  stop : ℤ
  first_le : layer.first H.start ≤ stop
  le_last : stop ≤ layer.last H.start
  long : H.start + H.period < stop
  margin : stop ≤ H.stop - H.period

namespace Request

variable {H : HostedGroup D} (R : H.Request)

theorem word_mem : textWord H.text H.start R.stop ∈ V :=
  R.layer.actual H.start R.stop R.first_le R.le_last

theorem touched {s t : List α} (P : Path V s t)
    (hv : P.Visits (textWord H.text H.start R.stop)) : R.layer.TouchedBy P :=
  ⟨H.start, R.stop, R.first_le, R.le_last, hv⟩

end Request
end HostedGroup
end Superstring.Hierarchical

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.Hierarchical

variable {α ι κ : Type} {V : Set (List α)} {A : ℤ → α} {q : ℕ}

/-- The complete host construction for records normalized into one cyclic turn.
Different children share at most their Fine-Wilf overlap; any number of layers
of one child may request at its single record. Their distinct budgets are summed
with multiplicity. -/
theorem host_normalized (closed : SubstringClosed V) (D : Layer V A q)
    (hq : 0 < q) (per : Function.Periodic A (q : ℤ)) (letters : ∀ x, [A x] ∈ V)
    (H : ι → HostedGroup D) (g : κ → ι) (R : ∀ i, (H (g i)).Request)
    (child_letters : ∀ j x, [(H j).text x] ∈ V)
    (different : ∀ i j, i ≠ j → ∀ c, (H i).text ≠ fun x => (H j).text (x + c))
    (I : Finset κ) (z : ι) (hz : ∃ i ∈ I, g i = z)
    (hmin : ∀ i ∈ I, (H z).period ≤ (H (g i)).period)
    (horder : ∀ i ∈ I,
      (H z).start ≤ (H (g i)).start ∧ (H (g i)).start ≤ (H z).start + q ∧
      (H z).stop ≤ (H (g i)).stop ∧ (H (g i)).stop ≤ (H z).stop + q) :
    ∃ Q : Path V [] [], Q.cost ≤ q + ∑ i ∈ I, (H (g i)).period ∧
      D.TouchedBy Q ∧ ∀ i ∈ I, (R i).layer.TouchedBy Q := by
  classical
  let initial := I.filter (fun i => g i = z)
  let later := I.filter (fun i => g i ≠ z)
  have hinit : initial.Nonempty := by
    obtain ⟨i, hi, he⟩ := hz
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, he⟩⟩
  obtain ⟨i₀, hi₀, emin⟩ := initial.exists_min_image (fun i => (R i).stop) hinit
  have hi₀I : i₀ ∈ I := (Finset.mem_filter.mp hi₀).1
  have hi₀g : g i₀ = z := (Finset.mem_filter.mp hi₀).2
  let T := (H z).start + q
  let s := fun i => min ((H (g i)).start + (H (g i)).period) T
  let h := fun i => max (R i).stop (H z).stop
  have he₀ : (H z).start + (H z).period < (R i₀).stop := by
    simpa only [hi₀g] using (R i₀).long
  have he₀b : (R i₀).stop ≤ (H z).stop := by
    have hh := (R i₀).margin
    simp only [hi₀g] at hh
    omega
  have hbase : (H z).stop < T + (H z).period := by
    have hh := (H z).length_lt hq per
    dsimp only [T]
    omega
  have bounds (i : κ) (hi : i ∈ later) :
      (H (g i)).start ≤ s i ∧ s i ≤ (H (g i)).start + (H (g i)).period ∧
      s i ≤ h i ∧ h i ≤ (H (g i)).stop ∧ (R i).stop ≤ h i ∧
      h i ≤ (R i).stop + (H (g i)).period ∧
      (H z).start ≤ s i ∧ s i ≤ T ∧ (H z).stop ≤ h i ∧ h i < T + (H z).period := by
    obtain ⟨hiI, hig⟩ := Finset.mem_filter.mp hi
    have ho := horder i hiI
    have hd : (H z).text ≠ (H (g i)).text := by
      simpa only [add_zero] using different z (g i) (Ne.symm hig) 0
    have hl := (H z).overlap_lt (H (g i)) ho.1 ho.2.2.1 hd
    have hr := (H (g i)).next_overlap_lt (H z) per ho.2.1 ho.2.2.2
      (by simpa only [sub_eq_add_neg] using different (g i) z hig (-(q : ℤ)))
    exact host_target_bounds (H z).start (H z).stop (H (g i)).start (H (g i)).stop
      (R i).stop T (H z).period (H (g i)).period (hmin i hiI) ho.1 ho.2.1
      ho.2.2.1 (R i).long (R i).margin hl hr hbase
  have raw (i j : κ) (hij : g i ≠ g j)
      (ha : (H (g i)).start ≤ (H (g j)).start)
      (hb : (H (g i)).stop ≤ (H (g j)).stop) :
      (H (g i)).start + (H (g i)).period ≤ (H (g j)).start + (H (g j)).period ∧
      (R i).stop ≤ (R j).stop := by
    have hd : (H (g i)).text ≠ (H (g j)).text := by
      simpa only [add_zero] using different (g i) (g j) hij 0
    have hov := (H (g i)).overlap_lt (H (g j)) ha hb hd
    have hlong := (R i).long
    have hmargin := (R i).margin
    have hlong' := (R j).long
    constructor <;> omega
  have chain : ∀ i ∈ later, ∀ j ∈ later,
      (s i ≤ s j ∧ h i ≤ h j) ∨ (s j ≤ s i ∧ h j ≤ h i) := by
    intro i _ j _
    have hc :
        ((H (g i)).start + (H (g i)).period ≤ (H (g j)).start + (H (g j)).period ∧
          (R i).stop ≤ (R j).stop) ∨
        ((H (g j)).start + (H (g j)).period ≤ (H (g i)).start + (H (g i)).period ∧
          (R j).stop ≤ (R i).stop) := by
      by_cases he : g i = g j
      · rcases le_total (R i).stop (R j).stop with hr | hr
        · exact Or.inl ⟨by rw [he], hr⟩
        · exact Or.inr ⟨by rw [he], hr⟩
      · by_cases ha : (H (g i)).start < (H (g j)).start
        · exact Or.inl (raw i j he ha.le
            (D.window_order (H (g i)).le_last (H (g j)).first_le ha))
        · by_cases hb : (H (g j)).start < (H (g i)).start
          · exact Or.inr (raw j i (Ne.symm he) hb.le
              (D.window_order (H (g j)).le_last (H (g i)).first_le hb))
          · rcases le_total (H (g i)).stop (H (g j)).stop with hs | hs
            · exact Or.inl (raw i j he (by omega) hs)
            · exact Or.inr (raw j i (Ne.symm he) (by omega) hs)
    rcases hc with hc | hc
    · exact Or.inl ⟨min_le_min_right _ hc.1, max_le_max_right _ hc.2⟩
    · exact Or.inr ⟨min_le_min_right _ hc.1, max_le_max_right _ hc.2⟩
  have hQ (i : κ) (hi : i ∈ later) : textWord A (s i) (h i) ∈ V :=
    closed (H (g i)).host_mem (textWord_infix A (bounds i hi).1
      (bounds i hi).2.2.1 (bounds i hi).2.2.2.1)
  obtain ⟨P, hcP, hrP, hvP, htP, w, hwP, hwlen⟩ := host_excursion_finite closed A letters
    q (H z).period (H z).positive per (H z).start (H z).stop (R i₀).stop
    he₀ he₀b (H z).host_mem hbase later s h chain
    (fun i hi => ⟨(bounds i hi).2.2.2.2.2.2.1, (bounds i hi).2.2.2.2.2.2.2.1,
      (bounds i hi).2.2.1, (bounds i hi).2.2.2.2.2.2.2.2.1,
      (bounds i hi).2.2.2.2.2.2.2.2.2⟩) hQ
  let K := {i // i ∈ later}
  have attachments (i : K) : ∃ F : Loop V, F.base = textWord A (s i.val) (h i.val) ∧
      F.cost = (H (g i.val)).period ∧
      F.Visits (textWord (H (g i.val)).text (H (g i.val)).start (R i.val).stop) := by
    have hb := bounds i.val i.property
    have heq : textWord (H (g i.val)).text (s i.val) (h i.val) =
        textWord A (s i.val) (h i.val) := textWord_eq_of_agree (fun x hx hy =>
      (H (g i.val)).agree x (hb.1.trans hx) (hy.trans_le hb.2.2.2.1))
    obtain ⟨F, hcF, hvF⟩ := request_attachment closed (H (g i.val)).text
      (child_letters (g i.val)) (H (g i.val)).period (H (g i.val)).periodic
      (by have := (R i.val).long; omega) hb.2.2.1 hb.1 hb.2.1 hb.2.2.2.2.1
      hb.2.2.2.2.2.1 (R i.val).word_mem (heq.symm ▸ hQ i.val i.property)
    exact ⟨⟨_, F.copy heq heq⟩, rfl, by simpa only [Loop.cost, Path.cost_copy] using hcF,
      (Path.visits_copy ..).mpr hvF⟩
  choose F hbF hcF hvF using attachments
  let E : Loop V := ⟨_, P⟩
  obtain ⟨Q, hcQ, hvQ, haQ⟩ := Loop.root_attachments closed E F Finset.univ (H z).period
    (fun i _ => ⟨_, htP i.val i.property, by
      rw [← hbF i]; exact Path.visits_start (F i).path⟩) ⟨w, hwP, hwlen.le⟩
  have hsum : (∑ i : K, (F i).cost) = ∑ i ∈ later, (H (g i)).period := by
    simp_rw [hcF]
    exact Finset.sum_coe_sort later (fun i => (H (g i)).period)
  have hn₀ : i₀ ∉ later := by
    intro hh
    exact (Finset.mem_filter.mp hh).2 hi₀g
  have hs : (H z).period + ∑ i ∈ later, (H (g i)).period ≤ ∑ i ∈ I, (H (g i)).period := by
    have hsub : insert i₀ later ⊆ I := Finset.insert_subset hi₀I (Finset.filter_subset _ _)
    have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ =>
      Nat.zero_le ((H (g i)).period))
    simpa only [Finset.sum_insert hn₀, hi₀g] using hh
  refine ⟨Q, ?_, ⟨(H z).start, (H z).stop, (H z).first_le, (H z).le_last, hvQ _ hrP⟩, ?_⟩
  · change Q.cost ≤ P.cost + (∑ i : K, (F i).cost) + (H z).period at hcQ
    rw [hcP, hsum] at hcQ
    omega
  · intro i hi
    apply (R i).touched Q
    by_cases he : g i = z
    · have hlo := emin i (Finset.mem_filter.mpr ⟨hi, he⟩)
      have hmargin := (R i).margin
      have hlong := (R i).long
      have eqw : textWord (H (g i)).text (H (g i)).start (R i).stop =
          textWord A (H (g i)).start (R i).stop := textWord_eq_of_agree
        (fun x hx hy => (H (g i)).agree x hx (by omega))
      rw [eqw, show (H (g i)).start = (H z).start from congrArg (fun j => (H j).start) he]
      apply hvQ _ (hvP _ hlo _)
      simp only [he] at hmargin
      omega
    · exact haQ ⟨i, Finset.mem_filter.mpr ⟨hi, he⟩⟩ (Finset.mem_univ _) _
        (hvF ⟨i, Finset.mem_filter.mpr ⟨hi, he⟩⟩)

end Superstring.Hierarchical

namespace Superstring.Hierarchical
namespace Layer

variable {α : Type} {V : Set (List α)} {A : ℤ → α} {p : ℕ}

/-- Simultaneous coordinate transport of a child text and its layer. -/
def translate (D : Layer V A p) (δ : ℤ) : Layer V (fun x => A (x - δ)) p where
  z x := D.z (x - δ) + δ
  mono := by
    intro x y h
    have hh := D.mono (sub_le_sub_right h δ)
    dsimp only
    omega
  lower x := by
    have hh := D.lower (x - δ)
    have he : x - 1 - δ = (x - δ) - 1 := by omega
    rw [he]
    omega
  shift x := by
    have he : x + p - δ = (x - δ) + p := by omega
    rw [he, D.shift]
    omega
  actual x e hfirst hlast := by
    have he : textWord (fun x => A (x - δ)) x e = textWord A (x - δ) (e - δ) := by
      simpa only [sub_eq_add_neg] using textWord_reindex A (-δ) x e
    rw [he]
    apply D.actual (x - δ) (e - δ)
    · have hx : x - δ - 1 = x - 1 - δ := by omega
      rw [hx]
      omega
    · omega

@[simp] theorem translate_first (D : Layer V A p) (δ x : ℤ) :
    (D.translate δ).first x = D.first (x - δ) + δ := by
  change D.z (x - 1 - δ) + δ = D.z (x - δ - 1) + δ
  congr 2
  omega

@[simp] theorem translate_last (D : Layer V A p) (δ x : ℤ) :
    (D.translate δ).last x = D.last (x - δ) + δ := rfl

theorem translate_touched (D : Layer V A p) (δ : ℤ) {s t : List α}
    (P : Path V s t) : (D.translate δ).TouchedBy P ↔ D.TouchedBy P := by
  constructor
  · rintro ⟨x, e, hf, hl, hv⟩
    rw [translate_first] at hf
    rw [translate_last] at hl
    refine ⟨x - δ, e - δ, by omega, by omega, ?_⟩
    have he : textWord (fun x => A (x - δ)) x e = textWord A (x - δ) (e - δ) := by
      simpa only [sub_eq_add_neg] using textWord_reindex A (-δ) x e
    rwa [he] at hv
  · rintro ⟨x, e, hf, hl, hv⟩
    refine ⟨x + δ, e + δ, ?_, ?_, ?_⟩
    · rw [translate_first, add_sub_cancel_right]
      omega
    · rw [translate_last, add_sub_cancel_right]
      omega
    · have he : textWord (fun x => A (x - δ)) (x + δ) (e + δ) = textWord A x e := by
        simpa only [← sub_eq_add_neg, add_sub_cancel_right] using
          textWord_reindex A (-δ) (x + δ) (e + δ)
      rwa [he]

/-- A cyclic record can be placed between a fixed actual record and its next
copy in BOTH coordinates. Equal-start vertical runs are treated explicitly. -/
theorem normalize_window (D : Layer V A p) (hp : 0 < p)
    {a b a₀ b₀ : ℤ} (hf : D.first a ≤ b) (hl : b ≤ D.last a)
    (hf₀ : D.first a₀ ≤ b₀) (hl₀ : b₀ ≤ D.last a₀) :
    ∃ m : ℤ, a₀ ≤ a + m * p ∧ a + m * p ≤ a₀ + p ∧
      b₀ ≤ b + m * p ∧ b + m * p ≤ b₀ + p := by
  let m : ℤ := -((a - a₀) / p)
  let r : ℤ := a + m * p
  let e : ℤ := b + m * p
  have hr : r = a₀ + (a - a₀) % p := by
    have hh := Int.emod_add_ediv_mul (a - a₀) (p : ℤ)
    dsimp only [r, m]
    simp only [neg_mul]
    omega
  have hrlo : a₀ ≤ r := by
    have hh := Int.emod_nonneg (a - a₀) (show (p : ℤ) ≠ 0 by omega)
    omega
  have hrhi : r < a₀ + p := by
    have hh := Int.emod_lt_of_pos (a - a₀) (show (0 : ℤ) < p by omega)
    omega
  have hfe : D.first r ≤ e := by
    dsimp only [r, e]
    rw [D.first_shift_int]
    omega
  have hle : e ≤ D.last r := by
    dsimp only [r, e, last]
    rw [D.shift_int]
    change b ≤ D.z a at hl
    omega
  have hfnext : D.first (a₀ + p) ≤ b₀ + p := by
    rw [D.first_shift]
    omega
  have hehi : e ≤ b₀ + p := D.window_order hle hfnext hrhi
  by_cases helo : b₀ ≤ e
  · exact ⟨m, hrlo, hrhi.le, helo, hehi⟩
  · have hre : r = a₀ := by
      by_contra hn
      have hh := D.window_order hl₀ hfe (by omega : a₀ < r)
      omega
    have hfn : D.first (r + p) ≤ e + p := by
      rw [D.first_shift]
      omega
    have helon : b₀ ≤ e + p := D.window_order hl₀ hfn (by omega)
    refine ⟨m + 1, ?_, ?_, ?_, ?_⟩ <;>
      dsimp only [r, e] at * <;> linarith

end Layer
end Superstring.Hierarchical

namespace Superstring.Hierarchical
namespace HostedGroup

variable {α : Type} {V : Set (List α)} {A : ℤ → α} {q : ℕ} {D : Layer V A q}

/-- Translate a hosted record by a whole number of host periods, transporting
its entire child text, not only its interval endpoints. -/
def translate (H : HostedGroup D) (per : Function.Periodic A (q : ℤ)) (m : ℤ) :
    HostedGroup D where
  text x := H.text (x - m * q)
  period := H.period
  positive := H.positive
  periodic x := by simpa only [add_sub_right_comm] using H.periodic (x - m * q)
  start := H.start + m * q
  stop := H.stop + m * q
  first_le := by
    rw [D.first_shift_int]
    have := H.first_le
    omega
  le_last := by
    change H.stop + m * q ≤ D.z (H.start + m * q)
    rw [D.shift_int]
    have := H.le_last
    change H.stop ≤ D.z H.start at this
    omega
  agree := by
    intro x hx hy
    have hp : A (x - m * q) = A x := by
      simpa using per.sub_int_mul_eq (x := x) m
    exact (H.agree (x - m * q) (by omega) (by omega)).trans hp
  foreign := by
    intro he
    apply H.foreign
    funext x
    have hh := congrFun he (x + m * q)
    change H.text (x + m * q - m * q) = A (x + m * q) at hh
    have hp : A (x + m * q) = A x := by simpa using (per.int_mul m) x
    simpa only [add_sub_cancel_right, hp] using hh

namespace Request

/-- All requester windows and layer coordinates travel with their one record. -/
def translate {H : HostedGroup D} (R : H.Request)
    (per : Function.Periodic A (q : ℤ)) (m : ℤ) : (H.translate per m).Request where
  layer := R.layer.translate (m * q)
  stop := R.stop + m * q
  first_le := by
    change (R.layer.translate (m * q)).first (H.start + m * q) ≤ R.stop + m * q
    rw [Layer.translate_first, add_sub_cancel_right]
    have := R.first_le
    omega
  le_last := by
    change R.stop + m * q ≤ (R.layer.translate (m * q)).last (H.start + m * q)
    rw [Layer.translate_last, add_sub_cancel_right]
    have := R.le_last
    omega
  long := by
    have := R.long
    change H.start + m * q + H.period < R.stop + m * q
    omega
  margin := by
    have := R.margin
    change R.stop + m * q ≤ H.stop + m * q - H.period
    omega

end Request
end HostedGroup


theorem host_requests {α ι κ : Type} {V : Set (List α)} {A : ℤ → α} {q : ℕ}
    (closed : SubstringClosed V) (D : Layer V A q)
    (hq : 0 < q) (per : Function.Periodic A (q : ℤ)) (letters : ∀ x, [A x] ∈ V)
    (H : ι → HostedGroup D) (g : κ → ι) (R : ∀ i, (H (g i)).Request)
    (child_letters : ∀ j x, [(H j).text x] ∈ V)
    (different : ∀ i j, i ≠ j → ∀ c, (H i).text ≠ fun x => (H j).text (x + c))
    (I : Finset κ) (hne : I.Nonempty) :
    ∃ Q : Path V [] [], Q.cost ≤ q + ∑ i ∈ I, (H (g i)).period ∧
      D.TouchedBy Q ∧ ∀ i ∈ I, (R i).layer.TouchedBy Q := by
  classical
  obtain ⟨i₀, hi₀, hmin⟩ := I.exists_min_image (fun i => (H (g i)).period) hne
  let z := g i₀
  have shifts : ∀ j, ∃ m : ℤ, (j = z → m = 0) ∧
      (H z).start ≤ (H j).start + m * q ∧ (H j).start + m * q ≤ (H z).start + q ∧
      (H z).stop ≤ (H j).stop + m * q ∧ (H j).stop + m * q ≤ (H z).stop + q := by
    intro j
    by_cases he : j = z
    · subst j
      exact ⟨0, fun _ => rfl, by omega, by omega, by omega, by omega⟩
    · obtain ⟨m, hm⟩ := D.normalize_window hq (H j).first_le (H j).le_last
        (H z).first_le (H z).le_last
      exact ⟨m, fun hj => (he hj).elim, hm⟩
  choose m hm hbound using shifts
  have hmz : m z = 0 := hm z rfl
  let H' := fun j => (H j).translate per (m j)
  let R' := fun i => (R i).translate per (m (g i))
  have hd : ∀ i j, i ≠ j → ∀ c, (H' i).text ≠ fun x => (H' j).text (x + c) := by
    intro i j hij c he
    apply different i j hij (m i * q + c - m j * q)
    funext x
    have hh := congrFun he (x + m i * q)
    change (H i).text (x + m i * q - m i * q) =
      (H j).text (x + m i * q + c - m j * q) at hh
    have hx : x + m i * q + c - m j * q = x + (m i * q + c - m j * q) := by omega
    simpa only [add_sub_cancel_right, hx] using hh
  have ho : ∀ i ∈ I,
      (H' z).start ≤ (H' (g i)).start ∧ (H' (g i)).start ≤ (H' z).start + q ∧
      (H' z).stop ≤ (H' (g i)).stop ∧ (H' (g i)).stop ≤ (H' z).stop + q := by
    intro i _
    simpa only [H', HostedGroup.translate, hmz, zero_mul, add_zero] using hbound (g i)
  obtain ⟨Q, hcQ, hvQ, hrQ⟩ := host_normalized closed D hq per letters H' g R'
    (fun j x => child_letters j (x - m j * q)) hd I z ⟨i₀, hi₀, rfl⟩ hmin ho
  refine ⟨Q, hcQ, hvQ, fun i hi => ?_⟩
  exact ((R i).layer.translate_touched (m (g i) * q) Q).mp (hrQ i hi)

end Superstring.Hierarchical

namespace Superstring.Hierarchical
namespace Layer

variable {α : Type} {V : Set (List α)} {A : ℤ → α} {p : ℕ}

/-- The actual vertices of a fixed base layer, independent of its coordinate
presentation. This is not the larger set of all recorded prefixes. -/
def Content (L : Layer V A p) : Set (List α) :=
  {w | ∃ x e, L.first x ≤ e ∧ e ≤ L.last x ∧ w = textWord A x e}

theorem content_mem (L : Layer V A p) {w : List α} (hw : w ∈ L.Content) : w ∈ V := by
  obtain ⟨x, e, hf, hl, rfl⟩ := hw
  exact L.actual x e hf hl

theorem touched_iff (L : Layer V A p) {s t : List α} (P : Path V s t) :
    L.TouchedBy P ↔ ∃ w ∈ L.Content, P.Visits w := by
  constructor
  · rintro ⟨x, e, hf, hl, hv⟩
    exact ⟨_, ⟨x, e, hf, hl, rfl⟩, hv⟩
  · rintro ⟨_, ⟨x, e, hf, hl, rfl⟩, hv⟩
    exact ⟨x, e, hf, hl, hv⟩

theorem translate_content (L : Layer V A p) (δ : ℤ) :
    (L.translate δ).Content = L.Content := by
  ext w
  constructor
  · rintro ⟨x, e, hf, hl, rfl⟩
    refine ⟨x - δ, e - δ, ?_, ?_, ?_⟩
    · rw [translate_first] at hf
      omega
    · rw [translate_last] at hl
      omega
    · simpa only [sub_eq_add_neg] using textWord_reindex A (-δ) x e
  · rintro ⟨x, e, hf, hl, rfl⟩
    refine ⟨x + δ, e + δ, ?_, ?_, ?_⟩
    · rw [translate_first, add_sub_cancel_right]
      omega
    · rw [translate_last, add_sub_cancel_right]
      omega
    · symm
      simpa only [← sub_eq_add_neg, add_sub_cancel_right] using
        textWord_reindex A (-δ) (x + δ) (e + δ)

/-- Every actual vertex is retained when one full base turn is materialized. -/
theorem content_loop (L : Layer V A p) (closed : SubstringClosed V)
    (hp : 0 < p) (per : Function.Periodic A (p : ℤ)) :
    ∃ P : Loop V, P.cost = p ∧ ∀ w ∈ L.Content, P.Visits w := by
  obtain ⟨P, hc, hv⟩ := L.full_turn closed hp per 0
  refine ⟨⟨_, P⟩, hc, ?_⟩
  rintro w ⟨x, e, hf, hl, rfl⟩
  exact hv x e hf hl


theorem below_baseline (L B : Layer V A p) (closed : SubstringClosed V)
    (letters : ∀ x, [A x] ∈ V) (per : Function.Periodic A (p : ℤ))
    (hbelow : ∀ x, L.z x ≤ B.z x) {a b : ℤ}
    (hbf : B.first a ≤ b) (hbl : b ≤ B.last a) (hlen : b - a < 2 * p) :
    (∃ Q : Path V [] [], Q.cost ≤ p ∧ L.TouchedBy Q) ∨
    (∃ Q : Path V (textWord A a b) (textWord A a b),
      Q.cost ≤ p ∧ L.TouchedBy Q) := by
  by_cases hs : L.HasShort p
  · obtain ⟨x, e, hf, hl, hshort⟩ := hs
    obtain ⟨Q, hc, hv⟩ := Path.root_loop closed _ (L.actual x e hf hl)
    exact Or.inl ⟨Q, hc.trans_le hshort, x, e, hf, hl, hv⟩
  · have hlf : L.first a ≤ b := (hbelow (a - 1)).trans hbf
    have hlong := L.first_long_of_not_short p hs a
    have hfl := L.first_le_last a
    obtain ⟨Q, hc, hv, _⟩ := individual_link closed A letters p p per L
      ((B.start_le_first a).trans hbf) (B.actual a b hbf hbl) hlf
      (by omega) (by omega)
    exact Or.inr ⟨Q, hc.le, hv⟩

end Layer


theorem fill_layers {α ι : Type} {V : Set (List α)}
    (closed : SubstringClosed V) {A : ι → ℤ → α} {p : ι → ℕ}
    (L : ∀ i, Layer V (A i) (p i)) (hp : ∀ i, 0 < p i)
    (per : ∀ i, Function.Periodic (A i) (p i : ℤ))
    (I : Finset ι) (P : Loop V) (htouch : ∀ i ∈ I, (L i).TouchedBy P.path) :
    ∃ Q : Loop V, Q.base = P.base ∧ Q.cost ≤ P.cost + ∑ i ∈ I, p i ∧
      (∀ w, P.Visits w → Q.Visits w) ∧
      ∀ i ∈ I, ∀ w ∈ (L i).Content, Q.Visits w := by
  classical
  choose F hc hv using fun i => (L i).content_loop closed (hp i) (per i)
  have hmeet : ∀ i ∈ I, P.Meets (F i) := by
    intro i hi
    obtain ⟨w, hw, hP⟩ := ((L i).touched_iff P.path).mp (htouch i hi)
    exact ⟨w, hP, hv i w hw⟩
  obtain ⟨Q, hb, hcost, hP, hF⟩ := Loop.attach F I P hmeet
  refine ⟨Q, hb, ?_, hP, fun i hi w hw => hF i hi w (hv i w hw)⟩
  simpa only [hc] using hcost

/-- The easy round trip through the top first window visits every lower first
height on its up path. Its cost is the top window's length, not a sum of lengths. -/
theorem root_upper {α ι : Type} {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (closed : SubstringClosed V) (L : ι → Layer V A p) (top : ι)
    (hupper : ∀ i x, (L i).z x ≤ (L top).z x) (t : ℤ) :
    ∃ Q : Path V [] [], Q.cost = (textWord A t ((L top).first t)).length ∧
      ∀ i, (L i).TouchedBy Q := by
  let H := (L top).first t
  have htH : t ≤ H := (L top).start_le_first t
  have hs : textWord A t H ∈ V := (L top).first_actual t
  obtain ⟨U, hcU, hvU⟩ := window_append closed A (le_refl t) htH hs
  let W := textWord A t H
  let D := Path.deletePrefix closed W [] (by simpa using hs)
  let Q : Path V [] [] :=
    (U.copy (textWord_self A t) rfl).trans (D.copy (by simp [W]) rfl)
  refine ⟨Q, ?_, ?_⟩
  · simp only [Q, Path.cost_trans, Path.cost_copy, hcU, D, Path.cost_deletePrefix,
      Nat.add_zero, length_textWord]
    rfl
  · intro i
    refine ⟨t, (L i).first t, le_rfl, (L i).first_le_last t, ?_⟩
    exact Or.inl ((Path.visits_copy ..).mpr
      (hvU _ ((L i).start_le_first t) (hupper i (t - 1))))

end Superstring.Hierarchical

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.Hierarchical

/-- A distinguished rotation exists by inspecting one finite period. -/
theorem exists_greatest_rotation {α : Type} [LinearOrder α] (A : ℤ → α)
    (p : ℕ) (hp : 0 < p) (per : Function.Periodic A (p : ℤ)) :
    ∃ t : ℤ, 0 ≤ t ∧ t < p ∧ ∀ x, forward A x ≤ forward A t := by
  classical
  let : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  obtain ⟨i, _, hmax⟩ := Finset.univ.exists_max_image
    (fun i : Fin p => forward A i.val) Finset.univ_nonempty
  refine ⟨i.val, by omega, by omega, ?_⟩
  intro x
  let r : Fin p := ⟨(x % (p : ℤ)).toNat, by
    have h0 := Int.emod_nonneg x (show (p : ℤ) ≠ 0 by omega)
    have h1 := Int.emod_lt_of_pos x (show (0 : ℤ) < p by omega)
    omega⟩
  have hr : (r.val : ℤ) = x % p := by
    dsimp only [r]
    exact Int.toNat_of_nonneg (Int.emod_nonneg x (by omega))
  have he : forward A x = forward A r.val := by
    apply congrArg toLex
    funext n
    have hdiv := Int.emod_add_ediv_mul x (p : ℤ)
    have hm := per.sub_int_mul_eq (x := x + n) (x / p)
    simp only [Int.cast_id] at hm
    have hx : x + n - (x / p) * p = r.val + n := by omega
    rw [hx] at hm
    exact hm.symm
  rw [he]
  exact hmax r (Finset.mem_univ _)

namespace Layer

variable {α : Type} {V : Set (List α)} {A : ℤ → α} {p : ℕ}

/-- Every text letter occurs on the fixed layer's last actual window. -/
theorem letters (L : Layer V A p) (closed : SubstringClosed V) (x : ℤ) : [A x] ∈ V := by
  have hlen : x + 1 ≤ L.last x := by
    have := L.start_le_first (x + 1)
    simpa only [first, last, add_sub_cancel_right] using this
  have hword : textWord A x (x + 1) = [A x] := by
    simp [textWord]
  rw [← hword]
  exact closed (L.last_actual x) (textWord_infix A le_rfl (by omega) hlen)

end Layer

/-- Finite ordered primitive-text groups supplied by the fixed base
 decomposition. All fields describe actual layers, never connecting walks. -/
structure LayerCollection {α : Type} (V : Set (List α)) (G : Type) where
  text : G → ℤ → α
  period : G → ℕ
  size : G → ℕ
  positive : ∀ g, 0 < period g
  nonempty : ∀ g, 0 < size g
  periodic : ∀ g, Function.Periodic (text g) (period g : ℤ)
  layer : ∀ g, Fin (size g) → Layer V (text g) (period g)
  ordered : ∀ g (i j : Fin (size g)), i ≤ j → ∀ x, (layer g i).z x ≤ (layer g j).z x
  different : ∀ g h, g ≠ h → ∀ c, text g ≠ fun x => text h (x + c)

namespace LayerCollection

variable {α G : Type} {V : Set (List α)} (C : LayerCollection V G)

abbrev Id := Σ g, Fin (C.size g)

def layerAt (i : C.Id) : Layer V (C.text i.1) (C.period i.1) := C.layer i.1 i.2

noncomputable def distinguished [LinearOrder α] (g : G) : ℤ :=
  (exists_greatest_rotation (C.text g) (C.period g) (C.positive g) (C.periodic g)).choose

theorem distinguished_max [LinearOrder α] (g : G) (x : ℤ) :
    forward (C.text g) x ≤ forward (C.text g) (C.distinguished g) :=
  (exists_greatest_rotation (C.text g) (C.period g) (C.positive g) (C.periodic g)).choose_spec.2.2 x

noncomputable def rank [LinearOrder α] (g : G) : Lex (ℕ → α) :=
  forward (C.text g) (C.distinguished g)

theorem letters (closed : SubstringClosed V) (g : G) (x : ℤ) : [C.text g x] ∈ V :=
  (C.layer g ⟨0, C.nonempty g⟩).letters closed x

end LayerCollection
end Superstring.Hierarchical

namespace Superstring.Hierarchical

/-- Constant-period version of base saturation, retaining every already
visited vertex. The finite index set is allowed to omit other layers. -/
theorem fill_same_layers {α ι : Type} {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (closed : SubstringClosed V) (L : ι → Layer V A p) (hp : 0 < p)
    (per : Function.Periodic A (p : ℤ)) (I : Finset ι) (P : Loop V)
    (htouch : ∀ i ∈ I, (L i).TouchedBy P.path) :
    ∃ Q : Loop V, Q.base = P.base ∧ Q.cost ≤ P.cost + I.card * p ∧
      (∀ w, P.Visits w → Q.Visits w) ∧
      ∀ i ∈ I, ∀ w ∈ (L i).Content, Q.Visits w := by
  obtain ⟨Q, hb, hc, hv, hl⟩ := fill_layers closed L (fun _ => hp) (fun _ => per) I P htouch
  exact ⟨Q, hb, by simpa using hc, hv, hl⟩

theorem forward_shift {α : Type} (A : ℤ → α) (c t : ℤ) :
    forward (fun x => A (x + c)) t = forward A (t + c) := by
  apply congrArg toLex
  funext n
  change A (t + n + c) = A (t + c + n)
  congr 1
  omega

namespace LayerCollection

variable {α G : Type} {V : Set (List α)} (C : LayerCollection V G)


def groupIds (g : G) (I : Finset (Fin (C.size g))) : Finset C.Id :=
  I.map ⟨Sigma.mk g, fun _ _ h => eq_of_heq (Sigma.mk.inj h).2⟩

@[simp] theorem card_groupIds (g : G) (I : Finset (Fin (C.size g))) :
    (C.groupIds g I).card = I.card := Finset.card_map _

theorem groupIds_same (g : G) (I : Finset (Fin (C.size g))) {i : C.Id}
    (hi : i ∈ C.groupIds g I) : i.1 = g := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
  rfl

/-- A concrete outgoing plan. Its local walks include each constituent base
turn exactly once in the reserve. -/
structure PlannedBlock [LinearOrder α] where
  source : G
  members : Finset C.Id
  nonempty : members.Nonempty
  same : ∀ i ∈ members, i.1 = source
  target : C.Id
  record : (C.layerAt target).Record (C.text source)
  foreign : C.text source ≠ fun x => C.text target.1 (x + record.offset)
  link : ∃ P : Loop V, P.cost ≤ 2 * (members.card * C.period source) ∧
    (∀ i ∈ members, ∀ w ∈ (C.layerAt i).Content, P.Visits w) ∧
    P.Visits (textWord (C.text source) record.start record.stop)
  internal : ∃ P : Loop V, P.cost + C.period source ≤ 2 * (members.card * C.period source) ∧
    ∀ i ∈ members, ∀ w ∈ (C.layerAt i).Content, P.Visits w
  short : C.rank target.1 ≤ C.rank source →
    ∃ P : Loop V, P.cost ≤ 2 * (members.card * C.period source) ∧
      (∀ i ∈ members, ∀ w ∈ (C.layerAt i).Content, P.Visits w) ∧
      P.Visits (textWord (C.text source) record.start record.stop) ∧
      ∃ w, P.Visits w ∧ w.length ≤ C.period target.1

namespace PlannedBlock

variable [LinearOrder α] {C : LayerCollection V G} (B : C.PlannedBlock)

def content : Set (List α) := {w | ∃ i ∈ B.members, w ∈ (C.layerAt i).Content}

def word : List α := textWord (C.text B.source) B.record.start B.record.stop

theorem word_content : B.word ∈ (C.layerAt B.target).Content := by
  refine ⟨B.record.start + B.record.offset, B.record.stop + B.record.offset,
    B.record.first_le, B.record.le_last, ?_⟩
  exact B.record.word_eq

theorem same_short (h : B.target.1 = B.source) : B.word.length ≤ C.period B.source := by
  have hh := B.record.same_period_length_lt (C.positive B.source) (C.periodic B.source)
    (by simpa only [h] using C.periodic B.target.1) B.foreign
  have hlo := B.record.start_le_stop
  simp only [word, length_textWord]
  omega

end PlannedBlock
end LayerCollection
end Superstring.Hierarchical

namespace Superstring.Hierarchical.LayerCollection

variable {α G : Type} [LinearOrder α] {V : Set (List α)} (C : LayerCollection V G)

omit [LinearOrder α] in
theorem covers_groupIds (g : G) (I : Finset (Fin (C.size g))) (Q : Loop V)
    (h : ∀ j ∈ I, ∀ w ∈ (C.layer g j).Content, Q.Visits w) :
    ∀ i ∈ C.groupIds g I, ∀ w ∈ (C.layerAt i).Content, Q.Visits w := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
  exact h j hj

/-- A single upper layer satisfies exactly the ordinary individual-link
conditions. The short contact is proved by the three-window path. -/
noncomputable def individualPlan (closed : SubstringClosed V)
    (g : G) (i : Fin (C.size g)) (target : C.Id)
    (R : (C.layerAt target).Record (C.text g))
    (hne : C.text g ≠ fun x => C.text target.1 (x + R.offset))
    (hf : (C.layer g i).first R.start ≤ R.stop)
    (hl : R.stop ≤ (C.layer g i).last R.start + C.period g) : C.PlannedBlock := by
  classical
  have hex : ∃ Q : Loop V, Q.cost ≤ 2 * C.period g ∧
      (∀ j ∈ C.groupIds g {i}, ∀ w ∈ (C.layerAt j).Content, Q.Visits w) ∧
      Q.Visits (textWord (C.text g) R.start R.stop) ∧
      ∃ w, Q.Visits w ∧ w.length ≤ C.period target.1 := by
    have hlen := R.length_lt (C.positive g) (C.positive target.1)
      (C.periodic g) (C.periodic target.1) hne
    obtain ⟨P, hcP, hvP, w, hw, hwlen⟩ := individual_link closed (C.text g)
      (C.letters closed g) (C.period g) (C.period target.1) (C.periodic g)
      (C.layer g i) R.start_le_stop R.word_mem hf hl hlen
    obtain ⟨Q, _, hcQ, hvQ, hlQ⟩ := fill_same_layers closed (C.layer g) (C.positive g)
      (C.periodic g) {i} ⟨_, P⟩ (by simpa using hvP)
    have hcost : Q.cost ≤ 2 * C.period g := by
      simpa only [Finset.card_singleton, one_mul, Loop.cost, hcP, two_mul] using hcQ
    have hcover := C.covers_groupIds g {i} Q hlQ
    have hR : Q.Visits (textWord (C.text g) R.start R.stop) := hvQ _ (Path.visits_start P)
    exact ⟨Q, hcost, hcover, hR, w, hvQ w hw, hwlen⟩
  refine {
    source := g
    members := C.groupIds g {i}
    nonempty := ⟨⟨g, i⟩, Finset.mem_map.mpr ⟨i, Finset.mem_singleton_self i, rfl⟩⟩
    same := fun _ hi => C.groupIds_same g {i} hi
    target := target
    record := R
    foreign := hne
    link := by
      obtain ⟨Q, hc, hv, hr, _⟩ := hex
      exact ⟨Q, by simpa using hc, hv, hr⟩
    internal := ?_
    short := fun _ => by simpa using hex }
  obtain ⟨F, hcF, hvF⟩ := (C.layer g i).content_loop closed (C.positive g) (C.periodic g)
  refine ⟨F, by simp [hcF, two_mul], C.covers_groupIds g {i} F ?_⟩
  intro j hj
  have he : j = i := Finset.mem_singleton.mp hj
  subst j
  exact hvF

/-- A collective top block is valid INCLUDING k=1. Its ordinary link, free
period internal alternative, and maximal-rank short-contact realization are
all materialized, with every constituent base turn included once. -/
noncomputable def collectivePlan (closed : SubstringClosed V)
    (g : G) (I : Finset (Fin (C.size g))) (lo hi : Fin (C.size g))
    (hlom : lo ∈ I) (hhim : hi ∈ I)
    (hlo : ∀ j ∈ I, lo ≤ j) (hhi : ∀ j ∈ I, j ≤ hi)
    (target : C.Id) (R : (C.layerAt target).Record (C.text g))
    (hne : C.text g ≠ fun x => C.text target.1 (x + R.offset))
    (hat : R.start ≤ C.distinguished g) (htb : C.distinguished g < R.stop)
    (hsharp : (C.layer g hi).first (C.distinguished g) -
      (C.layer g lo).last (C.distinguished g) ≤ ((I.card - 1) * C.period g : ℕ))
    (hH : (C.layer g hi).first (C.distinguished g) ≤ R.stop + (I.card * C.period g : ℕ))
    (hlast : R.stop ≤ (C.layer g lo).last R.start + (I.card * C.period g : ℕ)) :
    C.PlannedBlock := by
  classical
  let L := fun j : {j // j ∈ I} => C.layer g j.val
  let l : {j // j ∈ I} := ⟨lo, hlom⟩
  let h : {j // j ∈ I} := ⟨hi, hhim⟩
  have hk : 0 < I.card := Finset.card_pos.mpr ⟨lo, hlom⟩
  have hl : ∀ j x, (L l).z x ≤ (L j).z x :=
    fun j x => C.ordered g lo j.val (hlo j.val j.property) x
  have hh : ∀ j x, (L j).z x ≤ (L h).z x :=
    fun j x => C.ordered g j.val hi (hhi j.val j.property) x
  have hband := Processing.wide_band (C.layer g hi) (C.layer g lo)
    (C.positive g) hk (C.distinguished g) hsharp R.start
  have hbudget : (I.card - 1) * C.period g + C.period g = I.card * C.period g := by
    calc
      (I.card - 1) * C.period g + C.period g = (I.card - 1 + 1) * C.period g := by rw [Nat.add_mul, Nat.one_mul]
      _ = I.card * C.period g := by rw [Nat.sub_add_cancel hk]
  have fill : ∀ P : Loop V, (∀ j, (L j).TouchedBy P.path) →
      ∃ Q : Loop V, Q.cost ≤ P.cost + I.card * C.period g ∧
        (∀ w, P.Visits w → Q.Visits w) ∧
        ∀ i ∈ C.groupIds g I, ∀ w ∈ (C.layerAt i).Content, Q.Visits w := by
    intro P ht
    obtain ⟨Q, _, hcQ, hvQ, hlQ⟩ := fill_same_layers closed (C.layer g) (C.positive g)
      (C.periodic g) I P (fun j hj => ht ⟨j, hj⟩)
    exact ⟨Q, hcQ, hvQ, C.covers_groupIds g I Q hlQ⟩
  refine {
    source := g
    members := C.groupIds g I
    nonempty := ⟨⟨g, lo⟩, Finset.mem_map.mpr ⟨lo, hlom, rfl⟩⟩
    same := fun _ hi => C.groupIds_same g I hi
    target := target
    record := R
    foreign := hne
    link := ?_
    internal := ?_
    short := ?_ }
  · obtain ⟨P, hcP, hvP⟩ := collective_link closed (C.text g) (C.letters closed g)
      (C.period g) I.card (C.periodic g) L l h hl hh R.start_le_stop R.word_mem
      ((C.layer g hi).first_mono hat |>.trans hH) hband hlast
    obtain ⟨Q, hcQ, hvQ, hlQ⟩ := fill ⟨_, P⟩ hvP
    refine ⟨Q, ?_, hlQ, hvQ _ (Path.visits_start P)⟩
    simp only [Loop.cost, hcP] at hcQ
    simpa only [card_groupIds, Loop.cost, two_mul] using hcQ
  · obtain ⟨P, hcP, hvP⟩ := one_free_period closed (C.text g) (C.letters closed g)
      (C.period g) I.card (C.periodic g) L l h hl hh (C.distinguished g) hsharp
    obtain ⟨Q, hcQ, _, hlQ⟩ := fill ⟨_, P⟩ hvP
    refine ⟨Q, ?_, hlQ⟩
    rw [card_groupIds]
    change Q.cost ≤ P.cost + I.card * C.period g at hcQ
    omega
  · intro hRank
    have hper : Function.Periodic (fun x => C.text target.1 (x + R.offset))
        (C.period target.1 : ℤ) := by
      intro x
      simpa only [add_right_comm] using C.periodic target.1 (x + R.offset)
    have hbelow : ∀ x, forward (fun x => C.text target.1 (x + R.offset)) x ≤
        forward (C.text g) (C.distinguished g) := by
      intro x
      rw [forward_shift]
      exact (C.distinguished_max target.1 (x + R.offset)).trans hRank
    obtain ⟨P, hcP, hvP, hs⟩ := cycle_collective_contact closed (C.text g)
      (fun x => C.text target.1 (x + R.offset)) (C.letters closed g)
      (C.period g) I.card (C.period target.1) (C.positive g) hk (C.positive target.1)
      (C.periodic g) hper L l h hl hh hat htb R.word_mem R.agree hne
      (C.distinguished_max g) hbelow hH hband hlast
    obtain ⟨Q, hcQ, hvQ, hlQ⟩ := fill ⟨_, P⟩ hvP
    refine ⟨Q, ?_, hlQ, hvQ _ (Path.visits_start P), ?_⟩
    · simp only [Loop.cost, hcP] at hcQ
      simpa only [card_groupIds, Loop.cost, two_mul] using hcQ
    · rcases hs with ⟨j, a, b, hf, hz, hlen⟩ | ⟨w, hw, hlen⟩
      · refine ⟨textWord (C.text g) a b, ?_, hlen⟩
        exact hlQ ⟨g, j.val⟩ (Finset.mem_map.mpr ⟨j.val, j.property, rfl⟩)
          _ ⟨a, b, hf, hz, rfl⟩
      · exact ⟨w, hvQ w hw, hlen⟩

end Superstring.Hierarchical.LayerCollection

namespace Superstring.Hierarchical.LayerCollection.PlannedBlock

variable {α G : Type} [LinearOrder α] {V : Set (List α)} {C : LayerCollection V G}

def reserve (B : C.PlannedBlock) : ℕ := 2 * (B.members.card * C.period B.source)

/-- Execute the concrete geometrically proved plans. Target ownership does
not require a disjointness assumption: any covering block can be chosen, and
every reserve is charged once. Group processing will prove the total budget. -/
theorem execute (closed : SubstringClosed V) (I : Finset C.PlannedBlock)
    (P : Path V [] [])
    (covered : ∀ i : C.Id, (∀ w ∈ (C.layerAt i).Content, P.Visits w) ∨
      ∃ B ∈ I, i ∈ B.members) :
    ∃ Q : Path V [] [], Q.cost ≤ P.cost + ∑ B ∈ I, B.reserve ∧
      (∀ w, P.Visits w → Q.Visits w) ∧
      ∀ i : C.Id, ∀ w ∈ (C.layerAt i).Content, Q.Visits w := by
  classical
  let target : C.PlannedBlock → Option C.PlannedBlock := fun B =>
    if h : ∃ D ∈ I, B.target ∈ D.members then some h.choose else none
  have spec : ∀ B D, target B = some D → D ∈ I ∧ B.target ∈ D.members := by
    intro B D he
    dsimp only [target] at he
    split_ifs at he with h
    · have hd : h.choose = D := Option.some.inj he
      exact hd ▸ h.choose_spec
  have no_spec : ∀ B, target B = none → ¬ ∃ D ∈ I, B.target ∈ D.members := by
    intro B he h
    simp [target, dite_eq_left h] at he
  let F : BlockPlan V C.PlannedBlock (Lex (ℕ → α)) := {
    content := fun B => B.content
    reserve := fun B => B.reserve
    free := fun B => C.period B.source
    rank := fun B => C.rank B.source
    target := target
    record := fun B => B.word
    target_mem := by
      intro B D he
      exact ⟨B.target, (spec B D he).2, B.word_content⟩
    link := by
      intro B
      obtain ⟨Q, hc, hv, hr⟩ := B.link
      exact ⟨Q, hc, fun w ⟨i, hi, hw⟩ => hv i hi w hw, hr⟩
    internal := by
      intro B
      obtain ⟨Q, hc, hv⟩ := B.internal
      exact ⟨Q, hc, fun w ⟨i, hi, hw⟩ => hv i hi w hw⟩
    short := by
      intro B D ht _ hr
      have hg := D.same B.target (spec B D ht).2
      obtain ⟨Q, hc, hv, hr, hs⟩ := B.short (by simpa only [hg] using hr)
      exact ⟨Q, hc, fun w ⟨i, hi, hw⟩ => hv i hi w hw, hr, by simpa only [hg] using hs⟩
    self_short := by
      intro B ht
      have hm := (spec B B ht).2
      exact ⟨B.word, ⟨B.target, hm, B.word_content⟩, B.same_short (B.same _ hm)⟩ }
  have ready : ∀ B ∈ I, match F.target B with
      | none => P.Visits (F.record B)
      | some D => D ∈ I ∨ P.Visits (F.record B) := by
    intro B _
    change match target B with
      | none => P.Visits B.word
      | some D => D ∈ I ∨ P.Visits B.word
    split <;> rename_i ht
    · rcases covered B.target with hroot | hblock
      · exact hroot B.word B.word_content
      · exact False.elim (no_spec B ht hblock)
    · exact Or.inl (spec B _ ht).1
  obtain ⟨Q, hcQ, hvQ, hbQ⟩ := F.connect closed I P (by
    intro B hB
    have hh := ready B hB
    cases h : F.target B <;> simpa only [h] using hh)
  refine ⟨Q, hcQ, hvQ, ?_⟩
  intro i w hw
  rcases covered i with hroot | ⟨B, hB, hi⟩
  · exact hvQ w (hroot w hw)
  · exact hbQ B hB w ⟨i, hi, hw⟩

end Superstring.Hierarchical.LayerCollection.PlannedBlock

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.Hierarchical.LayerCollection

variable {α G : Type} {V : Set (List α)} (C : LayerCollection V G)


structure Child (d : C.Id) where
  source : G
  members : Finset (Fin (C.size source))
  nonempty : members.Nonempty
  record : (C.layerAt d).Record (C.text source)
  foreign : C.text source ≠ fun x => C.text d.1 (x + record.offset)
  long : ∀ i ∈ members, record.start + C.period source < (C.layer source i).first record.start
  margin : ∀ i ∈ members, (C.layer source i).last record.start < record.stop - C.period source

namespace Child

variable {C} {d : C.Id} (R : C.Child d)

def ids : Finset C.Id := C.groupIds R.source R.members

def budget : ℕ := R.members.card * C.period R.source

theorem later : C.period R.source < C.period d.1 := by
  obtain ⟨i, hi⟩ := R.nonempty
  have hl := R.long i hi
  have hm := R.margin i hi
  have hf := (C.layer R.source i).first_le_last R.record.start
  have hb := R.record.length_lt (C.positive R.source) (C.positive d.1)
    (C.periodic R.source) (C.periodic d.1) R.foreign
  omega


def hosted : HostedGroup (C.layerAt d) where
  text := fun x => C.text R.source (x - R.record.offset)
  period := C.period R.source
  positive := C.positive R.source
  periodic := fun x => by
    simpa only [add_sub_right_comm] using C.periodic R.source (x - R.record.offset)
  start := R.record.start + R.record.offset
  stop := R.record.stop + R.record.offset
  first_le := R.record.first_le
  le_last := R.record.le_last
  agree := by
    intro x hx hy
    have hh := R.record.agree (x - R.record.offset) (by omega) (by omega)
    simpa only [sub_add_cancel] using hh
  foreign := by
    intro he
    apply R.foreign
    funext x
    simpa only [add_sub_cancel_right] using congrFun he (x + R.record.offset)

def request (i : {j // j ∈ R.members}) : R.hosted.Request where
  layer := (C.layer R.source i.val).translate R.record.offset
  stop := (C.layer R.source i.val).first R.record.start + R.record.offset
  first_le := by simp [hosted]
  le_last := by
    simp only [hosted, Layer.translate_last, add_sub_cancel_right]
    have hf := (C.layer R.source i.val).first_le_last R.record.start
    omega
  long := by
    have hh := R.long i.val i.property
    change R.record.start + R.record.offset + C.period R.source < _
    omega
  margin := by
    have hh := R.margin i.val i.property
    have hf := (C.layer R.source i.val).first_le_last R.record.start
    change _ ≤ R.record.stop + R.record.offset - C.period R.source
    omega

theorem hosted_different (S : C.Child d) (hne : R.source ≠ S.source) (c : ℤ) :
    R.hosted.text ≠ fun x => S.hosted.text (x + c) := by
  intro he
  apply C.different R.source S.source hne (R.record.offset + c - S.record.offset)
  funext x
  have hh := congrFun he (x + R.record.offset)
  change C.text R.source (x + R.record.offset - R.record.offset) =
    C.text S.source (x + R.record.offset + c - S.record.offset) at hh
  have hx : x + R.record.offset + c - S.record.offset =
      x + (R.record.offset + c - S.record.offset) := by omega
  simpa only [add_sub_cancel_right, hx] using hh

end Child

/-- A nonempty collection of actual child groups can be fulfilled together.
The reserve includes the original turn of every requesting layer and of the
recipient. No other layer of the recipient group is charged or rooted here. -/
theorem fulfill {ι : Type} [Fintype ι] [Nonempty ι]
    (closed : SubstringClosed V) (d : C.Id) (R : ι → C.Child d)
    (distinct : Function.Injective (fun i => (R i).source)) :
    ∃ Q : Path V [] [], Q.cost ≤ 2 * C.period d.1 + 2 * ∑ i, (R i).budget ∧
      (∀ w ∈ (C.layerAt d).Content, Q.Visits w) ∧
      ∀ j i, i ∈ (R j).members → ∀ w ∈ (C.layer (R j).source i).Content, Q.Visits w := by
  classical
  let K := Σ j : ι, {i // i ∈ (R j).members}
  let child : K → ι := fun k => k.1
  let req := fun k : K => (R k.1).request k.2
  have hK : (Finset.univ : Finset K).Nonempty := by
    obtain ⟨j⟩ := ‹Nonempty ι›
    obtain ⟨i, hi⟩ := (R j).nonempty
    exact ⟨⟨j, i, hi⟩, Finset.mem_univ _⟩
  have budget_sum : (∑ k : K, C.period (R k.1).source) = ∑ j, (R j).budget := by
    simp only [K, Fintype.sum_sigma, Finset.sum_const, Finset.card_univ,
      Fintype.card_coe, smul_eq_mul, Child.budget]
  obtain ⟨P, hcP, hdP, hrP⟩ := host_requests closed (C.layerAt d) (C.positive d.1)
    (C.periodic d.1) (C.letters closed d.1) (fun j => (R j).hosted) child req
    (fun j x => C.letters closed (R j).source (x - (R j).record.offset))
    (fun i j hij c => (R i).hosted_different (R j) (fun he => hij (distinct he)) c)
    Finset.univ hK
  obtain ⟨Q, hbQ, hcQ, hvQ, hdQ⟩ := fill_same_layers closed (fun _ : Unit => C.layerAt d)
    (C.positive d.1) (C.periodic d.1) {()} ⟨[], P⟩ (fun _ _ => hdP)
  obtain ⟨T, hbT, hcT, hvT, hrT⟩ := fill_layers closed (fun k : K => (req k).layer)
    (fun k => C.positive (R k.1).source) (fun k => (R k.1).hosted.periodic) Finset.univ Q
    (fun k hk => by
      obtain ⟨x, e, hf, hl, hp⟩ := hrP k hk
      exact ⟨x, e, hf, hl, hvQ _ hp⟩)
  have hbase : T.base = [] := hbT.trans hbQ
  refine ⟨T.path.copy hbase hbase, ?_, ?_, ?_⟩
  · simp only [Path.cost_copy]
    change T.cost ≤ _
    simp only [Finset.card_singleton, one_mul] at hcQ
    change Q.cost ≤ P.cost + C.period d.1 at hcQ
    change P.cost ≤ C.period d.1 + ∑ k : K, C.period (R k.1).source at hcP
    change T.cost ≤ Q.cost + ∑ k : K, C.period (R k.1).source at hcT
    rw [budget_sum] at hcP hcT
    omega
  · intro w hw
    exact (Path.visits_copy ..).mpr (hvT w (hdQ () (Finset.mem_singleton_self ()) w hw))
  · intro j i hi w hw
    apply (Path.visits_copy ..).mpr
    apply hrT ⟨j, i, hi⟩ (Finset.mem_univ _) w
    change w ∈ ((C.layer (R j).source i).translate (R j).record.offset).Content
    rwa [Layer.translate_content]

end Superstring.Hierarchical.LayerCollection

namespace Superstring.Hierarchical

/-- Concatenate a finite family of rooted closed walks, preserving every
visit and charging at most their sum. Abstracted only to avoid repeated splices. -/
theorem combine_rooted {α ι : Type} {V : Set (List α)} (he : [] ∈ V)
    (F : ι → Path V [] []) (I : Finset ι) :
    ∃ Q : Path V [] [], Q.cost ≤ ∑ i ∈ I, (F i).cost ∧
      ∀ i ∈ I, ∀ w, (F i).Visits w → Q.Visits w := by
  apply Loop.of_connected (fun i => ⟨[], F i⟩) I [] he
  intro U hU hclosed i hi w hw
  exact hclosed i hi ⟨[], hU, Path.visits_start (F i)⟩ w hw

namespace LayerCollection

variable {α G : Type} {V : Set (List α)} (C : LayerCollection V G)

include C in
theorem empty_mem (closed : SubstringClosed V) (g : G) : [] ∈ V :=
  closed (C.letters closed g 0) List.nil_infix

theorem root_short (closed : SubstringClosed V) (g : G) (i : Fin (C.size g))
    (hs : (C.layer g i).HasShort (C.period g)) :
    ∃ Q : Path V [] [], Q.cost ≤ 2 * C.period g ∧
      ∀ w ∈ (C.layer g i).Content, Q.Visits w := by
  obtain ⟨x, e, hf, hl, hc⟩ := hs
  obtain ⟨P, hcP, hvP⟩ := Path.root_loop closed _ ((C.layer g i).actual x e hf hl)
  obtain ⟨Q, hbQ, hcQ, _, hvQ⟩ := fill_same_layers closed (C.layer g) (C.positive g)
    (C.periodic g) {i} ⟨[], P⟩ (by
      intro j hj
      have he : j = i := Finset.mem_singleton.mp hj
      subst j
      exact ⟨x, e, hf, hl, hvP⟩)
  refine ⟨Q.path.copy hbQ hbQ, ?_, fun w hw => (Path.visits_copy ..).mpr
    (hvQ i (Finset.mem_singleton_self i) w hw)⟩
  simp only [Path.cost_copy]
  change Q.cost ≤ _
  simp only [Finset.card_singleton, one_mul] at hcQ
  change Q.cost ≤ P.cost + C.period g at hcQ
  omega

end LayerCollection
end Superstring.Hierarchical

namespace Superstring.Hierarchical.Processing

/-- Once the cardinality test stops, every layer strictly below the top k
has last end strictly below the tested threshold. -/
theorem below_stopped {m : ℕ} (z : Fin m → ℤ) (hz : Monotone z) (H : ℤ) (p k : ℕ)
    (hstop : (qualifying z H p k).card ≤ k) (i : Fin m) (hi : i.val < m - k) :
    z i < H - (k * p : ℕ) := by
  by_contra hh
  have hsub : Finset.Ici i ⊆ qualifying z H p k := by
    intro j hj
    simp only [qualifying, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (le_of_not_gt hh).trans (hz (Finset.mem_Ici.mp hj))
  have hc := Finset.card_le_card hsub
  rw [Fin.card_Ici] at hc
  omega

end Superstring.Hierarchical.Processing

namespace Superstring.Hierarchical.LayerCollection

variable {α G : Type} [LinearOrder α] {V : Set (List α)} (C : LayerCollection V G)


theorem distribute_individuals (closed : SubstringClosed V) (g : G)
    (d : C.Id) (R : (C.layerAt d).Record (C.text g))
    (foreign : C.text g ≠ fun x => C.text d.1 (x + R.offset))
    (I : Finset (Fin (C.size g)))
    (hfirst : ∀ i ∈ I, (C.layer g i).first R.start ≤ R.stop) :
    ∃ (Q : Path V [] []) (B : Finset C.PlannedBlock) (A : Finset (Fin (C.size g))),
      Q.cost + (∑ b ∈ B, b.reserve) + 2 * (A.card * C.period g) ≤ 2 * (I.card * C.period g) ∧
      (∀ i ∈ I, (∀ w ∈ (C.layer g i).Content, Q.Visits w) ∨
        (∃ b ∈ B, (⟨g, i⟩ : C.Id) ∈ b.members) ∨ i ∈ A) ∧
      A ⊆ I ∧
      (∀ i ∈ A, R.start + C.period g < (C.layer g i).first R.start) ∧
      (∀ i ∈ A, (C.layer g i).last R.start < R.stop - C.period g) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    exact ⟨.nil [] (C.empty_mem closed g), ∅, ∅, by simp [Path.cost],
      by simp, by simp, by simp, by simp⟩
  | @insert i I hi ih =>
    obtain ⟨Q, B, A, hcQ, hvQ, hAI, hlong, hmargin⟩ := ih
      (fun j hj => hfirst j (Finset.mem_insert_of_mem hj))
    have hcard : 2 * ((insert i I).card * C.period g) =
        2 * (I.card * C.period g) + 2 * C.period g := by
      rw [Finset.card_insert_of_notMem hi, Nat.add_mul, Nat.one_mul, Nat.mul_add]
    have lift_cover (T : Path V [] []) (B' : Finset C.PlannedBlock)
        (A' : Finset (Fin (C.size g)))
        (hP : ∀ w, Q.Visits w → T.Visits w) (hB : B ⊆ B') (hA : A ⊆ A')
        (hv : (∀ w ∈ (C.layer g i).Content, T.Visits w) ∨
          (∃ b ∈ B', (⟨g, i⟩ : C.Id) ∈ b.members) ∨ i ∈ A') :
        ∀ j ∈ insert i I, (∀ w ∈ (C.layer g j).Content, T.Visits w) ∨
          (∃ b ∈ B', (⟨g, j⟩ : C.Id) ∈ b.members) ∨ j ∈ A' := by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hv
      · rcases hvQ j hj with hp | ⟨b, hb, hm⟩ | ha
        · exact Or.inl (fun w hw => hP w (hp w hw))
        · exact Or.inr (Or.inl ⟨b, hB hb, hm⟩)
        · exact Or.inr (Or.inr (hA ha))
    by_cases hs : (C.layer g i).HasShort (C.period g)
    · obtain ⟨P, hcP, hvP⟩ := C.root_short closed g i hs
      refine ⟨Q.trans P, B, A, ?_, lift_cover _ _ _ (fun _ h => Or.inl h)
        (fun _ h => h) (fun _ h => h) (Or.inl (fun w hw => Or.inr (hvP w hw))),
        hAI.trans (Finset.subset_insert i I), hlong, hmargin⟩
      rw [Path.cost_trans, hcard]
      omega
    · by_cases ht : R.stop ≤ (C.layer g i).last R.start + C.period g
      · let b := C.individualPlan closed g i d R foreign
          (hfirst i (Finset.mem_insert_self i I)) ht
        have hbc : b.reserve = 2 * C.period g := by
          simp [b, individualPlan, PlannedBlock.reserve]
        have hsum : (∑ x ∈ insert b B, x.reserve) ≤ b.reserve + ∑ x ∈ B, x.reserve := by
          by_cases hb : b ∈ B
          · rw [Finset.insert_eq_of_mem hb]
            omega
          · rw [Finset.sum_insert hb]
        have hmem : (⟨g, i⟩ : C.Id) ∈ b.members := by
          exact Finset.mem_map.mpr ⟨i, Finset.mem_singleton_self i, rfl⟩
        refine ⟨Q, insert b B, A, ?_, lift_cover _ _ _ (fun _ h => h)
          (Finset.subset_insert b B) (fun _ h => h)
          (Or.inr (Or.inl ⟨b, Finset.mem_insert_self b B, hmem⟩)),
          hAI.trans (Finset.subset_insert i I), hlong, hmargin⟩
        rw [hcard]
        omega
      · have hni : i ∉ A := fun hm => hi (hAI hm)
        have hl := (C.layer g i).first_long_of_not_short (C.period g) hs R.start
        refine ⟨Q, B, insert i A, ?_, lift_cover _ _ _ (fun _ h => h)
          (fun _ h => h) (Finset.subset_insert i A)
          (Or.inr (Or.inr (Finset.mem_insert_self i A))),
          Finset.insert_subset_insert i hAI, ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem hni, Nat.add_mul, Nat.one_mul, Nat.mul_add, hcard]
          omega
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · omega
          · exact hlong j hj
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · omega
          · exact hmargin j hj

end Superstring.Hierarchical.LayerCollection

namespace Superstring.Hierarchical.LayerCollection

variable {α G : Type} [LinearOrder α] {V : Set (List α)} (C : LayerCollection V G)

/-- The hard-case distribution, using the ONE record already forced by the
count rule. Collective and uncollected individual budgets are disjoint. -/
theorem distribute_record (closed : SubstringClosed V) (g : G)
    (I : Finset (Fin (C.size g))) (k : ℕ) (hk : 0 < k) (hkm : k ≤ C.size g)
    (hI : ∀ i : Fin (C.size g), C.size g - k ≤ i.val → i ∈ I)
    (d : C.Id) (R : (C.layerAt d).Record (C.text g))
    (foreign : C.text g ≠ fun x => C.text d.1 (x + R.offset))
    (hat : R.start ≤ C.distinguished g) (htb : C.distinguished g < R.stop)
    (hb : (C.layer g ⟨C.size g - 1, by have := C.nonempty g; omega⟩).first (C.distinguished g)
      ≤ R.stop + (k * C.period g : ℕ))
    (hsharp : (C.layer g ⟨C.size g - 1, by have := C.nonempty g; omega⟩).first (C.distinguished g) -
      (C.layer g ⟨C.size g - k, by omega⟩).last (C.distinguished g) ≤ ((k - 1) * C.period g : ℕ))
    (hstop : (Processing.qualifying (fun j => (C.layer g j).last (C.distinguished g))
      ((C.layer g ⟨C.size g - 1, by have := C.nonempty g; omega⟩).first (C.distinguished g))
      (C.period g) k).card ≤ k) :
    ∃ (Q : Path V [] []) (B : Finset C.PlannedBlock) (A : Finset (Fin (C.size g))),
      Q.cost + (∑ b ∈ B, b.reserve) + 2 * (A.card * C.period g) ≤ 2 * (I.card * C.period g) ∧
      (∀ i ∈ I, (∀ w ∈ (C.layer g i).Content, Q.Visits w) ∨
        (∃ b ∈ B, (⟨g, i⟩ : C.Id) ∈ b.members) ∨ i ∈ A) ∧
      A ⊆ I ∧
      (∀ i ∈ A, R.start + C.period g < (C.layer g i).first R.start) ∧
      (∀ i ∈ A, (C.layer g i).last R.start < R.stop - C.period g) := by
  classical
  let top : Fin (C.size g) := ⟨C.size g - 1, by have := C.nonempty g; omega⟩
  let lo : Fin (C.size g) := ⟨C.size g - k, by omega⟩
  let J := Finset.Ici lo
  have hJcard : J.card = k := by simp only [J, Fin.card_Ici, lo]; omega
  have hJI : J ⊆ I := by
    intro i hi
    have hh : lo ≤ i := Finset.mem_Ici.mp hi
    exact hI i hh
  have htop : ∀ i : Fin (C.size g), i ≤ top := by
    intro i
    change i.val ≤ C.size g - 1
    omega
  have hlo : lo ∈ J := Finset.mem_Ici.mpr le_rfl
  have hhi : top ∈ J := Finset.mem_Ici.mpr (htop lo)
  have first_below : ∀ i : Fin (C.size g), i ∉ J → (C.layer g i).first R.start ≤ R.stop := by
    intro i hi
    have hil : i.val < C.size g - k := by
      have hh : ¬ lo ≤ i := fun h => hi (Finset.mem_Ici.mpr h)
      change ¬ C.size g - k ≤ i.val at hh
      omega
    have hh := Processing.below_stopped (fun j => (C.layer g j).last (C.distinguished g))
      (fun i j hij => C.ordered g i j hij _) ((C.layer g top).first (C.distinguished g))
      (C.period g) k hstop i hil
    have hfa := (C.layer g i).first_mono hat
    have hfl := (C.layer g i).first_le_last (C.distinguished g)
    change (C.layer g top).first (C.distinguished g) ≤ _ at hb
    omega
  by_cases hcollect : R.stop ≤ (C.layer g lo).last R.start + (k * C.period g : ℕ)
  · let b := C.collectivePlan closed g J lo top hlo hhi
      (fun _ hj => Finset.mem_Ici.mp hj) (fun i _ => htop i) d R foreign hat htb
      (by simpa only [hJcard] using hsharp) (by simpa only [hJcard] using hb)
      (by simpa only [hJcard] using hcollect)
    obtain ⟨Q, B, A, hcQ, hvQ, hA, hlong, hmargin⟩ := C.distribute_individuals closed g d R foreign
      (I \ J) (fun i hi => first_below i (Finset.mem_sdiff.mp hi).2)
    have hbc : b.reserve = 2 * (k * C.period g) := by
      simp only [b, collectivePlan, PlannedBlock.reserve, card_groupIds, hJcard]
    have hsum : (∑ x ∈ insert b B, x.reserve) ≤ b.reserve + ∑ x ∈ B, x.reserve := by
      by_cases hb : b ∈ B
      · rw [Finset.insert_eq_of_mem hb]; omega
      · rw [Finset.sum_insert hb]
    have hcard := Finset.card_sdiff_add_card_eq_card hJI
    have hcost : 2 * ((I \ J).card * C.period g) + 2 * (k * C.period g) =
        2 * (I.card * C.period g) := by
      rw [← Nat.mul_add, ← Nat.add_mul, ← hJcard, hcard]
    refine ⟨Q, insert b B, A, by omega, ?_, hA.trans Finset.sdiff_subset, hlong, hmargin⟩
    intro i hi
    by_cases hij : i ∈ J
    · exact Or.inr (Or.inl ⟨b, Finset.mem_insert_self b B,
        Finset.mem_map.mpr ⟨i, hij, rfl⟩⟩)
    · rcases hvQ i (Finset.mem_sdiff.mpr ⟨hi, hij⟩) with hr | ⟨x, hx, hm⟩ | ha
      · exact Or.inl hr
      · exact Or.inr (Or.inl ⟨x, Finset.mem_insert_of_mem hx, hm⟩)
      · exact Or.inr (Or.inr ha)
  · apply C.distribute_individuals closed g d R foreign I
    intro i _
    have hw := Processing.wide_band (C.layer g top) (C.layer g lo)
      (C.positive g) hk (C.distinguished g) hsharp R.start
    have hu := C.ordered g i top (htop i) (R.start - 1)
    change (C.layer g i).first R.start ≤ (C.layer g top).first R.start at hu
    omega

end Superstring.Hierarchical.LayerCollection

namespace Superstring.Hierarchical.Threading

variable {α ι : Type} [Fintype ι] {V : Set (List α)}

/-- The finite ordered collection is the actual sorted base decomposition,
not an arbitrary family substituted for its multiplicities. -/
noncomputable def collection (T : Threading V ι) (closed : SubstringClosed V) :
    LayerCollection V T.Groups where
  text := T.groupText
  period := T.groupPeriod
  size := fun g => Fintype.card (T.Aligned (T.groupText g))
  positive := fun g => (T.primitive_group g).positive
  nonempty := fun g => Fintype.card_pos_iff.mpr ⟨⟨Quotient.out g, rfl⟩⟩
  periodic := fun g => (T.primitive_group g).periodic
  layer := fun g j => T.layerAt closed ⟨g, j⟩
  ordered := fun g i j hij x => T.layers_ordered (T.groupText g) i j hij x
  different := by
    intro g h hne c he
    apply hne
    exact (T.group_eq_of_alignment g h c 0 (fun x => by
      simpa only [add_zero] using (congrFun he x).symm)).symm

end Superstring.Hierarchical.Threading

namespace Superstring.Hierarchical.LayerCollection

variable {α G : Type} {V : Set (List α)} (C : LayerCollection V G)


def RecordSupply : Prop :=
  ∀ (g : G) (j : Fin (C.size g)) (t : ℤ) (k : ℕ), 0 < k →
    t + (k * C.period g : ℕ) < (C.layer g j).first t →
    (Processing.qualifying (fun l => (C.layer g l).last t)
      ((C.layer g j).first t) (C.period g) k).card ≤ k →
    ∃ d : C.Id, ∃ R : (C.layerAt d).Record (C.text g),
      R.start ≤ t ∧ (C.layer g j).first t - (k * C.period g : ℕ) ≤ R.stop ∧
      C.text g ≠ fun x => C.text d.1 (x + R.offset)

end Superstring.Hierarchical.LayerCollection

namespace Superstring.Counts.Data

variable {α : Type} [DecidableEq α] [Inhabited α]

theorem collection_records (D : Data α) (hD : D.WellFormed) :
    ((D.threading hD).collection hD.closed).RecordSupply := by
  intro g j t k hk hh hs
  obtain ⟨d, R, ha, hb, hd, _⟩ := D.hard_case_record hD g j t k hk hh hs
  exact ⟨d, R, ha, hb, hd⟩

end Superstring.Counts.Data

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.Hierarchical.LayerCollection

variable {α G : Type} {V : Set (List α)} (C : LayerCollection V G)

/-- Complete one touched base layer and splice it into the rooted walk.
Only this layer's base turn and its one geometric connection are charged. -/
theorem attach_layer (closed : SubstringClosed V) (g : G) (i : Fin (C.size g))
    (P : Path V [] []) (F : Loop V) (hcF : F.cost ≤ C.period g)
    (ht : (C.layer g i).TouchedBy F.path) (hmeet : (Loop.mk [] P).Meets F) :
    ∃ Q : Path V [] [], Q.cost ≤ P.cost + 2 * C.period g ∧
      (∀ w, P.Visits w → Q.Visits w) ∧
      ∀ w ∈ (C.layer g i).Content, Q.Visits w := by
  obtain ⟨T, _, hcT, hvT, hlT⟩ := fill_same_layers closed (C.layer g) (C.positive g)
    (C.periodic g) {i} F (by simpa using ht)
  obtain ⟨w, hp, hf⟩ := hmeet
  obtain ⟨Q, hcQ, hvQ⟩ := P.splice T.path w hp (hvT w hf)
  refine ⟨Q, ?_, fun v hv => (hvQ v).mpr (Or.inl hv), fun v hv => ?_⟩
  · simp only [Finset.card_singleton, one_mul] at hcT
    change Q.cost = P.cost + T.cost at hcQ
    omega
  · exact (hvQ v).mpr (Or.inr (hlT i (Finset.mem_singleton_self i) v hv))

/-- Root each as-yet-unspent layer below the chosen recipient baseline. The
baseline itself is already fully retained by the incoming-request operation. -/
theorem root_below (closed : SubstringClosed V) (g : G) (base : Fin (C.size g))
    (P : Path V [] []) (hp : ∀ w ∈ (C.layer g base).Content, P.Visits w)
    (a b : ℤ) (hbf : (C.layer g base).first a ≤ b)
    (hbl : b ≤ (C.layer g base).last a) (hlen : b - a < 2 * C.period g)
    (I : Finset (Fin (C.size g))) (hbelow : ∀ i ∈ I, i ≤ base) :
    ∃ Q : Path V [] [], Q.cost ≤ P.cost + 2 * (I.card * C.period g) ∧
      (∀ w, P.Visits w → Q.Visits w) ∧
      ∀ i ∈ I, ∀ w ∈ (C.layer g i).Content, Q.Visits w := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨P, by simp, fun _ h => h, by simp⟩
  | @insert i I hi ih =>
    obtain ⟨Q, hcQ, hvQ, hlQ⟩ := ih (fun j hj => hbelow j (Finset.mem_insert_of_mem hj))
    have hqbase : Q.Visits (textWord (C.text g) a b) :=
      hvQ _ (hp _ ⟨a, b, hbf, hbl, rfl⟩)
    obtain ⟨F, hcF, htF, hmeet⟩ : ∃ F : Loop V,
        F.cost ≤ C.period g ∧ (C.layer g i).TouchedBy F.path ∧ (Loop.mk [] Q).Meets F := by
      rcases (C.layer g i).below_baseline (C.layer g base) closed (C.letters closed g)
        (C.periodic g) (C.ordered g i base (hbelow i (Finset.mem_insert_self i I)))
        hbf hbl hlen with ⟨F, hcF, htF⟩ | ⟨F, hcF, htF⟩
      · exact ⟨⟨[], F⟩, hcF, htF, [], Path.visits_start Q, Path.visits_start F⟩
      · exact ⟨⟨_, F⟩, hcF, htF, _, hqbase, Path.visits_start F⟩
    obtain ⟨T, hcT, hvT, hlT⟩ := C.attach_layer closed g i Q F hcF htF hmeet
    refine ⟨T, ?_, fun w hw => hvT w (hvQ w hw), ?_⟩
    · rw [Finset.card_insert_of_notMem hi, Nat.add_mul, Nat.one_mul, Nat.mul_add]
      omega
    · intro j hj w hw
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hlT w hw
      · exact hvT w (hlQ j hj w hw)

/-- Easy upper round-trip branch, including all upper base turns. -/
theorem root_upper_budget (closed : SubstringClosed V) (g : G)
    (I : Finset (Fin (C.size g))) (top : Fin (C.size g))
    (hupper : ∀ i ∈ I, i ≤ top) (t : ℤ)
    (hcost : (C.layer g top).first t - t ≤ (I.card * C.period g : ℕ)) :
    ∃ Q : Path V [] [], Q.cost ≤ 2 * (I.card * C.period g) ∧
      ∀ i ∈ I, ∀ w ∈ (C.layer g i).Content, Q.Visits w := by
  let L := fun i : Fin (C.size g) => C.layer g i
  have hall : ∀ j : {i // i ∈ insert top I}, ∀ x, (L j.val).z x ≤ (L top).z x := by
    intro j x
    rcases Finset.mem_insert.mp j.property with he | hj
    · rw [he]
    · exact C.ordered g j.val top (hupper j.val hj) x
  obtain ⟨P, hcP, htP⟩ := root_upper closed (fun j : {i // i ∈ insert top I} => L j.val)
    ⟨top, Finset.mem_insert_self top I⟩ hall t
  obtain ⟨Q, hbQ, hcQ, _, hvQ⟩ := fill_same_layers closed (C.layer g) (C.positive g)
    (C.periodic g) I ⟨[], P⟩ (fun i hi => htP ⟨i, Finset.mem_insert_of_mem hi⟩)
  refine ⟨Q.path.copy hbQ hbQ, ?_, fun i hi w hw => (Path.visits_copy ..).mpr (hvQ i hi w hw)⟩
  simp only [Path.cost_copy]
  change Q.cost ≤ _
  change Q.cost ≤ P.cost + I.card * C.period g at hcQ
  simp only [length_textWord] at hcP
  have ht := (C.layer g top).start_le_first t
  change P.cost = Int.toNat ((C.layer g top).first t - t) at hcP
  omega

/-- Easy upper band branch, paid only by upper layers, not by the already
rooted baseline's budget. -/
theorem attach_upper_band (closed : SubstringClosed V) (g : G)
    (I : Finset (Fin (C.size g))) (base top : Fin (C.size g))
    (horder : ∀ i ∈ I, base ≤ i ∧ i ≤ top) (hbt : base ≤ top)
    (P : Path V [] []) (hp : ∀ w ∈ (C.layer g base).Content, P.Visits w) (t : ℤ)
    (hband : (C.layer g top).first t - (C.layer g base).last t ≤ (I.card * C.period g : ℕ)) :
    ∃ Q : Path V [] [], Q.cost ≤ P.cost + 2 * (I.card * C.period g) ∧
      (∀ w, P.Visits w → Q.Visits w) ∧
      ∀ i ∈ I, ∀ w ∈ (C.layer g i).Content, Q.Visits w := by
  classical
  let J := insert base (insert top I)
  let L := fun j : {i // i ∈ J} => C.layer g j.val
  let lo : {i // i ∈ J} := ⟨base, Finset.mem_insert_self _ _⟩
  let hi : {i // i ∈ J} := ⟨top, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
  have ho : ∀ j : {i // i ∈ J}, base ≤ j.val ∧ j.val ≤ top := by
    intro j
    rcases Finset.mem_insert.mp j.property with he | hm
    · simpa only [he] using And.intro (le_refl base) hbt
    · rcases Finset.mem_insert.mp hm with he | hm
      · simpa only [he] using And.intro hbt (le_refl top)
      · exact horder j.val hm
  obtain ⟨F, hcF, htF⟩ := join_band closed (C.text g) (C.letters closed g)
    (C.period g) I.card (C.periodic g) L lo hi
    (fun j x => C.ordered g base j.val (ho j).1 x)
    (fun j x => C.ordered g j.val top (ho j).2 x) t hband
  obtain ⟨T, _, hcT, hvT, hlT⟩ := fill_same_layers closed (C.layer g) (C.positive g)
    (C.periodic g) I ⟨_, F⟩ (fun i hi => htF ⟨i, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hi)⟩)
  let w := textWord (C.text g) t ((C.layer g base).last t)
  have hwP : P.Visits w := hp w ⟨t, _, (C.layer g base).first_le_last t, le_rfl, rfl⟩
  have hwT : T.Visits w := hvT _ (Path.visits_start F)
  obtain ⟨Q, hcQ, hvQ⟩ := P.splice T.path w hwP hwT
  refine ⟨Q, ?_, fun v hv => (hvQ v).mpr (Or.inl hv), fun i hi v hv =>
    (hvQ v).mpr (Or.inr (hlT i hi v hv))⟩
  change T.cost ≤ F.cost + I.card * C.period g at hcT
  change Q.cost = P.cost + T.cost at hcQ
  omega

end Superstring.Hierarchical.LayerCollection

namespace Superstring.Hierarchical.LayerCollection

variable {α G : Type} {V : Set (List α)} (C : LayerCollection V G)


abbrev Pending := Σ d : C.Id, C.Child d

namespace Pending
variable {C} (r : C.Pending)
def source : G := r.2.source
def ids : Finset C.Id := r.2.ids
def reserve : ℕ := 2 * r.2.budget

theorem later : C.period r.source < C.period r.1.1 := r.2.later

theorem same (i : C.Id) (hi : i ∈ r.ids) : i.1 = r.source :=
  C.groupIds_same r.source r.2.members hi
end Pending

def upper (g : G) (cut : ℕ) : Finset (Fin (C.size g)) :=
  Finset.univ.filter (fun i => cut ≤ i.val)

@[simp] theorem mem_upper (g : G) (cut : ℕ) (i : Fin (C.size g)) :
    i ∈ C.upper g cut ↔ cut ≤ i.val := by simp [upper]

@[simp] theorem card_upper (g : G) (cut : ℕ) :
    (C.upper g cut).card = C.size g - cut := by
  by_cases hc : cut < C.size g
  · have he : C.upper g cut = Finset.Ici (⟨cut, hc⟩ : Fin (C.size g)) := by
      ext i
      simp only [mem_upper, Finset.mem_Ici, Fin.le_def]
    rw [he, Fin.card_Ici]
  · have he : C.upper g cut = ∅ := by
      ext i
      simp only [mem_upper, Finset.notMem_empty, iff_false]
      omega
    rw [he, Finset.card_empty]
    omega

variable [LinearOrder α]

def Covered (P : Path V [] []) (B : Finset C.PlannedBlock) (R : Finset C.Pending)
    (i : C.Id) : Prop :=
  (∀ w ∈ (C.layerAt i).Content, P.Visits w) ∨
    (∃ b ∈ B, i ∈ b.members) ∨ ∃ r ∈ R, i ∈ r.ids

/-- Complete exactly the unspent upper interval. The failed count test is
resolved by the proved record supply, not taken as a plan oracle. -/
theorem complete_upper (closed : SubstringClosed V) (supply : C.RecordSupply)
    (g : G) (cut : ℕ) (hcut : cut ≤ C.size g) (P : Path V [] [])
    (hp : ∀ i : Fin (C.size g), i.val < cut →
      ∀ w ∈ (C.layer g i).Content, P.Visits w) :
    ∃ (Q : Path V [] []) (B : Finset C.PlannedBlock) (R : Finset C.Pending),
      Q.cost + (∑ b ∈ B, b.reserve) + (∑ r ∈ R, r.reserve) ≤
        P.cost + 2 * ((C.size g - cut) * C.period g) ∧
      (∀ w, P.Visits w → Q.Visits w) ∧
      (∀ i ∈ C.upper g cut, C.Covered Q B R ⟨g, i⟩) ∧
      (∀ r ∈ R, r.source = g) ∧ R.card ≤ 1 := by
  classical
  let n := C.size g - cut
  let I := C.upper g cut
  have hcard : I.card = n := C.card_upper g cut
  by_cases hn : n = 0
  · refine ⟨P, ∅, ∅, by simp, fun _ h => h, ?_, by simp, by simp⟩
    intro i hi
    have hh := (C.mem_upper g cut i).mp hi
    have := i.isLt
    dsimp only [n] at hn
    omega
  have hnpos : 0 < n := by omega
  have hnm : n ≤ C.size g := Nat.sub_le _ _
  let top : Fin (C.size g) := ⟨C.size g - 1, by have := C.nonempty g; omega⟩
  let t := C.distinguished g
  let H := (C.layer g top).first t
  have htop : ∀ i ∈ I, i ≤ top := by
    intro i _
    change i.val ≤ C.size g - 1
    omega
  have easy (Q : Path V [] []) (hc : Q.cost ≤ P.cost + 2 * (n * C.period g))
      (hv : ∀ w, P.Visits w → Q.Visits w)
      (hi : ∀ i ∈ I, ∀ w ∈ (C.layer g i).Content, Q.Visits w) :
      ∃ (Q : Path V [] []) (B : Finset C.PlannedBlock) (R : Finset C.Pending),
        Q.cost + (∑ b ∈ B, b.reserve) + (∑ r ∈ R, r.reserve) ≤
          P.cost + 2 * ((C.size g - cut) * C.period g) ∧
        (∀ w, P.Visits w → Q.Visits w) ∧
        (∀ i ∈ C.upper g cut, C.Covered Q B R ⟨g, i⟩) ∧
        (∀ r ∈ R, r.source = g) ∧ R.card ≤ 1 := by
    exact ⟨Q, ∅, ∅, by simpa using hc, hv, fun i hm => Or.inl (hi i hm),
      by simp, by simp⟩
  by_cases he : H - t ≤ (n * C.period g : ℕ)
  · obtain ⟨Q, hcQ, hvQ⟩ := C.root_upper_budget closed g I top htop t (by simpa [hcard] using he)
    apply easy (P.trans Q)
    · rw [Path.cost_trans]
      rw [hcard] at hcQ
      omega
    · exact fun _ h => Or.inl h
    · exact fun i hi w hw => Or.inr (hvQ i hi w hw)
  have hz : Monotone (fun i : Fin (C.size g) => (C.layer g i).last t) := by
    intro i j hij
    exact C.ordered g i j hij t
  by_cases hb : ∃ base : Fin (C.size g), base.val + 1 = cut ∧
      H - (C.layer g base).last t ≤ (n * C.period g : ℕ)
  · obtain ⟨base, hbase, hband⟩ := hb
    obtain ⟨Q, hcQ, hvQ, hiQ⟩ := C.attach_upper_band closed g I base top
      (by intro i hi; exact ⟨by have hh := (C.mem_upper g cut i).mp hi; change base.val ≤ i.val; omega,
        htop i hi⟩)
      (by change base.val ≤ C.size g - 1; omega) P
      (hp base (by omega)) t (by simpa [hcard] using hband)
    exact easy Q (by simpa only [hcard] using hcQ) hvQ hiQ
  have hstopn : (Processing.qualifying (fun i => (C.layer g i).last t)
      H (C.period g) n).card ≤ n := by
    by_cases hzero : cut = 0
    · have hh := Finset.card_le_univ (Processing.qualifying
        (fun i => (C.layer g i).last t) H (C.period g) n)
      simpa only [Fintype.card_fin, n, hzero, Nat.sub_zero] using hh
    · let base : Fin (C.size g) := ⟨cut - 1, by omega⟩
      have hfail : (C.layer g base).last t < H - (n * C.period g : ℕ) := by
        by_contra hh
        apply hb
        exact ⟨base, by dsimp only [base]; omega, by omega⟩
      have hh := Processing.qualifying_bound _ hz H (C.period g) n base hfail
      change _ ≤ C.size g - 1 - (cut - 1) at hh
      dsimp only [n] at hh ⊢
      omega
  obtain ⟨k, hk, hkn, hstop, hsharp⟩ := Processing.choose_k hnpos hnm _ hz H
    (C.period g) ((C.layer g top).first_le_last t) hstopn
  have hkm : k ≤ C.size g := hkn.trans hnm
  have hmul : k * C.period g ≤ n * C.period g := Nat.mul_le_mul_right _ hkn
  have hhard : t + (k * C.period g : ℕ) < (C.layer g top).first t := by omega
  obtain ⟨d, R, ha, hh, hd⟩ := supply g top t k hk hhard hstop
  have ht : t < R.stop := by omega
  obtain ⟨Q, B, A, hcQ, hvQ, hAI, hlA, hmA⟩ := C.distribute_record closed g I k hk hkm
    (by intro i hi; apply (C.mem_upper g cut i).mpr; dsimp only [n] at hkn; omega)
    d R hd ha ht (by dsimp only [top, t, H] at hh ⊢; omega)
      (by dsimp only [top, t, H] at hsharp ⊢; omega) hstop
  have hhcost : (P.trans Q).cost + (∑ b ∈ B, b.reserve) + 2 * (A.card * C.period g) ≤
      P.cost + 2 * ((C.size g - cut) * C.period g) := by
    rw [Path.cost_trans]
    rw [hcard] at hcQ
    dsimp only [n] at hcQ
    omega
  by_cases hA : A.Nonempty
  · let r : C.Pending := ⟨d, {
      source := g
      members := A
      nonempty := hA
      record := R
      foreign := hd
      long := hlA
      margin := hmA }⟩
    refine ⟨P.trans Q, B, {r}, ?_, fun _ h => Or.inl h, ?_, ?_, by simp⟩
    · simpa [r, Pending.reserve, Child.budget] using hhcost
    · intro i hi
      rcases hvQ i hi with hv | hB | hiA
      · exact Or.inl (fun w hw => Or.inr (hv w hw))
      · exact Or.inr (Or.inl hB)
      · exact Or.inr (Or.inr ⟨r, Finset.mem_singleton_self _,
          Finset.mem_map.mpr ⟨i, hiA, rfl⟩⟩)
    · intro s hs
      have heq := Finset.mem_singleton.mp hs
      subst s
      rfl
  · have heA : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    refine ⟨P.trans Q, B, ∅, ?_, fun _ h => Or.inl h, ?_, by simp, by simp⟩
    · simpa only [heA, Finset.card_empty, Nat.zero_mul, Nat.mul_zero, add_zero,
        Finset.sum_empty] using hhcost
    · intro i hi
      rcases hvQ i hi with hv | hB | hiA
      · exact Or.inl (fun w hw => Or.inr (hv w hw))
      · exact Or.inr (Or.inl hB)
      · simp only [heA, Finset.notMem_empty] at hiA

end Superstring.Hierarchical.LayerCollection

namespace Superstring.Hierarchical.LayerCollection

variable {α G : Type} {V : Set (List α)} (C : LayerCollection V G)

namespace Pending
variable {C} (r : C.Pending)

def onTarget (d : C.Id) (h : r.1 = d) : C.Child d := h ▸ r.2

@[simp] theorem at_source (d : C.Id) (h : r.1 = d) : (r.onTarget d h).source = r.source := by
  cases h
  rfl

@[simp] theorem at_budget (d : C.Id) (h : r.1 = d) : 2 * (r.onTarget d h).budget = r.reserve := by
  cases h
  rfl

@[simp] theorem at_ids (d : C.Id) (h : r.1 = d) : (r.onTarget d h).ids = r.ids := by
  cases h
  rfl

end Pending

/-- Fulfill precisely the pending requests on one fixed recipient. -/
theorem fulfill_fibre (closed : SubstringClosed V) (d : C.Id) (R : Finset C.Pending)
    (hne : R.Nonempty) (ht : ∀ r ∈ R, r.1 = d)
    (distinct : Set.InjOn Pending.source (R : Set C.Pending)) :
    ∃ Q : Path V [] [], Q.cost ≤ 2 * C.period d.1 + ∑ r ∈ R, r.reserve ∧
      (∀ w ∈ (C.layerAt d).Content, Q.Visits w) ∧
      ∀ r ∈ R, ∀ i ∈ r.ids, ∀ w ∈ (C.layerAt i).Content, Q.Visits w := by
  classical
  let ι := {r // r ∈ R}
  let : Nonempty ι := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  let F : ι → C.Child d := fun r => r.val.onTarget d (ht r.val r.property)
  have hd : Function.Injective (fun r => (F r).source) := by
    intro r s he
    apply Subtype.ext
    apply distinct r.property s.property
    simpa only [F, Pending.at_source] using he
  obtain ⟨Q, hc, hv, hr⟩ := C.fulfill closed d F hd
  have hsum : 2 * ∑ r : ι, (F r).budget = ∑ r ∈ R, r.reserve := by
    rw [Finset.mul_sum]
    simp only [F, Pending.at_budget]
    exact (Finset.sum_subtype R (fun _ => Iff.rfl) Pending.reserve).symm
  refine ⟨Q, by simpa only [hsum] using hc, hv, ?_⟩
  intro r hrR i hi w hw
  have hiF : i ∈ (F ⟨r, hrR⟩).ids := by simpa only [F, Pending.at_ids] using hi
  obtain ⟨j, hj, he⟩ := Finset.mem_map.mp hiF
  subst i
  exact hr ⟨r, hrR⟩ j hj w hw


theorem fulfill_all (closed : SubstringClosed V) (g : G) (R : Finset C.Pending)
    (targets : ∀ r ∈ R, r.1.1 = g)
    (distinct : Set.InjOn Pending.source (R : Set C.Pending)) :
    ∃ (Q : Path V [] []) (J : Finset (Fin (C.size g))),
      Q.cost ≤ 2 * (J.card * C.period g) + ∑ r ∈ R, r.reserve ∧
      (∀ j ∈ J, ∀ w ∈ (C.layer g j).Content, Q.Visits w) ∧
      (∀ r ∈ R, ∀ i ∈ r.ids, ∀ w ∈ (C.layerAt i).Content, Q.Visits w) ∧
      (∀ j ∈ J, ∃ a b : ℤ, (C.layer g j).first a ≤ b ∧
        b ≤ (C.layer g j).last a ∧ b - a < 2 * C.period g) ∧
      (J = ∅ ↔ R = ∅) := by
  classical
  let J : Finset (Fin (C.size g)) := Finset.univ.filter
    (fun j => ∃ r ∈ R, r.1 = ⟨g, j⟩)
  let fibre := fun j => R.filter (fun r => r.1 = ⟨g, j⟩)
  have hJ : ∀ j, j ∈ J ↔ ∃ r ∈ R, r.1 = ⟨g, j⟩ := by simp [J]
  have recipient : ∀ r ∈ R, ∃ j : Fin (C.size g), r.1 = ⟨g, j⟩ := by
    intro r hr
    obtain ⟨⟨a, j⟩, c⟩ := r
    have he := targets ⟨⟨a, j⟩, c⟩ hr
    change a = g at he
    subst a
    exact ⟨j, rfl⟩
  have hex : ∀ j ∈ J, ∃ Q : Path V [] [],
      Q.cost ≤ 2 * C.period g + ∑ r ∈ fibre j, r.reserve ∧
      (∀ w ∈ (C.layer g j).Content, Q.Visits w) ∧
      ∀ r ∈ fibre j, ∀ i ∈ r.ids, ∀ w ∈ (C.layerAt i).Content, Q.Visits w := by
    intro j hj
    obtain ⟨r, hr, ht⟩ := (hJ j).mp hj
    exact C.fulfill_fibre closed ⟨g, j⟩ (fibre j)
      ⟨r, Finset.mem_filter.mpr ⟨hr, ht⟩⟩
      (fun _ h => (Finset.mem_filter.mp h).2)
      (distinct.mono (by intro r hr; exact (Finset.mem_filter.mp hr).1))
  let F : Fin (C.size g) → Path V [] [] := fun j =>
    if h : j ∈ J then (hex j h).choose else .nil [] (C.empty_mem closed g)
  have hF : ∀ j ∈ J,
      (F j).cost ≤ 2 * C.period g + ∑ r ∈ fibre j, r.reserve ∧
      (∀ w ∈ (C.layer g j).Content, (F j).Visits w) ∧
      ∀ r ∈ fibre j, ∀ i ∈ r.ids, ∀ w ∈ (C.layerAt i).Content, (F j).Visits w := by
    intro j hj
    simpa only [F, dite_eq_left hj] using (hex j hj).choose_spec
  have hsum : ∑ j ∈ J, ∑ r ∈ fibre j, r.reserve = ∑ r ∈ R, r.reserve := by
    simp only [fibre, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    obtain ⟨j, hj⟩ := recipient r hr
    have hjJ : j ∈ J := (hJ j).mpr ⟨r, hr, hj⟩
    rw [Finset.sum_eq_single j]
    · simp only [hj, ↓reduceIte]
    · intro k _ hkj
      have hne : r.1 ≠ ⟨g, k⟩ := by
        intro he
        have hh : j = k := by simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hj.symm.trans he
        exact hkj hh.symm
      simp only [hne, ↓reduceIte]
    · exact fun h => False.elim (h hjJ)
  obtain ⟨Q, hcQ, hvQ⟩ := combine_rooted (C.empty_mem closed g) F J
  refine ⟨Q, J, ?_, ?_, ?_, ?_, ?_⟩
  · have hh := Finset.sum_le_sum (fun j hj => (hF j hj).1)
    have he : (∑ j ∈ J, (2 * C.period g + ∑ r ∈ fibre j, r.reserve)) =
        2 * (J.card * C.period g) + ∑ r ∈ R, r.reserve := by
      rw [Finset.sum_add_distrib, hsum]
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
      ring
    rw [he] at hh
    exact hcQ.trans hh
  · intro j hj w hw
    exact hvQ j hj w ((hF j hj).2.1 w hw)
  · intro r hr i hi w hw
    obtain ⟨j, hj⟩ := recipient r hr
    have hjJ : j ∈ J := (hJ j).mpr ⟨r, hr, hj⟩
    exact hvQ j hjJ w ((hF j hjJ).2.2 r (Finset.mem_filter.mpr ⟨hr, hj⟩) i hi w hw)
  · intro j hj
    obtain ⟨r, hr, ht⟩ := (hJ j).mp hj
    let c := r.onTarget ⟨g, j⟩ ht
    refine ⟨c.record.start + c.record.offset, c.record.stop + c.record.offset,
      c.record.first_le, c.record.le_last, ?_⟩
    have hl := c.record.length_lt (C.positive c.source) (C.positive g)
      (C.periodic c.source) (C.periodic g) c.foreign
    have hp := c.later
    change c.record.stop - c.record.start < (C.period c.source : ℤ) + C.period g at hl
    change C.period c.source < C.period g at hp
    omega
  · constructor
    · intro he
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      obtain ⟨j, hj⟩ := recipient r hr
      have hm := (hJ j).mpr ⟨r, hr, hj⟩
      simp only [he, Finset.notMem_empty] at hm
    · intro he
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      obtain ⟨r, hr, _⟩ := (hJ j).mp hj
      simp only [he, Finset.notMem_empty] at hr

end Superstring.Hierarchical.LayerCollection

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.Hierarchical.LayerCollection

variable {α G : Type} [LinearOrder α] {V : Set (List α)} (C : LayerCollection V G)

/-- A whole group is processed, reserving at most one outgoing request record.
Incoming reserves are spent once; every new block and request is included in
this exact numerical budget. -/
theorem process_group (closed : SubstringClosed V) (supply : C.RecordSupply)
    (g : G) (R : Finset C.Pending) (targets : ∀ r ∈ R, r.1.1 = g)
    (distinct : Set.InjOn Pending.source (R : Set C.Pending)) :
    ∃ (Q : Path V [] []) (B : Finset C.PlannedBlock) (O : Finset C.Pending),
      Q.cost + (∑ b ∈ B, b.reserve) + (∑ r ∈ O, r.reserve) ≤
        2 * (C.size g * C.period g) + ∑ r ∈ R, r.reserve ∧
      (∀ i : Fin (C.size g), C.Covered Q B O ⟨g, i⟩) ∧
      (∀ r ∈ R, ∀ i ∈ r.ids, ∀ w ∈ (C.layerAt i).Content, Q.Visits w) ∧
      (∀ r ∈ O, r.source = g) ∧ O.card ≤ 1 := by
  classical
  obtain ⟨P, J, hcP, hjP, hrP, hshort, _⟩ := C.fulfill_all closed g R targets distinct
  have finish (cut : ℕ) (hcut : cut ≤ C.size g) (P' : Path V [] [])
      (hcP' : P'.cost ≤ 2 * (cut * C.period g) + ∑ r ∈ R, r.reserve)
      (hp : ∀ i : Fin (C.size g), i.val < cut → ∀ w ∈ (C.layer g i).Content, P'.Visits w)
      (hpres : ∀ w, P.Visits w → P'.Visits w) :
      ∃ (Q : Path V [] []) (B : Finset C.PlannedBlock) (O : Finset C.Pending),
        Q.cost + (∑ b ∈ B, b.reserve) + (∑ r ∈ O, r.reserve) ≤
          2 * (C.size g * C.period g) + ∑ r ∈ R, r.reserve ∧
        (∀ i : Fin (C.size g), C.Covered Q B O ⟨g, i⟩) ∧
        (∀ r ∈ R, ∀ i ∈ r.ids, ∀ w ∈ (C.layerAt i).Content, Q.Visits w) ∧
        (∀ r ∈ O, r.source = g) ∧ O.card ≤ 1 := by
    obtain ⟨Q, B, O, hcQ, hvQ, hiQ, hsQ, hcardQ⟩ := C.complete_upper closed supply g cut hcut P' hp
    refine ⟨Q, B, O, ?_, ?_, ?_, hsQ, hcardQ⟩
    · have hmul := Nat.add_mul cut (C.size g - cut) (C.period g)
      rw [Nat.add_sub_of_le hcut] at hmul
      omega
    · intro i
      by_cases hi : i.val < cut
      · exact Or.inl (fun w hw => hvQ w (hp i hi w hw))
      · exact hiQ i ((C.mem_upper g cut i).mpr (by omega))
    · exact fun r hr i hi w hw => hvQ w (hpres w (hrP r hr i hi w hw))
  by_cases hJ : J.Nonempty
  · let base := J.max' hJ
    have hbJ : base ∈ J := Finset.max'_mem J hJ
    have hjbase : ∀ j ∈ J, j ≤ base := fun j hj => Finset.le_max' J j hj
    let I := Finset.Iic base \ J
    have hJsub : J ⊆ Finset.Iic base := fun j hj => Finset.mem_Iic.mpr (hjbase j hj)
    have hcard : I.card + J.card = base.val + 1 := by
      have hh := Finset.card_sdiff_add_card_eq_card hJsub
      rw [Fin.card_Iic] at hh
      exact hh
    obtain ⟨a, b, hf, hl, hlen⟩ := hshort base hbJ
    obtain ⟨Q, hcQ, hvQ, hiQ⟩ := C.root_below closed g base P (hjP base hbJ)
      a b hf hl hlen I (fun i hi => Finset.mem_Iic.mp (Finset.mem_sdiff.mp hi).1)
    apply finish (base.val + 1) (by omega) Q
    · have hmul := Nat.add_mul I.card J.card (C.period g)
      rw [hcard] at hmul
      omega
    · intro i hi w hw
      by_cases hj : i ∈ J
      · exact hvQ w (hjP i hj w hw)
      · exact hiQ i (Finset.mem_sdiff.mpr ⟨Finset.mem_Iic.mpr (by change i.val ≤ base.val; omega), hj⟩) w hw
    · exact hvQ
  · have heJ : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    apply finish 0 (Nat.zero_le _) P
    · simpa only [heJ, Finset.card_empty, Nat.zero_mul, Nat.mul_zero] using hcP
    · intro i hi
      omega
    · exact fun _ h => h

end Superstring.Hierarchical.LayerCollection

namespace Superstring.Hierarchical.LayerCollection

variable {α G : Type} [LinearOrder α] {V : Set (List α)} (C : LayerCollection V G)

namespace Covered
variable {C} {P Q : Path V [] []} {B D : Finset C.PlannedBlock} {R O : Finset C.Pending}

 theorem mono {i : C.Id} (h : C.Covered P B R i)
    (hp : ∀ w, P.Visits w → Q.Visits w) (hb : B ⊆ D) (hr : R ⊆ O) :
    C.Covered Q D O i := by
  rcases h with hv | ⟨b, hm, hi⟩ | ⟨r, hm, hi⟩
  · exact Or.inl (fun w hw => hp w (hv w hw))
  · exact Or.inr (Or.inl ⟨b, hb hm, hi⟩)
  · exact Or.inr (Or.inr ⟨r, hr hm, hi⟩)
end Covered

/-- Finite period-order scheduling, with all previously spent and reserved
budgets retained. Strict increase of outgoing requests is proved by their
actual record, and prevents both backward requests and duplicate sources. -/
theorem schedule (closed : SubstringClosed V) (supply : C.RecordSupply)
    (I : Finset G) (P : Path V [] []) (B : Finset C.PlannedBlock) (R : Finset C.Pending)
    (upward : ∀ g ∈ I, ∀ h, C.period g < C.period h → h ∈ I)
    (targets : ∀ r ∈ R, r.1.1 ∈ I) (sources : ∀ r ∈ R, r.source ∉ I)
    (distinct : Set.InjOn Pending.source (R : Set C.Pending))
    (ready : ∀ i : C.Id, i.1 ∈ I ∨ C.Covered P B R i) :
    ∃ Q : Path V [] [],
      Q.cost ≤ P.cost + (∑ b ∈ B, b.reserve) + (∑ r ∈ R, r.reserve) +
        ∑ g ∈ I, 2 * (C.size g * C.period g) ∧
      (∀ w, P.Visits w → Q.Visits w) ∧
      ∀ i : C.Id, ∀ w ∈ (C.layerAt i).Content, Q.Visits w := by
  classical
  induction I using Finset.strongInductionOn generalizing P B R with
  | _ I ih =>
    by_cases hI : I.Nonempty
    · obtain ⟨g, hg, hmin⟩ := Finset.exists_min_image I C.period hI
      let In := R.filter (fun r => r.1.1 = g)
      let Rest := R.filter (fun r => r.1.1 ≠ g)
      have hIn : ∀ r ∈ In, r.1.1 = g := fun _ h => (Finset.mem_filter.mp h).2
      have hdIn : Set.InjOn Pending.source (In : Set C.Pending) :=
        distinct.mono (by intro r hr; exact (Finset.mem_filter.mp hr).1)
      obtain ⟨F, D, O, hcF, hvF, hiF, hsO, hcardO⟩ := C.process_group closed supply g In hIn hdIn
      let P' := P.trans F
      let B' := B ∪ D
      let R' := Rest ∪ O
      have hup : ∀ a ∈ I.erase g, ∀ b, C.period a < C.period b → b ∈ I.erase g := by
        intro a ha b hb
        have haI := (Finset.mem_erase.mp ha).2
        apply Finset.mem_erase.mpr
        refine ⟨?_, upward a haI b hb⟩
        intro he
        subst b
        have := hmin a haI
        omega
      have htarget : ∀ r ∈ R', r.1.1 ∈ I.erase g := by
        intro r hr
        rcases Finset.mem_union.mp hr with hr | hr
        · exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hr).2,
            targets r (Finset.mem_filter.mp hr).1⟩
        · have hl := r.later
          rw [hsO r hr] at hl
          exact Finset.mem_erase.mpr ⟨by intro he; rw [he] at hl; omega,
            upward g hg _ hl⟩
      have hsource : ∀ r ∈ R', r.source ∉ I.erase g := by
        intro r hr
        rcases Finset.mem_union.mp hr with hr | hr
        · exact fun hh => sources r (Finset.mem_filter.mp hr).1 (Finset.mem_of_mem_erase hh)
        · rw [hsO r hr]
          exact Finset.notMem_erase g I
      have hd : Set.InjOn Pending.source (R' : Set C.Pending) := by
        intro r hr s hs he
        rcases Finset.mem_union.mp hr with hr | hr <;>
          rcases Finset.mem_union.mp hs with hs | hs
        · exact distinct (Finset.mem_filter.mp hr).1 (Finset.mem_filter.mp hs).1 he
        · have hh : r.source = g := he.trans (hsO s hs)
          exact False.elim (sources r (Finset.mem_filter.mp hr).1 (hh ▸ hg))
        · have hh : s.source = g := he.symm.trans (hsO r hr)
          exact False.elim (sources s (Finset.mem_filter.mp hs).1 (hh ▸ hg))
        · exact Finset.card_le_one.mp hcardO r hr s hs
      have hready : ∀ i : C.Id, i.1 ∈ I.erase g ∨ C.Covered P' B' R' i := by
        intro i
        by_cases hi : i.1 ∈ I.erase g
        · exact Or.inl hi
        apply Or.inr
        by_cases hig : i.1 = g
        · obtain ⟨a, j⟩ := i
          change a = g at hig
          subst a
          exact (hvF j).mono (fun _ h => Or.inr h)
            Finset.subset_union_right Finset.subset_union_right
        · have hnot : i.1 ∉ I := fun hm => hi (Finset.mem_erase.mpr ⟨hig, hm⟩)
          have hcov := (ready i).resolve_left hnot
          rcases hcov with hv | ⟨b, hb, hbi⟩ | ⟨r, hr, hri⟩
          · exact Or.inl (fun w hw => Or.inl (hv w hw))
          · exact Or.inr (Or.inl ⟨b, Finset.mem_union_left _ hb, hbi⟩)
          · by_cases hrg : r.1.1 = g
            · exact Or.inl (fun w hw => Or.inr (hiF r (Finset.mem_filter.mpr ⟨hr, hrg⟩) i hri w hw))
            · exact Or.inr (Or.inr ⟨r, Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hr, hrg⟩), hri⟩)
      obtain ⟨Q, hcQ, hvQ, hlQ⟩ := ih (I.erase g) (Finset.erase_ssubset hg)
        P' B' R' hup htarget hsource hd hready
      refine ⟨Q, ?_, fun w hw => hvQ w (Or.inl hw), hlQ⟩
      have hBsum : (∑ b ∈ B', b.reserve) ≤ (∑ b ∈ B, b.reserve) + ∑ b ∈ D, b.reserve := by
        have hh := Finset.sum_union_inter (s₁ := B) (s₂ := D) (f := PlannedBlock.reserve)
        change _ ≤ _
        dsimp only [B']
        omega
      have hRsum : (∑ r ∈ R', r.reserve) ≤ (∑ r ∈ Rest, r.reserve) + ∑ r ∈ O, r.reserve := by
        have hh := Finset.sum_union_inter (s₁ := Rest) (s₂ := O) (f := Pending.reserve)
        dsimp only [R']
        omega
      have hpartition : (∑ r ∈ In, r.reserve) + (∑ r ∈ Rest, r.reserve) = ∑ r ∈ R, r.reserve :=
        Finset.sum_filter_add_sum_filter_not R (fun r => r.1.1 = g) Pending.reserve
      have hbudget := Finset.sum_erase_add I (fun g => 2 * (C.size g * C.period g)) hg
      have hPcost : P'.cost = P.cost + F.cost := Path.cost_trans _ _
      omega
    · have heI : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
      have heR : R = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro r hr
        have hh := targets r hr
        simp only [heI, Finset.notMem_empty] at hh
      obtain ⟨Q, hcQ, hvQ, hlQ⟩ := PlannedBlock.execute closed B P (by
        intro i
        have hh := ready i
        simp only [heI, Finset.notMem_empty, false_or] at hh
        rcases hh with hv | hb | ⟨r, hr, _⟩
        · exact Or.inl hv
        · exact Or.inr hb
        · simp only [heR, Finset.notMem_empty] at hr)
      exact ⟨Q, by simpa only [heI, heR, Finset.sum_empty, add_zero] using hcQ, hvQ, hlQ⟩

/-- The geometric main_oai bound for any actual finite layer collection supplied
by the count rule. All local plans, requests, and functional cycles are paid. -/
theorem connect [Fintype G] (closed : SubstringClosed V) (he : [] ∈ V)
    (supply : C.RecordSupply) :
    ∃ Q : Path V [] [], Q.cost ≤ 2 * ∑ g, C.size g * C.period g ∧
      ∀ i : C.Id, ∀ w ∈ (C.layerAt i).Content, Q.Visits w := by
  classical
  obtain ⟨Q, hcQ, _, hvQ⟩ := C.schedule closed supply Finset.univ (.nil [] he) ∅ ∅
    (by simp) (by simp) (by simp) (by simp [Set.InjOn]) (by simp)
  refine ⟨Q, ?_, hvQ⟩
  simpa only [Path.cost, Finset.sum_empty, zero_add, Finset.mul_sum] using hcQ

end Superstring.Hierarchical.LayerCollection

namespace Superstring.Counts.Data

variable {α : Type} [LinearOrder α] [DecidableEq α] [Inhabited α]

/-- Reading the fully connected actual layer graph gives a constructive
numerical bound, without treating recorded prefixes as vertices. -/
theorem superstring_of_counts (D : Data α) (hD : D.WellFormed)
    (required_valid : ∀ s ∈ D.required, s ∈ D.vertices ∧ s ≠ []) :
    ∃ T : List α, T.length ≤ 2 * D.weight ∧ ∀ s ∈ D.required, s <:+: T := by
  classical
  let C := (D.threading hD).collection hD.closed
  obtain ⟨Q, hcQ, hvQ⟩ := C.connect hD.closed hD.empty_mem (D.collection_records hD)
  have hbudget : (∑ g, C.size g * C.period g) = D.weight := by
    simpa only [C, Hierarchical.Threading.collection, Nat.mul_comm] using D.layer_budget hD
  refine ⟨Q.written, ?_, ?_⟩
  · rw [Hierarchical.Path.length_written]
    simpa only [hbudget] using hcQ
  · intro s hs
    obtain ⟨hsV, hsne⟩ := required_valid s hs
    have hn := D.required_le_count hsV hsne hs
    have hpos : 0 < Fintype.card ((D.threading hD).Recorded s) := by
      rw [D.recorded_count hD hsne]
      omega
    obtain ⟨o⟩ := Fintype.card_pos_iff.mp hpos
    let e := ((D.threading hD).occurrenceEquiv hD.closed s).symm o
    let L := C.layerAt e.1
    have hprefix : s <+: Hierarchical.textWord (C.text e.1.1) e.2.val.val (L.last e.2.val.val) :=
      (L.records_iff_prefix s e.2.val.val).mp e.2.property
    have hv := hvQ e.1 _ ⟨e.2.val.val, L.last e.2.val.val,
      L.first_le_last e.2.val.val, le_rfl, rfl⟩
    have hinfix := Q.visited_infix_written hv
    simpa only [List.nil_append] using hprefix.isInfix.trans hinfix

end Superstring.Counts.Data

namespace Superstring

/-- The approximation inequality, separated from computational implementation.
This lemma is NOT the main_oai theorem: a polynomial bit implementation is required. -/
theorem exists_two_approximation (S : Instance) :
    ∃ T : Word, IsCommonSuperstring S T ∧ T.length ≤ 2 * opt S := by
  obtain ⟨T, hcT, hvT⟩ := (Input.data S).superstring_of_counts
    (Counts.Data.input_wellFormed S) (fun s hs =>
      ⟨Input.required_mem hs, (Input.mem_core.mp hs).2.1⟩)
  exact ⟨T, (Input.core_superstring_iff S T).mp hvT,
    hcT.trans (Nat.mul_le_mul_left 2 (weight_le_opt S))⟩

end Superstring

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.BitCode

abbrev Store (K : Type) := K → List Bool

/-- A finite-control bit-stack instruction. There is no unbounded internal
state and no operation on an entire stack other than one push/pop/peek. -/
inductive Instr (K L : Type)
  | push (k : K) (b : Bool) (next : L)
  | pop (k : K) (next : L)
  | branch (k : K) (empty low high : L)
  | jump (next : L)

namespace Instr

def map {K L M : Type} (f : L → M) : Instr K L → Instr K M
  | .push k b l => .push k b (f l)
  | .pop k l => .pop k (f l)
  | .branch k e l h => .branch k (f e) (f l) (f h)
  | .jump l => .jump (f l)

def run {K L : Type} [DecidableEq K] : Instr K L → Store K → L × Store K
  | .push k b l, s => (l, Function.update s k (b :: s k))
  | .pop k l, s => (l, Function.update s k (s k).tail)
  | .branch k e l h, s => (match (s k).head? with
      | none => e
      | some false => l
      | some true => h, s)
  | .jump l, s => (l, s)

@[simp] theorem run_map {K L M : Type} [DecidableEq K] (f : L → M)
    (i : Instr K L) (s : Store K) : (i.map f).run s = Prod.map f id (i.run s) := by
  cases i with
  | branch k e l h => cases hs : (s k).head? with
    | none => simp [map, run, hs]
    | some b => cases b <;> simp [map, run, hs]
  | _ => rfl


def emit {K L : Type} : Instr K (Option L) →
    Turing.TM2.Stmt (fun _ : K => Bool) L (Option Bool)
  | .push k b l => .push k (fun _ => b) (finish l)
  | .pop k l => .pop k (fun _ _ => none) (finish l)
  | .branch k e l h => .peek k (fun _ b => b)
      (.branch Option.isNone (finish e)
        (.branch (fun b => b.getD false) (finish h) (finish l)))
  | .jump l => finish l
where
  finish {K L : Type} (l : Option L) :
      Turing.TM2.Stmt (fun _ : K => Bool) L (Option Bool) :=
    .load (fun _ => none) (match l with | none => .halt | some x => .goto (fun _ => x))

theorem finish_step {K L : Type} [DecidableEq K] (l : Option L)
    (v : Option Bool) (s : Store K) :
    Turing.TM2.stepAux (emit.finish l) v s = ⟨l, none, s⟩ := by
  cases l <;> rfl

theorem emit_step {K L : Type} [DecidableEq K] (i : Instr K (Option L))
    (v : Option Bool) (s : Store K) :
    Turing.TM2.stepAux i.emit v s = ⟨(i.run s).1, none, (i.run s).2⟩ := by
  cases i with
  | push k b l => exact finish_step l v _
  | pop k l => exact finish_step l none _
  | branch k e l h =>
    cases hs : (s k).head? with
    | none => simp [emit, Turing.TM2.stepAux, hs, finish_step, run]
    | some b => cases b <;> simp [emit, Turing.TM2.stepAux, hs, finish_step, run]
  | jump l => exact finish_step l v s

end Instr

/-- Structured bit-stack code. Loops are ordinary operational loops, not
unbounded-cost primitives. Their iteration count is charged in `Exec`. -/
inductive Block (K : Type)
  | push (k : K) (b : Bool)
  | pop (k : K)
  | skip
  | branch (k : K) (empty low high : Block K)
  | seq (first second : Block K)
  | loop (k : K) (body : Block K)

namespace Block

def Label {K : Type} : Block K → Type
  | .push _ _ | .pop _ | .skip => Unit
  | .branch _ a b c => Unit ⊕ (Label a ⊕ Label b ⊕ Label c)
  | .seq a b => Label a ⊕ Label b
  | .loop _ a => Option (Label a)

instance labelFintype {K : Type} : (b : Block K) → Fintype b.Label
  | .push _ _ | .pop _ | .skip => inferInstanceAs (Fintype Unit)
  | .branch _ a b c => by
    letI := labelFintype a
    letI := labelFintype b
    letI := labelFintype c
    exact inferInstanceAs (Fintype (Unit ⊕ (Label a ⊕ Label b ⊕ Label c)))
  | .seq a b => by
    letI := labelFintype a
    letI := labelFintype b
    exact inferInstanceAs (Fintype (Label a ⊕ Label b))
  | .loop _ a => by
    letI := labelFintype a
    exact inferInstanceAs (Fintype (Option (Label a)))

instance labelDecidableEq {K : Type} : (b : Block K) → DecidableEq b.Label
  | .push _ _ | .pop _ | .skip => inferInstanceAs (DecidableEq Unit)
  | .branch _ a b c => by
    letI := labelDecidableEq a
    letI := labelDecidableEq b
    letI := labelDecidableEq c
    exact inferInstanceAs (DecidableEq (Unit ⊕ (Label a ⊕ Label b ⊕ Label c)))
  | .seq a b => by
    letI := labelDecidableEq a
    letI := labelDecidableEq b
    exact inferInstanceAs (DecidableEq (Label a ⊕ Label b))
  | .loop _ a => by
    letI := labelDecidableEq a
    exact inferInstanceAs (DecidableEq (Option (Label a)))

def start {K : Type} : (b : Block K) → b.Label
  | .push _ _ | .pop _ | .skip => ()
  | .branch _ _ _ _ => .inl ()
  | .seq a _ => .inl a.start
  | .loop _ _ => none

def code {K : Type} : (b : Block K) → b.Label → Instr K (Option b.Label)
  | .push k b, _ => .push k b none
  | .pop k, _ => .pop k none
  | .skip, _ => .jump none
  | .branch k a b c, .inl _ => .branch k
      (some (.inr (.inl a.start))) (some (.inr (.inr (.inl b.start))))
      (some (.inr (.inr (.inr c.start))))
  | .branch _ a _ _, .inr (.inl l) => (a.code l).map (Option.map (Sum.inr ∘ Sum.inl))
  | .branch _ _ b _, .inr (.inr (.inl l)) =>
      (b.code l).map (Option.map (Sum.inr ∘ Sum.inr ∘ Sum.inl))
  | .branch _ _ _ c, .inr (.inr (.inr l)) =>
      (c.code l).map (Option.map (Sum.inr ∘ Sum.inr ∘ Sum.inr))
  | .seq a b, .inl l => (a.code l).map (fun q =>
      match q with | none => some (.inr b.start) | some x => some (.inl x))
  | .seq _ b, .inr l => (b.code l).map (Option.map Sum.inr)
  | .loop k a, none => .branch k none (some (some a.start)) (some (some a.start))
  | .loop _ a, some l => (a.code l).map (fun q => some q)

end Block

end Superstring.BitCode

namespace Superstring.BitCode

variable {K : Type} [DecidableEq K]

/-- Exact execution in the finite-control graph, stopping before a halt label
is stepped. This is a finite trace, not an oracle for a computation. -/
inductive Steps {L : Type} (code : L → Instr K (Option L)) :
    (Option L × Store K) → ℕ → (Option L × Store K) → Prop
  | refl (c) : Steps code c 0 c
  | step (l : L) (s : Store K) {n d} (h : Steps code ((code l).run s) n d) :
      Steps code (some l, s) (n + 1) d

namespace Steps

variable {L M : Type} {code : L → Instr K (Option L)}

theorem trans {a b c} {m n : ℕ} (h : Steps code a m b) (h' : Steps code b n c) :
    Steps code a (m + n) c := by
  induction h with
  | refl => simpa using h'
  | step l s h ih => simpa only [Nat.add_assoc, Nat.add_comm 1] using step l s (ih h')

theorem map (f : Option L → Option M) (j : L → M)
    {big : M → Instr K (Option M)}
    (hl : ∀ l, f (some l) = some (j l))
    (hc : ∀ l, big (j l) = (code l).map f)
    {a b} {n} (h : Steps code a n b) :
    Steps big (Prod.map f id a) n (Prod.map f id b) := by
  induction h with
  | refl => exact .refl _
  | step l s h ih =>
    simp only [Prod.map, id_eq, hl] at *
    apply Steps.step
    simpa only [hc, Instr.run_map, Prod.map, id_eq] using ih

end Steps

namespace Block

/-- Big-step semantics with the exact number of primitive bit instructions. -/
inductive Exec : Block K → Store K → Store K → ℕ → Prop
  | push (k b s) : Exec (.push k b) s (Function.update s k (b :: s k)) 1
  | pop (k s) : Exec (.pop k) s (Function.update s k (s k).tail) 1
  | skip (s) : Exec .skip s s 1
  | branch_none {k a b c s t n} (h : (s k).head? = none) (run : Exec a s t n) :
      Exec (.branch k a b c) s t (n + 1)
  | branch_false {k a b c s t n} (h : (s k).head? = some false) (run : Exec b s t n) :
      Exec (.branch k a b c) s t (n + 1)
  | branch_true {k a b c s t n} (h : (s k).head? = some true) (run : Exec c s t n) :
      Exec (.branch k a b c) s t (n + 1)
  | seq {a b s t u m n} (first : Exec a s t m) (second : Exec b t u n) :
      Exec (.seq a b) s u (m + n)
  | loop_nil {k a s} (h : s k = []) : Exec (.loop k a) s s 1
  | loop_cons {k a s t u m n} (h : s k ≠ []) (body : Exec a s t m)
      (rest : Exec (.loop k a) t u n) : Exec (.loop k a) s u (m + n + 1)

theorem exec_steps {b : Block K} {s t : Store K} {n : ℕ} (h : b.Exec s t n) :
    Steps b.code (some b.start, s) n (none, t) := by
  induction h with
  | push k b s => exact .step () s (.refl _)
  | pop k s => exact .step () s (.refl _)
  | skip s => exact .step () s (.refl _)
  | @branch_none k a b c s t n hh run ih =>
    apply Steps.step
    simp only [code, start, Instr.run, hh]
    exact ih.map (Option.map (Sum.inr ∘ Sum.inl)) (Sum.inr ∘ Sum.inl)
      (fun _ => rfl) (fun _ => rfl)
  | @branch_false k a b c s t n hh run ih =>
    apply Steps.step
    simp only [code, start, Instr.run, hh]
    exact ih.map (Option.map (Sum.inr ∘ Sum.inr ∘ Sum.inl))
      (Sum.inr ∘ Sum.inr ∘ Sum.inl) (fun _ => rfl) (fun _ => rfl)
  | @branch_true k a b c s t n hh run ih =>
    apply Steps.step
    simp only [code, start, Instr.run, hh]
    exact ih.map (Option.map (Sum.inr ∘ Sum.inr ∘ Sum.inr))
      (Sum.inr ∘ Sum.inr ∘ Sum.inr) (fun _ => rfl) (fun _ => rfl)
  | @seq a b s t u m n first second ih₁ ih₂ =>
    let f : Option a.Label → Option ((seq a b).Label) := fun q =>
      match q with | none => some (.inr b.start) | some x => some (.inl x)
    have h₁ : Steps (seq a b).code (some (.inl a.start), s) m (some (.inr b.start), t) :=
      ih₁.map f Sum.inl (fun _ => rfl) (fun _ => rfl)
    have h₂ : Steps (seq a b).code (some (.inr b.start), t) n (none, u) :=
      ih₂.map (Option.map Sum.inr) Sum.inr (fun _ => rfl) (fun _ => rfl)
    exact h₁.trans h₂
  | @loop_nil k a s hh =>
    apply Steps.step
    simpa only [code, start, Instr.run, hh, List.head?_nil] using
      (Steps.refl (code := code (.loop k a)) (none, s))
  | @loop_cons k a s t u m n hh body rest ih₁ ih₂ =>
    apply Steps.step
    have hstart : ((code (.loop k a)) none).run s = (some (some a.start), s) := by
      cases he : s k with
      | nil => exact False.elim (hh he)
      | cons x xs => cases x <;> simp only [code, Instr.run, he, List.head?_cons] <;> rfl
    dsimp only [start]
    rw [hstart]
    exact (ih₁.map some some (fun _ => rfl) (fun _ => rfl)).trans ih₂


def machine [Fintype K] (b : Block K) (input output : K) : Turing.FinTM2 where
  K := K
  k₀ := input
  k₁ := output
  Γ _ := Bool
  Λ := b.Label
  main := b.start
  σ := Option Bool
  initialState := none
  m l := (b.code l).emit

def pack {L : Type} (c : Option L × Store K) :
    Turing.TM2.Cfg (fun _ : K => Bool) L (Option Bool) := ⟨c.1, none, c.2⟩

theorem steps_iterate {L : Type} {code : L → Instr K (Option L)}
    {s t : Option L × Store K} {n : ℕ} (h : Steps code s n t) :
    (fun c => c.bind (Turing.TM2.step (fun l => (code l).emit)))^[n]
      (some (pack s)) = some (pack t) := by
  induction h with
  | refl => rfl
  | step l S h ih =>
    rw [Function.iterate_succ_apply]
    simpa only [pack, Option.bind_some, Turing.TM2.step, Instr.emit_step] using ih

def exec_machine [Fintype K] (b : Block K) (input output : K)
    {s t : Store K} {n : ℕ} (h : b.Exec s t n) :
    StateTransition.EvalsToInTime (b.machine input output).step
      (pack (some b.start, s)) (some (pack (none, t))) n :=
  ⟨⟨n, steps_iterate (exec_steps h)⟩, le_rfl⟩

end Block

end Superstring.BitCode

namespace Superstring.BitCode

variable {K : Type} [DecidableEq K]

/-- A single populated stack: the exact Mathlib initial/final convention. -/
def single (k : K) (w : List Bool) : Store K := fun j => if j = k then w else []

namespace Block

theorem init_eq [Fintype K] (b : Block K) (i o : K) (w : List Bool) :
    Turing.initList (b.machine i o) w = pack (some b.start, single i w) := by
  dsimp only [Turing.initList, machine, pack]
  apply congrArg (fun S : Store K => Turing.TM2.Cfg.mk (some b.start) none S)
  funext k
  by_cases h : k = i
  · subst k
    rfl
  · simp only [dite_eq_right h, single, ite_eq_right h]

theorem halt_eq [Fintype K] (b : Block K) (i o : K) (w : List Bool) :
    Turing.haltList (b.machine i o) w = pack (none, single o w) := by
  dsimp only [Turing.haltList, machine, pack]
  apply congrArg (fun S : Store K => Turing.TM2.Cfg.mk none none S)
  funext k
  by_cases h : k = o
  · subst k
    rfl
  · simp only [dite_eq_right h, single, ite_eq_right h]

/-- Execution with a polynomial clock gives a polynomial-time TM2 certificate. -/
noncomputable def certificate [Fintype K] {α β : Type}
    (ea : α → List Bool) (eb : β → List Bool) (f : α → β)
    (b : Block K) (i o : K) (P : Polynomial ℕ)
    (correct : ∀ a, ∃ n, n ≤ P.eval (ea a).length ∧
      b.Exec (single i (ea a)) (single o (eb (f a))) n) :
    Turing.TM2ComputableInPolyTime ea eb f where
  tm := b.machine i o
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := P
  outputsFun a := by
    let n := (correct a).choose
    have hn := (correct a).choose_spec
    refine ⟨⟨n, ?_⟩, hn.1⟩
    change (flip bind (b.machine i o).step)^[n]
      (some (Turing.initList (b.machine i o) ((ea a).map id))) =
        some (Turing.haltList (b.machine i o) ((eb (f a)).map id))
    have hi := init_eq b i o (ea a)
    have ho := halt_eq b i o (eb (f a))
    dsimp only [machine] at *
    simp only [List.map_id]
    rw [hi, ho]
    exact steps_iterate (exec_steps hn.2)

theorem certificate_finite [Fintype K] {α β : Type}
    (ea : α → List Bool) (eb : β → List Bool) (f : α → β)
    (b : Block K) (i o : K) (P : Polynomial ℕ)
    (correct : ∀ a, ∃ n, n ≤ P.eval (ea a).length ∧
      b.Exec (single i (ea a)) (single o (eb (f a))) n)
    (k : (b.certificate ea eb f i o P correct).tm.K) :
    Finite ((b.certificate ea eb f i o P correct).tm.Γ k) := inferInstanceAs (Finite Bool)

end Block

section Size
variable [Fintype K]

def size (s : Store K) : ℕ := ∑ k, (s k).length

theorem size_update (s : Store K) (k : K) (w : List Bool) :
    size (Function.update s k w) + (s k).length = size s + w.length := by
  classical
  have h₁ := Finset.sum_erase_add Finset.univ (fun j => (Function.update s k w j).length)
    (Finset.mem_univ k)
  have h₂ := Finset.sum_erase_add Finset.univ (fun j => (s j).length) (Finset.mem_univ k)
  have he : (∑ j ∈ Finset.univ.erase k, (Function.update s k w j).length) =
      ∑ j ∈ Finset.univ.erase k, (s j).length := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  simp only [he, Function.update_self] at h₁
  dsimp only [size]
  omega

theorem size_push (s : Store K) (k : K) (b : Bool) :
    size (Function.update s k (b :: s k)) = size s + 1 := by
  have hh := size_update s k (b :: s k)
  simp only [List.length_cons] at hh
  omega

theorem size_pop (s : Store K) (k : K) :
    size (Function.update s k (s k).tail) ≤ size s := by
  have hh := size_update s k (s k).tail
  simp only [List.length_tail] at hh
  omega

/-- Every actually executed primitive bit instruction increases total stored
length by at most one; branch tests and iterations do not hide bulk operations. -/
theorem Block.Exec.size_le {b : Block K} {s t : Store K} {n : ℕ}
    (h : b.Exec s t n) : size t ≤ size s + n := by
  induction h with
  | push k b s => exact le_of_eq (size_push s k b)
  | pop k s => exact (size_pop s k).trans (Nat.le_add_right _ _)
  | skip => omega
  | branch_none _ _ ih => omega
  | branch_false _ _ ih => omega
  | branch_true _ _ ih => omega
  | seq _ _ ih₁ ih₂ => omega
  | loop_nil => omega
  | loop_cons _ _ _ ih₁ ih₂ => omega

end Size

end Superstring.BitCode

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.BitCode.Block

variable {K : Type} [DecidableEq K]

/-- Clearing and transfers are explicit bit programs. In particular, reversing
or copying a variable-width label is never given unit cost. -/
def clear (k : K) : Block K := .loop k (.pop k)

def transfer (i j : K) : Block K := .loop i
  (.branch i .skip (.seq (.pop i) (.push j false)) (.seq (.pop i) (.push j true)))

theorem clear_exec (k : K) (s : Store K) :
    (clear k).Exec s (Function.update s k []) (2 * (s k).length + 1) := by
  generalize he : s k = w
  induction w generalizing s with
  | nil =>
    have hx : Function.update s k [] = s := by rw [← he, Function.update_eq_self]
    rw [hx]
    exact .loop_nil he
  | cons x xs ih =>
    let t := Function.update s k xs
    have ht : t k = xs := Function.update_self _ _ _
    have hbody : Exec (.pop k) s t 1 := by
      simpa only [he, List.tail_cons, t] using Exec.pop k s
    have hrest := ih t ht
    have hu : Function.update t k [] = Function.update s k [] := Function.update_idem _ _ _
    have hh := Exec.loop_cons (by simp [he]) hbody hrest
    rw [hu] at hh
    rw [show 2 * (x :: xs).length + 1 = 1 + (2 * xs.length + 1) + 1 by
      simp only [List.length_cons]; omega]
    exact hh

theorem transfer_exec (i j : K) (hne : i ≠ j) (s : Store K) :
    (transfer i j).Exec s
      (Function.update (Function.update s i []) j ((s i).reverse ++ s j))
      (4 * (s i).length + 1) := by
  generalize he : s i = w
  induction w generalizing s with
  | nil =>
    have hx : Function.update (Function.update s i []) j (List.reverse [] ++ s j) = s := by
      simp only [List.reverse_nil, List.nil_append]
      rw [← he, Function.update_eq_self, Function.update_eq_self]
    rw [hx]
    exact .loop_nil he
  | cons x xs ih =>
    let t := Function.update (Function.update s i xs) j (x :: s j)
    have ht : t i = xs := by simp [t, hne]
    have htj : t j = x :: s j := Function.update_self _ _ _
    have hpop : Exec (.pop i) s (Function.update s i xs) 1 := by
      simpa only [he, List.tail_cons] using Exec.pop i s
    have hpush : Exec (.push j x) (Function.update s i xs) t 1 := by
      simpa only [Function.update_of_ne hne.symm, t] using Exec.push j x (Function.update s i xs)
    have hbody : Exec
        (.branch i .skip (.seq (.pop i) (.push j false)) (.seq (.pop i) (.push j true))) s t 3 := by
      cases x with
      | false => exact .branch_false (by simp [he]) (.seq hpop hpush)
      | true => exact .branch_true (by simp [he]) (.seq hpop hpush)
    have hrest := ih t ht
    rw [htj] at hrest
    have hu : Function.update (Function.update t i []) j (xs.reverse ++ x :: s j) =
        Function.update (Function.update s i []) j ((x :: xs).reverse ++ s j) := by
      funext k
      by_cases hik : k = i
      · subst k
        simp [hne]
      · by_cases hjk : k = j
        · subst k
          simp [List.reverse_cons, List.append_assoc]
        · simp [t, hik, hjk]
    have hh := Exec.loop_cons (by simp [he]) hbody hrest
    rw [hu] at hh
    rw [show 4 * (x :: xs).length + 1 = 3 + (4 * xs.length + 1) + 1 by
      simp only [List.length_cons]; omega]
    exact hh

end Superstring.BitCode.Block

namespace Superstring.BitCode.Block

variable {K : Type} [DecidableEq K]


def fanout (i j k : K) : Block K := .loop i (.branch i .skip
  (.seq (.pop i) (.seq (.push j false) (.push k false)))
  (.seq (.pop i) (.seq (.push j true) (.push k true))))

theorem fanout_exec (i j k : K) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (s : Store K) : (fanout i j k).Exec s
      (Function.update (Function.update (Function.update s i [])
        j ((s i).reverse ++ s j)) k ((s i).reverse ++ s k))
      (5 * (s i).length + 1) := by
  generalize he : s i = w
  induction w generalizing s with
  | nil =>
    have hx : Function.update (Function.update (Function.update s i [])
        j (List.reverse [] ++ s j)) k (List.reverse [] ++ s k) = s := by
      simp only [List.reverse_nil, List.nil_append]
      rw [← he, Function.update_eq_self, Function.update_eq_self, Function.update_eq_self]
    rw [hx]
    exact .loop_nil he
  | cons x xs ih =>
    let t := Function.update (Function.update (Function.update s i xs) j (x :: s j)) k (x :: s k)
    have ht : t i = xs := by simp [t, hij, hik]
    have htj : t j = x :: s j := by simp [t, hjk]
    have htk : t k = x :: s k := Function.update_self _ _ _
    have hp : Exec (.pop i) s (Function.update s i xs) 1 := by
      simpa only [he, List.tail_cons] using Exec.pop i s
    have hj : Exec (.push j x) (Function.update s i xs)
        (Function.update (Function.update s i xs) j (x :: s j)) 1 := by
      simpa only [Function.update_of_ne hij.symm] using Exec.push j x (Function.update s i xs)
    have hk : Exec (.push k x) (Function.update (Function.update s i xs) j (x :: s j)) t 1 := by
      simpa only [Function.update_of_ne hjk.symm, Function.update_of_ne hik.symm, t]
        using Exec.push k x (Function.update (Function.update s i xs) j (x :: s j))
    have hbody : Exec (.branch i .skip
        (.seq (.pop i) (.seq (.push j false) (.push k false)))
        (.seq (.pop i) (.seq (.push j true) (.push k true)))) s t 4 := by
      cases x with
      | false => exact .branch_false (by simp [he]) (.seq hp (.seq hj hk))
      | true => exact .branch_true (by simp [he]) (.seq hp (.seq hj hk))
    have hrest := ih t ht
    rw [htj, htk] at hrest
    have hu : Function.update (Function.update (Function.update t i [])
        j (xs.reverse ++ x :: s j)) k (xs.reverse ++ x :: s k) =
        Function.update (Function.update (Function.update s i [])
        j ((x :: xs).reverse ++ s j)) k ((x :: xs).reverse ++ s k) := by
      funext l
      by_cases hli : l = i
      · subst l; simp [hij, hik]
      · by_cases hlj : l = j
        · subst l; simp [hjk, List.reverse_cons, List.append_assoc]
        · by_cases hlk : l = k
          · subst l; simp [List.reverse_cons, List.append_assoc]
          · simp [t, hli, hlj, hlk]
    have hh := Exec.loop_cons (by simp [he]) hbody hrest
    rw [hu] at hh
    rw [show 5 * (x :: xs).length + 1 = 4 + (5 * xs.length + 1) + 1 by
      simp only [List.length_cons]; omega]
    exact hh


def copy (i j t : K) : Block K :=
  .seq (clear j) (.seq (transfer i t) (fanout t i j))

theorem copy_exec (i j t : K) (hij : i ≠ j) (hit : i ≠ t) (hjt : j ≠ t)
    (s : Store K) (ht : s t = []) : (copy i j t).Exec s
      (Function.update s j (s i)) (2 * (s j).length + 9 * (s i).length + 3) := by
  let s₁ := Function.update s j []
  let s₂ := Function.update (Function.update s₁ i []) t ((s₁ i).reverse ++ s₁ t)
  have h₁ := clear_exec j s
  have h₂ := transfer_exec i t hit s₁
  have h₃ := fanout_exec t i j hit.symm hjt.symm hij s₂
  have hi₁ : s₁ i = s i := Function.update_of_ne hij _ _
  have ht₁ : s₁ t = [] := by simp [s₁, hjt.symm, ht]
  have ht₂ : s₂ t = (s i).reverse := by simp [s₂, hi₁, ht₁]
  have hi₂ : s₂ i = [] := by simp [s₂, hit]
  have hj₂ : s₂ j = [] := by simp [s₂, s₁, hjt, hij.symm]
  simp only [ht₂, hi₂, hj₂, List.append_nil, List.reverse_reverse, List.length_reverse] at h₃
  have hfinal : Function.update (Function.update (Function.update s₂ t []) i (s i)) j (s i) =
      Function.update s j (s i) := by
    funext l
    by_cases hlj : l = j
    · subst l; simp
    · by_cases hli : l = i
      · subst l; simp [hij]
      · by_cases hlt : l = t
        · subst l; simp [hjt.symm, hit.symm, ht]
        · simp [s₂, s₁, hlj, hli, hlt]
  rw [hfinal] at h₃
  have hh := Exec.seq h₁ (Exec.seq h₂ h₃)
  rw [hi₁] at hh
  convert hh using 1 <;> first | rfl | omega

end Superstring.BitCode.Block

namespace Superstring.BitCode.Block

variable {K L : Type}

/-- Change the names of registers; loops and instructions are unchanged. -/
def rename (f : K → L) : Block K → Block L
  | .push k b => .push (f k) b
  | .pop k => .pop (f k)
  | .skip => .skip
  | .branch k a b c => .branch (f k) (a.rename f) (b.rename f) (c.rename f)
  | .seq a b => .seq (a.rename f) (b.rename f)
  | .loop k a => .loop (f k) (a.rename f)

/-- A syntax tree mentions only finitely many registers. -/
def support [DecidableEq K] : Block K → Finset K
  | .push k _ | .pop k => {k}
  | .skip => ∅
  | .branch k a b c => insert k (a.support ∪ b.support ∪ c.support)
  | .seq a b => a.support ∪ b.support
  | .loop k a => insert k a.support

theorem update_comp [DecidableEq K] [DecidableEq L] (g : L → K)
    (hg : Function.Injective g) (s : Store K) (j : L) (w : List Bool) :
    Function.update s (g j) w ∘ g = Function.update (s ∘ g) j w := by
  funext i
  by_cases h : i = j
  · subst i; simp
  · have hh : g i ≠ g j := fun he => h (hg he)
    simp [h, hh]

/-- Restrict an execution to any injective family of registers containing all
registers in its syntax. The rest of an infinite ambient store is irrelevant. -/
theorem Exec.pullback [DecidableEq K] [DecidableEq L] (f : K → L) (g : L → K)
    (hg : Function.Injective g) {b : Block K} {s t : Store K} {n : ℕ}
    (h : b.Exec s t n) (hf : ∀ k ∈ b.support, g (f k) = k) :
    (b.rename f).Exec (s ∘ g) (t ∘ g) n := by
  induction h with
  | push k v s =>
    have hk := hf k (by simp [support])
    have hu (w : List Bool) : Function.update s k w ∘ g =
        Function.update (s ∘ g) (f k) w := by
      simpa only [hk] using update_comp g hg s (f k) w
    rw [hu]
    simpa only [rename, Function.comp_apply, hk] using Exec.push (f k) v (s ∘ g)
  | pop k s =>
    have hk := hf k (by simp [support])
    have hu (w : List Bool) : Function.update s k w ∘ g =
        Function.update (s ∘ g) (f k) w := by
      simpa only [hk] using update_comp g hg s (f k) w
    rw [hu]
    simpa only [rename, Function.comp_apply, hk] using Exec.pop (f k) (s ∘ g)
  | skip s => exact .skip _
  | @branch_none k a b c s t n hh h ih =>
    apply Exec.branch_none
    · simpa only [Function.comp_apply, hf k (Finset.mem_insert_self _ _)] using hh
    · exact ih (fun k hk => hf k (by simp [support, hk]))
  | @branch_false k a b c s t n hh h ih =>
    apply Exec.branch_false
    · simpa only [Function.comp_apply, hf k (Finset.mem_insert_self _ _)] using hh
    · exact ih (fun k hk => hf k (by simp [support, hk]))
  | @branch_true k a b c s t n hh h ih =>
    apply Exec.branch_true
    · simpa only [Function.comp_apply, hf k (Finset.mem_insert_self _ _)] using hh
    · exact ih (fun k hk => hf k (by simp [support, hk]))
  | seq h₁ h₂ ih₁ ih₂ =>
    exact .seq (ih₁ (fun k hk => hf k (by simp [support, hk])))
      (ih₂ (fun k hk => hf k (by simp [support, hk])))
  | @loop_nil k a s hh =>
    apply Exec.loop_nil
    simpa only [Function.comp_apply, hf k (Finset.mem_insert_self _ _)] using hh
  | @loop_cons k a s t u m n hh h₁ h₂ ih₁ ih₂ =>
    apply Exec.loop_cons
    · simpa only [Function.comp_apply, hf k (Finset.mem_insert_self _ _)] using hh
    · exact ih₁ (fun k hk => hf k (by simp [support, hk]))
    · exact ih₂ hf

end Superstring.BitCode.Block

namespace Superstring.BitCode

/-- A bounded-loop register language. Every `repeat` uses the ORIGINAL input
length, not a mutable register. Nesting is static in the finite program. Copy is
assignment, not concatenation; the only operation increasing maximum word length
is a one-bit push. This gives uniform polynomial bounds for every program. -/
inductive Program (K : Type)
  | push (k : K) (b : Bool)
  | pop (k : K)
  | clear (k : K)
  | copy (source target : K)
  | skip
  | branch (k : K) (empty low high : Program K)
  | seq (first second : Program K)
  | repeat (body : Program K)

namespace Program

variable {K : Type} [DecidableEq K]

def run (N : ℕ) : Program K → Store K → Store K
  | .push k b, s => Function.update s k (b :: s k)
  | .pop k, s => Function.update s k (s k).tail
  | .clear k, s => Function.update s k []
  | .copy i j, s => Function.update s j (s i)
  | .skip, s => s
  | .branch k a b c, s => match (s k).head? with
    | none => a.run N s
    | some false => b.run N s
    | some true => c.run N s
  | .seq a b, s => b.run N (a.run N s)
  | .repeat a, s => (a.run N)^[N] s

def work (N : ℕ) : Program K → ℕ
  | .push _ _ | .pop _ | .clear _ | .copy _ _ | .skip => 1
  | .branch _ a b c => 1 + a.work N + b.work N + c.work N
  | .seq a b => a.work N + b.work N
  | .repeat a => (N + 1) * (a.work N + 1)

noncomputable def polynomial : Program K → Polynomial ℕ
  | .push _ _ | .pop _ | .clear _ | .copy _ _ | .skip => 1
  | .branch _ a b c => 1 + a.polynomial + b.polynomial + c.polynomial
  | .seq a b => a.polynomial + b.polynomial
  | .repeat a => (Polynomial.X + 1) * (a.polynomial + 1)

omit [DecidableEq K] in
theorem eval_polynomial (p : Program K) (N : ℕ) : p.polynomial.eval N = p.work N := by
  induction p <;> simp_all [polynomial, work]

omit [DecidableEq K] in
theorem work_pos (p : Program K) (N : ℕ) : 0 < p.work N := by
  induction p <;> simp_all [work]

/-- All stack lengths are bounded by a common number. -/
def Bounded (s : Store K) (M : ℕ) : Prop := ∀ k, (s k).length ≤ M

omit [DecidableEq K] in
theorem Bounded.mono {s : Store K} {M M' : ℕ} (h : Bounded s M) (hh : M ≤ M') :
    Bounded s M' := fun k => (h k).trans hh

theorem Bounded.update {s : Store K} {M : ℕ} (h : Bounded s M) (k : K)
    (w : List Bool) (hw : w.length ≤ M) : Bounded (Function.update s k w) M := by
  intro j
  by_cases hj : j = k
  · subst j; simpa using hw
  · simpa [hj] using h j

omit [DecidableEq K] in
theorem iterate_bounded (f : Store K → Store K) (w : ℕ)
    (h : ∀ s M, Bounded s M → Bounded (f s) (M + w))
    (s : Store K) (M n : ℕ) (hs : Bounded s M) :
    Bounded (f^[n] s) (M + n * w) := by
  induction n with
  | zero => simpa using hs
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hh := h (f^[n] s) (M + n * w) ih
    simpa only [Nat.succ_mul, Nat.add_assoc] using hh

theorem run_bounded (p : Program K) (N : ℕ) (s : Store K) (M : ℕ)
    (hs : Bounded s M) : Bounded (p.run N s) (M + p.work N) := by
  induction p generalizing s M with
  | push k b =>
    change Bounded (Function.update s k (b :: s k)) (M + 1)
    exact (hs.mono (Nat.le_add_right M 1)).update k (b :: s k)
      (by simpa only [List.length_cons] using Nat.succ_le_succ (hs k))
  | pop k =>
    change Bounded (Function.update s k (s k).tail) (M + 1)
    exact (hs.mono (Nat.le_add_right M 1)).update k (s k).tail
      (by simp only [List.length_tail]; have := hs k; omega)
  | clear k =>
    exact (hs.mono (Nat.le_add_right M 1)).update k [] (by simp)
  | copy i j =>
    exact (hs.mono (Nat.le_add_right M 1)).update j (s i) ((hs i).trans (Nat.le_add_right M 1))
  | skip => exact hs.mono (Nat.le_add_right M 1)
  | branch k a b c iha ihb ihc =>
    dsimp only [run]
    cases hh : (s k).head? with
    | none => exact (iha s M hs).mono (by change M + a.work N ≤ M + (1 + a.work N + b.work N + c.work N); omega)
    | some q => cases q with
      | false => exact (ihb s M hs).mono (by change M + b.work N ≤ M + (1 + a.work N + b.work N + c.work N); omega)
      | true => exact (ihc s M hs).mono (by change M + c.work N ≤ M + (1 + a.work N + b.work N + c.work N); omega)
  | seq a b iha ihb =>
    have hh := ihb (a.run N s) (M + a.work N) (iha s M hs)
    simpa only [run, work, Nat.add_assoc] using hh
  | «repeat» a ih =>
    have hh := iterate_bounded (a.run N) (a.work N) ih s M N hs
    exact hh.mono (by change M + N * a.work N ≤ M + ((N + 1) * (a.work N + 1)); linarith)

/-- Only the maximum loop-nesting depth determines the number of counters. -/
def depth : Program K → ℕ
  | .push _ _ | .pop _ | .clear _ | .copy _ _ | .skip => 0
  | .branch _ a b c => max a.depth (max b.depth c.depth)
  | .seq a b => max a.depth b.depth
  | .repeat a => a.depth + 1


def compile : Program K → Block (K ⊕ ℕ)
  | .push k b => .push (.inl k) b
  | .pop k => .pop (.inl k)
  | .clear k => Block.clear (.inl k)
  | .copy i j => if i = j then .skip else Block.copy (.inl i) (.inl j) (.inr 1)
  | .skip => .skip
  | .branch k a b c => .branch (.inl k) a.compile b.compile c.compile
  | .seq a b => .seq a.compile b.compile
  | .repeat a => .seq (Block.copy (.inr 0) (.inr (a.depth + 2)) (.inr 1))
      (.loop (.inr (a.depth + 2)) (.seq (.pop (.inr (a.depth + 2))) a.compile))

/-- Unused higher counters may contain arbitrary data, for compositional use. -/
def Clean (d : ℕ) (z : Store ℕ) : Prop := z 1 = [] ∧ ∀ j < d, z (j + 2) = []

theorem Clean.mono {d e : ℕ} {z : Store ℕ} (hz : Clean e z) (h : d ≤ e) : Clean d z :=
  ⟨hz.1, fun j hj => hz.2 j (lt_of_lt_of_le hj h)⟩

theorem Clean.update_above {d e : ℕ} {z : Store ℕ} (hz : Clean d z) (h : d ≤ e)
    (w : List Bool) : Clean d (Function.update z (e + 2) w) := by
  constructor
  · simp [hz.1]
  · intro j hj
    rw [Function.update_of_ne (by omega)]
    exact hz.2 j hj

@[simp] theorem sum_update_left (s : Store K) (z : Store ℕ) (k : K) (w : List Bool) :
    Function.update (Sum.elim s z) (.inl k) w = Sum.elim (Function.update s k w) z := by
  funext j
  cases j with
  | inl j => by_cases h : j = k <;> simp [h]
  | inr j => simp

@[simp] theorem sum_update_right (s : Store K) (z : Store ℕ) (k : ℕ) (w : List Bool) :
    Function.update (Sum.elim s z) (.inr k) w = Sum.elim s (Function.update z k w) := by
  funext j
  cases j with
  | inl j => simp
  | inr j => by_cases h : j = k <;> simp [h]

end Program

end Superstring.BitCode

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.BitCode.Program

variable {K : Type} [DecidableEq K]

/-- Execute a reserved loop counter, with a uniform bound for each body call.
There is no test of an arbitrary predicate: only this counter is tested. -/
theorem counter_loop (b : Block (K ⊕ ℕ)) (f : Store K → Store K)
    (d N M C : ℕ)
    (hb : ∀ s z, Clean d z → (z 0).length = N → Bounded s M →
      ∃ n ≤ C, b.Exec (Sum.elim s z) (Sum.elim (f s) z) n)
    (s : Store K) (z : Store ℕ) (hz : Clean d z) (hN : (z 0).length = N)
    (hinv : ∀ i ≤ (z (d + 2)).length, Bounded (f^[i] s) M) :
    ∃ n ≤ (z (d + 2)).length * (C + 2) + 1,
      (Block.loop (.inr (d + 2)) (.seq (.pop (.inr (d + 2))) b)).Exec
        (Sum.elim s z)
        (Sum.elim (f^[(z (d + 2)).length] s) (Function.update z (d + 2) [])) n := by
  generalize he : z (d + 2) = w at *
  induction w generalizing s z with
  | nil =>
    have hu : Function.update z (d + 2) [] = z := by rw [← he, Function.update_eq_self]
    refine ⟨1, by simp, ?_⟩
    simpa only [List.length_nil, Function.iterate_zero, id_eq, hu] using
      (Block.Exec.loop_nil (a := Block.seq (.pop (.inr (d + 2))) b)
        (show (Sum.elim s z) (.inr (d + 2)) = [] from he))
  | cons x xs ih =>
    let z' := Function.update z (d + 2) xs
    have hz' : Clean d z' := hz.update_above le_rfl xs
    have hN' : (z' 0).length = N := by simpa only [z', Function.update_of_ne (show (0 : ℕ) ≠ d + 2 by omega)] using hN
    have hhead : Bounded s M := by simpa using hinv 0 (by omega)
    obtain ⟨n, hn, hh⟩ := hb s z' hz' hN' hhead
    have hpop : Block.Exec (.pop (.inr (d + 2))) (Sum.elim s z) (Sum.elim s z') 1 := by
      simpa only [Sum.elim_inr, he, List.tail_cons, sum_update_right, z'] using
        Block.Exec.pop (.inr (d + 2)) (Sum.elim s z)
    have htail : ∀ i ≤ xs.length, Bounded (f^[i] (f s)) M := by
      intro i hi
      rw [← Function.iterate_succ_apply]
      apply hinv
      simp only [List.length_cons]
      omega
    obtain ⟨m, hm, hrest⟩ := ih (f s) z' hz' hN' (Function.update_self _ _ _) htail
    have hresult := Block.Exec.loop_cons
      (show (Sum.elim s z) (.inr (d + 2)) ≠ [] by simp [he])
      (Block.Exec.seq hpop hh) hrest
    refine ⟨1 + n + m + 1, ?_, ?_⟩
    · simp only [List.length_cons]
      linarith
    · simpa only [z', Function.update_idem, List.length_cons, Function.iterate_succ_apply]
        using hresult

end Superstring.BitCode.Program

namespace Superstring.BitCode.Program

/-- Uniform bit clock; the polynomial work counts syntactic bounded iterations. -/
def clock (w N M : ℕ) : ℕ := 13 * w * (M + N + w + 1)

theorem clock_add (a b N M : ℕ) :
    clock a N M + clock b N (M + a) ≤ clock (a + b) N M := by
  dsimp only [clock]
  nlinarith

theorem clock_step {a b : ℕ} (h : a + 1 ≤ b) (N M : ℕ) :
    clock a N M + 1 ≤ clock b N M := by
  dsimp only [clock]
  linarith [Nat.mul_le_mul_right (M + N + a + 1) h,
    Nat.mul_le_mul_left b (show M + N + a + 1 ≤ M + N + b + 1 by omega)]

theorem clock_loop (w N M : ℕ) :
    9 * N + 3 + (N * (clock w N (M + N * w) + 2) + 1) ≤
      clock ((N + 1) * (w + 1)) N M := by
  let W := (N + 1) * (w + 1)
  let B := M + N + W + 1
  have hW : N * w + w ≤ W := by dsimp [W]; linarith
  have h₁ : clock w N (M + N * w) ≤ 13 * w * B := by
    apply Nat.mul_le_mul_left
    dsimp only [B]
    omega
  have h₂ : 11 * N + 4 ≤ 13 * (N + 1) * B := by
    have hB : 1 ≤ B := by dsimp [B]; omega
    linarith [Nat.mul_le_mul_left (13 * (N + 1)) hB]
  have h₃ : N * w + (N + 1) ≤ W := by dsimp [W]; linarith
  calc
    _ ≤ 9 * N + 3 + (N * (13 * w * B + 2) + 1) := by gcongr
    _ = 13 * (N * w) * B + (11 * N + 4) := by ring
    _ ≤ 13 * (N * w) * B + 13 * (N + 1) * B := Nat.add_le_add_left h₂ _
    _ = 13 * (N * w + (N + 1)) * B := by ring
    _ ≤ 13 * W * B := by gcongr

variable {K : Type} [DecidableEq K]

/-- Complete correctness and a polynomial bit-clock for bounded-loop programs. -/
theorem compile_exec (p : Program K) (N : ℕ) (s : Store K) (M : ℕ)
    (hs : Bounded s M) (z : Store ℕ) (hz : Clean p.depth z)
    (hN : (z 0).length = N) :
    ∃ n ≤ clock (p.work N) N M,
      p.compile.Exec (Sum.elim s z) (Sum.elim (p.run N s) z) n := by
  induction p generalizing s M z with
  | push k v =>
    refine ⟨1, by simp [work, clock]; omega, ?_⟩
    simpa only [compile, run, Sum.elim_inl, sum_update_left] using
      Block.Exec.push (.inl k) v (Sum.elim s z)
  | pop k =>
    refine ⟨1, by simp [work, clock]; omega, ?_⟩
    simpa only [compile, run, Sum.elim_inl, sum_update_left] using
      Block.Exec.pop (.inl k) (Sum.elim s z)
  | clear k =>
    refine ⟨2 * (s k).length + 1, ?_, ?_⟩
    · have := hs k
      simp only [work, clock]
      omega
    · simpa only [compile, run, Sum.elim_inl, sum_update_left] using
        Block.clear_exec (.inl k) (Sum.elim s z)
  | copy i j =>
    by_cases hij : i = j
    · subst j
      refine ⟨1, by simp [work, clock]; omega, ?_⟩
      simpa [compile, run] using
        Block.Exec.skip (Sum.elim s z)
    · refine ⟨2 * (s j).length + 9 * (s i).length + 3, ?_, ?_⟩
      · have := hs i
        have := hs j
        simp only [work, clock]
        omega
      · simpa only [compile, ite_eq_right hij, run, Sum.elim_inl, sum_update_left] using
          Block.copy_exec (Sum.inl i : K ⊕ ℕ) (.inl j) (.inr 1) (by simpa using hij)
            (by simp) (by simp) (Sum.elim s z) hz.1
  | skip =>
    exact ⟨1, by simp [work, clock]; omega, Block.Exec.skip _⟩
  | branch k a b c iha ihb ihc =>
    have ha := hz.mono (le_max_left _ _)
    have hb := hz.mono ((le_max_left _ _).trans (le_max_right _ _))
    have hc := hz.mono ((le_max_right _ _).trans (le_max_right _ _))
    cases hh : (s k).head? with
    | none =>
      obtain ⟨n, hn, hrun⟩ := iha s M hs z ha hN
      refine ⟨n + 1, (Nat.add_le_add_right hn 1).trans (clock_step (by dsimp [work]; omega) N M), ?_⟩
      simpa only [compile, run, hh] using Block.Exec.branch_none (k := Sum.inl k)
        (b := b.compile) (c := c.compile) hh hrun
    | some q => cases q with
      | false =>
        obtain ⟨n, hn, hrun⟩ := ihb s M hs z hb hN
        refine ⟨n + 1, (Nat.add_le_add_right hn 1).trans (clock_step (by dsimp [work]; omega) N M), ?_⟩
        simpa only [compile, run, hh] using Block.Exec.branch_false (k := Sum.inl k)
          (a := a.compile) (c := c.compile) hh hrun
      | true =>
        obtain ⟨n, hn, hrun⟩ := ihc s M hs z hc hN
        refine ⟨n + 1, (Nat.add_le_add_right hn 1).trans (clock_step (by dsimp [work]; omega) N M), ?_⟩
        simpa only [compile, run, hh] using Block.Exec.branch_true (k := Sum.inl k)
          (a := a.compile) (b := b.compile) hh hrun
  | seq a b iha ihb =>
    obtain ⟨n, hn, ha⟩ := iha s M hs z (hz.mono (le_max_left _ _)) hN
    obtain ⟨m, hm, hb⟩ := ihb (a.run N s) (M + a.work N) (a.run_bounded N s M hs)
      z (hz.mono (le_max_right _ _)) hN
    exact ⟨n + m, (Nat.add_le_add hn hm).trans (clock_add _ _ _ _), Block.Exec.seq ha hb⟩
  | «repeat» a ih =>
    let c := a.depth + 2
    let z' := Function.update z c (z 0)
    have hc : z c = [] := hz.2 a.depth (Nat.lt_succ_self _)
    have hcopy : (Block.copy (.inr 0) (.inr c) (.inr 1)).Exec
        (Sum.elim s z) (Sum.elim s z') (9 * N + 3) := by
      have hh := Block.copy_exec (Sum.inr 0 : K ⊕ ℕ) (.inr c) (.inr 1)
        (by simp [c]) (by simp) (by simp [c]) (Sum.elim s z) hz.1
      simpa only [Sum.elim_inr, hc, List.length_nil, hN, Nat.mul_zero, Nat.zero_add,
        sum_update_right, z'] using hh
    have hz' : Clean a.depth z' := (hz.mono (Nat.le_succ _)).update_above le_rfl _
    have hN' : (z' 0).length = N := by simp [z', c, hN]
    have hend : Function.update z' c [] = z := by
      rw [Function.update_idem, ← hc, Function.update_eq_self]
    have hInv : ∀ i ≤ (z' c).length, Bounded ((a.run N)^[i] s) (M + N * a.work N) := by
      intro i hi
      have hi' : i ≤ N := by simpa only [z', Function.update_self, hN] using hi
      exact (iterate_bounded (a.run N) (a.work N) (a.run_bounded N) s M i hs).mono
        (Nat.add_le_add_left (Nat.mul_le_mul_right _ hi') _)
    obtain ⟨n, hn, hloop⟩ := counter_loop a.compile (a.run N) a.depth N
      (M + N * a.work N) (clock (a.work N) N (M + N * a.work N))
      (fun s z hz hN hs => ih s _ hs z hz hN) s z' hz' hN' hInv
    simp only [z', c, Function.update_self, hN] at hn hloop
    rw [show Function.update (Function.update z c (z 0)) c [] = z from hend] at hloop
    refine ⟨9 * N + 3 + n, ?_, ?_⟩
    · exact (Nat.add_le_add_left hn _).trans (clock_loop (a.work N) N M)
    · exact Block.Exec.seq hcopy hloop

end Superstring.BitCode.Program

namespace Superstring.BitCode

variable {K : Type} [DecidableEq K]

theorem single_bounded (i : K) (w : List Bool) : Program.Bounded (single i w) w.length := by
  intro j
  by_cases hj : j = i <;> simp [single, hj]

namespace Block

/-- No syntax can modify a register it does not mention. -/
theorem Exec.frame {b : Block K} {s t : Store K} {n : ℕ} (h : b.Exec s t n)
    (k : K) (hk : k ∉ b.support) : t k = s k := by
  induction h with
  | push i v s => exact Function.update_of_ne (by simpa [support] using hk) _ _
  | pop i s => exact Function.update_of_ne (by simpa [support] using hk) _ _
  | skip => rfl
  | branch_none _ _ ih => exact ih (fun hh => hk (by simp [support, hh]))
  | branch_false _ _ ih => exact ih (fun hh => hk (by simp [support, hh]))
  | branch_true _ _ ih => exact ih (fun hh => hk (by simp [support, hh]))
  | seq _ _ ih₁ ih₂ =>
    exact (ih₂ (fun hh => hk (by simp [support, hh]))).trans
      (ih₁ (fun hh => hk (by simp [support, hh])))
  | loop_nil => rfl
  | loop_cons _ _ _ ih₁ ih₂ => exact (ih₂ hk).trans (ih₁ (fun hh => hk (by simp [support, hh])))

/-- The maximum stack length, unlike the total size, needs no finiteness of the
ambient register type. A finite code will subsequently be restricted to its support. -/
theorem Exec.bounded {b : Block K} {s t : Store K} {n : ℕ} (h : b.Exec s t n)
    (M : ℕ) (hs : Program.Bounded s M) : Program.Bounded t (M + n) := by
  induction h generalizing M with
  | push k v s =>
    exact (hs.mono (Nat.le_add_right M 1)).update k (v :: s k)
      (by simpa only [List.length_cons] using Nat.succ_le_succ (hs k))
  | pop k s =>
    exact (hs.mono (Nat.le_add_right M 1)).update k (s k).tail
      (by simp only [List.length_tail]; have := hs k; omega)
  | skip => exact hs.mono (by omega)
  | branch_none _ _ ih => exact (ih M hs).mono (by omega)
  | branch_false _ _ ih => exact (ih M hs).mono (by omega)
  | branch_true _ _ ih => exact (ih M hs).mono (by omega)
  | seq _ _ ih₁ ih₂ =>
    have hh := ih₂ _ (ih₁ M hs)
    simpa only [Nat.add_assoc] using hh
  | loop_nil => exact hs.mono (by omega)
  | loop_cons _ _ _ ih₁ ih₂ => exact (ih₂ _ (ih₁ M hs)).mono (by omega)

def clearMany : List K → Block K
  | [] => .skip
  | k :: ks => .seq (clear k) (clearMany ks)

def cleared (s : Store K) (l : List K) : Store K := fun k => if k ∈ l then [] else s k

theorem clearMany_exec (l : List K) (s : Store K) (M : ℕ) (hs : Program.Bounded s M) :
    ∃ n ≤ l.length * (2 * M + 1) + 1, (clearMany l).Exec s (cleared s l) n := by
  induction l generalizing s with
  | nil =>
    have he : cleared s [] = s := by funext k; simp [cleared]
    exact ⟨1, by simp, by simpa only [clearMany, he] using Exec.skip s⟩
  | cons k ks ih =>
    obtain ⟨n, hn, hh⟩ := ih (Function.update s k []) (hs.update k [] (by simp))
    have he : cleared (Function.update s k []) ks = cleared s (k :: ks) := by
      funext j
      by_cases hj : j = k <;> by_cases hmem : j ∈ ks <;> simp [cleared, hj, hmem]
    rw [he] at hh
    refine ⟨2 * (s k).length + 1 + n, ?_, Exec.seq (clear_exec k s) hh⟩
    simp only [List.length_cons]
    have := hs k
    linarith

/-- Restrict to the finitely many registers used by the actual finite code.
This proves that infinite ambient names are merely notation, not infinite memory
in the delivered machine. Every restricted alphabet is Bool. -/
theorem certificate_any {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (Φ : α → β) (b : Block K) (i o : K) (P : Polynomial ℕ)
    (correct : ∀ a, ∃ n ≤ P.eval (ea a).length,
      b.Exec (single i (ea a)) (single o (eb (Φ a))) n) :
    ∃ M : Turing.TM2ComputableInPolyTime ea eb Φ, ∀ k : M.tm.K, Finite (M.tm.Γ k) := by
  classical
  let U := insert i (insert o b.support)
  let R := ↥U
  let i' : R := ⟨i, by simp [U]⟩
  let o' : R := ⟨o, by simp [U]⟩
  let reg : K → R := fun k => if h : k ∈ U then ⟨k, h⟩ else i'
  let code := b.rename reg
  have hreg : ∀ k ∈ b.support, (reg k).val = k := by
    intro k hk
    simp only [reg, dite_eq_left (show k ∈ U by simp [U, hk])]
  have hi (w : List Bool) : single i w ∘ (Subtype.val : R → K) = single i' w := by
    funext j
    have he : j.val = i ↔ j = i' := by
      constructor
      · exact fun h => Subtype.ext h
      · exact fun h => congrArg Subtype.val h
    simp only [Function.comp_apply, single, he]
  have ho (w : List Bool) : single o w ∘ (Subtype.val : R → K) = single o' w := by
    funext j
    have he : j.val = o ↔ j = o' := by
      constructor
      · exact fun h => Subtype.ext h
      · exact fun h => congrArg Subtype.val h
    simp only [Function.comp_apply, single, he]
  have hcorrect : ∀ a, ∃ n ≤ P.eval (ea a).length,
      code.Exec (single i' (ea a)) (single o' (eb (Φ a))) n := by
    intro a
    obtain ⟨n, hn, hh⟩ := correct a
    refine ⟨n, hn, ?_⟩
    simpa only [hi, ho] using hh.pullback reg (Subtype.val : R → K) Subtype.val_injective hreg
  exact ⟨code.certificate ea eb Φ i' o' P hcorrect,
    code.certificate_finite ea eb Φ i' o' P hcorrect⟩

/-- Uniformly erase every used non-output stack. A proof of the observed output
and a polynomial clock suffice; hidden garbage is neither permitted nor assumed
away in the exact Mathlib final configuration. -/
theorem certificate_observed {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (Φ : α → β) (b : Block K) (i o : K) (P : Polynomial ℕ)
    (correct : ∀ a, ∃ n t, n ≤ P.eval (ea a).length ∧
      b.Exec (single i (ea a)) t n ∧ t o = eb (Φ a)) :
    ∃ M : Turing.TM2ComputableInPolyTime ea eb Φ, ∀ k : M.tm.K, Finite (M.tm.Γ k) := by
  classical
  let l := ((insert i b.support).erase o).toList
  let code := Block.seq b (clearMany l)
  let Q : Polynomial ℕ := P + Polynomial.C l.length * (2 * (Polynomial.X + P) + 1) + 1
  apply certificate_any ea eb Φ code i o Q
  intro a
  obtain ⟨n, t, hn, hrun, hout⟩ := correct a
  let N := (ea a).length
  have ht := (hrun.bounded N (single_bounded i (ea a))).mono (Nat.add_le_add_left hn N)
  obtain ⟨m, hm, hclear⟩ := clearMany_exec l t (N + P.eval N) ht
  have hfinal : cleared t l = single o (eb (Φ a)) := by
    funext k
    by_cases hko : k = o
    · subst k
      simp [cleared, l, single, hout]
    · by_cases hk : k ∈ l
      · simp [cleared, hk, single, hko]
      · have hnot : k ∉ insert i b.support := by
          intro hh
          apply hk
          simp only [l, Finset.mem_toList, Finset.mem_erase]
          exact ⟨hko, hh⟩
        have hi : k ≠ i := fun he => hnot (by simp [he])
        have hb : k ∉ b.support := fun he => hnot (Finset.mem_insert_of_mem he)
        have htk : t k = [] := by simpa only [single, ite_eq_right hi] using hrun.frame k hb
        simp only [cleared, ite_eq_right hk, single, ite_eq_right hko, htk]
  rw [hfinal] at hclear
  refine ⟨n + m, ?_, Exec.seq hrun hclear⟩
  simp only [Q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_X]
  exact (Nat.add_le_add hn hm).trans (by dsimp only [N]; omega)

end Block

end Superstring.BitCode

namespace Superstring.BitCode.Program

variable {K : Type} [DecidableEq K]

/-- A syntactically bounded-loop program gives a polynomial-time
certificate, including finite alphabets and erasure of temporary registers. -/
theorem certificate {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (f : α → β) (p : Program K) (i o : K)
    (correct : ∀ a, (p.run (ea a).length (single i (ea a))) o = eb (f a)) :
    ∃ M : Turing.TM2ComputableInPolyTime ea eb f, ∀ k : M.tm.K, Finite (M.tm.Γ k) := by
  let b : Block (K ⊕ ℕ) := .seq (Block.copy (.inl i) (.inr 0) (.inr 1)) p.compile
  let P : Polynomial ℕ := 9 * Polynomial.X + 3 +
    13 * p.polynomial * (Polynomial.X + Polynomial.X + p.polynomial + 1)
  apply Block.certificate_observed ea eb f b (.inl i) (.inl o) P
  intro a
  let w := ea a
  let N := w.length
  let s := single i w
  let z : Store ℕ := single 0 w
  have hinit : Function.update (single (Sum.inl i) w : Store (K ⊕ ℕ)) (.inr 0) w =
      Sum.elim s z := by
    funext k
    cases k with
    | inl k => simp [s, single]
    | inr k =>
      by_cases hk : k = 0 <;> simp [z, single, hk]
  have hcopy := Block.copy_exec (Sum.inl i : K ⊕ ℕ) (.inr 0) (.inr 1)
    Sum.inl_ne_inr Sum.inl_ne_inr (by simp) (single (.inl i) w)
    (by simp [single])
  have hin : (single (Sum.inl i) w : Store (K ⊕ ℕ)) (.inl i) = w := by simp [single]
  have hout : (single (Sum.inl i) w : Store (K ⊕ ℕ)) (.inr 0) = [] := by simp [single]
  rw [hin, hout] at hcopy
  simp only [List.length_nil, Nat.mul_zero, Nat.zero_add] at hcopy
  rw [hinit] at hcopy
  have hz : Clean p.depth z := by
    constructor
    · simp [z, single]
    · intro j _
      simp [z, single]
  have hN : (z 0).length = N := by simp [z, single, N]
  obtain ⟨n, hn, hh⟩ := p.compile_exec N s N (single_bounded i w) z hz hN
  refine ⟨9 * N + 3 + n, Sum.elim (p.run N s) z, ?_, Block.Exec.seq hcopy hh, ?_⟩
  · simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X, Polynomial.eval_one, eval_polynomial]
    exact Nat.add_le_add_left hn (9 * N + 3)
  · exact correct a

end Superstring.BitCode.Program

namespace Superstring.BitCode.Block

variable {K L : Type} [DecidableEq K] [DecidableEq L]

@[simp] theorem update_left (s : Store K) (r : Store L) (k : K) (w : List Bool) :
    Function.update (Sum.elim s r) (.inl k) w = Sum.elim (Function.update s k w) r := by
  funext j
  cases j with
  | inl j => by_cases hj : j = k <;> simp [hj]
  | inr j => simp

@[simp] theorem update_right (s : Store K) (r : Store L) (k : L) (w : List Bool) :
    Function.update (Sum.elim s r) (.inr k) w = Sum.elim s (Function.update r k w) := by
  funext j
  cases j with
  | inl j => simp
  | inr j => by_cases hj : j = k <;> simp [hj]

/-- Renaming into a disjoint register bank preserves a run and frames the
entire other bank, even when that other bank contains nonempty data. -/
theorem Exec.left {b : Block K} {s t : Store K} {n : ℕ} (h : b.Exec s t n)
    (r : Store L) : (b.rename Sum.inl).Exec (Sum.elim s r) (Sum.elim t r) n := by
  induction h with
  | push k x s =>
    simpa only [rename, Sum.elim_inl, update_left] using Exec.push (.inl k) x (Sum.elim s r)
  | pop k s =>
    simpa only [rename, Sum.elim_inl, update_left] using Exec.pop (.inl k) (Sum.elim s r)
  | skip => exact .skip _
  | branch_none hh _ ih => exact .branch_none hh ih
  | branch_false hh _ ih => exact .branch_false hh ih
  | branch_true hh _ ih => exact .branch_true hh ih
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | loop_nil hh => exact .loop_nil hh
  | loop_cons hh _ _ ih₁ ih₂ => exact .loop_cons hh ih₁ ih₂

theorem Exec.right {b : Block L} {s t : Store L} {n : ℕ} (h : b.Exec s t n)
    (r : Store K) : (b.rename Sum.inr).Exec (Sum.elim r s) (Sum.elim r t) n := by
  induction h with
  | push k x s =>
    simpa only [rename, Sum.elim_inr, update_right] using Exec.push (.inr k) x (Sum.elim r s)
  | pop k s =>
    simpa only [rename, Sum.elim_inr, update_right] using Exec.pop (.inr k) (Sum.elim r s)
  | skip => exact .skip _
  | branch_none hh _ ih => exact .branch_none hh ih
  | branch_false hh _ ih => exact .branch_false hh ih
  | branch_true hh _ ih => exact .branch_true hh ih
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | loop_nil hh => exact .loop_nil hh
  | loop_cons hh _ _ ih₁ ih₂ => exact .loop_cons hh ih₁ ih₂

end Superstring.BitCode.Block

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.BitCode

/-- Actual code and a clock, not an oracle or a premise of the main_oai theorem.
Ambient register types may be infinite names; certificate_any restricts them
exactly to finite support. All executions start and end with the single encoded
input/output stack. -/
def RunsInPolyTime {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (f : α → β) : Prop :=
  ∃ (K : Type) (_ : DecidableEq K) (i o : K) (b : Block K) (P : Polynomial ℕ),
    ∀ a, ∃ n ≤ P.eval (ea a).length,
      b.Exec (single i (ea a)) (single o (eb (f a))) n

namespace RunsInPolyTime

variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
  {f : α → β} {g : β → γ}

theorem certificate (h : RunsInPolyTime ea eb f) :
    ∃ M : Turing.TM2ComputableInPolyTime ea eb f, ∀ k : M.tm.K, Finite (M.tm.Γ k) := by
  obtain ⟨K, inst, i, o, b, P, hb⟩ := h
  exact b.certificate_any ea eb f i o P hb

theorem output_length (h : RunsInPolyTime ea eb f) :
    ∃ P : Polynomial ℕ, ∀ a, (eb (f a)).length ≤ P.eval (ea a).length := by
  obtain ⟨K, inst, i, o, b, P, hb⟩ := h
  refine ⟨Polynomial.X + P, ?_⟩
  intro a
  obtain ⟨n, hn, hh⟩ := hb a
  have hl := hh.bounded _ (single_bounded i (ea a)) o
  simp only [single, ↓reduceIte] at hl
  simpa only [Polynomial.eval_add, Polynomial.eval_X] using hl.trans (Nat.add_le_add_left hn _)

theorem id (e : α → List Bool) : RunsInPolyTime e e id := by
  refine ⟨Unit, inferInstance, (), (), .skip, 1, ?_⟩
  intro a
  exact ⟨1, by simp, Block.Exec.skip _⟩

end RunsInPolyTime

end Superstring.BitCode

namespace Superstring.BitCode

variable {K L : Type} [DecidableEq K] [DecidableEq L]

@[simp] theorem single_left (i : K) (w : List Bool) :
    Sum.elim (single i w) (fun _ : L => []) = single (Sum.inl i) w := by
  funext k
  cases k with
  | inl k => simp [single]
  | inr k => simp [single]

@[simp] theorem single_right (i : L) (w : List Bool) :
    Sum.elim (fun _ : K => []) (single i w) = single (Sum.inr i) w := by
  funext k
  cases k with
  | inl k => simp [single]
  | inr k => simp [single]

namespace Block

theorem transfer_single (i j : K) (hij : i ≠ j) (w : List Bool) :
    (transfer i j).Exec (single i w) (single j w.reverse) (4 * w.length + 1) := by
  have hh := transfer_exec i j hij (single i w)
  have hi : single i w i = w := by simp [single]
  have hj : single i w j = [] := by simp [single, hij.symm]
  rw [hi, hj, List.append_nil] at hh
  have he : Function.update (Function.update (single i w) i []) j w.reverse = single j w.reverse := by
    funext k
    by_cases hk : k = j
    · subst k; simp [single]
    · by_cases hki : k = i
      · subst k; simp [single, hij]
      · simp [single, hk, hki]
  rw [he] at hh
  exact hh

/-- Relocate a single encoded value without reversing its bit order. -/
def move (i j scratch : K) : Block K := .seq (transfer i scratch) (transfer scratch j)

theorem move_single (i j scratch : K) (hi : i ≠ scratch) (hj : j ≠ scratch)
    (w : List Bool) : (move i j scratch).Exec (single i w) (single j w) (8 * w.length + 2) := by
  have hh := Exec.seq (transfer_single i scratch hi w) (transfer_single scratch j hj.symm w.reverse)
  simp only [List.reverse_reverse, List.length_reverse] at hh
  convert hh using 1 <;> first | rfl | omega


end Block

omit [DecidableEq K] [DecidableEq L] in
theorem eval_mono_nat (P : Polynomial ℕ) : Monotone P.eval := by
  intro n m h
  induction P using Polynomial.induction_on' with
  | add P Q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial k c => simp only [Polynomial.eval_monomial]; gcongr

namespace RunsInPolyTime

variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
  {f : α → β} {g : β → γ}

/-- Composition of finite bit programs preserves polynomial-time computability. -/
theorem comp (hg : RunsInPolyTime eb ec g) (hf : RunsInPolyTime ea eb f) :
    RunsInPolyTime ea ec (g ∘ f) := by
  obtain ⟨K, instK, i, o, b, P, hb⟩ := hf
  obtain ⟨L, instL, j, v, c, Q, hc⟩ := hg
  let code : Block ((K ⊕ L) ⊕ Unit) :=
    .seq ((b.rename Sum.inl).rename Sum.inl)
      (.seq (Block.move (.inl (.inl o)) (.inl (.inr j)) (.inr ()))
        ((c.rename Sum.inr).rename Sum.inl))
  let R : Polynomial ℕ := P + (8 * (Polynomial.X + P) + 2) + Q.comp (Polynomial.X + P)
  refine ⟨(K ⊕ L) ⊕ Unit, inferInstance, .inl (.inl i), .inl (.inr v), code, R, ?_⟩
  intro a
  obtain ⟨n, hn, hf⟩ := hb a
  obtain ⟨m, hm, hg⟩ := hc (f a)
  have hl := hf.bounded _ (single_bounded i (ea a)) o
  simp only [single, ↓reduceIte] at hl
  have hout : (eb (f a)).length ≤ (ea a).length + P.eval (ea a).length :=
    hl.trans (Nat.add_le_add_left hn _)
  have hfirst := (hf.left (fun _ : L => [])).left (fun _ : Unit => [])
  have hlast := (hg.right (fun _ : K => [])).left (fun _ : Unit => [])
  simp only [single_left, single_right] at hfirst hlast
  have hmove := Block.move_single (Sum.inl (Sum.inl o) : (K ⊕ L) ⊕ Unit)
    (.inl (.inr j)) (.inr ()) Sum.inl_ne_inr Sum.inl_ne_inr (eb (f a))
  refine ⟨n + ((8 * (eb (f a)).length + 2) + m), ?_,
    Block.Exec.seq hfirst (Block.Exec.seq hmove hlast)⟩
  simp only [R, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, Polynomial.eval_comp]
  have hm' := hm.trans (eval_mono_nat Q hout)
  linarith

end RunsInPolyTime

end Superstring.BitCode

namespace Superstring.BitCode.RunsInPolyTime

variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}

/-- Turn an observed-output proof into clean composable code. No garbage is
silently ignored, and every extra clearing step is paid for. -/
theorem of_observed {K : Type} [DecidableEq K] (b : Block K) (i o : K)
    (P : Polynomial ℕ)
    (correct : ∀ a, ∃ n t, n ≤ P.eval (ea a).length ∧
      b.Exec (single i (ea a)) t n ∧ t o = eb (f a)) : RunsInPolyTime ea eb f := by
  classical
  let l := ((insert i b.support).erase o).toList
  let code := Block.seq b (Block.clearMany l)
  let Q : Polynomial ℕ := P + Polynomial.C l.length * (2 * (Polynomial.X + P) + 1) + 1
  refine ⟨K, inferInstance, i, o, code, Q, ?_⟩
  intro a
  obtain ⟨n, t, hn, hrun, hout⟩ := correct a
  let N := (ea a).length
  have ht := (hrun.bounded N (single_bounded i (ea a))).mono (Nat.add_le_add_left hn N)
  obtain ⟨m, hm, hclear⟩ := Block.clearMany_exec l t (N + P.eval N) ht
  have hfinal : Block.cleared t l = single o (eb (f a)) := by
    funext k
    by_cases hko : k = o
    · subst k
      simp [Block.cleared, l, single, hout]
    · by_cases hk : k ∈ l
      · simp [Block.cleared, hk, single, hko]
      · have hnot : k ∉ insert i b.support := by
          intro hh
          apply hk
          simp only [l, Finset.mem_toList, Finset.mem_erase]
          exact ⟨hko, hh⟩
        have hi : k ≠ i := fun he => hnot (by simp [he])
        have hb : k ∉ b.support := fun he => hnot (Finset.mem_insert_of_mem he)
        have htk : t k = [] := by simpa only [single, ite_eq_right hi] using hrun.frame k hb
        simp only [Block.cleared, ite_eq_right hk, single, ite_eq_right hko, htk]
  rw [hfinal] at hclear
  refine ⟨n + m, ?_, Block.Exec.seq hrun hclear⟩
  simp only [Q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_X]
  exact (Nat.add_le_add hn hm).trans (by dsimp only [N]; omega)

theorem of_program {K : Type} [DecidableEq K] (p : Program K) (i o : K)
    (correct : ∀ a, (p.run (ea a).length (single i (ea a))) o = eb (f a)) :
    RunsInPolyTime ea eb f := by
  let b : Block (K ⊕ ℕ) := .seq (Block.copy (.inl i) (.inr 0) (.inr 1)) p.compile
  let P : Polynomial ℕ := 9 * Polynomial.X + 3 +
    13 * p.polynomial * (Polynomial.X + Polynomial.X + p.polynomial + 1)
  apply of_observed b (.inl i) (.inl o) P
  intro a
  let w := ea a
  let N := w.length
  let s := single i w
  let z : Store ℕ := single 0 w
  have hinit : Function.update (single (Sum.inl i) w : Store (K ⊕ ℕ)) (.inr 0) w =
      Sum.elim s z := by
    funext k
    cases k with
    | inl k => simp [s, single]
    | inr k => by_cases hk : k = 0 <;> simp [z, single, hk]
  have hcopy := Block.copy_exec (Sum.inl i : K ⊕ ℕ) (.inr 0) (.inr 1)
    Sum.inl_ne_inr Sum.inl_ne_inr (by simp) (single (.inl i) w)
    (by simp [single])
  have hin : (single (Sum.inl i) w : Store (K ⊕ ℕ)) (.inl i) = w := by simp [single]
  have hout : (single (Sum.inl i) w : Store (K ⊕ ℕ)) (.inr 0) = [] := by simp [single]
  rw [hin, hout] at hcopy
  simp only [List.length_nil, Nat.mul_zero, Nat.zero_add] at hcopy
  rw [hinit] at hcopy
  have hz : Program.Clean p.depth z := by
    constructor
    · simp [z, single]
    · intro j _; simp [z, single]
  have hN : (z 0).length = N := by simp [z, single, N]
  obtain ⟨n, hn, hh⟩ := p.compile_exec N s N (single_bounded i w) z hz hN
  refine ⟨9 * N + 3 + n, Sum.elim (p.run N s) z, ?_, Block.Exec.seq hcopy hh, ?_⟩
  · simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X, Polynomial.eval_one, Program.eval_polynomial]
    exact Nat.add_le_add_left hn (9 * N + 3)
  · exact correct a

end Superstring.BitCode.RunsInPolyTime

namespace Superstring.BitCode.Block

variable {K L : Type} [DecidableEq K] [DecidableEq L]

/-- Embed a program into any injectively named register bank. Its entire
complement is framed. This also permits distinct routines to share designated
input/output registers while having disjoint private work registers. -/
theorem Exec.embed {b : Block K} {s t : Store K} {n : ℕ} (h : b.Exec s t n)
    (f : K → L) (hf : Function.Injective f) (S : Store L)
    (hs : ∀ k, S (f k) = s k) :
    ∃ T, (b.rename f).Exec S T n ∧ (∀ k, T (f k) = t k) ∧
      ∀ j, (∀ k, f k ≠ j) → T j = S j := by
  induction h generalizing S with
  | push k x s =>
    refine ⟨Function.update S (f k) (x :: S (f k)), Exec.push _ _ _, ?_, ?_⟩
    · intro j
      by_cases hj : j = k
      · subst j; simp [hs]
      · have hh : f j ≠ f k := fun he => hj (hf he)
        simp [hj, hh, hs]
    · intro j hj
      exact Function.update_of_ne (Ne.symm (hj k)) _ _
  | pop k s =>
    refine ⟨Function.update S (f k) (S (f k)).tail, Exec.pop _ _, ?_, ?_⟩
    · intro j
      by_cases hj : j = k
      · subst j; simp [hs]
      · have hh : f j ≠ f k := fun he => hj (hf he)
        simp [hj, hh, hs]
    · intro j hj
      exact Function.update_of_ne (Ne.symm (hj k)) _ _
  | skip => exact ⟨S, Exec.skip S, hs, fun _ _ => rfl⟩
  | branch_none he _ ih =>
    obtain ⟨T, ht, hT, hframe⟩ := ih S hs
    exact ⟨T, Exec.branch_none (by rwa [hs]) ht, hT, hframe⟩
  | branch_false he _ ih =>
    obtain ⟨T, ht, hT, hframe⟩ := ih S hs
    exact ⟨T, Exec.branch_false (by rwa [hs]) ht, hT, hframe⟩
  | branch_true he _ ih =>
    obtain ⟨T, ht, hT, hframe⟩ := ih S hs
    exact ⟨T, Exec.branch_true (by rwa [hs]) ht, hT, hframe⟩
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨T, ht, hT, htframe⟩ := ih₁ S hs
    obtain ⟨U, hu, hU, huframe⟩ := ih₂ T hT
    exact ⟨U, Exec.seq ht hu, hU, fun j hj => (huframe j hj).trans (htframe j hj)⟩
  | loop_nil he => exact ⟨S, Exec.loop_nil (by rwa [hs]), hs, fun _ _ => rfl⟩
  | loop_cons he _ _ ih₁ ih₂ =>
    obtain ⟨T, ht, hT, htframe⟩ := ih₁ S hs
    obtain ⟨U, hu, hU, huframe⟩ := ih₂ T hT
    exact ⟨U, Exec.loop_cons (by rwa [hs]) ht hu, hU,
      fun j hj => (huframe j hj).trans (htframe j hj)⟩

/-- The convenient exact-final-state form of framed register embedding. -/
theorem Exec.transport {b : Block K} {s t : Store K} {n : ℕ} (h : b.Exec s t n)
    (f : K → L) (hf : Function.Injective f) (S T : Store L)
    (hs : ∀ k, S (f k) = s k) (ht : ∀ k, T (f k) = t k)
    (hframe : ∀ j, (∀ k, f k ≠ j) → T j = S j) :
    (b.rename f).Exec S T n := by
  obtain ⟨U, hu, hU, huframe⟩ := h.embed f hf S hs
  have he : U = T := by
    funext j
    by_cases hj : ∃ k, f k = j
    · obtain ⟨k, rfl⟩ := hj
      exact (hU k).trans (ht k).symm
    · have hj' : ∀ k, f k ≠ j := by simpa only [not_exists] using hj
      exact (huframe j hj').trans (hframe j hj').symm
  rwa [he] at hu

end Superstring.BitCode.Block

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.BitCode

/-- A pair of public bit-stack ports and a private register bank. -/
abbrev Ports (K : Type) := Bool ⊕ K

def inputPort {K : Type} : Ports K := .inl false
def outputPort {K : Type} : Ports K := .inl true

def portStore {K : Type} (x y : List Bool) (z : Store K) : Store (Ports K) :=
  Sum.elim (fun b => if b then y else x) z

def pairStore {K : Type} (x y : List Bool) : Store (Ports K) := portStore x y (fun _ => [])

@[simp] theorem portStore_input {K : Type} (x y : List Bool) (z : Store K) :
    portStore x y z inputPort = x := rfl
@[simp] theorem portStore_output {K : Type} (x y : List Bool) (z : Store K) :
    portStore x y z outputPort = y := rfl
@[simp] theorem portStore_private {K : Type} (x y : List Bool) (z : Store K) (k : K) :
    portStore x y z (.inr k) = z k := rfl

@[simp] theorem update_input {K : Type} [DecidableEq K] (x y w : List Bool) (z : Store K) :
    Function.update (portStore x y z) inputPort w = portStore w y z := by
  funext k
  cases k with
  | inl b => cases b <;> simp [inputPort, portStore]
  | inr k => simp [inputPort, portStore]

@[simp] theorem update_output {K : Type} [DecidableEq K] (x y w : List Bool) (z : Store K) :
    Function.update (portStore x y z) outputPort w = portStore x w z := by
  funext k
  cases k with
  | inl b => cases b <;> simp [outputPort, portStore]
  | inr k => simp [outputPort, portStore]

@[simp] theorem update_private {K : Type} [DecidableEq K] (x y w : List Bool) (z : Store K) (j : K) :
    Function.update (portStore x y z) (.inr j) w = portStore x y (Function.update z j w) :=
  Block.update_right _ _ _ _

namespace Block

/-- Move exactly one bit, leaving the suffix and the old output accumulator in
place. Empty input is a no-op, but valid parser calls always supply the bit. -/
def readBit {K : Type} (i o : K) : Block K := .branch i .skip
  (.seq (.pop i) (.push o false)) (.seq (.pop i) (.push o true))

theorem readBit_exec {K : Type} [DecidableEq K] (x : Bool) (xs ys : List Bool)
    (z : Store K) :
    (readBit inputPort outputPort).Exec (portStore (x :: xs) ys z)
      (portStore xs (x :: ys) z) 3 := by
  have hpop : Exec (.pop inputPort) (portStore (x :: xs) ys z) (portStore xs ys z) 1 := by
    simpa only [portStore_input, List.tail_cons, update_input] using
      Exec.pop inputPort (portStore (x :: xs) ys z)
  have hpush : Exec (.push outputPort x) (portStore xs ys z) (portStore xs (x :: ys) z) 1 := by
    simpa only [portStore_output, update_output] using Exec.push outputPort x (portStore xs ys z)
  cases x with
  | false => exact .branch_false rfl (.seq hpop hpush)
  | true => exact .branch_true rfl (.seq hpop hpush)

/-- Lift a two-port clean routine while leaving an arbitrary disjoint private
bank untouched. Public input/output ports are deliberately shared. -/
theorem Exec.ports {K L : Type} [DecidableEq K] [DecidableEq L]
    {b : Block (Ports K)} {x y x' y' : List Bool} {n : ℕ}
    (h : b.Exec (pairStore x y) (pairStore x' y') n)
    (f : K → L) (hf : Function.Injective f) (z : Store L) (hz : ∀ k, z (f k) = []) :
    (b.rename (Sum.map id f)).Exec (portStore x y z) (portStore x' y' z) n := by
  apply h.transport (Sum.map id f) (Sum.map_injective.mpr ⟨Function.injective_id, hf⟩)
  · intro k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => exact hz k
  · intro k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => exact hz k
  · intro k hk
    cases k with
    | inl k => exact False.elim (hk (.inl k) rfl)
    | inr k => rfl

end Block

/-- A linear-time prefix scanner for an explicit encoding. It consumes exactly
one encoded value, pushes its reversal onto an accumulator, and restores every
private stack to empty, independently of the untouched input suffix. -/
def Parses {α : Type} (e : α → List Bool) : Prop :=
  ∃ (K : Type) (_ : DecidableEq K) (b : Block (Ports K)) (c : ℕ),
    ∀ a tail acc, ∃ n ≤ c * ((e a).length + 1),
      b.Exec (pairStore (e a ++ tail) acc) (pairStore tail ((e a).reverse ++ acc)) n

namespace Parses

theorem bit : Parses (fun b : Bool => [b]) := by
  refine ⟨Unit, inferInstance, Block.readBit inputPort outputPort, 3, ?_⟩
  intro b tail acc
  refine ⟨3, by simp, ?_⟩
  simpa only [List.singleton_append, List.reverse_singleton, pairStore] using
    Block.readBit_exec b tail acc (fun _ : Unit => [])

/-- A fixed code word is a prefix encoding of a unit value. -/
theorem const (w : List Bool) : Parses (fun _ : Unit => w) := by
  induction w with
  | nil =>
    refine ⟨Unit, inferInstance, .skip, 1, ?_⟩
    intro a tail acc
    exact ⟨1, by simp, by simpa only [List.nil_append, List.reverse_nil] using Block.Exec.skip (pairStore tail acc)⟩
  | cons x xs ih =>
    obtain ⟨K, inst, b, c, hb⟩ := ih
    refine ⟨K, inst, .seq (Block.readBit inputPort outputPort) b, c + 3, ?_⟩
    intro a tail acc
    obtain ⟨n, hn, hh⟩ := hb a tail (x :: acc)
    refine ⟨3 + n, ?_, ?_⟩
    · simp only [List.length_cons]
      linarith
    · simpa only [List.cons_append, List.reverse_cons, List.append_assoc, List.singleton_append,
        List.nil_append, pairStore] using
        Block.Exec.seq (Block.readBit_exec x (xs ++ tail) acc (fun _ : K => [])) hh

/-- Consecutive self-delimiting values can be parsed in succession without
scanning or copying the remaining suffix. -/
theorem prod {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    (ha : Parses ea) (hb : Parses eb) : Parses (fun p : α × β => ea p.1 ++ eb p.2) := by
  obtain ⟨K, instK, b, c, hparse⟩ := ha
  obtain ⟨L, instL, d, e, hd⟩ := hb
  let code : Block (Ports (K ⊕ L)) := .seq (b.rename (Sum.map id Sum.inl))
    (d.rename (Sum.map id Sum.inr))
  refine ⟨K ⊕ L, inferInstance, code, c + e, ?_⟩
  intro p tail acc
  obtain ⟨n, hn, h₁⟩ := hparse p.1 (eb p.2 ++ tail) acc
  obtain ⟨m, hm, h₂⟩ := hd p.2 tail ((ea p.1).reverse ++ acc)
  have h₁' := h₁.ports (Sum.inl : K → K ⊕ L) Sum.inl_injective (fun _ => []) (fun _ => rfl)
  have h₂' := h₂.ports (Sum.inr : L → K ⊕ L) Sum.inr_injective (fun _ => []) (fun _ => rfl)
  refine ⟨n + m, ?_, ?_⟩
  · simp only [List.length_append]
    nlinarith
  · simpa only [List.append_assoc, List.reverse_append, pairStore, code] using Block.Exec.seq h₁' h₂'

end Parses

end Superstring.BitCode

namespace Superstring.BitCode


def listCode {α : Type} (e : α → List Bool) : List α → List Bool
  | [] => [true]
  | x :: xs => false :: (e x ++ listCode e xs)

namespace Parses

/-- Lists of a linearly parsable self-delimiting type are themselves linearly
parsable. Exactly one fixed-size private flag is added, not an infinite alphabet
or uncharged whole-value operation. -/
theorem list {α : Type} {e : α → List Bool} (hp : Parses e) : Parses (listCode e) := by
  obtain ⟨K, instK, b, c, hb⟩ := hp
  let flag : Ports (K ⊕ Unit) := .inr (.inr ())
  let z : Store (K ⊕ Unit) := single (.inr ()) [true]
  let inner : Block (Ports (K ⊕ Unit)) := b.rename (Sum.map id Sum.inl)
  let step : Block (Ports (K ⊕ Unit)) := .branch inputPort
    (.pop flag)
    (.seq (Block.readBit inputPort outputPort) inner)
    (.seq (Block.readBit inputPort outputPort) (.pop flag))
  let loop : Block (Ports (K ⊕ Unit)) := .loop flag step
  let code : Block (Ports (K ⊕ Unit)) := .seq (.push flag true) loop
  have hz : z (.inr ()) = [true] := by simp [z, single]
  have hzleft : ∀ k : K, z (.inl k) = [] := by intro k; simp [z, single]
  have hzend : Function.update z (.inr ()) [] = fun _ => [] := by
    funext k
    by_cases hk : k = Sum.inr () <;> simp [z, single, hk]
  have hloop (xs : List α) (tail acc : List Bool) :
      ∃ n ≤ (c + 7) * (listCode e xs).length,
        loop.Exec (portStore (listCode e xs ++ tail) acc z)
          (pairStore tail ((listCode e xs).reverse ++ acc)) n := by
    induction xs generalizing acc with
    | nil =>
      have hread := Block.readBit_exec true tail acc z
      have hpop : Block.Exec (.pop flag) (portStore tail (true :: acc) z)
          (pairStore tail (true :: acc)) 1 := by
        simpa only [flag, portStore_private, hz, List.tail_cons, update_private,
          hzend, pairStore] using Block.Exec.pop flag (portStore tail (true :: acc) z)
      have hbody : step.Exec (portStore (true :: tail) acc z)
          (pairStore tail (true :: acc)) (3 + 1 + 1) :=
        Block.Exec.branch_true rfl (Block.Exec.seq hread hpop)
      have hend : loop.Exec (pairStore tail (true :: acc)) (pairStore tail (true :: acc)) 1 :=
        Block.Exec.loop_nil rfl
      have hh := Block.Exec.loop_cons (by simp [flag, hz]) hbody hend
      refine ⟨7, ?_, ?_⟩
      · simp [listCode]
      · simpa only [listCode, List.singleton_append, List.reverse_singleton] using hh
    | cons x xs ih =>
      obtain ⟨n, hn, hinner⟩ := hb x (listCode e xs ++ tail) (false :: acc)
      have hin := hinner.ports (Sum.inl : K → K ⊕ Unit) Sum.inl_injective z hzleft
      obtain ⟨m, hm, hrest⟩ := ih ((e x).reverse ++ false :: acc)
      have hread := Block.readBit_exec false (e x ++ (listCode e xs ++ tail)) acc z
      have hbody : step.Exec (portStore (false :: (e x ++ (listCode e xs ++ tail))) acc z)
          (portStore (listCode e xs ++ tail) ((e x).reverse ++ false :: acc) z) (3 + n + 1) :=
        Block.Exec.branch_false rfl (Block.Exec.seq hread hin)
      have hh := Block.Exec.loop_cons (by simp [flag, hz]) hbody hrest
      refine ⟨3 + n + 1 + m + 1, ?_, ?_⟩
      · simp only [listCode, List.length_cons, List.length_append]
        linarith
      · simpa only [listCode, List.cons_append, List.append_assoc, List.reverse_cons,
          List.reverse_append, List.singleton_append, List.nil_append] using hh
  refine ⟨K ⊕ Unit, inferInstance, code, c + 8, ?_⟩
  intro xs tail acc
  obtain ⟨n, hn, hh⟩ := hloop xs tail acc
  have hstart : Block.Exec (.push flag true) (pairStore (listCode e xs ++ tail) acc)
      (portStore (listCode e xs ++ tail) acc z) 1 := by
    have he : Function.update (fun _ : K ⊕ Unit => ([] : List Bool)) (.inr ()) [true] = z := by
      funext k
      by_cases hk : k = Sum.inr () <;> simp [z, single, hk]
    simpa only [pairStore, flag, portStore_private, update_private, he] using
      Block.Exec.push flag true (pairStore (listCode e xs ++ tail) acc)
  refine ⟨1 + n, ?_, Block.Exec.seq hstart hh⟩
  linarith

end Parses

end Superstring.BitCode

namespace Superstring.BitCode

@[simp] theorem pairStore_input {K : Type} [DecidableEq K] (w : List Bool) :
    (pairStore w [] : Store (Ports K)) = single inputPort w := by
  funext k
  cases k with
  | inl b => cases b <;> simp [pairStore, portStore, single, inputPort]
  | inr k => simp [pairStore, portStore, single, inputPort]

@[simp] theorem pairStore_output {K : Type} [DecidableEq K] (w : List Bool) :
    (pairStore [] w : Store (Ports K)) = single outputPort w := by
  funext k
  cases k with
  | inl b => cases b <;> simp [pairStore, portStore, single, outputPort]
  | inr k => simp [pairStore, portStore, single, outputPort]

namespace Block

/-- Write a fixed finite bit word, in the correct order. -/
def pushWord {K : Type} (i : K) : List Bool → Block K
  | [] => .skip
  | b :: bs => .seq (pushWord i bs) (.push i b)

theorem pushWord_exec {K : Type} [DecidableEq K] (i : K) (w : List Bool) (s : Store K) :
    (pushWord i w).Exec s (Function.update s i (w ++ s i)) (w.length + 1) := by
  induction w with
  | nil => simpa only [pushWord, List.nil_append, List.length_nil, Function.update_eq_self] using Exec.skip s
  | cons x xs ih =>
    have hh := Exec.seq ih (Exec.push i x (Function.update s i (xs ++ s i)))
    simpa only [Function.update_self, Function.update_idem, List.cons_append,
      pushWord, List.length_cons, Nat.add_assoc] using hh

end Block

namespace RunsInPolyTime

theorem const {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (b : β) :
    RunsInPolyTime ea eb (fun _ => b) := by
  let code : Block Unit := .seq (Block.clear ()) (Block.pushWord () (eb b))
  refine ⟨Unit, inferInstance, (), (), code,
    2 * Polynomial.X + Polynomial.C ((eb b).length + 2), ?_⟩
  intro a
  have h₁ := Block.clear_exec () (single () (ea a))
  have h₂ := Block.pushWord_exec () (eb b) (Function.update (single () (ea a)) () [])
  have he : Function.update (Function.update (single () (ea a)) () []) () (eb b) =
      single () (eb b) := by funext k; cases k; simp [single]
  simp only [Function.update_self, List.append_nil] at h₂
  rw [he] at h₂
  have hh := Block.Exec.seq h₁ h₂
  have hlen : (single () (ea a) ()).length = (ea a).length := by simp [single]
  rw [hlen] at hh
  refine ⟨2 * (ea a).length + 1 + ((eb b).length + 1), ?_, hh⟩
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, Polynomial.eval_C]
  omega

theorem reverseEncoding {α : Type} (e : α → List Bool) :
    RunsInPolyTime (fun a => (e a).reverse) e _root_.id := by
  refine ⟨Bool, inferInstance, false, true, Block.transfer false true,
    4 * Polynomial.X + 1, ?_⟩
  intro a
  refine ⟨4 * (e a).length + 1, by simp, ?_⟩
  simpa only [List.length_reverse, List.reverse_reverse, _root_.id] using
    Block.transfer_single false true Bool.false_ne_true (e a).reverse

/-- First projection from two consecutive self-delimiting values. -/
theorem fst {α β : Type} {ea : α → List Bool} (eb : β → List Bool) (hp : Parses ea) :
    RunsInPolyTime (fun p : α × β => ea p.1 ++ eb p.2) ea Prod.fst := by
  obtain ⟨K, inst, b, c, hb⟩ := hp
  have hrev : RunsInPolyTime (fun p : α × β => ea p.1 ++ eb p.2)
      (fun a => (ea a).reverse) Prod.fst := by
    apply of_observed b inputPort outputPort (Polynomial.C c * (Polynomial.X + 1))
    intro p
    obtain ⟨n, hn, hh⟩ := hb p.1 (eb p.2) []
    simp only [pairStore_input, List.append_nil] at hh
    refine ⟨n, pairStore (eb p.2) (ea p.1).reverse, ?_, hh, rfl⟩
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one, List.length_append]
    exact hn.trans (Nat.mul_le_mul_left _ (by omega))
  exact (reverseEncoding ea).comp hrev

/-- Second projection consumes just the first value; it does not copy or
re-parse the tail. Accumulated garbage is explicitly erased by of_observed. -/
theorem snd {α β : Type} {ea : α → List Bool} (eb : β → List Bool) (hp : Parses ea) :
    RunsInPolyTime (fun p : α × β => ea p.1 ++ eb p.2) eb Prod.snd := by
  obtain ⟨K, inst, b, c, hb⟩ := hp
  apply of_observed b inputPort inputPort (Polynomial.C c * (Polynomial.X + 1))
  intro p
  obtain ⟨n, hn, hh⟩ := hb p.1 (eb p.2) []
  simp only [pairStore_input, List.append_nil] at hh
  refine ⟨n, pairStore (eb p.2) (ea p.1).reverse, ?_, hh, rfl⟩
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, List.length_append]
  exact hn.trans (Nat.mul_le_mul_left _ (by omega))

theorem cons {α : Type} (e : α → List Bool) :
    RunsInPolyTime (fun p : α × List α => e p.1 ++ listCode e p.2)
      (listCode e) (fun p => p.1 :: p.2) := by
  refine ⟨Unit, inferInstance, (), (), .push () false, 1, ?_⟩
  intro p
  refine ⟨1, by simp, ?_⟩
  have he : Function.update (single () (e p.1 ++ listCode e p.2)) ()
      (false :: (e p.1 ++ listCode e p.2)) = single () (listCode e (p.1 :: p.2)) := by
    funext k; cases k; simp [single, listCode]
  simpa only [single, ↓reduceIte, he] using
    Block.Exec.push () false (single () (e p.1 ++ listCode e p.2))

end RunsInPolyTime

end Superstring.BitCode

namespace Superstring.BitCode.Block

variable {K : Type} [DecidableEq K]

/-- Destructive linear concatenation, preserving every unrelated register. -/
theorem move_exec (i j scratch : K) (hij : i ≠ j) (hit : i ≠ scratch) (hjt : j ≠ scratch)
    (s : Store K) (ht : s scratch = []) :
    (move i j scratch).Exec s
      (Function.update (Function.update s i []) j (s i ++ s j)) (8 * (s i).length + 2) := by
  let t := Function.update (Function.update s i []) scratch (s i).reverse
  have h₁ := transfer_exec i scratch hit s
  rw [ht, List.append_nil] at h₁
  have h₂ := transfer_exec scratch j hjt.symm t
  have htt : t scratch = (s i).reverse := by simp [t]
  have htj : t j = s j := by simp [t, hjt, hij.symm]
  rw [htt, htj, List.reverse_reverse, List.length_reverse] at h₂
  have he : Function.update (Function.update t scratch []) j (s i ++ s j) =
      Function.update (Function.update s i []) j (s i ++ s j) := by
    funext k
    by_cases hkj : k = j
    · subst k; simp
    · by_cases hkt : k = scratch
      · subst k; simp [hjt.symm, hit.symm, ht]
      · simp [t, hkj, hkt]
  rw [he] at h₂
  have hh := Exec.seq h₁ h₂
  convert hh using 1 <;> first | rfl | omega

end Superstring.BitCode.Block

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.BitCode.RunsInPolyTime

variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
  {f : α → β} {g : α → γ}

/-- Compute two values from the same explicitly coded input, then concatenate
their self-delimiting encodings. Duplication and concatenation are charged bitwise. -/
theorem pair (hf : RunsInPolyTime ea eb f) (hg : RunsInPolyTime ea ec g) :
    RunsInPolyTime ea (fun p : β × γ => eb p.1 ++ ec p.2) (fun a => (f a, g a)) := by
  obtain ⟨K, instK, i, o, b, P, hb⟩ := hf
  obtain ⟨L, instL, j, v, c, Q, hc⟩ := hg
  let input : (K ⊕ L) ⊕ Unit := .inl (.inl i)
  let ginput : (K ⊕ L) ⊕ Unit := .inl (.inr j)
  let foutput : (K ⊕ L) ⊕ Unit := .inl (.inl o)
  let output : (K ⊕ L) ⊕ Unit := .inl (.inr v)
  let scratch : (K ⊕ L) ⊕ Unit := .inr ()
  let code : Block ((K ⊕ L) ⊕ Unit) :=
    .seq (Block.copy input ginput scratch)
      (.seq ((b.rename Sum.inl).rename Sum.inl)
        (.seq ((c.rename Sum.inr).rename Sum.inl) (Block.move foutput output scratch)))
  let R : Polynomial ℕ := 17 * Polynomial.X + 9 * P + Q + 5
  refine ⟨(K ⊕ L) ⊕ Unit, inferInstance, input, output, code, R, ?_⟩
  intro a
  obtain ⟨n, hn, hf⟩ := hb a
  obtain ⟨m, hm, hg⟩ := hc a
  let s₀ := Sum.elim (Sum.elim (single i (ea a)) (single j (ea a))) (fun _ : Unit => [])
  let s₁ := Sum.elim (Sum.elim (single o (eb (f a))) (single j (ea a))) (fun _ : Unit => [])
  let s₂ := Sum.elim (Sum.elim (single o (eb (f a))) (single v (ec (g a)))) (fun _ : Unit => [])
  have hcopy := Block.copy_exec input ginput scratch (by simp [input, ginput])
    (by simp [input, scratch]) (by simp [ginput, scratch]) (single input (ea a))
    (by simp [single, input, scratch])
  have hi : single input (ea a) input = ea a := by simp [single]
  have hj : single input (ea a) ginput = [] := by simp [single, ginput, input]
  rw [hi, hj] at hcopy
  simp only [List.length_nil, Nat.mul_zero, Nat.zero_add] at hcopy
  have he₀ : Function.update (single input (ea a)) ginput (ea a) = s₀ := by
    funext k
    rcases k with (k | k) | k
    · simp [input, ginput, s₀, single]
    · by_cases hk : k = j <;> simp [input, ginput, s₀, single, hk]
    · simp [input, ginput, s₀, single]
  rw [he₀] at hcopy
  have hf' : ((b.rename Sum.inl).rename Sum.inl).Exec s₀ s₁ n :=
    (hf.left (single j (ea a))).left (fun _ : Unit => [])
  have hg' : ((c.rename Sum.inr).rename Sum.inl).Exec s₁ s₂ m :=
    (hg.right (single o (eb (f a)))).left (fun _ : Unit => [])
  have hmove := Block.move_exec foutput output scratch (by simp [foutput, output])
    (by simp [foutput, scratch]) (by simp [output, scratch]) s₂ rfl
  have hfo : s₂ foutput = eb (f a) := by simp [s₂, foutput, single]
  have hgo : s₂ output = ec (g a) := by simp [s₂, output, single]
  rw [hfo, hgo] at hmove
  have he₂ : Function.update (Function.update s₂ foutput []) output (eb (f a) ++ ec (g a)) =
      single output (eb (f a) ++ ec (g a)) := by
    funext k
    rcases k with (k | k) | k
    · by_cases hk : k = o <;> simp only [s₂, foutput, output, single, Function.update_apply, Sum.elim, Sum.inl.injEq, reduceCtorEq, hk, ite_true, ite_false]
    · by_cases hk : k = v <;> simp only [s₂, foutput, output, single, Function.update_apply, Sum.elim, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, hk, ite_true, ite_false]
    · simp only [s₂, foutput, output, single, Function.update_apply, Sum.elim, reduceCtorEq, ite_false]
  rw [he₂] at hmove
  refine ⟨9 * (ea a).length + 3 + (n + (m + (8 * (eb (f a)).length + 2))), ?_,
    Block.Exec.seq hcopy (Block.Exec.seq hf' (Block.Exec.seq hg' hmove))⟩
  have hlen := hf.bounded _ (single_bounded i (ea a)) o
  simp only [single, ↓reduceIte] at hlen
  simp only [R, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X]
  omega

end Superstring.BitCode.RunsInPolyTime

namespace Superstring.BitCode

/-- Unary natural numbers have an explicit end marker, so prefix parsing never
relies on an uncharged register-length operation. -/
def natCode : ℕ → List Bool
  | 0 => [true]
  | n + 1 => false :: natCode n

@[simp] theorem length_natCode (n : ℕ) : (natCode n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [natCode, List.length_cons, ih]

 theorem natCode_eq (n : ℕ) : natCode n = listCode (fun _ : Unit => []) (List.replicate n ()) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [natCode, List.replicate_succ, listCode, List.nil_append, ih]

@[simp] theorem natCode_reverse (n : ℕ) : (natCode n).reverse = true :: List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [natCode, List.reverse_cons, ih, List.cons_append]
    exact congrArg (fun x => true :: x) (by
      simpa only [List.replicate_one] using (List.replicate_add n 1 false).symm)

 theorem Parses.nat : Parses natCode := by
  obtain ⟨K, inst, b, c, hb⟩ := (Parses.const []).list
  refine ⟨K, inst, b, c, ?_⟩
  intro n tail acc
  simpa only [← natCode_eq] using hb (List.replicate n ()) tail acc

namespace RunsInPolyTime

variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}

/-- Normalize any clean routine to the same input and output register. The
linear bit-order-preserving relocation is included in its polynomial clock. -/
theorem inPlace (hf : RunsInPolyTime ea eb f) :
    ∃ (K : Type) (_ : DecidableEq K) (i : K) (b : Block K) (P : Polynomial ℕ),
      ∀ a, ∃ n ≤ P.eval (ea a).length, b.Exec (single i (ea a)) (single i (eb (f a))) n := by
  obtain ⟨K, inst, i, o, b, P, hb⟩ := hf
  let code : Block (K ⊕ Unit) := .seq (b.rename Sum.inl)
    (Block.move (.inl o) (.inl i) (.inr ()))
  refine ⟨K ⊕ Unit, inferInstance, .inl i, code, 9 * P + 8 * Polynomial.X + 2, ?_⟩
  intro a
  obtain ⟨n, hn, hh⟩ := hb a
  have h₁ := hh.left (fun _ : Unit => [])
  simp only [single_left] at h₁
  have h₂ := Block.move_single (Sum.inl o : K ⊕ Unit) (.inl i) (.inr ())
    (by simp) (by simp) (eb (f a))
  refine ⟨n + (8 * (eb (f a)).length + 2), ?_, Block.Exec.seq h₁ h₂⟩
  have hs := hh.bounded _ (single_bounded i (ea a)) o
  simp only [single, ↓reduceIte] at hs
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
  omega

end RunsInPolyTime

namespace Block

variable {K : Type} [DecidableEq K] {α : Type} {e : α → List Bool} {f : α → α}

/-- Iterate a clean in-place routine once per explicitly stored counter bit.
The hypothesis is a STATE SIZE invariant, not an assumed time or computation
oracle. The only computation premise is an actual bit-program execution. -/
theorem iterate_exec (b : Block K) (i : K) (P : Polynomial ℕ)
    (hb : ∀ a, ∃ n ≤ P.eval (e a).length, b.Exec (single i (e a)) (single i (e (f a))) n)
    (n M : ℕ) (a : α) (hsize : ∀ j < n, (e (f^[j] a)).length ≤ M) :
    ∃ t ≤ n * (P.eval M + 2) + 1,
      (Block.loop (Sum.inr () : K ⊕ Unit) (.seq (.pop (.inr ())) (b.rename Sum.inl))).Exec
        (Sum.elim (single i (e a)) (fun _ : Unit => List.replicate n false))
        (Sum.elim (single i (e (f^[n] a))) (fun _ : Unit => [])) t := by
  induction n generalizing a with
  | zero =>
    exact ⟨1, by simp, Exec.loop_nil rfl⟩
  | succ n ih =>
    have hrest : ∀ j < n, (e (f^[j] (f a))).length ≤ M := by
      intro j hj
      simpa only [← Function.iterate_succ_apply] using hsize (j + 1) (by omega)
    obtain ⟨m, hm, hrun⟩ := hb a
    obtain ⟨t, ht, htail⟩ := ih (f a) hrest
    have hpop : Exec (.pop (Sum.inr () : K ⊕ Unit))
        (Sum.elim (single i (e a)) (fun _ : Unit => List.replicate (n + 1) false))
        (Sum.elim (single i (e a)) (fun _ : Unit => List.replicate n false)) 1 := by
      have he : Function.update (fun _ : Unit => List.replicate (n + 1) false) ()
          (List.replicate (n + 1) false).tail = fun _ : Unit => List.replicate n false := by
        funext k; cases k; simp
      simpa only [Sum.elim_inr, update_right, he] using
        Exec.pop (Sum.inr () : K ⊕ Unit)
          (Sum.elim (single i (e a)) (fun _ : Unit => List.replicate (n + 1) false))
    have hstep := hrun.left (fun _ : Unit => List.replicate n false)
    have hh := Exec.loop_cons (by simp only [Sum.elim_inr, List.replicate_succ, ne_eq,
      List.cons_ne_nil, not_false_eq_true]) (Exec.seq hpop hstep) htail
    refine ⟨1 + m + t + 1, ?_, ?_⟩
    · have hs := hsize 0 (by omega)
      simp only [Function.iterate_zero, _root_.id] at hs
      have hp := eval_mono_nat P hs
      linarith
    · simpa only [Function.iterate_succ_apply] using hh

end Block

end Superstring.BitCode

namespace Superstring.BitCode

/-- Place the parser's input in an existing work bank, its private storage in a
fresh bank, and its output in a fresh counter register. -/
def parserEmbedding {K L : Type} (i : K) : Ports L → (K ⊕ L) ⊕ Unit
  | .inl false => .inl (.inl i)
  | .inl true => .inr ()
  | .inr k => .inl (.inr k)

 theorem parserEmbedding_injective {K L : Type} (i : K) :
    Function.Injective (parserEmbedding (L := L) i) := by
  intro x y he
  rcases x with (x | x) <;> rcases y with (y | y)
  · cases x <;> cases y <;> simp_all only [parserEmbedding, reduceCtorEq]
  · cases x <;> simp only [parserEmbedding, Sum.inl.injEq, reduceCtorEq] at he
  · cases y <;> simp only [parserEmbedding, Sum.inl.injEq, reduceCtorEq] at he
  · simpa only [parserEmbedding, Sum.inl.injEq, Sum.inr.injEq] using he

namespace Block

 theorem Exec.parseAt {K L : Type} [DecidableEq K] [DecidableEq L]
    {b : Block (Ports L)} {x y u v : List Bool} {n : ℕ}
    (h : b.Exec (pairStore x u) (pairStore y v) n) (i : K) :
    (b.rename (parserEmbedding i)).Exec
      (Sum.elim (Sum.elim (single i x) (fun _ : L => [])) (fun _ : Unit => u))
      (Sum.elim (Sum.elim (single i y) (fun _ : L => [])) (fun _ : Unit => v)) n := by
  apply h.transport (parserEmbedding i) (parserEmbedding_injective i)
  · intro k
    cases k with
    | inl k => cases k <;> simp [parserEmbedding, pairStore, portStore, single]
    | inr k => rfl
  · intro k
    cases k with
    | inl k => cases k <;> simp [parserEmbedding, pairStore, portStore, single]
    | inr k => rfl
  · intro k hk
    rcases k with (k | k) | k
    · have hne : k ≠ i := by
        intro he
        exact hk (.inl false) (by simp [parserEmbedding, he])
      simp [single, hne]
    · rfl
    · cases k
      exact False.elim (hk (.inl true) rfl)

end Block

namespace RunsInPolyTime

/-- Bounded iteration of an actual polynomial bit routine is polynomial. The
bound is on encoded intermediate DATA, and the counter is explicitly unary.
This closure rule does not assume a polynomial-time evaluator or a time oracle. -/
theorem iterate {α : Type} {e : α → List Bool} {f : α → α}
    (hf : RunsInPolyTime e e f) (R : Polynomial ℕ)
    (hsize : ∀ n a j, j < n → (e (f^[j] a)).length ≤
      R.eval (natCode n ++ e a).length) :
    RunsInPolyTime (fun p : ℕ × α => natCode p.1 ++ e p.2) e
      (fun p => f^[p.1] p.2) := by
  obtain ⟨K, instK, i, b, P, hb⟩ := hf.inPlace
  obtain ⟨L, instL, parse, c, hp⟩ := Parses.nat
  let inp : (K ⊕ L) ⊕ Unit := .inl (.inl i)
  let counter : (K ⊕ L) ⊕ Unit := .inr ()
  let code : Block ((K ⊕ L) ⊕ Unit) :=
    .seq (parse.rename (parserEmbedding i))
      (.seq (.pop counter)
        (.loop counter (.seq (.pop counter) ((b.rename Sum.inl).rename Sum.inl))))
  let Q : Polynomial ℕ := Polynomial.C (c + 2) * (Polynomial.X + 1) +
    Polynomial.X * (P.comp R + 2) + 2
  refine ⟨(K ⊕ L) ⊕ Unit, inferInstance, inp, inp, code, Q, ?_⟩
  rintro ⟨n, a⟩
  let N := (natCode n ++ e a).length
  let M := R.eval N
  obtain ⟨t, ht, hparse⟩ := hp n (e a) []
  simp only [List.append_nil, natCode_reverse, length_natCode] at hparse ht
  have hparse' := hparse.parseAt i
  simp only [single_left] at hparse'
  have hb' : ∀ a, ∃ t ≤ P.eval (e a).length,
      (b.rename Sum.inl).Exec (single (Sum.inl i : K ⊕ L) (e a))
        (single (.inl i) (e (f a))) t := by
    intro a
    obtain ⟨t, ht, hh⟩ := hb a
    exact ⟨t, ht, by simpa only [single_left] using hh.left (fun _ : L => [])⟩
  have hpop : Block.Exec (.pop counter)
      (Sum.elim (single (Sum.inl i : K ⊕ L) (e a))
        (fun _ : Unit => true :: List.replicate n false))
      (Sum.elim (single (Sum.inl i : K ⊕ L) (e a))
        (fun _ : Unit => List.replicate n false)) 1 := by
    have he : Function.update (fun _ : Unit => true :: List.replicate n false) ()
        (List.replicate n false) = fun _ : Unit => List.replicate n false := by
      funext k; cases k; simp
    simpa only [counter, Sum.elim_inr, List.tail_cons, Block.update_right, he] using
      Block.Exec.pop counter (Sum.elim (single (Sum.inl i : K ⊕ L) (e a))
        (fun _ : Unit => true :: List.replicate n false))
  obtain ⟨u, hu, hloop⟩ := Block.iterate_exec (b.rename Sum.inl) (Sum.inl i : K ⊕ L)
    P hb' n M a (hsize n a)
  simp only [single_left] at hloop
  refine ⟨t + (1 + u), ?_, Block.Exec.seq hparse' (Block.Exec.seq hpop hloop)⟩
  have hn : n + 1 ≤ N := by simp only [N, List.length_append, length_natCode]; omega
  simp only [Q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat, Polynomial.eval_comp]
  change t + (1 + u) ≤ (c + 2) * (N + 1) + N * (P.eval M + 2) + 2
  have hm := Nat.mul_le_mul_right (P.eval M + 2) (show n ≤ N by omega)
  have ht' := ht.trans (Nat.mul_le_mul_left c (show n + 1 + 1 ≤ N + 1 by omega))
  linarith

end RunsInPolyTime

end Superstring.BitCode

namespace Superstring.BitCode

abbrev Workspace (K : Type) := Unit ⊕ K
abbrev workPort {K : Type} : Workspace K := .inl ()
def workStore {K : Type} (w : List Bool) (z : Store K) : Store (Workspace K) :=
  Sum.elim (fun _ => w) z

@[simp] theorem workStore_single {K : Type} [DecidableEq K] (w : List Bool) :
    workStore w (fun _ : K => []) = single workPort w := by
  funext k
  cases k with
  | inl k => cases k; simp [workStore, single, workPort]
  | inr k => simp [workStore, single, workPort]

 def workEmbedding {K : Type} [DecidableEq K] (i : K) (k : K) : Workspace K :=
   if k = i then workPort else .inr k

 theorem workEmbedding_injective {K : Type} [DecidableEq K] (i : K) :
     Function.Injective (workEmbedding i) := by
   intro x y he
   by_cases hx : x = i <;> by_cases hy : y = i
   · exact hx.trans hy.symm
   · simp only [workEmbedding, ite_eq_left hx, ite_eq_right hy, workPort, reduceCtorEq] at he
   · simp only [workEmbedding, ite_eq_right hx, ite_eq_left hy, workPort, reduceCtorEq] at he
   · exact Sum.inr.inj (by simpa only [workEmbedding, ite_eq_right hx, ite_eq_right hy] using he)

namespace Block

 theorem Exec.inWorkspace {K : Type} [DecidableEq K] {i : K}
    {b : Block K} {w v : List Bool} {n : ℕ}
    (h : b.Exec (single i w) (single i v) n) :
    (b.rename (workEmbedding i)).Exec
      (workStore w (fun _ : K => [])) (workStore v (fun _ : K => [])) n := by
  apply h.transport (workEmbedding i) (workEmbedding_injective i)
  · intro k
    by_cases hk : k = i <;> simp [workEmbedding, hk, workPort, workStore, single]
  · intro k
    by_cases hk : k = i <;> simp [workEmbedding, hk, workPort, workStore, single]
  · intro k hk
    cases k with
    | inl u =>
      cases u
      exact False.elim (hk i (by simp [workEmbedding, workPort]))
    | inr k => rfl

/-- Two in-place workspaces may share their data register, with all their
private registers disjoint. Everything outside the active workspace is framed. -/
theorem Exec.workspace {K L : Type} [DecidableEq K] [DecidableEq L]
    {b : Block (Workspace K)} {w v : List Bool} {n : ℕ}
    (h : b.Exec (workStore w (fun _ : K => [])) (workStore v (fun _ : K => [])) n)
    (f : K → L) (hf : Function.Injective f) (z : Store L) (hz : ∀ k, z (f k) = []) :
    (b.rename (Sum.map _root_.id f)).Exec (workStore w z) (workStore v z) n := by
  apply h.transport (Sum.map _root_.id f) (Sum.map_injective.mpr ⟨Function.injective_id, hf⟩)
  · intro k
    cases k with
    | inl k => rfl
    | inr k => exact hz k
  · intro k
    cases k with
    | inl k => rfl
    | inr k => exact hz k
  · intro k hk
    cases k with
    | inl u => exact False.elim (hk (.inl u) rfl)
    | inr k => rfl

end Block

namespace RunsInPolyTime

 theorem canonical {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    (h : RunsInPolyTime ea eb f) :
    ∃ (K : Type) (_ : DecidableEq K) (b : Block (Workspace K)) (P : Polynomial ℕ),
      ∀ a, ∃ n ≤ P.eval (ea a).length,
        b.Exec (workStore (ea a) (fun _ => [])) (workStore (eb (f a)) (fun _ => [])) n := by
  obtain ⟨K, inst, i, b, P, hb⟩ := h.inPlace
  refine ⟨K, inst, b.rename (workEmbedding i), P, ?_⟩
  intro a
  obtain ⟨n, hn, hh⟩ := hb a
  exact ⟨n, hn, hh.inWorkspace⟩

/-- Branch on an explicitly encoded Boolean, charging the branch and removal
of its bit. No unbounded predicate acts as a primitive instruction. -/
theorem boolCase {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f g : α → β} (hf : RunsInPolyTime ea eb f) (hg : RunsInPolyTime ea eb g) :
    RunsInPolyTime (fun p : Bool × α => p.1 :: ea p.2) eb
      (fun p => if p.1 then f p.2 else g p.2) := by
  obtain ⟨K, instK, b, P, hb⟩ := hf.canonical
  obtain ⟨L, instL, c, Q, hc⟩ := hg.canonical
  let bt : Block (Workspace (K ⊕ L)) := b.rename (Sum.map _root_.id Sum.inl)
  let bf : Block (Workspace (K ⊕ L)) := c.rename (Sum.map _root_.id Sum.inr)
  let code : Block (Workspace (K ⊕ L)) := .branch workPort .skip
    (.seq (.pop workPort) bf) (.seq (.pop workPort) bt)
  refine ⟨Workspace (K ⊕ L), inferInstance, workPort, workPort, code, P + Q + 2, ?_⟩
  rintro ⟨v, a⟩
  have hpop : Block.Exec (.pop workPort)
      (workStore (v :: ea a) (fun _ : K ⊕ L => []))
      (workStore (ea a) (fun _ : K ⊕ L => [])) 1 := by
    have he : Function.update (fun _ : Unit => v :: ea a) () (ea a) =
        fun _ : Unit => ea a := by funext k; cases k; simp
    simpa only [workStore, workPort, Sum.elim_inl, List.tail_cons,
      Block.update_left, he] using
      Block.Exec.pop (workPort : Workspace (K ⊕ L))
        (workStore (v :: ea a) (fun _ : K ⊕ L => []))
  cases v with
  | false =>
    obtain ⟨n, hn, hh⟩ := hc a
    have hrun := hh.workspace (Sum.inr : L → K ⊕ L) Sum.inr_injective (fun _ => []) (fun _ => rfl)
    have he := Block.Exec.branch_false (k := (workPort : Workspace (K ⊕ L)))
      (a := Block.skip) (c := .seq (.pop workPort) bt) rfl (Block.Exec.seq hpop hrun)
    refine ⟨1 + n + 1, ?_, ?_⟩
    · have hq : Q.eval (ea a).length ≤ Q.eval (false :: ea a).length :=
        eval_mono_nat Q (by simp)
      simp only [Polynomial.eval_add, Polynomial.eval_ofNat]
      omega
    · simpa only [workStore_single, Bool.false_eq_true, ↓reduceIte] using he
  | true =>
    obtain ⟨n, hn, hh⟩ := hb a
    have hrun := hh.workspace (Sum.inl : K → K ⊕ L) Sum.inl_injective (fun _ => []) (fun _ => rfl)
    have he := Block.Exec.branch_true (k := (workPort : Workspace (K ⊕ L)))
      (a := Block.skip) (b := .seq (.pop workPort) bf) rfl (Block.Exec.seq hpop hrun)
    refine ⟨1 + n + 1, ?_, ?_⟩
    · have hp : P.eval (ea a).length ≤ P.eval (true :: ea a).length :=
        eval_mono_nat P (by simp)
      simp only [Polynomial.eval_add, Polynomial.eval_ofNat]
      omega
    · simpa only [workStore_single, ↓reduceIte] using he

end RunsInPolyTime

end Superstring.BitCode

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.BitCode

namespace Steps

 theorem terminal_unique {K L : Type} [DecidableEq K] {code : L → Instr K (Option L)}
    {c : Option L × Store K} {n m : ℕ} {s t : Store K}
    (h : Steps code c n (none, s)) (g : Steps code c m (none, t)) : s = t := by
  induction n generalizing c m s t with
  | zero => cases h; cases g; rfl
  | succ n ih =>
    cases h with
    | step l u h =>
      cases g with
      | step _ _ g => exact ih h g

end Steps

namespace Block

 theorem Exec.deterministic {K : Type} [DecidableEq K] {b : Block K}
    {r s t : Store K} {n m : ℕ} (h : b.Exec r s n) (g : b.Exec r t m) : s = t :=
  Steps.terminal_unique (exec_steps h) (exec_steps g)

end Block

 theorem Parses.separate {α : Type} {e : α → List Bool} (hp : Parses e)
    {a b : α} {x y : List Bool} (he : e a ++ x = e b ++ y) :
    e a = e b ∧ x = y := by
  obtain ⟨K, inst, code, c, hc⟩ := hp
  obtain ⟨n, _, ha⟩ := hc a x []
  obtain ⟨m, _, hb⟩ := hc b y []
  rw [he] at ha
  have hh := ha.deterministic hb
  have hx := congrFun hh inputPort
  have ho := congrFun hh outputPort
  change x = y at hx
  change (e a).reverse ++ [] = (e b).reverse ++ [] at ho
  simp only [List.append_nil] at ho
  exact ⟨List.reverse_injective ho, hx⟩


class Coded (α : Type) where
  code : α → List Bool
  parses : Parses code
  injective : Function.Injective code

abbrev bits {α : Type} [Coded α] : α → List Bool := Coded.code
abbrev bitSize {α : Type} [Coded α] (a : α) := (bits a).length

def Poly {α β : Type} [Coded α] [Coded β] (f : α → β) : Prop :=
  RunsInPolyTime bits bits f

instance codedBool : Coded Bool where
  code b := [b]
  parses := Parses.bit
  injective := by intro a b h; exact List.singleton_injective h

instance codedUnit : Coded Unit where
  code _ := []
  parses := Parses.const []
  injective := fun _ _ _ => Subsingleton.elim _ _

instance codedNat : Coded ℕ where
  code := natCode
  parses := Parses.nat
  injective := by
    intro a b h
    have hh := congrArg List.length h
    simp only [length_natCode] at hh
    omega

instance codedProd {α β : Type} [Coded α] [Coded β] : Coded (α × β) where
  code p := bits p.1 ++ bits p.2
  parses := Coded.parses.prod Coded.parses
  injective := by
    intro a b h
    obtain ⟨hh, ht⟩ := Coded.parses.separate h
    exact Prod.ext (Coded.injective hh) (Coded.injective ht)

instance codedList {α : Type} [Coded α] : Coded (List α) where
  code := listCode bits
  parses := Coded.parses.list
  injective := by
    intro a b h
    induction a generalizing b with
    | nil => cases b with
      | nil => rfl
      | cons b bs => simp only [listCode, List.cons.injEq, Bool.true_eq_false, false_and] at h
    | cons a as ih => cases b with
      | nil => simp only [listCode, List.cons.injEq, Bool.false_eq_true, false_and] at h
      | cons b bs =>
        have he : bits a ++ listCode bits as = bits b ++ listCode bits bs := List.cons.inj h |>.2
        obtain ⟨ha, ht⟩ := Coded.parses.separate he
        exact congrArg₂ List.cons (Coded.injective ha) (ih ht)

@[simp] theorem bits_bool (b : Bool) : bits b = [b] := rfl
@[simp] theorem bits_unit (u : Unit) : bits u = [] := rfl
@[simp] theorem bits_nat (n : ℕ) : bits n = natCode n := rfl
@[simp] theorem bits_prod {α β : Type} [Coded α] [Coded β] (a : α) (b : β) :
    bits (a, b) = bits a ++ bits b := rfl
@[simp] theorem bits_nil {α : Type} [Coded α] : bits ([] : List α) = [true] := rfl
@[simp] theorem bits_cons {α : Type} [Coded α] (a : α) (as : List α) :
    bits (a :: as) = false :: (bits a ++ bits as) := rfl
@[simp] theorem bitSize_nat (n : ℕ) : bitSize n = n + 1 := length_natCode n
@[simp] theorem bitSize_prod {α β : Type} [Coded α] [Coded β] (a : α) (b : β) :
    bitSize (a, b) = bitSize a + bitSize b := List.length_append
@[simp] theorem bitSize_nil {α : Type} [Coded α] : bitSize ([] : List α) = 1 := rfl
@[simp] theorem bitSize_cons {α : Type} [Coded α] (a : α) (as : List α) :
    bitSize (a :: as) = 1 + bitSize a + bitSize as := by
  simp only [bitSize, bits_cons, List.length_cons, List.length_append]; omega

 theorem length_le_bitSize {α : Type} [Coded α] (as : List α) : as.length + 1 ≤ bitSize as := by
  induction as with
  | nil => simp
  | cons a as ih => simp only [bitSize_cons, List.length_cons]; omega

namespace Poly

variable {α β γ δ : Type} [Coded α] [Coded β] [Coded γ] [Coded δ]

 theorem id : Poly (_root_.id : α → α) := RunsInPolyTime.id bits
 theorem const (b : β) : Poly (fun _ : α => b) := RunsInPolyTime.const bits bits b
 theorem comp {f : α → β} {g : β → γ} (hg : Poly g) (hf : Poly f) : Poly (g ∘ f) :=
   RunsInPolyTime.comp hg hf
 theorem pair {f : α → β} {g : α → γ} (hf : Poly f) (hg : Poly g) :
     Poly (fun a => (f a, g a)) := RunsInPolyTime.pair hf hg
 theorem fst : Poly (Prod.fst : α × β → α) := RunsInPolyTime.fst bits Coded.parses
 theorem snd : Poly (Prod.snd : α × β → β) := RunsInPolyTime.snd bits Coded.parses
 theorem cons : Poly (fun p : α × List α => p.1 :: p.2) := RunsInPolyTime.cons bits
 theorem ite {p : α → Bool} {f g : α → β} (hp : Poly p) (hf : Poly f) (hg : Poly g) :
     Poly (fun a => if p a then f a else g a) := by
   have hb := RunsInPolyTime.boolCase hf hg
   have hp' := hp.pair (id : Poly (_root_.id : α → α))
   exact hb.comp hp'
 theorem iterate {f : α → α} (hf : Poly f) (R : Polynomial ℕ)
     (hs : ∀ n a j, j < n → bitSize (f^[j] a) ≤ R.eval (bitSize (n, a))) :
     Poly (fun p : ℕ × α => f^[p.1] p.2) := RunsInPolyTime.iterate hf R hs

 theorem output_size {f : α → β} (hf : Poly f) :
     ∃ P : Polynomial ℕ, ∀ a, bitSize (f a) ≤ P.eval (bitSize a) :=
   RunsInPolyTime.output_length hf

end Poly

end Superstring.BitCode

namespace Superstring.BitCode

 def sumCode {α β : Type} (ea : α → List Bool) (eb : β → List Bool) : α ⊕ β → List Bool
   | .inl a => false :: ea a
   | .inr b => true :: eb b

 theorem Parses.sum {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    (ha : Parses ea) (hz : Parses eb) : Parses (sumCode ea eb) := by
  obtain ⟨K, instK, b, c, hb⟩ := ha
  obtain ⟨L, instL, d, e, hd⟩ := hz
  let left : Block (Ports (K ⊕ L)) := b.rename (Sum.map _root_.id Sum.inl)
  let right : Block (Ports (K ⊕ L)) := d.rename (Sum.map _root_.id Sum.inr)
  let code : Block (Ports (K ⊕ L)) := .branch inputPort .skip
    (.seq (Block.readBit inputPort outputPort) left)
    (.seq (Block.readBit inputPort outputPort) right)
  refine ⟨K ⊕ L, inferInstance, code, c + e + 4, ?_⟩
  intro a tail acc
  cases a with
  | inl a =>
    obtain ⟨n, hn, hh⟩ := hb a tail (false :: acc)
    have hrun := hh.ports (Sum.inl : K → K ⊕ L) Sum.inl_injective (fun _ => []) (fun _ => rfl)
    have hread := Block.readBit_exec false (ea a ++ tail) acc (fun _ : K ⊕ L => [])
    have he := Block.Exec.branch_false (k := (inputPort : Ports (K ⊕ L))) (a := Block.skip)
      (c := .seq (Block.readBit inputPort outputPort) right) rfl (Block.Exec.seq hread hrun)
    refine ⟨3 + n + 1, ?_, ?_⟩
    · simp only [sumCode, List.length_cons]; nlinarith
    · simpa only [sumCode, List.cons_append, List.reverse_cons, List.append_assoc,
        List.singleton_append, List.nil_append, pairStore] using he
  | inr a =>
    obtain ⟨n, hn, hh⟩ := hd a tail (true :: acc)
    have hrun := hh.ports (Sum.inr : L → K ⊕ L) Sum.inr_injective (fun _ => []) (fun _ => rfl)
    have hread := Block.readBit_exec true (eb a ++ tail) acc (fun _ : K ⊕ L => [])
    have he := Block.Exec.branch_true (k := (inputPort : Ports (K ⊕ L))) (a := Block.skip)
      (b := .seq (Block.readBit inputPort outputPort) left) rfl (Block.Exec.seq hread hrun)
    refine ⟨3 + n + 1, ?_, ?_⟩
    · simp only [sumCode, List.length_cons]; nlinarith
    · simpa only [sumCode, List.cons_append, List.reverse_cons, List.append_assoc,
        List.singleton_append, List.nil_append, pairStore] using he

instance codedSum {α β : Type} [Coded α] [Coded β] : Coded (α ⊕ β) where
  code := sumCode bits bits
  parses := Coded.parses.sum Coded.parses
  injective := by
    intro a b h
    cases a with
    | inl a => cases b with
      | inl b => exact congrArg Sum.inl (Coded.injective (List.cons.inj h).2)
      | inr b => simp only [sumCode, List.cons.injEq, Bool.false_eq_true, false_and] at h
    | inr a => cases b with
      | inl b => simp only [sumCode, List.cons.injEq, Bool.true_eq_false, false_and] at h
      | inr b => exact congrArg Sum.inr (Coded.injective (List.cons.inj h).2)

@[simp] theorem bits_inl {α β : Type} [Coded α] [Coded β] (a : α) :
    bits (Sum.inl a : α ⊕ β) = false :: bits a := rfl
@[simp] theorem bits_inr {α β : Type} [Coded α] [Coded β] (b : β) :
    bits (Sum.inr b : α ⊕ β) = true :: bits b := rfl

namespace Poly

 theorem sumCases {α β γ : Type} [Coded α] [Coded β] [Coded γ]
    {f : α → γ} {g : β → γ} (hf : Poly f) (hg : Poly g) : Poly (Sum.elim f g) := by
  obtain ⟨K, instK, b, P, hb⟩ := hf.canonical
  obtain ⟨L, instL, c, Q, hc⟩ := hg.canonical
  let bf : Block (Workspace (K ⊕ L)) := b.rename (Sum.map _root_.id Sum.inl)
  let bt : Block (Workspace (K ⊕ L)) := c.rename (Sum.map _root_.id Sum.inr)
  let code : Block (Workspace (K ⊕ L)) := .branch workPort .skip
    (.seq (.pop workPort) bf) (.seq (.pop workPort) bt)
  refine ⟨Workspace (K ⊕ L), inferInstance, workPort, workPort, code, P + Q + 2, ?_⟩
  intro a
  have hpop (v : Bool) (w : List Bool) : Block.Exec (.pop workPort)
      (workStore (v :: w) (fun _ : K ⊕ L => []))
      (workStore w (fun _ : K ⊕ L => [])) 1 := by
    have he : Function.update (fun _ : Unit => v :: w) () w =
        fun _ : Unit => w := by funext k; cases k; simp
    simpa only [workStore, workPort, Sum.elim_inl, List.tail_cons,
      Block.update_left, he] using
      Block.Exec.pop (workPort : Workspace (K ⊕ L))
        (workStore (v :: w) (fun _ : K ⊕ L => []))
  cases a with
  | inl a =>
    obtain ⟨n, hn, hh⟩ := hb a
    have hrun := hh.workspace (Sum.inl : K → K ⊕ L) Sum.inl_injective (fun _ => []) (fun _ => rfl)
    have he := Block.Exec.branch_false (k := (workPort : Workspace (K ⊕ L)))
      (a := Block.skip) (c := .seq (.pop workPort) bt) rfl (Block.Exec.seq (hpop false (bits a)) hrun)
    refine ⟨1 + n + 1, ?_, ?_⟩
    · have hp : P.eval (bits a).length ≤ P.eval (false :: bits a).length := eval_mono_nat P (by simp)
      simp only [bits_inl, Polynomial.eval_add, Polynomial.eval_ofNat]
      omega
    · simpa only [workStore_single, bits_inl, Sum.elim_inl] using he
  | inr a =>
    obtain ⟨n, hn, hh⟩ := hc a
    have hrun := hh.workspace (Sum.inr : L → K ⊕ L) Sum.inr_injective (fun _ => []) (fun _ => rfl)
    have he := Block.Exec.branch_true (k := (workPort : Workspace (K ⊕ L)))
      (a := Block.skip) (b := .seq (.pop workPort) bf) rfl (Block.Exec.seq (hpop true (bits a)) hrun)
    refine ⟨1 + n + 1, ?_, ?_⟩
    · have hq : Q.eval (bits a).length ≤ Q.eval (true :: bits a).length := eval_mono_nat Q (by simp)
      simp only [bits_inr, Polynomial.eval_add, Polynomial.eval_ofNat]
      omega
    · simpa only [workStore_single, bits_inr, Sum.elim_inr] using he

/-- Merely changing a typed view of the SAME input bits does not execute the
view function. This is used only with an explicit encoding equality below. -/
 theorem reencode {α β γ : Type} [Coded α] [Coded β] [Coded γ]
    {f : β → γ} (hf : Poly f) (r : α → β) (he : ∀ a, bits (r a) = bits a) :
    Poly (f ∘ r) := by
  obtain ⟨K, inst, i, o, b, P, hb⟩ := hf
  refine ⟨K, inst, i, o, b, P, ?_⟩
  intro a
  simpa only [he, Function.comp_apply] using hb (r a)

/-- One-step list destructor, implemented only by the leading spine marker.
The nonempty branch receives exactly the head followed by the encoded tail. -/
 theorem listCases {α β : Type} [Coded α] [Coded β] (z : β)
    {f : α × List α → β} (hf : Poly f) :
    Poly (fun xs : List α => match xs with | [] => z | x :: xs => f (x, xs)) := by
  let view : List α → (α × List α) ⊕ Unit
    | [] => .inr ()
    | x :: xs => .inl (x, xs)
  have he (xs : List α) : bits (view xs) = bits xs := by cases xs <;> rfl
  convert (hf.sumCases (const z : Poly (fun _ : Unit => z))).reencode view he using 1
  funext xs; cases xs <;> rfl

 theorem tail {α : Type} [Coded α] : Poly (List.tail : List α → List α) :=
   listCases [] snd

 theorem headD {α : Type} [Coded α] (z : α) : Poly (fun xs : List α => xs.headD z) := by
   convert listCases z (fst : Poly (Prod.fst : α × List α → α)) using 1
   funext xs; cases xs <;> rfl

 theorem isEmpty {α : Type} [Coded α] : Poly (List.isEmpty : List α → Bool) :=
   listCases true (const false)

end Poly

end Superstring.BitCode

namespace Superstring.BitCode

namespace Block

 def countBits {K : Type} (i o : K) : Block K := .loop i (.seq (.pop i) (.push o false))

 theorem countBits_exec {K : Type} [DecidableEq K] (w : List Bool) (j : ℕ) (z : Store K) :
    (countBits inputPort outputPort).Exec (portStore w (natCode j) z)
      (portStore [] (natCode (w.length + j)) z) (3 * w.length + 1) := by
  induction w generalizing j with
  | nil => simpa [countBits] using (Exec.loop_nil (a := .seq (.pop inputPort) (.push outputPort false)) (rfl : portStore [] (natCode j) z inputPort = []))
  | cons b w ih =>
    have hp : Exec (.pop inputPort) (portStore (b :: w) (natCode j) z)
        (portStore w (natCode j) z) 1 := by
      simpa only [portStore_input, List.tail_cons, update_input] using
        Exec.pop inputPort (portStore (b :: w) (natCode j) z)
    have hq : Exec (.push outputPort false) (portStore w (natCode j) z)
        (portStore w (natCode (j + 1)) z) 1 := by
      simpa only [portStore_output, update_output, natCode] using
        Exec.push outputPort false (portStore w (natCode j) z)
    have he := Exec.loop_cons (show portStore (b :: w) (natCode j) z inputPort ≠ [] from List.cons_ne_nil _ _) (Exec.seq hp hq) (ih (j + 1))
    simpa only [countBits, List.length_cons,
      show w.length + 1 + j = w.length + (j + 1) by omega,
      show 3 * (w.length + 1) + 1 = 1 + 1 + (3 * w.length + 1) + 1 by omega] using he

end Block

namespace Poly

 theorem size {α : Type} [Coded α] : Poly (bitSize : α → ℕ) := by
  let code : Block (Ports Unit) := .seq (.push outputPort true)
    (Block.countBits inputPort outputPort)
  refine ⟨Ports Unit, inferInstance, inputPort, outputPort, code, 3 * Polynomial.X + 2, ?_⟩
  intro a
  have hp : Block.Exec (.push outputPort true) (pairStore (bits a) [] : Store (Ports Unit))
      (pairStore (bits a) (natCode 0)) 1 := by
    simpa only [pairStore, portStore_output, update_output, natCode] using
      Block.Exec.push (outputPort : Ports Unit) true (pairStore (bits a) [])
  have he := Block.Exec.seq hp (Block.countBits_exec (bits a) 0 (fun _ : Unit => []))
  refine ⟨1 + (3 * (bits a).length + 1), ?_, ?_⟩
  · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]; omega
  · have he' : code.Exec (pairStore (bits a) [])
        (pairStore [] (natCode (bits a).length)) (1 + (3 * (bits a).length + 1)) := by
      simpa only [code, pairStore, Nat.add_zero] using he
    change code.Exec (single inputPort (bits a)) (single outputPort (natCode (bits a).length)) _
    simpa only [pairStore_input, pairStore_output] using he'

 theorem succ : Poly (Nat.succ : ℕ → ℕ) := by
  refine ⟨Unit, inferInstance, (), (), .push () false, 1, ?_⟩
  intro a
  refine ⟨1, by simp, ?_⟩
  have he : Function.update (single () (bits a)) () (false :: single () (bits a) ()) =
      single () (bits a.succ) := by funext k; cases k; simp [single, natCode]
  simpa only [he] using Block.Exec.push () false (single () (bits a))

 theorem listCasesWith {α β γ : Type} [Coded α] [Coded β] [Coded γ]
    {z : β → γ} {f : α × (List α × β) → γ} (hz : Poly z) (hf : Poly f) :
    Poly (fun p : List α × β => match p.1 with
      | [] => z p.2 | x :: xs => f (x, xs, p.2)) := by
  let view : List α × β → (α × (List α × β)) ⊕ β
    | ([], b) => .inr b
    | (x :: xs, b) => .inl (x, xs, b)
  have he (p : List α × β) : bits (view p) = bits p := by
    rcases p with ⟨xs, b⟩; cases xs <;>
      simp only [view, bits_inl, bits_inr, bits_prod, bits_nil, bits_cons,
        List.nil_append, List.cons_append, List.append_assoc]
  convert (hf.sumCases hz).reencode view he using 1
  funext p; rcases p with ⟨xs, b⟩; cases xs <;> rfl

 theorem natCasesWith {β γ : Type} [Coded β] [Coded γ]
    {z : β → γ} {f : ℕ × β → γ} (hz : Poly z) (hf : Poly f) :
    Poly (fun p : ℕ × β => match p.1 with
      | 0 => z p.2 | n + 1 => f (n, p.2)) := by
  let view : ℕ × β → (ℕ × β) ⊕ β
    | (0, b) => .inr b
    | (n + 1, b) => .inl (n, b)
  have he (p : ℕ × β) : bits (view p) = bits p := by
    rcases p with ⟨n, b⟩; cases n <;>
      simp only [view, bits_inl, bits_inr, bits_prod, bits_nat, natCode,
        List.nil_append, List.cons_append]
  convert (hf.sumCases hz).reencode view he using 1
  funext p; rcases p with ⟨n, b⟩; cases n <;> rfl

end Poly

end Superstring.BitCode

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.BitCode

 theorem bitSize_sublist {α : Type} [Coded α] {xs ys : List α} (h : xs.Sublist ys) :
    bitSize xs ≤ bitSize ys := by
  induction h with
  | slnil => exact le_rfl
  | cons b h ih => simp only [bitSize_cons]; omega
  | cons_cons b h ih => simp only [bitSize_cons]; omega

 theorem bitSize_append {α : Type} [Coded α] (xs ys : List α) :
    bitSize (xs ++ ys) + 1 = bitSize xs + bitSize ys := by
  induction xs with
  | nil => simp [Nat.add_comm]
  | cons x xs ih => simp only [List.cons_append, bitSize_cons]; omega

 def foldStep {α β : Type} (f : β → α → β) (p : List α × β) : List α × β :=
   match p.1 with
   | [] => p
   | x :: xs => (xs, f p.2 x)

 theorem iterate_foldStep {α β : Type} (f : β → α → β) (n : ℕ) (xs : List α) (a : β) :
    (foldStep f)^[n] (xs, a) = (xs.drop n, (xs.take n).foldl f a) := by
  induction n generalizing xs a with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    cases xs with
    | nil => simpa only [foldStep, List.take_nil, List.drop_nil, List.foldl_nil] using ih [] a
    | cons x xs => simpa only [foldStep, List.take_succ_cons, List.drop_succ_cons,
        List.foldl_cons] using ih xs (f a x)

namespace Poly

 theorem foldStep {α β : Type} [Coded α] [Coded β] {f : β → α → β}
    (hf : Poly (fun p : β × α => f p.1 p.2)) : Poly (foldStep f) := by
  have hn : Poly (fun a : β => (([] : List α), a)) := (const []).pair id
  have hc : Poly (fun p : α × (List α × β) => (p.2.1, f p.2.2 p.1)) :=
    (fst.comp snd).pair (hf.comp ((snd.comp snd).pair fst))
  convert listCasesWith hn hc using 1
  funext p; rcases p with ⟨xs, a⟩; cases xs <;> rfl

/-- A bounded list fold, with its genuine encoded-data invariant exposed.
The bound concerns mathematical intermediate values, not an assumed runtime. -/
 theorem foldl {α β : Type} [Coded α] [Coded β] {f : β → α → β}
    (hf : Poly (fun p : β × α => f p.1 p.2)) (R : Polynomial ℕ)
    (hs : ∀ (xs : List α) (a : β) (j : ℕ), bitSize ((xs.take j).foldl f a) ≤ R.eval (bitSize (xs, a))) :
    Poly (fun p : List α × β => p.1.foldl f p.2) := by
  have hi : Poly (fun p : ℕ × (List α × β) => (Superstring.BitCode.foldStep f)^[p.1] p.2) := by
    apply (foldStep hf).iterate (Polynomial.X + R)
    intro n p j _
    rcases p with ⟨xs, a⟩
    rw [iterate_foldStep]
    simp only [bitSize_prod, Polynomial.eval_add, Polynomial.eval_X]
    have hd := bitSize_sublist (List.drop_sublist j xs)
    have hb := hs xs a j
    have hr := eval_mono_nat R (show bitSize (xs, a) ≤ bitSize n + (bitSize xs + bitSize a) by simp)
    simp only [bitSize_prod] at hb hr
    omega
  have htimer : Poly (fun p : List α × β => (bitSize p.1, p)) :=
    (size.comp fst).pair id
  have he : (fun p : List α × β => ((Superstring.BitCode.foldStep f)^[bitSize p.1] p).2) =
      fun p => p.1.foldl f p.2 := by
    funext p
    rcases p with ⟨xs, a⟩
    rw [iterate_foldStep]
    simp only [List.take_of_length_le (show xs.length ≤ bitSize xs by have := length_le_bitSize xs; omega)]
  exact he ▸ snd.comp (hi.comp htimer)

end Poly

end Superstring.BitCode

namespace Superstring.BitCode

 theorem bitSize_mem {α : Type} [Coded α] {x : α} {xs : List α} (h : x ∈ xs) :
    bitSize x ≤ bitSize xs := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp only [bitSize_cons]; omega
    · have := ih h; simp only [bitSize_cons]; omega

 theorem foldl_size_additive {α β : Type} [Coded α] [Coded β]
    (f : β → α → β) (Q : Polynomial ℕ)
    (hf : ∀ a x, bitSize (f a x) ≤ bitSize a + Q.eval (bitSize x))
    (xs : List α) (M : ℕ) (hx : ∀ x ∈ xs, bitSize x ≤ M) (a : β) :
    bitSize (xs.foldl f a) ≤ bitSize a + xs.length * Q.eval M := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    have hh := ih (fun y hy => hx y (List.mem_cons_of_mem x hy)) (f a x)
    have hg := hf a x
    have hm := eval_mono_nat Q (hx x (List.mem_cons_self))
    simp only [List.foldl_cons, List.length_cons]
    linarith

namespace Poly

 theorem foldl_additive {α β : Type} [Coded α] [Coded β] {f : β → α → β}
    (hf : Poly (fun p : β × α => f p.1 p.2)) (Q : Polynomial ℕ)
    (hs : ∀ a x, bitSize (f a x) ≤ bitSize a + Q.eval (bitSize x)) :
    Poly (fun p : List α × β => p.1.foldl f p.2) := by
  apply foldl hf (Polynomial.X + Polynomial.X * Q)
  intro xs a j
  let N := bitSize (xs, a)
  have hx : ∀ x ∈ xs.take j, bitSize x ≤ N := by
    intro x hx
    have hm := bitSize_mem (List.mem_of_mem_take hx)
    dsimp [N]; simp only [bitSize_prod]; omega
  have hb := foldl_size_additive f Q hs (xs.take j) N hx a
  have hl : (xs.take j).length ≤ N := by
    have h₁ : (xs.take j).length ≤ xs.length := by simp only [List.length_take]; exact Nat.min_le_right _ _
    have h₂ := length_le_bitSize xs
    dsimp [N]; simp only [bitSize_prod]; omega
  have ha : bitSize a ≤ N := by simp [N]
  have hmul := Nat.mul_le_mul_right (Q.eval N) hl
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
  change bitSize ((xs.take j).foldl f a) ≤ N + N * Q.eval N
  omega

 theorem reverse {α : Type} [Coded α] : Poly (List.reverse : List α → List α) := by
  have hf : Poly (fun p : List α × α => p.2 :: p.1) := cons.comp (snd.pair fst)
  have hs : ∀ (a : List α) (x : α), bitSize (x :: a) ≤
      bitSize a + (Polynomial.X + 1 : Polynomial ℕ).eval (bitSize x) := by
    intros; simp only [bitSize_cons, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_one]; omega
  have hp := (foldl_additive hf (Polynomial.X + 1) hs).comp
    ((id : Poly (_root_.id : List α → List α)).pair (const ([] : List α)))
  convert hp using 1
  funext xs
  simp only [Function.comp_apply, _root_.id, List.foldl_flip_cons_eq_append', List.append_nil]

end Poly

end Superstring.BitCode

namespace Superstring.BitCode

@[simp] theorem bitSize_reverse {α : Type} [Coded α] (xs : List α) :
    bitSize xs.reverse = bitSize xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have h := bitSize_append xs.reverse [x]
    simp only [List.reverse_cons, bitSize_cons, bitSize_nil] at *
    omega

namespace Poly

 theorem map {α β : Type} [Coded α] [Coded β] {f : α → β}
    (hf : Poly f) : Poly (List.map f) := by
  obtain ⟨P, hP⟩ := hf.output_size
  have hstep : Poly (fun p : List β × α => f p.2 :: p.1) := cons.comp ((hf.comp snd).pair fst)
  have hs : ∀ (a : List β) (x : α), bitSize (f x :: a) ≤
      bitSize a + (P + 1).eval (bitSize x) := by
    intro a x
    have := hP x
    simp only [bitSize_cons, Polynomial.eval_add, Polynomial.eval_one]; omega
  have hp := reverse.comp ((foldl_additive hstep (P + 1) hs).comp
    ((id : Poly (_root_.id : List α → List α)).pair (const ([] : List β))))
  convert hp using 1
  funext xs
  simp only [Function.comp_apply, _root_.id, List.foldl_flip_cons_eq_append,
    List.append_nil, List.reverse_reverse]

 theorem append {α : Type} [Coded α] : Poly (fun p : List α × List α => p.1 ++ p.2) := by
  have hstep : Poly (fun p : List α × α => p.2 :: p.1) := cons.comp (snd.pair fst)
  have hs : ∀ (a : List α) (x : α), bitSize (x :: a) ≤
      bitSize a + (Polynomial.X + 1 : Polynomial ℕ).eval (bitSize x) := by
    intros; simp only [bitSize_cons, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_one]; omega
  have hp := (foldl_additive hstep (Polynomial.X + 1) hs).comp
    ((reverse.comp fst).pair (snd : Poly (Prod.snd : List α × List α → List α)))
  convert hp using 1
  funext p
  simp only [Function.comp_apply, List.foldl_flip_cons_eq_append', List.reverse_reverse]

 theorem length {α : Type} [Coded α] : Poly (List.length : List α → ℕ) := by
  have hf : Poly (fun p : ℕ × α => p.1 + 1) := succ.comp fst
  have hs : ∀ (a : ℕ) (x : α), bitSize (a + 1) ≤
      bitSize a + (1 : Polynomial ℕ).eval (bitSize x) := by intros; simp
  have hp := (foldl_additive hf 1 hs).comp
    ((id : Poly (_root_.id : List α → List α)).pair (const 0))
  convert hp using 1
  funext xs
  have hl (xs : List α) (n : ℕ) : xs.foldl (fun n _ => n + 1) n = n + xs.length := by
    induction xs generalizing n with
    | nil => simp
    | cons x xs ih => simp only [List.foldl_cons, List.length_cons, ih]; omega
  simp only [Function.comp_apply, _root_.id, hl, Nat.zero_add]

 theorem not : Poly (Bool.not : Bool → Bool) := by
   convert ite (id : Poly (_root_.id : Bool → Bool)) (const false) (const true) using 1
   funext b; cases b <;> rfl

 theorem and : Poly (fun p : Bool × Bool => p.1 && p.2) := by
   convert ite (fst : Poly (Prod.fst : Bool × Bool → Bool)) snd (const false) using 1
   funext p; cases p with | mk b c => cases b <;> rfl

 theorem or : Poly (fun p : Bool × Bool => p.1 || p.2) := by
   convert ite (fst : Poly (Prod.fst : Bool × Bool → Bool)) (const true) snd using 1
   funext p; cases p with | mk b c => cases b <;> rfl

 theorem eqBool : Poly (fun p : Bool × Bool => decide (p.1 = p.2)) := by
   convert ite (fst : Poly (Prod.fst : Bool × Bool → Bool)) snd (not.comp snd) using 1
   funext p; cases p with | mk b c => cases b <;> cases c <;> rfl

 theorem pred : Poly (Nat.pred : ℕ → ℕ) := by
   have hp := (natCasesWith (const 0 : Poly (fun _ : Unit => 0))
      (fst : Poly (Prod.fst : ℕ × Unit → ℕ))).comp
      ((id : Poly (_root_.id : ℕ → ℕ)).pair (const ()))
   convert hp using 1
   funext n; cases n <;> rfl

 theorem isZero : Poly (fun n : ℕ => decide (n = 0)) := by
   have hp := (natCasesWith (const true : Poly (fun _ : Unit => true))
      (const false : Poly (fun _ : ℕ × Unit => false))).comp
      ((id : Poly (_root_.id : ℕ → ℕ)).pair (const ()))
   convert hp using 1
   funext n; cases n <;> rfl

 theorem add : Poly (fun p : ℕ × ℕ => p.1 + p.2) := by
   have hi := succ.iterate (2 * Polynomial.X)
     (by intro n a j hj
         have he : Nat.succ^[j] a = a + j := by
           induction j with
           | zero => simp
           | succ j ih => simp only [Function.iterate_succ_apply']; omega
         simp only [he, bitSize_nat, bitSize_prod, Polynomial.eval_mul,
           Polynomial.eval_ofNat, Polynomial.eval_X]; omega)
   convert hi using 1
   funext p
   rcases p with ⟨n, a⟩
   induction n with
   | zero => simp
   | succ n ih => simp only [Function.iterate_succ_apply', ← ih]; omega

end Poly

end Superstring.BitCode

namespace Superstring.BitCode

namespace Block

 def encodeBitList {K : Type} (i o : K) : Block K := .loop i
   (.seq (readBit i o) (.push o false))

 theorem encodeBitList_exec {K : Type} [DecidableEq K] (w acc : List Bool) (z : Store K) :
    (encodeBitList inputPort outputPort).Exec (portStore w acc z)
      (portStore [] (w.foldl (fun acc b => false :: b :: acc) acc) z) (5 * w.length + 1) := by
   induction w generalizing acc with
   | nil => simpa [encodeBitList] using
       (Exec.loop_nil (a := .seq (readBit inputPort outputPort) (.push outputPort false))
         (rfl : portStore [] acc z inputPort = []))
   | cons b w ih =>
     have h₁ := readBit_exec b w acc z
     have h₂ : Exec (.push outputPort false) (portStore w (b :: acc) z)
         (portStore w (false :: b :: acc) z) 1 := by
       simpa only [portStore_output, update_output] using
         Exec.push outputPort false (portStore w (b :: acc) z)
     have he := Exec.loop_cons
       (show portStore (b :: w) acc z inputPort ≠ [] from List.cons_ne_nil _ _)
       (Exec.seq h₁ h₂) (ih (false :: b :: acc))
     simpa only [encodeBitList, List.foldl_cons, List.length_cons,
       show 5 * (w.length + 1) + 1 = 3 + 1 + (5 * w.length + 1) + 1 by omega] using he

end Block

 theorem fold_encodeBitList (w acc : List Bool) :
    w.foldl (fun acc b => false :: b :: acc) acc =
      (w.reverse.flatMap (fun b => [false, b])) ++ acc := by
  induction w generalizing acc with
  | nil => simp
  | cons b w ih =>
    simp only [List.foldl_cons, ih, List.reverse_cons, List.flatMap_append,
      List.flatMap_singleton, List.append_assoc, List.cons_append, List.nil_append]

 theorem listCode_bit (w : List Bool) :
    listCode (fun b => [b]) w = w.flatMap (fun b => [false, b]) ++ [true] := by
  induction w with
  | nil => rfl
  | cons b w ih => simp only [listCode, List.flatMap_cons, List.cons_append,
      List.nil_append, ih]

namespace Poly

/-- Materialize the input encoding as an ordinary typed bit list. Each marker
and bit is written by charged finite-state stack code. -/
 theorem encoding {α : Type} [Coded α] : Poly (bits : α → List Bool) := by
   have hrev : RunsInPolyTime (bits : α → List Bool) (fun a => (bits a).reverse) _root_.id := by
     simpa only [List.reverse_reverse] using RunsInPolyTime.reverseEncoding (fun a : α => (bits a).reverse)
   have henc : RunsInPolyTime (fun a : α => (bits a).reverse) (bits : List Bool → List Bool)
       (bits : α → List Bool) := by
     let code : Block (Ports Unit) := .seq (.push outputPort true)
       (.loop inputPort (.seq (Block.readBit inputPort outputPort) (.push outputPort false)))
     refine ⟨Ports Unit, inferInstance, inputPort, outputPort, code, 5 * Polynomial.X + 2, ?_⟩
     intro a
     have hp : Block.Exec (.push outputPort true)
         (pairStore (bits a).reverse [] : Store (Ports Unit)) (pairStore (bits a).reverse [true]) 1 := by
       simpa only [pairStore, portStore_output, update_output] using
         Block.Exec.push (outputPort : Ports Unit) true (pairStore (bits a).reverse [])
     have hl := Block.encodeBitList_exec (bits a).reverse [true] (fun _ : Unit => [])
     rw [fold_encodeBitList, List.reverse_reverse, ← listCode_bit] at hl
     have he := Block.Exec.seq hp hl
     refine ⟨1 + (5 * (bits a).reverse.length + 1), ?_, ?_⟩
     · simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]; omega
     · have he' : code.Exec (pairStore (bits a).reverse [])
           (pairStore [] (bits (bits a))) (1 + (5 * (bits a).reverse.length + 1)) := he
       simpa only [pairStore_input, pairStore_output] using he'
   exact henc.comp hrev

end Poly

end Superstring.BitCode

namespace Superstring.BitCode

 def compareBitsStep (s : List Bool × Bool) (x : Bool) : List Bool × Bool :=
   match s.1 with
   | [] => ([], false)
   | y :: ys => (ys, s.2 && decide (x = y))

 theorem compareBits_correct (xs ys : List Bool) (b : Bool) :
    let r := xs.foldl compareBitsStep (ys, b)
    (r.2 && r.1.isEmpty) = (b && decide (xs = ys)) := by
   induction xs generalizing ys b with
   | nil => cases ys <;> simp
   | cons x xs ih =>
     cases ys with
     | nil => simpa only [List.foldl_cons, compareBitsStep, List.cons_ne_nil,
         decide_false, Bool.and_false, Bool.false_and] using ih [] false
     | cons y ys =>
       simpa only [List.foldl_cons, compareBitsStep, List.cons.injEq, Bool.decide_and,
         Bool.and_assoc] using ih ys (b && decide (x = y))

 theorem compareBits_size (s : List Bool × Bool) (x : Bool) :
    bitSize (compareBitsStep s x) ≤ bitSize s := by
   obtain ⟨ys, b⟩ := s
   cases ys <;> simp [compareBitsStep, bitSize, bits_bool]

namespace Poly

 theorem compareBitsStep : Poly (fun p : (List Bool × Bool) × Bool =>
     Superstring.BitCode.compareBitsStep p.1 p.2) := by
   have hn : Poly (fun _ : Bool × Bool => (([] : List Bool), false)) := const ([], false)
   have hc : Poly (fun p : Bool × (List Bool × (Bool × Bool)) =>
       (p.2.1, p.2.2.1 && decide (p.2.2.2 = p.1))) :=
     (fst.comp snd).pair
       (and.comp ((fst.comp (snd.comp snd)).pair
         (eqBool.comp ((snd.comp (snd.comp snd)).pair fst))))
   have hp := (listCasesWith hn hc).comp
     ((fst.comp fst).pair ((snd.comp fst).pair (snd : Poly (Prod.snd : (List Bool × Bool) × Bool → Bool))))
   convert hp using 1
   funext p; rcases p with ⟨⟨ys, b⟩, x⟩; cases ys <;> rfl

 theorem eqBits : Poly (fun p : List Bool × List Bool => decide (p.1 = p.2)) := by
   have hf := foldl_additive compareBitsStep 0
     (fun s x => by simpa only [Polynomial.eval_zero, Nat.add_zero] using compareBits_size s x)
   have hp := (and.comp (snd.pair (isEmpty.comp fst))).comp
     (hf.comp (fst.pair (snd.pair (const true : Poly (fun _ : List Bool × List Bool => true)))))
   convert hp using 1
   funext p
   simpa only [Bool.true_and, Function.comp_apply] using (compareBits_correct p.1 p.2 true).symm

 theorem eq {α : Type} [Coded α] [DecidableEq α] :
     Poly (fun p : α × α => decide (p.1 = p.2)) := by
   have hp := eqBits.comp (((encoding : Poly (bits : α → List Bool)).comp
     (fst : Poly (Prod.fst : α × α → α))).pair (encoding.comp snd))
   convert hp using 1
   funext p
   change decide (p.1 = p.2) = decide (bits p.1 = bits p.2)
   congr 1
   exact propext Coded.injective.eq_iff.symm

end Poly

end Superstring.BitCode

namespace Superstring.BitCode

 theorem bitSize_map_le {α β : Type} [Coded β] (xs : List α) (f : α → β) (M : ℕ)
    (h : ∀ x ∈ xs, bitSize (f x) ≤ M) :
    bitSize (xs.map f) ≤ 1 + xs.length * (M + 1) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hb := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    have hx := h x List.mem_cons_self
    simp only [List.map_cons, bitSize_cons, List.length_cons]
    linarith

 def mapWithStep {α β γ : Type} (f : γ × α → β) (s : γ × List β) (x : α) : γ × List β :=
   (s.1, f (s.1, x) :: s.2)

 theorem foldl_mapWithStep {α β γ : Type} (f : γ × α → β) (xs : List α)
    (c : γ) (out : List β) :
    xs.foldl (mapWithStep f) (c, out) = (c, (xs.map (fun x => f (c, x))).reverse ++ out) := by
  induction xs generalizing out with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, mapWithStep, ih, List.map_cons, List.reverse_cons,
      List.append_assoc, List.singleton_append]

namespace Poly

 theorem mapWith {α β γ : Type} [Coded α] [Coded β] [Coded γ]
     {f : γ × α → β} (hf : Poly f) :
     Poly (fun p : γ × List α => p.2.map (fun x => f (p.1, x))) := by
   obtain ⟨P, hP⟩ := hf.output_size
   have hstep : Poly (fun p : (γ × List β) × α => mapWithStep f p.1 p.2) :=
     (fst.comp fst).pair (cons.comp ((hf.comp ((fst.comp fst).pair snd)).pair (snd.comp fst)))
   have hfold := foldl hstep (Polynomial.X + Polynomial.X * (P + 1) + 1) (by
     intro xs s j
     rcases s with ⟨c, out⟩
     rw [foldl_mapWithStep]
     let N := bitSize xs + (bitSize c + bitSize out)
     have hx : ∀ x ∈ xs.take j, bitSize (f (c, x)) ≤ P.eval N := by
       intro x hx
       apply (hP _).trans
       apply eval_mono_nat
       have hm := bitSize_mem (List.mem_of_mem_take hx)
       simp only [N, bitSize_prod]; omega
     have hm := bitSize_map_le (xs.take j) (fun x => f (c, x)) (P.eval N) hx
     have ha := bitSize_append ((xs.take j).map (fun x => f (c, x))).reverse out
     rw [bitSize_reverse] at ha
     have hl : (xs.take j).length ≤ N := by
       have h₁ := List.length_take_le' j xs
       have h₂ := length_le_bitSize xs
       simp only [N]; omega
     have hmul := Nat.mul_le_mul_right (P.eval N + 1) hl
     have hs : bitSize c + bitSize out ≤ N := by simp [N]
     simp only [bitSize_prod, Polynomial.eval_add, Polynomial.eval_mul,
       Polynomial.eval_X, Polynomial.eval_one]
     change bitSize c + bitSize (((xs.take j).map (fun x => f (c, x))).reverse ++ out) ≤
       N + N * (P.eval N + 1) + 1
     omega)
   have hp := reverse.comp (snd.comp (hfold.comp (snd.pair
     (fst.pair (const ([] : List β) : Poly (fun _ : γ × List α => []))))))
   convert hp using 1
   funext p
   simp only [Function.comp_apply, foldl_mapWithStep, List.append_nil, List.reverse_reverse]

 theorem flatten {α : Type} [Coded α] : Poly (List.flatten : List (List α) → List α) := by
   have hs : ∀ (a x : List α), bitSize (a ++ x) ≤ bitSize a +
       (Polynomial.X : Polynomial ℕ).eval (bitSize x) := by
     intro a x
     have h := bitSize_append a x
     simp only [Polynomial.eval_X]; omega
   have hp := (foldl_additive append Polynomial.X hs).comp
     ((id : Poly (_root_.id : List (List α) → List (List α))).pair (const ([] : List α)))
   convert hp using 1
   funext xs
   simp only [Function.comp_apply, _root_.id]
   have he : ∀ a : List α, xs.foldl (· ++ ·) a = a ++ xs.flatten := by
     intro a
     induction xs generalizing a with
     | nil => simp
     | cons x xs ih => simp only [List.foldl_cons, ih, List.flatten_cons, List.append_assoc]
   simpa only [List.nil_append] using (he []).symm

 theorem filter {α : Type} [Coded α] {p : α → Bool} (hp : Poly p) : Poly (List.filter p) := by
   have hc : Poly (fun x => if p x then [x] else []) :=
     ite hp (cons.comp (id.pair (const []))) (const [])
   have hf := flatten.comp (map hc)
   convert hf using 1
   funext xs
   induction xs with
   | nil => rfl
   | cons x xs ih =>
     simp only [Function.comp_apply, List.map_cons, List.flatten_cons, List.filter_cons] at *
     by_cases hx : p x = true <;> simp [hx, ih]

 theorem filterWith {α γ : Type} [Coded α] [Coded γ] {p : γ × α → Bool}
     (hp : Poly p) : Poly (fun q : γ × List α => q.2.filter (fun x => p (q.1, x))) := by
   have hc : Poly (fun q : γ × α => if p q then [q.2] else []) :=
     ite hp (cons.comp (snd.pair (const []))) (const [])
   have hf := flatten.comp (mapWith hc)
   convert hf using 1
   funext q
   rcases q with ⟨c, xs⟩
   induction xs with
   | nil => rfl
   | cons x xs ih =>
     simp only [Function.comp_apply, List.map_cons, List.flatten_cons, List.filter_cons] at *
     by_cases hx : p (c, x) = true <;> simp [hx, ih]

end Poly

end Superstring.BitCode

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.BitCode

attribute [fun_prop] Poly
attribute [fun_prop] Poly.id Poly.const Poly.comp Poly.pair Poly.fst Poly.snd
attribute [fun_prop] Poly.cons Poly.ite Poly.reverse Poly.append Poly.length Poly.size
attribute [fun_prop] Poly.not Poly.and Poly.or Poly.eqBool Poly.eq Poly.succ Poly.pred Poly.isZero Poly.add
attribute [fun_prop] Poly.flatten Poly.tail Poly.headD Poly.isEmpty Poly.encoding

namespace Poly

@[fun_prop] theorem mapFn {α β γ : Type} [Coded α] [Coded β] [Coded γ]
    {f : γ × α → β} {xs : γ → List α} (hf : Poly f) (hxs : Poly xs) :
    Poly (fun c => (xs c).map (fun x => f (c, x))) :=
  (mapWith hf).comp (id.pair hxs)

@[fun_prop] theorem filterFn {α γ : Type} [Coded α] [Coded γ]
    {p : γ × α → Bool} {xs : γ → List α} (hp : Poly p) (hxs : Poly xs) :
    Poly (fun c => (xs c).filter (fun x => p (c, x))) :=
  (filterWith hp).comp (id.pair hxs)

 theorem sub : Poly (fun p : ℕ × ℕ => p.1 - p.2) := by
   have he : ∀ j a : ℕ, Nat.pred^[j] a = a - j := by
     intro j; induction j with
     | zero => simp
     | succ j ih => intro a; rw [Function.iterate_succ_apply', ih]; simp only [Nat.pred_eq_sub_one]; omega
   have hi := pred.iterate Polynomial.X (by
     intro n a j _
     rw [he]
     simp only [Polynomial.eval_X, bitSize_prod, bitSize_nat]
     omega)
   convert hi.comp (snd.pair fst) using 1
   funext p; simp only [Function.comp_apply, he]

attribute [fun_prop] sub

 theorem le : Poly (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) := by
   have h := isZero.comp sub
   convert h using 1
   funext p; simp only [Function.comp_apply, decide_eq_decide]; omega

 theorem lt : Poly (fun p : ℕ × ℕ => decide (p.1 < p.2)) := by
   have h := not.comp (le.comp (snd.pair fst))
   convert h using 1
   funext p; simp only [Function.comp_apply, ← decide_not, decide_eq_decide]; omega

attribute [fun_prop] le lt

 theorem max : Poly (fun p : ℕ × ℕ => max p.1 p.2) := by
   have h : Poly (fun p : ℕ × ℕ => if decide (p.1 ≤ p.2) then p.2 else p.1) := by fun_prop
   convert h using 1
   funext p; by_cases hh : p.1 ≤ p.2
   · simp [hh]
   · simp [hh, max_eq_left (Nat.le_of_not_ge hh)]

 theorem min : Poly (fun p : ℕ × ℕ => min p.1 p.2) := by
   have h : Poly (fun p : ℕ × ℕ => if decide (p.1 ≤ p.2) then p.1 else p.2) := by fun_prop
   convert h using 1
   funext p; by_cases hh : p.1 ≤ p.2
   · simp [hh]
   · simp [hh, min_eq_right (Nat.le_of_not_ge hh)]

attribute [fun_prop] max min

 theorem mul : Poly (fun p : ℕ × ℕ => p.1 * p.2) := by
   let step : ℕ × ℕ → ℕ × ℕ := fun p => (p.1, p.2 + p.1)
   have hs : Poly step := by dsimp [step]; fun_prop
   have he : ∀ j (a b : ℕ), step^[j] (a, b) = (a, b + j * a) := by
     intro j; induction j with
     | zero => simp
     | succ j ih => intro a b; rw [Function.iterate_succ_apply', ih]; dsimp [step]; congr 1; ring
   have hi := hs.iterate (Polynomial.X + Polynomial.X * Polynomial.X) (by
     intro n p j hj
     rcases p with ⟨a, b⟩
     rw [he]
     simp only [bitSize_prod, bitSize_nat, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
     nlinarith)
   have hp := snd.comp (hi.comp (fst.pair (snd.pair (const 0))))
   convert hp using 1
   funext p; simp only [Function.comp_apply, he, Nat.zero_add]

attribute [fun_prop] mul

 theorem drop {α : Type} [Coded α] : Poly (fun p : ℕ × List α => p.2.drop p.1) := by
   have he : ∀ n (xs : List α), List.tail^[n] xs = xs.drop n := by
     intro n; induction n with
     | zero => simp
     | succ n ih => intro xs; rw [Function.iterate_succ_apply', ih]; simp [List.tail_drop]
   have hi := (tail : Poly (List.tail : List α → List α)).iterate Polynomial.X (by
     intro n xs j _
     rw [he]
     have h := bitSize_sublist (List.drop_sublist j xs)
     simp only [Polynomial.eval_X, bitSize_prod]; omega)
   convert hi using 1
   funext p; exact (he _ _).symm

attribute [fun_prop] drop

 theorem take {α : Type} [Coded α] : Poly (fun p : ℕ × List α => p.2.take p.1) := by
   have h : Poly (fun p : ℕ × List α => (p.2.reverse.drop (p.2.length - p.1)).reverse) := by fun_prop
   convert h using 1
   funext p
   simp only [List.drop_reverse, List.reverse_reverse, List.take_eq_take_iff]; omega

attribute [fun_prop] take

 theorem getD {α : Type} [Coded α] (d : α) :
     Poly (fun p : List α × ℕ => p.1[p.2]?.getD d) := by
   have h := (headD d).comp (drop.comp (snd.pair fst))
   convert h using 1
   funext p
   simp only [Function.comp_apply, List.headD_eq_head?_getD, List.head?_drop]

end Poly

end Superstring.BitCode

namespace Superstring.BitCode
namespace Poly

@[fun_prop] theorem eqFn {α β : Type} [Coded α] [Coded β] [DecidableEq β]
    {f g : α → β} (hf : Poly f) (hg : Poly g) : Poly (fun a => decide (f a = g a)) :=
  eq.comp (hf.pair hg)

@[fun_prop] theorem leFn {α : Type} [Coded α] {f g : α → ℕ}
    (hf : Poly f) (hg : Poly g) : Poly (fun a => decide (f a ≤ g a)) := le.comp (hf.pair hg)

@[fun_prop] theorem ltFn {α : Type} [Coded α] {f g : α → ℕ}
    (hf : Poly f) (hg : Poly g) : Poly (fun a => decide (f a < g a)) := lt.comp (hf.pair hg)

 theorem anyB : Poly (fun xs : List Bool => xs.any _root_.id) := by
   have hs : ∀ (a x : Bool), bitSize (a || x) ≤ bitSize a + (0 : Polynomial ℕ).eval (bitSize x) := by
     intros; simp only [bitSize, bits_bool, List.length_singleton, Polynomial.eval_zero, Nat.add_zero, le_refl]
   have hp := (foldl_additive or 0 hs).comp ((id : Poly (_root_.id : List Bool → List Bool)).pair (const false))
   convert hp using 1
   funext xs
   have he : ∀ b : Bool, xs.foldl (· || ·) b = (b || xs.any _root_.id) := by
     intro b; induction xs generalizing b with
     | nil => simp
     | cons x xs ih => simp [ih, Bool.or_assoc]
   simp only [Function.comp_apply, _root_.id, he, Bool.false_or]

 theorem allB : Poly (fun xs : List Bool => xs.all _root_.id) := by
   have hp := not.comp (anyB.comp (map not))
   convert hp using 1
   funext xs
   simp only [Function.comp_apply, List.any_map, Function.comp_def, _root_.id]
   exact List.all_eq_not_any_not

@[fun_prop] theorem anyFn {α γ : Type} [Coded α] [Coded γ] {p : γ × α → Bool}
    {xs : γ → List α} (hp : Poly p) (hxs : Poly xs) :
    Poly (fun c => (xs c).any (fun x => p (c, x))) := by
   have h := anyB.comp (mapFn hp hxs)
   convert h using 1
   funext c; simp

@[fun_prop] theorem allFn {α γ : Type} [Coded α] [Coded γ] {p : γ × α → Bool}
    {xs : γ → List α} (hp : Poly p) (hxs : Poly xs) :
    Poly (fun c => (xs c).all (fun x => p (c, x))) := by
   have h := allB.comp (mapFn hp hxs)
   convert h using 1
   funext c; simp

 theorem mem {α : Type} [Coded α] [DecidableEq α] :
    Poly (fun p : α × List α => decide (p.1 ∈ p.2)) := by
   have hf : Poly (fun q : (α × List α) × α => decide (q.1.1 = q.2)) :=
     eq.comp ((fst.comp fst).pair snd)
   have hp := anyFn hf (snd : Poly (Prod.snd : α × List α → List α))
   convert hp using 1
   funext p
   apply Bool.eq_iff_iff.mpr
   simp only [decide_eq_true_eq, List.any_eq_true]
   simp

@[fun_prop] theorem memFn {α γ : Type} [Coded α] [Coded γ] [DecidableEq α]
    {x : γ → α} {xs : γ → List α} (hx : Poly x) (hxs : Poly xs) :
    Poly (fun c => decide (x c ∈ xs c)) := mem.comp (hx.pair hxs)

 theorem sum : Poly (List.sum : List ℕ → ℕ) := by
   have hs : ∀ (a x : ℕ), bitSize (a + x) ≤ bitSize a +
       (Polynomial.X : Polynomial ℕ).eval (bitSize x) := by intros; simp only [bitSize_nat, Polynomial.eval_X]; omega
   have hp := (foldl_additive add Polynomial.X hs).comp
     ((id : Poly (_root_.id : List ℕ → List ℕ)).pair (const 0))
   convert hp using 1
   funext xs
   simp [List.sum_eq_foldl]

attribute [fun_prop] sum

 theorem maxFold : Poly (fun xs : List ℕ => xs.foldl Max.max 0) := by
   have hs : ∀ (a x : ℕ), bitSize (Max.max a x) ≤ bitSize a +
       (Polynomial.X : Polynomial ℕ).eval (bitSize x) := by
     intros; simp only [bitSize_nat, Polynomial.eval_X]; omega
   exact (foldl_additive max Polynomial.X hs).comp
     ((id : Poly (_root_.id : List ℕ → List ℕ)).pair (const 0))

attribute [fun_prop] maxFold

end Poly

 def rangeStep (p : ℕ × List ℕ) : ℕ × List ℕ := (p.1 + 1, p.1 :: p.2)

 theorem iterate_rangeStep (j a : ℕ) (out : List ℕ) :
     rangeStep^[j] (a, out) = (a + j, (List.range' a j).reverse ++ out) := by
   induction j with
   | zero => simp
   | succ j ih =>
     rw [Function.iterate_succ_apply', ih]
     simp only [rangeStep, List.range'_1_concat, List.reverse_append, List.reverse_singleton,
       List.cons_append]
     congr 1

namespace Poly

 theorem range : Poly (List.range : ℕ → List ℕ) := by
   have hs : Poly rangeStep := by unfold rangeStep; fun_prop
   have hi := hs.iterate (4 * Polynomial.X * Polynomial.X + 4 * Polynomial.X + 4) (by
     intro n p j hj
     rcases p with ⟨a, out⟩
     rw [iterate_rangeStep]
     have hh := bitSize_map_le (List.range' a j) (_root_.id : ℕ → ℕ) (a + j + 1)
       (fun x hx => by simp only [_root_.id, bitSize_nat]; have := List.mem_range'.mp hx; omega)
     simp only [List.map_id, List.length_range'] at hh
     have ha := bitSize_append (List.range' a j).reverse out
     rw [bitSize_reverse] at ha
     simp only [bitSize_prod, bitSize_nat, Polynomial.eval_add, Polynomial.eval_mul,
       Polynomial.eval_ofNat, Polynomial.eval_X]
     nlinarith)
   have hp := reverse.comp (snd.comp (hi.comp ((id : Poly (_root_.id : ℕ → ℕ)).pair (const (0, ([] : List ℕ))))))
   convert hp using 1
   funext n
   simp only [Function.comp_apply, _root_.id, iterate_rangeStep, Nat.zero_add,
     List.append_nil, List.reverse_reverse, ← List.range_eq_range']

attribute [fun_prop] range getD

end Poly
end Superstring.BitCode

namespace Superstring.BitCode

 def equal {α : Type} [DecidableEq α] (a b : α) : Bool := decide (a = b)
 def less (a b : ℕ) : Bool := decide (a < b)
 def lessEq (a b : ℕ) : Bool := decide (a ≤ b)

namespace Poly

@[fun_prop] theorem equal {α : Type} [Coded α] [DecidableEq α] :
    Poly (fun p : α × α => Superstring.BitCode.equal p.1 p.2) := eq
@[fun_prop] theorem less : Poly (fun p : ℕ × ℕ => Superstring.BitCode.less p.1 p.2) := lt
@[fun_prop] theorem lessEq : Poly (fun p : ℕ × ℕ => Superstring.BitCode.lessEq p.1 p.2) := le

/-- Output reinterpretation executes exactly the same bits, not a hidden function. -/
 theorem recode {α β γ : Type} [Coded α] [Coded β] [Coded γ]
    {f : α → β} {g : α → γ} (hf : Poly f) (he : ∀ a, bits (g a) = bits (f a)) : Poly g := by
   obtain ⟨K, inst, i, o, b, P, hb⟩ := hf
   refine ⟨K, inst, i, o, b, P, ?_⟩
   intro a
   simpa only [he] using hb a

@[fun_prop] theorem inl {α β : Type} [Coded α] [Coded β] : Poly (Sum.inl : α → α ⊕ β) := by
   exact ((const false).pair (id : Poly (_root_.id : α → α))).recode (fun a => rfl)

@[fun_prop] theorem inr {α β : Type} [Coded α] [Coded β] : Poly (Sum.inr : β → α ⊕ β) := by
   exact ((const true).pair (id : Poly (_root_.id : β → β))).recode (fun a => rfl)

 theorem headDWith {α : Type} [Coded α] : Poly (fun p : List α × α => p.1.headD p.2) := by
   convert listCasesWith (id : Poly (_root_.id : α → α))
     (fst : Poly (Prod.fst : α × (List α × α) → α)) using 1
   funext p; rcases p with ⟨xs, a⟩; cases xs <;> rfl

attribute [fun_prop] headDWith

end Poly

 def cappedStep {α : Type} [Coded α] (f : α → α) (p : ℕ × α) : ℕ × α :=
   (p.1, if lessEq (bitSize (f p.2)) p.1 then f p.2 else p.2)

 theorem iterate_cappedStep_size {α : Type} [Coded α] (f : α → α) (n B : ℕ) (a : α) :
     ((cappedStep f)^[n] (B, a)).1 = B ∧
     bitSize (((cappedStep f)^[n] (B, a)).2) ≤ max B (bitSize a) := by
   induction n with
   | zero => exact ⟨rfl, le_max_right _ _⟩
   | succ n ih =>
     rw [Function.iterate_succ_apply']
     simp only [cappedStep, ih.1, lessEq, decide_eq_true_eq]
     exact ⟨True.intro, by split <;> omega⟩

 theorem iterate_cappedStep_eq {α : Type} [Coded α] (f : α → α) (n B : ℕ) (a : α)
     (h : ∀ j, 1 ≤ j → j ≤ n → bitSize (f^[j] a) ≤ B) :
     (cappedStep f)^[n] (B, a) = (B, f^[n] a) := by
   induction n with
   | zero => rfl
   | succ n ih =>
     rw [Function.iterate_succ_apply', ih (fun j hj hjn => h j hj (by omega))]
     have hh := h (n + 1) (by omega) le_rfl
     rw [Function.iterate_succ_apply'] at hh ⊢
     simp only [cappedStep, lessEq, decide_eq_true_eq, ite_eq_left hh]

namespace Poly

 theorem cappedStep {α : Type} [Coded α] {f : α → α} (hf : Poly f) : Poly (cappedStep f) := by
   unfold Superstring.BitCode.cappedStep
   fun_prop

/-- A genuine bounded-workspace loop. The clock and workspace cap are unary
input data. Every attempted step is executed/charged before its size check. -/
 theorem cappedIterate {α : Type} [Coded α] {f : α → α} (hf : Poly f) :
     Poly (fun p : ℕ × (ℕ × α) => ((Superstring.BitCode.cappedStep f)^[p.1] p.2).2) := by
   apply snd.comp
   apply (cappedStep hf).iterate (2 * Polynomial.X)
   intro n p j _
   rcases p with ⟨B, a⟩
   have hh := iterate_cappedStep_size f j B a
   rw [← Prod.eta ((Superstring.BitCode.cappedStep f)^[j] (B, a)), bitSize_prod, hh.1]
   simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X, bitSize_prod, bitSize_nat]
   omega

end Poly

 def uniqueStep {α : Type} [DecidableEq α] (a : List α) (x : α) : List α :=
   if x ∈ a then a else x :: a
 def unique {α : Type} [DecidableEq α] (xs : List α) : List α := xs.foldl uniqueStep []

 theorem mem_foldl_uniqueStep {α : Type} [DecidableEq α] (xs a : List α) (x : α) :
     x ∈ xs.foldl uniqueStep a ↔ x ∈ xs ∨ x ∈ a := by
   induction xs generalizing a with
   | nil => simp
   | cons y ys ih =>
     simp only [List.foldl_cons, ih, List.mem_cons, uniqueStep]
     by_cases hy : y ∈ a <;> simp only [hy, ite_true, ite_false, List.mem_cons] <;> aesop

 theorem nodup_foldl_uniqueStep {α : Type} [DecidableEq α] (xs a : List α) (ha : a.Nodup) :
     (xs.foldl uniqueStep a).Nodup := by
   induction xs generalizing a with
   | nil => exact ha
   | cons x xs ih =>
     apply ih
     unfold uniqueStep
     split
     · exact ha
     · exact List.nodup_cons.mpr ⟨‹_›, ha⟩

@[simp] theorem mem_unique {α : Type} [DecidableEq α] (xs : List α) (x : α) :
     x ∈ unique xs ↔ x ∈ xs := by simp [unique, mem_foldl_uniqueStep]
 theorem nodup_unique {α : Type} [DecidableEq α] (xs : List α) : (unique xs).Nodup :=
   nodup_foldl_uniqueStep xs [] List.nodup_nil

namespace Poly

 theorem unique {α : Type} [Coded α] [DecidableEq α] : Poly (unique : List α → List α) := by
   have hf : Poly (fun p : List α × α => uniqueStep p.1 p.2) := by
     have hp : Poly (fun p : List α × α => decide (p.2 ∈ p.1)) := mem.comp (snd.pair fst)
     simpa only [uniqueStep, decide_eq_true_eq, Function.comp_apply] using
       ite hp fst (cons.comp (snd.pair fst))
   have hs : ∀ (a : List α) (x : α), bitSize (uniqueStep a x) ≤ bitSize a +
       (Polynomial.X + 1 : Polynomial ℕ).eval (bitSize x) := by
     intro a x
     unfold uniqueStep
     simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
     split
     · omega
     · simp only [bitSize_cons]; omega
   exact (foldl_additive hf (Polynomial.X + 1) hs).comp
     ((id : Poly (_root_.id : List α → List α)).pair (const []))

attribute [fun_prop] unique

 theorem product {α β : Type} [Coded α] [Coded β] :
     Poly (fun p : List α × List β => p.1.product p.2) := by
   have hi : Poly (fun q : (List α × List β) × α =>
       q.1.2.map (fun b => (q.2,b))) :=
     mapFn ((snd.comp fst).pair snd) (snd.comp fst)
   have hp : Poly (fun p : List α × List β =>
       (p.1.map (fun a => p.2.map (fun b => (a,b)))).flatten) :=
     flatten.comp (mapFn hi fst)
   convert hp using 1
   funext p
   induction p.1 with
   | nil => rfl
   | cons a as ih => simpa only [List.product, List.flatMap_cons, List.map_cons,
       List.flatten_cons] using congrArg (p.2.map (Prod.mk a) ++ ·) ih

attribute [fun_prop] product

end Poly
end Superstring.BitCode

namespace Superstring.BitCode

def residueStep (q : ℕ × ℕ) : ℕ × ℕ :=
  (q.1, if equal (q.2 + 1) q.1 then 0 else q.2 + 1)

theorem iterate_residueStep_bound (p r n : ℕ) :
    (residueStep^[n] (p,r)).1 = p ∧ (residueStep^[n] (p,r)).2 ≤ r + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    simp only [residueStep, ih.1]
    exact ⟨True.intro, by split <;> omega⟩

theorem iterate_residueStep (p n : ℕ) : residueStep^[n] (p,0) = (p,n % p) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [residueStep, equal, decide_eq_true_eq]
    congr 1
    by_cases hp : p = 0
    · subst p; simp
    · have hp' : 0 < p := Nat.pos_of_ne_zero hp
      have hr := Nat.mod_lt n hp'
      rw [← Nat.mod_add_mod n p 1]
      by_cases he : n % p + 1 = p
      · simp [he]
      · rw [ite_eq_right he]
        exact (Nat.mod_eq_of_lt (show n % p + 1 < p by omega)).symm

namespace Poly

@[fun_prop] theorem mod : Poly (fun q : ℕ × ℕ => q.1 % q.2) := by
  have hs : Poly residueStep := by unfold residueStep; fun_prop
  have hi := hs.iterate (2 * Polynomial.X) (by
    intro n q j hj
    rcases q with ⟨p,r⟩
    have hh := iterate_residueStep_bound p r j
    rw [← Prod.eta (residueStep^[j] (p,r)), bitSize_prod, hh.1]
    simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
      bitSize_prod, bitSize_nat]
    omega)
  have hp := snd.comp (hi.comp (fst.pair (snd.pair (const 0))))
  convert hp using 1
  funext q
  simp only [Function.comp_apply, iterate_residueStep]

end Poly

def intView : ℤ → ℕ ⊕ ℕ
  | .ofNat n => .inl n
  | .negSucc n => .inr n

theorem Parses.precomp {α β : Type} {e : β → List Bool} (h : Parses e) (f : α → β) :
    Parses (e ∘ f) := by
  obtain ⟨K, i, b, c, hb⟩ := h
  exact ⟨K, i, b, c, fun a t z => hb (f a) t z⟩

instance codedInt : Coded ℤ where
  code := bits ∘ intView
  parses := Coded.parses.precomp intView
  injective := by
    intro a b h
    have hh := Coded.injective h
    cases a <;> cases b <;> simp only [intView, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl] at hh
    · exact congrArg Int.ofNat hh
    · exact congrArg Int.negSucc hh

namespace Poly

 theorem intCases {β : Type} [Coded β] {f g : ℕ → β} (hf : Poly f) (hg : Poly g) :
    Poly (fun z : ℤ => match z with | .ofNat n => f n | .negSucc n => g n) := by
  convert (sumCases hf hg).reencode intView (fun _ => rfl) using 1
  funext z; cases z <;> rfl

 theorem intCasesWith {β γ : Type} [Coded β] [Coded γ]
     {f g : ℕ × γ → β} (hf : Poly f) (hg : Poly g) :
     Poly (fun q : ℤ × γ => match q.1 with | .ofNat n => f (n,q.2) | .negSucc n => g (n,q.2)) := by
   let view : ℤ × γ → (ℕ × γ) ⊕ (ℕ × γ) := fun q => match q.1 with
     | .ofNat n => .inl (n,q.2)
     | .negSucc n => .inr (n,q.2)
   convert (sumCases hf hg).reencode view (by
     intro q; rcases q with ⟨z,c⟩; cases z <;> rfl) using 1
   funext q; rcases q with ⟨z,c⟩; cases z <;> rfl

@[fun_prop] theorem ofNat : Poly (Int.ofNat : ℕ → ℤ) :=
  (inl : Poly (Sum.inl : ℕ → ℕ ⊕ ℕ)).recode (fun _ => rfl)
@[fun_prop] theorem negSucc : Poly (Int.negSucc : ℕ → ℤ) :=
  (inr : Poly (Sum.inr : ℕ → ℕ ⊕ ℕ)).recode (fun _ => rfl)
@[fun_prop] theorem toNat : Poly (Int.toNat : ℤ → ℕ) := intCases id (const 0)
@[fun_prop] theorem natAbs : Poly (Int.natAbs : ℤ → ℕ) := intCases id succ

end Poly
end Superstring.BitCode

namespace Superstring.BitCode.Poly

@[fun_prop] theorem subNatNat : Poly (fun q : ℕ × ℕ => Int.subNatNat q.1 q.2) := by
  have h : Poly (fun q : ℕ × ℕ =>
      if BitCode.less q.1 q.2 then Int.negSucc (q.2 - q.1 - 1) else Int.ofNat (q.1 - q.2)) := by fun_prop
  convert h using 1
  funext q
  simp only [BitCode.less, decide_eq_true_eq, Int.subNatNat_eq_coe, Int.ofNat_eq_natCast]
  split <;> omega

@[fun_prop] theorem negInt : Poly (fun z : ℤ => -z) := by
  have hf : Poly (fun n : ℕ => Int.subNatNat 0 n) := by fun_prop
  convert intCases hf (ofNat.comp succ) using 1
  funext z; cases z <;> simp [Int.subNatNat_eq_coe]

@[fun_prop] theorem addInt : Poly (fun q : ℤ × ℤ => q.1 + q.2) := by
  have hf : Poly (fun q : ℤ × ℕ => match q.1 with
      | .ofNat n => Int.ofNat (q.2 + n)
      | .negSucc n => Int.subNatNat q.2 (n+1)) := by
    exact intCasesWith
      (show Poly (fun q : ℕ × ℕ => Int.ofNat (q.2 + q.1)) by fun_prop)
      (show Poly (fun q : ℕ × ℕ => Int.subNatNat q.2 (q.1+1)) by fun_prop)
  have hg : Poly (fun q : ℤ × ℕ => match q.1 with
      | .ofNat n => Int.subNatNat n (q.2+1)
      | .negSucc n => Int.negSucc (q.2+n+1)) := by
    exact intCasesWith
      (show Poly (fun q : ℕ × ℕ => Int.subNatNat q.1 (q.2+1)) by fun_prop)
      (show Poly (fun q : ℕ × ℕ => Int.negSucc (q.2+q.1+1)) by fun_prop)
  have hh := intCasesWith (hf.comp (snd.pair fst)) (hg.comp (snd.pair fst))
  convert hh using 1
  funext q; rcases q with ⟨a,b⟩; cases a <;> cases b <;> rfl

@[fun_prop] theorem subInt : Poly (fun q : ℤ × ℤ => q.1 - q.2) := by
  convert addInt.comp (fst.pair (negInt.comp snd)) using 1
  funext q
  exact sub_eq_add_neg q.1 q.2

@[fun_prop] theorem modIntNat : Poly (fun q : ℤ × ℕ => (q.1 % (q.2 : ℤ)).toNat) := by
  have hf : Poly (fun q : ℕ × ℕ => q.1 % q.2) := mod
  have hg : Poly (fun q : ℕ × ℕ => q.2 - (q.1 % q.2 + 1)) := by fun_prop
  convert intCasesWith hf hg using 1
  funext q; rcases q with ⟨a,b⟩; cases a with
  | ofNat n => rfl
  | negSucc n => simp only [Int.negSucc_emod_ofNat, Int.subNatNat_eq_coe, Int.toNat_sub]

end Superstring.BitCode.Poly

namespace Superstring.BitCode.Poly
@[fun_prop] theorem natCastInt : Poly (fun n : ℕ => (n : ℤ)) := ofNat
end Superstring.BitCode.Poly

namespace Superstring.BitCode
/-- Freeze the equality implementation at the abstract element type. Nested
lists may otherwise elaborate different, extensionally equal BEq instances. -/
def member {α : Type} [DecidableEq α] (a : α) (xs : List α) : Bool := decide (a ∈ xs)
@[simp] theorem member_eq {α : Type} [DecidableEq α] (a : α) (xs : List α) :
    member a xs = true ↔ a ∈ xs := decide_eq_true_iff
namespace Poly
@[fun_prop] theorem member {α : Type} [Coded α] [DecidableEq α] :
    Poly (fun q : α × List α => BitCode.member q.1 q.2) := mem
end Poly
end Superstring.BitCode

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.Computable
open BitCode
variable {α : Type} [DecidableEq α] [Inhabited α] [Coded α]

def nth (xs : List α) (i : ℕ) : α := xs[i]?.getD default
omit [DecidableEq α] in
@[fun_prop] theorem poly_nth {γ : Type} [Coded γ] {xs : γ → List α} {i : γ → ℕ}
    (hx : Poly xs) (hi : Poly i) : Poly (fun q => nth (xs q) (i q)) :=
  (BitCode.Poly.getD default).comp (hx.pair hi)

/-- All indices and loop counters below are explicitly represented unary data. -/
def occurs (T s : List α) (j : ℕ) : Bool :=
  lessEq (j + s.length) T.length && equal ((T.drop j).take s.length) s

def infixB (s T : List α) : Bool :=
  (List.range (T.length + 1)).any (fun j => occurs T s j)

def text (v : List α) (p : ℕ) (x : ℤ) : α :=
  nth v ((x % (p : ℤ)).toNat)

def matchesB (v : List α) (p : ℕ) (w : List α) : Bool :=
  (List.range w.length).all (fun i => equal (nth w i) (text v p i))

def blocks (v : List α) (p : ℕ) (s r : List α) (j : ℕ) : Bool :=
  less 0 j && less (j + s.length) r.length && occurs r s j &&
  ((List.range r.length).all (fun h =>
    !(less 0 h && less (h+1) r.length) ||
    equal (nth r h) (text v p ((h : ℤ) - j)))) &&
  !equal (nth r 0) (text v p (-(j : ℤ))) &&
  !equal (nth r (r.length-1)) (text v p (((r.length-1 : ℕ) : ℤ) - j))

def coefficient (v : List α) (p : ℕ) (s r : List α) : ℕ :=
  ((List.range (r.length + 1)).filter (fun j => blocks v p s r j)).length

omit [Inhabited α] in
@[fun_prop] theorem poly_occurs : Poly (fun q : List α × List α × ℕ => occurs q.1 q.2.1 q.2.2) := by
  unfold occurs
  fun_prop
omit [Inhabited α] in
@[fun_prop] theorem poly_infix : Poly (fun q : List α × List α => infixB q.1 q.2) := by
  unfold infixB
  exact BitCode.Poly.anyFn (p := fun q : (List α × List α) × ℕ => occurs q.1.2 q.1.1 q.2)
    (by fun_prop) (by fun_prop)
omit [DecidableEq α] in
@[fun_prop] theorem poly_text : Poly (fun q : List α × ℕ × ℤ => text q.1 q.2.1 q.2.2) := by
  unfold text
  exact (BitCode.Poly.getD default).comp (BitCode.Poly.fst.pair
    (BitCode.Poly.modIntNat.comp ((BitCode.Poly.snd.comp BitCode.Poly.snd).pair (BitCode.Poly.fst.comp BitCode.Poly.snd))))
@[fun_prop] theorem poly_matches : Poly (fun q : List α × ℕ × List α => matchesB q.1 q.2.1 q.2.2) := by
  unfold matchesB
  exact BitCode.Poly.allFn (p := fun q : (List α × ℕ × List α) × ℕ =>
    equal (nth q.1.2.2 q.2) (text q.1.1 q.1.2.1 q.2)) (by fun_prop) (by fun_prop)
@[fun_prop] theorem poly_blocks : Poly (fun q : List α × ℕ × List α × List α × ℕ =>
    blocks q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  have hi : Poly (fun q : (List α × ℕ × List α × List α × ℕ) × ℕ =>
      !(less 0 q.2 && less (q.2+1) q.1.2.2.2.1.length) ||
      equal (nth q.1.2.2.2.1 q.2) (text q.1.1 q.1.2.1 ((q.2 : ℤ) - q.1.2.2.2.2))) := by fun_prop
  have ha : Poly (fun q : List α × ℕ × List α × List α × ℕ =>
      (List.range q.2.2.2.1.length).all (fun h =>
        !(less 0 h && less (h+1) q.2.2.2.1.length) ||
        equal (nth q.2.2.2.1 h) (text q.1 q.2.1 ((h : ℤ) - q.2.2.2.2)))) :=
    BitCode.Poly.allFn hi (by fun_prop)
  unfold blocks
  fun_prop
@[fun_prop] theorem poly_coefficient : Poly (fun q : List α × ℕ × List α × List α =>
    coefficient q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold coefficient
  apply BitCode.Poly.length.comp
  exact BitCode.Poly.filterFn (p := fun q : (List α × ℕ × List α × List α) × ℕ =>
    blocks q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2) (by fun_prop) (by fun_prop)

omit [Inhabited α] [Coded α] in
theorem occurs_eq (T s : List α) (j : ℕ) : occurs T s j = true ↔ Counts.Occurs T s j := by
  simp only [occurs, Bool.and_eq_true, lessEq, equal, decide_eq_true_eq, Counts.Occurs]
  constructor
  · rintro ⟨hb,he⟩
    refine ⟨hb, fun i => ?_⟩
    have h := congrArg (fun w : List α => w[i.val]?) he
    simpa only [List.getElem?_take, ite_eq_left i.isLt, List.getElem?_drop] using h
  · rintro ⟨hb,he⟩
    refine ⟨hb, List.ext_getElem? (fun i => ?_)⟩
    by_cases hi : i < s.length
    · simpa only [List.getElem?_take, ite_eq_left hi, List.getElem?_drop] using he ⟨i,hi⟩
    · rw [List.getElem?_take, ite_eq_right hi, List.getElem?_eq_none_iff.mpr (by omega)]

omit [Inhabited α] [Coded α] in
theorem infix_eq (s T : List α) : infixB s T = true ↔ s <:+: T := by
  simp only [infixB, List.any_eq_true, List.mem_range, occurs_eq]
  constructor
  · rintro ⟨j,_,hj⟩; exact hj.infix
  · rintro ⟨a,b,rfl⟩
    refine ⟨a.length, by simp, ?_⟩
    apply (occurs_eq _ _ _).mp
    simp [occurs, lessEq, equal]

omit [DecidableEq α] [Coded α] in
theorem text_eq (v : List α) (p : ℕ) (x : ℤ) : text v p x = Counts.finiteText v p x := by
  simp only [text, nth, Counts.finiteText, List.getElem!_eq_getElem?_getD]

omit [Coded α] in
theorem matches_eq (v : List α) (p : ℕ) (w : List α) :
    matchesB v p w = true ↔ Counts.Matches (Counts.finiteText v p) w := by
  simp only [matchesB, List.all_eq_true, List.mem_range, Counts.Matches]
  constructor
  · intro h i
    have hh : nth w i.val = text v p i.val := of_decide_eq_true (h i.val i.isLt)
    rw [List.getElem?_eq_getElem i.isLt]
    exact congrArg some (by simpa only [nth, List.getElem?_eq_getElem i.isLt, Option.getD_some, text_eq] using hh)
  · intro h i hi
    apply decide_eq_true
    simpa only [nth, List.getElem?_eq_getElem hi, Option.getD_some, text_eq, Option.some.injEq] using h ⟨i,hi⟩

end Superstring.Computable

namespace Superstring.Computable
open BitCode
variable {α : Type} [DecidableEq α] [Inhabited α]

omit [DecidableEq α] in
theorem nth_eq_iff {r : List α} {i : ℕ} (hi : i < r.length) (a : α) :
    nth r i = a ↔ r[i]? = some a := by
  simp only [nth, List.getElem?_eq_getElem hi, Option.getD_some, Option.some.injEq]

theorem blocks_eq (v : List α) (p : ℕ) (s r : List α) (j : ℕ) :
    blocks v p s r j = true ↔ Counts.Block (Counts.finiteText v p) s r j := by
  have hi (h : ℕ) :
      (!(less 0 h && less (h+1) r.length) ||
        equal (nth r h) (text v p ((h : ℤ) - j))) = true ↔
      (0 < h → h+1 < r.length → nth r h = text v p ((h : ℤ) - j)) := by
    simp only [less, equal, Bool.or_eq_true, Bool.not_eq_true_eq_eq_false, Bool.and_eq_false_iff,
      decide_eq_false_iff_not, decide_eq_true_eq]
    tauto
  have ha : ((List.range r.length).all (fun h =>
      !(less 0 h && less (h+1) r.length) ||
      equal (nth r h) (text v p ((h : ℤ) - j)))) = true ↔
      ∀ h : Fin r.length, 0 < h.val → h.val + 1 < r.length →
        r[h.val]? = some (Counts.finiteText v p ((h.val : ℤ) - j)) := by
    simp only [List.all_eq_true, List.mem_range, hi]
    constructor
    · intro h i hi₀ hi₁
      exact (nth_eq_iff i.isLt _).mp (by simpa only [text_eq] using h i.val i.isLt hi₀ hi₁)
    · intro h i hilen hi₀ hi₁
      exact (nth_eq_iff hilen _).mpr (by simpa only [text_eq] using h ⟨i,hilen⟩ hi₀ hi₁)
  by_cases hj : 0 < j
  · by_cases hr : j + s.length < r.length
    · have hr0 : 0 < r.length := by omega
      have hr1 : r.length - 1 < r.length := by omega
      simp only [blocks, Bool.and_eq_true, ha, occurs_eq, Bool.not_eq_true_eq_eq_false]
      have hj' : 1 ≤ j := by omega
      simp only [less, equal, decide_eq_true_eq, decide_eq_false_iff_not,
        text_eq, nth_eq_iff hr0, nth_eq_iff hr1, Counts.Block, hj, hr, hj', true_and]
      tauto
    · simp [blocks, less, hr, Counts.Block]
  · have hj' : ¬1 ≤ j := by omega
    simp [blocks, less, hj, Counts.Block, hj']

end Superstring.Computable

namespace Superstring.Computable
open BitCode

theorem length_filter_range_card (n : ℕ) (b : ℕ → Bool) (P : ℕ → Prop) [DecidablePred P]
    (hb : ∀ i, b i = true ↔ P i) :
    ((List.range n).filter b).length = Fintype.card {i : Fin n // P i.val} := by
  let F := ((List.range n).filter b).toFinset
  have hm (i : ℕ) : i ∈ F ↔ i < n ∧ P i := by
    simp only [F, List.mem_toFinset, List.mem_filter, List.mem_range, hb]
  let e : {i : Fin n // P i.val} ≃ F := {
    toFun := fun i => ⟨i.val.val, (hm _).mpr ⟨i.val.isLt,i.property⟩⟩
    invFun := fun i => ⟨⟨i.val, ((hm _).mp i.property).1⟩, ((hm _).mp i.property).2⟩
    left_inv := fun i => by rfl
    right_inv := fun i => by rfl }
  have he := Fintype.card_congr e
  rw [Fintype.card_coe, List.toFinset_card_of_nodup (List.nodup_range.filter b)] at he
  exact he.symm

variable {α : Type} [DecidableEq α] [Inhabited α]

theorem coefficient_eq (v : List α) (p : ℕ) (s r : List α) :
    coefficient v p s r = Counts.coefficient (Counts.finiteText v p) s r :=
  length_filter_range_card _ _ _ (fun j => blocks_eq v p s r j)


def subwords (s : List α) : List (List α) := unique
  (((List.range (s.length+1)).map (fun i =>
    (List.range (s.length+1)).map (fun n => (s.drop i).take n))).flatten)

def vertices (S : List (List α)) : List (List α) := unique ([] :: (S.map subwords).flatten)

def required (S : List (List α)) : List (List α) := (unique S).filter (fun s =>
  !s.isEmpty && S.all (fun t => !infixB s t || equal t s))

def alphabet (S : List (List α)) : List α := unique S.flatten

omit [Inhabited α] in
theorem mem_subwords (w s : List α) : w ∈ subwords s ↔ w <:+: s := by
  simp only [subwords, mem_unique, List.mem_flatten, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨xs,⟨i,_,rfl⟩,hw⟩
    obtain ⟨n,_,rfl⟩ := List.mem_map.mp hw
    exact (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix
  · rintro ⟨a,b,rfl⟩
    refine ⟨_,⟨a.length, by simp, rfl⟩, ?_⟩
    apply List.mem_map.mpr
    refine ⟨w.length, List.mem_range.mpr (by simp; omega), ?_⟩
    simp

omit [Inhabited α] in
theorem vertices_eq (S : List (List α)) : (vertices S).toFinset = Input.vertices S := by
  ext w
  simp only [List.mem_toFinset, vertices, mem_unique, List.mem_cons, List.mem_flatten,
    List.mem_map, Input.mem_vertices]
  constructor
  · rintro (rfl | ⟨ws,⟨s,hs,rfl⟩,hw⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨s,hs,(mem_subwords _ _).mp hw⟩
  · rintro (rfl | ⟨s,hs,hw⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨subwords s,⟨s,hs,rfl⟩,(mem_subwords _ _).mpr hw⟩

omit [Inhabited α] in
theorem required_eq (S : List (List α)) : (required S).toFinset = Input.core S := by
  ext w
  simp only [required, List.mem_toFinset, List.mem_filter, mem_unique, Bool.and_eq_true,
    Bool.not_eq_true_eq_eq_false, List.isEmpty_eq_false_iff, List.all_eq_true, Bool.or_eq_true,
    equal, decide_eq_true_eq, Input.mem_core]
  have h (t : List α) : infixB w t = false ↔ ¬w <:+: t := by
    rw [Bool.eq_false_iff]
    exact not_congr (infix_eq _ _)
  simp only [h]
  constructor
  · rintro ⟨hw,hn,hh⟩
    exact ⟨hw,hn,fun t ht hwt => (hh t ht).resolve_left (not_not.mpr hwt)⟩
  · rintro ⟨hw,hn,hh⟩
    refine ⟨hw,hn,fun t ht => ?_⟩
    by_cases hwt : w <:+: t
    · exact Or.inr (hh t ht hwt)
    · exact Or.inl hwt

omit [Inhabited α] in
theorem alphabet_eq (S : List (List α)) : (alphabet S).toFinset = Input.alphabet S := by
  ext a
  simp only [alphabet, Input.alphabet, List.mem_toFinset, mem_unique]

end Superstring.Computable

namespace Superstring.Computable
open BitCode
variable {α : Type} [DecidableEq α] [Coded α]

@[fun_prop] theorem poly_subwords : Poly (subwords : List α → List (List α)) := by
  have hi : Poly (fun q : List α × ℕ =>
      (List.range (q.1.length+1)).map (fun n => (q.1.drop q.2).take n)) :=
    BitCode.Poly.mapFn (f := fun q : (List α × ℕ) × ℕ => (q.1.1.drop q.1.2).take q.2)
      (by fun_prop) (by fun_prop)
  unfold subwords
  exact BitCode.Poly.unique.comp (BitCode.Poly.flatten.comp (BitCode.Poly.mapFn hi (by fun_prop)))

@[fun_prop] theorem poly_vertices : Poly (vertices : List (List α) → List (List α)) := by
  unfold vertices
  have hm : Poly (fun S : List (List α) => (S.map subwords).flatten) :=
    BitCode.Poly.flatten.comp (BitCode.Poly.map (poly_subwords (α := α)))
  have hc : Poly (fun S : List (List α) => ([] : List α) :: (S.map subwords).flatten) := by
    exact (BitCode.Poly.cons (α := List α)).comp ((BitCode.Poly.const ([] : List α)).pair hm)
  exact BitCode.Poly.unique.comp hc

@[fun_prop] theorem poly_required : Poly (required : List (List α) → List (List α)) := by
  have ha : Poly (fun q : List (List α) × List α =>
      q.1.all (fun t => !infixB q.2 t || equal t q.2)) :=
    BitCode.Poly.allFn (p := fun q : (List (List α) × List α) × List α =>
      !infixB q.1.2 q.2 || equal q.2 q.1.2) (by fun_prop) (by fun_prop)
  unfold required
  exact BitCode.Poly.filterFn (p := fun q : List (List α) × List α =>
    !q.2.isEmpty && q.1.all (fun t => !infixB q.2 t || equal t q.2))
    (by fun_prop) (by fun_prop)

@[fun_prop] theorem poly_alphabet : Poly (alphabet : List (List α) → List α) := by
  unfold alphabet
  exact BitCode.Poly.unique.comp BitCode.Poly.flatten

end Superstring.Computable

namespace Superstring.Computable
open BitCode
variable {α : Type} [DecidableEq α]

abbrev DataCode (α : Type) := List (List α) × List (List α) × List α
abbrev Table (α : Type) := List (List α × ℕ)

def dataCode (S : List (List α)) : DataCode α := (vertices S, required S, alphabet S)

def decodeData (d : DataCode α) : Counts.Data α :=
  ⟨d.1.toFinset, d.2.1.toFinset, d.2.2.toFinset⟩

theorem decode_dataCode (S : List (List α)) : decodeData (dataCode S) = Input.data S := by
  simp only [decodeData, dataCode, vertices_eq, required_eq, alphabet_eq, Input.data]

/-- A finite association table; every stage is materialized before the next. -/
def lookup (t : Table α) (w : List α) : ℕ :=
  ((t.filter (fun e => equal e.1 w)).map Prod.snd).headD 0

theorem lookup_map (V : List (List α)) (f : List α → ℕ) (w : List α) :
    lookup (V.map (fun v => (v,f v))) w = if w ∈ V then f w else 0 := by
  induction V with
  | nil => simp [lookup]
  | cons v V ih =>
    by_cases hv : v = w
    · subst v; simp [lookup, equal]
    · simp only [List.map_cons, lookup, List.filter_cons, equal, decide_eq_true_eq,
        ite_eq_right hv, List.mem_cons] at *
      rw [ih]
      simp only [eq_comm (a := w) (b := v), hv, false_or]

theorem sum_map_finset {β : Type} [DecidableEq β] (xs : List β) (hn : xs.Nodup)
    (f : β → ℕ) : (xs.map f).sum = ∑ x ∈ xs.toFinset, f x := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := List.nodup_cons.mp hn
    have hnx : x ∉ xs.toFinset := by simpa only [List.mem_toFinset] using hh.1
    rw [List.map_cons, List.sum_cons, List.toFinset_cons, Finset.sum_insert hnx, ih hh.2]

theorem max_map_finset {β : Type} [DecidableEq β] (xs : List β) (f : β → ℕ) :
    (xs.map f).foldl Max.max 0 = xs.toFinset.sup f := by
  have h : ∀ a : ℕ, (xs.map f).foldl Max.max a = max a (xs.toFinset.sup f) := by
    intro a
    induction xs generalizing a with
    | nil => simp
    | cons x xs ih => simp only [List.map_cons, List.foldl_cons, ih,
        List.toFinset_cons, Finset.sup_insert, max_assoc]
  simpa using h 0

variable [Inhabited α]

def blocking (d : DataCode α) (t : Table α) (v : List α) (p : ℕ) (w : List α) : ℕ :=
  (d.1.map (fun r => coefficient v p w r * lookup t r)).sum

def rule (d : DataCode α) (t : Table α) (w v : List α) (p k : ℕ) : ℕ :=
  if less 0 p && less 0 k && !w.isEmpty && equal (w.length + k*p) v.length &&
      matchesB v p v && matchesB v p w then
    if less (blocking d t v p v) (lookup t v) then blocking d t v p w + k + 1 else 0
  else 0

def rulesFor (d : DataCode α) (t : Table α) (w v : List α) : ℕ :=
  ((List.range (v.length+1)).map (fun p =>
    ((List.range (v.length+1)).map (fun k => rule d t w v p k)).foldl Max.max 0)).foldl Max.max 0

def rules (d : DataCode α) (t : Table α) (w : List α) : ℕ :=
  (d.1.map (fun v => rulesFor d t w v)).foldl Max.max 0

def left (d : DataCode α) (t : Table α) (w : List α) : ℕ :=
  (d.2.2.map (fun c => if member (c::w) d.1 then lookup t (c::w) else 0)).sum

def right (d : DataCode α) (t : Table α) (w : List α) : ℕ :=
  (d.2.2.map (fun c => if member (w++[c]) d.1 then lookup t (w++[c]) else 0)).sum

def step (d : DataCode α) (t : Table α) (w : List α) : ℕ :=
  if member (w) d.1 && !w.isEmpty then
    max (if member (w) d.2.1 then 1 else 0)
      (max (left d t w) (max (right d t w) (rules d t w)))
  else 0

def tableStep (d : DataCode α) (t : Table α) : Table α := d.1.map (fun w => (w,step d t w))

theorem blocking_eq (d : DataCode α) (hd : d.1.Nodup) (t : Table α)
    (v : List α) (p : ℕ) (w : List α) :
    blocking d t v p w = Counts.blocking d.1.toFinset (Counts.finiteText v p) w (lookup t) := by
  simp only [blocking, sum_map_finset _ hd, coefficient_eq, Counts.blocking]

theorem rule_eq (d : DataCode α) (hd : d.1.Nodup) (t : Table α)
    (w v : List α) (p k : ℕ) :
    rule d t w v p k = (decodeData d).rule (lookup t) w v p k := by
  simp only [rule, Bool.and_eq_true, less, equal, decide_eq_true_eq,
    Bool.not_eq_true_eq_eq_false, List.isEmpty_eq_false_iff, matches_eq,
    blocking_eq d hd, decodeData, Counts.Data.rule]
  simp only [and_assoc]
  rfl

theorem rules_eq (d : DataCode α) (hd : d.1.Nodup) (t : Table α) (w : List α) :
    rules d t w = (decodeData d).rules (lookup t) w := by
  simp only [rules, rulesFor, max_map_finset, rule_eq d hd,
    List.toFinset_range, decodeData, Counts.Data.rules]

theorem step_eq (d : DataCode α) (hd : d.1.Nodup) (ha : d.2.2.Nodup)
    (t : Table α) (w : List α) : step d t w = (decodeData d).step (lookup t) w := by
  have hl : left d t w = (decodeData d).left (lookup t) w := by
    simp only [left, sum_map_finset _ ha, member_eq, Counts.Data.left,
      decodeData, List.mem_toFinset]
  have hr : right d t w = (decodeData d).right (lookup t) w := by
    simp only [right, sum_map_finset _ ha, member_eq, Counts.Data.right,
      decodeData, List.mem_toFinset]
  simp only [step, Bool.and_eq_true, member_eq, Bool.not_eq_true_eq_eq_false,
    List.isEmpty_eq_false_iff, hl, hr, rules_eq d hd, Counts.Data.step, decodeData,
    List.mem_toFinset]

end Superstring.Computable

namespace Superstring.Computable
open BitCode
variable {α : Type} [DecidableEq α] [Inhabited α] [Coded α]

omit [Inhabited α] in
@[fun_prop] theorem poly_dataCode : Poly (dataCode : List (List α) → DataCode α) := by
  unfold dataCode
  fun_prop

omit [Inhabited α] in
@[fun_prop] theorem poly_lookup : Poly (fun q : Table α × List α => lookup q.1 q.2) := by
  have hf : Poly (fun q : Table α × List α => q.1.filter (fun e => equal e.1 q.2)) :=
    BitCode.Poly.filterFn (p := fun q : (Table α × List α) × (List α × ℕ) => equal q.2.1 q.1.2)
      (by fun_prop) (by fun_prop)
  unfold lookup
  exact (BitCode.Poly.headD 0).comp ((BitCode.Poly.map BitCode.Poly.snd).comp hf)

@[fun_prop] theorem poly_blocking :
    Poly (fun q : DataCode α × Table α × List α × ℕ × List α =>
      blocking q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  unfold blocking
  exact BitCode.Poly.sum.comp (BitCode.Poly.mapFn
    (f := fun q : (DataCode α × Table α × List α × ℕ × List α) × List α =>
      coefficient q.1.2.2.1 q.1.2.2.2.1 q.1.2.2.2.2 q.2 * lookup q.1.2.1 q.2)
    (by fun_prop) (by fun_prop))

@[fun_prop] theorem poly_rule :
    Poly (fun q : DataCode α × Table α × List α × List α × ℕ × ℕ =>
      rule q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2) := by
  unfold rule
  fun_prop

@[fun_prop] theorem poly_rulesFor :
    Poly (fun q : DataCode α × Table α × List α × List α =>
      rulesFor q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  have hi : Poly (fun q : (DataCode α × Table α × List α × List α) × ℕ =>
      ((List.range (q.1.2.2.2.length+1)).map (fun k =>
        rule q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2 k)).foldl Max.max 0) :=
    BitCode.Poly.maxFold.comp (BitCode.Poly.mapFn
      (f := fun q : ((DataCode α × Table α × List α × List α) × ℕ) × ℕ =>
        rule q.1.1.1 q.1.1.2.1 q.1.1.2.2.1 q.1.1.2.2.2 q.1.2 q.2)
      (by fun_prop) (by fun_prop))
  unfold rulesFor
  exact BitCode.Poly.maxFold.comp (BitCode.Poly.mapFn hi (by fun_prop))

@[fun_prop] theorem poly_rules : Poly (fun q : DataCode α × Table α × List α =>
    rules q.1 q.2.1 q.2.2) := by
  unfold rules
  exact BitCode.Poly.maxFold.comp (BitCode.Poly.mapFn
    (f := fun q : (DataCode α × Table α × List α) × List α =>
      rulesFor q.1.1 q.1.2.1 q.1.2.2 q.2) (by fun_prop) (by fun_prop))

omit [Inhabited α] in
@[fun_prop] theorem poly_left : Poly (fun q : DataCode α × Table α × List α =>
    left q.1 q.2.1 q.2.2) := by
  unfold left
  exact BitCode.Poly.sum.comp (BitCode.Poly.mapFn
    (f := fun q : (DataCode α × Table α × List α) × α =>
      if member (q.2::q.1.2.2) q.1.1.1 then lookup q.1.2.1 (q.2::q.1.2.2) else 0)
    (by fun_prop) (by fun_prop))

omit [Inhabited α] in
@[fun_prop] theorem poly_right : Poly (fun q : DataCode α × Table α × List α =>
    right q.1 q.2.1 q.2.2) := by
  unfold right
  exact BitCode.Poly.sum.comp (BitCode.Poly.mapFn
    (f := fun q : (DataCode α × Table α × List α) × α =>
      if member (q.1.2.2++[q.2]) q.1.1.1 then lookup q.1.2.1 (q.1.2.2++[q.2]) else 0)
    (by fun_prop) (by fun_prop))

@[fun_prop] theorem poly_step : Poly (fun q : DataCode α × Table α × List α =>
    step q.1 q.2.1 q.2.2) := by
  unfold step
  fun_prop

@[fun_prop] theorem poly_tableStep : Poly (fun q : DataCode α × Table α => tableStep q.1 q.2) := by
  unfold tableStep
  exact BitCode.Poly.mapFn (f := fun q : (DataCode α × Table α) × List α =>
    (q.2,step q.1.1 q.1.2 q.2)) (by fun_prop) (by fun_prop)

end Superstring.Computable

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.Computable
open BitCode
variable {α : Type} [DecidableEq α] [Inhabited α]

theorem stage_zero (D : Counts.Data α) (n : ℕ) (w : List α)
    (hw : w ∉ D.vertices ∨ w = []) : D.stage n w = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Counts.Data.stage, Counts.Data.step]
    split
    · rename_i hh
      exact False.elim (hw.elim (fun h => h hh.1) (fun h => hh.2 h))
    · rfl

theorem input_stage_bound (S : List (List α)) (n : ℕ) (w : List α) :
    (Input.data S).stage n w ≤ S.flatten.length := by
  by_cases he : w = []
  · rw [stage_zero _ _ _ (Or.inr he)]; exact Nat.zero_le _
  · exact ((Input.data S).stage_le_number S.flatten
      (fun _ hw => List.infix_of_mem_flatten ((Input.mem_core.mp hw).1)) n w).trans
        (Counts.number_le_length he)

def stageTable (S : List (List α)) (n : ℕ) : Table α :=
  (vertices S).map (fun w => (w,(Input.data S).stage n w))

theorem lookup_stageTable (S : List (List α)) (n : ℕ) (w : List α) :
    lookup (stageTable S n) w = (Input.data S).stage n w := by
  rw [stageTable, lookup_map]
  split
  · rfl
  · exact (stage_zero _ _ _ (Or.inl (by
      simpa only [Input.data, ← vertices_eq S, List.mem_toFinset] using ‹w ∉ vertices S›))).symm

/-- Only finite materialized tables are passed between consecutive iterations. -/
def rawCountStep (q : List (List α) × Table α) : List (List α) × Table α :=
  (q.1, tableStep (dataCode q.1) q.2)

def initialTable (S : List (List α)) : Table α := (vertices S).map (fun w => (w,0))

theorem rawCountStep_stage (S : List (List α)) (n : ℕ) :
    rawCountStep (S,stageTable S n) = (S,stageTable S (n+1)) := by
  simp only [rawCountStep, tableStep, dataCode, stageTable, Prod.mk.injEq, true_and]
  apply List.map_congr_left
  intro w _
  congr 1
  have hd : (dataCode S).1.Nodup := nodup_unique _
  have ha : (dataCode S).2.2.Nodup := nodup_unique _
  change step (dataCode S) (stageTable S n) w = _
  rw [step_eq (dataCode S) hd ha, decode_dataCode]
  rw [show lookup (stageTable S n) = (Input.data S).stage n from funext (lookup_stageTable S n)]
  rfl

theorem iterate_rawCountStep (S : List (List α)) (n : ℕ) :
    rawCountStep^[n] (S,initialTable S) = (S,stageTable S n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, rawCountStep_stage]

variable [Coded α]

/-- A proved polynomial workspace guard. The cap is part of the implemented
loop; the mathematical bound proves it never fires on an actual input. -/
def countCap (S : List (List α)) : ℕ :=
  bitSize S + 1 + (vertices S).length * (bitSize (vertices S) + S.flatten.length + 2)

def countDepth (S : List (List α)) : ℕ :=
  ((vertices S).map List.length).foldl Max.max 0 + 1

def computeCounts (S : List (List α)) : Table α :=
  (((cappedStep rawCountStep)^[countDepth S] (countCap S,(S,initialTable S))).2).2

theorem stageTable_size (S : List (List α)) (n : ℕ) :
    bitSize (S,stageTable S n) ≤ countCap S := by
  have h := bitSize_map_le (vertices S) (fun w => (w,(Input.data S).stage n w))
    (bitSize (vertices S) + S.flatten.length + 1) (by
      intro w hw
      have hv := bitSize_mem hw
      have hn := input_stage_bound S n w
      simp only [bitSize_prod, bitSize_nat]
      omega)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h
  simp only [stageTable, bitSize_prod, countCap, Nat.add_assoc]
  omega

theorem computeCounts_eq (S : List (List α)) :
    computeCounts S = (vertices S).map (fun w => (w,(Input.data S).count w)) := by
  have he := iterate_cappedStep_eq rawCountStep (countDepth S) (countCap S)
    (S,initialTable S) (fun j _ _ => by rw [iterate_rawCountStep]; exact stageTable_size S j)
  rw [computeCounts, he, iterate_rawCountStep]
  have hd : countDepth S = (Input.data S).depth + 1 := by
    simp only [countDepth, max_map_finset, vertices_eq, Counts.Data.depth, Input.data]
  simp only [hd, stageTable, Counts.Data.count]

theorem lookup_computeCounts (S : List (List α)) (w : List α) :
    lookup (computeCounts S) w = (Input.data S).count w := by
  rw [computeCounts_eq, lookup_map]
  split
  · rfl
  · exact ((Input.data S).count_zero _ (Or.inl (by
      simpa only [Input.data, ← vertices_eq S, List.mem_toFinset] using ‹w ∉ vertices S›))).symm

omit [Inhabited α] in
@[fun_prop] theorem poly_initialTable : Poly (initialTable : List (List α) → Table α) := by
  unfold initialTable
  exact (BitCode.Poly.map (BitCode.Poly.id.pair (BitCode.Poly.const 0))).comp poly_vertices

@[fun_prop] theorem poly_rawCountStep : Poly (rawCountStep : List (List α) × Table α → _) := by
  unfold rawCountStep
  fun_prop

omit [Inhabited α] in
@[fun_prop] theorem poly_countCap : Poly (countCap : List (List α) → ℕ) := by
  unfold countCap
  fun_prop

omit [Inhabited α] in
@[fun_prop] theorem poly_countDepth : Poly (countDepth : List (List α) → ℕ) := by
  have hm : Poly (fun S : List (List α) => ((vertices S).map List.length).foldl Max.max 0) :=
    BitCode.Poly.maxFold.comp ((BitCode.Poly.map BitCode.Poly.length).comp poly_vertices)
  unfold countDepth
  fun_prop

@[fun_prop] theorem poly_computeCounts : Poly (computeCounts : List (List α) → Table α) := by
  have hp := BitCode.Poly.cappedIterate (poly_rawCountStep (α := α))
  exact BitCode.Poly.snd.comp (hp.comp (poly_countDepth.pair (poly_countCap.pair
    (BitCode.Poly.id.pair poly_initialTable))))

end Superstring.Computable

namespace Superstring.PrefixGreedy

variable {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def Capacity (req : β → List α) (sup : γ → List α) (R : Finset β) (S : Finset γ) : Prop :=
  ∀ w, (R.filter (fun a => w <+: req a)).card ≤ (S.filter (fun b => w <+: sup b)).card

omit [DecidableEq β] [DecidableEq γ] in
theorem exists_supply {req : β → List α} {sup : γ → List α} {R : Finset β} {S : Finset γ}
    (h : Capacity req sup R S) {a : β} (ha : a ∈ R) :
    ∃ b ∈ S, req a <+: sup b := by
  have hc := h (req a)
  have hp : 0 < (R.filter (fun r => req a <+: req r)).card :=
    Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, List.prefix_refl _⟩⟩
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (lt_of_lt_of_le hp hc)
  exact ⟨b, Finset.mem_filter.mp hb⟩

/-- Deleting a longest request and any of its extensions preserves all subtree capacities. -/
theorem capacity_erase {req : β → List α} {sup : γ → List α} {R : Finset β} {S : Finset γ}
    (h : Capacity req sup R S) {a : β} {b : γ} (ha : a ∈ R) (hb : b ∈ S)
    (hm : ∀ r ∈ R, (req r).length ≤ (req a).length) (hp : req a <+: sup b) :
    Capacity req sup (R.erase a) (S.erase b) := by
  intro w
  rw [Finset.filter_erase, Finset.filter_erase]
  by_cases hw : w <+: req a
  · have hwa : a ∈ R.filter (fun r => w <+: req r) := Finset.mem_filter.mpr ⟨ha, hw⟩
    have hwb : b ∈ S.filter (fun r => w <+: sup r) := Finset.mem_filter.mpr ⟨hb, hw.trans hp⟩
    rw [Finset.card_erase_of_mem hwa, Finset.card_erase_of_mem hwb]
    exact Nat.sub_le_sub_right (h w) 1
  · by_cases hwb : w <+: sup b
    · have hz : (R.filter (fun r => w <+: req r)) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro r hr
        obtain ⟨hr, hwr⟩ := Finset.mem_filter.mp hr
        apply hw
        exact List.prefix_of_prefix_length_le hwb hp (hwr.length_le.trans (hm r hr))
      rw [hz, Finset.erase_empty, Finset.card_empty]
      exact Nat.zero_le _
    · have hna : a ∉ R.filter (fun r => w <+: req r) := by simp only [Finset.mem_filter]; tauto
      have hnb : b ∉ S.filter (fun r => w <+: sup r) := by simp only [Finset.mem_filter]; tauto
      rw [Finset.erase_eq_of_notMem hna, Finset.erase_eq_of_notMem hnb]
      exact h w

end Superstring.PrefixGreedy

namespace Superstring.PrefixGreedy

abbrev Token (α : Type) := ℕ × List α

def prefer {α : Type} (a b : Token α) : Token α := if a.2.length < b.2.length then b else a

def largest {α : Type} (xs : List (Token α)) : Token α := xs.foldl prefer (xs.headD (0,[]))

theorem fold_prefer {α : Type} (xs : List (Token α)) (a : Token α) :
    xs.foldl prefer a ∈ a :: xs ∧ a.2.length ≤ (xs.foldl prefer a).2.length ∧
      ∀ b ∈ xs, b.2.length ≤ (xs.foldl prefer a).2.length := by
  induction xs generalizing a with
  | nil => simp
  | cons b xs ih =>
    simp only [List.foldl_cons]
    obtain ⟨hm, ha, hx⟩ := ih (prefer a b)
    have hp : prefer a b = a ∨ prefer a b = b := by unfold prefer; split <;> simp
    have hal : a.2.length ≤ (prefer a b).2.length := by unfold prefer; split <;> omega
    have hbl : b.2.length ≤ (prefer a b).2.length := by unfold prefer; split <;> omega
    refine ⟨?_, le_trans hal ha, ?_⟩
    · simp only [List.mem_cons] at hm ⊢
      rcases hm with h | h
      · rw [h]; exact hp.elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact Or.inr (Or.inr h)
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact le_trans hbl ha
      · exact hx c hc

theorem largest_spec {α : Type} (xs : List (Token α)) (hne : xs ≠ []) :
    largest xs ∈ xs ∧ ∀ b ∈ xs, b.2.length ≤ (largest xs).2.length := by
  obtain ⟨hm, _, hb⟩ := fold_prefer xs (xs.headD (0,[]))
  have hh : xs.headD (0,[]) ∈ xs := by cases xs with
    | nil => exact (hne rfl).elim
    | cons a xs => simp
  refine ⟨?_, hb⟩
  change xs.foldl prefer (xs.headD (0,[])) ∈ xs
  exact (List.mem_cons.mp hm).elim (fun h => h.symm ▸ hh) id

variable {α : Type} [DecidableEq α]

def prefixB (a b : List α) : Bool := decide (a <+: b)

def remove (a : Token α) (xs : List (Token α)) : List (Token α) :=
  xs.filter (fun b => decide (b ≠ a))

@[simp] theorem mem_remove (a b : Token α) (xs : List (Token α)) :
    b ∈ remove a xs ↔ b ∈ xs ∧ b ≠ a := by simp [remove]

@[simp] theorem toFinset_remove (a : Token α) (xs : List (Token α)) :
    (remove a xs).toFinset = xs.toFinset.erase a := by
  ext b; simp only [List.mem_toFinset, mem_remove, Finset.mem_erase]; tauto

def extension (a : Token α) (S : List (Token α)) : Token α :=
  (S.filter (fun b => prefixB a.2 b.2)).headD (0,[])

theorem extension_spec {a : Token α} {S : List (Token α)}
    (h : ∃ b ∈ S, a.2 <+: b.2) : extension a S ∈ S ∧ a.2 <+: (extension a S).2 := by
  have hm : extension a S ∈ S.filter (fun b => prefixB a.2 b.2) := by
    have hne : S.filter (fun b => prefixB a.2 b.2) ≠ [] := by
      obtain ⟨b, hb, hp⟩ := h
      intro he
      have hm : b ∈ S.filter (fun b => prefixB a.2 b.2) := by simp [hb, prefixB, hp]
      rw [he] at hm
      exact List.not_mem_nil hm
    unfold extension
    generalize S.filter (fun b => prefixB a.2 b.2) = xs at *
    cases xs with
    | nil => exact (hne rfl).elim
    | cons b xs => simp
  simpa only [List.mem_filter, prefixB, decide_eq_true_eq] using hm

abbrev State (α : Type) := List (Token α) × List (Token α) × List (Token α × Token α)

def step (q : State α) : State α :=
  if q.1.isEmpty then q else
    let a := largest q.1
    let b := extension a q.2.1
    (remove a q.1, remove b q.2.1, (a,b)::q.2.2)

end Superstring.PrefixGreedy

namespace Superstring.PrefixGreedy
variable {α : Type} [DecidableEq α]

theorem remove_nodup (a : Token α) {xs : List (Token α)} (h : xs.Nodup) :
    (remove a xs).Nodup := h.filter _

theorem remove_perm {a : Token α} {xs : List (Token α)} (h : xs.Nodup) (ha : a ∈ xs) :
    xs.Perm (a :: remove a xs) := by
  apply (List.perm_ext_iff_of_nodup h (List.nodup_cons.mpr ⟨by simp, remove_nodup a h⟩)).mpr
  intro b
  simp only [List.mem_cons, mem_remove]
  constructor
  · intro hb; by_cases he : b = a
    · exact Or.inl he
    · exact Or.inr ⟨hb,he⟩
  · rintro (rfl | ⟨hb,_⟩)
    · exact ha
    · exact hb

/-- The explicit greedy loop returns a complete matching, with no search over permutations. -/
theorem iterate_correct (n : ℕ) (R S : List (Token α)) (P : List (Token α × Token α))
    (hR : R.Nodup) (hS : S.Nodup) (hc : Capacity Prod.snd Prod.snd R.toFinset S.toFinset)
    (hlen : R.length = S.length) (hn : R.length ≤ n)
    (hP : ∀ p ∈ P, p.1.2 <+: p.2.2) :
    let q := step^[n] (R,S,P)
    q.1 = [] ∧ q.2.1 = [] ∧
      (q.2.2.map Prod.fst).Perm (R ++ P.map Prod.fst) ∧
      (q.2.2.map Prod.snd).Perm (S ++ P.map Prod.snd) ∧
      ∀ p ∈ q.2.2, p.1.2 <+: p.2.2 := by
  induction n generalizing R S P with
  | zero =>
    have hr : R = [] := List.length_eq_zero_iff.mp (by omega)
    have hs : S = [] := List.length_eq_zero_iff.mp (by omega)
    subst R; subst S
    simpa only [Function.iterate_zero_apply, List.nil_append, true_and] using
      And.intro (List.Perm.refl _) (And.intro (List.Perm.refl _) hP)
  | succ n ih =>
    change _ ∧ _ ∧ _ ∧ _ ∧ _
    rw [Function.iterate_succ_apply]
    by_cases hr : R = []
    · subst R
      have hs : S = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      subst S
      simpa only [step, List.isEmpty_nil, Bool.true_eq, ite_true] using
        ih [] [] P hR hS hc hlen (Nat.zero_le n) hP
    · let a := largest R
      let b := extension a S
      have ha : a ∈ R := (largest_spec R hr).1
      have hm : ∀ r ∈ R.toFinset, r.2.length ≤ a.2.length := by
        intro r hh; exact (largest_spec R hr).2 r (List.mem_toFinset.mp hh)
      have hex : ∃ b ∈ S, a.2 <+: b.2 := by
        simpa only [List.mem_toFinset] using exists_supply hc (List.mem_toFinset.mpr ha)
      obtain ⟨hb, hp⟩ := extension_spec hex
      have hbS : b ∈ S := hb
      have hmatch : a.2 <+: b.2 := hp
      have hc' : Capacity Prod.snd Prod.snd (remove a R).toFinset (remove b S).toFinset := by
        rw [toFinset_remove, toFinset_remove]
        exact capacity_erase hc (List.mem_toFinset.mpr ha) (List.mem_toFinset.mpr hbS) hm hmatch
      have hrp := remove_perm hR ha
      have hsp := remove_perm hS hbS
      have hlr := hrp.length_eq
      have hls := hsp.length_eq
      simp only [List.length_cons] at hlr hls
      have hsub := ih (remove a R) (remove b S) ((a,b)::P)
        (remove_nodup a hR) (remove_nodup b hS) hc' (by omega) (by omega)
        (by intro p hh; rcases List.mem_cons.mp hh with rfl | hh
            · exact hmatch
            · exact hP p hh)
      have he : step (R,S,P) = (remove a R,remove b S,(a,b)::P) := by
        simp only [step, a, b, List.isEmpty_iff, hr, ite_false]
      rw [he]
      refine ⟨hsub.1, hsub.2.1, ?_, ?_, hsub.2.2.2.2⟩
      · have hh := hsub.2.2.1
        simp only [List.map_cons] at hh
        exact hh.trans (List.perm_middle.trans (hrp.symm.append_right _))
      · have hh := hsub.2.2.2.1
        simp only [List.map_cons] at hh
        exact hh.trans (List.perm_middle.trans (hsp.symm.append_right _))

end Superstring.PrefixGreedy

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.PrefixGreedy
open BitCode
variable {α : Type} [Coded α]

@[fun_prop] theorem poly_prefer : Poly (fun q : Token α × Token α => prefer q.1 q.2) := by
  have hp : Poly (fun q : Token α × Token α => if less q.1.2.length q.2.2.length then q.2 else q.1) := by
    fun_prop
  simpa only [prefer, less, decide_eq_true_eq] using hp

@[fun_prop] theorem poly_largest : Poly (largest : List (Token α) → Token α) := by
  have hs : ∀ a b : Token α, bitSize (prefer a b) ≤ bitSize a +
      (Polynomial.X : Polynomial ℕ).eval (bitSize b) := by
    intro a b
    unfold prefer
    split <;> simp only [Polynomial.eval_X] <;> omega
  have hf := BitCode.Poly.foldl_additive poly_prefer Polynomial.X hs
  exact hf.comp (BitCode.Poly.id.pair (BitCode.Poly.headD (0,[])))

variable [DecidableEq α]

@[fun_prop] theorem poly_prefixB : Poly (fun q : List α × List α => prefixB q.1 q.2) := by
  have hp : Poly (fun q : List α × List α => equal q.1 (q.2.take q.1.length)) := by fun_prop
  convert hp using 1
  funext q
  apply Bool.eq_iff_iff.mpr
  simp only [prefixB, equal, decide_eq_true_eq, List.prefix_iff_eq_take]

@[fun_prop] theorem poly_remove : Poly (fun q : Token α × List (Token α) => remove q.1 q.2) := by
  have hp := BitCode.Poly.filterFn (p := fun q : (Token α × List (Token α)) × Token α =>
    !(equal q.2 q.1.1)) (by fun_prop) (BitCode.Poly.snd : Poly (Prod.snd : Token α × List (Token α) → _))
  convert hp using 1
  funext q
  simp only [remove, equal, decide_not]

@[fun_prop] theorem poly_extension : Poly (fun q : Token α × List (Token α) => extension q.1 q.2) := by
  unfold extension
  exact (BitCode.Poly.headD (0,[])).comp (BitCode.Poly.filterFn
    (p := fun q : (Token α × List (Token α)) × Token α => prefixB q.1.1.2 q.2.2)
    (by fun_prop) BitCode.Poly.snd)

@[fun_prop] theorem poly_step : Poly (step : State α → State α) := by
  unfold step
  fun_prop

omit [DecidableEq α] in
theorem largest_size {R : List (Token α)} (hR : R ≠ []) : bitSize (largest R) ≤ bitSize R :=
  bitSize_mem (largest_spec R hR).1

theorem extension_size (a : Token α) (S : List (Token α)) :
    bitSize (extension a S) ≤ bitSize S + 2 := by
  have hb : ∀ xs : List (Token α), bitSize (xs.headD (0,[])) ≤ bitSize xs + 2 := by
    intro xs
    cases xs with
    | nil => simp
    | cons x xs => simp only [List.headD_cons, bitSize_cons]; omega
  have hh := hb (S.filter (fun b => prefixB a.2 b.2))
  have hm := bitSize_sublist (List.filter_sublist (p := fun b => prefixB a.2 b.2) (l := S))
  exact le_trans hh (Nat.add_le_add_right hm 2)

theorem step_bounds (q : State α) :
    bitSize (step q).1 + bitSize (step q).2.1 ≤ bitSize q.1 + bitSize q.2.1 ∧
    bitSize (step q).2.2 ≤ bitSize q.2.2 + (bitSize q.1 + bitSize q.2.1 + 3) := by
  by_cases he : q.1.isEmpty = true
  · simp only [step, he, ite_true]
    omega
  · have hne : q.1 ≠ [] := by simpa only [List.isEmpty_iff] using he
    have ha := largest_size hne
    have hb := extension_size (largest q.1) q.2.1
    have hr := bitSize_sublist (List.filter_sublist (p := fun b => decide (b ≠ largest q.1)) (l := q.1))
    have hs := bitSize_sublist (List.filter_sublist (p := fun b => decide (b ≠ extension (largest q.1) q.2.1)) (l := q.2.1))
    simp only [step, he, Bool.false_eq_true, ite_false, bitSize_cons, bitSize_prod, remove]
    constructor <;> omega

theorem iterate_size (q : State α) (n : ℕ) :
    bitSize (step^[n] q).1 + bitSize (step^[n] q).2.1 ≤ bitSize q.1 + bitSize q.2.1 ∧
    bitSize (step^[n] q).2.2 ≤ bitSize q.2.2 + n * (bitSize q.1 + bitSize q.2.1 + 3) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hh := step_bounds (step^[n] q)
    constructor
    · exact hh.1.trans ih.1
    · rw [Nat.succ_mul]
      omega

@[fun_prop] theorem poly_iterate : Poly (fun q : ℕ × State α => step^[q.1] q.2) := by
  apply BitCode.Poly.iterate poly_step (Polynomial.X * Polynomial.X + 4 * Polynomial.X + 4)
  intro n q j hj
  have h := iterate_size q j
  rcases q with ⟨R,S,P⟩
  have ht : bitSize (step^[j] (R,S,P)) ≤
      bitSize R + bitSize S + bitSize P + j * (bitSize R + bitSize S + 3) := by
    generalize he : step^[j] (R,S,P) = z at *
    rcases z with ⟨R',S',P'⟩
    simp only [bitSize_prod]
    dsimp only at h
    omega
  simp only [bitSize_prod, bitSize_nat, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_ofNat]
  have hjn : j ≤ n := by omega
  have hm := Nat.mul_le_mul_right (bitSize R + bitSize S + 3) hjn
  nlinarith

def compute (R S : List (Token α)) : List (Token α × Token α) :=
  (step^[R.length] (R,S,[])).2.2

@[fun_prop] theorem poly_compute : Poly (fun q : List (Token α) × List (Token α) => compute q.1 q.2) := by
  unfold compute
  exact (BitCode.Poly.snd.comp BitCode.Poly.snd).comp
    (poly_iterate.comp (BitCode.Poly.length.comp BitCode.Poly.fst |>.pair
      (BitCode.Poly.fst.pair (BitCode.Poly.snd.pair (BitCode.Poly.const [])))))

omit [Coded α] in
theorem compute_correct (R S : List (Token α)) (hR : R.Nodup) (hS : S.Nodup)
    (hc : Capacity Prod.snd Prod.snd R.toFinset S.toFinset) (hl : R.length = S.length) :
    ((compute R S).map Prod.fst).Perm R ∧ ((compute R S).map Prod.snd).Perm S ∧
      ∀ p ∈ compute R S, p.1.2 <+: p.2.2 := by
  have h := iterate_correct R.length R S [] hR hS hc hl le_rfl (by simp)
  simpa only [compute, List.map_nil, List.append_nil] using h.2.2

end Superstring.PrefixGreedy

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.ArrayPerm
open BitCode

abbrev Edges := List (ℕ × ℕ)

def Valid (n : ℕ) (E : Edges) : Prop :=
  (E.map Prod.fst).Perm (List.range n) ∧ (E.map Prod.snd).Perm (List.range n)

def next (E : Edges) (i : ℕ) : ℕ :=
  ((E.filter (fun e => equal e.1 i)).headD (0,0)).2

@[fun_prop] theorem poly_next : Poly (fun q : Edges × ℕ => next q.1 q.2) := by
  unfold next
  exact BitCode.Poly.snd.comp ((BitCode.Poly.headD (0,0)).comp (BitCode.Poly.filterFn
    (p := fun q : (Edges × ℕ) × (ℕ × ℕ) => equal q.2.1 q.1.2)
    (by fun_prop) BitCode.Poly.fst))

theorem next_mem {n : ℕ} {E : Edges} (h : Valid n E) {i : ℕ} (hi : i < n) :
    (i,next E i) ∈ E := by
  have hm : i ∈ E.map Prod.fst := h.1.mem_iff.mpr (List.mem_range.mpr hi)
  obtain ⟨e,he,hi'⟩ := List.mem_map.mp hm
  have hx : e ∈ E.filter (fun e => equal e.1 i) := by
    simp only [List.mem_filter, equal, decide_eq_true_eq]
    exact ⟨he,hi'⟩
  have hn : E.filter (fun e => equal e.1 i) ≠ [] := by
    intro he'; rw [he'] at hx; exact List.not_mem_nil hx
  have hh : (E.filter (fun e => equal e.1 i)).headD (0,0) ∈ E.filter (fun e => equal e.1 i) := by
    generalize E.filter (fun e => equal e.1 i) = L at *
    cases L with
    | nil => exact (hn rfl).elim
    | cons a L => simp
  obtain ⟨hh,heq⟩ := List.mem_filter.mp hh
  have heq' : ((E.filter (fun e => equal e.1 i)).headD (0,0)).1 = i := by
    exact of_decide_eq_true heq
  have hh' : (i, next E i) = ((E.filter (fun e => equal e.1 i)).headD (0,0)) :=
    Prod.ext heq'.symm rfl
  rw [hh']
  exact hh

theorem next_lt {n : ℕ} {E : Edges} (h : Valid n E) {i : ℕ} (hi : i < n) : next E i < n := by
  have hm := List.mem_map_of_mem (f := Prod.snd) (next_mem h hi)
  exact List.mem_range.mp (h.2.mem_iff.mp hm)

theorem next_injective {n : ℕ} {E : Edges} (h : Valid n E) {i j : ℕ}
    (hi : i < n) (hj : j < n) (he : next E i = next E j) : i = j := by
  have hn : (E.map Prod.snd).Nodup := h.2.nodup_iff.mpr List.nodup_range
  have hh := List.inj_on_of_nodup_map hn (next_mem h hi) (next_mem h hj) he
  exact congrArg Prod.fst hh

noncomputable def perm {n : ℕ} {E : Edges} (h : Valid n E) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun i => ⟨next E i.val, next_lt h i.isLt⟩)
    ((Fintype.bijective_iff_injective_and_card (f := fun i : Fin n =>
      (⟨next E i.val, next_lt h i.isLt⟩ : Fin n))).mpr ⟨by
        intro i j he
        exact Fin.ext (next_injective h i.isLt j.isLt (congrArg Fin.val he)), rfl⟩)

@[simp] theorem perm_apply {n : ℕ} {E : Edges} (h : Valid n E) (i : Fin n) :
    (perm h i).val = next E i.val := rfl


theorem next_size (E : Edges) (i : ℕ) : bitSize (next E i) ≤ bitSize E + 2 := by
  let L := E.filter (fun e => equal e.1 i)
  by_cases hn : L = []
  · change bitSize (L.headD (0,0)).2 ≤ _
    rw [hn]
    simp only [List.headD_nil, bitSize_nat]
    omega
  · have hm : L.headD (0,0) ∈ L := by
      cases hL : L with
      | nil => exact (hn hL).elim
      | cons a l => simp
    have hb := bitSize_mem ((List.mem_filter.mp hm).1)
    have hh : ∀ a : ℕ × ℕ, bitSize a.2 ≤ bitSize a := by
      rintro ⟨a,b⟩
      simp only [bitSize_prod]
      omega
    change bitSize (L.headD (0,0)).2 ≤ _
    exact (hh _).trans (hb.trans (Nat.le_add_right _ _))

def advance (q : Edges × ℕ) : Edges × ℕ := (q.1,next q.1 q.2)

@[fun_prop] theorem poly_advance : Poly advance := by unfold advance; fun_prop

theorem iterate_advance (E : Edges) (i n : ℕ) :
    advance^[n] (E,i) = (E,(next E)^[n] i) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']; rfl

@[fun_prop] theorem poly_iterate_advance : Poly (fun q : ℕ × (Edges × ℕ) => advance^[q.1] q.2) := by
  apply BitCode.Poly.iterate poly_advance (2 * Polynomial.X + 2)
  rintro n ⟨E,i⟩ j _
  rw [iterate_advance, bitSize_prod]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, bitSize_prod, bitSize_nat]
  cases j with
  | zero => simp only [Function.iterate_zero_apply]; omega
  | succ j =>
    rw [Function.iterate_succ_apply']
    have hh := next_size E ((next E)^[j] i)
    simp only [bitSize_nat] at hh
    omega

def power (E : Edges) (n i : ℕ) : ℕ := (next E)^[n] i

@[fun_prop] theorem poly_power : Poly (fun q : Edges × ℕ × ℕ => power q.1 q.2.1 q.2.2) := by
  have hh : Poly (fun q : Edges × ℕ × ℕ => (advance^[q.2.1] (q.1,q.2.2)).2) := by fun_prop
  simpa only [iterate_advance, power] using hh

theorem power_perm {n : ℕ} {E : Edges} (h : Valid n E) (k : ℕ) (i : Fin n) :
    power E k i.val = ((perm h ^ k) i).val := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [power, Function.iterate_succ_apply']
    change next E (power E k i.val) = _
    rw [ih, pow_succ', Equiv.Perm.mul_apply, perm_apply]

theorem power_lt {n : ℕ} {E : Edges} (h : Valid n E) (k i : ℕ) (hi : i < n) :
    power E k i < n := by
  rw [power_perm h k ⟨i,hi⟩]
  exact ((perm h ^ k) ⟨i,hi⟩).isLt

end Superstring.ArrayPerm
namespace Superstring.Computable
open BitCode
variable {α : Type} [Coded α]

@[fun_prop] theorem poly_replicate : Poly (fun q : ℕ × α => List.replicate q.1 q.2) := by
  have hp := BitCode.Poly.mapFn (f := fun q : (ℕ × α) × ℕ => q.1.2)
    (by fun_prop) (BitCode.Poly.range.comp BitCode.Poly.fst)
  simpa only [Function.comp_apply, List.map_const', List.length_range] using hp

def indexed {α : Type} (xs : List (List α)) : List (PrefixGreedy.Token α) :=
  (List.range xs.length).map (fun i => (i,xs[i]?.getD []))

@[fun_prop] theorem poly_indexed : Poly (indexed : List (List α) → _) := by
  unfold indexed
  exact BitCode.Poly.mapFn (f := fun q : List (List α) × ℕ => (q.2,q.1[q.2]?.getD []))
    (by exact BitCode.Poly.snd.pair ((BitCode.Poly.getD []).comp BitCode.Poly.id))
    (by fun_prop)

omit [Coded α] in
theorem indexed_fst (xs : List (List α)) : (indexed xs).map Prod.fst = List.range xs.length := by
  simp only [indexed, List.map_map, Function.comp_def]
  exact List.map_id _

omit [Coded α] in
theorem indexed_snd (xs : List (List α)) : (indexed xs).map Prod.snd = xs := by
  apply List.ext_getElem
  · simp only [indexed, List.length_map, List.length_range]
  · intro i hi hi'
    simp only [indexed, List.getElem_map, List.getElem_range, List.getElem?_eq_getElem hi',
      Option.getD_some]

omit [Coded α] in
theorem indexed_nodup (xs : List (List α)) : (indexed xs).Nodup :=
  List.Nodup.of_map Prod.fst (by rw [indexed_fst]; exact List.nodup_range)

omit [Coded α] in
theorem mem_indexed {xs : List (List α)} {i : ℕ} {w : List α} :
    (i,w) ∈ indexed xs ↔ ∃ h : i < xs.length, xs[i] = w := by
  simp only [indexed, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨j,hj,he,hw⟩
    subst j
    exact ⟨hj, by simpa only [List.getElem?_eq_getElem hj, Option.getD_some] using hw⟩
  · rintro ⟨hi,rfl⟩
    exact ⟨i,hi,rfl,by rw [List.getElem?_eq_getElem hi, Option.getD_some]⟩

variable [DecidableEq α] [Inhabited α]

def downValue (S : List (List α)) (w : List α) : ℕ :=
  lookup (computeCounts S) w - right (dataCode S) (computeCounts S) w

@[fun_prop] theorem poly_downValue : Poly (fun q : List (List α) × List α => downValue q.1 q.2) := by
  unfold downValue
  fun_prop

theorem downValue_eq (S : List (List α)) (w : List α) : downValue S w = (Input.data S).down w := by
  unfold downValue Counts.Data.down
  rw [lookup_computeCounts]
  have hh : right (dataCode S) (computeCounts S) w =
      ∑ c ∈ (Input.data S).alphabet, (Input.data S).count (w++[c]) := by
    have hr : right (dataCode S) (computeCounts S) w =
        (decodeData (dataCode S)).right (lookup (computeCounts S)) w := by
      simp only [right, sum_map_finset _ (show (dataCode S).2.2.Nodup from nodup_unique _), member_eq, Counts.Data.right,
        decodeData, List.mem_toFinset]
    rw [hr, decode_dataCode, ← Counts.Data.right_count]
    unfold Counts.Data.right
    apply Finset.sum_congr rfl
    intro c hc
    split
    · exact lookup_computeCounts S _
    · rfl
  rw [hh]

def downWords (S : List (List α)) : List (List α) :=
  ((vertices S).map (fun w => List.replicate (downValue S w) w)).flatten

@[fun_prop] theorem poly_downWords : Poly (downWords : List (List α) → _) := by
  unfold downWords
  exact BitCode.Poly.flatten.comp (BitCode.Poly.mapFn
    (f := fun q : List (List α) × List α => List.replicate (downValue q.1 q.2) q.2)
    (by fun_prop) poly_vertices)

theorem downWords_count (S : List (List α)) (P : List α → Bool) :
    (downWords S).countP P = ∑ w ∈ (Input.data S).vertices,
      if P w then (Input.data S).down w else 0 := by
  unfold downWords
  rw [List.countP_flatten]
  simp only [List.map_map, Function.comp_def, List.countP_replicate, downValue_eq]
  rw [sum_map_finset _ (show (vertices S).Nodup from nodup_unique _) _, vertices_eq]
  rfl


def requests (xs : List (List α)) : List (PrefixGreedy.Token α) :=
  (indexed xs).map (fun t => (t.1,t.2.tail))

omit [DecidableEq α] [Inhabited α] in
@[fun_prop] theorem poly_requests : Poly (requests : List (List α) → _) := by
  unfold requests
  exact (BitCode.Poly.map (by fun_prop)).comp poly_indexed

omit [Coded α] [DecidableEq α] [Inhabited α] in
theorem requests_fst (xs : List (List α)) : (requests xs).map Prod.fst = List.range xs.length := by
  simp only [requests, List.map_map, Function.comp_def]
  exact indexed_fst xs

omit [Coded α] [DecidableEq α] [Inhabited α] in
theorem requests_snd (xs : List (List α)) : (requests xs).map Prod.snd = xs.map List.tail := by
  rw [requests, List.map_map]
  change (indexed xs).map (List.tail ∘ Prod.snd) = _
  rw [← List.map_map, indexed_snd]

omit [Coded α] [DecidableEq α] [Inhabited α] in
theorem requests_nodup (xs : List (List α)) : (requests xs).Nodup :=
  List.Nodup.of_map Prod.fst (by rw [requests_fst]; exact List.nodup_range)

theorem down_capacity (S : List (List α)) :
    PrefixGreedy.Capacity Prod.snd Prod.snd
      (requests (downWords S)).toFinset (indexed (downWords S)).toFinset := by
  intro w
  rw [(requests_nodup _).card_eq_countP, (indexed_nodup _).card_eq_countP]
  change (requests (downWords S)).countP (fun t => decide (w <+: t.2)) ≤
    (indexed (downWords S)).countP (fun t => decide (w <+: t.2))
  have hr := List.countP_map (l := requests (downWords S)) (f := Prod.snd)
    (p := fun t => decide (w <+: t))
  have hs := List.countP_map (l := indexed (downWords S)) (f := Prod.snd)
    (p := fun t => decide (w <+: t))
  dsimp only [Function.comp_def] at hr hs
  rw [← hr, ← hs, requests_snd, indexed_snd, List.countP_map]
  rw [downWords_count, downWords_count]
  have hh := Counts.Data.DownToken.capacity (Input.data S) (Counts.Data.input_wellFormed S) w
  rw [Counts.Data.DownToken.histogram _ (fun v => w <+: v.tail),
    Counts.Data.DownToken.histogram _ (fun v => w <+: v)] at hh
  simpa only [Function.comp_def, decide_eq_true_eq] using hh

def computePairs (S : List (List α)) : List (PrefixGreedy.Token α × PrefixGreedy.Token α) :=
  PrefixGreedy.compute (requests (downWords S)) (indexed (downWords S))

@[fun_prop] theorem poly_computePairs : Poly (computePairs : List (List α) → _) := by
  unfold computePairs
  fun_prop

theorem computePairs_correct (S : List (List α)) :
    ((computePairs S).map Prod.fst).Perm (requests (downWords S)) ∧
    ((computePairs S).map Prod.snd).Perm (indexed (downWords S)) ∧
    ∀ p ∈ computePairs S, p.1.2 <+: p.2.2 := by
  apply PrefixGreedy.compute_correct _ _ (requests_nodup _) (indexed_nodup _) (down_capacity S)
  simp only [requests, List.length_map]

theorem downWords_mem {S : List (List α)} {w : List α} (h : w ∈ downWords S) :
    w ∈ (Input.data S).vertices ∧ w ≠ [] := by
  simp only [downWords, List.mem_flatten, List.mem_map] at h
  obtain ⟨ws, ⟨v,hv,rfl⟩,hw⟩ := h
  have hwV : w = v := List.eq_of_mem_replicate hw
  subst v
  have hp : 0 < (Input.data S).down w := by
    have hh := List.length_pos_of_mem hw
    simpa only [List.length_replicate, downValue_eq] using hh
  refine ⟨?_, ?_⟩
  · change w ∈ Input.vertices S
    rw [← vertices_eq S]
    exact List.mem_toFinset.mpr hv
  · intro he
    subst w
    have hz := (Input.data S).count_zero [] (Or.inr rfl)
    simp only [Counts.Data.down, hz, Nat.zero_sub] at hp
    omega

theorem downWords_length (S : List (List α)) : (downWords S).length = (Input.data S).weight := by
  have hh := downWords_count S (fun _ => true)
  simp only [List.countP_true, ite_true] at hh
  rw [hh]
  exact (Input.data S).total_down (Counts.Data.input_wellFormed S)

end Superstring.Computable
namespace Superstring.Computable
open BitCode
variable {α : Type} [Coded α] [DecidableEq α] [Inhabited α]

omit [Coded α] [DecidableEq α] [Inhabited α] in
theorem mem_requests {xs : List (List α)} {i : ℕ} {w : List α} :
    (i,w) ∈ requests xs ↔ ∃ h : i < xs.length, xs[i].tail = w := by
  simp only [requests, List.mem_map]
  constructor
  · rintro ⟨⟨j,v⟩,hj,he⟩
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    obtain ⟨h,rfl⟩ := mem_indexed.mp hj
    exact ⟨h,rfl⟩
  · rintro ⟨h,rfl⟩
    exact ⟨(i,xs[i]),mem_indexed.mpr ⟨h,rfl⟩,rfl⟩

def edges (S : List (List α)) : ArrayPerm.Edges :=
  (computePairs S).map (fun p => (p.1.1,p.2.1))

@[fun_prop] theorem poly_edges : Poly (edges : List (List α) → _) := by
  unfold edges
  exact (BitCode.Poly.map (by fun_prop)).comp poly_computePairs

theorem edges_valid (S : List (List α)) : ArrayPerm.Valid (downWords S).length (edges S) := by
  obtain ⟨hl,hr,_⟩ := computePairs_correct S
  have hl' := hl.map Prod.fst
  have hr' := hr.map Prod.fst
  rw [requests_fst] at hl'
  rw [indexed_fst] at hr'
  constructor
  · simpa only [edges, List.map_map, Function.comp_def] using hl'
  · simpa only [edges, List.map_map, Function.comp_def] using hr'

theorem edge_follows (S : List (List α)) {i j : ℕ} (he : (i,j) ∈ edges S) :
    ∃ (hi : i < (downWords S).length) (hj : j < (downWords S).length),
      (downWords S)[i].tail <+: (downWords S)[j] := by
  obtain ⟨p,hp,hp'⟩ := List.mem_map.mp he
  have h1 : p.1.1 = i := congrArg Prod.fst hp'
  have h2 : p.2.1 = j := congrArg Prod.snd hp'
  have h := computePairs_correct S
  have hR := h.1.mem_iff.mp (List.mem_map_of_mem (f := Prod.fst) hp)
  have hS := h.2.1.mem_iff.mp (List.mem_map_of_mem (f := Prod.snd) hp)
  obtain ⟨hi,hw1⟩ := mem_requests.mp hR
  obtain ⟨hj,hw2⟩ := mem_indexed.mp hS
  subst i; subst j
  exact ⟨hi,hj,by rw [hw1,hw2]; exact h.2.2 p hp⟩

/-- The actual polynomially computed greedy matching, used as a mathematical
threading. Only its finite inverse proof is noncomputable; the forward table is code. -/
noncomputable def arrayThreading (S : List (List α)) :
    Hierarchical.Threading ((Input.data S).vertices : Set (List α)) (Fin (downWords S).length) where
  word := fun i => (downWords S)[i.val]
  nonempty := fun i => (downWords_mem (List.getElem_mem i.isLt)).2
  mem := fun i => (downWords_mem (List.getElem_mem i.isLt)).1
  next := ArrayPerm.perm (edges_valid S)
  follows := fun i => by
    obtain ⟨hi,hj,hpre⟩ := edge_follows S (ArrayPerm.next_mem (edges_valid S) i.isLt)
    exact hpre

omit [Coded α] [DecidableEq α] [Inhabited α] in
theorem countP_sum (xs : List α) (P : α → Bool) :
    xs.countP P = (xs.map (fun a => if P a then 1 else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.countP_cons, List.map_cons, List.sum_cons, ih]; omega

omit [Coded α] [DecidableEq α] [Inhabited α] in
theorem card_get_filter (xs : List α) (P : α → Bool) :
    (Finset.univ.filter (fun i : Fin xs.length => P xs[i.val])).card = xs.countP P := by
  rw [Finset.card_filter, countP_sum, ← List.ofFn_getElem_eq_map, List.sum_ofFn]

theorem arrayThreading_histogram (S : List (List α)) (P : List α → Bool) :
    (Finset.univ.filter (fun i => P ((arrayThreading S).word i))).card =
      ∑ w ∈ (Input.data S).vertices, if P w then (Input.data S).down w else 0 := by
  change (Finset.univ.filter (fun i : Fin (downWords S).length => P (downWords S)[i.val])).card = _
  rw [card_get_filter, downWords_count]

theorem arrayThreading_recorded_count (S : List (List α)) {w : List α} (hw : w ≠ []) :
    Fintype.card ((arrayThreading S).Recorded w) = (Input.data S).count w := by
  rw [Hierarchical.Threading.card_recorded]
  have hh := arrayThreading_histogram S (fun v => decide (w <+: v))
  simp only [decide_eq_true_eq] at hh
  rw [hh, ← Finset.sum_filter]
  exact (Input.data S).down_descendants (Counts.Data.input_wellFormed S) hw

theorem arrayThreading_budget (S : List (List α)) :
    ∑ g : (arrayThreading S).Groups,
      (arrayThreading S).groupPeriod g *
        Fintype.card ((arrayThreading S).Aligned ((arrayThreading S).groupText g)) =
      (Input.data S).weight := by
  rw [Hierarchical.Threading.sum_layer_periods, Fintype.card_fin, downWords_length]

end Superstring.Computable
namespace Superstring.Hierarchical.Threading
variable {α ι : Type} {V : Set (List α)} [Fintype ι]

/-- A single orbit, not the (potentially exponentially large) order of the
whole permutation, bounds each stored primitive phase word. -/
theorem short_text_period (C : Threading V ι) (i : ι) :
    ∃ p : ℕ, 0 < p ∧ p ≤ Fintype.card ι ∧ Function.Periodic (C.text i) (p : ℤ) := by
  let p := Function.minimalPeriod C.next i
  have hp : 0 < p := Function.minimalPeriod_pos_of_mem_periodicPts (C.next.injective.mem_periodicPts i)
  have hb : p ≤ Fintype.card ι := Function.minimalPeriod_le_card
  have hf : (C.next ^ p) i = i := Function.isPeriodicPt_minimalPeriod C.next i
  refine ⟨p,hp,hb,?_⟩
  intro x
  rw [← C.text_zpow, zpow_natCast, hf]

theorem primitive_le_card (C : Threading V ι) {i : ι} {p : ℕ}
    (hp : Primitive (C.text i) p) : p ≤ Fintype.card ι := by
  obtain ⟨q,hq,hb,hper⟩ := C.short_text_period i
  exact (hp.least q hq hper).trans hb

def finiteKey (C : Threading V ι) (i : ι) : List α :=
  textWord (C.text i) 0 (2 * Fintype.card ι)

theorem length_finiteKey (C : Threading V ι) (i : ι) :
    (C.finiteKey i).length = 2 * Fintype.card ι := by
  simp only [finiteKey, length_textWord, sub_zero]
  omega

theorem finiteKey_get (C : Threading V ι) (i : ι) {k : ℕ} (hk : k < 2 * Fintype.card ι) :
    (C.finiteKey i)[k]? = some (C.text i (k : ℤ)) := by
  have hk' : k < (C.finiteKey i).length := by rw [length_finiteKey]; exact hk
  rw [List.getElem?_eq_getElem hk']
  simp only [finiteKey, textWord, List.getElem_ofFn, zero_add]

theorem finiteKey_eq_iff (C : Threading V ι) (i j : ι) :
    C.finiteKey i = C.finiteKey j ↔ C.text i = C.text j := by
  constructor
  · intro he
    obtain ⟨p,hp,hpb,hpi⟩ := C.short_text_period i
    obtain ⟨q,hq,hqb,hqj⟩ := C.short_text_period j
    apply eq_of_long_agreement (C.text i) (C.text j) p q hp hq hpi hqj 0
    intro x hx hxp
    have hk : x.toNat < 2 * Fintype.card ι := by omega
    have hx' : (x.toNat : ℤ) = x := by omega
    have hh := congrArg (fun w : List α => w[x.toNat]?) he
    rw [finiteKey_get C i hk, finiteKey_get C j hk, hx'] at hh
    exact Option.some.inj hh
  · intro he
    simp only [finiteKey, he]

theorem sameText_bounded (C : Threading V ι) (i j : ι) :
    C.SameText i j ↔ ∃ r : ℕ, r < Fintype.card ι ∧
      C.finiteKey ((C.next ^ r) i) = C.finiteKey j := by
  constructor
  · rintro ⟨d,hd⟩
    obtain ⟨p,hp,hb,hper⟩ := C.short_text_period i
    have hm0 := Int.emod_nonneg d (show (p : ℤ) ≠ 0 by omega)
    have hml := Int.emod_lt_of_pos d (show (0 : ℤ) < p by omega)
    let r := (d % (p : ℤ)).toNat
    have hr : (r : ℤ) = d % (p : ℤ) := by dsimp only [r]; omega
    refine ⟨r,by omega,(C.finiteKey_eq_iff _ _).mpr ?_⟩
    funext x
    rw [← zpow_natCast, C.text_zpow]
    have hh := hper.int_mul (d / (p : ℤ)) (x + r)
    have hm := Int.emod_add_ediv_mul d (p : ℤ)
    have he : x + r + d / (p : ℤ) * p = x + d := by omega
    simp only [Int.cast_id, he] at hh
    exact hh.symm.trans (hd x)
  · rintro ⟨r,_,he⟩
    have hh := (C.finiteKey_eq_iff _ _).mp he
    refine ⟨(r : ℤ),?_⟩
    intro x
    have hv := congrFun hh x
    simpa only [← zpow_natCast, C.text_zpow] using hv

end Superstring.Hierarchical.Threading


namespace Superstring.ThreadArray
open BitCode Hierarchical
variable {α : Type} [Coded α] [DecidableEq α] [Inhabited α]

abbrev Code (α : Type) := List (List α) × ArrayPerm.Edges

/-- Finite array semantics: no periodic/oracle tests are hidden in the code. -/
structure Represents {V : Set (List α)} (K : Code α)
    (C : Threading V (Fin K.1.length)) : Prop where
  word : ∀ i, C.word i = K.1[i.val]
  next : ∀ i, (C.next i).val = ArrayPerm.next K.2 i.val

def key (K : Code α) (i : ℕ) : List α :=
  (List.range (2 * K.1.length)).map (fun r =>
    ((K.1[ArrayPerm.power K.2 r i]?).getD []).headD default)

omit [DecidableEq α] in
@[fun_prop] theorem poly_key : Poly (fun q : Code α × ℕ => key q.1 q.2) := by
  unfold key
  exact BitCode.Poly.mapFn
    (f := fun q : (Code α × ℕ) × ℕ =>
      ((q.1.1.1[ArrayPerm.power q.1.1.2 q.2 q.1.2]?).getD []).headD default)
    (by
      apply (BitCode.Poly.headD default).comp
      exact (BitCode.Poly.getD ([] : List α)).comp
        (f := fun q : (Code α × ℕ) × ℕ =>
          (q.1.1.1, ArrayPerm.power q.1.1.2 q.2 q.1.2)) (by fun_prop)) (by fun_prop)

omit [Coded α] [DecidableEq α] [Inhabited α] in
theorem power_eq {K : Code α} {V : Set (List α)} {C : Threading V (Fin K.1.length)}
    (h : Represents K C) (k : ℕ) (i : Fin K.1.length) :
    ArrayPerm.power K.2 k i.val = ((C.next ^ k) i).val := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [ArrayPerm.power, Function.iterate_succ_apply']
    change ArrayPerm.next K.2 (ArrayPerm.power K.2 k i.val) = _
    rw [ih, pow_succ', Equiv.Perm.mul_apply, h.next]

omit [Coded α] [DecidableEq α] in
theorem key_eq {K : Code α} {V : Set (List α)} {C : Threading V (Fin K.1.length)}
    (h : Represents K C) (i : Fin K.1.length) : key K i.val = C.finiteKey i := by
  apply List.ext_getElem
  · simp only [key, List.length_map, List.length_range, Threading.length_finiteKey,
      Fintype.card_fin]
  · intro k hk hk'
    have hki : k < 2 * K.1.length := by
      simpa only [key, List.length_map, List.length_range] using hk
    have ht := C.finiteKey_get i (by simpa only [Fintype.card_fin] using hki)
    rw [List.getElem?_eq_getElem hk'] at ht
    have hr := Option.some.inj ht
    rw [hr]
    simp only [key, List.getElem_map, List.getElem_range, power_eq h]
    rw [List.getElem?_eq_getElem (((C.next ^ k) i).isLt), Option.getD_some, ← h.word]
    simp only [Threading.text, zpow_natCast]
    rw [List.headD_eq_head?_getD, List.head?_eq_some_head]
    rfl

def compatible (K : Code α) (i j : ℕ) : Bool :=
  (List.range K.1.length).any (fun r => equal (key K (ArrayPerm.power K.2 r i)) (key K j))

@[fun_prop] theorem poly_compatible : Poly (fun q : Code α × ℕ × ℕ => compatible q.1 q.2.1 q.2.2) := by
  unfold compatible
  exact BitCode.Poly.anyFn
    (p := fun q : (Code α × ℕ × ℕ) × ℕ =>
      equal (key q.1.1 (ArrayPerm.power q.1.1.2 q.2 q.1.2.1)) (key q.1.1 q.1.2.2))
    (by fun_prop) (by fun_prop)

omit [Coded α] in
theorem compatible_eq {K : Code α} {V : Set (List α)} {C : Threading V (Fin K.1.length)}
    (h : Represents K C) (i j : Fin K.1.length) : compatible K i.val j.val = true ↔ C.SameText i j := by
  rw [C.sameText_bounded]
  simp only [compatible, List.any_eq_true, List.mem_range, equal, decide_eq_true_eq,
    Fintype.card_fin]
  apply exists_congr
  intro r
  rw [power_eq h, key_eq h, key_eq h]

/-- A bounded first-admissible search. Its proof gives both success and order;
it does not assume a choice primitive in the computational model. -/
def first (n : ℕ) (P : ℕ → Bool) : ℕ := ((List.range n).filter P).headD 0

omit [Coded α] [DecidableEq α] [Inhabited α] in
theorem first_spec {n : ℕ} {P : ℕ → Bool} (hw : ∃ k < n, P k = true) :
    first n P < n ∧ P (first n P) = true ∧ ∀ k < n, P k = true → first n P ≤ k := by
  let L := (List.range n).filter P
  have hn : L ≠ [] := by
    obtain ⟨k,hk,hP⟩ := hw
    have hm : k ∈ L := List.mem_filter.mpr ⟨List.mem_range.mpr hk,hP⟩
    intro he; rw [he] at hm; exact List.not_mem_nil hm
  have hs : L.Pairwise (· ≤ ·) := List.pairwise_le_range.filter P
  have hm : L.headD 0 ∈ L := by
    cases hL : L with
    | nil => exact (hn hL).elim
    | cons a l => simp
  obtain ⟨hm,hP⟩ := List.mem_filter.mp hm
  refine ⟨List.mem_range.mp hm,hP,?_⟩
  intro k hk hkP
  have hkm : k ∈ L := List.mem_filter.mpr ⟨List.mem_range.mpr hk,hkP⟩
  change L.headD 0 ≤ k
  cases hL : L with
  | nil => exact (hn hL).elim
  | cons a l =>
    rw [hL] at hs hkm
    simp only [List.headD_cons]
    rcases List.mem_cons.mp hkm with rfl | hk
    · exact le_rfl
    · exact (List.pairwise_cons.mp hs).1 k hk

def period (K : Code α) (i : ℕ) : ℕ :=
  first (K.1.length+1) (fun p => less 0 p && equal (key K (ArrayPerm.power K.2 p i)) (key K i))

@[fun_prop] theorem poly_period : Poly (fun q : Code α × ℕ => period q.1 q.2) := by
  unfold period first
  exact (BitCode.Poly.headD 0).comp (BitCode.Poly.filterFn
    (p := fun q : (Code α × ℕ) × ℕ => less 0 q.2 &&
      equal (key q.1.1 (ArrayPerm.power q.1.1.2 q.2 q.1.2)) (key q.1.1 q.1.2))
    (by fun_prop) (by fun_prop))

omit [Coded α] in
theorem test_period {K : Code α} {V : Set (List α)} {C : Threading V (Fin K.1.length)}
    (h : Represents K C) (i : Fin K.1.length) (p : ℕ) :
    equal (key K (ArrayPerm.power K.2 p i.val)) (key K i.val) = true ↔
      Function.Periodic (C.text i) (p : ℤ) := by
  rw [power_eq h, key_eq h, key_eq h]
  simp only [equal, decide_eq_true_eq, C.finiteKey_eq_iff, funext_iff]
  simp only [← zpow_natCast, C.text_zpow, Function.Periodic]

omit [Coded α] in
theorem period_spec {K : Code α} {V : Set (List α)} {C : Threading V (Fin K.1.length)}
    (h : Represents K C) (i : Fin K.1.length) :
    Primitive (C.text i) (period K i.val) ∧ period K i.val ≤ K.1.length := by
  obtain ⟨p,hp,hpb,hpt⟩ := C.short_text_period i
  have hex : ∃ k < K.1.length+1,
      (less 0 k && equal (key K (ArrayPerm.power K.2 k i.val)) (key K i.val)) = true := by
    refine ⟨p,by simpa only [Fintype.card_fin, Nat.lt_add_one_iff] using hpb,?_⟩
    simp only [Bool.and_eq_true, less, decide_eq_true_eq, test_period h]
    exact ⟨hp,hpt⟩
  have hh := first_spec hex
  change period K i.val < K.1.length+1 ∧ _ at hh
  have ht := hh.2.1
  simp only [Bool.and_eq_true, less, test_period h] at ht
  refine ⟨⟨of_decide_eq_true ht.1,ht.2,?_⟩,by omega⟩
  intro k hk hkt
  by_cases hkn : k < K.1.length+1
  · apply hh.2.2 k hkn
    simp only [Bool.and_eq_true, less, decide_eq_true_eq, test_period h]
    exact ⟨hk,hkt⟩
  · omega

end Superstring.ThreadArray


namespace Superstring.BitCode.Poly
@[fun_prop] theorem div : Poly (fun q : ℕ × ℕ => q.1 / q.2) := by
  have h : Poly (fun q : ℕ × ℕ =>
      if BitCode.equal q.2 0 then 0 else ThreadArray.first (q.1+1) (fun k => BitCode.less q.1 ((k+1)*q.2))) := by
    apply Poly.ite (by fun_prop) (by fun_prop)
    unfold ThreadArray.first
    exact (Poly.headD 0).comp (Poly.filterFn
      (p := fun q : (ℕ × ℕ) × ℕ => BitCode.less q.1.1 ((q.2+1)*q.1.2)) (by fun_prop) (by fun_prop))
  convert h using 1
  funext q
  by_cases hz : q.2 = 0
  · simp only [hz,BitCode.equal,decide_true,↓reduceIte,Nat.div_zero]
  · have hp : 0 < q.2 := Nat.pos_of_ne_zero hz
    simp only [BitCode.equal,decide_eq_true_eq,ite_eq_right hz]
    have hb : q.1 / q.2 < q.1+1 := by have := Nat.div_le_self q.1 q.2; omega
    have ht : BitCode.less q.1 ((q.1/q.2+1)*q.2) = true := by
      apply decide_eq_true
      simpa only [mul_comm] using Nat.lt_mul_div_succ q.1 hp
    obtain ⟨_,hh,hm⟩ := ThreadArray.first_spec (n := q.1+1) (P := fun k => BitCode.less q.1 ((k+1)*q.2)) ⟨q.1/q.2,hb,ht⟩
    apply le_antisymm
    · have he := (Nat.div_lt_iff_lt_mul hp).mpr (show q.1 < (ThreadArray.first (q.1+1) (fun k => BitCode.less q.1 ((k+1)*q.2))+1)*q.2 from of_decide_eq_true hh)
      omega
    · exact hm _ hb ht
end Superstring.BitCode.Poly

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.WalkCode
open BitCode Hierarchical
variable {α : Type}

abbrev Walk (α : Type) := List (List α)

def Edge (s t : List α) : Prop :=
  (∃ a, t = s ++ [a]) ∨ ∃ a, s = a :: t

def Valid (V : Set (List α)) (P : Walk α) : Prop :=
  P ≠ [] ∧ (∀ w ∈ P, w ∈ V) ∧ P.IsChain Edge

def cost (P : Walk α) : ℕ :=
  (P.zip P.tail).countP (fun q => decide (q.1.length < q.2.length))

def join (P Q : Walk α) : Walk α := P ++ Q.tail

def Visits (P : Walk α) (w : List α) : Prop := w ∈ P

namespace Path

def points {V : Set (List α)} : {s t : List α} → Hierarchical.Path V s t → Walk α
  | _, _, .nil s _ => [s]
  | _, _, .up s a _ _ => [s,s ++ [a]]
  | _, _, .down a s _ _ => [a :: s,s]
  | _, _, .trans P Q => join (points P) (points Q)

end Path

@[simp] theorem join_cons (s : List α) (P : Walk α) (t : List α) (Q : Walk α) :
    join (s::P) (t::Q) = s :: (P ++ Q) := rfl

@[simp] theorem cost_nil : cost ([] : Walk α) = 0 := rfl
@[simp] theorem cost_singleton (s : List α) : cost [s] = 0 := rfl
@[simp] theorem cost_cons_cons (s t : List α) (P : Walk α) :
    cost (s::t::P) = (if s.length < t.length then 1 else 0) + cost (t::P) := by
  simp only [cost, List.tail_cons, List.zip_cons_cons, List.countP_cons, decide_eq_true_eq]
  split <;> omega

@[simp] theorem cost_join (P Q : Walk α) (u : List α)
    (hp : P.getLast? = some u) (hq : Q.head? = some u) :
    cost (join P Q) = cost P + cost Q := by
  induction P with
  | nil => simp at hp
  | cons a P ih =>
    cases P with
    | nil =>
      have ha : a = u := by simpa using hp
      cases Q with
      | nil => simp at hq
      | cons b Q =>
        have hb : b = u := by simpa using hq
        subst a; subst b
        simp only [join_cons, List.nil_append, cost_singleton, Nat.zero_add]
    | cons b P =>
      have hh : (b :: P).getLast? = some u := by simpa using hp
      have ht := ih hh
      change cost (a :: (b :: P ++ Q.tail)) = _
      change cost (a :: b :: (P ++ Q.tail)) = _
      rw [cost_cons_cons]
      change (if a.length < b.length then 1 else 0) + cost (join (b::P) Q) = _
      rw [ht, cost_cons_cons]
      omega

 theorem cost_eq_edges {P : Walk α} : cost P ≤ P.length := by
  exact (List.countP_le_length).trans (by simp [List.length_zip])

 theorem valid_nil {V : Set (List α)} (s : List α) (hs : s ∈ V) : Valid V [s] := by
  exact ⟨by simp, by simpa using hs, by simp⟩

 theorem valid_step {V : Set (List α)} {s t : List α}
    (hs : s ∈ V) (ht : t ∈ V) (he : Edge s t) : Valid V [s,t] := by
  exact ⟨by simp, by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro w h; rcases h with rfl|rfl <;> assumption,
    by simpa using he⟩

 theorem edge_path {V : Set (List α)} {s t : List α}
    (hs : s ∈ V) (ht : t ∈ V) (he : Edge s t) :
    ∃ P : Hierarchical.Path V s t, Path.points P = [s,t] ∧
      P.cost = (if s.length < t.length then 1 else 0) ∧
      ∀ w, P.Visits w ↔ w = s ∨ w = t := by
  rcases he with ⟨a,rfl⟩ | ⟨a,rfl⟩
  · exact ⟨.up s a hs ht, rfl, by simp [Hierarchical.Path.cost], by intro w; rfl⟩
  · exact ⟨.down a t hs ht, rfl, by simp [Hierarchical.Path.cost], by intro w; rfl⟩

 theorem realize {V : Set (List α)} {s : List α} {P : Walk α}
    (hv : Valid V (s::P)) :
    ∃ t, ∃ Q : Hierarchical.Path V s t, (s::P).getLast? = some t ∧
      Path.points Q = s::P ∧ Q.cost = cost (s::P) ∧
      ∀ w, Q.Visits w ↔ w ∈ s::P := by
  induction P generalizing s with
  | nil =>
    refine ⟨s,.nil s (hv.2.1 s (by simp)),rfl,rfl,rfl,?_⟩
    intro w
    simp only [Hierarchical.Path.Visits, List.mem_singleton]
  | cons t P ih =>
    have hchain := List.isChain_cons_cons.mp hv.2.2
    have ht : Valid V (t::P) := ⟨by simp, fun w hw => hv.2.1 w (List.mem_cons_of_mem _ hw), hchain.2⟩
    obtain ⟨u,Q,hl,hQ,hcQ,hvQ⟩ := ih ht
    obtain ⟨R,hR,hcR,hvR⟩ := edge_path (hv.2.1 s (by simp)) (hv.2.1 t (by simp)) hchain.1
    refine ⟨u,R.trans Q,?_,?_,?_,?_⟩
    · simpa using hl
    · simp only [Path.points, hR,hQ,join_cons,List.cons_append,List.nil_append]
    · simp only [Hierarchical.Path.cost_trans,hcR,hcQ,cost_cons_cons]
    · intro w
      simp only [Hierarchical.Path.Visits,hvR,hvQ,List.mem_cons]
      tauto

end Superstring.WalkCode

namespace Superstring.WalkCode
open BitCode Hierarchical
variable {α : Type}

 theorem mem_join {P Q : Walk α} {u w : List α}
    (hp : P.getLast? = some u) (hq : Q.head? = some u) :
    w ∈ join P Q ↔ w ∈ P ∨ w ∈ Q := by
  cases Q with
  | nil => simp at hq
  | cons x Q =>
    have hx : x = u := by simpa using hq
    subst x
    have hu : u ∈ P := List.mem_of_getLast? hp
    simp only [join,List.tail_cons,List.mem_append,List.mem_cons]
    constructor
    · intro h; rcases h with h|h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · intro h; rcases h with h|rfl|h
      · exact Or.inl h
      · exact Or.inl hu
      · exact Or.inr h

 theorem valid_join {V : Set (List α)} {P Q : Walk α} {u : List α}
    (hP : Valid V P) (hQ : Valid V Q)
    (hp : P.getLast? = some u) (hq : Q.head? = some u) : Valid V (join P Q) := by
  refine ⟨?_,?_,?_⟩
  · intro he
    exact hP.1 (List.append_eq_nil_iff.mp he).1
  · intro w hw
    rcases (mem_join hp hq).mp hw with hw|hw
    · exact hP.2.1 _ hw
    · exact hQ.2.1 _ hw
  · apply hP.2.2.append hQ.2.2.tail
    intro x hx y hy
    have hx' : x = u := by
      have hh : u = x := by simpa only [hp,Option.mem_some_iff] using hx
      exact hh.symm
    subst x
    cases Q with
    | nil => simp at hq
    | cons a Q =>
      have ha : a = u := by simpa using hq
      subst a
      exact (List.isChain_cons.mp hQ.2.2).1 y hy

@[simp] theorem head_join {P Q : Walk α} (hP : P ≠ []) :
    (join P Q).head? = P.head? := by
  cases P with
  | nil => contradiction
  | cons s P => rfl

@[simp] theorem last_join {P Q : Walk α} {u : List α}
    (hp : P.getLast? = some u) (hq : Q.head? = some u) :
    (join P Q).getLast? = Q.getLast? := by
  cases Q with
  | nil => simp at hq
  | cons a Q =>
    cases Q with
    | nil =>
      have ha : a = u := by simpa using hq
      subst a
      simpa only [join,List.tail_cons,List.append_nil,List.getLast?_singleton] using hp
    | cons b Q =>
      simp only [join,List.tail_cons,List.getLast?_append]
      rw [List.getLast?_eq_some_getLast (by simp)]
      rfl

 theorem points_spec {V : Set (List α)} {s t : List α} (P : Hierarchical.Path V s t) :
    Valid V (Path.points P) ∧ (Path.points P).head? = some s ∧
      (Path.points P).getLast? = some t ∧ cost (Path.points P) = P.cost ∧
      ∀ w, w ∈ Path.points P ↔ P.Visits w := by
  induction P with
  | nil s hs =>
    exact ⟨valid_nil s hs,rfl,rfl,rfl,by intro w; simp [Path.points,Hierarchical.Path.Visits]⟩
  | up s a hs ht =>
    exact ⟨valid_step hs ht (Or.inl ⟨a,rfl⟩),rfl,rfl,
      by simp [Path.points,Hierarchical.Path.cost],by intro w; simp [Path.points,Hierarchical.Path.Visits]⟩
  | down a s hs ht =>
    exact ⟨valid_step hs ht (Or.inr ⟨a,rfl⟩),rfl,rfl,
      by simp [Path.points,Hierarchical.Path.cost],by intro w; simp [Path.points,Hierarchical.Path.Visits]⟩
  | trans P Q ihP ihQ =>
    refine ⟨valid_join ihP.1 ihQ.1 ihP.2.2.1 ihQ.2.1,?_,?_,?_,?_⟩
    · exact (head_join ihP.1.1).trans ihP.2.1
    · exact (last_join ihP.2.2.1 ihQ.2.1).trans ihQ.2.2.1
    · change cost (join (Path.points P) (Path.points Q)) = _
      rw [cost_join _ _ _ ihP.2.2.1 ihQ.2.1,ihP.2.2.2.1,ihQ.2.2.2.1]
      rfl
    · intro w
      change w ∈ join (Path.points P) (Path.points Q) ↔ _
      rw [mem_join ihP.2.2.1 ihQ.2.1,ihP.2.2.2.2,ihQ.2.2.2.2]
      rfl

 theorem length_cost {V : Set (List α)} {s : List α} {P : Walk α}
    (hv : Valid V (s::P)) :
    P.length + ((s::P).getLast?.getD []).length = 2 * cost (s::P) + s.length := by
  induction P generalizing s with
  | nil => simp
  | cons t P ih =>
    have he := List.isChain_cons_cons.mp hv.2.2
    have ht : Valid V (t::P) := ⟨by simp,fun w hw => hv.2.1 w (List.mem_cons_of_mem _ hw),he.2⟩
    have hi := ih ht
    simp only [List.length_cons,cost_cons_cons]
    have hl : (s :: t :: P).getLast? = (t :: P).getLast? := by simp
    rw [hl]
    rcases he.1 with ⟨a,rfl⟩|⟨a,rfl⟩
    · simp only [List.length_append,List.length_singleton] at hi ⊢
      rw [ite_eq_left (by omega)]
      omega
    · simp only [List.length_cons] at hi ⊢
      rw [ite_eq_right (by omega)]
      omega

variable [Coded α]

@[fun_prop] theorem poly_join : Poly (fun q : Walk α × Walk α => join q.1 q.2) := by
  unfold join
  fun_prop

@[fun_prop] theorem poly_zip : Poly (fun p : Walk α × Walk α => p.1.zip p.2) := by
  have h : Poly (fun p : Walk α × Walk α =>
      (List.range (min p.1.length p.2.length)).map
        (fun i => (p.1[i]?.getD [], p.2[i]?.getD []))) := by
    apply BitCode.Poly.mapFn (f := fun q : (Walk α × Walk α) × ℕ =>
      (q.1.1[q.2]?.getD [], q.1.2[q.2]?.getD []))
    · exact ((BitCode.Poly.getD ([] : List α)).comp
          (f := fun q : (Walk α × Walk α) × ℕ => (q.1.1,q.2)) (by fun_prop)).pair
        ((BitCode.Poly.getD ([] : List α)).comp
          (f := fun q : (Walk α × Walk α) × ℕ => (q.1.2,q.2)) (by fun_prop))
    · fun_prop
  convert h using 1
  funext p
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_zip,List.getElem_map,List.getElem_range]
    have hi1 : i < p.1.length := (lt_min_iff.mp (by simpa using h1)).1
    have hi2 : i < p.2.length := (lt_min_iff.mp (by simpa using h1)).2
    simp only [List.getElem?_eq_getElem hi1,List.getElem?_eq_getElem hi2,Option.getD_some]

@[fun_prop] theorem poly_cost : Poly (fun P : Walk α => cost P) := by
  have h : Poly (fun P : Walk α =>
      ((P.zip P.tail).filter (fun q => decide (q.1.length < q.2.length))).length) := by
    apply BitCode.Poly.length.comp
    apply BitCode.Poly.filterFn (p := fun q : Walk α × (List α × List α) =>
      decide (q.2.1.length < q.2.2.length))
    · fun_prop
    · fun_prop
  simpa only [cost,List.countP_eq_length_filter] using h

end Superstring.WalkCode


namespace Superstring.WalkCode
open BitCode Hierarchical
variable {α : Type}

def delete (a b : List α) : Walk α :=
  (List.range (a.length+1)).map (fun i => (a++b).drop i)

def append (a b : List α) : Walk α :=
  (List.range (b.length+1)).map (fun i => a++b.take i)

def gap (w : List α) : Walk α := [[]] ++ w.flatMap (fun a => [[a],[]])

@[simp] theorem delete_nil (b : List α) : delete [] b = [b] := by simp [delete]
@[simp] theorem delete_cons (a : α) (as b : List α) :
    delete (a::as) b = (a::(as++b)) :: delete as b := by
  simp only [delete,List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map,
    List.cons_append,List.drop_zero,List.drop_succ_cons,Function.comp_def]

@[simp] theorem append_nil (a : List α) : append a [] = [a] := by simp [append]
@[simp] theorem append_cons (a : List α) (b : α) (bs : List α) :
    append a (b::bs) = a :: append (a++[b]) bs := by
  simp only [append,List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map,
    List.take_zero,List.append_nil,List.take_succ_cons,Function.comp_def]
  simp only [List.append_assoc,List.singleton_append]

@[simp] theorem gap_nil : gap ([] : List α) = [[]] := rfl
@[simp] theorem gap_cons (a : α) (as : List α) :
    gap (a::as) = [] :: [a] :: gap as := by rfl

 theorem points_copy {V : Set (List α)} {s t s' t' : List α}
    (P : Hierarchical.Path V s t) (hs : s = s') (ht : t = t') :
    Path.points (P.copy hs ht) = Path.points P := by subst s'; subst t'; rfl

 theorem points_delete {V : Set (List α)} (closed : SubstringClosed V)
    (a b : List α) (h : a++b ∈ V) :
    Path.points (Hierarchical.Path.deletePrefix closed a b h) = delete a b := by
  induction a with
  | nil => simp [Hierarchical.Path.deletePrefix,Path.points]
  | cons a as ih =>
    simp only [Hierarchical.Path.deletePrefix,Path.points,ih,delete_cons]
    have hhead : (delete as b).head? = some (as++b) := by
      unfold delete
      rw [List.range_succ_eq_map]
      simp only [List.map_cons,List.drop_zero,List.head?_cons]
    cases he : delete as b with
    | nil => simp [he] at hhead
    | cons x xs =>
      have hx : x = as++b := by simpa [he] using hhead
      simp [join,hx]

 theorem points_append {V : Set (List α)} (closed : SubstringClosed V)
    (a b : List α) (h : a++b ∈ V) :
    Path.points (Hierarchical.Path.appendSuffix closed a b h) = append a b := by
  induction b generalizing a with
  | nil => simp [Hierarchical.Path.appendSuffix,points_copy,Path.points]
  | cons b bs ih =>
    simp only [Hierarchical.Path.appendSuffix,points_copy,Path.points,ih,append_cons]
    unfold join
    have hhead : (append (a++[b]) bs).head? = some (a++[b]) := by
      rw [← ih _ (by simpa only [List.append_assoc,List.singleton_append] using h)]
      exact (points_spec _).2.1
    cases he : append (a++[b]) bs with
    | nil => simp [he] at hhead
    | cons x xs =>
      have hx : x = a++[b] := by simpa [he] using hhead
      simp [hx]

 theorem points_gap {V : Set (List α)} (h0 : ([] : List α) ∈ V)
    (w : List α) (h : ∀ a ∈ w, [a] ∈ V) :
    Path.points (Hierarchical.Path.readGap h0 w h) = gap w := by
  induction w with
  | nil => rfl
  | cons a as ih => simp [Hierarchical.Path.readGap,Path.points,ih,join,gap]

 theorem delete_spec {V : Set (List α)} (closed : SubstringClosed V)
    (a b : List α) (h : a++b ∈ V) :
    Valid V (delete a b) ∧ (delete a b).head? = some (a++b) ∧
      (delete a b).getLast? = some b ∧ cost (delete a b) = 0 := by
  have hh := points_spec (Hierarchical.Path.deletePrefix closed a b h)
  rw [points_delete] at hh
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1.trans (Hierarchical.Path.cost_deletePrefix ..)⟩

 theorem append_spec {V : Set (List α)} (closed : SubstringClosed V)
    (a b : List α) (h : a++b ∈ V) :
    Valid V (append a b) ∧ (append a b).head? = some a ∧
      (append a b).getLast? = some (a++b) ∧ cost (append a b) = b.length := by
  have hh := points_spec (Hierarchical.Path.appendSuffix closed a b h)
  rw [points_append] at hh
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1.trans (Hierarchical.Path.cost_appendSuffix ..)⟩

 theorem gap_spec {V : Set (List α)} (h0 : ([] : List α) ∈ V)
    (w : List α) (h : ∀ a ∈ w, [a] ∈ V) :
    Valid V (gap w) ∧ (gap w).head? = some [] ∧
      (gap w).getLast? = some [] ∧ cost (gap w) = w.length := by
  have hh := points_spec (Hierarchical.Path.readGap h0 w h)
  rw [points_gap] at hh
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1.trans (Hierarchical.Path.cost_readGap ..)⟩

 theorem mem_delete (a b : List α) (i : ℕ) (hi : i ≤ a.length) :
    (a++b).drop i ∈ delete a b := by
  exact List.mem_map.mpr ⟨i,List.mem_range.mpr (by omega),rfl⟩

 theorem mem_append (a b : List α) (i : ℕ) (hi : i ≤ b.length) :
    a++b.take i ∈ append a b := by
  exact List.mem_map.mpr ⟨i,List.mem_range.mpr (by omega),rfl⟩

variable [Coded α]

@[fun_prop] theorem poly_delete : Poly (fun q : List α × List α => delete q.1 q.2) := by
  unfold delete
  exact BitCode.Poly.mapFn
    (f := fun q : (List α × List α) × ℕ => (q.1.1++q.1.2).drop q.2)
    (by fun_prop) (by fun_prop)

@[fun_prop] theorem poly_append : Poly (fun q : List α × List α => append q.1 q.2) := by
  unfold append
  exact BitCode.Poly.mapFn
    (f := fun q : (List α × List α) × ℕ => q.1.1++q.1.2.take q.2)
    (by fun_prop) (by fun_prop)

@[fun_prop] theorem poly_gap : Poly (gap : List α → Walk α) := by
  have hm : Poly (fun w : List α => w.map (fun a => [[a],[]])) :=
    BitCode.Poly.map (show Poly (fun a : α => [[a],[]]) from by fun_prop)
  have hf := BitCode.Poly.flatten.comp hm
  have ha : Poly (fun w : List α => [[]] ++ (w.map (fun a => [[a],[]])).flatten) := by
    fun_prop
  exact ha

end Superstring.WalkCode


namespace Superstring.WalkCode
open BitCode Hierarchical
variable {α : Type}

def Runs (V : Set (List α)) (s t : List α) (P : Walk α) : Prop :=
  Valid V P ∧ P.head? = some s ∧ P.getLast? = some t

 theorem runs_join {V : Set (List α)} {s t u : List α} {P Q : Walk α}
    (hp : Runs V s t P) (hq : Runs V t u Q) : Runs V s u (join P Q) :=
  ⟨valid_join hp.1 hq.1 hp.2.2 hq.2.1,
    (head_join hp.1.1).trans hp.2.1,(last_join hp.2.2 hq.2.1).trans hq.2.2⟩

 theorem runs_points {V : Set (List α)} {s t : List α} (P : Hierarchical.Path V s t) :
    Runs V s t (Path.points P) := by
  have h := points_spec P
  exact ⟨h.1,h.2.1,h.2.2.1⟩

 theorem take_drop_join (P : Walk α) {i : ℕ} (_hi : i < P.length) :
    join (P.take (i+1)) (P.drop i) = P := by
  simp only [join,List.tail_drop]
  exact List.take_append_drop _ _

 theorem split_runs {V : Set (List α)} {s t : List α} {P : Walk α}
    (hp : Runs V s t P) {i : ℕ} (hi : i < P.length) :
    Runs V s P[i] (P.take (i+1)) ∧ Runs V P[i] t (P.drop i) := by
  have ht : P.take (i+1) ≠ [] := List.length_pos_iff.mp (by simp only [List.length_take]; omega)
  have hd : P.drop i ≠ [] := List.length_pos_iff.mp (by simp only [List.length_drop]; omega)
  have htake : Valid V (P.take (i+1)) :=
    ⟨ht,fun w hw => hp.1.2.1 w (List.mem_of_mem_take hw),hp.1.2.2.take _⟩
  have hdrop : Valid V (P.drop i) :=
    ⟨hd,fun w hw => hp.1.2.1 w (List.mem_of_mem_drop hw),hp.1.2.2.drop _⟩
  refine ⟨⟨htake,?_,?_⟩,⟨hdrop,?_,?_⟩⟩
  · simpa only [List.head?_take,ite_eq_right (by omega : i+1 ≠ 0)] using hp.2.1
  · simp only [List.getLast?_take,ite_eq_right (by omega : i+1 ≠ 0),Nat.add_sub_cancel,
      List.getElem?_eq_getElem hi,Option.some_or]
  · simp [List.head?_drop,List.getElem?_eq_getElem hi]
  · simpa only [List.getLast?_drop,ite_eq_right (by omega : ¬P.length ≤ i)] using hp.2.2

def rotate (P : Walk α) (i : ℕ) : Walk α := join (P.drop i) (P.take (i+1))

 theorem rotate_spec {V : Set (List α)} {s : List α} {P : Walk α}
    (hp : Runs V s s P) {i : ℕ} (hi : i < P.length) :
    Runs V P[i] P[i] (rotate P i) ∧ cost (rotate P i) = cost P ∧
      ∀ w, w ∈ rotate P i ↔ w ∈ P := by
  obtain ⟨hA,hB⟩ := split_runs hp hi
  refine ⟨runs_join hB hA,?_,?_⟩
  · unfold rotate
    rw [cost_join _ _ _ hB.2.2 hA.2.1]
    have hh := cost_join _ _ _ hA.2.2 hB.2.1
    rw [take_drop_join P hi] at hh
    omega
  · intro w
    unfold rotate
    rw [mem_join hB.2.2 hA.2.1]
    have hh := @mem_join α (P.take (i+1)) (P.drop i) P[i] w hA.2.2 hB.2.1
    rw [take_drop_join P hi] at hh
    tauto

def insertAt (P Q : Walk α) (i : ℕ) : Walk α :=
  join (join (P.take (i+1)) Q) (P.drop i)

 theorem insertAt_spec {V : Set (List α)} {s t : List α} {P Q : Walk α}
    (hp : Runs V s t P) {i : ℕ} (hi : i < P.length)
    (hq : Runs V P[i] P[i] Q) :
    Runs V s t (insertAt P Q i) ∧ cost (insertAt P Q i) = cost P + cost Q ∧
      ∀ w, w ∈ insertAt P Q i ↔ w ∈ P ∨ w ∈ Q := by
  obtain ⟨hA,hB⟩ := split_runs hp hi
  have hAQ := runs_join hA hq
  refine ⟨runs_join hAQ hB,?_,?_⟩
  · unfold insertAt
    rw [cost_join _ _ _ hAQ.2.2 hB.2.1,cost_join _ _ _ hA.2.2 hq.2.1]
    have hh := cost_join _ _ _ hA.2.2 hB.2.1
    rw [take_drop_join P hi] at hh
    omega
  · intro w
    unfold insertAt
    rw [mem_join hAQ.2.2 hB.2.1,mem_join hA.2.2 hq.2.1]
    have hh := @mem_join α (P.take (i+1)) (P.drop i) P[i] w hA.2.2 hB.2.1
    rw [take_drop_join P hi] at hh
    tauto

variable [Coded α]
@[fun_prop] theorem poly_rotate : Poly (fun q : Walk α × ℕ => rotate q.1 q.2) := by
  unfold rotate
  fun_prop
@[fun_prop] theorem poly_insertAt : Poly (fun q : Walk α × Walk α × ℕ =>
    insertAt q.1 q.2.1 q.2.2) := by
  unfold insertAt
  fun_prop

end Superstring.WalkCode


namespace Superstring.WalkCode
open BitCode Hierarchical
variable {α : Type} [DecidableEq α]

def locate (P : Walk α) (w : List α) : ℕ :=
  ThreadArray.first P.length (fun i => equal (P[i]?.getD []) w)

def meeting (P Q : Walk α) : ℕ :=
  ThreadArray.first P.length (fun i => member (P[i]?.getD []) Q)

def splice (P Q : Walk α) : Walk α :=
  let i := meeting P Q
  let j := locate Q (P[i]?.getD [])
  insertAt P (rotate Q j) i

 theorem locate_spec {P : Walk α} {w : List α} (hw : w ∈ P) :
    locate P w < P.length ∧ P[locate P w]?.getD [] = w := by
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hw
  have hex : ∃ i < P.length, equal (P[i]?.getD []) w = true := by
    exact ⟨i,hi,by simp [List.getElem?_eq_getElem hi,he,equal]⟩
  have hh := ThreadArray.first_spec hex
  exact ⟨hh.1, of_decide_eq_true hh.2.1⟩

 theorem meeting_spec {P Q : Walk α} (h : ∃ w, w ∈ P ∧ w ∈ Q) :
    meeting P Q < P.length ∧ P[meeting P Q]?.getD [] ∈ Q := by
  obtain ⟨w,hwP,hwQ⟩ := h
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hwP
  have hex : ∃ i < P.length, member (P[i]?.getD []) Q = true := by
    exact ⟨i,hi,by simp [List.getElem?_eq_getElem hi,he,hwQ]⟩
  have hh := ThreadArray.first_spec hex
  exact ⟨hh.1,(member_eq ..).mp hh.2.1⟩

 theorem splice_spec {V : Set (List α)} {s t u : List α} {P Q : Walk α}
    (hp : Runs V s t P) (hq : Runs V u u Q) (hm : ∃ w, w ∈ P ∧ w ∈ Q) :
    Runs V s t (splice P Q) ∧ cost (splice P Q) = cost P + cost Q ∧
      ∀ w, w ∈ splice P Q ↔ w ∈ P ∨ w ∈ Q := by
  obtain ⟨hi,hm⟩ := meeting_spec hm
  obtain ⟨hj,he⟩ := locate_spec hm
  have he' : Q[locate Q (P[meeting P Q]?.getD [])] = P[meeting P Q] := by
    rw [List.getElem?_eq_getElem hj,Option.getD_some] at he
    simpa only [List.getElem?_eq_getElem hi,Option.getD_some] using he
  obtain ⟨hr,hc,hv⟩ := rotate_spec hq hj
  rw [he'] at hr
  obtain ⟨hR,hRc,hRv⟩ := insertAt_spec hp hi hr
  exact ⟨hR,by simpa only [splice,hc] using hRc,by intro w; simpa only [splice,hv] using hRv w⟩

variable [Coded α]
@[fun_prop] theorem poly_locate : Poly (fun q : Walk α × List α => locate q.1 q.2) := by
  unfold locate ThreadArray.first
  exact (BitCode.Poly.headD 0).comp (BitCode.Poly.filterFn
    (p := fun q : (Walk α × List α) × ℕ => equal (q.1.1[q.2]?.getD []) q.1.2)
    (BitCode.Poly.equal.comp (((BitCode.Poly.getD ([] : List α)).comp
      (f := fun q : (Walk α × List α) × ℕ => (q.1.1,q.2)) (by fun_prop)).pair (by fun_prop))) (by fun_prop))
@[fun_prop] theorem poly_meeting : Poly (fun q : Walk α × Walk α => meeting q.1 q.2) := by
  unfold meeting ThreadArray.first
  exact (BitCode.Poly.headD 0).comp (BitCode.Poly.filterFn
    (p := fun q : (Walk α × Walk α) × ℕ => member (q.1.1[q.2]?.getD []) q.1.2)
    (BitCode.Poly.member.comp (((BitCode.Poly.getD ([] : List α)).comp
      (f := fun q : (Walk α × Walk α) × ℕ => (q.1.1,q.2)) (by fun_prop)).pair (by fun_prop))) (by fun_prop))
@[fun_prop] theorem poly_splice : Poly (fun q : Walk α × Walk α => splice q.1 q.2) := by
  have hh : Poly (fun q : Walk α × Walk α => q.1[meeting q.1 q.2]?.getD []) :=
    (BitCode.Poly.getD ([] : List α)).comp (BitCode.Poly.fst.pair poly_meeting)
  unfold splice
  dsimp only
  fun_prop

 omit [DecidableEq α] in
 theorem size_join (P Q : Walk α) : bitSize (join P Q) ≤ bitSize P + bitSize Q := by
  have hh := bitSize_append P Q.tail
  have ht := bitSize_sublist (List.tail_sublist Q)
  unfold join
  omega

 omit [DecidableEq α] in
 theorem size_rotate (P : Walk α) (i : ℕ) : bitSize (rotate P i) ≤ 2 * bitSize P := by
  have hh := size_join (P.drop i) (P.take (i+1))
  have hd := bitSize_sublist (List.drop_sublist i P)
  have ht := bitSize_sublist (List.take_sublist (i+1) P)
  unfold rotate
  omega

 omit [DecidableEq α] in
 theorem size_insertAt (P Q : Walk α) (i : ℕ) :
    bitSize (insertAt P Q i) ≤ bitSize P + bitSize Q := by
  have he : insertAt P Q i = (P.take (i+1) ++ Q.tail) ++ P.drop (i+1) := by
    simp only [insertAt,join,List.tail_drop]
  rw [he]
  have h1 := bitSize_append (P.take (i+1)) Q.tail
  have h2 := bitSize_append (P.take (i+1) ++ Q.tail) (P.drop (i+1))
  have h3 := bitSize_append (P.take (i+1)) (P.drop (i+1))
  rw [List.take_append_drop] at h3
  have ht := bitSize_sublist (List.tail_sublist Q)
  omega
 theorem size_splice (P Q : Walk α) : bitSize (splice P Q) ≤ bitSize P + 2 * bitSize Q := by
  exact (size_insertAt _ _ _).trans (Nat.add_le_add_left (size_rotate _ _) _)

 def fill (P : Walk α) (Qs : List (Walk α)) : Walk α := Qs.foldl splice P
@[fun_prop] theorem poly_fill : Poly (fun q : Walk α × List (Walk α) => fill q.1 q.2) := by
  have hs : ∀ P Q : Walk α, bitSize (splice P Q) ≤ bitSize P +
      (2 * Polynomial.X : Polynomial ℕ).eval (bitSize Q) := by
    intro P Q
    simpa only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X] using size_splice P Q
  exact (BitCode.Poly.foldl_additive poly_splice (2 * Polynomial.X) hs).comp
    (BitCode.Poly.snd.pair BitCode.Poly.fst)

omit [Coded α] in
 theorem fill_spec {V : Set (List α)} {s t : List α} (P : Walk α) (Qs : List (Walk α))
    (hp : Runs V s t P) (hq : ∀ Q ∈ Qs, ∃ u, Runs V u u Q)
    (hm : ∀ Q ∈ Qs, ∃ w, w ∈ P ∧ w ∈ Q) :
    Runs V s t (fill P Qs) ∧ cost (fill P Qs) = cost P + (Qs.map cost).sum ∧
      ∀ w, w ∈ fill P Qs ↔ w ∈ P ∨ ∃ Q ∈ Qs, w ∈ Q := by
  induction Qs generalizing P with
  | nil => exact ⟨hp,by simp [fill],by simp [fill]⟩
  | cons Q Qs ih =>
    obtain ⟨u,hu⟩ := hq Q (by simp)
    obtain ⟨hr,hc,hv⟩ := splice_spec hp hu (hm Q (by simp))
    obtain ⟨hR,hC,hV⟩ := ih (splice P Q) hr
      (fun R hR => hq R (List.mem_cons_of_mem _ hR)) (by
        intro R hR
        obtain ⟨w,hw,hwR⟩ := hm R (List.mem_cons_of_mem _ hR)
        exact ⟨w,(hv w).mpr (Or.inl hw),hwR⟩)
    refine ⟨hR,?_,?_⟩
    · change cost (fill (splice P Q) Qs) = _
      rw [hC,hc,List.map_cons,List.sum_cons]
      omega
    · intro w
      change w ∈ fill (splice P Q) Qs ↔ _
      rw [hV,hv]
      simp only [List.mem_cons,or_and_right,exists_or,exists_eq_left]
      tauto
end Superstring.WalkCode

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.ThreadArray
open BitCode Hierarchical
variable {α : Type} [Coded α] [DecidableEq α] [Inhabited α]

def aligned (K : Code α) (g : ℕ) : List ℕ :=
  (List.range K.1.length).filter (fun i => equal (key K i) (key K g))

@[fun_prop] theorem poly_aligned : Poly (fun q : Code α × ℕ => aligned q.1 q.2) := by
  unfold aligned
  exact BitCode.Poly.filterFn
    (p := fun q : (Code α × ℕ) × ℕ => equal (key q.1.1 q.2) (key q.1.1 q.1.2))
    (by fun_prop) (by fun_prop)

omit [Coded α] [DecidableEq α] [Inhabited α] in
theorem countP_range (n : ℕ) (P : ℕ → Bool) :
    (List.range n).countP P = (Finset.univ.filter (fun i : Fin n => P i.val)).card := by
  have he : List.range n = List.ofFn (fun i : Fin n => i.val) := by
    apply List.ext_getElem <;> simp
  rw [he, OrderStats.countP_ofFn, Finset.card_filter]

omit [Coded α] in
theorem aligned_length {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (g : Fin K.1.length) :
    (aligned K g.val).length = Fintype.card (C.Aligned (C.text g)) := by
  classical
  change (aligned K g.val).length = Fintype.card {i : Fin K.1.length // C.text i = C.text g}
  rw [Fintype.card_subtype]
  rw [aligned, ← List.countP_eq_length_filter, countP_range]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i _
  simp only [equal, decide_eq_true_eq, key_eq h, C.finiteKey_eq_iff]

omit [DecidableEq α] [Inhabited α] in
def atLength (K : Code α) (r i : ℕ) : ℕ :=
  ((K.1[ArrayPerm.power K.2 r i]?).getD []).length

omit [DecidableEq α] [Inhabited α] in
@[fun_prop] theorem poly_atLength : Poly (fun q : Code α × ℕ × ℕ => atLength q.1 q.2.1 q.2.2) := by
  unfold atLength
  exact BitCode.Poly.length.comp ((BitCode.Poly.getD ([] : List α)).comp
    (f := fun q : Code α × ℕ × ℕ => (q.1.1,ArrayPerm.power q.1.2 q.2.1 q.2.2)) (by fun_prop))

omit [Coded α] [DecidableEq α] [Inhabited α] in
theorem atLength_eq {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (r : ℕ) (i : Fin K.1.length) :
    atLength K r i.val = (C.word ((C.next ^ r) i)).length := by
  simp only [atLength, power_eq h, List.getElem?_eq_getElem (((C.next ^ r) i).isLt),
    Option.getD_some, ← h.word]

omit [DecidableEq α] [Inhabited α] in
theorem atLength_bound (K : Code α) (r i : ℕ) : atLength K r i ≤ bitSize K := by
  unfold atLength
  cases he : K.1[ArrayPerm.power K.2 r i]? with
  | none => simp
  | some w =>
    simp only [Option.getD_some]
    have hm : w ∈ K.1 := List.mem_of_getElem? he
    have hh := bitSize_mem hm
    have hl := length_le_bitSize w
    have hk : bitSize K = bitSize K.1 + bitSize K.2 := by cases K; exact bitSize_prod _ _
    omega

def rankLength (K : Code α) (g j r : ℕ) : ℕ :=
  first (bitSize K + 1) (fun l =>
    less j ((aligned K g).filter (fun i => lessEq (atLength K r i) l)).length)

@[fun_prop] theorem poly_rankLength : Poly (fun q : Code α × ℕ × ℕ × ℕ =>
    rankLength q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  have hc : Poly (fun q : (Code α × ℕ × ℕ × ℕ) × ℕ =>
      ((aligned q.1.1 q.1.2.1).filter (fun i => lessEq (atLength q.1.1 q.1.2.2.2 i) q.2)).length) := by
    apply BitCode.Poly.length.comp
    exact BitCode.Poly.filterFn
      (p := fun q : ((Code α × ℕ × ℕ × ℕ) × ℕ) × ℕ =>
        lessEq (atLength q.1.1.1 q.1.1.2.2.2 q.2) q.1.2)
      (by fun_prop) (by fun_prop)
  unfold rankLength first
  exact (BitCode.Poly.headD 0).comp (BitCode.Poly.filterFn
    (p := fun q : (Code α × ℕ × ℕ × ℕ) × ℕ => less q.1.2.2.1
      ((aligned q.1.1 q.1.2.1).filter (fun i => lessEq (atLength q.1.1 q.1.2.2.2 i) q.2)).length)
    (by fun_prop) (by fun_prop))

noncomputable def lengthValues {K : Code α} {V : Set (List α)}
    (C : Threading V (Fin K.1.length)) (g : Fin K.1.length) (r : ℕ) :
    Fin (Fintype.card (C.Aligned (C.text g))) → ℕ :=
  fun j => (C.word ((C.next ^ r) (C.enumerate (C.text g) j).val)).length

omit [Coded α] in
theorem count_rank {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C)
    (g : Fin K.1.length) (r l : ℕ) :
    ((aligned K g.val).filter (fun i => lessEq (atLength K r i) l)).length =
      (Finset.univ.filter (fun j => lengthValues C g r j ≤ l)).card := by
  classical
  have he := Fintype.card_congr (Equiv.subtypeEquiv (C.enumerate (C.text g))
    (p := fun j => lengthValues C g r j ≤ l)
    (q := fun j => (C.word ((C.next ^ r) j.val)).length ≤ l) (fun _ => Iff.rfl))
  have he' := Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun i : Fin K.1.length => C.text i = C.text g)
    (fun i => (C.word ((C.next ^ r) i)).length ≤ l))
  rw [Fintype.card_subtype] at he
  change Fintype.card {x : C.Aligned (C.text g) //
    (C.word ((C.next ^ r) x.val)).length ≤ l} = _ at he'
  rw [he,he',Fintype.card_subtype]
  rw [← List.countP_eq_length_filter, aligned, List.countP_filter, countP_range]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i _
  simp only [Bool.and_eq_true, lessEq, equal, decide_eq_true_eq, atLength_eq h,
    key_eq h, C.finiteKey_eq_iff, and_comm]

theorem rankLength_eq {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C)
    (g : Fin K.1.length) (j : Fin (Fintype.card (C.Aligned (C.text g)))) (r : ℕ) :
    rankLength K g.val j.val r = OrderStats.order (lengthValues C g r) j := by
  classical
  have hb : OrderStats.order (lengthValues C g r) j ≤ bitSize K := by
    obtain ⟨i, hi⟩ := OrderStats.order_mem (lengthValues C g r) j
    rw [← hi]
    change (C.word ((C.next ^ r) (C.enumerate (C.text g) i).val)).length ≤ _
    rw [← atLength_eq h]
    exact atLength_bound K r _
  have ht (l : ℕ) :
      less j.val ((aligned K g.val).filter (fun i => lessEq (atLength K r i) l)).length = true ↔
      OrderStats.order (lengthValues C g r) j ≤ l := by
    rw [count_rank h, less, decide_eq_true_eq, OrderStats.order_le_iff]
  have hs := first_spec (n := bitSize K+1)
    (P := fun l => less j.val ((aligned K g.val).filter (fun i => lessEq (atLength K r i) l)).length)
    ⟨OrderStats.order (lengthValues C g r) j, by omega, (ht _).mpr le_rfl⟩
  change rankLength K g.val j.val r < bitSize K+1 ∧ _ at hs
  exact le_antisymm (hs.2.2 _ (by omega) ((ht _).mpr le_rfl)) ((ht _).mp hs.2.1)

theorem sortedExit_eq_rank {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C)
    (g : Fin K.1.length) (j : Fin (Fintype.card (C.Aligned (C.text g)))) (r : ℕ) :
    C.sortedExit (C.text g) j (r : ℤ) = (r : ℤ) + rankLength K g.val j.val r := by
  rw [rankLength_eq h]
  have he : C.exits (C.text g) (r : ℤ) = fun i => (lengthValues C g r i : ℤ) + r := by
    funext i
    simp only [Threading.exits, lengthValues, zpow_natCast]
    omega
  change OrderStats.order (C.exits (C.text g) r) j = _
  rw [he, OrderStats.order_add, add_comm]
  congr 1
  have hh : OrderStats.order (fun i => (lengthValues C g r i : ℤ)) j =
      ((OrderStats.order (lengthValues C g r) j : ℕ) : ℤ) := by
    apply le_antisymm
    · rw [OrderStats.order_le_iff]
      convert (OrderStats.order_le_iff (lengthValues C g r) j _).mp le_rfl using 1
      simp only [Nat.cast_le]
    · obtain ⟨i,hi⟩ := OrderStats.order_mem (fun i => (lengthValues C g r i : ℤ)) j
      rw [← hi]
      norm_cast
      rw [OrderStats.order_le_iff]
      have hh := (OrderStats.order_le_iff (fun i => (lengthValues C g r i : ℤ)) j _).mp
        (le_of_eq hi.symm)
      simpa only [Nat.cast_le] using hh
  exact hh

end Superstring.ThreadArray

namespace Superstring.ThreadArray
open BitCode Hierarchical
variable {α : Type} [Coded α] [DecidableEq α] [Inhabited α]

def exit (K : Code α) (g j : ℕ) (x : ℤ) : ℤ :=
  x + rankLength K g j (x % (period K g : ℤ)).toNat

@[fun_prop] theorem poly_exit : Poly (fun q : Code α × ℕ × ℕ × ℤ =>
    exit q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  have hm : Poly (fun q : Code α × ℕ × ℕ × ℤ =>
      (q.2.2.2 % (period q.1 q.2.1 : ℤ)).toNat) :=
    BitCode.Poly.modIntNat.comp (f := fun q : Code α × ℕ × ℕ × ℤ =>
      (q.2.2.2,period q.1 q.2.1)) (by fun_prop)
  unfold exit
  fun_prop

theorem exit_eq {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (closed : SubstringClosed V)
    (g : Fin K.1.length) (j : Fin (Fintype.card (C.Aligned (C.text g)))) (x : ℤ) :
    exit K g.val j.val x = (C.layer closed (period_spec h g).1.periodic j).z x := by
  let p := period K g.val
  let r := (x % (p : ℤ)).toNat
  have hp : 0 < p := (period_spec h g).1.positive
  have hr : (r : ℤ) = x % (p : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg x (by omega))
  have hx : x = (r : ℤ) + (x / (p : ℤ)) * p := by
    rw [hr]; exact (Int.emod_add_ediv_mul x p).symm
  have he := (C.layer closed (period_spec h g).1.periodic j).shift_int (x / p) r
  change C.sortedExit (C.text g) j ((r : ℤ) + (x / p) * p) =
    C.sortedExit (C.text g) j r + (x / p) * p at he
  rw [← hx, sortedExit_eq_rank h] at he
  change x + (rankLength K g.val j.val r : ℤ) = C.sortedExit (C.text g) j x
  omega

end Superstring.ThreadArray


namespace Superstring.WindowCode
open Hierarchical WalkCode
variable {α : Type}

def down (A : ℤ → α) (a b c : ℤ) : Walk α :=
  delete (textWord A a c) (textWord A c b)

def up (A : ℤ → α) (a b d : ℤ) : Walk α :=
  append (textWord A a b) (textWord A b d)

def route (A : ℤ → α) (a b c d : ℤ) : Walk α :=
  if c ≤ b then join (down A a b c) (up A c b d)
  else join (join (down A a b b) (gap (textWord A b c))) (up A c c d)

 theorem down_realizes {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) {a b c : ℤ} (hac : a ≤ c) (hcb : c ≤ b)
    (hw : textWord A a b ∈ V) :
    ∃ P : Hierarchical.Path V (textWord A a b) (textWord A c b),
      Path.points P = down A a b c ∧ P.cost = 0 ∧
      ∀ x, a ≤ x → x ≤ c → P.Visits (textWord A x b) := by
  have heq := textWord_append A hac hcb
  let D := Hierarchical.Path.deletePrefix closed (textWord A a c) (textWord A c b) (heq.symm ▸ hw)
  refine ⟨D.copy heq rfl,?_,by simp [D],?_⟩
  · simp only [points_copy,D,points_delete,down]
  · intro x hax hxc
    simp only [Hierarchical.Path.visits_copy]
    have heq' := textWord_append A hax hxc
    have hh : ∀ (u : List α) (h : u ++ textWord A c b ∈ V),
        u = textWord A a c →
        (Hierarchical.Path.deletePrefix closed u (textWord A c b) h).Visits (textWord A x b) →
        D.Visits (textWord A x b) := by
      intro u h he hv; subst u; exact hv
    apply hh _ _ heq'
    rw [← textWord_append A hxc hcb]
    exact Hierarchical.Path.deletePrefix_visits closed (textWord A a x)
      (textWord A x c) (textWord A c b) (by rw [heq',heq]; exact hw)

 theorem up_realizes {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) {a b d : ℤ} (hab : a ≤ b) (hbd : b ≤ d)
    (hw : textWord A a d ∈ V) :
    ∃ P : Hierarchical.Path V (textWord A a b) (textWord A a d),
      Path.points P = up A a b d ∧ P.cost = (d-b).toNat ∧
      ∀ y, b ≤ y → y ≤ d → P.Visits (textWord A a y) := by
  have heq := textWord_append A hab hbd
  let U := Hierarchical.Path.appendSuffix closed (textWord A a b) (textWord A b d) (heq.symm ▸ hw)
  refine ⟨U.copy rfl heq,?_,by simp [U],?_⟩
  · simp only [points_copy,U,points_append,up]
  · intro y hby hyd
    simp only [Hierarchical.Path.visits_copy]
    have heq' := textWord_append A hby hyd
    have hv := Hierarchical.Path.appendSuffix_visits closed (textWord A a b) (textWord A b y)
      (textWord A y d) (show textWord A a b ++ (textWord A b y ++ textWord A y d) ∈ V by
        rw [heq',heq]; exact hw)
    have hh : ∀ (b' : List α) (h : textWord A a b ++ b' ∈ V),
        b' = textWord A b d →
        (Hierarchical.Path.appendSuffix closed (textWord A a b) b' h).Visits (textWord A a y) →
        U.Visits (textWord A a y) := by
      intro b' h e hv'; subst b'; exact hv'
    apply hh _ _ heq'
    simpa only [textWord_append A hab hby] using hv

 theorem route_realizes {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V)
    {a b c d : ℤ} (hab : a ≤ b) (hcd : c ≤ d) (hac : a ≤ c) (hbd : b ≤ d)
    (h₁ : textWord A a b ∈ V) (h₂ : textWord A c d ∈ V) :
    ∃ P : Hierarchical.Path V (textWord A a b) (textWord A c d),
      Path.points P = route A a b c d ∧ P.cost = (d-b).toNat ∧
      (∀ x, a ≤ x → x ≤ c → x ≤ b → P.Visits (textWord A x b)) ∧
      ∃ w, P.Visits w ∧ (w.length : ℤ) ≤ max 0 (b-c) := by
  by_cases hcb : c ≤ b
  · obtain ⟨D,hD,hDc,hDv⟩ := down_realizes closed A hac hcb h₁
    obtain ⟨U,hU,hUc,_⟩ := up_realizes closed A hcb hbd h₂
    refine ⟨D.trans U,?_,by simp [hDc,hUc],?_,textWord A c b,Or.inl (Hierarchical.Path.visits_end D),?_⟩
    · simp only [Path.points,hD,hU,route,ite_eq_left hcb]
    · exact fun x hax hxc _ => Or.inl (hDv x hax hxc)
    · simp only [length_textWord]; omega
  · have hbc : b ≤ c := by omega
    have h0 : ([] : List α) ∈ V := closed h₁ List.nil_infix
    obtain ⟨D,hD,hDc,hDv⟩ := down_realizes closed A hab le_rfl h₁
    obtain ⟨U,hU,hUc,_⟩ := up_realizes closed A (a := c) le_rfl hcd h₂
    let G := Hierarchical.Path.readGap h0 (textWord A b c) (by
      intro x hx
      obtain ⟨i,_,_,rfl⟩ := mem_textWord A hx
      exact letters i)
    let D' := D.copy rfl (textWord_self A b)
    let U' := U.copy (textWord_self A c) rfl
    refine ⟨(D'.trans G).trans U',?_,?_,?_,[],Or.inl (Or.inl (Hierarchical.Path.visits_end D')),by simp⟩
    · simp only [Path.points,D',U',points_copy,hD,hU,G,points_gap,route,ite_eq_right hcb]
    · simp only [Hierarchical.Path.cost_trans,D',U',Hierarchical.Path.cost_copy,hDc,hUc,
        G,Hierarchical.Path.cost_readGap,length_textWord]
      omega
    · intro x hax _ hxb
      exact Or.inl (Or.inl (by simpa [D'] using hDv x hax hxb))

end Superstring.WindowCode


namespace Superstring.BitCode.Poly
@[fun_prop] theorem leInt : Poly (fun q : ℤ × ℤ => decide (q.1 ≤ q.2)) := by
  have h : Poly (fun q : ℤ × ℤ => decide ((q.1-q.2).toNat = 0)) := by fun_prop
  convert h using 1
  funext q
  simp only [decide_eq_decide]
  omega
@[fun_prop] theorem ltInt : Poly (fun q : ℤ × ℤ => decide (q.1 < q.2)) := by
  have h : Poly (fun q : ℤ × ℤ => !(decide (q.2 ≤ q.1))) :=
    Poly.not.comp (leInt.comp (Poly.snd.pair Poly.fst))
  convert h using 1
  funext q
  by_cases hq : q.2 ≤ q.1
  · simp [hq,not_lt_of_ge hq]
  · simp [hq,lt_of_not_ge hq]
@[fun_prop] theorem maxInt : Poly (fun q : ℤ × ℤ => Max.max q.1 q.2) := by
  have h : Poly (fun q : ℤ × ℤ => if decide (q.1 ≤ q.2) then q.2 else q.1) := by fun_prop
  convert h using 1
  funext q
  by_cases hq : q.1 ≤ q.2
  · simp [hq]
  · simp [hq,max_eq_left (le_of_not_ge hq)]
@[fun_prop] theorem minInt : Poly (fun q : ℤ × ℤ => Min.min q.1 q.2) := by
  have h : Poly (fun q : ℤ × ℤ => if decide (q.1 ≤ q.2) then q.1 else q.2) := by fun_prop
  convert h using 1
  funext q
  by_cases hq : q.1 ≤ q.2
  · simp [hq]
  · simp [hq,min_eq_right (le_of_not_ge hq)]
end Superstring.BitCode.Poly

namespace Superstring.PeriodWord
open BitCode Hierarchical
variable {α : Type} [Inhabited α]

def text (U : List α) (x : ℤ) : α := U[(x % (U.length : ℤ)).toNat]?.getD default

def window (U : List α) (a b : ℤ) : List α :=
  (List.range (b-a).toNat).map (fun i : ℕ => text U (a + (i : ℤ)))

 theorem window_eq (U : List α) (a b : ℤ) : window U a b = textWord (text U) a b := by
  apply List.ext_getElem
  · simp only [window,textWord,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi hi'
    simp only [window,textWord,List.getElem_map,List.getElem_range,List.getElem_ofFn]

 theorem periodic (U : List α) : Function.Periodic (text U) (U.length : ℤ) := by
  intro x
  simp [text]

 theorem eq_of_prefix (U : List α) (A : ℤ → α) (hp : 0 < U.length)
    (per : Function.Periodic A (U.length : ℤ))
    (h : ∀ i, (hi : i < U.length) → U[i] = A i) : text U = A := by
  funext x
  have hr : 0 ≤ x % (U.length : ℤ) := Int.emod_nonneg x (by omega)
  have hb : x % (U.length : ℤ) < U.length := Int.emod_lt_of_pos x (by omega)
  have hn : (x % (U.length : ℤ)).toNat < U.length := by omega
  simp only [text,List.getElem?_eq_getElem hn,Option.getD_some,h]
  rw [Int.toNat_of_nonneg hr]
  exact periodic_emod A U.length per x

variable [Coded α]
@[fun_prop] theorem poly_text : Poly (fun q : List α × ℤ => text q.1 q.2) := by
  unfold text
  exact (BitCode.Poly.getD default).comp
    (BitCode.Poly.fst.pair (BitCode.Poly.modIntNat.comp
      (f := fun q : List α × ℤ => (q.2,q.1.length)) (by fun_prop)))

@[fun_prop] theorem poly_window : Poly (fun q : List α × ℤ × ℤ => window q.1 q.2.1 q.2.2) := by
  unfold window
  exact BitCode.Poly.mapFn
    (f := fun q : (List α × ℤ × ℤ) × ℕ => text q.1.1 (q.1.2.1+q.2))
    (by fun_prop) (show Poly (fun q : List α × ℤ × ℤ => List.range (q.2.2-q.2.1).toNat) from by fun_prop)

@[fun_prop] theorem poly_textWord : Poly (fun q : List α × ℤ × ℤ =>
    textWord (text q.1) q.2.1 q.2.2) := by
  simpa only [window_eq] using (poly_window (α := α))

end Superstring.PeriodWord

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.PeriodWord
open BitCode Hierarchical
variable {α : Type} [Coded α] [Inhabited α]
@[fun_prop] theorem poly_down : Poly (fun q : List α × ℤ × ℤ × ℤ =>
    WindowCode.down (text q.1) q.2.1 q.2.2.1 q.2.2.2) := by
  unfold WindowCode.down
  exact WalkCode.poly_delete.comp
    ((poly_textWord.comp (f := fun q : List α × ℤ × ℤ × ℤ => (q.1,q.2.1,q.2.2.2)) (by fun_prop)).pair
    (poly_textWord.comp (f := fun q : List α × ℤ × ℤ × ℤ => (q.1,q.2.2.2,q.2.2.1)) (by fun_prop)))
@[fun_prop] theorem poly_up : Poly (fun q : List α × ℤ × ℤ × ℤ =>
    WindowCode.up (text q.1) q.2.1 q.2.2.1 q.2.2.2) := by
  unfold WindowCode.up
  exact WalkCode.poly_append.comp
    ((poly_textWord.comp (f := fun q : List α × ℤ × ℤ × ℤ => (q.1,q.2.1,q.2.2.1)) (by fun_prop)).pair
    (poly_textWord.comp (f := fun q : List α × ℤ × ℤ × ℤ => (q.1,q.2.2.1,q.2.2.2)) (by fun_prop)))
@[fun_prop] theorem down_fn {β : Type} [Coded β] {U : β → List α} {a b c : β → ℤ}
    (hU : Poly U) (ha : Poly a) (hb : Poly b) (hc : Poly c) :
    Poly (fun q => WindowCode.down (text (U q)) (a q) (b q) (c q)) :=
  poly_down.comp (hU.pair (ha.pair (hb.pair hc)))
@[fun_prop] theorem up_fn {β : Type} [Coded β] {U : β → List α} {a b c : β → ℤ}
    (hU : Poly U) (ha : Poly a) (hb : Poly b) (hc : Poly c) :
    Poly (fun q => WindowCode.up (text (U q)) (a q) (b q) (c q)) :=
  poly_up.comp (hU.pair (ha.pair (hb.pair hc)))
@[fun_prop] theorem textWord_fn {β : Type} [Coded β] {U : β → List α} {a b : β → ℤ}
    (hU : Poly U) (ha : Poly a) (hb : Poly b) :
    Poly (fun q => textWord (text (U q)) (a q) (b q)) :=
  poly_textWord.comp (hU.pair (ha.pair hb))
@[fun_prop] theorem poly_route : Poly (fun q : List α × ℤ × ℤ × ℤ × ℤ =>
    WindowCode.route (text q.1) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  have h : Poly (fun q : List α × ℤ × ℤ × ℤ × ℤ =>
      if decide (q.2.2.2.1 ≤ q.2.2.1) then
        WalkCode.join (WindowCode.down (text q.1) q.2.1 q.2.2.1 q.2.2.2.1)
          (WindowCode.up (text q.1) q.2.2.2.1 q.2.2.1 q.2.2.2.2)
      else WalkCode.join (WalkCode.join
        (WindowCode.down (text q.1) q.2.1 q.2.2.1 q.2.2.1)
        (WalkCode.gap (textWord (text q.1) q.2.2.1 q.2.2.2.1)))
        (WindowCode.up (text q.1) q.2.2.2.1 q.2.2.2.1 q.2.2.2.2)) := by
    apply BitCode.Poly.ite
    · exact BitCode.Poly.leInt.comp (f := fun q : List α × ℤ × ℤ × ℤ × ℤ => (q.2.2.2.1,q.2.2.1)) (by fun_prop)
    · fun_prop
    · fun_prop
  simpa only [decide_eq_true_eq,WindowCode.route] using h
end Superstring.PeriodWord

namespace Superstring.GeoCode
open BitCode Hierarchical WalkCode
variable {α : Type}

def exit (Z : List ℕ) (x : ℤ) : ℤ :=
  x + ((Z[(x % (Z.length : ℤ)).toNat]?).getD 0 : ℕ)

def first (Z : List ℕ) (x : ℤ) : ℤ := exit Z (x-1)

@[fun_prop] theorem poly_exit : Poly (fun q : List ℕ × ℤ => exit q.1 q.2) := by
  unfold exit
  have h : Poly (fun q : List ℕ × ℤ => (q.1[(q.2 % (q.1.length : ℤ)).toNat]?).getD 0) :=
    (BitCode.Poly.getD 0).comp (BitCode.Poly.fst.pair (BitCode.Poly.modIntNat.comp
      (f := fun q : List ℕ × ℤ => (q.2,q.1.length)) (by fun_prop)))
  fun_prop
@[fun_prop] theorem poly_first : Poly (fun q : List ℕ × ℤ => first q.1 q.2) := by
  unfold first
  fun_prop

def passage (A : ℤ → α) (z : ℤ → ℤ) (x : ℤ) : Walk α :=
  join (WindowCode.up A x (z (x-1)) (z x)) (WindowCode.down A x (z x) (x+1))

def segment (A : ℤ → α) (z : ℤ → ℤ) (t : ℤ) (n : ℕ) : Walk α :=
  textWord A t (z (t-1)) ::
    (List.range n).flatMap (fun i : ℕ => (passage A z (t+(i : ℤ))).tail)

 theorem segment_zero (A : ℤ → α) (z : ℤ → ℤ) (t : ℤ) :
    segment A z t 0 = [textWord A t (z (t-1))] := rfl
 theorem segment_succ (A : ℤ → α) (z : ℤ → ℤ) (t : ℤ) (n : ℕ) :
    segment A z t (n+1) = join (segment A z t n) (passage A z (t+n)) := by
  simp only [segment,List.range_succ,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,join,List.cons_append]

 theorem passage_realizes {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : Layer V A p) (closed : SubstringClosed V) (x : ℤ) :
    ∃ P : Hierarchical.Path V (textWord A x (L.first x))
        (textWord A (x+1) (L.first (x+1))),
      Path.points P = passage A L.z x ∧
      P.cost = (L.first (x+1)-L.first x).toNat ∧
      ∀ e, L.first x ≤ e → e ≤ L.last x → P.Visits (textWord A x e) := by
  have heq : L.first (x+1) = L.last x := by simp [Layer.first,Layer.last]
  have hbound : x+1 ≤ L.last x := by simpa only [heq] using L.start_le_first (x+1)
  obtain ⟨U,hU,hUc,hUv⟩ := WindowCode.up_realizes closed A (L.start_le_first x)
    (L.first_le_last x) (L.last_actual x)
  obtain ⟨D,hD,hDc,_⟩ := WindowCode.down_realizes closed A (show x ≤ x+1 by omega)
    hbound (L.last_actual x)
  refine ⟨(U.trans D).copy rfl (by rw [heq]),?_,?_,?_⟩
  · rw [WalkCode.points_copy]
    change join (WalkCode.Path.points U) (WalkCode.Path.points D) = _
    rw [hU,hD]
    rfl
  · simp only [Hierarchical.Path.cost_copy,Hierarchical.Path.cost_trans,hUc,hDc,Nat.add_zero,heq]
  · intro e hfe hel
    simpa only [Hierarchical.Path.visits_copy,Hierarchical.Path.Visits] using
      (Or.inl (hUv e hfe hel) : U.Visits (textWord A x e) ∨ D.Visits (textWord A x e))

 theorem segment_realizes {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : Layer V A p) (closed : SubstringClosed V) (t : ℤ) (n : ℕ) :
    ∃ P : Hierarchical.Path V (textWord A t (L.first t))
        (textWord A (t+n) (L.first (t+n))),
      Path.points P = segment A L.z t n ∧
      P.cost = (L.first (t+n)-L.first t).toNat ∧
      ∀ x e, t ≤ x → x < t+n → L.first x ≤ e → e ≤ L.last x →
        P.Visits (textWord A x e) := by
  induction n with
  | zero =>
    refine ⟨(Hierarchical.Path.nil _ (L.first_actual t)).copy rfl (by simp),?_,by simp [Hierarchical.Path.cost],?_⟩
    · rw [WalkCode.points_copy]
      rfl
    · intro x e htx hxt; omega
  | succ n ih =>
    obtain ⟨P,hP,hPc,hPv⟩ := ih
    obtain ⟨Q,hQ,hQc,hQv⟩ := passage_realizes L closed (t+n)
    have hend : t+(n : ℤ)+1 = t+(n+1 : ℕ) := by omega
    refine ⟨(P.trans Q).copy rfl (by rw [hend]),?_,?_,?_⟩
    · simp only [points_copy,Path.points,hP,hQ,segment_succ]
    · simp only [Hierarchical.Path.cost_copy,Hierarchical.Path.cost_trans,hPc,hQc]
      have h₁ := L.first_mono (show t ≤ t+(n : ℤ) by omega)
      have h₂ := L.first_mono (show t+(n : ℤ) ≤ t+n+1 by omega)
      rw [hend] at *
      omega
    · intro x e htx hxt hfe hel
      simp only [Hierarchical.Path.visits_copy,Hierarchical.Path.Visits]
      by_cases h : x < t+n
      · exact Or.inl (hPv x e htx h hfe hel)
      · have hx : x = t+n := by omega
        subst x
        exact Or.inr (hQv e hfe hel)

variable [Coded α] [Inhabited α]
@[fun_prop] theorem poly_passage : Poly (fun q : List α × List ℕ × ℤ =>
    passage (PeriodWord.text q.1) (exit q.2.1) q.2.2) := by
  unfold passage
  fun_prop
@[fun_prop] theorem poly_segment : Poly (fun q : List α × List ℕ × ℤ × ℕ =>
    segment (PeriodWord.text q.1) (exit q.2.1) q.2.2.1 q.2.2.2) := by
  have h : Poly (fun q : List α × List ℕ × ℤ × ℕ =>
      (List.range q.2.2.2).flatMap (fun i : ℕ =>
        (passage (PeriodWord.text q.1) (exit q.2.1) (q.2.2.1+i)).tail)) := by
    exact BitCode.Poly.flatten.comp (BitCode.Poly.mapFn
      (f := fun q : (List α × List ℕ × ℤ × ℕ) × ℕ =>
        (passage (PeriodWord.text q.1.1) (exit q.1.2.1) (q.1.2.2.1+q.2)).tail)
      (BitCode.Poly.tail.comp (poly_passage.comp
        (f := fun q : (List α × List ℕ × ℤ × ℕ) × ℕ =>
          (q.1.1, q.1.2.1, q.1.2.2.1+(q.2 : ℤ))) (by fun_prop))) (by fun_prop))
  unfold segment
  fun_prop
end Superstring.GeoCode


namespace Superstring.GeoCode
open BitCode Hierarchical WalkCode
variable {α : Type}

def collective (A : ℤ → α) (hi : ℤ → ℤ) (p k : ℕ) (a b : ℤ) : Walk α :=
  let Y := max b (hi (a-1))
  join (WindowCode.up A a b Y) (WindowCode.route A a Y (a+(k*p : ℕ)) (b+(k*p : ℕ)))

def band (A : ℤ → α) (lo hi : ℤ → ℤ) (p k : ℕ) (t : ℤ) : Walk α :=
  let E := lo t
  let H := hi (t-1)
  if H ≤ E then [textWord A t E]
  else join (WindowCode.up A t E H) (WindowCode.route A t H (t+(k*p : ℕ)) (E+(k*p : ℕ)))

def shortSweep (A : ℤ → α) (hi : ℤ → ℤ) (p k : ℕ) (a b t : ℤ) : Walk α :=
  let K : ℕ := k*p
  let x := min t (a+K)
  let F := hi (x-1)
  join (join (WindowCode.down A a b x) (WindowCode.up A x b F))
    (WindowCode.route A x F (a+K) (b+K))

def individual (A : ℤ → α) (z : ℤ → ℤ) (p : ℕ) (a b : ℤ) : Walk α :=
  let e := max b (z (a+p-1))
  join (WindowCode.route A a b (a+p) e) (WindowCode.up A (a+p) e (b+p))
theorem collective_link_realizes {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (p k : ℕ)
    (per : ∀ x, A (x + p) = A x)
    {ι : Type} (L : ι → Layer V A p) (lo hi : ι)
    (hlo : ∀ i x, (L lo).z x ≤ (L i).z x)
    (hhi : ∀ i x, (L i).z x ≤ (L hi).z x)
    {a b : ℤ} (hab : a ≤ b) (hR : textWord A a b ∈ V)
    (h₁ : (L hi).first a ≤ b + (k * p : ℕ))
    (h₂ : (L hi).first a - (L lo).last a ≤ (k * p : ℕ))
    (h₃ : b ≤ (L lo).last a + (k * p : ℕ)) :
    ∃ P : Hierarchical.Path V (textWord A a b) (textWord A a b),
      WalkCode.Path.points P = collective A (L hi).z p k a b ∧
      P.cost = k * p ∧ ∀ i, (L i).TouchedBy P := by
  let K : ℕ := k * p
  let Y := max b ((L hi).first a)
  have hbY : b ≤ Y := le_max_left _ _
  have hHY : (L hi).first a ≤ Y := le_max_right _ _
  have hYK : Y ≤ b + K := by dsimp [Y, K]; omega
  have haY : a ≤ Y := le_trans hab hbY
  have hYV : textWord A a Y ∈ V := by
    by_cases h : b ≤ (L hi).first a
    · simpa only [Y, max_eq_right h] using (L hi).first_actual a
    · simpa only [Y, max_eq_left (le_of_not_ge h)] using hR
  have perK : ∀ x, A (x + K) = A x := periodic_mul A p per k
  have heqR := textWord_translate A (K : ℤ) perK a b
  have hRV : textWord A (a + K) (b + K) ∈ V := heqR.symm ▸ hR
  obtain ⟨U, hU, hUc, hUv⟩ := WindowCode.up_realizes closed A hab hbY hYV
  obtain ⟨Q, hQ, hQc, hQv, _⟩ := WindowCode.route_realizes closed A letters haY
    (show a + K ≤ b + K by omega) (show a ≤ a + K by omega) hYK hYV hRV
  refine ⟨(U.trans Q).copy rfl heqR, ?_, ?_, ?_⟩
  · rw [WalkCode.points_copy]
    change join (WalkCode.Path.points U) (WalkCode.Path.points Q) = _
    rw [hU,hQ]
    rfl
  · simp only [Path.cost_copy, Path.cost_trans, hUc, hQc]
    dsimp [K] at *
    omega
  · intro i
    have hf : (L i).first a ≤ Y := le_trans (hhi i (a - 1)) hHY
    have hz : Y ≤ (L i).last (a + K) := by
      have heq := (L i).shift_mul k a
      have hlo' := hlo i a
      dsimp [Layer.last, K] at *
      rw [heq]
      dsimp [Y]
      omega
    obtain ⟨x, hax, hxK, hfx, hxl⟩ := (L i).meets_height a Y K hf hz
    refine ⟨x, Y, hfx, hxl, ?_⟩
    simp only [Path.visits_copy, Path.Visits]
    exact Or.inr (hQv x hax hxK (le_trans ((L i).start_le_first x) hfx))

theorem join_band_realizes {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (p k : ℕ)
    (per : ∀ x, A (x + p) = A x)
    {ι : Type} (L : ι → Layer V A p) (lo hi : ι)
    (hlo : ∀ i x, (L lo).z x ≤ (L i).z x)
    (hhi : ∀ i x, (L i).z x ≤ (L hi).z x)
    (t : ℤ) (hband : (L hi).first t - (L lo).last t ≤ (k * p : ℕ)) :
    ∃ P : Hierarchical.Path V (textWord A t ((L lo).last t)) (textWord A t ((L lo).last t)),
      WalkCode.Path.points P = band A (L lo).z (L hi).z p k t ∧
      P.cost ≤ k * p ∧ ∀ i, (L i).TouchedBy P := by
  let E := (L lo).last t
  let H := (L hi).first t
  let K := k * p
  have hE : textWord A t E ∈ V := (L lo).last_actual t
  have hH : textWord A t H ∈ V := (L hi).first_actual t
  have htE : t ≤ E := le_trans ((L lo).start_le_first t) ((L lo).first_le_last t)
  have htH : t ≤ H := (L hi).start_le_first t
  by_cases hHE : H ≤ E
  · refine ⟨Path.nil _ hE, ?_, Nat.zero_le _, ?_⟩
    · change (L hi).z (t-1) ≤ (L lo).z t at hHE
      simp only [WalkCode.Path.points,band,ite_eq_left hHE]
      rfl
    · intro i
      refine ⟨t, E, le_trans (hhi i (t - 1)) hHE, hlo i t, rfl⟩
  · have hEH : E ≤ H := by omega
    have hHK : H ≤ E + K := by dsimp [H, E, K]; omega
    have perK : ∀ x, A (x + K) = A x := periodic_mul A p per k
    have heqE := textWord_translate A (K : ℤ) perK t E
    obtain ⟨U, hU, hUc, hUv⟩ := WindowCode.up_realizes closed A htE hEH hH
    obtain ⟨Q, hQ, hQc, _, _⟩ := WindowCode.route_realizes closed A letters htH
      (show t + K ≤ E + K by omega) (show t ≤ t + K by omega) hHK hH
      (heqE.symm ▸ hE)
    refine ⟨(U.trans Q).copy rfl heqE, ?_, ?_, ?_⟩
    · rw [WalkCode.points_copy]
      change join (WalkCode.Path.points U) (WalkCode.Path.points Q) = _
      rw [hU,hQ]
      change ¬(L hi).z (t-1) ≤ (L lo).z t at hHE
      simp only [band,ite_eq_right hHE]
      rfl
    · simp only [Path.cost_copy, Path.cost_trans, hUc, hQc]
      dsimp [K] at *
      omega
    · intro i
      let e := max E ((L i).first t)
      have hfe : (L i).first t ≤ e := le_max_right _ _
      have heE : E ≤ e := le_max_left _ _
      have hel : e ≤ (L i).last t := max_le (hlo i t) ((L i).first_le_last t)
      have heH : e ≤ H := max_le hEH (hhi i (t - 1))
      refine ⟨t, e, hfe, hel, ?_⟩
      simp only [Path.visits_copy, Path.Visits]
      exact Or.inl (hUv e heE heH)

theorem collective_short_sweep_realizes {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (p k q : ℕ)
    (hk : 1 ≤ k) (per : ∀ x, A (x + p) = A x)
    {ι : Type} (L : ι → Layer V A p) (hi : ι)
    (hhi : ∀ i x, (L i).z x ≤ (L hi).z x)
    (hlong : ∀ i, ¬ (L i).HasShort q)
    {a b t : ℤ} (hat : a ≤ t) (htb : t < b)
    (hR : textWord A a b ∈ V)
    (hH : (L hi).first t ≤ b + (k * p : ℕ))
    (hlen : b - a < p + q) (hagr : b - t < q) :
    ∃ P : Hierarchical.Path V (textWord A a b) (textWord A a b),
      WalkCode.Path.points P = shortSweep A (L hi).z p k a b t ∧
      P.cost = k * p ∧ (∀ i, (L i).TouchedBy P) ∧
      ∃ w, P.Visits w ∧ w.length ≤ q := by
  let K := k * p
  let x := min t (a + K)
  let F := (L hi).first x
  have hpK : (p : ℤ) ≤ K := by
    have := Nat.mul_le_mul_right p hk
    simp only [one_mul] at this
    exact_mod_cast this
  have hax : a ≤ x := le_min hat (by omega)
  have hxt : x ≤ t := min_le_left _ _
  have hxK : x ≤ a + K := min_le_right _ _
  have hxb : x ≤ b := by omega
  have hshort : b - x < q := by
    by_cases h : t ≤ a + K
    · dsimp [x]; rw [min_eq_left h]; exact hagr
    · have heq : x = a + K := min_eq_right (by omega)
      rw [heq]
      omega
  have hbfirst : ∀ i, b ≤ (L i).first x := by
    intro i
    have := (L i).first_long_of_not_short q (hlong i) x
    omega
  have hbF : b ≤ F := hbfirst hi
  have hFK : F ≤ b + K := le_trans ((L hi).first_mono hxt) hH
  have hFV : textWord A x F ∈ V := (L hi).first_actual x
  have heqR := textWord_translate A (K : ℤ) (periodic_mul A p per k) a b
  obtain ⟨D, hD, hDc, _⟩ := WindowCode.down_realizes closed A hax hxb hR
  obtain ⟨U, hU, hUc, hUv⟩ := WindowCode.up_realizes closed A hxb hbF hFV
  obtain ⟨Q, hQ, hQc, _, _⟩ := WindowCode.route_realizes closed A letters (le_trans hxb hbF)
    (show a + K ≤ b + K by omega) hxK hFK hFV (heqR.symm ▸ hR)
  refine ⟨((D.trans U).trans Q).copy rfl heqR, ?_, ?_, ?_, ?_⟩
  · rw [WalkCode.points_copy]
    change join (join (WalkCode.Path.points D) (WalkCode.Path.points U)) (WalkCode.Path.points Q) = _
    rw [hD,hU,hQ]
    rfl
  · simp only [Path.cost_copy, Path.cost_trans, hDc, hUc, hQc]
    dsimp [K] at *
    omega
  · intro i
    refine ⟨x, (L i).first x, le_rfl, (L i).first_le_last x, ?_⟩
    simp only [Path.visits_copy, Path.Visits]
    exact Or.inl (Or.inr (hUv _ (hbfirst i) (hhi i (x - 1))))
  · refine ⟨textWord A x b, ?_, ?_⟩
    · simp only [Path.visits_copy, Path.Visits]
      exact Or.inl (Or.inl (Path.visits_end D))
    · simp only [length_textWord]
      omega

theorem individual_link_realizes {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (p q : ℕ)
    (per : ∀ x, A (x + p) = A x) (L : Layer V A p)
    {a b : ℤ} (hab : a ≤ b) (hR : textWord A a b ∈ V)
    (hfirst : L.first a ≤ b) (hlast : b ≤ L.last a + p)
    (hlen : b - a < p + q) :
    ∃ P : Hierarchical.Path V (textWord A a b) (textWord A a b),
      WalkCode.Path.points P = individual A L.z p a b ∧
      P.cost = p ∧ L.TouchedBy P ∧ ∃ w, P.Visits w ∧ w.length ≤ q := by
  let e := max b (L.first (a + p))
  have hbe : b ≤ e := le_max_left _ _
  have hfe : L.first (a + p) ≤ e := le_max_right _ _
  have heL : e ≤ L.last (a + p) := by
    apply max_le
    · simpa only [Layer.last_shift] using hlast
    · exact L.first_le_last _
  have hebp : e ≤ b + p := by
    apply max_le
    · omega
    · rw [Layer.first_shift]
      omega
  have hapse : a + p ≤ e := le_trans (L.start_le_first _) hfe
  have heV : textWord A (a + p) e ∈ V := L.actual _ _ hfe heL
  have heq := textWord_translate A p per a b
  obtain ⟨Q, hQ, hQc, _, w, hQw, hwlen⟩ := WindowCode.route_realizes closed A letters hab hapse
    (by omega) hbe hR heV
  obtain ⟨U, hU, hUc, _⟩ := WindowCode.up_realizes closed A hapse hebp (heq.symm ▸ hR)
  refine ⟨(Q.trans U).copy rfl heq, ?_, ?_, ?_, w, ?_, ?_⟩
  · rw [WalkCode.points_copy]
    change join (WalkCode.Path.points Q) (WalkCode.Path.points U) = _
    rw [hQ,hU]
    rfl
  · simp only [Path.cost_copy, Path.cost_trans, hQc, hUc]
    omega
  · refine ⟨a + p, e, hfe, heL, ?_⟩
    simp only [Path.visits_copy, Path.Visits]
    exact Or.inl (Path.visits_end Q)
  · simpa only [Path.visits_copy, Path.Visits] using (Or.inl hQw : Q.Visits w ∨ U.Visits w)
  · omega

end Superstring.GeoCode


namespace Superstring.WalkCode
open BitCode
variable {α β : Type} [Coded α] [Coded β]
@[fun_prop] theorem join_fn {P Q : β → Walk α} (hP : Poly P) (hQ : Poly Q) :
    Poly (fun q => join (P q) (Q q)) := poly_join.comp (hP.pair hQ)
end Superstring.WalkCode
namespace Superstring.PeriodWord
open BitCode Hierarchical
variable {α β : Type} [Coded α] [Coded β] [Inhabited α]
@[fun_prop] theorem route_fn {U : β → List α} {a b c d : β → ℤ}
    (hU : Poly U) (ha : Poly a) (hb : Poly b) (hc : Poly c) (hd : Poly d) :
    Poly (fun q => WindowCode.route (text (U q)) (a q) (b q) (c q) (d q)) :=
  poly_route.comp (hU.pair (ha.pair (hb.pair (hc.pair hd))))
end Superstring.PeriodWord
namespace Superstring.BitCode.Poly
variable {β : Type} [Coded β]
@[fun_prop] theorem leInt_fn {a b : β → ℤ} (ha : Poly a) (hb : Poly b) :
    Poly (fun q => decide (a q ≤ b q)) := leInt.comp (ha.pair hb)
@[fun_prop] theorem maxInt_fn {a b : β → ℤ} (ha : Poly a) (hb : Poly b) :
    Poly (fun q => Max.max (a q) (b q)) := maxInt.comp (ha.pair hb)
@[fun_prop] theorem minInt_fn {a b : β → ℤ} (ha : Poly a) (hb : Poly b) :
    Poly (fun q => Min.min (a q) (b q)) := minInt.comp (ha.pair hb)
end Superstring.BitCode.Poly
namespace Superstring.GeoCode
open BitCode Hierarchical WalkCode
variable {α : Type} [Coded α] [Inhabited α]
@[fun_prop] theorem exit_fn {β : Type} [Coded β] {Z : β → List ℕ} {x : β → ℤ}
    (hZ : Poly Z) (hx : Poly x) : Poly (fun q => exit (Z q) (x q)) :=
  poly_exit.comp (hZ.pair hx)
@[fun_prop] theorem poly_collective : Poly (fun q : List α × List ℕ × ℕ × ℕ × ℤ × ℤ =>
    collective (PeriodWord.text q.1) (exit q.2.1) q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2) := by
  unfold collective
  dsimp only
  fun_prop
@[fun_prop] theorem poly_band : Poly (fun q : List α × List ℕ × List ℕ × ℕ × ℕ × ℤ =>
    band (PeriodWord.text q.1) (exit q.2.1) (exit q.2.2.1) q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2) := by
  unfold band
  dsimp only
  have h : Poly (fun q : List α × List ℕ × List ℕ × ℕ × ℕ × ℤ =>
      if decide (exit q.2.2.1 (q.2.2.2.2.2-1) ≤ exit q.2.1 q.2.2.2.2.2) then
        [textWord (PeriodWord.text q.1) q.2.2.2.2.2 (exit q.2.1 q.2.2.2.2.2)] else
        join (WindowCode.up (PeriodWord.text q.1) q.2.2.2.2.2 (exit q.2.1 q.2.2.2.2.2)
          (exit q.2.2.1 (q.2.2.2.2.2-1)))
        (WindowCode.route (PeriodWord.text q.1) q.2.2.2.2.2 (exit q.2.2.1 (q.2.2.2.2.2-1))
          (q.2.2.2.2.2+(q.2.2.2.2.1*q.2.2.2.1 : ℕ))
          (exit q.2.1 q.2.2.2.2.2+(q.2.2.2.2.1*q.2.2.2.1 : ℕ)))) := by
    apply BitCode.Poly.ite
    · fun_prop
    · fun_prop
    · fun_prop
  simpa only [decide_eq_true_eq] using h
@[fun_prop] theorem poly_shortSweep : Poly (fun q : List α × List ℕ × ℕ × ℕ × ℤ × ℤ × ℤ =>
    shortSweep (PeriodWord.text q.1) (exit q.2.1) q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2) := by
  unfold shortSweep
  dsimp only
  fun_prop
@[fun_prop] theorem poly_individual : Poly (fun q : List α × List ℕ × ℕ × ℤ × ℤ =>
    individual (PeriodWord.text q.1) (exit q.2.1) q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  unfold individual
  dsimp only
  fun_prop
end Superstring.GeoCode


namespace Superstring.WalkCode
open BitCode Hierarchical
variable {α : Type}

def root (w : List α) : Walk α := join (append [] w) (delete w [])
def rootAt (P : Walk α) (i : ℕ) : Walk α :=
  let w := P[i]?.getD []
  join (join (append [] w) (rotate P i)) (delete w [])

theorem root_spec {V : Set (List α)} (closed : SubstringClosed V) {w : List α} (hw : w ∈ V) :
    Runs V [] [] (root w) ∧ cost (root w) = w.length ∧ w ∈ root w := by
  have ha := append_spec closed [] w (by simpa using hw)
  have hd := delete_spec closed w [] (by simpa using hw)
  have hA : Runs V [] w (append [] w) := by simpa only [List.nil_append] using ⟨ha.1,ha.2.1,ha.2.2.1⟩
  have hD : Runs V w [] (delete w []) := by exact ⟨hd.1,by simpa only [List.append_nil] using hd.2.1,hd.2.2.1⟩
  refine ⟨runs_join hA hD,?_,?_⟩
  · rw [root,cost_join _ _ _ hA.2.2 hD.2.1,ha.2.2.2,hd.2.2.2,Nat.add_zero]
  · rw [root,mem_join hA.2.2 hD.2.1]
    exact Or.inr (List.mem_of_head? hD.2.1)

theorem rootAt_spec {V : Set (List α)} (closed : SubstringClosed V) {P : Walk α} {s : List α}
    (hP : Runs V s s P) {i : ℕ} (hi : i < P.length) :
    Runs V [] [] (rootAt P i) ∧ cost (rootAt P i) = cost P + P[i].length ∧
      ∀ w ∈ P, w ∈ rootAt P i := by
  have hw := hP.1.2.1 P[i] (List.getElem_mem hi)
  obtain ⟨hR,hcR,hvR⟩ := rotate_spec hP hi
  have ha := append_spec closed [] P[i] (by simpa using hw)
  have hd := delete_spec closed P[i] [] (by simpa using hw)
  have hA : Runs V [] P[i] (append [] P[i]) := by simpa only [List.nil_append] using ⟨ha.1,ha.2.1,ha.2.2.1⟩
  have hD : Runs V P[i] [] (delete P[i] []) := by exact ⟨hd.1,by simpa only [List.append_nil] using hd.2.1,hd.2.2.1⟩
  simp only [rootAt,List.getElem?_eq_getElem hi,Option.getD_some]
  have hAR := runs_join hA hR
  refine ⟨runs_join hAR hD,?_,?_⟩
  · rw [cost_join _ _ _ hAR.2.2 hD.2.1,cost_join _ _ _ hA.2.2 hR.2.1,ha.2.2.2,hd.2.2.2,hcR]
    omega
  · intro w hw
    rw [mem_join hAR.2.2 hD.2.1,mem_join hA.2.2 hR.2.1,hvR]
    exact Or.inl (Or.inr hw)

variable [Coded α]
@[fun_prop] theorem poly_root : Poly (root : List α → Walk α) := by unfold root; fun_prop
@[fun_prop] theorem poly_rootAt : Poly (fun q : Walk α × ℕ => rootAt q.1 q.2) := by
  have hw : Poly (fun q : Walk α × ℕ => q.1[q.2]?.getD []) := BitCode.Poly.getD []
  unfold rootAt
  dsimp only
  fun_prop
end Superstring.WalkCode


namespace Superstring.WalkCode
open BitCode Hierarchical
variable {α : Type} [Inhabited α] [DecidableEq α]

def edgeCheck (s t : List α) : Bool :=
  equal t (s ++ [t[s.length]?.getD default]) || equal s ((s[0]?.getD default)::t)

theorem edgeCheck_eq (s t : List α) : edgeCheck s t = true ↔ Edge s t := by
  simp only [edgeCheck,Bool.or_eq_true,BitCode.equal,decide_eq_true_eq,Edge]
  constructor
  · rintro (h|h)
    · exact Or.inl ⟨_,h⟩
    · exact Or.inr ⟨_,h⟩
  · rintro (⟨a,rfl⟩|⟨a,rfl⟩)
    · left
      simp
    · right
      simp

def check (vs P : Walk α) : Bool :=
  !(equal P []) && equal (P.filter (fun w => member w vs)) P &&
    equal ((P.zip P.tail).filter (fun q => edgeCheck q.1 q.2)) (P.zip P.tail)

omit [Inhabited α] [DecidableEq α] in
theorem chain_zip (P : Walk α) : P.IsChain Edge ↔ ∀ q ∈ P.zip P.tail, Edge q.1 q.2 := by
  induction P with
  | nil => simp
  | cons s P ih =>
    cases P with
    | nil => simp
    | cons t P =>
      simp only [List.tail_cons,List.zip_cons_cons,List.isChain_cons_cons,List.mem_cons]
      constructor
      · rintro ⟨hs,hP⟩ q (rfl|hq)
        · exact hs
        · exact ih.mp hP q hq
      · intro h
        exact ⟨h (s,t) (Or.inl rfl),ih.mpr (fun q hq => h q (Or.inr hq))⟩

theorem check_eq (vs P : Walk α) : check vs P = true ↔ Valid {w | w ∈ vs} P := by
  simp only [check,Bool.and_eq_true,Bool.not_eq_true',BitCode.equal,decide_eq_false_iff_not,
    decide_eq_true_eq,List.filter_eq_self,member,Valid,Set.mem_ofPred_eq]
  rw [chain_zip]
  constructor
  · rintro ⟨⟨hne,hv⟩,hc⟩
    exact ⟨hne,fun w hw => hv w hw,fun q hq => (edgeCheck_eq ..).mp (hc q hq)⟩
  · rintro ⟨hne,hv,hc⟩
    exact ⟨⟨hne,fun w hw => hv w hw⟩,fun q hq => (edgeCheck_eq ..).mpr (hc q hq)⟩

variable [Coded α]
@[fun_prop] theorem poly_edgeCheck : Poly (fun q : List α × List α => edgeCheck q.1 q.2) := by
  have h₁ : Poly (fun q : List α × List α => q.2[q.1.length]?.getD default) :=
    (BitCode.Poly.getD default).comp (f := fun q : List α × List α => (q.2,q.1.length)) (by fun_prop)
  have h₂ : Poly (fun q : List α × List α => q.1[0]?.getD default) :=
    (BitCode.Poly.getD default).comp (f := fun q : List α × List α => (q.1,0)) (by fun_prop)
  unfold edgeCheck
  fun_prop
@[fun_prop] theorem poly_check : Poly (fun q : Walk α × Walk α => check q.1 q.2) := by
  unfold check
  have hv : Poly (fun q : Walk α × Walk α => q.2.filter (fun w => member w q.1)) :=
    BitCode.Poly.filterFn (p := fun q : (Walk α × Walk α) × List α => member q.2 q.1.1)
      (by fun_prop) (by fun_prop)
  have he : Poly (fun q : Walk α × Walk α => (q.2.zip q.2.tail).filter (fun x => edgeCheck x.1 x.2)) :=
    BitCode.Poly.filterFn (p := fun q : (Walk α × Walk α) × (List α × List α) => edgeCheck q.2.1 q.2.2)
      (by fun_prop) (by fun_prop)
  fun_prop
end Superstring.WalkCode


namespace Superstring.GeoCode
open BitCode Hierarchical WalkCode
variable {α : Type} {V : Set (List α)} {A : ℤ → α} {p : ℕ}
theorem full_turn_realizes (L : Layer V A p) (closed : SubstringClosed V) (hp : 0 < p)
    (per : ∀ x, A (x + p) = A x) (t : ℤ) :
    ∃ P : Hierarchical.Path V (textWord A t (L.first t)) (textWord A t (L.first t)),
      WalkCode.Path.points P = segment A L.z t p ∧
      P.cost = p ∧ ∀ x e, L.first x ≤ e → e ≤ L.last x →
        P.Visits (textWord A x e) := by
  obtain ⟨Q, hQ, hcQ, hvQ⟩ := segment_realizes L closed t p
  have heq : textWord A (t + p) (L.first (t + p)) = textWord A t (L.first t) := by
    rw [L.first_shift]
    exact textWord_translate A p per t (L.first t)
  let P := Q.copy rfl heq
  have hP : WalkCode.Path.points P = segment A L.z t p := by
    rw [WalkCode.points_copy]
    exact hQ
  have hPc : P.cost = p := by
    simp only [P,Hierarchical.Path.cost_copy,hcQ,L.first_shift]
    omega
  have hPv : ∀ x e, t ≤ x → x < t+p → L.first x ≤ e → e ≤ L.last x →
      P.Visits (textWord A x e) := by
    intro x e htx hxp hfe hel
    exact (Hierarchical.Path.visits_copy ..).mpr (hvQ x e htx hxp hfe hel)
  refine ⟨P,hP, hPc, ?_⟩
  intro x e hfe hel
  let r := t + (x - t) % (p : ℤ)
  let m := (x - t) / (p : ℤ)
  have htr : t ≤ r := by
    have := Int.emod_nonneg (x - t) (show (p : ℤ) ≠ 0 by omega)
    dsimp [r]; omega
  have hrt : r < t + p := by
    have := Int.emod_lt_of_pos (x - t) (show (0 : ℤ) < p by omega)
    dsimp [r]; omega
  have hrx : r + m * p = x := by
    have := Int.emod_add_ediv_mul (x - t) (p : ℤ)
    dsimp [r, m]; omega
  have hf : L.first r ≤ e - m * p := by
    have hh := L.first_shift_int m r
    rw [hrx] at hh
    omega
  have hl : e - m * p ≤ L.last r := by
    have hh := L.shift_int m r
    rw [hrx] at hh
    change e ≤ L.z x at hel
    change e - m * p ≤ L.z r
    omega
  have hpA : Function.Periodic A (p : ℤ) := per
  have heq := textWord_translate A (m * p) (hpA.int_mul m) r (e - m * p)
  rw [hrx, sub_add_cancel] at heq
  rw [heq]
  exact hPv r (e - m * p) htr hrt hf hl


end Superstring.GeoCode

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.ThreadArray
open BitCode Hierarchical
variable {α : Type} [Coded α] [DecidableEq α] [Inhabited α]

def layerWord (K : Code α) (g : ℕ) : List α := (key K g).take (period K g)
def layerExits (K : Code α) (g j : ℕ) : List ℕ :=
  (List.range (period K g)).map (fun r => rankLength K g j r)

@[fun_prop] theorem poly_layerWord : Poly (fun q : Code α × ℕ => layerWord q.1 q.2) := by
  unfold layerWord; fun_prop
@[fun_prop] theorem poly_layerExits : Poly (fun q : Code α × ℕ × ℕ => layerExits q.1 q.2.1 q.2.2) := by
  unfold layerExits
  exact BitCode.Poly.mapFn
    (f := fun q : (Code α × ℕ × ℕ) × ℕ => rankLength q.1.1 q.1.2.1 q.1.2.2 q.2)
    (by fun_prop) (by fun_prop)

omit [Coded α] in
theorem length_layerWord {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (g : Fin K.1.length) :
    (layerWord K g.val).length = period K g.val := by
  have hp := (period_spec h g).2
  simp only [layerWord,List.length_take,key,List.length_map,List.length_range]
  omega

omit [Coded α] in
theorem text_layerWord {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (g : Fin K.1.length) :
    PeriodWord.text (layerWord K g.val) = C.text g := by
  apply PeriodWord.eq_of_prefix
  · rw [length_layerWord h g]; exact (period_spec h g).1.positive
  · rw [length_layerWord h g]; exact (period_spec h g).1.periodic
  · intro i hi
    have hir : i < 2 * K.1.length := by
      rw [length_layerWord h g] at hi; have := (period_spec h g).2; omega
    have he := C.finiteKey_get g (by simpa only [Fintype.card_fin] using hir)
    have he' := key_eq h g
    have hi' : i < (key K g.val).length := by simpa only [key,List.length_map,List.length_range] using hir
    have heq : (key K g.val)[i] = C.text g (i : ℤ) := by
      rw [← he'] at he
      exact Option.some.inj (by simpa only [List.getElem?_eq_getElem hi'] using he)
    simpa only [layerWord,List.getElem_take] using heq

theorem exit_layerExits (K : Code α) (g j : ℕ) (hp : 0 < period K g) (x : ℤ) :
    GeoCode.exit (layerExits K g j) x = exit K g j x := by
  unfold GeoCode.exit layerExits exit
  simp only [List.length_map,List.length_range]
  have hi : (x % (period K g : ℤ)).toNat < period K g := by
    have h₀ := Int.emod_nonneg x (show (period K g : ℤ) ≠ 0 by omega)
    have h₁ := Int.emod_lt_of_pos x (show (0 : ℤ) < period K g by omega)
    omega
  simp only [List.getElem?_map,List.getElem?_range hi,Option.map_some,Option.getD_some]

end Superstring.ThreadArray


namespace Superstring.LayerArray
open BitCode Hierarchical WalkCode
variable {α : Type} [Inhabited α]
abbrev GroupData (α : Type) := List α × List (List ℕ)
def turn (U : List α) (Z : List ℕ) : Walk α :=
  GeoCode.segment (PeriodWord.text U) (GeoCode.exit Z) 0 U.length
structure Represents {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (U : List α) (Z : List ℕ) (L : Layer V A p) : Prop where
  text_eq : PeriodWord.text U = A
  length_eq : U.length = p
  exit_eq : GeoCode.exit Z = L.z

theorem turn_spec {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    {U : List α} {Z : List ℕ} {L : Layer V A p} (h : Represents U Z L)
    (closed : SubstringClosed V) (hp : 0 < p) (per : Function.Periodic A (p : ℤ)) :
    Runs V (textWord A 0 (L.first 0)) (textWord A 0 (L.first 0)) (turn U Z) ∧
      cost (turn U Z) = p ∧ ∀ w ∈ L.Content, w ∈ turn U Z := by
  obtain ⟨P,hP,hc,hv⟩ := GeoCode.full_turn_realizes L closed hp per 0
  have he : turn U Z = WalkCode.Path.points P := by
    rw [turn,h.text_eq,h.length_eq,h.exit_eq,hP]
  rw [he]
  have hs := WalkCode.points_spec P
  refine ⟨⟨hs.1,hs.2.1,hs.2.2.1⟩,hs.2.2.2.1.trans hc,?_⟩
  rintro w ⟨x,e,hf,hl,rfl⟩
  exact (hs.2.2.2.2 _).mpr (hv x e hf hl)

variable [DecidableEq α]
def saturate (D : GroupData α) (js : List ℕ) (P : Walk α) : Walk α :=
  fill P (js.map (fun j => turn D.1 (D.2[j]?.getD [])))

theorem saturate_spec {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    {D : GroupData α} {js : List ℕ} {P : Walk α} {s t : List α}
    (L : ℕ → Layer V A p) (h : ∀ j ∈ js, Represents D.1 (D.2[j]?.getD []) (L j))
    (closed : SubstringClosed V) (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    (hP : Runs V s t P) (htouch : ∀ j ∈ js, ∃ w ∈ (L j).Content, w ∈ P) :
    Runs V s t (saturate D js P) ∧ cost (saturate D js P) = cost P + js.length*p ∧
      (∀ w ∈ P, w ∈ saturate D js P) ∧ ∀ j ∈ js, ∀ w ∈ (L j).Content, w ∈ saturate D js P := by
  have ht (j : ℕ) (hj : j ∈ js) := turn_spec (h j hj) closed hp per
  obtain ⟨hR,hc,hv⟩ := fill_spec P (js.map (fun j => turn D.1 (D.2[j]?.getD []))) hP
    (by rintro Q hQ; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hQ; exact ⟨_,(ht j hj).1⟩)
    (by rintro Q hQ; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hQ
        obtain ⟨w,hw,hwP⟩ := htouch j hj
        exact ⟨w,hwP,(ht j hj).2.2 w hw⟩)
  refine ⟨hR,?_,fun w hw => (hv w).mpr (Or.inl hw),?_⟩
  · rw [List.map_map] at hc
    have he : (js.map (fun j => cost (turn D.1 (D.2[j]?.getD [])))).sum = js.length*p := by
      rw [List.map_congr_left (g := fun _ => p) (fun j hj => (ht j hj).2.1)]
      simp only [List.map_const',List.sum_replicate,nsmul_eq_mul,Nat.cast_id]
    exact hc.trans (congrArg (cost P + ·) he)
  · intro j hj w hw
    exact (hv w).mpr (Or.inr ⟨_,List.mem_map.mpr ⟨j,hj,rfl⟩,(ht j hj).2.2 w hw⟩)

variable [Coded α]
omit [DecidableEq α] in
@[fun_prop] theorem poly_turn : Poly (fun q : List α × List ℕ => turn q.1 q.2) := by
  unfold turn
  exact GeoCode.poly_segment.comp (f := fun q : List α × List ℕ => (q.1,q.2,(0 : ℤ),q.1.length)) (by fun_prop)
omit [DecidableEq α] in
@[fun_prop] theorem poly_indexturn : Poly (fun q : GroupData α × ℕ => turn q.1.1 (q.1.2[q.2]?.getD [])) := by
  have hz : Poly (fun q : GroupData α × ℕ => q.1.2[q.2]?.getD []) :=
    (BitCode.Poly.getD ([] : List ℕ)).comp (f := fun q : GroupData α × ℕ => (q.1.2,q.2)) (by fun_prop)
  exact poly_turn.comp (f := fun q : GroupData α × ℕ => (q.1.1,q.1.2[q.2]?.getD []))
    ((show Poly (fun q : GroupData α × ℕ => q.1.1) from by fun_prop).pair hz)
@[fun_prop] theorem poly_saturate : Poly (fun q : GroupData α × List ℕ × Walk α =>
    saturate q.1 q.2.1 q.2.2) := by
  unfold saturate
  have ht : Poly (fun q : (GroupData α × List ℕ × Walk α) × ℕ =>
      turn q.1.1.1 (q.1.1.2[q.2]?.getD [])) :=
    poly_indexturn.comp (f := fun q : (GroupData α × List ℕ × Walk α) × ℕ => (q.1.1,q.2)) (by fun_prop)
  have hm : Poly (fun q : GroupData α × List ℕ × Walk α =>
      q.2.1.map (fun j => turn q.1.1 (q.1.2[j]?.getD []))) :=
    BitCode.Poly.mapFn ht (by fun_prop)
  exact WalkCode.poly_fill.comp ((show Poly (fun q : GroupData α × List ℕ × Walk α => q.2.2) from by fun_prop).pair hm)
end Superstring.LayerArray


namespace Superstring.LayerArray
open BitCode Hierarchical WalkCode
variable {α : Type} [Inhabited α]

def phaseContent (U : List α) (Z : List ℕ) (r : ℕ) : List (List α) :=
  let a := GeoCode.first Z r
  (List.range ((GeoCode.exit Z r-a).toNat+1)).map
    (fun i : ℕ => PeriodWord.window U r (a+i))
def content (U : List α) (Z : List ℕ) : List (List α) :=
  (List.range U.length).flatMap (phaseContent U Z)

theorem mem_phaseContent {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    {U : List α} {Z : List ℕ} {L : Layer V A p} (h : Represents U Z L)
    (r : ℕ) (w : List α) : w ∈ phaseContent U Z r ↔
      ∃ e, L.first r ≤ e ∧ e ≤ L.last r ∧ w = textWord A r e := by
  simp only [phaseContent,GeoCode.first,h.exit_eq,PeriodWord.window_eq,h.text_eq,
    List.mem_map,List.mem_range]
  constructor
  · rintro ⟨i,hi,rfl⟩
    refine ⟨L.first r+i,by omega,?_,rfl⟩
    have hh := L.first_le_last r
    change L.z ((r : ℤ)-1)+(i : ℤ) ≤ L.z r
    unfold Layer.first Layer.last at hh
    omega
  · rintro ⟨e,hf,hl,rfl⟩
    refine ⟨(e-L.first r).toNat,?_,?_⟩
    · unfold Layer.first Layer.last at *
      omega
    · congr 1
      change L.first r+((e-L.first r).toNat : ℤ) = e
      omega

theorem mem_content {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    {U : List α} {Z : List ℕ} {L : Layer V A p} (h : Represents U Z L)
    (hp : 0 < p) (per : Function.Periodic A (p : ℤ)) (w : List α) :
    w ∈ content U Z ↔ w ∈ L.Content := by
  simp only [content,List.mem_flatMap,List.mem_range,h.length_eq,mem_phaseContent h]
  constructor
  · rintro ⟨r,_,e,hf,hl,he⟩
    exact ⟨r,e,hf,hl,he⟩
  · rintro ⟨x,e,hf,hl,rfl⟩
    let r := x % (p : ℤ)
    let m := x / (p : ℤ)
    have hr0 : 0 ≤ r := Int.emod_nonneg x (by omega)
    have hrp : r < p := Int.emod_lt_of_pos x (by omega)
    have hrx : r+m*p = x := Int.emod_add_ediv_mul x p
    have hfr := L.first_shift_int m r
    have hlr := L.shift_int m r
    rw [hrx] at hfr hlr
    have hrn : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hr0
    refine ⟨r.toNat,by omega,e-m*p,?_,?_,?_⟩
    · rw [hrn]; omega
    · rw [hrn]
      change _ ≤ L.z r
      change e ≤ L.z x at hl
      omega
    · rw [hrn]
      have he := textWord_translate A (m*p) (per.int_mul m) r (e-m*p)
      rw [hrx,sub_add_cancel] at he
      exact he

variable [Coded α]
@[fun_prop] theorem poly_phaseContent : Poly (fun q : List α × List ℕ × ℕ =>
    phaseContent q.1 q.2.1 q.2.2) := by
  unfold phaseContent
  exact BitCode.Poly.mapFn
    (f := fun q : (List α × List ℕ × ℕ) × ℕ =>
      PeriodWord.window q.1.1 q.1.2.2 (GeoCode.first q.1.2.1 q.1.2.2+q.2))
    (by fun_prop) (by fun_prop)
@[fun_prop] theorem poly_content : Poly (fun q : List α × List ℕ => content q.1 q.2) := by
  unfold content
  exact BitCode.Poly.flatten.comp (BitCode.Poly.mapFn
    (f := fun q : (List α × List ℕ) × ℕ => phaseContent q.1.1 q.1.2 q.2)
    (by fun_prop) (by fun_prop))
end Superstring.LayerArray

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.LayerArray
open BitCode Hierarchical WalkCode
variable {α : Type} [Inhabited α] [DecidableEq α]

def exits (D : GroupData α) (j : ℕ) : List ℕ := D.2[j]?.getD []
def covered (D : GroupData α) (js : List ℕ) (P : Walk α) : Bool :=
  js.all (fun j => (content D.1 (exits D j)).all (fun w => member w P))
def collective (D : GroupData α) (js : List ℕ) (hi : ℕ) (a b : ℤ) : Walk α :=
  saturate D js (GeoCode.collective (PeriodWord.text D.1) (GeoCode.exit (exits D hi))
    D.1.length js.length a b)
def band (D : GroupData α) (js : List ℕ) (lo hi k : ℕ) (t : ℤ) : Walk α :=
  saturate D js (GeoCode.band (PeriodWord.text D.1) (GeoCode.exit (exits D lo))
    (GeoCode.exit (exits D hi)) D.1.length k t)
def shortSweep (D : GroupData α) (js : List ℕ) (hi : ℕ) (a b t : ℤ) : Walk α :=
  saturate D js (GeoCode.shortSweep (PeriodWord.text D.1) (GeoCode.exit (exits D hi))
    D.1.length js.length a b t)
def individual (D : GroupData α) (i : ℕ) (a b : ℤ) : Walk α :=
  saturate D [i] (GeoCode.individual (PeriodWord.text D.1) (GeoCode.exit (exits D i))
    D.1.length a b)

theorem covered_eq {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {js : List ℕ}
    (h : ∀ j ∈ js, Represents D.1 (exits D j) (L j))
    (hp : 0 < p) (per : Function.Periodic A (p : ℤ)) (P : Walk α) :
    covered D js P = true ↔ ∀ j ∈ js, ∀ w ∈ (L j).Content, w ∈ P := by
  simp only [covered,List.all_eq_true,member,decide_eq_true_eq]
  constructor
  · intro hc j hj w hw
    exact hc j hj w ((mem_content (h j hj) hp per w).mpr hw)
  · intro hc j hj w hw
    exact hc j hj w ((mem_content (h j hj) hp per w).mp hw)

theorem filled_realized {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {js : List ℕ}
    (h : ∀ j ∈ js, Represents D.1 (exits D j) (L j))
    (closed : SubstringClosed V) (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    {s : List α} {P : Hierarchical.Path V s s} {W : Walk α}
    (he : WalkCode.Path.points P = W) (ht : ∀ j ∈ js, (L j).TouchedBy P) :
    Runs V s s (saturate D js W) ∧
      cost (saturate D js W) = P.cost+js.length*p ∧
      (∀ w, P.Visits w → w ∈ saturate D js W) ∧
      ∀ j ∈ js, ∀ w ∈ (L j).Content, w ∈ saturate D js W := by
  have hs := WalkCode.points_spec P
  obtain ⟨hr,hc,hv,hw⟩ := saturate_spec L h closed hp per
    (s:=s) (t:=s) (P:=W) (by rw [← he]; exact ⟨hs.1,hs.2.1,hs.2.2.1⟩)
    (by intro j hj; obtain ⟨x,e,hf,hl,hv⟩ := ht j hj
        exact ⟨_,⟨x,e,hf,hl,rfl⟩,he ▸ (hs.2.2.2.2 _).mpr hv⟩)
  refine ⟨hr,?_,fun w hw => hv w (he ▸ (hs.2.2.2.2 w).mpr hw),hw⟩
  rw [← he,hs.2.2.2.1] at hc
  simpa only [he] using hc

theorem collective_spec {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {js : List ℕ} {lo hi : ℕ}
    (h : ∀ j ∈ js, Represents D.1 (exits D j) (L j))
    (hlo : lo ∈ js) (hhi : hi ∈ js)
    (lower : ∀ j ∈ js, ∀ x, (L lo).z x ≤ (L j).z x)
    (upper : ∀ j ∈ js, ∀ x, (L j).z x ≤ (L hi).z x)
    (closed : SubstringClosed V) (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    (letters : ∀ x, [A x] ∈ V) {a b : ℤ} (hab : a ≤ b)
    (hR : textWord A a b ∈ V)
    (hH : (L hi).first a ≤ b + (js.length*p : ℕ))
    (hgap : (L hi).first a-(L lo).last a ≤ (js.length*p : ℕ))
    (hB : b ≤ (L lo).last a + (js.length*p : ℕ)) :
    Runs V (textWord A a b) (textWord A a b) (collective D js hi a b) ∧
      cost (collective D js hi a b) = 2*(js.length*p) ∧
      (∀ j ∈ js, ∀ w ∈ (L j).Content, w ∈ collective D js hi a b) ∧
      textWord A a b ∈ collective D js hi a b := by
  obtain ⟨P,he,hc,ht⟩ := GeoCode.collective_link_realizes closed A letters p js.length per
    (fun j : {j // j ∈ js} => L j.val) ⟨lo,hlo⟩ ⟨hi,hhi⟩
    (fun j => lower j.val j.property) (fun j => upper j.val j.property) hab hR hH hgap hB
  have he' : WalkCode.Path.points P = GeoCode.collective (PeriodWord.text D.1)
      (GeoCode.exit (exits D hi)) D.1.length js.length a b := by
    rw [(h hi hhi).text_eq,(h hi hhi).exit_eq,(h hi hhi).length_eq]; exact he
  obtain ⟨hr,hc',hv,hw⟩ := filled_realized L h closed hp per he' (fun j hj => ht ⟨j,hj⟩)
  refine ⟨hr,?_,hw,hv _ (Hierarchical.Path.visits_start P)⟩
  change cost (saturate D js _) = _
  rw [hc',hc,two_mul]

theorem band_spec {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {js : List ℕ} {lo hi k : ℕ}
    (h : ∀ j ∈ js, Represents D.1 (exits D j) (L j))
    (hlo : lo ∈ js) (hhi : hi ∈ js)
    (lower : ∀ j ∈ js, ∀ x, (L lo).z x ≤ (L j).z x)
    (upper : ∀ j ∈ js, ∀ x, (L j).z x ≤ (L hi).z x)
    (closed : SubstringClosed V) (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    (letters : ∀ x, [A x] ∈ V) (t : ℤ)
    (hB : (L hi).first t-(L lo).last t ≤ (k*p : ℕ)) :
    Runs V (textWord A t ((L lo).last t)) (textWord A t ((L lo).last t)) (band D js lo hi k t) ∧
      cost (band D js lo hi k t) ≤ (k+js.length)*p ∧
      ∀ j ∈ js, ∀ w ∈ (L j).Content, w ∈ band D js lo hi k t := by
  obtain ⟨P,he,hc,ht⟩ := GeoCode.join_band_realizes closed A letters p k per
    (fun j : {j // j ∈ js} => L j.val) ⟨lo,hlo⟩ ⟨hi,hhi⟩
    (fun j => lower j.val j.property) (fun j => upper j.val j.property) t hB
  have he' : WalkCode.Path.points P = GeoCode.band (PeriodWord.text D.1)
      (GeoCode.exit (exits D lo)) (GeoCode.exit (exits D hi)) D.1.length k t := by
    rw [(h hi hhi).text_eq,(h hi hhi).exit_eq,(h lo hlo).exit_eq,(h hi hhi).length_eq]; exact he
  obtain ⟨hr,hc',_,hw⟩ := filled_realized L h closed hp per he' (fun j hj => ht ⟨j,hj⟩)
  refine ⟨hr,?_,hw⟩
  change cost (saturate D js _) ≤ _
  rw [hc',Nat.add_mul]
  omega

variable [Coded α]
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem poly_exits : Poly (fun q : GroupData α × ℕ => exits q.1 q.2) := by
  unfold exits
  exact (BitCode.Poly.getD ([] : List ℕ)).comp (f := fun q : GroupData α × ℕ => (q.1.2,q.2)) (by fun_prop)
@[fun_prop] theorem poly_covered : Poly (fun q : GroupData α × List ℕ × Walk α => covered q.1 q.2.1 q.2.2) := by
  unfold covered
  apply BitCode.Poly.allFn (p := fun q : (GroupData α × List ℕ × Walk α) × ℕ =>
    (content q.1.1.1 (exits q.1.1 q.2)).all (fun w => member w q.1.2.2))
  · exact BitCode.Poly.allFn (p := fun q : ((GroupData α × List ℕ × Walk α) × ℕ) × List α =>
      member q.2 q.1.1.2.2) (by fun_prop) (by fun_prop)
  · fun_prop
@[fun_prop] theorem saturate_fn {β : Type} [Coded β]
    {D : β → GroupData α} {js : β → List ℕ} {P : β → Walk α}
    (hD : Poly D) (hjs : Poly js) (hP : Poly P) :
    Poly (fun q => saturate (D q) (js q) (P q)) :=
  poly_saturate.comp (hD.pair (hjs.pair hP))
@[fun_prop] theorem poly_collective : Poly (fun q : GroupData α × List ℕ × ℕ × ℤ × ℤ =>
    collective q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  unfold collective
  apply saturate_fn (by fun_prop) (by fun_prop)
  exact GeoCode.poly_collective.comp
    (f := fun q : GroupData α × List ℕ × ℕ × ℤ × ℤ =>
      (q.1.1,exits q.1 q.2.2.1,q.1.1.length,q.2.1.length,q.2.2.2.1,q.2.2.2.2)) (by fun_prop)
@[fun_prop] theorem poly_band : Poly (fun q : GroupData α × List ℕ × ℕ × ℕ × ℕ × ℤ =>
    band q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2) := by
  unfold band
  apply saturate_fn (by fun_prop) (by fun_prop)
  exact GeoCode.poly_band.comp
    (f := fun q : GroupData α × List ℕ × ℕ × ℕ × ℕ × ℤ =>
      (q.1.1,exits q.1 q.2.2.1,exits q.1 q.2.2.2.1,q.1.1.length,q.2.2.2.2.1,q.2.2.2.2.2)) (by fun_prop)
@[fun_prop] theorem poly_shortSweep : Poly (fun q : GroupData α × List ℕ × ℕ × ℤ × ℤ × ℤ =>
    shortSweep q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2) := by
  unfold shortSweep
  apply saturate_fn (by fun_prop) (by fun_prop)
  exact GeoCode.poly_shortSweep.comp
    (f := fun q : GroupData α × List ℕ × ℕ × ℤ × ℤ × ℤ =>
      (q.1.1,exits q.1 q.2.2.1,q.1.1.length,q.2.1.length,q.2.2.2.1,q.2.2.2.2.1,q.2.2.2.2.2)) (by fun_prop)
@[fun_prop] theorem poly_individual : Poly (fun q : GroupData α × ℕ × ℤ × ℤ =>
    individual q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold individual
  apply saturate_fn (by fun_prop) (by fun_prop)
  exact GeoCode.poly_individual.comp
    (f := fun q : GroupData α × ℕ × ℤ × ℤ =>
      (q.1.1,exits q.1 q.2.1,q.1.1.length,q.2.2.1,q.2.2.2)) (by fun_prop)
end Superstring.LayerArray


namespace Superstring.LayerArray
open BitCode Hierarchical WalkCode
variable {α : Type} [Inhabited α] [DecidableEq α]

theorem individual_spec {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {i : ℕ}
    (h : Represents D.1 (exits D i) (L i))
    (closed : SubstringClosed V) (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    (letters : ∀ x, [A x] ∈ V) (q : ℕ) {a b : ℤ} (hab : a ≤ b)
    (hR : textWord A a b ∈ V) (hf : (L i).first a ≤ b) (hl : b ≤ (L i).last a+p)
    (hlen : b-a < p+q) :
    Runs V (textWord A a b) (textWord A a b) (individual D i a b) ∧
      cost (individual D i a b) = 2*p ∧
      (∀ w ∈ (L i).Content, w ∈ individual D i a b) ∧
      textWord A a b ∈ individual D i a b ∧
      ∃ w ∈ individual D i a b, w.length ≤ q := by
  obtain ⟨P,he,hc,ht,w,hw,hwlen⟩ := GeoCode.individual_link_realizes closed A letters p q per
    (L i) hab hR hf hl hlen
  have he' : WalkCode.Path.points P = GeoCode.individual (PeriodWord.text D.1)
      (GeoCode.exit (exits D i)) D.1.length a b := by
    rw [h.text_eq,h.exit_eq,h.length_eq]; exact he
  obtain ⟨hr,hc',hv,hcover⟩ := filled_realized L
    (D:=D) (js:=[i]) (by intro j hj; have := List.mem_singleton.mp hj; subst j; exact h)
    closed hp per he' (by intro j hj; simpa only [List.mem_singleton.mp hj] using ht)
  refine ⟨hr,?_,hcover i (by simp),hv _ (Hierarchical.Path.visits_start P),w,hv w hw,hwlen⟩
  change cost (saturate D [i] _) = _
  rw [hc',hc]
  simp only [List.length_singleton,one_mul,two_mul]

theorem shortSweep_spec {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {js : List ℕ} {hi : ℕ}
    (h : ∀ j ∈ js, Represents D.1 (exits D j) (L j)) (hhi : hi ∈ js)
    (upper : ∀ j ∈ js, ∀ x, (L j).z x ≤ (L hi).z x)
    (closed : SubstringClosed V) (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    (letters : ∀ x, [A x] ∈ V) (q : ℕ)
    (hlong : ∀ j ∈ js, ¬(L j).HasShort q) {a b t : ℤ} (hat : a ≤ t) (htb : t < b)
    (hR : textWord A a b ∈ V) (hH : (L hi).first t ≤ b+(js.length*p : ℕ))
    (hlen : b-a < p+q) (hagr : b-t < q) :
    Runs V (textWord A a b) (textWord A a b) (shortSweep D js hi a b t) ∧
      cost (shortSweep D js hi a b t) = 2*(js.length*p) ∧
      (∀ j ∈ js, ∀ w ∈ (L j).Content, w ∈ shortSweep D js hi a b t) ∧
      textWord A a b ∈ shortSweep D js hi a b t ∧
      ∃ w ∈ shortSweep D js hi a b t, w.length ≤ q := by
  have hk : 1 ≤ js.length := by have := List.length_pos_of_mem hhi; omega
  obtain ⟨P,he,hc,ht,w,hw,hwlen⟩ := GeoCode.collective_short_sweep_realizes closed A letters p js.length q hk per
    (fun j : {j // j ∈ js} => L j.val) ⟨hi,hhi⟩
    (fun j => upper j.val j.property) (fun j => hlong j.val j.property) hat htb hR hH hlen hagr
  have he' : WalkCode.Path.points P = GeoCode.shortSweep (PeriodWord.text D.1)
      (GeoCode.exit (exits D hi)) D.1.length js.length a b t := by
    rw [(h hi hhi).text_eq,(h hi hhi).exit_eq,(h hi hhi).length_eq]; exact he
  obtain ⟨hr,hc',hv,hcover⟩ := filled_realized L h closed hp per he' (fun j hj => ht ⟨j,hj⟩)
  refine ⟨hr,?_,hcover,hv _ (Hierarchical.Path.visits_start P),w,hv w hw,hwlen⟩
  change cost (saturate D js _) = _
  rw [hc',hc,two_mul]

theorem collective_contact [LinearOrder α] {V : Set (List α)} {A B : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {js : List ℕ} {lo hi : ℕ}
    (h : ∀ j ∈ js, Represents D.1 (exits D j) (L j)) (hlo : lo ∈ js) (hhi : hi ∈ js)
    (lower : ∀ j ∈ js, ∀ x, (L lo).z x ≤ (L j).z x)
    (upper : ∀ j ∈ js, ∀ x, (L j).z x ≤ (L hi).z x)
    (closed : SubstringClosed V) (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    (letters : ∀ x, [A x] ∈ V) (q : ℕ) (hq : 0 < q) (perB : Function.Periodic B (q : ℤ))
    {a b t : ℤ} (hat : a ≤ t) (htb : t < b)
    (hR : textWord A a b ∈ V) (hag : AgreeOn A B a b) (hne : A ≠ B)
    (hmax : ∀ x, forward A x ≤ forward A t) (hbelow : ∀ x, forward B x ≤ forward A t)
    (hH : (L hi).first t ≤ b+(js.length*p : ℕ))
    (hgap : (L hi).first a-(L lo).last a ≤ (js.length*p : ℕ))
    (hB : b ≤ (L lo).last a+(js.length*p : ℕ)) :
    ∃ P ∈ [collective D js hi a b,shortSweep D js hi a b t],
      Runs V (textWord A a b) (textWord A a b) P ∧ cost P = 2*(js.length*p) ∧
      (∀ j ∈ js, ∀ w ∈ (L j).Content, w ∈ P) ∧ textWord A a b ∈ P ∧
      ∃ w ∈ P, w.length ≤ q := by
  classical
  by_cases hs : ∃ j ∈ js, (L j).HasShort q
  · obtain ⟨hr,hc,hcover,hR'⟩ := collective_spec L h hlo hhi lower upper closed hp per letters
      (by omega) hR (le_trans ((L hi).first_mono hat) hH) hgap hB
    obtain ⟨j,hj,x,e,hf,hl,hshort⟩ := hs
    exact ⟨_,by simp,hr,hc,hcover,hR',_,hcover j hj _ ⟨x,e,hf,hl,rfl⟩,hshort⟩
  · have hlen := agreement_bound A B p q hp hq per perB hne a b hag
    have hagr : b-t < q := by
      obtain ⟨n,hn,hd⟩ := maximal_rotation A B p q hp hq per perB t hmax hbelow hne
      by_contra hh
      exact hd (hag (t+n) (by omega) (by omega))
    obtain ⟨hr,hc,hcover,hR',hw⟩ := shortSweep_spec L h hhi upper closed hp per letters q
      (by intro j hj hh; exact hs ⟨j,hj,hh⟩) hat htb hR hH hlen hagr
    exact ⟨_,by simp,hr,hc,hcover,hR',hw⟩
end Superstring.LayerArray


namespace Superstring.WalkCode
open BitCode Hierarchical
variable {α : Type}
theorem root_prefix {V : Set (List α)} (closed : SubstringClosed V) {w v : List α}
    (hw : w ∈ V) (hv : v <+: w) : v ∈ root w := by
  obtain ⟨u,rfl⟩ := hv
  have ha := append_spec closed [] (v++u) (by simpa using hw)
  have hd := delete_spec closed (v++u) [] (by simpa using hw)
  rw [root,mem_join ha.2.2.1 (by simpa only [List.nil_append,List.append_nil] using hd.2.1)]
  apply Or.inl
  simpa using mem_append ([] : List α) (v++u) v.length (by simp)
end Superstring.WalkCode

namespace Superstring.LayerArray
open BitCode Hierarchical WalkCode
variable {α : Type} [Inhabited α] [DecidableEq α]
def rootContent (D : GroupData α) (js : List ℕ) (w : List α) : Walk α :=
  saturate D js (WalkCode.root w)
def shortPool (D : GroupData α) (i : ℕ) : List (Walk α) :=
  (content D.1 (exits D i)).map (rootContent D [i])
def rootUpper (D : GroupData α) (js : List ℕ) (hi : ℕ) (t : ℤ) : Walk α :=
  rootContent D js (PeriodWord.window D.1 t (GeoCode.first (exits D hi) t))

theorem rootContent_spec {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {js : List ℕ} {w : List α}
    (h : ∀ j ∈ js, Represents D.1 (exits D j) (L j))
    (closed : SubstringClosed V) (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    (hw : w ∈ V) (htouch : ∀ j ∈ js, ∃ v ∈ (L j).Content, v <+: w) :
    Runs V [] [] (rootContent D js w) ∧ cost (rootContent D js w) = w.length+js.length*p ∧
      ∀ j ∈ js, ∀ v ∈ (L j).Content, v ∈ rootContent D js w := by
  have hr := WalkCode.root_spec closed hw
  obtain ⟨hR,hc,_,hv⟩ := saturate_spec L h closed hp per hr.1 (by
    intro j hj
    obtain ⟨v,hv,hpre⟩ := htouch j hj
    exact ⟨v,hv,WalkCode.root_prefix closed hw hpre⟩)
  exact ⟨hR,by simpa only [rootContent,hr.2.1] using hc,hv⟩

theorem shortPool_spec {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {i : ℕ}
    (h : Represents D.1 (exits D i) (L i))
    (closed : SubstringClosed V) (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    (hs : (L i).HasShort p) :
    ∃ P ∈ shortPool D i, Runs V [] [] P ∧ cost P ≤ 2*p ∧
      ∀ w ∈ (L i).Content, w ∈ P := by
  obtain ⟨x,e,hf,hl,hlen⟩ := hs
  let w := textWord A x e
  have hw : w ∈ (L i).Content := ⟨x,e,hf,hl,rfl⟩
  refine ⟨rootContent D [i] w,List.mem_map.mpr ⟨w,(mem_content h hp per w).mpr hw,rfl⟩,?_⟩
  obtain ⟨hr,hc,hv⟩ := rootContent_spec L (D:=D) (js:=[i])
    (by intro j hj; have := List.mem_singleton.mp hj; subst j; exact h)
    closed hp per ((L i).actual x e hf hl)
    (by intro j hj; have := List.mem_singleton.mp hj; subst j; exact ⟨w,hw,List.prefix_refl _⟩)
  exact ⟨hr,by simp only [List.length_singleton,one_mul] at hc; dsimp only [w]; omega,hv i (by simp)⟩

theorem rootUpper_spec {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {js : List ℕ} {hi : ℕ}
    (h : ∀ j ∈ js, Represents D.1 (exits D j) (L j)) (hh : Represents D.1 (exits D hi) (L hi))
    (upper : ∀ j ∈ js, ∀ x, (L j).z x ≤ (L hi).z x)
    (closed : SubstringClosed V) (hp : 0 < p) (per : Function.Periodic A (p : ℤ)) (t : ℤ)
    (hlen : (L hi).first t-t ≤ (js.length*p : ℕ)) :
    Runs V [] [] (rootUpper D js hi t) ∧ cost (rootUpper D js hi t) ≤ 2*(js.length*p) ∧
      ∀ j ∈ js, ∀ w ∈ (L j).Content, w ∈ rootUpper D js hi t := by
  have he : PeriodWord.window D.1 t (GeoCode.first (exits D hi) t) =
      textWord A t ((L hi).first t) := by
    simp only [PeriodWord.window_eq,hh.text_eq,GeoCode.first,hh.exit_eq,Layer.first]
  unfold rootUpper
  rw [he]
  obtain ⟨hr,hc,hv⟩ := rootContent_spec L h closed hp per ((L hi).first_actual t) (by
    intro j hj
    refine ⟨textWord A t ((L j).first t),⟨t,_,le_rfl,(L j).first_le_last t,rfl⟩,?_⟩
    exact ⟨textWord A ((L j).first t) ((L hi).first t),
      textWord_append A ((L j).start_le_first t) (upper j hj (t-1))⟩)
  refine ⟨hr,?_,hv⟩
  rw [hc,length_textWord]
  have ht := (L hi).start_le_first t
  omega

variable [Coded α]
@[fun_prop] theorem poly_rootContent : Poly (fun q : GroupData α × List ℕ × List α =>
    rootContent q.1 q.2.1 q.2.2) := by unfold rootContent; fun_prop
@[fun_prop] theorem poly_shortPool : Poly (fun q : GroupData α × ℕ => shortPool q.1 q.2) := by
  unfold shortPool
  exact BitCode.Poly.mapFn
    (f := fun q : (GroupData α × ℕ) × List α => rootContent q.1.1 [q.1.2] q.2)
    (by fun_prop) (by fun_prop)
@[fun_prop] theorem poly_rootUpper : Poly (fun q : GroupData α × List ℕ × ℕ × ℤ =>
    rootUpper q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold rootUpper
  exact poly_rootContent.comp
    (f := fun q : GroupData α × List ℕ × ℕ × ℤ =>
      (q.1,q.2.1,PeriodWord.window q.1.1 q.2.2.2 (GeoCode.first (exits q.1 q.2.2.1) q.2.2.2))) (by fun_prop)
end Superstring.LayerArray


namespace Superstring.WalkCode
open BitCode Hierarchical
variable {α : Type}
def rootShort (P : Walk α) (p : ℕ) : Walk α :=
  rootAt P (ThreadArray.first P.length (fun i => lessEq (P[i]?.getD []).length p))

theorem rootShort_spec {V : Set (List α)} (closed : SubstringClosed V) {P : Walk α} {s : List α}
    (hP : Runs V s s P) (p : ℕ) (hs : ∃ w ∈ P, w.length ≤ p) :
    Runs V [] [] (rootShort P p) ∧ cost (rootShort P p) ≤ cost P+p ∧
      ∀ w ∈ P, w ∈ rootShort P p := by
  obtain ⟨x,hx,hlen⟩ := hs
  obtain ⟨i,hi,hix⟩ := List.mem_iff_getElem.mp hx
  have he : lessEq (P[i]?.getD []).length p = true := by
    simpa only [List.getElem?_eq_getElem hi,Option.getD_some,hix,lessEq,decide_eq_true_eq] using hlen
  obtain ⟨hj,hp',_⟩ := ThreadArray.first_spec (P := fun i => lessEq (P[i]?.getD []).length p) ⟨i,hi,he⟩
  obtain ⟨hR,hc,hv⟩ := rootAt_spec closed hP hj
  have hl : P[ThreadArray.first P.length (fun i => lessEq (P[i]?.getD []).length p)].length ≤ p := by
    have hh := of_decide_eq_true hp'
    simpa only [List.getElem?_eq_getElem hj,Option.getD_some] using hh
  exact ⟨hR,hc.trans_le (Nat.add_le_add_left hl _),hv⟩

variable [Coded α]
@[fun_prop] theorem poly_rootShort : Poly (fun q : Walk α × ℕ => rootShort q.1 q.2) := by
  unfold rootShort ThreadArray.first
  apply poly_rootAt.comp (f := fun q : Walk α × ℕ =>
    (q.1,((List.range q.1.length).filter (fun i => lessEq (q.1[i]?.getD []).length q.2)).headD 0))
  apply Poly.pair (by fun_prop)
  apply (Poly.headD 0).comp (f := fun q : Walk α × ℕ =>
     (List.range q.1.length).filter (fun i => lessEq (q.1[i]?.getD []).length q.2))
  apply Poly.filterFn (p := fun q : (Walk α × ℕ) × ℕ => lessEq (q.1.1[q.2]?.getD []).length q.1.2)
  · have h := (Poly.getD ([] : List α)).comp
      (f := fun q : (Walk α × ℕ) × ℕ => (q.1.1,q.2)) (by fun_prop)
    fun_prop
  · fun_prop
end Superstring.WalkCode

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.BlockClose
open BitCode Hierarchical WalkCode
variable {α β : Type}
abbrev Block (α : Type) := ((ℕ × ℕ) × (List ℕ × List α)) × ((ℕ × ℕ) × (Walk α × List (Walk α)))
instance [DecidableEq α] : DecidableEq (Block α) := by
  letI : DecidableEq ((ℕ × ℕ) × (List ℕ × List α)) := inferInstance
  letI : DecidableEq ((ℕ × ℕ) × (Walk α × List (Walk α))) := inferInstance
  exact instDecidableEqProd
instance [Coded α] : Coded (Block α) := by
  letI : Coded ((ℕ × ℕ) × (List ℕ × List α)) := inferInstance
  letI : Coded ((ℕ × ℕ) × (Walk α × List (Walk α))) := inferInstance
  exact codedProd
namespace Block
abbrev source (b : Block α) := b.1.1.1
abbrev target (b : Block α) := b.1.1.2
abbrev members (b : Block α) := b.1.2.1
abbrev word (b : Block α) := b.1.2.2
abbrev period (b : Block α) := b.2.1.1
abbrev reserve (b : Block α) := b.2.1.2
abbrev internal (b : Block α) := b.2.2.1
abbrev links (b : Block α) := b.2.2.2
end Block
abbrev Action (α : Type) := List (Block α) × Walk α

def Covers (L : ℕ → List (List α)) (I : List ℕ) (P : Walk α) : Prop :=
  ∀ i ∈ I, ∀ w ∈ L i, w ∈ P

def Good (V : Set (List α)) (L : ℕ → List (List α)) (P : Walk α) (a : Action α) : Prop :=
  Runs V [] [] a.2 ∧ cost a.2 ≤ cost P+(a.1.map Block.reserve).sum ∧
    (∀ w ∈ P, w ∈ a.2) ∧ ∀ b ∈ a.1, Covers L b.members a.2

structure ValidBlock [LinearOrder β] (V : Set (List α)) (ids : List ℕ)
    (L : ℕ → List (List α)) (owner per : ℕ → ℕ) (rank : ℕ → β) (b : Block α) : Prop where
  period_eq : b.period = per b.source
  target_mem : b.target ∈ ids
  same : ∀ i ∈ b.members, owner i = b.source
  word_mem : b.word ∈ L b.target
  same_short : owner b.target = b.source → b.word.length ≤ b.period
  internal : ∃ s, Runs V s s b.internal ∧ cost b.internal+b.period ≤ b.reserve ∧ Covers L b.members b.internal
  link : ∃ Q ∈ b.links, ∃ s, Runs V s s Q ∧ cost Q ≤ b.reserve ∧ Covers L b.members Q ∧ b.word ∈ Q
  short : rank (owner b.target) ≤ rank b.source →
    ∃ Q ∈ b.links, ∃ s, Runs V s s Q ∧ cost Q ≤ b.reserve ∧ Covers L b.members Q ∧ b.word ∈ Q ∧
      ∃ w ∈ Q, w.length ≤ per (owner b.target)

variable [DecidableEq α]
def singles (P : Walk α) (b : Block α) : List (Action α) :=
  ([b],join P (rootShort b.internal b.period)) :: b.links.map (fun Q => ([b],splice P Q))
def doubles (P : Walk α) (b c : Block α) : List (Action α) :=
  b.links.map (fun Q => ([b,c],join P (rootShort (splice Q c.internal) c.period)))
def pool (P : Walk α) (B : List (Block α)) : List (Action α) :=
  B.flatMap (fun b => singles P b ++ (B.filter (fun c => !(equal c b))).flatMap (doubles P b))

omit [DecidableEq α] in
theorem covers_mono {L : ℕ → List (List α)} {I : List ℕ} {P Q : Walk α}
    (hc : Covers L I P) (h : ∀ w ∈ P, w ∈ Q) : Covers L I Q := fun i hi w hw => h w (hc i hi w hw)

theorem pool_single (P : Walk α) {B : List (Block α)} {b : Block α} (hb : b ∈ B) :
    ([b],join P (rootShort b.internal b.period)) ∈ pool P B := by
  exact List.mem_flatMap.mpr ⟨b,hb,List.mem_append_left _ (List.mem_cons_self ..)⟩
theorem pool_link (P : Walk α) {B : List (Block α)} {b : Block α} (hb : b ∈ B)
    {Q : Walk α} (hq : Q ∈ b.links) : ([b],splice P Q) ∈ pool P B := by
  exact List.mem_flatMap.mpr ⟨b,hb,List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨Q,hq,rfl⟩))⟩
theorem pool_double (P : Walk α) {B : List (Block α)} {b c : Block α} (hb : b ∈ B) (hc : c ∈ B)
    (hne : c ≠ b) {Q : Walk α} (hq : Q ∈ b.links) :
    ([b,c],join P (rootShort (splice Q c.internal) c.period)) ∈ pool P B := by
  apply List.mem_flatMap.mpr
  refine ⟨b,hb,List.mem_append_right _ (List.mem_flatMap.mpr ⟨c,?_,List.mem_map.mpr ⟨Q,hq,rfl⟩⟩)⟩
  simpa only [List.mem_filter,Bool.not_eq_true',equal,decide_eq_false_iff_not] using And.intro hc hne

theorem pool_sane (P : Walk α) (B : List (Block α)) {a : Action α} (ha : a ∈ pool P B) :
    a.1 ≠ [] ∧ a.1.Nodup ∧ ∀ b ∈ a.1, b ∈ B := by
  obtain ⟨b,hb,ha⟩ := List.mem_flatMap.mp ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨by simp,by simp,by intro c hc; simpa only [List.mem_singleton.mp hc] using hb⟩
    · obtain ⟨Q,_,rfl⟩ := List.mem_map.mp ha
      exact ⟨by simp,by simp,by intro c hc; simpa only [List.mem_singleton.mp hc] using hb⟩
  · obtain ⟨c,hc,ha⟩ := List.mem_flatMap.mp ha
    have hc' : c ∈ B ∧ c ≠ b := by
      simpa only [List.mem_filter,Bool.not_eq_true',equal,decide_eq_false_iff_not] using hc
    obtain ⟨Q,_,rfl⟩ := List.mem_map.mp ha
    exact ⟨by simp,by simp [Ne.symm hc'.2],by
      intro d hd; rcases List.mem_cons.mp hd with rfl|hd
      · exact hb
      · exact List.mem_singleton.mp hd ▸ hc'.1⟩

variable [LinearOrder β]
theorem pool_complete {V : Set (List α)} (closed : SubstringClosed V)
    (ids : List ℕ) (L : ℕ → List (List α)) (owner per : ℕ → ℕ) (rank : ℕ → β)
    (P : Walk α) (B : List (Block α)) (hP : Runs V [] [] P) (hne : B ≠ [])
    (valid : ∀ b ∈ B, ValidBlock V ids L owner per rank b)
    (ready : ∀ i ∈ ids, (∀ w ∈ L i, w ∈ P) ∨ ∃ b ∈ B, i ∈ b.members) :
    ∃ a ∈ pool P B, Good V L P a := by
  classical
  obtain ⟨b,hb,hmax⟩ := Finset.exists_max_image B.toFinset (fun b => rank b.source)
    (by obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil B hne; exact ⟨b,List.mem_toFinset.mpr hb⟩)
  have hb : b ∈ B := List.mem_toFinset.mp hb
  have vb := valid b hb
  rcases ready b.target vb.target_mem with hroot | ⟨c,hc,ht⟩
  · obtain ⟨Q,hq,s,hQ,hQc,hcov,hw⟩ := vb.link
    obtain ⟨hS,hSc,hSv⟩ := splice_spec hP hQ ⟨b.word,hroot _ vb.word_mem,hw⟩
    refine ⟨_,pool_link P hb hq,hS,?_,?_,?_⟩
    · simpa only [List.map_singleton,List.sum_singleton,hSc] using Nat.add_le_add_left hQc (cost P)
    · intro w hw; exact (hSv w).mpr (Or.inl hw)
    · intro d hd; have he := List.mem_singleton.mp hd; subst d
      exact covers_mono hcov (fun w hw => (hSv w).mpr (Or.inr hw))
  · by_cases hown : b.target ∈ b.members
    · obtain ⟨s,hI,hIc,hcover⟩ := vb.internal
      obtain ⟨hR,hRc,hRv⟩ := rootShort_spec closed hI b.period
        ⟨b.word,hcover _ hown _ vb.word_mem,vb.same_short (vb.same _ hown)⟩
      have hJ := runs_join hP hR
      have hJc := cost_join P _ _ hP.2.2 hR.2.1
      have hJv (w : List α) := mem_join (w:=w) hP.2.2 hR.2.1
      refine ⟨_,pool_single P hb,hJ,?_,?_,?_⟩
      · simp only [List.map_singleton,List.sum_singleton]; omega
      · intro w hw; exact (hJv w).mpr (Or.inl hw)
      · intro d hd; have he := List.mem_singleton.mp hd; subst d
        exact covers_mono hcover (fun w hw => (hJv w).mpr (Or.inr (hRv w hw)))
    · have hcb : c ≠ b := by intro he; subst c; exact hown ht
      have vc := valid c hc
      have ho := vc.same _ ht
      have hrank : rank (owner b.target) ≤ rank b.source := by
        rw [ho]; exact hmax c (List.mem_toFinset.mpr hc)
      obtain ⟨Q,hq,s,hQ,hQc,hcov,hw,x,hx,hxl⟩ := vb.short hrank
      obtain ⟨t,hI,hIc,hcover⟩ := vc.internal
      obtain ⟨hS,hSc,hSv⟩ := splice_spec hQ hI ⟨b.word,hw,hcover _ ht _ vb.word_mem⟩
      have hlen : x.length ≤ c.period := by simpa only [vc.period_eq,ho] using hxl
      obtain ⟨hR,hRc,hRv⟩ := rootShort_spec closed hS c.period
        ⟨x,(hSv x).mpr (Or.inl hx),hlen⟩
      have hJ := runs_join hP hR
      have hJc := cost_join P _ _ hP.2.2 hR.2.1
      have hJv (w : List α) := mem_join (w:=w) hP.2.2 hR.2.1
      refine ⟨_,pool_double P hb hc hcb hq,hJ,?_,?_,?_⟩
      · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]; omega
      · intro w hw; exact (hJv w).mpr (Or.inl hw)
      · intro d hd
        rcases List.mem_cons.mp hd with rfl|hd
        · exact covers_mono hcov (fun w hw => (hJv w).mpr (Or.inr (hRv w ((hSv w).mpr (Or.inl hw)))))
        · have he := List.mem_singleton.mp hd; subst d
          exact covers_mono hcover (fun w hw => (hJv w).mpr (Or.inr (hRv w ((hSv w).mpr (Or.inr hw)))))
end Superstring.BlockClose


namespace Superstring.BlockClose
open BitCode Hierarchical WalkCode
variable {α : Type} [DecidableEq α] [Inhabited α]

def rootedCheck (vs P : Walk α) : Bool :=
  check vs P && equal (P.take 1) [[]] && equal (P.reverse.take 1) [[]]

theorem rootedCheck_eq (vs P : Walk α) : rootedCheck vs P = true ↔ Runs {w | w ∈ vs} [] [] P := by
  have h (Q : Walk α) : Q.take 1 = [[]] ↔ Q.head? = some [] := by
    cases Q <;> simp
  simp only [rootedCheck,Bool.and_eq_true,check_eq,equal,decide_eq_true_eq,h,List.head?_reverse,Runs]
  tauto

def lookup (L : List (Walk α)) (i : ℕ) : Walk α := L[i]?.getD []
def coversCheck (L : List (Walk α)) (I : List ℕ) (P : Walk α) : Bool :=
  I.all (fun i => (lookup L i).all (fun w => member w P))
omit [Inhabited α] in
theorem coversCheck_eq (L : List (Walk α)) (I : List ℕ) (P : Walk α) :
    coversCheck L I P = true ↔ Covers (lookup L) I P := by
  simp only [coversCheck,List.all_eq_true,member,decide_eq_true_eq,Covers]

def goodCheck (vs : Walk α) (L : List (Walk α)) (P : Walk α) (a : Action α) : Bool :=
  rootedCheck vs a.2 && lessEq (cost a.2) (cost P+(a.1.map Block.reserve).sum) &&
    P.all (fun w => member w a.2) && a.1.all (fun b => coversCheck L b.members a.2)
theorem goodCheck_eq (vs : Walk α) (L : List (Walk α)) (P : Walk α) (a : Action α) :
    goodCheck vs L P a = true ↔ Good {w | w ∈ vs} (lookup L) P a := by
  simp only [goodCheck,Bool.and_eq_true,rootedCheck_eq,lessEq,decide_eq_true_eq,List.all_eq_true,
    member,coversCheck_eq,Good]
  tauto

def select (vs : Walk α) (L : List (Walk α)) (P : Walk α) (B : List (Block α)) : Action α :=
  ((pool P B).filter (goodCheck vs L P)).headD ([],P)
def remaining (B D : List (Block α)) : List (Block α) :=
  B.filter (fun b => !(member b D))

theorem select_spec (vs : Walk α) (L : List (Walk α)) (P : Walk α) (B : List (Block α))
    (hex : ∃ a ∈ pool P B, Good {w | w ∈ vs} (lookup L) P a) :
    select vs L P B ∈ pool P B ∧ Good {w | w ∈ vs} (lookup L) P (select vs L P B) := by
  have hn : (pool P B).filter (goodCheck vs L P) ≠ [] := by
    obtain ⟨a,ha,hg⟩ := hex
    have hm := List.mem_filter.mpr ⟨ha,(goodCheck_eq ..).mpr hg⟩
    intro he; rw [he] at hm; exact List.not_mem_nil hm
  have hm : select vs L P B ∈ (pool P B).filter (goodCheck vs L P) := by
    unfold select
    generalize (pool P B).filter (goodCheck vs L P) = X at hn ⊢
    cases X with
    | nil => exact False.elim (hn rfl)
    | cons a X => exact List.mem_cons_self ..
  have hs := List.mem_filter.mp hm
  exact ⟨hs.1,(goodCheck_eq ..).mp hs.2⟩

omit [Inhabited α] in
theorem mem_remaining (B D : List (Block α)) (b : Block α) :
    b ∈ remaining B D ↔ b ∈ B ∧ b ∉ D := by
  simp only [remaining,List.mem_filter,Bool.not_eq_true',member,decide_eq_false_iff_not]

omit [Inhabited α] in
theorem remaining_budget (B D : List (Block α)) (hd : D.Nodup) (hsub : D ⊆ B) :
    (D.map Block.reserve).sum+((remaining B D).map Block.reserve).sum ≤ (B.map Block.reserve).sum := by
  let E := B.filter (fun b => member b D)
  have hDE : D ⊆ E := fun b hb => List.mem_filter.mpr ⟨hsub hb,(member_eq ..).mpr hb⟩
  obtain ⟨F,hperm,hsub⟩ := hd.subperm hDE
  have hsum := (hsub.map Block.reserve).sum_le_sum (fun _ _ => Nat.zero_le _)
  rw [(hperm.map Block.reserve).sum_eq] at hsum
  have hp := ((List.filter_append_perm (fun b => member b D) B).map Block.reserve).sum_eq
  simp only [List.map_append,List.sum_append] at hp
  change (E.map Block.reserve).sum+((remaining B D).map Block.reserve).sum = _ at hp
  omega

omit [Inhabited α] in
theorem remaining_length (B D : List (Block α)) (hne : D ≠ []) (hsub : D ⊆ B) :
    (remaining B D).length < B.length := by
  have hh : (remaining B D).Sublist B := List.filter_sublist
  by_contra hn
  have he : remaining B D = B := hh.eq_of_length (by have := hh.length_le; omega)
  obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil D hne
  have hm : b ∈ remaining B D := by rw [he]; exact hsub hb
  exact ((mem_remaining B D b).mp hm).2 hb

abbrev State (α : Type) := Walk α × List (Block α)
def step (vs : Walk α) (L : List (Walk α)) (s : State α) : State α :=
  let a := select vs L s.1 s.2
  (a.2,remaining s.2 a.1)

variable {β : Type} [LinearOrder β]
theorem step_spec (vs : Walk α) (closed : SubstringClosed {w | w ∈ vs}) (L : List (Walk α))
    (ids : List ℕ) (owner per : ℕ → ℕ) (rank : ℕ → β) (s : State α)
    (hP : Runs {w | w ∈ vs} [] [] s.1) (hne : s.2 ≠ [])
    (valid : ∀ b ∈ s.2, ValidBlock {w | w ∈ vs} ids (lookup L) owner per rank b)
    (ready : ∀ i ∈ ids, (∀ w ∈ lookup L i, w ∈ s.1) ∨ ∃ b ∈ s.2, i ∈ b.members) :
    Runs {w | w ∈ vs} [] [] (step vs L s).1 ∧
      cost (step vs L s).1+((step vs L s).2.map Block.reserve).sum ≤ cost s.1+(s.2.map Block.reserve).sum ∧
      (∀ w ∈ s.1, w ∈ (step vs L s).1) ∧
      (step vs L s).2.Sublist s.2 ∧ (step vs L s).2.length < s.2.length ∧
      ∀ i ∈ ids, (∀ w ∈ lookup L i, w ∈ (step vs L s).1) ∨ ∃ b ∈ (step vs L s).2, i ∈ b.members := by
  obtain ⟨ha,hgood⟩ := select_spec vs L s.1 s.2
    (pool_complete closed ids (lookup L) owner per rank s.1 s.2 hP hne valid ready)
  obtain ⟨hn,hd,hsub⟩ := pool_sane s.1 s.2 ha
  obtain ⟨hQ,hQc,hQv,hQb⟩ := hgood
  have hbudget := remaining_budget s.2 (select vs L s.1 s.2).1 hd hsub
  refine ⟨hQ,by dsimp only [step]; omega,hQv,List.filter_sublist,remaining_length _ _ hn hsub,?_⟩
  intro i hi
  rcases ready i hi with h | ⟨b,hb,hm⟩
  · exact Or.inl (fun w hw => hQv w (h w hw))
  · by_cases hd : b ∈ (select vs L s.1 s.2).1
    · exact Or.inl (hQb b hd i hm)
    · exact Or.inr ⟨b,(mem_remaining _ _ _).mpr ⟨hb,hd⟩,hm⟩
end Superstring.BlockClose


namespace Superstring.BitCode.Poly
@[fun_prop] theorem flatMapFn {α β γ : Type} [Coded α] [Coded β] [Coded γ]
    {f : γ × α → List β} {xs : γ → List α} (hf : Poly f) (hxs : Poly xs) :
    Poly (fun c => (xs c).flatMap (fun a => f (c,a))) := by
  simpa only [List.flatMap, Function.comp_def] using flatten.comp (mapFn hf hxs)
end Superstring.BitCode.Poly
namespace Superstring.BlockClose
open BitCode WalkCode
variable {α : Type} [Coded α] [DecidableEq α] [Inhabited α]
instance codedState : Coded (State α) := codedProd
instance codedAction : Coded (Action α) := codedProd
instance codedContextState : Coded ((Walk α × List (Walk α)) × State α) := codedProd
instance codedContextAction : Coded ((Walk α × List (Walk α)) × (Walk α × Action α)) := codedProd
omit [Inhabited α] in
@[fun_prop] theorem poly_singles : Poly (fun q : Walk α × Block α => singles q.1 q.2) := by
  unfold singles
  have hm : Poly (fun q : Walk α × Block α => q.2.links.map (fun Q => ([q.2],splice q.1 Q))) := by
    apply BitCode.Poly.mapFn (f := fun q : (Walk α × Block α) × Walk α => ([q.1.2],splice q.1.1 q.2))
    · fun_prop
    · fun_prop
  fun_prop
omit [Inhabited α] in
@[fun_prop] theorem poly_doubles : Poly (fun q : Walk α × Block α × Block α => doubles q.1 q.2.1 q.2.2) := by
  unfold doubles
  apply BitCode.Poly.mapFn (f := fun q : (Walk α × Block α × Block α) × Walk α =>
    ([q.1.2.1,q.1.2.2],join q.1.1 (rootShort (splice q.2 q.1.2.2.internal) q.1.2.2.period)))
  · fun_prop
  · fun_prop
omit [Inhabited α] in
@[fun_prop] theorem poly_pool : Poly (fun q : Walk α × List (Block α) => pool q.1 q.2) := by
  unfold pool
  apply BitCode.Poly.flatMapFn (f := fun q : (Walk α × List (Block α)) × Block α =>
    singles q.1.1 q.2 ++ (q.1.2.filter (fun c => !(equal c q.2))).flatMap (doubles q.1.1 q.2))
  · apply BitCode.Poly.append.comp (f := fun q : (Walk α × List (Block α)) × Block α =>
      (singles q.1.1 q.2, (q.1.2.filter (fun c => !(equal c q.2))).flatMap (doubles q.1.1 q.2)))
    apply BitCode.Poly.pair (by fun_prop)
    apply BitCode.Poly.flatMapFn
      (f := fun q : ((Walk α × List (Block α)) × Block α) × Block α => doubles q.1.1.1 q.1.2 q.2)
    · fun_prop
    · exact BitCode.Poly.filterFn
        (p := fun q : ((Walk α × List (Block α)) × Block α) × Block α => !(equal q.2 q.1.2))
        (by fun_prop) (by fun_prop)
  · fun_prop
@[fun_prop] theorem poly_rootedCheck : Poly (fun q : Walk α × Walk α => rootedCheck q.1 q.2) := by
  unfold rootedCheck
  fun_prop
omit [DecidableEq α] [Inhabited α] in
@[fun_prop] theorem poly_lookup : Poly (fun q : List (Walk α) × ℕ => lookup q.1 q.2) := by
  exact BitCode.Poly.getD []
omit [Inhabited α] in
@[fun_prop] theorem poly_coversCheck : Poly (fun q : List (Walk α) × List ℕ × Walk α => coversCheck q.1 q.2.1 q.2.2) := by
  unfold coversCheck
  apply BitCode.Poly.allFn
    (p := fun q : (List (Walk α) × List ℕ × Walk α) × ℕ => (lookup q.1.1 q.2).all (fun w => member w q.1.2.2))
  · exact BitCode.Poly.allFn
      (p := fun q : ((List (Walk α) × List ℕ × Walk α) × ℕ) × List α => member q.2 q.1.1.2.2)
      (by fun_prop) (by fun_prop)
  · fun_prop
omit [DecidableEq α] [Inhabited α] in
@[fun_prop] theorem poly_reserves : Poly (fun B : List (Block α) => (B.map Block.reserve).sum) := by
  apply BitCode.Poly.sum.comp
  exact BitCode.Poly.mapFn (f := fun q : List (Block α) × Block α => q.2.reserve) (by fun_prop) (by fun_prop)
@[fun_prop] theorem poly_goodCheck : Poly (fun q : (Walk α × List (Walk α)) × (Walk α × Action α) =>
    goodCheck q.1.1 q.1.2 q.2.1 q.2.2) := by
  have hp : Poly (fun q : (Walk α × List (Walk α)) × (Walk α × Action α) => q.2.1.all (fun w => member w q.2.2.2)) := by
    exact BitCode.Poly.allFn
      (p := fun q : ((Walk α × List (Walk α)) × (Walk α × Action α)) × List α => member q.2 q.1.2.2.2)
      (by fun_prop) (by fun_prop)
  have hb : Poly (fun q : (Walk α × List (Walk α)) × (Walk α × Action α) =>
      q.2.2.1.all (fun b => coversCheck q.1.2 b.members q.2.2.2)) := by
    exact BitCode.Poly.allFn
      (p := fun q : ((Walk α × List (Walk α)) × (Walk α × Action α)) × Block α =>
        coversCheck q.1.1.2 q.2.members q.1.2.2.2) (by fun_prop) (by fun_prop)
  have hs : Poly (fun q : (Walk α × List (Walk α)) × (Walk α × Action α) =>
      (q.2.2.1.map Block.reserve).sum) := poly_reserves.comp (by fun_prop)
  have hc : Poly (fun q : (Walk α × List (Walk α)) × (Walk α × Action α) =>
      lessEq (cost q.2.2.2) (cost q.2.1+(q.2.2.1.map Block.reserve).sum)) := by fun_prop
  unfold goodCheck
  fun_prop
omit [DecidableEq α] [Inhabited α] in
theorem poly_shuffle : Poly (fun q : ((Walk α × List (Walk α)) × State α) × Action α =>
    (q.1.1,(q.1.2.1,q.2))) := by
  exact ((BitCode.Poly.fst.comp BitCode.Poly.fst).pair
    ((BitCode.Poly.fst.comp (BitCode.Poly.snd.comp BitCode.Poly.fst)).pair BitCode.Poly.snd))
theorem poly_goodCheck_context : Poly (fun q : ((Walk α × List (Walk α)) × State α) × Action α =>
    goodCheck q.1.1.1 q.1.1.2 q.1.2.1 q.2) := by
  exact BitCode.Poly.comp
    (f := fun q : ((Walk α × List (Walk α)) × State α) × Action α => (q.1.1,(q.1.2.1,q.2)))
    (g := fun q : (Walk α × List (Walk α)) × (Walk α × Action α) => goodCheck q.1.1 q.1.2 q.2.1 q.2.2)
    (poly_goodCheck (α := α)) (poly_shuffle (α := α))
theorem poly_filteredPool : Poly (fun q : (Walk α × List (Walk α)) × State α =>
    (pool q.2.1 q.2.2).filter (goodCheck q.1.1 q.1.2 q.2.1)) := by
  exact BitCode.Poly.filterFn poly_goodCheck_context (poly_pool.comp BitCode.Poly.snd)
@[fun_prop] theorem poly_select : Poly (fun q : (Walk α × List (Walk α)) × State α => select q.1.1 q.1.2 q.2.1 q.2.2) := by
  exact BitCode.Poly.headDWith.comp (poly_filteredPool.pair
    ((BitCode.Poly.const []).pair (BitCode.Poly.fst.comp BitCode.Poly.snd)))
omit [Inhabited α] in
@[fun_prop] theorem poly_remaining : Poly (fun q : List (Block α) × List (Block α) => remaining q.1 q.2) := by
  unfold remaining
  exact BitCode.Poly.filterFn
    (p := fun q : (List (Block α) × List (Block α)) × Block α => !(member q.2 q.1.2))
    (by fun_prop) (by fun_prop)
@[fun_prop] theorem poly_step : Poly (fun q : (Walk α × List (Walk α)) × State α => step q.1.1 q.1.2 q.2) := by
  unfold step
  dsimp only
  fun_prop
end Superstring.BlockClose


namespace Superstring.BlockFactory
open BitCode Hierarchical WalkCode LayerArray BlockClose
variable {α : Type} [Inhabited α] [DecidableEq α]

def pack (D : GroupData α) (src tar off : ℕ) (js : List ℕ) (a b : ℤ)
    (P : Walk α) (Qs : List (Walk α)) : BlockClose.Block α :=
  (((src,tar),(js.map (off+·),PeriodWord.window D.1 a b)),
    ((D.1.length,2*(js.length*D.1.length)),(P,Qs)))
def individual (D : GroupData α) (src tar off i : ℕ) (a b : ℤ) : BlockClose.Block α :=
  pack D src tar off [i] a b (turn D.1 (exits D i)) [LayerArray.individual D i a b]
def collective (D : GroupData α) (src tar off : ℕ) (js : List ℕ) (lo hi : ℕ) (a b t : ℤ) : BlockClose.Block α :=
  pack D src tar off js a b (band D js lo hi (js.length-1) t)
    [LayerArray.collective D js hi a b,shortSweep D js hi a b t]

omit [DecidableEq α] in
theorem pack_cover {V : Set (List α)} {A : ℤ → α} {p : ℕ} (L : ℕ → Layer V A p)
    {D : GroupData α} {src tar off : ℕ} {js : List ℕ} {a b : ℤ}
    {P Q : Walk α} {Qs : List (Walk α)} {ls : ℕ → Walk α}
    (he : ∀ j ∈ js, ∀ w ∈ ls (off+j), w ∈ (L j).Content)
    (hv : ∀ j ∈ js, ∀ w ∈ (L j).Content, w ∈ Q) :
    Covers ls (pack D src tar off js a b P Qs).members Q := by
  intro i hi w hw
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  exact hv j hj w (he j hj w hw)

variable [LinearOrder α]
theorem individual_valid {V : Set (List α)} {A B : ℤ → α} {p q : ℕ}
    (L : ℕ → Layer V A p) (T : Layer V B q) {D : GroupData α} {i src tar off : ℕ}
    (h : Represents D.1 (exits D i) (L i)) (closed : SubstringClosed V)
    (hp : 0 < p) (hq : 0 < q) (perA : Function.Periodic A (p : ℤ))
    (perB : Function.Periodic B (q : ℤ)) (letters : ∀ x, [A x] ∈ V)
    (R : T.Record A) (hne : A ≠ fun x => B (x+R.offset))
    (hf : (L i).first R.start ≤ R.stop) (hl : R.stop ≤ (L i).last R.start+p)
    (ids : List ℕ) (ls : ℕ → Walk α) (owner periods : ℕ → ℕ) (rank : ℕ → Lex (ℕ → α))
    (hsrc : periods src = p) (htar : tar ∈ ids) (hown : owner (off+i) = src)
    (htper : periods (owner tar) = q)
    (hself : owner tar = src → p = q)
    (hrec : textWord A R.start R.stop ∈ ls tar)
    (hlayers : ∀ w ∈ ls (off+i), w ∈ (L i).Content) :
    ValidBlock V ids ls owner periods rank (individual D src tar off i R.start R.stop) := by
  have hlen := R.length_lt hp hq perA perB hne
  obtain ⟨hI,hIc,hIv⟩ := turn_spec h closed hp perA
  obtain ⟨hQ,hQc,hQv,hR,w,hw,hs⟩ := LayerArray.individual_spec L h closed hp perA letters q
    R.start_le_stop R.word_mem hf hl hlen
  have hword : (individual D src tar off i R.start R.stop).word = textWord A R.start R.stop := by
    simp only [individual,pack,BlockClose.Block.word,PeriodWord.window_eq,h.text_eq]
  have hcov : ∀ P : Walk α, (∀ w ∈ (L i).Content, w ∈ P) →
      Covers ls (individual D src tar off i R.start R.stop).members P := by
    intro P hv j hj w hw
    have he : j = off+i := by simpa only [individual,pack,BlockClose.Block.members,List.map_singleton,List.mem_singleton] using hj
    subst j
    exact hv w (hlayers w hw)
  refine ⟨?_,htar,?_,by rw [hword]; exact hrec,?_,?_,?_,?_⟩
  · change D.1.length = periods src
    exact h.length_eq.trans hsrc.symm
  · intro j hj
    have he : j = off+i := by simpa only [individual,pack,BlockClose.Block.members,List.map_singleton,List.mem_singleton] using hj
    exact he ▸ hown
  · intro he
    have hlen' := R.same_period_length_lt hp perA (by rw [hself he]; exact perB) hne
    change (PeriodWord.window D.1 R.start R.stop).length ≤ D.1.length
    rw [PeriodWord.window_eq,h.text_eq,h.length_eq,length_textWord]
    have := R.start_le_stop; omega
  · refine ⟨_,hI,?_,hcov _ hIv⟩
    change cost (turn D.1 (exits D i))+D.1.length ≤ 2*([i].length*D.1.length)
    simp only [List.length_singleton,one_mul,h.length_eq,hIc]; omega
  · refine ⟨_,List.mem_singleton_self _,_,hQ,?_,hcov _ hQv,?_⟩
    · change cost (LayerArray.individual D i R.start R.stop) ≤ 2*([i].length*D.1.length)
      simp only [List.length_singleton,one_mul,h.length_eq,hQc]; exact le_rfl
    · rw [hword]; exact hR
  · intro _
    refine ⟨_,List.mem_singleton_self _,_,hQ,?_,hcov _ hQv,?_,w,hw,?_⟩
    · change cost (LayerArray.individual D i R.start R.stop) ≤ 2*([i].length*D.1.length)
      simp only [List.length_singleton,one_mul,h.length_eq,hQc]; exact le_rfl
    · rw [hword]; exact hR
    · change w.length ≤ periods (owner tar)
      rw [htper]; exact hs

theorem collective_valid {V : Set (List α)} {A B : ℤ → α} {p q : ℕ}
    (L : ℕ → Layer V A p) (T : Layer V B q) {D : GroupData α} {js : List ℕ} {lo hi src tar off : ℕ}
    (h : ∀ j ∈ js, Represents D.1 (exits D j) (L j)) (hlo : lo ∈ js) (hhi : hi ∈ js)
    (lower : ∀ j ∈ js, ∀ x, (L lo).z x ≤ (L j).z x)
    (upper : ∀ j ∈ js, ∀ x, (L j).z x ≤ (L hi).z x)
    (closed : SubstringClosed V) (hp : 0 < p) (hq : 0 < q)
    (perA : Function.Periodic A (p : ℤ)) (perB : Function.Periodic B (q : ℤ))
    (letters : ∀ x, [A x] ∈ V) (R : T.Record A) (hne : A ≠ fun x => B (x+R.offset))
    (t : ℤ) (hat : R.start ≤ t) (htb : t < R.stop)
    (hmax : ∀ x, forward A x ≤ forward A t)
    (hH : (L hi).first t ≤ R.stop+(js.length*p : ℕ))
    (hgap : (L hi).first R.start-(L lo).last R.start ≤ (js.length*p : ℕ))
    (hB : R.stop ≤ (L lo).last R.start+(js.length*p : ℕ))
    (hsharp : (L hi).first t-(L lo).last t ≤ ((js.length-1)*p : ℕ))
    (ids : List ℕ) (ls : ℕ → Walk α) (owner periods : ℕ → ℕ) (rank : ℕ → Lex (ℕ → α))
    (hsrc : periods src = p) (htar : tar ∈ ids) (hown : ∀ j ∈ js, owner (off+j) = src)
    (htper : periods (owner tar) = q) (hself : owner tar = src → p = q)
    (hrank : rank (owner tar) ≤ rank src → ∀ x, forward (fun x => B (x+R.offset)) x ≤ forward A t)
    (hrec : textWord A R.start R.stop ∈ ls tar)
    (hlayers : ∀ j ∈ js, ∀ w ∈ ls (off+j), w ∈ (L j).Content) :
    ValidBlock V ids ls owner periods rank (collective D src tar off js lo hi R.start R.stop t) := by
  have hD := h hi hhi
  have hk : 1 ≤ js.length := by have := List.length_pos_of_mem hhi; omega
  obtain ⟨hI,hIc,hIv⟩ := band_spec L h hlo hhi lower upper closed hp perA letters t hsharp
  obtain ⟨hQ,hQc,hQv,hR⟩ := collective_spec L h hlo hhi lower upper closed hp perA letters
    R.start_le_stop R.word_mem ((L hi).first_mono hat |>.trans hH) hgap hB
  have hword : (collective D src tar off js lo hi R.start R.stop t).word = textWord A R.start R.stop := by
    simp only [collective,pack,BlockClose.Block.word,PeriodWord.window_eq,hD.text_eq]
  have hcov : ∀ P : Walk α, (∀ j ∈ js, ∀ w ∈ (L j).Content, w ∈ P) →
      Covers ls (collective D src tar off js lo hi R.start R.stop t).members P := by
    intro P hv i hi w hw
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    exact hv j hj w (hlayers j hj w hw)
  have hreserve : (collective D src tar off js lo hi R.start R.stop t).reserve = 2*(js.length*p) := by
    change 2*(js.length*D.1.length) = _
    rw [hD.length_eq]
  refine ⟨?_,htar,?_,by rw [hword]; exact hrec,?_,?_,?_,?_⟩
  · change D.1.length = periods src
    exact hD.length_eq.trans hsrc.symm
  · intro i hi
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    exact hown j hj
  · intro he
    have hlen := R.same_period_length_lt hp perA (by rw [hself he]; exact perB) hne
    change (PeriodWord.window D.1 R.start R.stop).length ≤ D.1.length
    rw [PeriodWord.window_eq,hD.text_eq,hD.length_eq,length_textWord]
    have := R.start_le_stop; omega
  · refine ⟨_,hI,?_,hcov _ hIv⟩
    rw [hreserve]
    change cost (band D js lo hi (js.length-1) t)+D.1.length ≤ _
    rw [hD.length_eq]
    have he : (js.length-1+js.length)*p+p = 2*(js.length*p) := by
      have : js.length-1+1 = js.length := by omega
      calc (js.length-1+js.length)*p+p = (js.length-1+1+js.length)*p := by ring
           _ = 2*(js.length*p) := by rw [this]; ring
    omega
  · refine ⟨_,List.mem_cons_self ..,_,hQ,?_,hcov _ hQv,?_⟩
    · rw [hreserve]; exact hQc.le
    · rw [hword]; exact hR
  · intro hr
    have perB' : Function.Periodic (fun x => B (x+R.offset)) (q : ℤ) := by
      intro x
      simpa only [add_right_comm] using perB (x+R.offset)
    obtain ⟨P,hmem,hP,hPc,hPv,hPr,w,hw,hwlen⟩ := collective_contact L h hlo hhi lower upper
      closed hp perA letters q hq perB' hat htb R.word_mem R.agree hne hmax (hrank hr) hH hgap hB
    refine ⟨P,hmem,_,hP,?_,hcov _ hPv,?_,w,hw,?_⟩
    · rw [hreserve]; exact hPc.le
    · rw [hword]; exact hPr
    · change w.length ≤ periods (owner tar)
      rw [htper]; exact hwlen

end Superstring.BlockFactory

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.BlockFactory
open BitCode Hierarchical WalkCode LayerArray BlockClose
variable {α : Type} [Coded α] [Inhabited α] [DecidableEq α]
abbrev PackInput (α : Type) := (GroupData α × ℕ × ℕ × ℕ) × (List ℕ × ℤ × ℤ) × (Walk α × List (Walk α))
instance codedPackInput : Coded (PackInput α) := codedProd
omit [DecidableEq α] in
@[fun_prop] theorem poly_pack : Poly (fun q : PackInput α =>
    pack q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2 q.2.2.1 q.2.2.2) := by
  unfold pack
  have hm : Poly (fun q : PackInput α => q.2.1.1.map (q.1.2.2.2+·)) :=
    BitCode.Poly.mapFn (f := fun q : PackInput α × ℕ => q.1.1.2.2.2+q.2) (by fun_prop) (by fun_prop)
  fun_prop
abbrev IndividualInput (α : Type) := (GroupData α × ℕ × ℕ × ℕ) × (ℕ × ℤ × ℤ)
instance codedIndividualInput : Coded (IndividualInput α) := codedProd
@[fun_prop] theorem poly_individual : Poly (fun q : IndividualInput α =>
    individual q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold individual
  exact poly_pack.comp
    (f := fun q : IndividualInput α => (q.1,([q.2.1],q.2.2),
      (turn q.1.1.1 (exits q.1.1 q.2.1),[LayerArray.individual q.1.1 q.2.1 q.2.2.1 q.2.2.2]))) (by fun_prop)
abbrev CollectiveInput (α : Type) := (GroupData α × ℕ × ℕ × ℕ) × (List ℕ × ℕ × ℕ) × (ℤ × ℤ × ℤ)
instance codedCollectiveInput : Coded (CollectiveInput α) := codedProd
@[fun_prop] theorem poly_collective : Poly (fun q : CollectiveInput α =>
    collective q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  unfold collective
  exact poly_pack.comp
    (f := fun q : CollectiveInput α => (q.1,(q.2.1.1,q.2.2.1,q.2.2.2.1),
      (band q.1.1 q.2.1.1 q.2.1.2.1 q.2.1.2.2 (q.2.1.1.length-1) q.2.2.2.2,
       [LayerArray.collective q.1.1 q.2.1.1 q.2.1.2.2 q.2.2.1 q.2.2.2.1,
        shortSweep q.1.1 q.2.1.1 q.2.1.2.2 q.2.2.1 q.2.2.2.1 q.2.2.2.2]))) (by fun_prop)
end Superstring.BlockFactory


namespace Superstring.LayerArray
open BitCode Hierarchical WalkCode
variable {α : Type} [Inhabited α] [DecidableEq α]
def shortWords (D : GroupData α) (i : ℕ) : List (List α) :=
  (content D.1 (exits D i)).filter (fun w => lessEq w.length D.1.length)
def hasShort (D : GroupData α) (i : ℕ) : Bool := !(shortWords D i).isEmpty
def shortLoop (D : GroupData α) (i : ℕ) : Walk α :=
  rootContent D [i] ((shortWords D i).headD [])

omit [DecidableEq α] in
theorem hasShort_eq {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    {D : GroupData α} {i : ℕ} {L : Layer V A p}
    (h : Represents D.1 (exits D i) L) (hp : 0 < p) (per : Function.Periodic A (p : ℤ)) :
    hasShort D i = true ↔ L.HasShort p := by
  simp only [hasShort,Bool.not_eq_true',List.isEmpty_eq_false_iff]
  constructor
  · intro hn
    obtain ⟨w,hw⟩ := List.exists_mem_of_ne_nil _ hn
    obtain ⟨hw,hl⟩ := List.mem_filter.mp (show w ∈ (content D.1 (exits D i)).filter (fun w => lessEq w.length D.1.length) from hw)
    obtain ⟨x,e,hf,he,rfl⟩ := (mem_content h hp per w).mp hw
    refine ⟨x,e,hf,he,?_⟩
    simpa only [lessEq,decide_eq_true_eq,h.length_eq,length_textWord] using hl
  · rintro ⟨x,e,hf,he,hl⟩
    have hm : textWord A x e ∈ shortWords D i := by
      apply List.mem_filter.mpr
      exact ⟨(mem_content h hp per _).mpr ⟨x,e,hf,he,rfl⟩,
        by simpa only [lessEq,decide_eq_true_eq,h.length_eq,length_textWord] using hl⟩
    exact fun hn => by rw [hn] at hm; exact List.not_mem_nil hm

theorem shortLoop_spec {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {i : ℕ}
    (h : Represents D.1 (exits D i) (L i)) (closed : SubstringClosed V)
    (hp : 0 < p) (per : Function.Periodic A (p : ℤ)) (hs : hasShort D i = true) :
    Runs V [] [] (shortLoop D i) ∧ cost (shortLoop D i) ≤ 2*p ∧
      ∀ w ∈ (L i).Content, w ∈ shortLoop D i := by
  have hn : shortWords D i ≠ [] := by simpa only [hasShort,Bool.not_eq_true',List.isEmpty_eq_false_iff] using hs
  have hm : (shortWords D i).headD [] ∈ shortWords D i := by
    generalize shortWords D i = X at hn ⊢
    cases X with
    | nil => exact False.elim (hn rfl)
    | cons w X => exact List.mem_cons_self ..
  change (shortWords D i).headD [] ∈ (content D.1 (exits D i)).filter (fun w => lessEq w.length D.1.length) at hm
  obtain ⟨hm,hl⟩ := List.mem_filter.mp hm
  have hw := (mem_content h hp per _).mp hm
  have hlen : ((shortWords D i).headD []).length ≤ p := by
    simpa only [lessEq,decide_eq_true_eq,h.length_eq] using hl
  obtain ⟨hr,hc,hv⟩ := rootContent_spec L (D:=D) (js:=[i])
    (by intro j hj; have := List.mem_singleton.mp hj; subst j; exact h)
    closed hp per ((L i).content_mem hw)
    (by intro j hj; have := List.mem_singleton.mp hj; subst j; exact ⟨_,hw,List.prefix_refl _⟩)
  refine ⟨hr,?_,hv i (by simp)⟩
  change cost (rootContent D [i] ((shortWords D i).headD [])) ≤ _
  rw [hc]
  simp only [List.length_singleton,one_mul]
  omega

variable [Coded α]
omit [DecidableEq α] in
@[fun_prop] theorem poly_shortWords : Poly (fun q : GroupData α × ℕ => shortWords q.1 q.2) := by
  unfold shortWords
  exact BitCode.Poly.filterFn
    (p := fun q : (GroupData α × ℕ) × List α => lessEq q.2.length q.1.1.1.length) (by fun_prop) (by fun_prop)
omit [DecidableEq α] in
@[fun_prop] theorem poly_hasShort : Poly (fun q : GroupData α × ℕ => hasShort q.1 q.2) := by
  unfold hasShort
  fun_prop
@[fun_prop] theorem poly_shortLoop : Poly (fun q : GroupData α × ℕ => shortLoop q.1 q.2) := by
  unfold shortLoop
  exact poly_rootContent.comp (f := fun q : GroupData α × ℕ => (q.1,[q.2],(shortWords q.1 q.2).headD [])) (by fun_prop)
end Superstring.LayerArray


namespace Superstring.BlockClose
open BitCode Hierarchical WalkCode
variable {α : Type} [DecidableEq α] [Inhabited α]

theorem step_nil (vs : Walk α) (L : List (Walk α)) (P : Walk α) : step vs L (P,[]) = (P,[]) := by
  simp [step,select,pool,remaining]

variable {β : Type} [LinearOrder β]
theorem iterate_step (vs : Walk α) (closed : SubstringClosed {w | w ∈ vs}) (L : List (Walk α))
    (ids : List ℕ) (owner per : ℕ → ℕ) (rank : ℕ → β) (s : State α)
    (hP : Runs {w | w ∈ vs} [] [] s.1)
    (valid : ∀ b ∈ s.2, ValidBlock {w | w ∈ vs} ids (lookup L) owner per rank b)
    (ready : ∀ i ∈ ids, (∀ w ∈ lookup L i, w ∈ s.1) ∨ ∃ b ∈ s.2, i ∈ b.members) (n : ℕ) :
    let t := (step vs L)^[n] s
    Runs {w | w ∈ vs} [] [] t.1 ∧
      cost t.1+(t.2.map Block.reserve).sum ≤ cost s.1+(s.2.map Block.reserve).sum ∧
      (∀ w ∈ s.1, w ∈ t.1) ∧ t.2.Sublist s.2 ∧ t.2.length ≤ s.2.length-n ∧
      ∀ i ∈ ids, (∀ w ∈ lookup L i, w ∈ t.1) ∨ ∃ b ∈ t.2, i ∈ b.members := by
  dsimp only
  induction n with
  | zero => exact ⟨hP,le_rfl,fun _ h => h,List.Sublist.refl _,by simp,ready⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    let t := (step vs L)^[n] s
    change Runs _ [] [] t.1 ∧ _ at ih
    by_cases hn : t.2 = []
    · have he : step vs L t = t := by
        rw [← Prod.eta t,hn,step_nil]
      rw [he]
      exact ⟨ih.1,ih.2.1,ih.2.2.1,ih.2.2.2.1,by simp [hn],ih.2.2.2.2.2⟩
    · obtain ⟨hQ,hcost,hvis,hsub,hlen,hr⟩ := step_spec vs closed L ids owner per rank t ih.1 hn
        (fun b hb => valid b (ih.2.2.2.1.subset hb)) ih.2.2.2.2.2
      exact ⟨hQ,hcost.trans ih.2.1,fun w hw => hvis w (ih.2.2.1 w hw),hsub.trans ih.2.2.2.1,
        by change (step vs L t).2.length ≤ _; have hh : t.2.length ≤ s.2.length-n := ih.2.2.2.2.1; omega,hr⟩

omit [DecidableEq α] [Inhabited α] [LinearOrder β] in
theorem rooted_length {V : Set (List α)} {P : Walk α} (hP : Runs V [] [] P) :
    P.length = 2*cost P+1 := by
  cases P with
  | nil => exact False.elim (hP.1.1 rfl)
  | cons a P =>
    have ha : a = [] := by simpa using hP.2.1
    subst a
    have h := length_cost hP.1
    simp only [hP.2.2,Option.getD_some,List.length_nil,Nat.add_zero] at h
    simpa only [List.length_cons] using congrArg (·+1) h

variable [Coded α]
abbrev Input (α : Type) := (Walk α × List (Walk α)) × State α
def iterStep (q : Input α) : Input α := (q.1,step q.1.1 q.1.2 q.2)
def capacity (q : Input α) : ℕ :=
  2*bitSize q + 1 + (2*(cost q.2.1+(q.2.2.map Block.reserve).sum)+1)*(bitSize q+1)
def close (q : Input α) : Walk α :=
  (((cappedStep iterStep)^[q.2.2.length] (capacity q,q)).2).2.1

omit [LinearOrder β] [Coded α] in
theorem iterate_iterStep (q : Input α) (n : ℕ) :
    iterStep^[n] q = (q.1,(step q.1.1 q.1.2)^[n] q.2) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,Function.iterate_succ_apply']; rfl

omit [LinearOrder β] [DecidableEq α] [Inhabited α] in
theorem state_size (q : Input α) (t : State α)
    (hP : Runs {w | w ∈ q.1.1} [] [] t.1)
    (hcost : cost t.1 ≤ cost q.2.1+(q.2.2.map Block.reserve).sum)
    (hsub : t.2.Sublist q.2.2) : bitSize (q.1,t) ≤ capacity q := by
  have eqQ : bitSize q = bitSize q.1+bitSize q.2 := bitSize_prod q.1 q.2
  have eqCtx : bitSize q.1 = bitSize q.1.1+bitSize q.1.2 := bitSize_prod q.1.1 q.1.2
  have eqS : bitSize q.2 = bitSize q.2.1+bitSize q.2.2 := bitSize_prod q.2.1 q.2.2
  have eqT : bitSize t = bitSize t.1+bitSize t.2 := bitSize_prod t.1 t.2
  have eqOut : bitSize (q.1,t) = bitSize q.1+bitSize t := bitSize_prod q.1 t
  have hv : ∀ w ∈ t.1, bitSize w ≤ bitSize q := by
    intro w hw
    have hm := bitSize_mem (hP.1.2.1 w hw)
    omega
  have hh := bitSize_map_le t.1 (fun w => w) (bitSize q) hv
  have hid : t.1.map (fun w => w) = t.1 := by simp
  rw [hid,rooted_length hP] at hh
  have hb := bitSize_sublist hsub
  unfold capacity
  nlinarith

theorem close_spec (q : Input α) (closed : SubstringClosed {w | w ∈ q.1.1})
    (ids : List ℕ) (owner per : ℕ → ℕ) (rank : ℕ → β)
    (hP : Runs {w | w ∈ q.1.1} [] [] q.2.1)
    (valid : ∀ b ∈ q.2.2, ValidBlock {w | w ∈ q.1.1} ids (lookup q.1.2) owner per rank b)
    (ready : ∀ i ∈ ids, (∀ w ∈ lookup q.1.2 i, w ∈ q.2.1) ∨ ∃ b ∈ q.2.2, i ∈ b.members) :
    Runs {w | w ∈ q.1.1} [] [] (close q) ∧
      cost (close q) ≤ cost q.2.1+(q.2.2.map Block.reserve).sum ∧
      (∀ w ∈ q.2.1, w ∈ close q) ∧ Covers (lookup q.1.2) ids (close q) := by
  have hi := iterate_step q.1.1 closed q.1.2 ids owner per rank q.2 hP valid ready
  have he := iterate_cappedStep_eq iterStep q.2.2.length (capacity q) q (by
    intro n _ _
    rw [iterate_iterStep]
    exact state_size q _ (hi n).1 (by have := (hi n).2.1; omega) (hi n).2.2.2.1)
  unfold close
  rw [he,iterate_iterStep]
  dsimp only
  have hh := hi q.2.2.length
  have hz : ((step q.1.1 q.1.2)^[q.2.2.length] q.2).2 = [] := by
    apply List.length_eq_zero_iff.mp
    have := hh.2.2.2.2.1; omega
  refine ⟨hh.1,by have := hh.2.1; omega,hh.2.2.1,?_⟩
  intro i hi
  rcases hh.2.2.2.2.2 i hi with h | ⟨b,hb,_⟩
  · exact h
  · rw [hz] at hb; exact False.elim (List.not_mem_nil hb)

omit [LinearOrder β] in
@[fun_prop] theorem poly_iterStep : Poly (iterStep : Input α → Input α) := by
  exact BitCode.Poly.fst.pair poly_step
omit [LinearOrder β] [DecidableEq α] [Inhabited α] in
@[fun_prop] theorem poly_capacity : Poly (capacity : Input α → ℕ) := by
  have hr : Poly (fun q : Input α => (q.2.2.map Block.reserve).sum) := poly_reserves.comp (by fun_prop)
  unfold capacity
  fun_prop
omit [LinearOrder β] in
@[fun_prop] theorem poly_close : Poly (close : Input α → Walk α) := by
  have ht : Poly (fun q : Input α => ((cappedStep iterStep)^[q.2.2.length] (capacity q,q)).2) :=
    (BitCode.Poly.cappedIterate poly_iterStep).comp
      (f := fun q : Input α => (q.2.2.length,(capacity q,q))) (by fun_prop)
  exact BitCode.Poly.fst.comp (BitCode.Poly.snd.comp ht)
end Superstring.BlockClose


namespace Superstring.WalkCode
open Hierarchical BitCode
variable {α : Type}
def collect (Ps : List (Walk α)) : Walk α := Ps.foldl join [[]]

theorem fold_join_spec {V : Set (List α)} (Ps : List (Walk α)) (P : Walk α)
    (hP : Runs V [] [] P) (h : ∀ Q ∈ Ps, Runs V [] [] Q) :
    Runs V [] [] (Ps.foldl join P) ∧
      cost (Ps.foldl join P) = cost P+(Ps.map cost).sum ∧
      (∀ w ∈ P, w ∈ Ps.foldl join P) ∧
      ∀ Q ∈ Ps, ∀ w ∈ Q, w ∈ Ps.foldl join P := by
  induction Ps generalizing P with
  | nil => exact ⟨hP,by simp,fun _ hw => hw,by simp⟩
  | cons Q Ps ih =>
    have hQ := h Q (List.mem_cons_self ..)
    obtain ⟨hr,hc,hv,ha⟩ := ih (join P Q) (runs_join hP hQ)
      (fun R hR => h R (List.mem_cons_of_mem _ hR))
    refine ⟨hr,?_,?_,?_⟩
    · simp only [List.foldl_cons,List.map_cons,List.sum_cons,hc,cost_join P Q [] hP.2.2 hQ.2.1]
      omega
    · intro w hw; exact hv w ((mem_join hP.2.2 hQ.2.1).mpr (Or.inl hw))
    · intro R hR w hw
      rcases List.mem_cons.mp hR with rfl|hR
      · exact hv w ((mem_join hP.2.2 hQ.2.1).mpr (Or.inr hw))
      · exact ha R hR w hw

theorem collect_spec {V : Set (List α)} (h0 : ([] : List α) ∈ V)
    (Ps : List (Walk α)) (h : ∀ Q ∈ Ps, Runs V [] [] Q) :
    Runs V [] [] (collect Ps) ∧ cost (collect Ps) = (Ps.map cost).sum ∧
      ∀ Q ∈ Ps, ∀ w ∈ Q, w ∈ collect Ps := by
  have hh := fold_join_spec Ps [[]] ⟨valid_nil [] h0,rfl,rfl⟩ h
  exact ⟨hh.1,by simpa only [collect,cost_singleton,Nat.zero_add] using hh.2.1,hh.2.2.2⟩

variable [Coded α]
@[fun_prop] theorem poly_collect : Poly (collect : List (Walk α) → Walk α) := by
  have hs : ∀ P Q : Walk α, bitSize (join P Q) ≤ bitSize P + (Polynomial.X : Polynomial ℕ).eval (bitSize Q) := by
    intro P Q
    simpa only [Polynomial.eval_X] using size_join P Q
  exact (BitCode.Poly.foldl_additive poly_join Polynomial.X hs).comp
    (f := fun Ps : List (Walk α) => (Ps,[[]])) (by fun_prop)
end Superstring.WalkCode

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.DistributeCode
open BitCode Hierarchical WalkCode LayerArray BlockClose
variable {α : Type} [Inhabited α] [DecidableEq α]
abbrev Result (α : Type) := Walk α × List (BlockClose.Block α) × List ℕ

def one (D : GroupData α) (src tar off i : ℕ) (a b : ℤ) : Result α :=
  if hasShort D i then (shortLoop D i,[],[])
  else if decide (b ≤ GeoCode.exit (exits D i) a+D.1.length) then
    ([[]],[BlockFactory.individual D src tar off i a b],[])
  else ([[]],[],[i])

def budget (o : Result α) (p : ℕ) : ℕ :=
  cost o.1+(o.2.1.map Block.reserve).sum+2*(o.2.2.length*p)
def combine (x y : Result α) : Result α :=
  (join x.1 y.1,x.2.1++y.2.1,x.2.2++y.2.2)
def many (D : GroupData α) (src tar off : ℕ) (I : List ℕ) (a b : ℤ) : Result α :=
  let os := I.map (fun i => one D src tar off i a b)
  (collect (os.map Prod.fst),os.flatMap (fun o => o.2.1),os.flatMap (fun o => o.2.2))

variable [LinearOrder α]
theorem one_spec {V : Set (List α)} {A B : ℤ → α} {p q : ℕ}
    (L : ℕ → Layer V A p) (T : Layer V B q) {D : GroupData α} {i src tar off : ℕ}
    (h : Represents D.1 (exits D i) (L i)) (closed : SubstringClosed V)
    (hp : 0 < p) (hq : 0 < q) (perA : Function.Periodic A (p : ℤ))
    (perB : Function.Periodic B (q : ℤ)) (letters : ∀ x, [A x] ∈ V)
    (R : T.Record A) (hne : A ≠ fun x => B (x+R.offset))
    (hf : (L i).first R.start ≤ R.stop)
    (ids : List ℕ) (ls : ℕ → Walk α) (owner periods : ℕ → ℕ) (rank : ℕ → Lex (ℕ → α))
    (hsrc : periods src = p) (htar : tar ∈ ids) (hown : owner (off+i) = src)
    (htper : periods (owner tar) = q)
    (hrec : textWord A R.start R.stop ∈ ls tar)
    (hlayers : ∀ w ∈ ls (off+i), w ∈ (L i).Content) :
    let o := one D src tar off i R.start R.stop
    Runs V [] [] o.1 ∧ budget o p ≤ 2*p ∧
      (∀ b ∈ o.2.1, ValidBlock V ids ls owner periods rank b) ∧
      ((∀ w ∈ ls (off+i), w ∈ o.1) ∨ (∃ b ∈ o.2.1, off+i ∈ b.members) ∨ i ∈ o.2.2) ∧
      o.2.2.Sublist [i] ∧
      ∀ j ∈ o.2.2, R.start+p < (L j).first R.start ∧ (L j).last R.start < R.stop-p := by
  dsimp only
  have h0 : ([] : List α) ∈ V := closed (letters 0) List.nil_infix
  have hroot : Runs V [] [] ([[]] : Walk α) := ⟨valid_nil [] h0,rfl,rfl⟩
  by_cases hs : hasShort D i = true
  · rw [one,ite_eq_left hs]
    obtain ⟨hr,hc,hv⟩ := shortLoop_spec L h closed hp perA hs
    exact ⟨hr,by simpa [budget] using hc,by simp,Or.inl (fun w hw => hv w (hlayers w hw)),by simp,by simp⟩
  · rw [one,ite_eq_right hs]
    by_cases ht : decide (R.stop ≤ GeoCode.exit (exits D i) R.start+D.1.length) = true
    · rw [ite_eq_left ht]
      have ht' : R.stop ≤ (L i).last R.start+p := by
        simpa only [h.exit_eq,h.length_eq,decide_eq_true_eq,Layer.last] using ht
      have hb := BlockFactory.individual_valid L T h closed hp hq perA perB letters R hne hf ht'
        ids ls owner periods rank hsrc htar hown htper
        (by intro he; rw [he,hsrc] at htper; exact htper) hrec hlayers
      refine ⟨hroot,?_,?_,Or.inr (Or.inl ⟨_,List.mem_singleton_self _,?_⟩),by simp,by simp⟩
      · simp [budget,BlockFactory.individual,BlockFactory.pack,Block.reserve,h.length_eq]
      · intro b hb'; have := List.mem_singleton.mp hb'; subst b; exact hb
      · simp [BlockFactory.individual,BlockFactory.pack,Block.members]
    · rw [ite_eq_right ht]
      have hn : ¬ (L i).HasShort p := fun hx => hs ((hasShort_eq h hp perA).mpr hx)
      have hl := (L i).first_long_of_not_short p hn R.start
      have ht' : (L i).last R.start+p < R.stop := by
        simp only [h.exit_eq,h.length_eq,decide_eq_true_eq] at ht
        change (L i).z R.start+p < R.stop
        omega
      refine ⟨hroot,by simp [budget],by simp,Or.inr (Or.inr (by simp)),List.Sublist.refl _,?_⟩
      intro j hj; have := List.mem_singleton.mp hj; subst j
      exact ⟨by omega,by omega⟩

omit [DecidableEq α] [Inhabited α] [LinearOrder α] in
theorem combine_budget (x y : Result α) (p : ℕ) {V : Set (List α)}
    (hx : Runs V [] [] x.1) (hy : Runs V [] [] y.1) :
    budget (combine x y) p = budget x p+budget y p := by
  simp only [budget,combine,cost_join _ _ _ hx.2.2 hy.2.1,List.map_append,List.sum_append,List.length_append]
  ring

omit [DecidableEq α] [Inhabited α] [LinearOrder α] in
theorem gather_budget {V : Set (List α)} (h0 : ([] : List α) ∈ V)
    (os : List (Result α)) (hr : ∀ o ∈ os, Runs V [] [] o.1) (p : ℕ) :
    budget (collect (os.map Prod.fst),os.flatMap (fun o => o.2.1),os.flatMap (fun o => o.2.2)) p =
      (os.map (fun o => budget o p)).sum := by
  have hh := collect_spec h0 (os.map Prod.fst) (by
    intro P hP; obtain ⟨o,ho,rfl⟩ := List.mem_map.mp hP; exact hr o ho)
  simp only [budget,hh.2.1,List.map_map]
  clear hh hr
  induction os with
  | nil => simp
  | cons o os ih =>
    simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.map_append,List.sum_append,
      List.length_append,Function.comp_apply,Nat.add_mul,Nat.mul_add]
    omega

omit [LinearOrder α] [Inhabited α] [DecidableEq α] in
theorem flatMap_sublist (I : List ℕ) (f : ℕ → List ℕ)
    (h : ∀ i ∈ I, (f i).Sublist [i]) : (I.flatMap f).Sublist I := by
  induction I with
  | nil => exact .refl _
  | cons i I ih =>
    simpa only [List.flatMap_cons,List.singleton_append] using
      (h i (List.mem_cons_self ..)).append (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))

theorem many_spec {V : Set (List α)} {A B : ℤ → α} {p q : ℕ}
    (L : ℕ → Layer V A p) (T : Layer V B q) {D : GroupData α} {I : List ℕ} {src tar off : ℕ}
    (h : ∀ i ∈ I, Represents D.1 (exits D i) (L i)) (closed : SubstringClosed V)
    (hp : 0 < p) (hq : 0 < q) (perA : Function.Periodic A (p : ℤ))
    (perB : Function.Periodic B (q : ℤ)) (letters : ∀ x, [A x] ∈ V)
    (R : T.Record A) (hne : A ≠ fun x => B (x+R.offset))
    (hf : ∀ i ∈ I, (L i).first R.start ≤ R.stop)
    (ids : List ℕ) (ls : ℕ → Walk α) (owner periods : ℕ → ℕ) (rank : ℕ → Lex (ℕ → α))
    (hsrc : periods src = p) (htar : tar ∈ ids) (hown : ∀ i ∈ I, owner (off+i) = src)
    (htper : periods (owner tar) = q) (hrec : textWord A R.start R.stop ∈ ls tar)
    (hlayers : ∀ i ∈ I, ∀ w ∈ ls (off+i), w ∈ (L i).Content) :
    let o := many D src tar off I R.start R.stop
    Runs V [] [] o.1 ∧ budget o p ≤ 2*(I.length*p) ∧
      (∀ b ∈ o.2.1, ValidBlock V ids ls owner periods rank b) ∧
      (∀ i ∈ I, (∀ w ∈ ls (off+i), w ∈ o.1) ∨ (∃ b ∈ o.2.1, off+i ∈ b.members) ∨ i ∈ o.2.2) ∧
      o.2.2.Sublist I ∧
      ∀ j ∈ o.2.2, R.start+p < (L j).first R.start ∧ (L j).last R.start < R.stop-p := by
  let f := fun i => one D src tar off i R.start R.stop
  have hh := fun i hi => one_spec L T (h i hi) closed hp hq perA perB letters R hne (hf i hi)
    ids ls owner periods rank hsrc htar (hown i hi) htper hrec (hlayers i hi)
  have h0 : ([] : List α) ∈ V := closed (letters 0) List.nil_infix
  have hr : ∀ o ∈ I.map f, Runs V [] [] o.1 := by
    intro o ho; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ho; exact (hh i hi).1
  have hc := collect_spec h0 ((I.map f).map Prod.fst) (by
    intro P hP; obtain ⟨o,ho,rfl⟩ := List.mem_map.mp hP; exact hr o ho)
  change Runs V [] [] (collect ((I.map f).map Prod.fst)) ∧ _
  refine ⟨hc.1,?_,?_,?_,?_,?_⟩
  · change budget (collect ((I.map f).map Prod.fst),(I.map f).flatMap (fun o => o.2.1),(I.map f).flatMap (fun o => o.2.2)) p ≤ _
    rw [gather_budget h0 (I.map f) hr p,List.map_map]
    have hb : (I.map (fun i => budget (f i) p)).sum ≤ (I.map (fun _ => 2*p)).sum :=
      List.sum_le_sum (fun i hi => (hh i hi).2.1)
    exact hb.trans_eq (by simp [List.sum_replicate]; ring)
  · intro b hb
    obtain ⟨o,ho,hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ho
    exact (hh i hi).2.2.1 b hb
  · intro i hi
    rcases (hh i hi).2.2.2.1 with hv|⟨b,hb,hm⟩|ha
    · exact Or.inl (fun w hw => hc.2.2 (f i).1 (List.mem_map.mpr ⟨f i,List.mem_map.mpr ⟨i,hi,rfl⟩,rfl⟩) w (hv w hw))
    · exact Or.inr (Or.inl ⟨b,List.mem_flatMap.mpr ⟨f i,List.mem_map.mpr ⟨i,hi,rfl⟩,hb⟩,hm⟩)
    · exact Or.inr (Or.inr (List.mem_flatMap.mpr ⟨f i,List.mem_map.mpr ⟨i,hi,rfl⟩,ha⟩))
  · change ((I.map f).flatMap _).Sublist I
    rw [List.flatMap_map]
    exact flatMap_sublist I _ (fun i hi => (hh i hi).2.2.2.2.1)
  · intro j hj
    obtain ⟨o,ho,hj⟩ := List.mem_flatMap.mp hj
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ho
    exact (hh i hi).2.2.2.2.2 j hj

variable [Coded α]
instance codedResult : Coded (Result α) := codedProd
abbrev OneInput (α : Type) := (GroupData α × ℕ × ℕ × ℕ) × (ℕ × ℤ × ℤ)
instance codedOneInput : Coded (OneInput α) := codedProd
omit [LinearOrder α] in
@[fun_prop] theorem poly_one : Poly (fun q : OneInput α => one q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold one
  fun_prop
omit [LinearOrder α] [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem poly_budget : Poly (fun q : Result α × ℕ => budget q.1 q.2) := by
  unfold budget
  have hs : Poly (fun q : Result α × ℕ => (q.1.2.1.map Block.reserve).sum) := poly_reserves.comp (by fun_prop)
  fun_prop
omit [LinearOrder α] in
@[fun_prop] theorem poly_many : Poly (fun q : (GroupData α × ℕ × ℕ × ℕ) × (List ℕ × ℤ × ℤ) =>
    many q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2.1 q.2.2.1 q.2.2.2) := by
  have hm : Poly (fun q : (GroupData α × ℕ × ℕ × ℕ) × (List ℕ × ℤ × ℤ) =>
      q.2.1.map (fun i => one q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 i q.2.2.1 q.2.2.2)) := by
    exact BitCode.Poly.mapFn
      (f := fun q : ((GroupData α × ℕ × ℕ × ℕ) × (List ℕ × ℤ × ℤ)) × ℕ =>
        one q.1.1.1 q.1.1.2.1 q.1.1.2.2.1 q.1.1.2.2.2 q.2 q.1.2.2.1 q.1.2.2.2)
      (poly_one.comp (f := fun q : ((GroupData α × ℕ × ℕ × ℕ) × (List ℕ × ℤ × ℤ)) × ℕ =>
        (q.1.1,(q.2,q.1.2.2))) (by fun_prop)) (by fun_prop)
  unfold many
  have h1 : Poly (fun os : List (Result α) => collect (os.map Prod.fst)) :=
    poly_collect.comp (BitCode.Poly.mapFn (f := fun q : List (Result α) × Result α => q.2.1) (by fun_prop) (by fun_prop))
  have h2 : Poly (fun os : List (Result α) => os.flatMap (fun o => o.2.1)) :=
    BitCode.Poly.flatMapFn (f := fun q : List (Result α) × Result α => q.2.2.1) (by fun_prop) (by fun_prop)
  have h3 : Poly (fun os : List (Result α) => os.flatMap (fun o => o.2.2)) :=
    BitCode.Poly.flatMapFn (f := fun q : List (Result α) × Result α => q.2.2.2) (by fun_prop) (by fun_prop)
  exact (h1.pair (h2.pair h3)).comp hm
end Superstring.DistributeCode


namespace Superstring.LayerArray
open BitCode Hierarchical WalkCode
variable {α : Type} [Inhabited α] [DecidableEq α]
def belowLoop (D : GroupData α) (i : ℕ) (a b : ℤ) : Walk α :=
  if hasShort D i then shortLoop D i else individual D i a b
def below (D : GroupData α) (I : List ℕ) (P : Walk α) (a b : ℤ) : Walk α :=
  fill P (I.map (fun i => belowLoop D i a b))

theorem belowLoop_spec {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {i base : ℕ}
    (h : Represents D.1 (exits D i) (L i)) (closed : SubstringClosed V)
    (hp : 0 < p) (per : Function.Periodic A (p : ℤ)) (letters : ∀ x, [A x] ∈ V)
    {P : Walk α} (hP : Runs V [] [] P)
    (hcover : ∀ w ∈ (L base).Content, w ∈ P)
    (hbelow : ∀ x, (L i).z x ≤ (L base).z x)
    {a b : ℤ} (hbf : (L base).first a ≤ b) (hbl : b ≤ (L base).last a)
    (hlen : b-a < 2*p) :
    (∃ u, Runs V u u (belowLoop D i a b)) ∧ cost (belowLoop D i a b) ≤ 2*p ∧
      (∀ w ∈ (L i).Content, w ∈ belowLoop D i a b) ∧
      ∃ w, w ∈ P ∧ w ∈ belowLoop D i a b := by
  by_cases hs : hasShort D i = true
  · rw [belowLoop,ite_eq_left hs]
    obtain ⟨hr,hc,hv⟩ := shortLoop_spec L h closed hp per hs
    exact ⟨⟨[],hr⟩,hc,hv,[],List.mem_of_head? hP.2.1,List.mem_of_head? hr.2.1⟩
  · rw [belowLoop,ite_eq_right hs]
    have hn : ¬ (L i).HasShort p := fun hh => hs ((hasShort_eq h hp per).mpr hh)
    have hl := (L i).first_long_of_not_short p hn a
    have hf : (L i).first a ≤ b := (hbelow (a-1)).trans hbf
    have hfl := (L i).first_le_last a
    obtain ⟨hr,hc,hv,hw,_⟩ := individual_spec L h closed hp per letters p
      ((L base).start_le_first a |>.trans hbf) ((L base).actual a b hbf hbl) hf (by omega) (by omega)
    exact ⟨⟨_,hr⟩,hc.le,hv,_,hcover _ ⟨a,b,hbf,hbl,rfl⟩,hw⟩

theorem below_spec {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {I : List ℕ} {base : ℕ}
    (h : ∀ i ∈ I, Represents D.1 (exits D i) (L i)) (closed : SubstringClosed V)
    (hp : 0 < p) (per : Function.Periodic A (p : ℤ)) (letters : ∀ x, [A x] ∈ V)
    {P : Walk α} (hP : Runs V [] [] P)
    (hcover : ∀ w ∈ (L base).Content, w ∈ P)
    (hbelow : ∀ i ∈ I, ∀ x, (L i).z x ≤ (L base).z x)
    {a b : ℤ} (hbf : (L base).first a ≤ b) (hbl : b ≤ (L base).last a)
    (hlen : b-a < 2*p) :
    Runs V [] [] (below D I P a b) ∧ cost (below D I P a b) ≤ cost P+2*(I.length*p) ∧
      (∀ w ∈ P, w ∈ below D I P a b) ∧
      ∀ i ∈ I, ∀ w ∈ (L i).Content, w ∈ below D I P a b := by
  have hh := fun i hi => belowLoop_spec L (h i hi) closed hp per letters hP hcover (hbelow i hi) hbf hbl hlen
  obtain ⟨hr,hc,hv⟩ := fill_spec P (I.map (fun i => belowLoop D i a b)) hP
    (by intro Q hQ; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hQ; exact (hh i hi).1)
    (by intro Q hQ; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hQ; exact (hh i hi).2.2.2)
  refine ⟨hr,?_,fun w hw => (hv w).mpr (Or.inl hw),?_⟩
  · change cost (fill P _) ≤ _
    rw [hc,List.map_map]
    have hb := List.sum_le_sum (g := fun _ : ℕ => 2*p) (fun i hi => (hh i hi).2.1)
    have he : (I.map (fun _ => 2*p)).sum = 2*(I.length*p) := by simp [List.sum_replicate]; ring
    rw [he] at hb
    exact Nat.add_le_add_left hb _
  · intro i hi w hw
    exact (hv w).mpr (Or.inr ⟨_,List.mem_map.mpr ⟨i,hi,rfl⟩,(hh i hi).2.2.1 w hw⟩)

variable [Coded α]
@[fun_prop] theorem poly_belowLoop : Poly (fun q : GroupData α × ℕ × ℤ × ℤ =>
    belowLoop q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold belowLoop
  fun_prop
@[fun_prop] theorem poly_below : Poly (fun q : (GroupData α × List ℕ) × Walk α × ℤ × ℤ =>
    below q.1.1 q.1.2 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold below
  have hm : Poly (fun q : (GroupData α × List ℕ) × Walk α × ℤ × ℤ =>
      q.1.2.map (fun i => belowLoop q.1.1 i q.2.2.1 q.2.2.2)) :=
    BitCode.Poly.mapFn (f := fun q : ((GroupData α × List ℕ) × Walk α × ℤ × ℤ) × ℕ =>
      belowLoop q.1.1.1 q.2 q.1.2.2.1 q.1.2.2.2) (by fun_prop) (by fun_prop)
  fun_prop
end Superstring.LayerArray


namespace Superstring.DistributeCode
open BitCode Hierarchical WalkCode LayerArray BlockClose
variable {α : Type} [Inhabited α] [DecidableEq α]
def record (D : GroupData α) (src tar off : ℕ) (I : List ℕ) (lo hi : ℕ) (a b t : ℤ) : Result α :=
  let J := I.filter (fun i => lessEq lo i)
  if decide (b ≤ GeoCode.exit (exits D lo) a+(J.length*D.1.length : ℕ)) then
    let o := many D src tar off (I.filter (fun i => !lessEq lo i)) a b
    (o.1,BlockFactory.collective D src tar off J lo hi a b t::o.2.1,o.2.2)
  else many D src tar off I a b

variable [LinearOrder α]
theorem record_spec {V : Set (List α)} {A B : ℤ → α} {p q : ℕ}
    (L : ℕ → Layer V A p) (T : Layer V B q) {D : GroupData α} {I : List ℕ} {src tar off lo hi : ℕ}
    (h : ∀ i ∈ I, Represents D.1 (exits D i) (L i)) (closed : SubstringClosed V)
    (hp : 0 < p) (hq : 0 < q) (perA : Function.Periodic A (p : ℤ))
    (perB : Function.Periodic B (q : ℤ)) (letters : ∀ x, [A x] ∈ V)
    (R : T.Record A) (hne : A ≠ fun x => B (x+R.offset))
    (t : ℤ) (hat : R.start ≤ t) (htb : t < R.stop)
    (hmax : ∀ x, forward A x ≤ forward A t)
    (hlo : lo ∈ I) (hhi : hi ∈ I) (hlohi : lo ≤ hi)
    (lower : ∀ i ∈ I, lo ≤ i → ∀ x, (L lo).z x ≤ (L i).z x)
    (upper : ∀ i ∈ I, ∀ x, (L i).z x ≤ (L hi).z x)
    (hfirst : ∀ i ∈ I, i < lo → (L i).first R.start ≤ R.stop)
    (hH : (L hi).first t ≤ R.stop+((I.filter (fun i => lessEq lo i)).length*p : ℕ))
    (hsharp : (L hi).first t-(L lo).last t ≤ (((I.filter (fun i => lessEq lo i)).length-1)*p : ℕ))
    (ids : List ℕ) (ls : ℕ → Walk α) (owner periods : ℕ → ℕ) (rank : ℕ → Lex (ℕ → α))
    (hsrc : periods src = p) (htar : tar ∈ ids) (hown : ∀ i ∈ I, owner (off+i) = src)
    (htper : periods (owner tar) = q)
    (hrank : rank (owner tar) ≤ rank src → ∀ x, forward (fun x => B (x+R.offset)) x ≤ forward A t)
    (hrec : textWord A R.start R.stop ∈ ls tar)
    (hlayers : ∀ i ∈ I, ∀ w ∈ ls (off+i), w ∈ (L i).Content) :
    let o := record D src tar off I lo hi R.start R.stop t
    Runs V [] [] o.1 ∧ budget o p ≤ 2*(I.length*p) ∧
      (∀ b ∈ o.2.1, ValidBlock V ids ls owner periods rank b) ∧
      (∀ i ∈ I, (∀ w ∈ ls (off+i), w ∈ o.1) ∨ (∃ b ∈ o.2.1, off+i ∈ b.members) ∨ i ∈ o.2.2) ∧
      o.2.2.Sublist I ∧
      ∀ j ∈ o.2.2, R.start+p < (L j).first R.start ∧ (L j).last R.start < R.stop-p := by
  let J := I.filter (fun i => lessEq lo i)
  let F := I.filter (fun i => !lessEq lo i)
  have hJ : ∀ i, i ∈ J ↔ i ∈ I ∧ lo ≤ i := by intro i; simp [J,lessEq]
  have hF : ∀ i, i ∈ F ↔ i ∈ I ∧ i < lo := by intro i; simp [F,lessEq]
  have hloJ : lo ∈ J := (hJ lo).mpr ⟨hlo,le_rfl⟩
  have hhiJ : hi ∈ J := (hJ hi).mpr ⟨hhi,hlohi⟩
  have hk : 0 < J.length := List.length_pos_of_mem hloJ
  have hgap := Processing.wide_band (L hi) (L lo) hp hk t hsharp R.start
  by_cases hc : decide (R.stop ≤ GeoCode.exit (exits D lo) R.start+(J.length*D.1.length : ℕ)) = true
  · change _ ∧ _
    simp only [record,show I.filter (fun i => lessEq lo i) = J from rfl,ite_eq_left hc]
    have hb : R.stop ≤ (L lo).last R.start+(J.length*p : ℕ) := by
      simpa only [(h lo hlo).exit_eq,(h lo hlo).length_eq,Layer.last,decide_eq_true_eq] using hc
    have hblock := BlockFactory.collective_valid L T (D:=D) (js:=J)
      (fun i hi => h i ((hJ i).mp hi).1) hloJ hhiJ
      (fun i hi => lower i ((hJ i).mp hi).1 ((hJ i).mp hi).2)
      (fun i hi => upper i ((hJ i).mp hi).1) closed hp hq perA perB letters R hne t hat htb
      hmax hH hgap hb hsharp ids ls owner periods rank hsrc htar
      (fun i hi => hown i ((hJ i).mp hi).1) htper
      (by intro he; rw [he,hsrc] at htper; exact htper) hrank hrec
      (fun i hi => hlayers i ((hJ i).mp hi).1)
    obtain ⟨hr,hbudget,hblocks,hcov,hs,hm⟩ := many_spec L T (D:=D) (I:=F)
      (fun i hi => h i ((hF i).mp hi).1) closed hp hq perA perB letters R hne
      (fun i hi => hfirst i ((hF i).mp hi).1 ((hF i).mp hi).2)
      ids ls owner periods rank hsrc htar (fun i hi => hown i ((hF i).mp hi).1) htper hrec
      (fun i hi => hlayers i ((hF i).mp hi).1)
    refine ⟨hr,?_,?_,?_,hs.trans (List.filter_sublist),hm⟩
    · have he : F.length+J.length = I.length := by
        simpa only [F,J,Nat.add_comm] using (List.length_eq_length_filter_add (l:=I) (fun i => lessEq lo i)).symm
      have hbsize : (BlockFactory.collective D src tar off J lo hi R.start R.stop t).reserve = 2*(J.length*p) := by
        simp only [BlockFactory.collective,BlockFactory.pack,Block.reserve,(h lo hlo).length_eq]
      change cost _ + ((_ :: _).map Block.reserve).sum + _ ≤ _
      simp only [List.map_cons,List.sum_cons,hbsize]
      change cost _ + _ + _ ≤ _ at hbudget
      have ha : 2*(I.length*p) = 2*(F.length*p)+2*(J.length*p) := by rw [← he]; ring
      dsimp only [F] at hbudget ha
      omega
    · intro b hb'
      rcases List.mem_cons.mp hb' with rfl|hb'
      · exact hblock
      · exact hblocks b hb'
    · intro i hi
      by_cases hj : lo ≤ i
      · exact Or.inr (Or.inl ⟨_,List.mem_cons_self ..,List.mem_map.mpr ⟨i,(hJ i).mpr ⟨hi,hj⟩,rfl⟩⟩)
      · rcases hcov i ((hF i).mpr ⟨hi,by omega⟩) with hv|⟨b,hb,hm⟩|ha
        · exact Or.inl hv
        · exact Or.inr (Or.inl ⟨b,List.mem_cons_of_mem _ hb,hm⟩)
        · exact Or.inr (Or.inr ha)
  · simp only [record,show I.filter (fun i => lessEq lo i) = J from rfl,ite_eq_right hc]
    apply many_spec L T h closed hp hq perA perB letters R hne _ ids ls owner periods rank hsrc htar hown htper hrec hlayers
    intro i hmem
    have hb : (L lo).last R.start+(J.length*p : ℕ) < R.stop := by
      simp only [(h lo hlo).exit_eq,(h lo hlo).length_eq,decide_eq_true_eq] at hc
      change (L lo).z R.start+_ < _
      omega
    have hu := upper i hmem (R.start-1)
    change (L i).first R.start ≤ (L hi).first R.start at hu
    omega

variable [Coded α]
abbrev RecordInput (α : Type) := (GroupData α × ℕ × ℕ × ℕ) × (List ℕ × ℕ × ℕ) × (ℤ × ℤ × ℤ)
instance codedRecordInput : Coded (RecordInput α) := codedProd
omit [LinearOrder α] in
@[fun_prop] theorem poly_record : Poly (fun q : RecordInput α =>
    record q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  have hj : Poly (fun q : RecordInput α => q.2.1.1.filter (fun i => lessEq q.2.1.2.1 i)) :=
    BitCode.Poly.filterFn (p := fun q : RecordInput α × ℕ => lessEq q.1.2.1.2.1 q.2) (by fun_prop) (by fun_prop)
  have hf : Poly (fun q : RecordInput α => q.2.1.1.filter (fun i => !lessEq q.2.1.2.1 i)) :=
    BitCode.Poly.filterFn (p := fun q : RecordInput α × ℕ => !lessEq q.1.2.1.2.1 q.2) (by fun_prop) (by fun_prop)
  have hc : Poly (fun q : RecordInput α => BlockFactory.collective q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2
      (q.2.1.1.filter (fun i => lessEq q.2.1.2.1 i)) q.2.1.2.1 q.2.1.2.2 q.2.2.1 q.2.2.2.1 q.2.2.2.2) :=
    BlockFactory.poly_collective.comp (f := fun q : RecordInput α =>
      (q.1,((q.2.1.1.filter (fun i => lessEq q.2.1.2.1 i)),q.2.1.2),q.2.2)) (by fun_prop)
  have hm : Poly (fun q : RecordInput α => many q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2
      (q.2.1.1.filter (fun i => !lessEq q.2.1.2.1 i)) q.2.2.1 q.2.2.2.1) :=
    poly_many.comp (f := fun q : RecordInput α =>
      (q.1,(q.2.1.1.filter (fun i => !lessEq q.2.1.2.1 i)),q.2.2.1,q.2.2.2.1)) (by fun_prop)
  have hm' : Poly (fun q : RecordInput α => many q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2.1.1 q.2.2.1 q.2.2.2.1) :=
    poly_many.comp (f := fun q : RecordInput α => (q.1,q.2.1.1,q.2.2.1,q.2.2.2.1)) (by fun_prop)
  unfold record
  dsimp only
  apply BitCode.Poly.ite
  · fun_prop
  · fun_prop
  · exact hm'
end Superstring.DistributeCode


namespace Superstring.LayerArray
open BitCode Hierarchical WalkCode
variable {α : Type} [Inhabited α] [DecidableEq α]
def attachBand (D : GroupData α) (I : List ℕ) (lo hi : ℕ) (P : Walk α) (t : ℤ) : Walk α :=
  splice P (band D I lo hi I.length t)

theorem band_general {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {I : List ℕ} {lo hi k : ℕ}
    (h : ∀ i ∈ I, Represents D.1 (exits D i) (L i))
    (hl : Represents D.1 (exits D lo) (L lo)) (hh : Represents D.1 (exits D hi) (L hi))
    (lower : ∀ i ∈ I, ∀ x, (L lo).z x ≤ (L i).z x)
    (upper : ∀ i ∈ I, ∀ x, (L i).z x ≤ (L hi).z x)
    (hlohi : ∀ x, (L lo).z x ≤ (L hi).z x)
    (closed : SubstringClosed V) (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    (letters : ∀ x, [A x] ∈ V) (t : ℤ)
    (hB : (L hi).first t-(L lo).last t ≤ (k*p : ℕ)) :
    Runs V (textWord A t ((L lo).last t)) (textWord A t ((L lo).last t)) (band D I lo hi k t) ∧
      cost (band D I lo hi k t) ≤ (k+I.length)*p ∧
      ∀ i ∈ I, ∀ w ∈ (L i).Content, w ∈ band D I lo hi k t := by
  let J := lo::hi::I
  have hloJ : lo ∈ J := List.mem_cons_self ..
  have hhiJ : hi ∈ J := List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have hlow : ∀ i ∈ J, ∀ x, (L lo).z x ≤ (L i).z x := by
    intro i hi' x
    rcases List.mem_cons.mp hi' with rfl|hi'
    · exact le_rfl
    rcases List.mem_cons.mp hi' with rfl|hi'
    · exact hlohi x
    · exact lower i hi' x
  have hupp : ∀ i ∈ J, ∀ x, (L i).z x ≤ (L hi).z x := by
    intro i hi' x
    rcases List.mem_cons.mp hi' with rfl|hi'
    · exact hlohi x
    rcases List.mem_cons.mp hi' with rfl|hi'
    · exact le_rfl
    · exact upper i hi' x
  obtain ⟨Q,he,hc,ht⟩ := GeoCode.join_band_realizes closed A letters p k per
    (fun j : {j // j ∈ J} => L j.val) ⟨lo,hloJ⟩ ⟨hi,hhiJ⟩
    (fun j => hlow j.val j.property) (fun j => hupp j.val j.property) t hB
  have he' : WalkCode.Path.points Q = GeoCode.band (PeriodWord.text D.1)
      (GeoCode.exit (exits D lo)) (GeoCode.exit (exits D hi)) D.1.length k t := by
    rw [hh.text_eq,hl.exit_eq,hh.exit_eq,hh.length_eq]; exact he
  obtain ⟨hr,hc',_,hv⟩ := filled_realized L h closed hp per he'
    (fun i hi' => ht ⟨i,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hi')⟩)
  refine ⟨hr,?_,hv⟩
  change cost (saturate D I _) ≤ _
  rw [hc',Nat.add_mul]
  omega

theorem attachBand_spec {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (L : ℕ → Layer V A p) {D : GroupData α} {I : List ℕ} {lo hi : ℕ}
    (h : ∀ i ∈ I, Represents D.1 (exits D i) (L i))
    (hl : Represents D.1 (exits D lo) (L lo)) (hh : Represents D.1 (exits D hi) (L hi))
    (lower : ∀ i ∈ I, ∀ x, (L lo).z x ≤ (L i).z x)
    (upper : ∀ i ∈ I, ∀ x, (L i).z x ≤ (L hi).z x)
    (hlohi : ∀ x, (L lo).z x ≤ (L hi).z x)
    (closed : SubstringClosed V) (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    (letters : ∀ x, [A x] ∈ V) (t : ℤ)
    (hB : (L hi).first t-(L lo).last t ≤ (I.length*p : ℕ))
    {P : Walk α} (hP : Runs V [] [] P) (hcP : ∀ w ∈ (L lo).Content, w ∈ P) :
    Runs V [] [] (attachBand D I lo hi P t) ∧ cost (attachBand D I lo hi P t) ≤ cost P+2*(I.length*p) ∧
      (∀ w ∈ P, w ∈ attachBand D I lo hi P t) ∧
      ∀ i ∈ I, ∀ w ∈ (L i).Content, w ∈ attachBand D I lo hi P t := by
  obtain ⟨hr,hc,hv⟩ := band_general L h hl hh lower upper hlohi closed hp per letters t hB
  have hm : textWord A t ((L lo).last t) ∈ P := hcP _ ⟨t,_,(L lo).first_le_last t,le_rfl,rfl⟩
  obtain ⟨hR,hc',hv'⟩ := splice_spec hP hr ⟨_,hm,List.mem_of_head? hr.2.1⟩
  refine ⟨hR,?_,fun w hw => (hv' w).mpr (Or.inl hw),fun i hi' w hw => (hv' w).mpr (Or.inr (hv i hi' w hw))⟩
  change cost (splice P _) ≤ _
  rw [hc']
  calc
    _ ≤ cost P+(I.length+I.length)*p := Nat.add_le_add_left hc _
    _ = _ := by ring

variable [Coded α]
@[fun_prop] theorem poly_attachBand : Poly (fun q : (GroupData α × List ℕ) × (ℕ × ℕ) × Walk α × ℤ =>
    attachBand q.1.1 q.1.2 q.2.1.1 q.2.1.2 q.2.2.1 q.2.2.2) := by
  unfold attachBand
  exact poly_splice.comp (f := fun q : (GroupData α × List ℕ) × (ℕ × ℕ) × Walk α × ℤ =>
    (q.2.2.1,band q.1.1 q.1.2 q.2.1.1 q.2.1.2 q.1.2.length q.2.2.2)) (by fun_prop)
end Superstring.LayerArray

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.ThreadArray
open BitCode Hierarchical
variable {α : Type} [Coded α] [DecidableEq α] [Inhabited α]

def representative (K : Code α) (i : ℕ) : ℕ :=
  first K.1.length (fun j => compatible K i j)

@[fun_prop] theorem poly_representative :
    Poly (fun q : Code α × ℕ => representative q.1 q.2) := by
  unfold representative first
  exact (BitCode.Poly.headD 0).comp (BitCode.Poly.filterFn
    (p := fun q : (Code α × ℕ) × ℕ => compatible q.1.1 q.1.2 q.2)
    (by fun_prop) (by fun_prop))

def groups (K : Code α) : List ℕ :=
  (List.range K.1.length).filter (fun i => equal (representative K i) i)

@[fun_prop] theorem poly_groups : Poly (fun K : Code α => groups K) := by
  unfold groups
  exact BitCode.Poly.filterFn
    (p := fun q : Code α × ℕ => equal (representative q.1 q.2) q.2)
    (by fun_prop) (by fun_prop)

omit [Coded α] in
theorem representative_spec {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (i : Fin K.1.length) :
    representative K i.val < K.1.length ∧
      compatible K i.val (representative K i.val) = true ∧
      ∀ j : Fin K.1.length, C.SameText i j → representative K i.val ≤ j.val := by
  obtain hh := first_spec (n := K.1.length) (P := fun j => compatible K i.val j)
    ⟨i.val,i.isLt,(compatible_eq h i i).mpr (C.textSetoid.refl i)⟩
  exact ⟨hh.1,hh.2.1,fun j hj => hh.2.2 j.val j.isLt ((compatible_eq h i j).mpr hj)⟩

omit [Coded α] in
def repFin {K : Code α} {V : Set (List α)} {C : Threading V (Fin K.1.length)}
    (h : Represents K C) (i : Fin K.1.length) : Fin K.1.length :=
  ⟨representative K i.val,(representative_spec h i).1⟩

omit [Coded α] in
theorem same_repFin {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (i : Fin K.1.length) :
    C.SameText i (repFin h i) :=
  (compatible_eq h i (repFin h i)).mp (representative_spec h i).2.1

omit [Coded α] in
theorem representative_eq_iff {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (i j : Fin K.1.length) :
    representative K i.val = representative K j.val ↔ C.SameText i j := by
  constructor
  · intro he
    have he' : repFin h i = repFin h j := Fin.ext he
    have hj := same_repFin h j
    rw [← he'] at hj
    exact C.textSetoid.trans (same_repFin h i) (C.textSetoid.symm hj)
  · intro hs
    apply le_antisymm
    · exact (representative_spec h i).2.2 (repFin h j)
        (C.textSetoid.trans hs (same_repFin h j))
    · exact (representative_spec h j).2.2 (repFin h i)
        (C.textSetoid.trans (C.textSetoid.symm hs) (same_repFin h i))

omit [Coded α] in
theorem representative_idem {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (i : Fin K.1.length) :
    representative K (representative K i.val) = representative K i.val :=
  ((representative_eq_iff h i (repFin h i)).mpr (same_repFin h i)).symm

abbrev Group (K : Code α) := {i : Fin K.1.length // representative K i.val = i.val}

omit [Coded α] in
def groupOf {K : Code α} {V : Set (List α)} {C : Threading V (Fin K.1.length)}
    (h : Represents K C) (i : Fin K.1.length) : Group K :=
  ⟨repFin h i,representative_idem h i⟩

omit [Coded α] in
theorem groupOf_eq_iff {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C)
    (i : Fin K.1.length) (g : Group K) :
    groupOf h i = g ↔ C.SameText i g.val := by
  constructor
  · intro he
    have hh := same_repFin h i
    have hh' := congrArg Subtype.val he
    rwa [← hh']
  · intro hs
    apply Subtype.ext
    apply Fin.ext
    exact ((representative_eq_iff h i g.val).mpr hs).trans g.property

omit [Coded α] in
theorem compatible_groupOf {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C)
    (i : Fin K.1.length) (g : Group K) :
    (∃ d : ℤ, ∀ x, C.text i x = C.text g.val (x+d)) ↔ groupOf h i = g := by
  rw [groupOf_eq_iff h]
  constructor
  · rintro ⟨d,hd⟩
    refine ⟨-d,fun x => ?_⟩
    simpa only [add_assoc, neg_add_cancel, add_zero] using hd (x + -d)
  · intro hi
    obtain ⟨d,hd⟩ := C.textSetoid.symm hi
    exact ⟨d,fun x => (hd x).symm⟩

noncomputable def collection {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (closed : SubstringClosed V) :
    LayerCollection V (Group K) where
  text := fun g => C.text g.val
  period := fun g => period K g.val.val
  size := fun g => Fintype.card (C.Aligned (C.text g.val))
  positive := fun g => (period_spec h g.val).1.positive
  periodic := fun g => (period_spec h g.val).1.periodic
  nonempty := fun g => Fintype.card_pos_iff.mpr ⟨⟨g.val,rfl⟩⟩
  layer := fun g j => C.layer closed (period_spec h g.val).1.periodic j
  ordered := fun g i j hij x => C.layers_ordered (C.text g.val) i j hij x
  different := by
    intro g d hgd c hh
    have hs : C.SameText g.val d.val := by
      refine ⟨-c,fun x => ?_⟩
      simpa only [add_assoc, neg_add_cancel, add_zero] using congrFun hh (x + -c)
    apply hgd
    apply Subtype.ext
    apply Fin.ext
    have he := (representative_eq_iff h g.val d.val).mpr hs
    simpa only [g.property, d.property] using he

noncomputable def phaseEquiv {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (g : Group K) :
    (Fin (period K g.val.val) × Fin (Fintype.card (C.Aligned (C.text g.val)))) ≃
      {i : Fin K.1.length // groupOf h i = g} :=
  (Equiv.prodCongr (Equiv.refl _) (C.enumerate (C.text g.val))).trans
    ((C.phaseEquiv (period_spec h g.val).1).trans
      (Equiv.subtypeEquivRight (fun i => compatible_groupOf h i g)))

noncomputable def allPhaseEquiv {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) :
    (Σ g : Group K, Fin (period K g.val.val) ×
      Fin (Fintype.card (C.Aligned (C.text g.val)))) ≃ Fin K.1.length :=
  (Equiv.sigmaCongrRight (phaseEquiv h)).trans (Equiv.sigmaFiberEquiv (groupOf h))

omit [Coded α] in
theorem collection_budget {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (closed : SubstringClosed V) :
    ∑ g : Group K, (collection h closed).period g * (collection h closed).size g =
      K.1.length := by
  classical
  have hh := Fintype.card_congr (allPhaseEquiv h)
  simpa only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, collection] using hh

omit [Coded α] in
theorem allPhaseEquiv_value {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (g : Group K)
    (r : Fin (period K g.val.val)) (j : Fin (Fintype.card (C.Aligned (C.text g.val)))) :
    allPhaseEquiv h ⟨g,r,j⟩ = (C.next ^ (r.val : ℤ)) (C.enumerate (C.text g.val) j).val := rfl

omit [Coded α] in
theorem phase_prefix_count {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (g : Group K)
    (r : Fin (period K g.val.val)) (s : List α) :
    (Finset.univ.filter (fun j => s <+: textWord (C.text g.val) r.val
      (C.sortedExit (C.text g.val) j r.val))).card =
      (Finset.univ.filter (fun j => s <+: C.word (allPhaseEquiv h ⟨g,r,j⟩))).card := by
  classical
  change (Finset.univ.filter (fun j => s <+: textWord (C.text g.val) r.val
    (OrderStats.order (C.exits (C.text g.val) r.val) j))).card = _
  rw [OrderStats.card_filter_order (C.exits (C.text g.val) r.val)
    (fun e => s <+: textWord (C.text g.val) r.val e)]
  congr 1
  apply Finset.filter_congr
  intro j _
  have he := C.translated_word (C.enumerate (C.text g.val) j).val (r.val : ℤ)
  rw [(C.enumerate (C.text g.val) j).property] at he
  rw [allPhaseEquiv_value, he]
  rfl

omit [Coded α] in
theorem collection_histogram {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (closed : SubstringClosed V)
    (s : List α) :
    Fintype.card (Family.Occurrence (collection h closed).layerAt s) =
      (Finset.univ.filter (fun i => s <+: C.word i)).card := by
  classical
  rw [Fintype.card_eq_nat_card, Nat.card_sigma]
  simp only [Fintype.sum_sigma]
  simp only [← Fintype.card_eq_nat_card, Layer.Occurrence, Fintype.card_subtype,
    Finset.card_filter]
  rw [← (allPhaseEquiv h).sum_comp (fun i => if s <+: C.word i then 1 else 0)]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro g _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  have hp := phase_prefix_count h g r s
  simp only [Finset.card_filter] at hp
  simp only [Layer.records_iff_prefix, collection, LayerCollection.layerAt,
    Threading.layer]
  convert hp using 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1

end Superstring.ThreadArray


namespace Superstring.Hierarchical.LayerCollection
open Counts
variable {α G : Type} [Fintype G] {V : Set (List α)} (C : LayerCollection V G)

omit [Fintype G] in
theorem eq_of_alignment (g h : G) (r t : ℤ)
    (halign : ∀ x, C.text h (x+r) = C.text g (x+t)) : h = g := by
  by_contra hne
  apply C.different h g hne (t-r)
  funext x
  convert halign (x-r) using 1 <;> congr 1 <;> omega

abbrev AlignedOccurrence (g : G) (t : ℤ) (s : List α) :=
  {o : Family.Occurrence C.layerAt s // ∀ x : ℤ, C.text o.1.1 (x+o.2.val.val) = C.text g (x+t)}

noncomputable instance (g : G) (t : ℤ) (s : List α) : Fintype (C.AlignedOccurrence g t s) := by
  classical
  exact inferInstanceAs (Fintype {o : Family.Occurrence C.layerAt s //
    ∀ x : ℤ, C.text o.1.1 (x+o.2.val.val) = C.text g (x+t)})

noncomputable def qualifyingLayer (prim : ∀ g, Primitive (C.text g) (C.period g))
    (g : G) (t : ℤ) (s : List α) (o : C.AlignedOccurrence g t s) :
    {j : Fin (C.size g) // t + s.length ≤ (C.layer g j).last t} := by
  rcases o with ⟨⟨⟨h,j⟩,r⟩,ha⟩
  have hh := C.eq_of_alignment g h r.val.val t ha
  subst h
  exact ⟨j, ((C.layer g j).records_at_alignment (prim g) r.property ha).2⟩

omit [Fintype G] in
theorem qualifyingLayer_injective (prim : ∀ g, Primitive (C.text g) (C.period g))
    (g : G) (t : ℤ) (s : List α) : Function.Injective (C.qualifyingLayer prim g t s) := by
  rintro ⟨⟨⟨h,j⟩,r⟩,hr⟩ ⟨⟨⟨h',j'⟩,r'⟩,hr'⟩ he
  have hh := C.eq_of_alignment g h r.val.val t hr
  have hh' := C.eq_of_alignment g h' r'.val.val t hr'
  subst h; subst h'
  have hj : j = j' := congrArg Subtype.val he
  subst j'
  have hphase : r.val = r'.val := by
    apply Fin.ext
    have hh := (prim g).alignment_unique
      (by omega : 0 ≤ (r.val.val : ℤ)) (by exact_mod_cast r.val.isLt)
      (by omega : 0 ≤ (r'.val.val : ℤ)) (by exact_mod_cast r'.val.isLt)
      (fun x => (hr x).trans (hr' x).symm)
    omega
  have hre : r = r' := Subtype.ext hphase
  subst r'
  rfl

theorem aligned_card_le_qualifying (prim : ∀ g, Primitive (C.text g) (C.period g))
    (g : G) (t : ℤ) (s : List α) :
    Nat.card (C.AlignedOccurrence g t s) ≤
      Nat.card {j : Fin (C.size g) // t + s.length ≤ (C.layer g j).last t} := by
  classical
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_le_of_injective (C.qualifyingLayer prim g t s)
      (C.qualifyingLayer_injective prim g t s)

variable [DecidableEq α] [Inhabited α]

 theorem blocking_count (D : Data α)
    (hist : ∀ s, s ≠ [] → Fintype.card (Family.Occurrence C.layerAt s) = D.count s)
    (A : ℤ → α) (s : List α) :
    blocking D.vertices A s (fun r => Fintype.card (Family.Occurrence C.layerAt r)) =
      blocking D.vertices A s D.count := by
  apply blocking_congr
  intro r _hr hlen
  apply hist r
  intro he
  simp only [he, List.length_nil] at hlen
  omega

theorem period_forces_matching (D : Data α) (hD : D.WellFormed)
    (hvtx : V = (D.vertices : Set (List α)))
    (hist : ∀ s, s ≠ [] → Fintype.card (Family.Occurrence C.layerAt s) = D.count s)
    {A : ℤ → α} {w v : List α} {p k : ℕ}
    (hp : 0 < p) (hk : 0 < k) (hper : Function.Periodic A (p : ℤ))
    (hw : w ∈ D.vertices) (hwne : w ≠ []) (hv : v ∈ D.vertices)
    (hmv : Matches A v) (hmw : Matches A w)
    (hlen : w.length + k * p = v.length)
    (ov : Family.Occurrence (C.layerAt) v)
    (halign : ∀ x : ℤ, C.text ov.1.1 (x + ov.2.val.val) = A x)
    (hfew : Nat.card {o : Family.Occurrence (C.layerAt) w //
      ∀ x : ℤ, C.text o.1.1 (x + o.2.val.val) = A x} ≤ k) :
    ∃ o : Family.Occurrence (C.layerAt) w,
      (¬ ∀ x : ℤ, C.text o.1.1 (x + o.2.val.val) = A x) ∧
      ∃ a b : ℤ, a ≤ o.2.val.val ∧ (o.2.val.val : ℤ) + w.length ≤ b ∧
        (C.layerAt o.1).first a ≤ b ∧
        b ≤ (C.layerAt o.1).last a ∧
        AgreeOn (C.text o.1.1) (fun x => A (x - o.2.val.val)) a b := by
  have hvne : v ≠ [] := by
    intro he
    have hwpos := List.length_pos_iff.mpr hwne
    simp only [he, List.length_nil] at hlen
    omega
  have pos := fun i : C.Id =>
    (C.positive i.1)
  have per := fun i : C.Id =>
    (C.periodic i.1)
  have ht := Family.blocking_lt_of_aligned (C.layerAt)
    pos per D.vertices ov halign
  rw [C.blocking_count D hist, hist v hvne] at ht
  have hexcess := D.period_rule hp hk hper hw hwne hv hmv hmw hlen ht
  apply Family.matching_different (C.layerAt)
    pos per D.vertices hvtx (by simpa only [hvtx] using hD.closed) hmw k _ hfew
  rw [C.blocking_count D hist, hist w hwne]
  omega


theorem hard_case_record (D : Data α) (hD : D.WellFormed)
    (hvtx : V = (D.vertices : Set (List α)))
    (hist : ∀ s, s ≠ [] → Fintype.card (Family.Occurrence C.layerAt s) = D.count s)
    (prim : ∀ g, Primitive (C.text g) (C.period g))
    (g : G) (j : Fin (C.size g)) (t : ℤ) (k : ℕ) (hk : 0 < k)
    (hhard : t + (k * C.period g : ℕ) < (C.layer g j).first t)
    (hfew : (Processing.qualifying (fun l => (C.layer g l).last t)
      ((C.layer g j).first t) (C.period g) k).card ≤ k) :
    ∃ i : C.Id, ∃ R : (C.layerAt i).Record (C.text g),
      R.start ≤ t ∧ (C.layer g j).first t - (k * C.period g : ℕ) ≤ R.stop ∧
      C.text g ≠ (fun x => C.text i.1 (x+R.offset)) ∧
      R.stop - R.start < C.period g + C.period i.1 ∧
      (i.1 = g → R.stop - R.start < C.period g) := by
  classical
  let A := C.text g
  let p := C.period g
  let L := C.layerAt ⟨g, j⟩
  let H := L.first t
  let v := textWord A t H
  let w := textWord A t (H - (k * p : ℕ))
  have hp : 0 < p := (prim g).positive
  have per : Function.Periodic A (p : ℤ) := (prim g).periodic
  change t + (k * p : ℕ) < H at hhard
  have hv : v ∈ D.vertices := by
    have hh := L.first_actual t
    exact (Set.ext_iff.mp hvtx v).mp hh
  have hw : w ∈ D.vertices := hD.closed hv (textWord_infix A le_rfl
    (by omega : t ≤ H - (k * p : ℕ)) (by omega))
  have hwlen : t + (w.length : ℤ) = H - (k * p : ℕ) := by
    dsimp only [w]
    rw [length_textWord]
    omega
  have hvlen : t + (v.length : ℤ) = H := by
    dsimp only [v]
    rw [length_textWord]
    omega
  have hwne : w ≠ [] := by
    intro he
    simp only [he, List.length_nil, Nat.cast_zero, add_zero] at hwlen
    omega
  have hlen : w.length + k * p = v.length := by omega
  have hvrec : L.Records v t := ⟨TextOccurs.word A t H, by
    rw [hvlen]
    exact L.first_le_last t⟩
  let ov : Family.Occurrence (C.layerAt) v :=
    ⟨⟨g, j⟩, L.normalize hp per hvrec⟩
  have halign : ∀ x, C.text ov.1.1 (x + ov.2.val.val) = A (x + t) :=
    L.normalize_alignment hp per hvrec
  have hmv : Matches (fun x => A (x + t)) v := by
    intro i
    simpa only [add_comm] using (TextOccurs.word A t H i)
  have hmw : Matches (fun x => A (x + t)) w := by
    intro i
    simpa only [add_comm] using (TextOccurs.word A t (H - (k * p : ℕ)) i)
  have hper : Function.Periodic (fun x => A (x + t)) (p : ℤ) := by
    intro x
    simpa only [add_right_comm] using per (x + t)
  have hcard : Nat.card {l : Fin (C.size g) //
      t + w.length ≤ (C.layer g l).last t} ≤ k := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    change (Processing.qualifying (fun l => (C.layer g l).last t) H p k).card ≤ k at hfew
    simpa only [hwlen, Processing.qualifying] using hfew
  have hAligned : Nat.card (C.AlignedOccurrence g t w) ≤ k :=
    (C.aligned_card_le_qualifying prim g t w).trans hcard
  obtain ⟨o, hdiff, a, b, har, hrb, hfa, hbl, hagree⟩ :=
    C.period_forces_matching D hD hvtx hist hp hk hper hw hwne hv hmv hmw hlen ov halign hAligned
  let c : ℤ := o.2.val.val - t
  let R : (C.layerAt o.1).Record A := {
    offset := c
    start := a - c
    stop := b - c
    first_le := by simpa only [sub_add_cancel] using hfa
    le_last := by simpa only [sub_add_cancel] using hbl
    agree := by
      intro x hax hxb
      have hh := hagree (x + c) (by omega) (by omega)
      change C.text o.1.1 (x + c) = A (x + c - o.2.val.val + t) at hh
      have he : x + c - (o.2.val.val : ℤ) + t = x := by dsimp only [c]; omega
      rw [he] at hh
      exact hh.symm }
  have hd : A ≠ fun x => C.text o.1.1 (x + R.offset) := by
    intro he
    apply hdiff
    intro x
    have hh := congrFun he (x + t)
    change A (x + t) = C.text o.1.1 (x + t + c) at hh
    have hc : x + t + c = x + (o.2.val.val : ℤ) := by dsimp only [c]; omega
    rw [hc] at hh
    exact hh.symm
  refine ⟨o.1, R, ?_, ?_, hd,
    R.length_lt hp (prim o.1.1).positive per
      (prim o.1.1).periodic hd, ?_⟩
  · change a - c ≤ t
    dsimp only [c]
    omega
  · change H - (k * p : ℕ) ≤ b - c
    dsimp only [c]
    omega
  · intro he
    apply R.same_period_length_lt hp per _ hd
    simpa only [he] using (prim o.1.1).periodic


theorem recordSupply_of_histogram (D : Data α) (hD : D.WellFormed)
    (hvtx : V = (D.vertices : Set (List α)))
    (hist : ∀ s, s ≠ [] → Fintype.card (Family.Occurrence C.layerAt s) = D.count s)
    (prim : ∀ g, Primitive (C.text g) (C.period g)) : C.RecordSupply := by
  intro g j t k hk hh hs
  obtain ⟨d,R,ha,hb,hd,_⟩ := C.hard_case_record D hD hvtx hist prim g j t k hk hh hs
  exact ⟨d,R,ha,hb,hd⟩

end Superstring.Hierarchical.LayerCollection


namespace Superstring.Hierarchical.Layer.Record
variable {α : Type} {V : Set (List α)} {A B : ℤ → α} {q : ℕ} {D : Layer V B q}

/-- Only the period residue of a recipient offset is stored. -/
def normalize (R : D.Record A) (per : Function.Periodic B (q : ℤ)) : D.Record A where
  offset := R.offset % q
  start := R.start
  stop := R.stop
  first_le := by
    have he : R.start + R.offset = R.start + R.offset % q + (R.offset / q) * q := by have := Int.emod_add_ediv_mul R.offset (q : ℤ); omega
    have hh := R.first_le
    rw [he,D.first_shift_int] at hh
    have := Int.emod_add_ediv_mul R.offset (q : ℤ)
    omega
  le_last := by
    have he : R.start + R.offset = R.start + R.offset % q + (R.offset / q) * q := by have := Int.emod_add_ediv_mul R.offset (q : ℤ); omega
    have hh := R.le_last
    change R.stop + R.offset ≤ D.z (R.start + R.offset) at hh
    rw [he,D.shift_int] at hh
    change R.stop + R.offset % q ≤ D.z (R.start + R.offset % q)
    have := Int.emod_add_ediv_mul R.offset (q : ℤ)
    omega
  agree := by
    intro x hx hy
    have he : B (x + R.offset % q) = B (x + R.offset) := by
      have ht := per.int_mul (R.offset / q) (x + R.offset % q)
      simp only [Int.cast_id] at ht
      convert ht.symm using 1
      congr 1
      have := Int.emod_add_ediv_mul R.offset (q : ℤ)
      omega
    exact (R.agree x hx hy).trans he.symm

theorem normalize_text (R : D.Record A) (per : Function.Periodic B (q : ℤ)) :
    (fun x => B (x + (R.normalize per).offset)) = fun x => B (x + R.offset) := by
  funext x
  have ht := per.int_mul (R.offset / q) (x + R.offset % q)
  simp only [Int.cast_id] at ht
  change B (x + R.offset % q) = B (x + R.offset)
  convert ht.symm using 1
  congr 1
  have := Int.emod_add_ediv_mul R.offset (q : ℤ)
  omega

theorem bounds (R : D.Record A) {t : ℤ} {M : ℕ} (ha : R.start ≤ t) (hb : t < R.stop)
    (len : ∀ w ∈ V, w.length ≤ M) :
    t - M ≤ R.start ∧ R.stop ≤ t + M := by
  have hm := len _ R.word_mem
  rw [length_textWord] at hm
  have hs := R.start_le_stop
  omega
end Superstring.Hierarchical.Layer.Record

namespace Superstring.RecordCode
open BitCode Hierarchical LayerArray
variable {α : Type} [Inhabited α] [DecidableEq α]

abbrev Code := ℤ × ℤ × ℤ
def offset (R : Code) : ℤ := R.1
def start (R : Code) : ℤ := R.2.1
def stop (R : Code) : ℤ := R.2.2

def check (U T : List α) (Z : List ℕ) (R : Code) : Bool :=
  decide (GeoCode.exit Z (start R + offset R - 1) ≤ stop R + offset R) &&
  decide (stop R + offset R ≤ GeoCode.exit Z (start R + offset R)) &&
  decide (start R ≤ stop R) &&
  equal (PeriodWord.window U (start R) (stop R))
    (PeriodWord.window T (start R + offset R) (stop R + offset R))

 theorem check_record {V : Set (List α)} {A B : ℤ → α} {q : ℕ}
    {S T : List α} {Z : List ℕ} {L : Layer V B q}
    (hS : PeriodWord.text S = A) (hL : Represents T Z L) (R : L.Record A) :
    check S T Z (R.offset,R.start,R.stop) = true := by
  simp only [check,offset,start,stop,PeriodWord.window_eq,hS,hL.text_eq,hL.exit_eq]
  have hh := R.word_eq
  simp only [Bool.and_eq_true,BitCode.equal,decide_eq_true_eq]
  exact ⟨⟨⟨R.first_le,R.le_last⟩,decide_eq_true R.start_le_stop⟩,hh⟩

variable [Coded α]
@[fun_prop] theorem poly_check : Poly (fun q : (List α × List α × List ℕ) × Code =>
    check q.1.1 q.1.2.1 q.1.2.2 q.2) := by
  unfold check start stop offset
  fun_prop
end Superstring.RecordCode

namespace Superstring.RecordCode
open BitCode Hierarchical LayerArray
variable {α : Type} [Inhabited α] [DecidableEq α]

omit [Inhabited α] [DecidableEq α] in
theorem agree_of_word_eq {A B : ℤ → α} {a b : ℤ}
    (he : textWord A a b = textWord B a b) : AgreeOn A B a b := by
  intro x hx hb
  have hi : (x-a).toNat < (b-a).toNat := by omega
  have ha : a + ((x-a).toNat : ℤ) = x := by omega
  have ht := congrArg (fun w : List α => w[(x-a).toNat]?) he
  simp only [textWord,List.getElem?_ofFn,hi,↓reduceDIte,Option.some.injEq] at ht
  simpa only [ha] using ht

def checkedRecord {V : Set (List α)} {A B : ℤ → α} {q : ℕ}
    {S T : List α} {Z : List ℕ} {L : Layer V B q}
    (hS : PeriodWord.text S = A) (hL : Represents T Z L) (R : Code)
    (h : check S T Z R = true) : L.Record A := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq,BitCode.equal,PeriodWord.window_eq,
    hS,hL.text_eq,hL.exit_eq] at h
  exact ⟨offset R,start R,stop R,h.1.1.1,h.1.1.2,
    agree_of_word_eq (h.2.trans (textWord_reindex B (offset R) (start R) (stop R)).symm)⟩

def pool (q M : ℕ) (t : ℤ) : List Code :=
  ((List.range q).product ((List.range (M+1)).product (List.range M))).map
    (fun r => ((r.1 : ℤ),t-M+r.2.1,t+1+r.2.2))

theorem mem_pool {q M : ℕ} {t : ℤ} {R : Code}
    (ho : 0 ≤ offset R) (hoq : offset R < q)
    (ha : t-M ≤ start R) (hat : start R ≤ t)
    (hb : t < stop R) (hbt : stop R ≤ t+M) : R ∈ pool q M t := by
  apply List.mem_map.mpr
  refine ⟨((offset R).toNat,((start R-t+M).toNat,(stop R-t-1).toNat)),?_,?_⟩
  · exact List.mem_product.mpr ⟨List.mem_range.mpr (by omega),
      List.mem_product.mpr ⟨List.mem_range.mpr (by omega),List.mem_range.mpr (by omega)⟩⟩
  · rcases R with ⟨o,a,b⟩
    simp only [offset,start,stop] at *
    apply Prod.ext
    · simp only [Int.toNat_of_nonneg ho]
    · apply Prod.ext
      · change t - M + ((a-t+M).toNat : ℤ) = a
        omega
      · change t + 1 + ((b-t-1).toNat : ℤ) = b
        omega

omit [Inhabited α] [DecidableEq α] in
theorem normalized_mem_pool {V : Set (List α)} {A B : ℤ → α} {q : ℕ}
    {L : Layer V B q} (hq : 0 < q) (per : Function.Periodic B (q : ℤ))
    (R : L.Record A) {t : ℤ} {M : ℕ} (ha : R.start ≤ t) (hb : t < R.stop)
    (len : ∀ w ∈ V, w.length ≤ M) :
    ((R.normalize per).offset,R.start,R.stop) ∈ pool q M t := by
  obtain ⟨hlo,hhi⟩ := R.bounds ha hb len
  exact mem_pool (Int.emod_nonneg _ (by omega)) (Int.emod_lt_of_pos _ (by omega))
    hlo ha hb hhi

variable [Coded α]
@[fun_prop] theorem poly_pool : Poly (fun q : ℕ × ℕ × ℤ => pool q.1 q.2.1 q.2.2) := by
  unfold pool
  exact BitCode.Poly.mapFn
    (f := fun q : (ℕ × ℕ × ℤ) × (ℕ × ℕ × ℕ) =>
      ((q.2.1 : ℤ),q.1.2.2-q.1.2.1+q.2.2.1,q.1.2.2+1+q.2.2.2))
    (by fun_prop) (by fun_prop)
end Superstring.RecordCode

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.BitCode
variable {α : Type} [Inhabited α] [DecidableEq α]
def lexLT (lt : α × α → Bool) (v w : List α) : Bool :=
  (equal v (w.take v.length) && less v.length w.length) ||
    (List.range (min v.length w.length)).any (fun i =>
      equal (v.take i) (w.take i) && lt (v[i]?.getD default,w[i]?.getD default))

omit [Inhabited α] [DecidableEq α] in
theorem take_eq_iff {v w : List α} {i : ℕ} (hv : i ≤ v.length) (hw : i ≤ w.length) :
    v.take i = w.take i ↔ ∀ j, (hj : j < i) → v[j]'(by omega) = w[j]'(by omega) := by
  constructor
  · intro he j hj
    have hh := congrArg (fun u => u[j]?) he
    simpa only [List.getElem?_take,ite_eq_left hj,List.getElem?_eq_getElem (by omega : j<v.length),
      List.getElem?_eq_getElem (by omega : j<w.length),Option.some.injEq] using hh
  · intro he
    apply List.ext_getElem
    · simp [List.length_take, Nat.min_eq_left hv,Nat.min_eq_left hw]
    · intro j hj hj'
      have hji : j < i := lt_of_lt_of_le hj (List.length_take_le _ _)
      simp only [List.getElem_take,he j hji]

theorem lexLT_eq [LinearOrder α] (lt : α × α → Bool)
    (hlt : ∀ x, lt x = decide (x.1<x.2)) (v w : List α) :
    lexLT lt v w = true ↔ v<w := by
  rw [List.lt_iff_exists]
  simp only [lexLT,Bool.or_eq_true,Bool.and_eq_true,equal,less,decide_eq_true_eq,
    List.any_eq_true,List.mem_range]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨i,hi,he,hlt'⟩
    have hv : i<v.length := lt_of_lt_of_le hi (Nat.min_le_left ..)
    have hw : i<w.length := lt_of_lt_of_le hi (Nat.min_le_right ..)
    refine ⟨i,hv,hw,(take_eq_iff hv.le hw.le).mp he,?_⟩
    simpa only [hlt,List.getElem?_eq_getElem hv,List.getElem?_eq_getElem hw,
      Option.getD_some,decide_eq_true_eq] using hlt'
  · rintro ⟨i,hv,hw,he,hl⟩
    refine ⟨i,lt_min hv hw,(take_eq_iff hv.le hw.le).mpr he,?_⟩
    simpa only [hlt,List.getElem?_eq_getElem hv,List.getElem?_eq_getElem hw,
      Option.getD_some,decide_eq_true_eq] using hl

variable [Coded α]
@[fun_prop] theorem poly_lexLT {lt : α × α → Bool} (hlt : Poly lt) :
    Poly (fun q : List α × List α => lexLT lt q.1 q.2) := by
  unfold lexLT
  apply Poly.or.comp (f := fun q : List α × List α =>
    (equal q.1 (q.2.take q.1.length) && less q.1.length q.2.length,
    (List.range (min q.1.length q.2.length)).any (fun i =>
      equal (q.1.take i) (q.2.take i) && lt (q.1[i]?.getD default,q.2[i]?.getD default))))
  apply Poly.pair (by fun_prop)
  apply Poly.anyFn (p := fun q : (List α × List α) × ℕ =>
    equal (q.1.1.take q.2) (q.1.2.take q.2) && lt (q.1.1[q.2]?.getD default,q.1.2[q.2]?.getD default))
  · apply Poly.and.comp (f := fun q : (List α × List α) × ℕ =>
      (equal (q.1.1.take q.2) (q.1.2.take q.2),lt (q.1.1[q.2]?.getD default,q.1.2[q.2]?.getD default)))
    apply Poly.pair (by fun_prop)
    apply hlt.comp
    exact ((Poly.getD default).comp (f := fun q : (List α × List α) × ℕ => (q.1.1,q.2)) (by fun_prop)).pair
      ((Poly.getD default).comp (f := fun q : (List α × List α) × ℕ => (q.1.2,q.2)) (by fun_prop))
  · fun_prop

@[fun_prop] theorem Poly.ltBool : Poly (fun q : Bool × Bool => decide (q.1 < q.2)) := by
  have h : Poly (fun q : Bool × Bool => !q.1 && q.2) := by fun_prop
  convert h using 1
  funext q
  rcases q with ⟨a,b⟩
  cases a <;> cases b <;> rfl

@[fun_prop] theorem Poly.ltList [LinearOrder α] (h : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (fun q : List α × List α => decide (q.1<q.2)) := by
  convert poly_lexLT h using 1
  funext q
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using (lexLT_eq _ (fun _ => rfl) q.1 q.2).symm

@[fun_prop] theorem Poly.leList [LinearOrder α] (h : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (fun q : List α × List α => decide (q.1≤q.2)) := by
  have H := Poly.not.comp ((Poly.ltList h).comp (Poly.snd.pair Poly.fst))
  convert H using 1
  funext q
  simp only [Function.comp_apply,← decide_not,not_lt]
end Superstring.BitCode


namespace Superstring.RotationCode
open BitCode Hierarchical
variable {α : Type} [Inhabited α] [LinearOrder α]

omit [Inhabited α] [LinearOrder α] in
theorem forward_mod {A : ℤ → α} {p : ℕ} (per : Function.Periodic A (p:ℤ)) (t : ℤ) (n : ℕ) :
    forward A t (n % p) = forward A t n := by
  have hh := periodic_emod (fun x => A (t+x)) (p:ℤ)
    (by intro x; simpa only [← add_assoc] using per (t+x)) (n:ℤ)
  simpa only [forward, Pi.toLex_apply, Int.natCast_emod] using hh

omit [Inhabited α] in
theorem window_lt_iff {A : ℤ → α} {p : ℕ} (hp : 0 < p)
    (per : Function.Periodic A (p:ℤ)) (a b : ℤ) :
    textWord A a (a+p) < textWord A b (b+p) ↔ forward A a < forward A b := by
  have hlen (t : ℤ) : (textWord A t (t+p)).length = p := by simp [length_textWord]
  rw [List.lt_iff_exists]
  constructor
  · rintro (⟨_,hh⟩|⟨i,hi,hj,he,hl⟩)
    · simp only [hlen,lt_self_iff_false] at hh
    · refine ⟨i,?_,?_⟩
      · intro j hj
        have hh := he j hj
        simpa only [textWord,List.getElem_ofFn,forward,Pi.toLex_apply] using hh
      · simpa only [textWord,List.getElem_ofFn,forward,Pi.toLex_apply] using hl
  · rintro ⟨i,he,hl⟩
    have hi : i < p := by
      by_contra hn
      have hm : i%p < i := lt_of_lt_of_le (Nat.mod_lt i hp) (by omega)
      have hh := he (i%p) hm
      rw [forward_mod per,forward_mod per] at hh
      exact (ne_of_lt hl) hh
    right
    refine ⟨i,by simpa only [hlen] using hi,by simpa only [hlen] using hi,?_,?_⟩
    · intro j hj
      simpa only [textWord,List.getElem_ofFn,forward,Pi.toLex_apply] using he j hj
    · simpa only [textWord,List.getElem_ofFn,forward,Pi.toLex_apply] using hl

omit [Inhabited α] in
theorem window_le_iff {A : ℤ → α} {p : ℕ} (hp : 0 < p)
    (per : Function.Periodic A (p:ℤ)) (a b : ℤ) :
    textWord A a (a+p) ≤ textWord A b (b+p) ↔ forward A a ≤ forward A b := by
  rw [← not_lt,← not_lt,window_lt_iff hp per]
  rfl

def phase (U : List α) : ℕ :=
  ThreadArray.first U.length (fun i => (List.range U.length).all (fun j =>
    decide (PeriodWord.window U j ((j:ℤ)+U.length) ≤ PeriodWord.window U i ((i:ℤ)+U.length))))

theorem phase_spec (U : List α) (hp : 0 < U.length) :
    phase U < U.length ∧ ∀ x, forward (PeriodWord.text U) x ≤ forward (PeriodWord.text U) (phase U) := by
  obtain ⟨t,ht0,htp,ht⟩ := exists_greatest_rotation (PeriodWord.text U) U.length hp (PeriodWord.periodic U)
  have hpref (x y : ℤ) : PeriodWord.window U x (x+U.length) ≤ PeriodWord.window U y (y+U.length) ↔
      forward (PeriodWord.text U) x ≤ forward (PeriodWord.text U) y := by
    simp only [PeriodWord.window_eq,window_le_iff hp (PeriodWord.periodic U)]
  have hex : ∃ i < U.length, (List.range U.length).all (fun j =>
      decide (PeriodWord.window U j ((j:ℤ)+U.length) ≤ PeriodWord.window U i ((i:ℤ)+U.length))) = true := by
    refine ⟨t.toNat,by omega,List.all_eq_true.mpr (fun j _ => ?_)⟩
    apply decide_eq_true
    apply (hpref _ _).mpr
    simpa only [Int.toNat_of_nonneg ht0] using ht j
  have hs := ThreadArray.first_spec hex
  refine ⟨hs.1,?_⟩
  intro x
  let r := (x % (U.length:ℤ)).toNat
  have hrlt : r < U.length := by
    have := Int.emod_nonneg x (show (U.length:ℤ) ≠ 0 by omega)
    have := Int.emod_lt_of_pos x (show (0:ℤ) < U.length by omega)
    dsimp only [r]; omega
  have hle := List.all_eq_true.mp hs.2.1 r (List.mem_range.mpr hrlt)
  have hh := (hpref _ _).mp (of_decide_eq_true hle)
  have he : forward (PeriodWord.text U) x = forward (PeriodWord.text U) r := by
    apply congrArg toLex
    funext n
    have hr : (r:ℤ) = x % (U.length:ℤ) := by
      exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
    have hdiv := Int.emod_add_ediv_mul x (U.length:ℤ)
    have hh := (PeriodWord.periodic U).sub_int_mul_eq (x := x+n) (x/U.length)
    simp only [Int.cast_id] at hh
    have hx : x+n-(x/(U.length:ℤ))*U.length = (r:ℤ)+n := by omega
    rw [hx] at hh
    exact hh.symm
  rw [he]
  exact hh

variable [Coded α]
@[fun_prop] theorem poly_phase (hlt : Poly (fun q : α × α => decide (q.1<q.2))) : Poly (phase (α := α)) := by
  have hle := BitCode.Poly.leList hlt
  unfold phase ThreadArray.first
  apply (BitCode.Poly.headD 0).comp
  apply BitCode.Poly.filterFn
    (p := fun t : List α × ℕ => (List.range t.1.length).all (fun j =>
      decide (PeriodWord.window t.1 j ((j:ℤ)+t.1.length) ≤ PeriodWord.window t.1 t.2 ((t.2:ℤ)+t.1.length))))
  · apply BitCode.Poly.allFn
      (p := fun t : (List α × ℕ) × ℕ =>
        decide (PeriodWord.window t.1.1 t.2 ((t.2:ℤ)+t.1.1.length) ≤
          PeriodWord.window t.1.1 t.1.2 ((t.1.2:ℤ)+t.1.1.length)))
    · exact hle.comp (f := fun t : (List α × ℕ) × ℕ =>
        (PeriodWord.window t.1.1 t.2 ((t.2:ℤ)+t.1.1.length),
          PeriodWord.window t.1.1 t.1.2 ((t.1.2:ℤ)+t.1.1.length))) (by fun_prop)
    · fun_prop
  · fun_prop
end Superstring.RotationCode


namespace Superstring.RotationCode
open BitCode Hierarchical
variable {α : Type} [LinearOrder α]
theorem maximal_unique {A : ℤ → α} {p : ℕ} (h : Primitive A p)
    {a b : ℤ} (ha : 0 ≤ a) (hap : a < p) (hb : 0 ≤ b) (hbp : b < p)
    (hA : ∀ x, forward A x ≤ forward A a) (hB : ∀ x, forward A x ≤ forward A b) : a = b := by
  have he : forward A a = forward A b := le_antisymm (hB a) (hA b)
  have he' : (fun x => A (x+a)) = (fun x => A (x+b)) := by
    apply periodic_eq_of_forward_eq _ _ p p h.positive h.positive
      (fun x => by simpa only [add_right_comm] using h.periodic (x+a))
      (fun x => by simpa only [add_right_comm] using h.periodic (x+b)) 0
    simpa only [forward_shift,zero_add] using he
  exact h.alignment_unique ha hap hb hbp (congrFun he')

variable [Inhabited α]
theorem phase_eq_distinguished {G : Type} {V : Set (List α)}
    (C : LayerCollection V G) (g : G) (hprim : Primitive (C.text g) (C.period g))
    (U : List α) (hlen : U.length = C.period g) (ht : PeriodWord.text U = C.text g) :
    (phase U : ℤ) = C.distinguished g := by
  obtain ⟨hp,hm⟩ := phase_spec U (by rw [hlen]; exact C.positive g)
  have hs := (exists_greatest_rotation (C.text g) (C.period g) (C.positive g) (C.periodic g)).choose_spec
  apply maximal_unique hprim (by omega) (by omega) hs.1 hs.2.1
  · simpa only [ht] using hm
  · exact C.distinguished_max g
end Superstring.RotationCode

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.ThreadArray
open BitCode Hierarchical LayerArray
variable {α : Type} [Coded α] [DecidableEq α] [Inhabited α]

def data (K : Code α) (g : ℕ) : GroupData α :=
  (layerWord K g,(List.range (aligned K g).length).map (layerExits K g))

@[fun_prop] theorem poly_data : Poly (fun q : Code α × ℕ => data q.1 q.2) := by
  have hm : Poly (fun q : Code α × ℕ => (List.range (aligned q.1 q.2).length).map (layerExits q.1 q.2)) :=
    BitCode.Poly.mapFn (f := fun q : (Code α × ℕ) × ℕ => layerExits q.1.1 q.1.2 q.2) (by fun_prop) (by fun_prop)
  unfold data
  fun_prop

theorem data_represents {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (closed : SubstringClosed V)
    (g : Fin K.1.length) (j : Fin (Fintype.card (C.Aligned (C.text g)))) :
    LayerArray.Represents (data K g.val).1 (exits (data K g.val) j.val)
      (C.layer closed (period_spec h g).1.periodic j) := by
  have he : exits (data K g.val) j.val = layerExits K g.val j.val := by
    have hj : j.val < (aligned K g.val).length := by rw [aligned_length h]; exact j.isLt
    simp only [exits,data,List.getElem?_map,List.getElem?_range hj,Option.map_some,Option.getD_some]
  refine ⟨text_layerWord h g,length_layerWord h g,?_⟩
  · funext x
    rw [he,exit_layerExits K g.val j.val (period_spec h g).1.positive,exit_eq h closed]

theorem data_size {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (g : Fin K.1.length) :
    (data K g.val).2.length = Fintype.card (C.Aligned (C.text g)) := by
  simp only [data,List.length_map,List.length_range,aligned_length h]

omit [Coded α] in
theorem aligned_length_le (K : Code α) (g : ℕ) : (aligned K g).length ≤ K.1.length := by
  exact (List.length_filter_le ..).trans_eq List.length_range

omit [Coded α] in
theorem letters_mem {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (closed : SubstringClosed V)
    (g : Fin K.1.length) (x : ℤ) : [C.text g x] ∈ V := by
  exact (C.layer closed (period_spec h g).1.periodic
    ⟨0,Fintype.card_pos_iff.mpr ⟨⟨g,rfl⟩⟩⟩).letters closed x
end Superstring.ThreadArray


namespace Superstring.UpperCode
open BitCode Hierarchical WalkCode LayerArray
variable {α : Type} [Inhabited α] [DecidableEq α]
abbrev Book (α : Type) := List (List α × List ℕ)
def lookup (B : Book α) (i : ℕ) : List α × List ℕ := B[i]?.getD ([],[])
def upper (m cut : ℕ) : List ℕ := (List.range m).filter (lessEq cut)
@[simp] theorem mem_upper (m cut i : ℕ) : i ∈ upper m cut ↔ cut ≤ i ∧ i < m := by
  simp only [upper,List.mem_filter,List.mem_range,lessEq,decide_eq_true_eq,and_comm]
theorem length_upper (m cut : ℕ) : (upper m cut).length = m-cut := by
  have he : (upper m cut).toFinset = Finset.Ico cut m := by ext i; simp
  have hn : (upper m cut).Nodup := List.Nodup.filter _ List.nodup_range
  rw [← List.toFinset_card_of_nodup hn,he,Nat.card_Ico]
theorem upper_filter {m cut lo : ℕ} (h : cut ≤ lo) :
    (upper m cut).filter (lessEq lo) = upper m lo := by
  simp only [upper,List.filter_filter]
  apply List.filter_congr
  intro i _
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,lessEq,decide_eq_true_eq]
  omega

abbrev Param := ℕ × ℕ × RecordCode.Code
def params (B : Book α) (ids : List ℕ) (m M : ℕ) (t : ℤ) : List Param :=
  (List.range (m+1)).flatMap (fun k => ids.flatMap (fun i =>
    (RecordCode.pool (lookup B i).1.length M t).map (fun r => (k,i,r))))

def test (D : GroupData α) (B : Book α) (cut : ℕ) (t : ℤ) (v : Param) : Bool :=
  let m := D.2.length
  let p := D.1.length
  let k := v.1
  let T := lookup B v.2.1
  let r := v.2.2
  less 0 k && lessEq k (m-cut) &&
    RecordCode.check D.1 T.1 T.2 r &&
    decide (RecordCode.start r ≤ t) && decide (t < RecordCode.stop r) &&
    decide (GeoCode.first (exits D (m-1)) t ≤ RecordCode.stop r+(k*p : ℕ)) &&
    decide (GeoCode.first (exits D (m-1)) t-GeoCode.exit (exits D (m-k)) t ≤ ((k-1)*p : ℕ)) &&
    ((upper m cut).filter (fun i => less i (m-k))).all
      (fun i => decide (GeoCode.first (exits D i) (RecordCode.start r) ≤ RecordCode.stop r))

-- A foreign-text filter is deliberately separate: its equality test uses only
-- a common product period, not a potentially unbounded infinite stream.
def choose (D : GroupData α) (B : Book α) (ids : List ℕ) (cut M : ℕ) (t : ℤ)
    (foreign : Param → Bool) : Param :=
  ((params B ids D.2.length M t).filter (fun v => test D B cut t v && foreign v)).headD (0,0,0,0,0)

omit [Inhabited α] [DecidableEq α] in
theorem params_mem {B : Book α} {ids : List ℕ} {m M k i : ℕ} {t : ℤ} {r : RecordCode.Code}
    (hk : k ≤ m) (hi : i ∈ ids) (hr : r ∈ RecordCode.pool (lookup B i).1.length M t) :
    (k,i,r) ∈ params B ids m M t := by
  exact List.mem_flatMap.mpr ⟨k,List.mem_range.mpr (by omega),List.mem_flatMap.mpr
    ⟨i,hi,List.mem_map.mpr ⟨r,hr,rfl⟩⟩⟩

theorem choose_spec (D : GroupData α) (B : Book α) (ids : List ℕ) (cut M : ℕ) (t : ℤ)
    (foreign : Param → Bool)
    (hex : ∃ v ∈ params B ids D.2.length M t, test D B cut t v = true ∧ foreign v = true) :
    let v := choose D B ids cut M t foreign
    v ∈ params B ids D.2.length M t ∧ test D B cut t v = true ∧ foreign v = true := by
  let vs := (params B ids D.2.length M t).filter (fun v => test D B cut t v && foreign v)
  have hn : vs ≠ [] := by
    obtain ⟨v,hv,ht,hf⟩ := hex
    have hm : v ∈ vs := List.mem_filter.mpr ⟨hv,by simp only [ht,hf,Bool.and_true]⟩
    exact List.ne_nil_of_mem hm
  have hm : vs.headD (0,0,0,0,0) ∈ vs := by
    cases he : vs with
    | nil => exact False.elim (hn he)
    | cons a as => simp
  simpa only [vs,List.mem_filter,Bool.and_eq_true,choose] using hm

variable [Coded α]
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem poly_lookup : Poly (fun q : Book α × ℕ => lookup q.1 q.2) := by
  exact BitCode.Poly.getD ([],[])
@[fun_prop] theorem poly_upper : Poly (fun q : ℕ × ℕ => upper q.1 q.2) := by
  unfold upper
  exact BitCode.Poly.filterFn (p := fun q : (ℕ × ℕ) × ℕ => lessEq q.1.2 q.2) (by fun_prop) (by fun_prop)
abbrev ParamsInput (α : Type) := Book α × List ℕ × ℕ × ℕ × ℤ
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem poly_params : Poly (fun q : ParamsInput α => params q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  unfold params
  apply BitCode.Poly.flatMapFn (f := fun q : ParamsInput α × ℕ => q.1.2.1.flatMap (fun i =>
    (RecordCode.pool (lookup q.1.1 i).1.length q.1.2.2.2.1 q.1.2.2.2.2).map (fun r => (q.2,i,r))))
  · apply BitCode.Poly.flatMapFn (f := fun q : (ParamsInput α × ℕ) × ℕ =>
      (RecordCode.pool (lookup q.1.1.1 q.2).1.length q.1.1.2.2.2.1 q.1.1.2.2.2.2).map (fun r => (q.1.2,q.2,r)))
    · exact BitCode.Poly.mapFn (f := fun q : ((ParamsInput α × ℕ) × ℕ) × RecordCode.Code =>
        (q.1.1.2,q.1.2,q.2)) (by fun_prop) (by fun_prop)
    · fun_prop
  · fun_prop
abbrev TestInput (α : Type) := GroupData α × Book α × ℕ × ℤ × Param
instance codedTestInput : Coded (TestInput α) := codedProd
@[fun_prop] theorem poly_test : Poly (fun q : TestInput α => test q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  unfold test
  dsimp only
  have ha : Poly (fun q : TestInput α =>
      ((upper q.1.2.length q.2.2.1).filter (fun i => less i (q.1.2.length-q.2.2.2.2.1))).all
        (fun i => decide (GeoCode.first (exits q.1 i) (RecordCode.start q.2.2.2.2.2.2) ≤ RecordCode.stop q.2.2.2.2.2.2))) := by
    apply BitCode.Poly.allFn (p := fun q : TestInput α × ℕ =>
      decide (GeoCode.first (exits q.1.1 q.2) (RecordCode.start q.1.2.2.2.2.2.2) ≤ RecordCode.stop q.1.2.2.2.2.2.2))
    · unfold RecordCode.start RecordCode.stop
      fun_prop
    · exact BitCode.Poly.filterFn (p := fun q : TestInput α × ℕ => less q.2 (q.1.1.2.length-q.1.2.2.2.2.1)) (by fun_prop) (by fun_prop)
  have hr : Poly (fun q : TestInput α => RecordCode.check q.1.1 (lookup q.2.1 q.2.2.2.2.2.1).1 (lookup q.2.1 q.2.2.2.2.2.1).2 q.2.2.2.2.2.2) :=
    RecordCode.poly_check.comp (f := fun q : TestInput α => ((q.1.1,(lookup q.2.1 q.2.2.2.2.2.1).1,(lookup q.2.1 q.2.2.2.2.2.1).2),q.2.2.2.2.2.2)) (by fun_prop)
  unfold RecordCode.start RecordCode.stop at *
  fun_prop
end Superstring.UpperCode


namespace Superstring.PeriodWord
open BitCode Hierarchical
variable {α : Type} [Inhabited α] [DecidableEq α]

def different (U W : List α) (d : ℤ) : Bool :=
  !equal (window U 0 (U.length*W.length : ℕ)) (window W d (d+(U.length*W.length : ℕ)))

theorem different_iff (U W : List α) (d : ℤ) (hU : 0 < U.length) (hW : 0 < W.length) :
    different U W d = true ↔ text U ≠ fun x => text W (x+d) := by
  have hm : 0 < U.length*W.length := Nat.mul_pos hU hW
  have perU : Function.Periodic (text U) ((U.length*W.length : ℕ) : ℤ) := by
    simpa only [nsmul_eq_mul,Nat.cast_mul,mul_comm] using (periodic U).nsmul W.length
  have perW : Function.Periodic (fun x => text W (x+d)) ((U.length*W.length : ℕ) : ℤ) := by
    have hp := (periodic W).nsmul U.length
    intro x
    simpa only [nsmul_eq_mul,Nat.cast_mul,add_right_comm] using hp (x+d)
  have he : window U 0 (U.length*W.length : ℕ) = window W d (d+(U.length*W.length : ℕ)) ↔
      text U = fun x => text W (x+d) := by
    rw [window_eq,window_eq]
    have hr := textWord_reindex (text W) d 0 (U.length*W.length : ℕ)
    simp only [zero_add] at hr
    rw [add_comm d,← hr]
    constructor
    · intro h
      funext x
      let r := x % ((U.length*W.length : ℕ) : ℤ)
      have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
      have hrm : r < (U.length*W.length : ℕ) := Int.emod_lt_of_pos _ (by omega)
      have hri : r.toNat < U.length*W.length := by omega
      have ha := congrArg (fun w : List α => w[r.toNat]?) h
      simp only [textWord,List.getElem?_ofFn] at ha
      have hlen : (((U.length*W.length : ℕ) : ℤ)-0).toNat = U.length*W.length := by omega
      simp only [hlen,hri,↓reduceDIte,zero_add,Option.some.injEq,Int.toNat_of_nonneg hr0] at ha
      have hu := periodic_emod (text U) ((U.length*W.length : ℕ) : ℤ) perU x
      have hw := periodic_emod (fun x => text W (x+d)) ((U.length*W.length : ℕ) : ℤ) perW x
      exact hu.symm.trans (ha.trans hw)
    · intro h
      rw [h]
  simpa only [different,equal,Bool.not_eq_true',decide_eq_false_iff_not] using not_congr he

variable [Coded α]
@[fun_prop] theorem poly_different : Poly (fun q : List α × List α × ℤ => different q.1 q.2.1 q.2.2) := by
  unfold different
  fun_prop
end Superstring.PeriodWord


namespace Superstring.UpperCode
open BitCode Hierarchical LayerArray
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}

def foreign (D : GroupData α) (B : Book α) (v : Param) : Bool :=
  PeriodWord.different D.1 (lookup B v.2.1).1 (RecordCode.offset v.2.2)

theorem supply_params (C : LayerCollection V G) (g : G) (supply : C.RecordSupply)
    (D : GroupData α) (B : Book α) (ids : List ℕ) (encode : C.Id → ℕ)
    (hsize : D.2.length = C.size g)
    (hD : ∀ i : Fin (C.size g), Represents D.1 (exits D i.val) (C.layer g i))
    (hB : ∀ i : C.Id, Represents (lookup B (encode i)).1 (lookup B (encode i)).2 (C.layerAt i))
    (hids : ∀ i, encode i ∈ ids) (M : ℕ) (len : ∀ w ∈ V, w.length ≤ M)
    (cut : ℕ) (hcut : cut < C.size g)
    (he : ¬ (C.layer g ⟨C.size g-1,by have := C.nonempty g; omega⟩).first (C.distinguished g) - C.distinguished g
      ≤ ((C.size g-cut)*C.period g : ℕ))
    (hb : ¬ ∃ base : Fin (C.size g), base.val+1=cut ∧
      (C.layer g ⟨C.size g-1,by have := C.nonempty g; omega⟩).first (C.distinguished g) -
        (C.layer g base).last (C.distinguished g) ≤ ((C.size g-cut)*C.period g : ℕ)) :
    ∃ v ∈ params B ids D.2.length M (C.distinguished g),
      test D B cut (C.distinguished g) v = true ∧ foreign D B v = true := by
  classical
  let n := C.size g-cut
  let top : Fin (C.size g) := ⟨C.size g-1,by have := C.nonempty g; omega⟩
  let t := C.distinguished g
  let H := (C.layer g top).first t
  have hn : 0 < n := by dsimp only [n]; omega
  have hnm : n ≤ C.size g := Nat.sub_le ..
  have hz : Monotone (fun i : Fin (C.size g) => (C.layer g i).last t) :=
    fun i j hij => C.ordered g i j hij t
  have hstopn : (Processing.qualifying (fun i => (C.layer g i).last t) H (C.period g) n).card ≤ n := by
    by_cases hzero : cut = 0
    · have hh := Finset.card_le_univ (Processing.qualifying (fun i => (C.layer g i).last t) H (C.period g) n)
      simpa only [Fintype.card_fin,n,hzero,Nat.sub_zero] using hh
    · let base : Fin (C.size g) := ⟨cut-1,by omega⟩
      have hfail : (C.layer g base).last t < H-(n*C.period g : ℕ) := by
        by_contra hh
        apply hb
        exact ⟨base,by dsimp only [base]; omega,by dsimp only [H,t,n,top] at hh ⊢; omega⟩
      have hh := Processing.qualifying_bound _ hz H (C.period g) n base hfail
      change _ ≤ C.size g-1-(cut-1) at hh
      dsimp only [n] at hh ⊢
      omega
  obtain ⟨k,hk,hkn,hstop,hsharp⟩ := Processing.choose_k hn hnm _ hz H
    (C.period g) ((C.layer g top).first_le_last t) hstopn
  have hkm : k ≤ C.size g := hkn.trans hnm
  have hmul : k*C.period g ≤ n*C.period g := Nat.mul_le_mul_right _ hkn
  have hhard : t+(k*C.period g : ℕ) < (C.layer g top).first t := by
    dsimp only [t,top] at *
    dsimp only [n] at hmul
    omega
  obtain ⟨d,R,ha,hh,hd⟩ := supply g top t k hk hhard hstop
  have ht : t < R.stop := by omega
  let R' := R.normalize (C.periodic d.1)
  let r : RecordCode.Code := (R'.offset,R.start,R.stop)
  have htext := (hD top).text_eq
  have hp := (hD top).length_eq
  have hr : r ∈ RecordCode.pool (lookup B (encode d)).1.length M t := by
    rw [(hB d).length_eq]
    exact RecordCode.normalized_mem_pool (C.positive d.1) (C.periodic d.1) R ha ht len
  refine ⟨(k,encode d,r),params_mem (by omega) (hids d) hr,?_,?_⟩
  · have hc : RecordCode.check D.1 (lookup B (encode d)).1 (lookup B (encode d)).2 r = true :=
      RecordCode.check_record htext (hB d) R'
    have htop : GeoCode.first (exits D (D.2.length-1)) t = (C.layer g top).first t := by
      rw [hsize]
      exact congrFun (hD top).exit_eq (t-1)
    have hlo : GeoCode.exit (exits D (D.2.length-k)) t = (C.layer g ⟨C.size g-k,by omega⟩).last t := by
      rw [hsize]
      exact congrFun (hD ⟨C.size g-k,by omega⟩).exit_eq t
    have hall : ((upper D.2.length cut).filter (fun i => less i (D.2.length-k))).all
        (fun i => decide (GeoCode.first (exits D i) R.start ≤ R.stop)) = true := by
      apply List.all_eq_true.mpr
      intro i hi
      have hi' : cut ≤ i ∧ i < C.size g ∧ i < C.size g-k := by
        simpa only [List.mem_filter,mem_upper,less,decide_eq_true_eq,hsize,and_assoc] using hi
      let j : Fin (C.size g) := ⟨i,hi'.2.1⟩
      have hj := Processing.below_stopped _ hz H (C.period g) k hstop j hi'.2.2
      have hfa := (C.layer g j).first_mono ha
      have hfl := (C.layer g j).first_le_last t
      have hg : GeoCode.first (exits D i) R.start = (C.layer g j).first R.start :=
        congrFun (hD j).exit_eq (R.start-1)
      apply decide_eq_true
      rw [hg]
      dsimp only [H] at hj
      omega
    simp only [test,less,lessEq,Bool.and_eq_true,decide_eq_true_eq]
    refine ⟨⟨⟨⟨⟨⟨⟨hk,by omega⟩,hc⟩,ha⟩,ht⟩,?_⟩,?_⟩,?_⟩
    · change GeoCode.first _ t ≤ R.stop+(k*D.1.length : ℕ)
      rw [htop,hp]
      omega
    · change GeoCode.first _ t-GeoCode.exit _ t ≤ ((k-1)*D.1.length : ℕ)
      rw [htop,hlo,hp]
      dsimp only [H] at hsharp
      omega
    · exact hall
  · unfold foreign
    apply (PeriodWord.different_iff _ _ _ (by rw [hp]; exact C.positive g)
      (by rw [(hB d).length_eq]; exact C.positive d.1)).mpr
    rw [htext,(hB d).text_eq]
    change C.text g ≠ fun x => C.text d.1 (x+R'.offset)
    rw [R.normalize_text (C.periodic d.1)]
    exact hd
end Superstring.UpperCode

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode
variable {α : Type} [Inhabited α] [DecidableEq α]
abbrev Env (α : Type) := (List (GroupData α) × List ℕ) × ℕ
def data (X : Env α) (g : ℕ) : GroupData α := X.1.1[g]?.getD ([],[])
def gs (X : Env α) : List ℕ := X.1.2
def stride (X : Env α) : ℕ := X.2
def owner (X : Env α) (i : ℕ) : ℕ := i / stride X
def idx (X : Env α) (i : ℕ) : ℕ := i % stride X
def layer (X : Env α) (i : ℕ) : List α × List ℕ :=
  ((data X (owner X i)).1,exits (data X (owner X i)) (idx X i))
def book (X : Env α) : UpperCode.Book α := (List.range (X.1.1.length*stride X)).map (layer X)
def ids (X : Env α) : List ℕ := (gs X).flatMap (fun g =>
  (List.range (data X g).2.length).map (fun i => g*stride X+i))
def per (X : Env α) (g : ℕ) : ℕ := (data X g).1.length
def phase [LinearOrder α] (X : Env α) (g : ℕ) : ℤ := RotationCode.phase (data X g).1
def contents (X : Env α) : List (Walk α) := (book X).map (fun d => content d.1 d.2)
def ls (X : Env α) : ℕ → Walk α := BlockClose.lookup (contents X)

omit [Inhabited α] [DecidableEq α] in
theorem owner_encode (X : Env α) (g i : ℕ) (hi : i < stride X) : owner X (g*stride X+i) = g := by
  have hp : 0 < stride X := by omega
  simp only [owner,Nat.add_mul_div_right i g hp,add_comm (g*stride X) i]
  rw [Nat.div_eq_of_lt hi,zero_add]
omit [Inhabited α] [DecidableEq α] in
theorem idx_encode (X : Env α) (g i : ℕ) (hi : i < stride X) : idx X (g*stride X+i) = i := by
  unfold idx
  rw [Nat.add_mod,Nat.mul_mod_left,zero_add,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hi]

omit [Inhabited α] [DecidableEq α] in
theorem lookup_encode (X : Env α) (g i : ℕ) (hg : g < X.1.1.length) (hi : i < stride X) :
    UpperCode.lookup (book X) (g*stride X+i) = ((data X g).1,exits (data X g) i) := by
  have hb : g*stride X+i < X.1.1.length*stride X := by nlinarith
  simp only [UpperCode.lookup,book,List.getElem?_map,List.getElem?_range hb,
    Option.map_some,Option.getD_some,layer,owner_encode X g i hi,idx_encode X g i hi]

omit [DecidableEq α] in
theorem ls_encode (X : Env α) (g i : ℕ) (hg : g < X.1.1.length) (hi : i < stride X) :
    ls X (g*stride X+i) = content (data X g).1 (exits (data X g) i) := by
  have hb : g*stride X+i < X.1.1.length*stride X := by nlinarith
  simp only [ls,BlockClose.lookup,contents,book,List.getElem?_map,List.getElem?_range hb,
    Option.map_some,Option.getD_some,layer,owner_encode X g i hi,idx_encode X g i hi]

omit [Inhabited α] [DecidableEq α] in
theorem encode_injective (X : Env α) {g h i j : ℕ} (hi : i < stride X) (hj : j < stride X)
    (he : g*stride X+i = h*stride X+j) : g = h ∧ i = j := by
  exact ⟨by have := congrArg (owner X) he; simpa only [owner_encode X g i hi,owner_encode X h j hj] using this,
    by have := congrArg (idx X) he; simpa only [idx_encode X g i hi,idx_encode X h j hj] using this⟩

variable [Coded α]
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem poly_data : Poly (fun q : Env α × ℕ => data q.1 q.2) := by
  unfold data
  exact (BitCode.Poly.getD ([],[])).comp (f := fun q : Env α × ℕ => (q.1.1.1,q.2)) (by fun_prop)
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem poly_owner : Poly (fun q : Env α × ℕ => owner q.1 q.2) := by unfold owner stride; fun_prop
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem poly_idx : Poly (fun q : Env α × ℕ => idx q.1 q.2) := by unfold idx stride; fun_prop
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem poly_layer : Poly (fun q : Env α × ℕ => layer q.1 q.2) := by unfold layer; fun_prop
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem poly_book : Poly (fun X : Env α => book X) := by
  unfold book stride
  exact BitCode.Poly.mapFn poly_layer (by fun_prop)
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem poly_ids : Poly (fun X : Env α => ids X) := by
  unfold ids gs stride
  apply BitCode.Poly.flatMapFn (f := fun q : Env α × ℕ =>
    (List.range (data q.1 q.2).2.length).map (fun i => q.2*q.1.2+i))
  · exact BitCode.Poly.mapFn (f := fun q : (Env α × ℕ) × ℕ => q.1.2*q.1.1.2+q.2) (by fun_prop) (by fun_prop)
  · fun_prop
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem poly_per : Poly (fun q : Env α × ℕ => per q.1 q.2) := by unfold per; fun_prop
omit [DecidableEq α] in
@[fun_prop] theorem poly_contents : Poly (fun X : Env α => contents X) := by
  unfold contents
  exact BitCode.Poly.mapFn (f := fun q : Env α × (List α × List ℕ) => content q.2.1 q.2.2) (by fun_prop) poly_book
variable [LinearOrder α]
omit [DecidableEq α] in
@[fun_prop] theorem poly_phase (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (fun q : Env α × ℕ => phase q.1 q.2) := by
  unfold phase
  exact BitCode.Poly.natCastInt.comp ((RotationCode.poly_phase hlt).comp (by fun_prop))
end Superstring.CollectionCode


namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}

noncomputable def rank (X : Env α) (g : ℕ) : Lex (ℕ → α) :=
  forward (PeriodWord.text (data X g).1) (phase X g)


structure Model (X : Env α) (C : LayerCollection V G) where
  group : G → ℕ
  group_inj : Function.Injective group
  groups : ∀ j, j ∈ gs X ↔ ∃ g, group g = j
  nodup : (gs X).Nodup
  bound : ∀ g, group g < X.1.1.length
  size : ∀ g, (data X (group g)).2.length = C.size g
  capacity : ∀ g, C.size g ≤ stride X
  rep : ∀ (g) (i : Fin (C.size g)), Represents (data X (group g)).1
    (exits (data X (group g)) i.val) (C.layer g i)
  phase_eq : ∀ g, phase X (group g) = C.distinguished g

namespace Model
variable {X : Env α} {C : LayerCollection V G} (h : Model X C)
def encode (i : C.Id) : ℕ := h.group i.1*stride X+i.2.val

include h
theorem local_lt (g : G) (i : Fin (C.size g)) : i.val < stride X := lt_of_lt_of_le i.isLt (h.capacity g)
@[simp] theorem owner_eq (i : C.Id) : owner X (h.encode i) = h.group i.1 :=
  owner_encode X _ _ (h.local_lt ..)
@[simp] theorem idx_eq (i : C.Id) : idx X (h.encode i) = i.2.val := idx_encode X _ _ (h.local_lt ..)

theorem encode_inj : Function.Injective h.encode := by
  intro i j he
  obtain ⟨i,k⟩ := i
  obtain ⟨j,l⟩ := j
  obtain ⟨hg,hi⟩ := encode_injective X (h.local_lt i k) (h.local_lt j l) he
  have hg' : i = j := h.group_inj hg
  subst j
  exact Sigma.mk.inj_iff.mpr ⟨rfl,heq_of_eq (Fin.ext hi)⟩

theorem id_mem (i : C.Id) : h.encode i ∈ ids X := by
  apply List.mem_flatMap.mpr
  refine ⟨h.group i.1,(h.groups _).mpr ⟨i.1,rfl⟩,List.mem_map.mpr ⟨i.2.val,?_,rfl⟩⟩
  rw [List.mem_range,h.size]
  exact i.2.isLt

theorem mem_ids (j : ℕ) : j ∈ ids X ↔ ∃ i, h.encode i = j := by
  constructor
  · intro hj
    obtain ⟨g,hg,hj⟩ := List.mem_flatMap.mp hj
    obtain ⟨a,rfl⟩ := (h.groups g).mp hg
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hj
    have hi' : i < C.size a := by simpa only [List.mem_range,h.size] using hi
    exact ⟨⟨a,⟨i,hi'⟩⟩,rfl⟩
  · rintro ⟨i,rfl⟩
    exact h.id_mem i

theorem book_rep (i : C.Id) : Represents (UpperCode.lookup (book X) (h.encode i)).1
    (UpperCode.lookup (book X) (h.encode i)).2 (C.layerAt i) := by
  rw [encode,lookup_encode X _ _ (h.bound _) (h.local_lt ..)]
  exact h.rep ..

theorem content_iff (i : C.Id) (w : List α) : w ∈ ls X (h.encode i) ↔ w ∈ (C.layerAt i).Content := by
  rw [encode,ls_encode X _ _ (h.bound _) (h.local_lt ..)]
  exact mem_content (h.rep i.1 i.2) (C.positive i.1) (C.periodic i.1) w

@[simp] theorem per_eq (g : G) : per X (h.group g) = C.period g :=
  (h.rep g ⟨0,C.nonempty g⟩).length_eq
@[simp] theorem text_eq (g : G) : PeriodWord.text (data X (h.group g)).1 = C.text g :=
  (h.rep g ⟨0,C.nonempty g⟩).text_eq
@[simp] theorem rank_eq (g : G) : rank X (h.group g) = C.rank g := by
  simp only [rank,h.text_eq,h.phase_eq,LayerCollection.rank]

def natIndex (_h : Model X C) (g : G) (i : ℕ) : Fin (C.size g) :=
  ⟨min i (C.size g-1),by have := C.nonempty g; omega⟩
def natLayer (g : G) (i : ℕ) : Layer V (C.text g) (C.period g) := C.layer g (h.natIndex g i)
@[simp] theorem natIndex_val (g : G) {i : ℕ} (hi : i < C.size g) : (h.natIndex g i).val = i := by
  exact Nat.min_eq_left (by omega)
@[simp] theorem natLayer_fin (g : G) (i : Fin (C.size g)) : h.natLayer g i.val = C.layer g i := by
  unfold natLayer
  congr 1
  exact Fin.ext (h.natIndex_val g i.isLt)
theorem nat_rep (g : G) {i : ℕ} (hi : i < C.size g) :
    Represents (data X (h.group g)).1 (exits (data X (h.group g)) i) (h.natLayer g i) := by
  simpa only [natLayer,h.natIndex_val g hi] using h.rep g (h.natIndex g i)
theorem nat_order (g : G) {i j : ℕ} (hij : i ≤ j) (x : ℤ) :
    (h.natLayer g i).z x ≤ (h.natLayer g j).z x := by
  apply C.ordered
  change min i _ ≤ min j _
  omega

theorem rank_shift (g : G) (d : C.Id) (r : ℤ)
    (hr : rank X (owner X (h.encode d)) ≤ rank X (h.group g)) :
    ∀ x, forward (fun x => C.text d.1 (x+r)) x ≤ forward (C.text g) (C.distinguished g) := by
  rw [h.owner_eq,h.rank_eq,h.rank_eq] at hr
  intro x
  rw [forward_shift]
  exact (C.distinguished_max d.1 (x+r)).trans hr
end Model
end Superstring.CollectionCode


namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode BlockClose
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}

def hard (X : Env α) (g cut : ℕ) (v : UpperCode.Param) : DistributeCode.Result α :=
  let D := data X g
  DistributeCode.record D g v.2.1 (g*stride X) (UpperCode.upper D.2.length cut)
    (D.2.length-v.1) (D.2.length-1) (RecordCode.start v.2.2) (RecordCode.stop v.2.2) (phase X g)

namespace Model
variable {X : Env α} {C : LayerCollection V G} (h : Model X C)

theorem hard_spec (closed : SubstringClosed V) (g : G) (cut : ℕ) (v : UpperCode.Param)
    (hcut : cut < C.size g) (hv : v.2.1 ∈ ids X)
    (ht : UpperCode.test (data X (h.group g)) (book X) cut (phase X (h.group g)) v = true)
    (hf : UpperCode.foreign (data X (h.group g)) (book X) v = true) :
    let o := hard X (h.group g) cut v
    Runs V [] [] o.1 ∧ DistributeCode.budget o (C.period g) ≤ 2*((C.size g-cut)*C.period g) ∧
      (∀ b ∈ o.2.1, ValidBlock V (ids X) (ls X) (owner X) (per X) (rank X) b) ∧
      (∀ i : Fin (C.size g), cut ≤ i.val →
        (∀ w ∈ ls X (h.encode ⟨g,i⟩), w ∈ o.1) ∨
        (∃ b ∈ o.2.1, h.encode ⟨g,i⟩ ∈ b.members) ∨ i.val ∈ o.2.2) ∧
      o.2.2.Sublist (UpperCode.upper (C.size g) cut) ∧
      ∃ (d : C.Id) (R : (C.layerAt d).Record (C.text g)), h.encode d = v.2.1 ∧
        R.offset = RecordCode.offset v.2.2 ∧ R.start = RecordCode.start v.2.2 ∧ R.stop = RecordCode.stop v.2.2 ∧
        C.text g ≠ (fun x => C.text d.1 (x+R.offset)) ∧
        ∀ i ∈ o.2.2, R.start+C.period g < (h.natLayer g i).first R.start ∧
          (h.natLayer g i).last R.start < R.stop-C.period g := by
  obtain ⟨d,hd⟩ := (h.mem_ids v.2.1).mp hv
  unfold UpperCode.test at ht
  unfold UpperCode.foreign at hf
  rw [← hd] at ht hf
  simp only [Bool.and_eq_true,less,lessEq,decide_eq_true_eq,
    h.size,h.phase_eq] at ht
  obtain ⟨⟨⟨⟨⟨⟨⟨hk,hkn⟩,hr⟩,hat⟩,htb⟩,hH⟩,hsharp⟩,hfirst⟩ := ht
  let D := data X (h.group g)
  have hp : D.1.length = C.period g := h.per_eq g
  let R := RecordCode.checkedRecord (h.text_eq g) (h.book_rep d) v.2.2 hr
  have hne : C.text g ≠ fun x => C.text d.1 (x+R.offset) := by
    have hh := (PeriodWord.different_iff D.1 (UpperCode.lookup (book X) (h.encode d)).1
      (RecordCode.offset v.2.2) (by rw [hp]; exact C.positive g)
      (by rw [(h.book_rep d).length_eq]; exact C.positive d.1)).mp hf
    simpa only [D,h.text_eq,(h.book_rep d).text_eq,R,RecordCode.checkedRecord] using hh
  let I := UpperCode.upper (C.size g) cut
  let lo := C.size g-v.1
  let hi := C.size g-1
  have hilo : lo ≤ hi := by dsimp [lo,hi]; omega
  have hm (i : ℕ) : i ∈ I ↔ cut ≤ i ∧ i < C.size g := UpperCode.mem_upper _ _ _
  have hlo : lo ∈ I := (hm _).mpr (by dsimp [lo]; omega)
  have hhi : hi ∈ I := (hm _).mpr (by dsimp [hi]; omega)
  have hlen : (I.filter (fun i => lessEq lo i)).length = v.1 := by
    rw [UpperCode.upper_filter (show cut ≤ lo from by dsimp [lo]; omega)]
    simp only [UpperCode.length_upper]
    dsimp only [lo]
    omega
  have hrep : ∀ i ∈ I, Represents D.1 (exits D i) (h.natLayer g i) :=
    fun i hi' => h.nat_rep g ((hm i).mp hi').2
  have hexit (i : ℕ) (hi' : i ∈ I) (x : ℤ) : GeoCode.exit (exits D i) x = (h.natLayer g i).z x :=
    congrFun (hrep i hi').exit_eq x
  have hh := DistributeCode.record_spec (h.natLayer g) (C.layerAt d) hrep closed
    (C.positive g) (C.positive d.1) (C.periodic g) (C.periodic d.1) (C.letters closed g)
    R hne (C.distinguished g) hat htb (C.distinguished_max g) hlo hhi hilo
    (fun i _ hil x => h.nat_order g hil x)
    (fun i hi' x => h.nat_order g (by have := (hm i).mp hi'; dsimp [hi]; omega) x)
    (by
      intro i hi' hil
      have hiF : i ∈ (UpperCode.upper (C.size g) cut).filter (fun i => decide (i < C.size g-v.1)) :=
        List.mem_filter.mpr ⟨hi',by simpa only [decide_eq_true_eq] using hil⟩
      have hh := of_decide_eq_true (List.all_eq_true.mp hfirst i hiF)
      change (h.natLayer g i).z (R.start-1) ≤ R.stop
      rw [← hexit i hi']
      exact hh)
    (by
      change (h.natLayer g hi).z (C.distinguished g-1) ≤ _
      rw [← hexit hi hhi,hlen,← hp]
      exact hH)
    (by
      change (h.natLayer g hi).z (C.distinguished g-1)-(h.natLayer g lo).z (C.distinguished g) ≤ _
      rw [← hexit hi hhi,← hexit lo hlo,hlen,← hp]
      exact hsharp)
    (ids X) (ls X) (owner X) (per X) (rank X) (h.per_eq g) (h.id_mem d)
    (by intro i hi'; exact owner_encode X _ _ (lt_of_lt_of_le ((hm i).mp hi').2 (h.capacity g)))
    (by rw [h.owner_eq,h.per_eq]) (h.rank_shift g d R.offset)
    ((h.content_iff d _).mpr ⟨R.start+R.offset,R.stop+R.offset,R.first_le,R.le_last,R.word_eq⟩)
    (by
      intro i hi' w hw
      let j : Fin (C.size g) := ⟨i,((hm i).mp hi').2⟩
      have hh := (h.content_iff ⟨g,j⟩ w).mp hw
      change w ∈ (C.layer g j).Content at hh
      have he : h.natLayer g i = C.layer g j := h.natLayer_fin g j
      rw [he]
      exact hh)
  dsimp only at hh ⊢
  have he : hard X (h.group g) cut v = DistributeCode.record D (h.group g) (h.encode d)
      (h.group g*stride X) I lo hi R.start R.stop (C.distinguished g) := by
    simp only [hard,h.size,h.phase_eq,hd,D,I,lo,hi,R,RecordCode.checkedRecord]
  rw [he]
  refine ⟨hh.1,?_,hh.2.2.1,?_,hh.2.2.2.2.1,d,R,hd,rfl,rfl,rfl,hne,hh.2.2.2.2.2⟩
  · simpa only [I,UpperCode.length_upper] using hh.2.1
  · intro i hi'
    exact hh.2.2.2.1 i.val ((hm i.val).mpr ⟨hi',i.isLt⟩)
end Model
end Superstring.CollectionCode


namespace Superstring.BitCode.Poly
variable {α β : Type} [Coded α] [Coded β] [Inhabited α] [Inhabited β]
@[fun_prop] theorem zip : Poly (fun p : List α × List β => p.1.zip p.2) := by
  have h : Poly (fun p : List α × List β =>
      (List.range (Min.min p.1.length p.2.length)).map
        (fun i => (p.1[i]?.getD default, p.2[i]?.getD default))) := by
    apply mapFn (f := fun q : (List α × List β) × ℕ =>
      (q.1.1[q.2]?.getD default, q.1.2[q.2]?.getD default))
    · exact ((getD default).comp
          (f := fun q : (List α × List β) × ℕ => (q.1.1,q.2)) (by fun_prop)).pair
        ((getD default).comp
          (f := fun q : (List α × List β) × ℕ => (q.1.2,q.2)) (by fun_prop))
    · fun_prop
  convert h using 1
  funext p
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    have h₁ : i < p.1.length := by simp only [List.length_zip] at hi; omega
    have h₂ : i < p.2.length := by simp only [List.length_zip] at hi; omega
    simp only [List.getElem_zip,List.getElem_map,List.getElem_range,
      List.getElem?_eq_getElem h₁,List.getElem?_eq_getElem h₂,Option.getD_some]
end Superstring.BitCode.Poly
namespace Superstring.WindowCode
open Hierarchical WalkCode BitCode
variable {α : Type}
abbrev Window := ℤ × ℤ
def ordered (u v : Window) : Prop := u.1 ≤ v.1 ∧ u.2 ≤ v.2
def routeList (A : ℤ → α) (u : Window) (W : List Window) : Walk α :=
  [textWord A u.1 u.2] ++ (((u::W).zip W).flatMap fun q =>
    (route A q.1.1 q.1.2 q.2.1 q.2.2).tail)

theorem routeList_nil (A : ℤ → α) (u : Window) : routeList A u [] = [textWord A u.1 u.2] := rfl

theorem routeList_cons (A : ℤ → α) (u v : Window) (W : List Window)
    (hh : (route A u.1 u.2 v.1 v.2).head? = some (textWord A u.1 u.2)) :
    routeList A u (v::W) = join (route A u.1 u.2 v.1 v.2) (routeList A v W) := by
  unfold routeList
  simp only [List.zip_cons_cons,List.flatMap_cons,List.singleton_append,join,List.tail_cons]
  cases he : route A u.1 u.2 v.1 v.2 with
  | nil => simp [he] at hh
  | cons x xs =>
    have hx : x = textWord A u.1 u.2 := by simpa only [he,List.head?_cons,Option.some.injEq] using hh
    simp only [hx,List.tail_cons,List.cons_append]

theorem routeList_realizes {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (u : Window) (W : List Window)
    (hchain : (u::W).Pairwise ordered)
    (hvalid : ∀ v ∈ u::W, v.1 ≤ v.2 ∧ textWord A v.1 v.2 ∈ V) :
    ∃ P : Hierarchical.Path V (textWord A u.1 u.2)
      (textWord A (W.getLastD u).1 (W.getLastD u).2),
      Path.points P = routeList A u W ∧ P.cost = ((W.getLastD u).2-u.2).toNat ∧
      ∀ v ∈ u::W, P.Visits (textWord A v.1 v.2) := by
  induction W generalizing u with
  | nil =>
    refine ⟨.nil _ (hvalid u (by simp)).2,rfl,?_,?_⟩
    · simp only [Hierarchical.Path.cost,List.getLastD_nil,sub_self,Int.toNat_zero]
    · intro v hv
      have he : v = u := List.mem_singleton.mp hv
      subst v
      exact Hierarchical.Path.visits_start _
  | cons v W ih =>
    obtain ⟨hfront,hrest⟩ := List.pairwise_cons.mp hchain
    have huv := hfront v (by simp)
    have hu := hvalid u (by simp)
    have hv := hvalid v (by simp)
    obtain ⟨P,hP,hcP,_,_⟩ := route_realizes closed A letters hu.1 hv.1 huv.1 huv.2 hu.2 hv.2
    obtain ⟨Q,hQ,hcQ,hvQ⟩ := ih v hrest (fun x hx => hvalid x (List.mem_cons_of_mem u hx))
    have hhead : (route A u.1 u.2 v.1 v.2).head? = some (textWord A u.1 u.2) := by
      rw [← hP]; exact (points_spec P).2.1
    have hlast : (v::W).getLastD u = W.getLastD v := by cases W <;> rfl
    have hend : v.2 ≤ (W.getLastD v).2 := by
      rcases List.mem_cons.mp (List.getLastD_mem_cons (l:=W) (a:=v)) with he | he
      · rw [he]
      · exact (List.pairwise_cons.mp hrest).1 _ he |>.2
    refine ⟨(P.trans Q).copy rfl (by rw [hlast]),?_,?_,?_⟩
    · rw [points_copy,Path.points,hP,hQ,routeList_cons A u v W hhead]
    · simp only [Hierarchical.Path.cost_copy,Hierarchical.Path.cost_trans,hcP,hcQ,hlast]
      have hh := huv.2
      omega
    · intro x hx
      apply (Hierarchical.Path.visits_copy ..).mpr
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl (Hierarchical.Path.visits_start P)
      · exact Or.inr (hvQ x hx)

variable [Inhabited α] [Coded α]
@[fun_prop] theorem poly_routeList : Poly (fun q : List α × Window × List Window =>
    routeList (PeriodWord.text q.1) q.2.1 q.2.2) := by
  unfold routeList
  apply Poly.append.comp (f := fun q : List α × Window × List Window =>
    ([textWord (PeriodWord.text q.1) q.2.1.1 q.2.1.2],
      (((q.2.1::q.2.2).zip q.2.2).flatMap fun r =>
        (route (PeriodWord.text q.1) r.1.1 r.1.2 r.2.1 r.2.2).tail)))
  apply Poly.pair
  · simp_rw [← PeriodWord.window_eq]
    fun_prop
  · change Poly (fun q : List α × Window × List Window =>
      ((((q.2.1::q.2.2).zip q.2.2).map (fun r =>
        (route (PeriodWord.text q.1) r.1.1 r.1.2 r.2.1 r.2.2).tail))).flatten)
    apply Poly.flatten.comp
    apply Poly.mapFn (f := fun q : (List α × Window × List Window) × (Window × Window) =>
      (route (PeriodWord.text q.1.1) q.2.1.1 q.2.1.2 q.2.2.1 q.2.2.2).tail)
    · fun_prop
    · exact (BitCode.Poly.zip (α:=Window) (β:=Window)).comp
        (f := fun q : List α × Window × List Window => (q.2.1::q.2.2,q.2.2)) (by fun_prop)
end Superstring.WindowCode

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.BitCode
variable {α : Type}
def keySort (xs : List (ℕ × α)) : List (ℕ × α) :=
  (List.range ((xs.map Prod.fst).foldl max 0+1)).flatMap fun k => xs.filter (fun x => equal x.1 k)

theorem initial_le_maxFold (xs : List ℕ) (a : ℕ) : a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => exact le_rfl
  | cons x xs ih => exact (le_max_left a x).trans (ih _)

theorem le_maxFold {x : ℕ} (xs : List ℕ) (a : ℕ) (hx : x ∈ xs) : x ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => cases hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hh
    · exact (le_max_right a x).trans (initial_le_maxFold ys _)
    · exact ih _ hh

theorem mem_keySort (xs : List (ℕ × α)) (x : ℕ × α) : x ∈ keySort xs ↔ x ∈ xs := by
  constructor
  · intro h
    obtain ⟨k,_,hk⟩ := List.mem_flatMap.mp h
    exact List.mem_of_mem_filter hk
  · intro h
    apply List.mem_flatMap.mpr
    refine ⟨x.1,List.mem_range.mpr ?_,List.mem_filter.mpr ⟨h,by simp [equal]⟩⟩
    have := le_maxFold (xs.map Prod.fst) 0 (List.mem_map.mpr ⟨x,h,rfl⟩)
    omega

theorem pairwise_keySort (xs : List (ℕ × α)) :
    (keySort xs).Pairwise (fun x y => x.1 ≤ y.1) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro k _
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj _
    have hx : (xs.filter (fun x => equal x.1 k))[i].1 = k :=
      of_decide_eq_true (List.mem_filter.mp (List.getElem_mem hi)).2
    have hy : (xs.filter (fun x => equal x.1 k))[j].1 = k :=
      of_decide_eq_true (List.mem_filter.mp (List.getElem_mem hj)).2
    omega
  · apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij x hx y hy
    have hx := (List.mem_filter.mp hx).2
    have hy := (List.mem_filter.mp hy).2
    simp only [equal,decide_eq_true_eq,List.getElem_range] at hx hy
    omega

variable [Coded α]
@[fun_prop] theorem poly_keySort : Poly (keySort (α:=α)) := by
  unfold keySort
  change Poly (fun xs : List (ℕ × α) => ((List.range ((xs.map Prod.fst).foldl max 0+1)).map
    (fun k => xs.filter (fun x => equal x.1 k))).flatten)
  apply Poly.flatten.comp
  apply Poly.mapFn (f := fun q : List (ℕ × α) × ℕ => q.1.filter (fun x => equal x.1 q.2))
  · exact Poly.filterFn (p := fun q : (List (ℕ × α) × ℕ) × (ℕ × α) => equal q.2.1 q.1.2)
      (by fun_prop) (by fun_prop)
  · have hm : Poly (fun xs : List (ℕ × α) => (xs.map Prod.fst).foldl max 0) :=
      Poly.maxFold.comp (Poly.map Poly.fst)
    fun_prop
end Superstring.BitCode


namespace Superstring.WindowCode
open BitCode Hierarchical WalkCode

def mass (W : List Window) : ℕ := (W.map (fun v => v.1.natAbs+v.2.natAbs)).sum
def windowSort (W : List Window) : List Window :=
  (keySort (W.map (fun v => ((v.1+v.2+(mass W : ℤ)).toNat,v)))).map Prod.snd

theorem mass_bound {W : List Window} {v : Window} (hv : v ∈ W) :
    0 ≤ v.1+v.2+(mass W : ℤ) := by
  have h := List.le_sum_of_mem (List.mem_map.mpr ⟨v,hv,rfl⟩ :
    v.1.natAbs+v.2.natAbs ∈ W.map (fun v => v.1.natAbs+v.2.natAbs))
  change v.1.natAbs+v.2.natAbs ≤ mass W at h
  have h₁ := Int.le_natAbs (a := -v.1)
  have h₂ := Int.le_natAbs (a := -v.2)
  simp only [Int.natAbs_neg] at h₁ h₂
  omega

theorem mem_windowSort (W : List Window) (v : Window) : v ∈ windowSort W ↔ v ∈ W := by
  simp only [windowSort,List.mem_map,mem_keySort]
  constructor
  · rintro ⟨x,⟨y,hy,rfl⟩,rfl⟩; exact hy
  · intro hv; exact ⟨_,⟨v,hv,rfl⟩,rfl⟩

theorem ordered_windowSort (W : List Window)
    (hc : ∀ u ∈ W, ∀ v ∈ W, ordered u v ∨ ordered v u) :
    (windowSort W).Pairwise ordered := by
  apply List.pairwise_map.mpr
  apply (pairwise_keySort _).imp_of_mem
  intro x y hx hy hxy
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ((mem_keySort _ _).mp hx)
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ((mem_keySort _ _).mp hy)
  have hn₁ := mass_bound hu
  have hn₂ := mass_bound hv
  dsimp only at hxy ⊢
  rcases hc u hu v hv with hh | hh
  · exact hh
  · rcases hh with ⟨hs,he⟩
    constructor <;> omega

@[fun_prop] theorem poly_mass : Poly mass := by
  unfold mass
  exact Poly.sum.comp (BitCode.Poly.map (f := fun v : Window => v.1.natAbs+v.2.natAbs) (by fun_prop))
@[fun_prop] theorem poly_windowSort : Poly windowSort := by
  unfold windowSort
  apply (BitCode.Poly.map Poly.snd).comp
  apply poly_keySort.comp
  exact Poly.mapFn (f := fun q : List Window × Window =>
      ((q.2.1+q.2.2+(mass q.1 : ℤ)).toNat,q.2)) (by fun_prop) (by fun_prop)

variable {α : Type}
def through (A : ℤ → α) (a b c d : ℤ) (W : List Window) : Walk α :=
  routeList A (a,b) (windowSort W ++ [(c,d)])

theorem through_realizes {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (a b c d : ℤ) (W : List Window)
    (hc : ∀ u ∈ W, ∀ v ∈ W, ordered u v ∨ ordered v u)
    (hv : ∀ u ∈ W, u.1 ≤ u.2 ∧ textWord A u.1 u.2 ∈ V)
    (hab : a ≤ b) (hcd : c ≤ d) (hac : a ≤ c) (hbd : b ≤ d)
    (ha : textWord A a b ∈ V) (hb : textWord A c d ∈ V)
    (bounds : ∀ u ∈ W, a ≤ u.1 ∧ u.1 ≤ c ∧ b ≤ u.2 ∧ u.2 ≤ d) :
    ∃ P : Hierarchical.Path V (textWord A a b) (textWord A c d),
      Path.points P = through A a b c d W ∧ P.cost = (d-b).toNat ∧
      ∀ u ∈ W, P.Visits (textWord A u.1 u.2) := by
  have ho : ((a,b)::(windowSort W ++ [(c,d)])).Pairwise ordered := by
    apply List.pairwise_cons.mpr
    constructor
    · intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · have hh := bounds u ((mem_windowSort W u).mp hu)
        exact ⟨hh.1,hh.2.2.1⟩
      · have he := List.mem_singleton.mp hu; subst u; exact ⟨hac,hbd⟩
    · apply List.pairwise_append.mpr
      refine ⟨ordered_windowSort W hc,by simp,?_⟩
      intro u hu v hv
      have he := List.mem_singleton.mp hv; subst v
      have hh := bounds u ((mem_windowSort W u).mp hu)
      exact ⟨hh.2.1,hh.2.2.2⟩
  have hvalid : ∀ u ∈ (a,b)::(windowSort W ++ [(c,d)]),
      u.1 ≤ u.2 ∧ textWord A u.1 u.2 ∈ V := by
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact ⟨hab,ha⟩
    · rcases List.mem_append.mp hu with hu | hu
      · exact hv u ((mem_windowSort W u).mp hu)
      · have he := List.mem_singleton.mp hu; subst u; exact ⟨hcd,hb⟩
  obtain ⟨P,hP,hcP,hvP⟩ := routeList_realizes closed A letters (a,b) _ ho hvalid
  refine ⟨P.copy rfl (by simp only [List.getLastD_concat]),?_,?_,?_⟩
  · simpa only [points_copy,through] using hP
  · simpa only [Hierarchical.Path.cost_copy,List.getLastD_concat] using hcP
  · intro u hu
    exact (Hierarchical.Path.visits_copy ..).mpr
      (hvP u (List.mem_cons_of_mem _ (List.mem_append_left _ ((mem_windowSort W u).mpr hu))))

variable [Inhabited α] [Coded α]
@[fun_prop] theorem poly_through : Poly (fun q : List α × ℤ × ℤ × ℤ × ℤ × List Window =>
    through (PeriodWord.text q.1) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2) := by
  unfold through
  exact poly_routeList.comp (f := fun q : List α × ℤ × ℤ × ℤ × ℤ × List Window =>
    (q.1,(q.2.1,q.2.2.1),windowSort q.2.2.2.2.2 ++ [(q.2.2.2.1,q.2.2.2.2.1)])) (by fun_prop)
end Superstring.WindowCode


namespace Superstring.BitCode.Poly
variable {α : Type} [Coded α]
@[fun_prop] theorem getLastDWith : Poly (fun q : List α × α => q.1.getLastD q.2) := by
  have h : Poly (fun q : List α × α => q.1.reverse.headD q.2) := by fun_prop
  simpa only [List.headD_eq_head?_getD,List.head?_reverse,List.getLastD_eq_getLast?] using h
end Superstring.BitCode.Poly

namespace Superstring.WindowCode
open Hierarchical WalkCode BitCode
variable {α : Type}

theorem ordered_getLastD (W : List Window) (d : Window) (ho : W.Pairwise ordered) :
    ∀ v ∈ W, ordered v (W.getLastD d) := by
  induction W generalizing d with
  | nil => simp
  | cons w W ih =>
    rw [List.getLastD_cons]
    intro v hv
    obtain ⟨hw,hW⟩ := List.pairwise_cons.mp ho
    rcases List.mem_cons.mp hv with he | hv
    · subst v
      rcases List.mem_cons.mp (List.getLastD_mem_cons (a:=w) (l:=W)) with he | he
      · rw [he]; exact ⟨le_rfl,le_rfl⟩
      · exact hw _ he
    · exact ih w hW v hv

def hostExcursion (A : ℤ → α) (q : ℕ) (a b e : ℤ) (W : List Window) : Walk α :=
  let last := (windowSort W).getLastD (a,b)
  join (join (up A a e b) (through A a b last.1 last.2 W))
    (route A last.1 last.2 (a+q) (e+q))

theorem hostExcursion_realizes {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (q p : ℕ)
    (hp : 0 < p) (per : Function.Periodic A (q : ℤ))
    (a b e : ℤ) (he : a+p < e) (heb : e ≤ b) (hR : textWord A a b ∈ V)
    (hshort : b < a+q+p) (W : List Window)
    (hc : ∀ u ∈ W, ∀ v ∈ W, ordered u v ∨ ordered v u)
    (hb : ∀ v ∈ W, a ≤ v.1 ∧ v.1 ≤ a+q ∧ v.1 ≤ v.2 ∧ b ≤ v.2 ∧ v.2 < a+q+p)
    (hv : ∀ v ∈ W, textWord A v.1 v.2 ∈ V) :
    ∃ P : Hierarchical.Path V (textWord A a e) (textWord A a e),
      Path.points P = hostExcursion A q a b e W ∧ P.cost = q ∧
      P.Visits (textWord A a b) ∧ (∀ d, e ≤ d → d ≤ b → P.Visits (textWord A a d)) ∧
      (∀ v ∈ W, P.Visits (textWord A v.1 v.2)) ∧
      ∃ w, P.Visits w ∧ w.length < p := by
  let last := (windowSort W).getLastD (a,b)
  have hm : last = (a,b) ∨ last ∈ W := by
    rcases List.mem_cons.mp (List.getLastD_mem_cons (a:=(a,b)) (l:=windowSort W)) with hh | hh
    · exact Or.inl hh
    · exact Or.inr ((mem_windowSort W last).mp hh)
  have hlast : a ≤ last.1 ∧ last.1 ≤ a+q ∧ last.1 ≤ last.2 ∧ b ≤ last.2 ∧ last.2 < a+q+p := by
    rcases hm with hh | hh
    · rw [hh]; exact ⟨le_rfl,by omega,by omega,le_rfl,hshort⟩
    · exact hb _ hh
  have hLv : textWord A last.1 last.2 ∈ V := by
    rcases hm with hh | hh
    · rw [hh]; exact hR
    · exact hv _ hh
  have hmax : ∀ v ∈ W, ordered v last := by
    intro v hv
    exact ordered_getLastD _ _ (ordered_windowSort W hc) v ((mem_windowSort W v).mpr hv)
  have hae : a ≤ e := by omega
  have hE : textWord A a e ∈ V := closed hR (textWord_infix A le_rfl hae heb)
  obtain ⟨U,hU,hUc,hUv⟩ := up_realizes closed A hae heb hR
  obtain ⟨Q,hQ,hQc,hQv⟩ := through_realizes closed A letters a b last.1 last.2 W hc
    (fun v hv' => ⟨(hb v hv').2.2.1,hv v hv'⟩) (by omega) hlast.2.2.1
    hlast.1 hlast.2.2.2.1 hR hLv
    (fun v hv' => ⟨(hb v hv').1,(hmax v hv').1,(hb v hv').2.2.2.1,(hmax v hv').2⟩)
  have heq := textWord_translate A q per a e
  obtain ⟨D,hD,hDc,_,w,hw,hwlen⟩ := route_realizes closed A letters hlast.2.2.1
    (show a+(q:ℤ) ≤ e+q by omega) hlast.2.1 (show last.2 ≤ e+q by have := hlast.2.2.2.2; omega)
    hLv (heq.symm ▸ hE)
  refine ⟨((U.trans Q).trans D).copy rfl heq,?_,?_,?_,?_,?_,w,?_,?_⟩
  · simp only [points_copy,Path.points,hU,hQ,hD,hostExcursion,last]
  · simp only [Hierarchical.Path.cost_copy,Hierarchical.Path.cost_trans,hUc,hQc,hDc]
    have := hlast.2.2.2.1
    have := hlast.2.2.2.2
    omega
  · exact (Hierarchical.Path.visits_copy ..).mpr (Or.inl (Or.inl (Hierarchical.Path.visits_end U)))
  · intro d hd hd'
    exact (Hierarchical.Path.visits_copy ..).mpr (Or.inl (Or.inl (hUv d hd hd')))
  · intro v hv
    exact (Hierarchical.Path.visits_copy ..).mpr (Or.inl (Or.inr (hQv v hv)))
  · exact (Hierarchical.Path.visits_copy ..).mpr (Or.inr hw)
  · have := hlast.2.2.2.2
    omega

variable [Inhabited α] [Coded α]
@[fun_prop] theorem poly_hostExcursion : Poly (fun t : List α × ℕ × ℤ × ℤ × ℤ × List Window =>
    hostExcursion (PeriodWord.text t.1) t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2) := by
  unfold hostExcursion
  dsimp only
  have hlast : Poly (fun t : List α × ℕ × ℤ × ℤ × ℤ × List Window =>
      (windowSort t.2.2.2.2.2).getLastD (t.2.2.1,t.2.2.2.1)) :=
    Poly.getLastDWith.comp (f := fun t : List α × ℕ × ℤ × ℤ × ℤ × List Window =>
      (windowSort t.2.2.2.2.2,(t.2.2.1,t.2.2.2.1))) (by fun_prop)
  have hthrough := poly_through.comp
    (f := fun t : List α × ℕ × ℤ × ℤ × ℤ × List Window =>
      (t.1,t.2.2.1,t.2.2.2.1,((windowSort t.2.2.2.2.2).getLastD (t.2.2.1,t.2.2.2.1)).1,
        ((windowSort t.2.2.2.2.2).getLastD (t.2.2.1,t.2.2.2.1)).2,t.2.2.2.2.2)) (by fun_prop)
  fun_prop
end Superstring.WindowCode

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.WindowCode
open Hierarchical WalkCode BitCode
variable {α : Type}
def requestAttachment (A : ℤ → α) (p : ℕ) (a e s h : ℤ) : Walk α :=
  join (route A s h (a+p) (e+p)) (route A (a+p) (e+p) (s+p) (h+p))

theorem requestAttachment_realizes {V : Set (List α)} (closed : SubstringClosed V)
    (A : ℤ → α) (letters : ∀ x, [A x] ∈ V) (p : ℕ)
    (per : Function.Periodic A (p : ℤ))
    {a e s h : ℤ} (hae : a ≤ e) (hsh : s ≤ h)
    (has : a ≤ s) (hsa : s ≤ a+p) (heh : e ≤ h) (hhe : h ≤ e+p)
    (hR : textWord A a e ∈ V) (hQ : textWord A s h ∈ V) :
    ∃ P : Hierarchical.Path V (textWord A s h) (textWord A s h),
      Path.points P = requestAttachment A p a e s h ∧
      P.cost = p ∧ P.Visits (textWord A a e) := by
  have hER := textWord_translate A p per a e
  have hEQ := textWord_translate A p per s h
  obtain ⟨U,hU,hUc,_,_⟩ := route_realizes closed A letters hsh
    (show a+(p:ℤ) ≤ e+p by omega) hsa hhe hQ (hER.symm ▸ hR)
  obtain ⟨D,hD,hDc,_,_⟩ := route_realizes closed A letters
    (show a+(p:ℤ) ≤ e+p by omega) (show s+(p:ℤ) ≤ h+p by omega)
    (show a+(p:ℤ) ≤ s+p by omega) (show e+(p:ℤ) ≤ h+p by omega)
    (hER.symm ▸ hR) (hEQ.symm ▸ hQ)
  refine ⟨(U.trans D).copy rfl hEQ,?_,?_,?_⟩
  · simp only [points_copy,Path.points,hU,hD,requestAttachment]
  · simp only [Hierarchical.Path.cost_copy,Hierarchical.Path.cost_trans,hUc,hDc]
    omega
  · rw [← hER]
    exact (Hierarchical.Path.visits_copy ..).mpr (Or.inl (Hierarchical.Path.visits_end U))

variable [Inhabited α] [Coded α]
@[fun_prop] theorem poly_requestAttachment : Poly (fun q : List α × ℕ × ℤ × ℤ × ℤ × ℤ =>
    requestAttachment (PeriodWord.text q.1) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2) := by
  unfold requestAttachment
  fun_prop
end Superstring.WindowCode


namespace Superstring.WalkCode
open Hierarchical
variable {α : Type}
theorem realizes_spec {V : Set (List α)} {s t : List α} (P : Hierarchical.Path V s t)
    {Q : Walk α} (h : Path.points P = Q) :
    Runs V s t Q ∧ cost Q = P.cost ∧ ∀ w, w ∈ Q ↔ P.Visits w := by
  obtain ⟨hV,hs,ht,hc,hv⟩ := points_spec P
  rw [h] at hV hs ht hc hv
  exact ⟨⟨hV,hs,ht⟩,hc,hv⟩
end Superstring.WalkCode

namespace Superstring.HostCode
open Hierarchical WalkCode WindowCode BitCode
variable {α : Type} [Inhabited α] [DecidableEq α]
abbrev RequestData (α : Type) := List α × Window × Window

def attachment (r : RequestData α) : Walk α :=
  requestAttachment (PeriodWord.text r.1) r.1.length r.2.1.1 r.2.1.2 r.2.2.1 r.2.2.2

def raw (U : List α) (p : ℕ) (a b e : ℤ) (R : List (RequestData α)) : Walk α :=
  rootShort (fill (hostExcursion (PeriodWord.text U) U.length a b e (R.map (·.2.2)))
    (R.map attachment)) p

theorem raw_spec {V : Set (List α)} (closed : SubstringClosed V)
    (U : List α) (letters : ∀ x, [PeriodWord.text U x] ∈ V) (p : ℕ)
    (hp : 0 < p) (a b e : ℤ) (he : a+p < e) (heb : e ≤ b)
    (hR : PeriodWord.window U a b ∈ V) (hshort : b < a+U.length+p)
    (R : List (RequestData α))
    (hc : ∀ r ∈ R, ∀ s ∈ R, ordered r.2.2 s.2.2 ∨ ordered s.2.2 r.2.2)
    (hb : ∀ r ∈ R, a ≤ r.2.2.1 ∧ r.2.2.1 ≤ a+U.length ∧
      r.2.2.1 ≤ r.2.2.2 ∧ b ≤ r.2.2.2 ∧ r.2.2.2 < a+U.length+p)
    (hv : ∀ r ∈ R, PeriodWord.window U r.2.2.1 r.2.2.2 ∈ V)
    (ha : ∀ r ∈ R,
      (∀ x, [PeriodWord.text r.1 x] ∈ V) ∧ r.2.1.1 ≤ r.2.1.2 ∧
      r.2.1.1 ≤ r.2.2.1 ∧ r.2.2.1 ≤ r.2.1.1+r.1.length ∧
      r.2.1.2 ≤ r.2.2.2 ∧ r.2.2.2 ≤ r.2.1.2+r.1.length ∧
      PeriodWord.window r.1 r.2.1.1 r.2.1.2 ∈ V ∧
      PeriodWord.window r.1 r.2.2.1 r.2.2.2 = PeriodWord.window U r.2.2.1 r.2.2.2) :
    Runs V [] [] (raw U p a b e R) ∧
      cost (raw U p a b e R) ≤ U.length + (R.map (fun r => r.1.length)).sum+p ∧
      PeriodWord.window U a b ∈ raw U p a b e R ∧
      (∀ d, e ≤ d → d ≤ b → PeriodWord.window U a d ∈ raw U p a b e R) ∧
      ∀ r ∈ R, PeriodWord.window r.1 r.2.1.1 r.2.1.2 ∈ raw U p a b e R := by
  obtain ⟨P,hP,hPc,hPr,hPv,hPw,x,hx,hxp⟩ := hostExcursion_realizes closed
    (PeriodWord.text U) letters U.length p hp (PeriodWord.periodic U) a b e he heb
    (by simpa only [PeriodWord.window_eq] using hR) hshort (R.map (·.2.2))
    (by intro u hu v hv; obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hu
        obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hv; exact hc r hr s hs)
    (by intro v hv; obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hv; exact hb r hr)
    (by intro v hv'; obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hv'
        simpa only [PeriodWord.window_eq] using hv r hr)
  obtain ⟨hP',hcost,hvis⟩ := realizes_spec P hP
  have hAtt : ∀ r ∈ R, Runs V (PeriodWord.window U r.2.2.1 r.2.2.2)
      (PeriodWord.window U r.2.2.1 r.2.2.2) (attachment r) ∧
      cost (attachment r) = r.1.length ∧
      PeriodWord.window r.1 r.2.1.1 r.2.1.2 ∈ attachment r := by
    intro r hr
    obtain ⟨hl,hle,has,hsa,heh,hhe,hw,heq⟩ := ha r hr
    obtain ⟨Q,hQ,hQc,hQv⟩ := requestAttachment_realizes closed (PeriodWord.text r.1)
      hl r.1.length (PeriodWord.periodic r.1) hle (hb r hr).2.2.1 has hsa heh hhe
      (by simpa only [PeriodWord.window_eq] using hw)
      (by have hh : PeriodWord.window r.1 r.2.2.1 r.2.2.2 ∈ V := heq.symm ▸ hv r hr
          simpa only [PeriodWord.window_eq] using hh)
    obtain ⟨hQ',hcost,hvis⟩ := realizes_spec Q hQ
    rw [← PeriodWord.window_eq,heq] at hQ'
    exact ⟨hQ',hcost.trans hQc,by simpa only [PeriodWord.window_eq,attachment] using (hvis _).mpr hQv⟩
  obtain ⟨hF,hFc,hFv⟩ := fill_spec _ (R.map attachment) hP'
    (by intro Q hQ; obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hQ; exact ⟨_,(hAtt r hr).1⟩)
    (by intro Q hQ; obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hQ
        exact ⟨_,(hvis _).mpr (hPw _ (List.mem_map.mpr ⟨r,hr,rfl⟩)),
          by simpa only [PeriodWord.window_eq] using List.mem_of_head? (hAtt r hr).1.2.1⟩)
  have hsum : ((R.map attachment).map cost).sum = (R.map (fun r => r.1.length)).sum := by
    rw [List.map_map]
    congr 1
    exact List.map_congr_left (fun r hr => (hAtt r hr).2.1)
  obtain ⟨hQ,hQc,hQv⟩ := rootShort_spec closed hF p
    ⟨x,(hFv x).mpr (Or.inl ((hvis x).mpr hx)),hxp.le⟩
  refine ⟨hQ,?_,?_,?_,?_⟩
  · rw [hFc,hcost,hPc,hsum] at hQc
    exact hQc
  · apply hQv
    simpa only [PeriodWord.window_eq] using (hFv _).mpr (Or.inl ((hvis _).mpr hPr))
  · intro d hd hd'
    apply hQv
    simpa only [PeriodWord.window_eq] using (hFv _).mpr (Or.inl ((hvis _).mpr (hPv d hd hd')))
  · intro r hr
    apply hQv
    exact (hFv _).mpr (Or.inr ⟨_,List.mem_map.mpr ⟨r,hr,rfl⟩,(hAtt r hr).2.2⟩)

variable [Coded α]
omit [DecidableEq α] in
@[fun_prop] theorem poly_attachment : Poly (attachment : RequestData α → Walk α) := by
  unfold attachment
  exact poly_requestAttachment.comp (f := fun r : RequestData α =>
    (r.1,r.1.length,r.2.1.1,r.2.1.2,r.2.2.1,r.2.2.2)) (by fun_prop)
@[fun_prop] theorem poly_raw : Poly (fun t : List α × ℕ × ℤ × ℤ × ℤ × List (RequestData α) =>
    raw t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2) := by
  unfold raw
  have hW : Poly (fun t : List α × ℕ × ℤ × ℤ × ℤ × List (RequestData α) => t.2.2.2.2.2.map (·.2.2)) :=
    (BitCode.Poly.map (show Poly (fun r : RequestData α => r.2.2) from by fun_prop)).comp (by fun_prop)
  have hH := poly_hostExcursion.comp
    (f := fun t : List α × ℕ × ℤ × ℤ × ℤ × List (RequestData α) =>
      (t.1,t.1.length,t.2.2.1,t.2.2.2.1,t.2.2.2.2.1,t.2.2.2.2.2.map (·.2.2)))
    (by fun_prop)
  have hA := (BitCode.Poly.map poly_attachment).comp (f := fun t : List α × ℕ × ℤ × ℤ × ℤ × List (RequestData α) => t.2.2.2.2.2) (by fun_prop)
  fun_prop
end Superstring.HostCode


namespace Superstring.PeriodWord
open Hierarchical BitCode
variable {α : Type} [Inhabited α]
def shift (U : List α) (d : ℤ) : List α := window U (-d) (-d+U.length)
@[simp] theorem length_shift (U : List α) (d : ℤ) : (shift U d).length = U.length := by
  simp only [shift,window_eq,textWord,List.length_ofFn]
  omega
theorem text_shift {U : List α} (hp : 0 < U.length) (d : ℤ) :
    text (shift U d) = fun x => text U (x-d) := by
  apply eq_of_prefix _ _ (by simpa using hp)
  · intro x
    simpa only [length_shift,add_sub_right_comm] using periodic U (x-d)
  · intro i hi
    simp only [length_shift] at hi
    simp only [shift,window_eq,textWord,List.getElem_ofFn]
    congr 1
    omega
variable [Coded α]
@[fun_prop] theorem poly_shift : Poly (fun q : List α × ℤ => shift q.1 q.2) := by
  unfold shift
  fun_prop
end Superstring.PeriodWord

namespace Superstring.HostCode
open Hierarchical WalkCode WindowCode BitCode
variable {α : Type} [Inhabited α] [DecidableEq α]
abbrev Entry (α : Type) := ℕ × List α × ℤ × ℤ × ℤ
namespace Entry
def tag (e : Entry α) := e.1
def word (e : Entry α) := e.2.1
def start (e : Entry α) := e.2.2.1
def stop (e : Entry α) := e.2.2.2.1
def req (e : Entry α) := e.2.2.2.2
def target (q : ℕ) (b e : Entry α) : RequestData α :=
  (e.word,(e.start,e.req),(min (e.start+e.word.length) (b.start+q),max e.req b.stop))
def shift (e : Entry α) (d : ℤ) : Entry α :=
  (e.tag,PeriodWord.shift e.word d,e.start+d,e.stop+d,e.req+d)
end Entry

def later (b : Entry α) (E : List (Entry α)) : List (Entry α) :=
  E.filter (fun e => !(equal e.tag b.tag))
def normalized (U : List α) (b : Entry α) (E : List (Entry α)) : Walk α :=
  raw U b.word.length b.start b.stop b.req ((later b E).map (Entry.target U.length b))

variable [Coded α]
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem Entry.poly_tag : Poly (Entry.tag : Entry α → ℕ) := by unfold tag; fun_prop
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem Entry.poly_word : Poly (Entry.word : Entry α → List α) := by unfold word; fun_prop
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem Entry.poly_start : Poly (Entry.start : Entry α → ℤ) := by unfold start; fun_prop
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem Entry.poly_stop : Poly (Entry.stop : Entry α → ℤ) := by unfold stop; fun_prop
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem Entry.poly_req : Poly (Entry.req : Entry α → ℤ) := by unfold req; fun_prop
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem Entry.poly_target : Poly (fun q : ℕ × Entry α × Entry α => Entry.target q.1 q.2.1 q.2.2) := by
  unfold target
  fun_prop
omit [DecidableEq α] in
@[fun_prop] theorem Entry.poly_shift : Poly (fun q : Entry α × ℤ => Entry.shift q.1 q.2) := by
  unfold shift
  fun_prop
omit [Inhabited α] [DecidableEq α] in
@[fun_prop] theorem poly_later : Poly (fun q : Entry α × List (Entry α) => later q.1 q.2) := by
  unfold later
  exact BitCode.Poly.filterFn (p := fun q : (Entry α × List (Entry α)) × Entry α =>
    !(equal q.2.tag q.1.1.tag)) (by fun_prop) (by fun_prop)
@[fun_prop] theorem poly_normalized : Poly (fun q : List α × Entry α × List (Entry α) => normalized q.1 q.2.1 q.2.2) := by
  have ht : Poly (fun q : List α × Entry α × List (Entry α) =>
      (later q.2.1 q.2.2).map (Entry.target q.1.length q.2.1)) := by
    apply BitCode.Poly.mapFn (f := fun q : (List α × Entry α × List (Entry α)) × Entry α =>
      Entry.target q.1.1.length q.1.2.1 q.2)
    · exact Entry.poly_target.comp (f := fun q : (List α × Entry α × List (Entry α)) × Entry α =>
        (q.1.1.length,q.1.2.1,q.2)) (by fun_prop)
    · fun_prop
  unfold normalized
  exact poly_raw.comp (f := fun q : List α × Entry α × List (Entry α) =>
    (q.1,q.2.1.word.length,q.2.1.start,q.2.1.stop,q.2.1.req,
      (later q.2.1 q.2.2).map (Entry.target q.1.length q.2.1))) (by fun_prop)
end Superstring.HostCode


namespace Superstring.Hierarchical
variable {α ι κ : Type} {V : Set (List α)} {A : ℤ → α} {q : ℕ}

theorem hosted_targets_chain (D : Layer V A q) (H : ι → HostedGroup D)
    (g : κ → ι) (R : ∀ i, (H (g i)).Request)
    (different : ∀ i j, i ≠ j → ∀ c, (H i).text ≠ fun x => (H j).text (x+c))
    (T b : ℤ) (i j : κ) :
    (min ((H (g i)).start+(H (g i)).period) T ≤ min ((H (g j)).start+(H (g j)).period) T ∧
      max (R i).stop b ≤ max (R j).stop b) ∨
    (min ((H (g j)).start+(H (g j)).period) T ≤ min ((H (g i)).start+(H (g i)).period) T ∧
      max (R j).stop b ≤ max (R i).stop b) := by
  have raw (i j : κ) (hij : g i ≠ g j)
      (ha : (H (g i)).start ≤ (H (g j)).start)
      (hb : (H (g i)).stop ≤ (H (g j)).stop) :
      (H (g i)).start + (H (g i)).period ≤ (H (g j)).start + (H (g j)).period ∧
      (R i).stop ≤ (R j).stop := by
    have hd : (H (g i)).text ≠ (H (g j)).text := by
      simpa only [add_zero] using different (g i) (g j) hij 0
    have hov := (H (g i)).overlap_lt (H (g j)) ha hb hd
    have hlong := (R i).long
    have hmargin := (R i).margin
    have hlong' := (R j).long
    constructor <;> omega
  have hc :
      ((H (g i)).start + (H (g i)).period ≤ (H (g j)).start + (H (g j)).period ∧
        (R i).stop ≤ (R j).stop) ∨
      ((H (g j)).start + (H (g j)).period ≤ (H (g i)).start + (H (g i)).period ∧
        (R j).stop ≤ (R i).stop) := by
    by_cases he : g i = g j
    · rcases le_total (R i).stop (R j).stop with hr | hr
      · exact Or.inl ⟨by rw [he], hr⟩
      · exact Or.inr ⟨by rw [he], hr⟩
    · by_cases ha : (H (g i)).start < (H (g j)).start
      · exact Or.inl (raw i j he ha.le
          (D.window_order (H (g i)).le_last (H (g j)).first_le ha))
      · by_cases hb : (H (g j)).start < (H (g i)).start
        · exact Or.inr (raw j i (Ne.symm he) hb.le
            (D.window_order (H (g j)).le_last (H (g i)).first_le hb))
        · rcases le_total (H (g i)).stop (H (g j)).stop with hs | hs
          · exact Or.inl (raw i j he (by omega) hs)
          · exact Or.inr (raw j i (Ne.symm he) (by omega) hs)
  rcases hc with hc | hc
  · exact Or.inl ⟨min_le_min_right _ hc.1, max_le_max_right _ hc.2⟩
  · exact Or.inr ⟨min_le_min_right _ hc.1, max_le_max_right _ hc.2⟩

theorem hosted_target_bounds (D : Layer V A q) (hq : 0 < q)
    (per : Function.Periodic A (q : ℤ)) (H J : HostedGroup D) (R : J.Request)
    (hmin : H.period ≤ J.period)
    (ho : H.start ≤ J.start ∧ J.start ≤ H.start+q ∧ H.stop ≤ J.stop ∧ J.stop ≤ H.stop+q)
    (hd : H.text ≠ J.text) (hd' : J.text ≠ fun x => H.text (x-q)) :
    let s := min (J.start+J.period) (H.start+q)
    let h := max R.stop H.stop
    J.start ≤ s ∧ s ≤ J.start+J.period ∧ s ≤ h ∧ h ≤ J.stop ∧ R.stop ≤ h ∧
      h ≤ R.stop+J.period ∧ H.start ≤ s ∧ s ≤ H.start+q ∧ H.stop ≤ h ∧ h < H.start+q+H.period := by
  have hl := H.overlap_lt J ho.1 ho.2.2.1 hd
  have hr := J.next_overlap_lt H per ho.2.1 ho.2.2.2 hd'
  have hbase : H.stop < H.start+q+H.period := by
    have hh := H.length_lt hq per
    omega
  exact host_target_bounds H.start H.stop J.start J.stop R.stop (H.start+q) H.period J.period
    hmin ho.1 ho.2.1 ho.2.2.1 R.long R.margin hl hr hbase
end Superstring.Hierarchical

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.HostCode
open Hierarchical WalkCode WindowCode BitCode
variable {α ι κ : Type} [Inhabited α] [DecidableEq α] {V : Set (List α)}

theorem filter_sum_reserve (I : List κ) (P : κ → Bool) (weight : κ → ℕ) (i : κ)
    (hi : i ∈ I) (hp : P i = false) :
    weight i + ((I.filter P).map weight).sum ≤ (I.map weight).sum := by
  have hb (L : List κ) : ((L.filter P).map weight).sum ≤ (L.map weight).sum := by
    induction L with
    | nil => simp
    | cons j L ih =>
      cases h : P j <;> simp only [List.filter_cons,h,Bool.false_eq_true,↓reduceIte,
        List.map_cons,List.sum_cons] <;> omega
  induction I with
  | nil => simp at hi
  | cons j I ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · simp only [List.filter_cons,hp,Bool.false_eq_true,↓reduceIte,List.map_cons,List.sum_cons]
      exact Nat.add_le_add_left (hb I) _
    · have hh := ih hi
      cases h : P j <;> simp only [List.filter_cons,h,Bool.false_eq_true,↓reduceIte,
        List.map_cons,List.sum_cons] <;> omega

omit [DecidableEq α] in
def entryOf {A : ℤ → α} {q : ℕ} {D : Layer V A q} (H : ι → HostedGroup D)
    (g : κ → ι) (R : ∀ i, (H (g i)).Request) (W : ι → List α) (tag : ι → ℕ) (i : κ) : Entry α :=
  (tag (g i),W (g i),(H (g i)).start,(H (g i)).stop,(R i).stop)

theorem normalized_spec {A : ℤ → α} {q : ℕ} (closed : SubstringClosed V)
    (D : Layer V A q) (hq : 0 < q) (per : Function.Periodic A (q : ℤ))
    (letters : ∀ x, [A x] ∈ V) (H : ι → HostedGroup D) (g : κ → ι)
    (R : ∀ i, (H (g i)).Request) (W : ι → List α) (tag : ι → ℕ)
    (htag : Function.Injective tag) (U : List α) (hU : U.length = q) (hUt : PeriodWord.text U = A)
    (hW : ∀ j, (W j).length = (H j).period) (hWt : ∀ j, PeriodWord.text (W j) = (H j).text)
    (child_letters : ∀ j x, [(H j).text x] ∈ V)
    (different : ∀ i j, i ≠ j → ∀ c, (H i).text ≠ fun x => (H j).text (x+c))
    (I : List κ) (i₀ : κ) (hi₀ : i₀ ∈ I)
    (hmin : ∀ i ∈ I, (H (g i₀)).period ≤ (H (g i)).period)
    (hreq : ∀ i ∈ I, g i = g i₀ → (R i₀).stop ≤ (R i).stop)
    (horder : ∀ i ∈ I,
      (H (g i₀)).start ≤ (H (g i)).start ∧ (H (g i)).start ≤ (H (g i₀)).start+q ∧
      (H (g i₀)).stop ≤ (H (g i)).stop ∧ (H (g i)).stop ≤ (H (g i₀)).stop+q) :
    let E := entryOf H g R W tag
    Runs V [] [] (normalized U (E i₀) (I.map E)) ∧
      cost (normalized U (E i₀) (I.map E)) ≤ q+(I.map (fun i => (H (g i)).period)).sum ∧
      textWord A (H (g i₀)).start (H (g i₀)).stop ∈ normalized U (E i₀) (I.map E) ∧
      ∀ i ∈ I, textWord (H (g i)).text (H (g i)).start (R i).stop ∈ normalized U (E i₀) (I.map E) := by
  classical
  let E := entryOf H g R W tag
  let J := I.filter (fun i => decide (g i ≠ g i₀))
  have hJ (i : κ) : i ∈ J ↔ i ∈ I ∧ g i ≠ g i₀ := by simp [J]
  let s := fun i => min ((H (g i)).start+(H (g i)).period) ((H (g i₀)).start+q)
  let h := fun i => max (R i).stop (H (g i₀)).stop
  let F := fun i => (W (g i),((H (g i)).start,(R i).stop),(s i,h i))
  have hmap : (later (E i₀) (I.map E)).map (Entry.target U.length (E i₀)) = J.map F := by
    have hl : later (E i₀) (I.map E) = J.map E := by
      unfold later J
      rw [List.filter_map]
      congr 1
      apply congrArg (fun f => I.filter f)
      funext i
      simp [E,entryOf,Entry.tag,equal,htag.eq_iff]
    rw [hl,List.map_map]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply,E,entryOf,Entry.target,Entry.word,Entry.start,Entry.req,Entry.stop,hU,hW,F,s,h]
  have hb (i : κ) (hi : i ∈ J) :
      (H (g i)).start ≤ s i ∧ s i ≤ (H (g i)).start+(H (g i)).period ∧
      s i ≤ h i ∧ h i ≤ (H (g i)).stop ∧ (R i).stop ≤ h i ∧
      h i ≤ (R i).stop+(H (g i)).period ∧ (H (g i₀)).start ≤ s i ∧
      s i ≤ (H (g i₀)).start+q ∧ (H (g i₀)).stop ≤ h i ∧ h i < (H (g i₀)).start+q+(H (g i₀)).period := by
    obtain ⟨hiI,hne⟩ := (hJ i).mp hi
    exact hosted_target_bounds D hq per _ _ (R i) (hmin i hiI) (horder i hiI)
      (by simpa only [add_zero] using different (g i₀) (g i) (Ne.symm hne) 0)
      (by simpa only [← sub_eq_add_neg] using different (g i) (g i₀) hne (-(q:ℤ)))
  have hv (i : κ) (hi : i ∈ J) : textWord A (s i) (h i) ∈ V :=
    closed (H (g i)).host_mem (textWord_infix A (hb i hi).1 (hb i hi).2.2.1 (hb i hi).2.2.2.1)
  have heq (i : κ) (hi : i ∈ J) : textWord (H (g i)).text (s i) (h i) = textWord A (s i) (h i) :=
    textWord_eq_of_agree (fun x hx hy => (H (g i)).agree x ((hb i hi).1.trans hx) (hy.trans_le (hb i hi).2.2.2.1))
  have hen : (H (g i₀)).start+(H (g i₀)).period < (R i₀).stop := (R i₀).long
  have heb : (R i₀).stop ≤ (H (g i₀)).stop := by have := (R i₀).margin; omega
  have hshort : (H (g i₀)).stop < (H (g i₀)).start+q+(H (g i₀)).period := by
    have hh := (H (g i₀)).length_lt hq per; omega
  obtain ⟨hQ,hQc,hQr,hQv,hQatt⟩ := raw_spec closed U (by simpa only [hUt] using letters)
    (H (g i₀)).period (H (g i₀)).positive (H (g i₀)).start (H (g i₀)).stop (R i₀).stop
    hen heb (by simpa only [PeriodWord.window_eq,hUt] using (H (g i₀)).host_mem)
    (by simpa only [hU] using hshort) (J.map F)
    (by intro r hr t ht; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ht
        exact hosted_targets_chain D H g R different _ _ i j)
    (by intro r hr; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
        dsimp only [F]; rw [hU]
        exact ⟨(hb i hi).2.2.2.2.2.2.1,(hb i hi).2.2.2.2.2.2.2.1,
          (hb i hi).2.2.1,(hb i hi).2.2.2.2.2.2.2.2.1,(hb i hi).2.2.2.2.2.2.2.2.2⟩)
    (by intro r hr; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
        simpa only [F,PeriodWord.window_eq,hUt] using hv i hi)
    (by intro r hr; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
        dsimp only [F]
        simp only [hW,PeriodWord.window_eq,hWt,hUt]
        refine ⟨child_letters _,?_,(hb i hi).1,(hb i hi).2.1,(hb i hi).2.2.2.2.1,
          (hb i hi).2.2.2.2.2.1,(R i).word_mem,heq i hi⟩
        have := (R i).long; omega)
  have hpath : normalized U (E i₀) (I.map E) =
      raw U (H (g i₀)).period (H (g i₀)).start (H (g i₀)).stop (R i₀).stop (J.map F) := by
    rw [normalized,hmap]
    simp only [E,entryOf,Entry.word,Entry.start,Entry.stop,Entry.req,hW]
  change Runs V [] [] (normalized U (E i₀) (I.map E)) ∧ _
  rw [hpath]
  refine ⟨hQ,?_,?_,?_⟩
  · simp only [hU,List.map_map,Function.comp_def,F,hW] at hQc
    have hh := filter_sum_reserve I (fun i => decide (g i ≠ g i₀))
      (fun i => (H (g i)).period) i₀ hi₀ (by simp)
    dsimp only [J,F] at hQc ⊢
    omega
  · simpa only [PeriodWord.window_eq,hUt] using hQr
  · intro i hi
    by_cases hg : g i = g i₀
    · have heq' : textWord (H (g i)).text (H (g i)).start (R i).stop =
          textWord A (H (g i₀)).start (R i).stop := by
        rw [← hg]
        apply textWord_eq_of_agree
        intro x hx hy
        apply (H (g i)).agree x hx
        have := (R i).margin
        omega
      rw [heq']
      have hb' : (R i).stop ≤ (H (g i₀)).stop := by
        have := (R i).margin
        have hs := congrArg (fun j => (H j).stop) hg
        omega
      simpa only [PeriodWord.window_eq,hUt] using hQv _ (hreq i hi hg) hb'
    · have hh := hQatt _ (List.mem_map.mpr ⟨i,(hJ i).mpr ⟨hi,hg⟩,rfl⟩)
      simpa only [F,PeriodWord.window_eq,hWt] using hh
end Superstring.HostCode


namespace Superstring.HostCode
open Hierarchical WalkCode WindowCode BitCode

def normalDelta (q : ℕ) (a b a₀ b₀ : ℤ) : ℤ :=
  let d := a₀+((a-a₀) % (q:ℤ)).toNat-a
  if decide (b₀ ≤ b+d) then d else d+q

@[simp] theorem normalDelta_self (q : ℕ) (a b : ℤ) : normalDelta q a b a b = 0 := by
  simp [normalDelta]

theorem normalDelta_spec {α : Type} {V : Set (List α)} {A : ℤ → α} {q : ℕ}
    (D : Layer V A q) (hq : 0 < q) {a b a₀ b₀ : ℤ}
    (hf : D.first a ≤ b) (hl : b ≤ D.last a)
    (hf₀ : D.first a₀ ≤ b₀) (hl₀ : b₀ ≤ D.last a₀) :
    ∃ m : ℤ, normalDelta q a b a₀ b₀ = m*q ∧
      a₀ ≤ a+m*q ∧ a+m*q ≤ a₀+q ∧ b₀ ≤ b+m*q ∧ b+m*q ≤ b₀+q := by
  let m : ℤ := -((a-a₀)/q)
  let r : ℤ := a+m*q
  let e : ℤ := b+m*q
  have hr : r = a₀+(a-a₀)%q := by
    have hh := Int.emod_add_ediv_mul (a-a₀) (q:ℤ)
    dsimp only [r,m]
    simp only [neg_mul]
    omega
  have hrlo : a₀ ≤ r := by have := Int.emod_nonneg (a-a₀) (show (q:ℤ) ≠ 0 by omega); omega
  have hrhi : r < a₀+q := by have := Int.emod_lt_of_pos (a-a₀) (show (0:ℤ) < q by omega); omega
  have hfe : D.first r ≤ e := by dsimp only [r,e]; rw [D.first_shift_int]; omega
  have hle : e ≤ D.last r := by
    dsimp only [r,e,Layer.last]
    rw [D.shift_int]
    change b ≤ D.z a at hl
    omega
  have hfnext : D.first (a₀+q) ≤ b₀+q := by rw [D.first_shift]; omega
  have hehi : e ≤ b₀+q := D.window_order hle hfnext hrhi
  have hd : a₀+(((a-a₀)%(q:ℤ)).toNat:ℤ)-a = m*q := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
    dsimp only [r] at hr
    omega
  by_cases hb : b₀ ≤ e
  · refine ⟨m,?_,hrlo,hrhi.le,hb,hehi⟩
    simp only [normalDelta,hd,show b₀ ≤ b+m*q from hb,decide_true,↓reduceIte]
  · have hre : r = a₀ := by
      by_contra hn
      have hh := D.window_order hl₀ hfe (by omega : a₀ < r)
      omega
    have hfn : D.first (r+q) ≤ e+q := by rw [D.first_shift]; omega
    have helon : b₀ ≤ e+q := D.window_order hl₀ hfn (by omega)
    refine ⟨m+1,?_,?_,?_,?_,?_⟩
    · simp only [normalDelta,hd,show ¬ b₀ ≤ b+m*q from hb,decide_false,Bool.false_eq_true,↓reduceIte]
      ring
    all_goals dsimp only [r,e] at *; linarith

@[fun_prop] theorem poly_normalDelta : Poly (fun t : ℕ × ℤ × ℤ × ℤ × ℤ =>
    normalDelta t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2) := by
  have hr : Poly (fun t : ℕ × ℤ × ℤ × ℤ × ℤ => ((t.2.1-t.2.2.2.1)%(t.1:ℤ)).toNat) :=
    Poly.modIntNat.comp (f := fun t : ℕ × ℤ × ℤ × ℤ × ℤ => (t.2.1-t.2.2.2.1,t.1)) (by fun_prop)
  unfold normalDelta
  dsimp only
  fun_prop

variable {α : Type} [Inhabited α] [DecidableEq α]
def normalizeEntry (q : ℕ) (base e : Entry α) : Entry α :=
  e.shift (normalDelta q e.start e.stop base.start base.stop)
def requestPath (U : List α) (base : Entry α) (E : List (Entry α)) : Walk α :=
  normalized U base (E.map (normalizeEntry U.length base))
def requestPool (U : List α) (E : List (Entry α)) : List (Walk α) :=
  E.map (fun b => requestPath U b E)
variable [Coded α]
omit [DecidableEq α] in
@[fun_prop] theorem poly_normalizeEntry : Poly (fun t : ℕ × Entry α × Entry α => normalizeEntry t.1 t.2.1 t.2.2) := by
  unfold normalizeEntry
  have hd := poly_normalDelta.comp (f := fun t : ℕ × Entry α × Entry α =>
    (t.1,t.2.2.start,t.2.2.stop,t.2.1.start,t.2.1.stop)) (by fun_prop)
  fun_prop
@[fun_prop] theorem poly_requestPath : Poly (fun t : List α × Entry α × List (Entry α) => requestPath t.1 t.2.1 t.2.2) := by
  have hm : Poly (fun t : List α × Entry α × List (Entry α) => t.2.2.map (normalizeEntry t.1.length t.2.1)) := by
    apply BitCode.Poly.mapFn (f := fun t : (List α × Entry α × List (Entry α)) × Entry α => normalizeEntry t.1.1.length t.1.2.1 t.2)
    · exact poly_normalizeEntry.comp (f := fun t : (List α × Entry α × List (Entry α)) × Entry α =>
        (t.1.1.length,t.1.2.1,t.2)) (by fun_prop)
    · fun_prop
  unfold requestPath
  fun_prop
@[fun_prop] theorem poly_requestPool : Poly (fun t : List α × List (Entry α) => requestPool t.1 t.2) := by
  unfold requestPool
  apply BitCode.Poly.mapFn (f := fun t : (List α × List (Entry α)) × Entry α => requestPath t.1.1 t.2 t.1.2)
  · exact poly_requestPath.comp (f := fun t : (List α × List (Entry α)) × Entry α => (t.1.1,t.2,t.1.2)) (by fun_prop)
  · fun_prop
end Superstring.HostCode


namespace Superstring.PeriodWord
variable {α : Type} [Inhabited α]
@[simp] theorem shift_zero (U : List α) : shift U 0 = U := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [shift,window_eq,Hierarchical.textWord,List.getElem_ofFn,neg_zero,zero_add]
    simp only [text,Int.emod_eq_of_lt (by omega : (0:ℤ) ≤ i) (by omega : (i:ℤ) < U.length),Int.toNat_natCast,
      List.getElem?_eq_getElem hi',Option.getD_some]
end Superstring.PeriodWord

namespace Superstring.HostCode
open Hierarchical WalkCode WindowCode BitCode
variable {α ι κ : Type} [Inhabited α] [DecidableEq α] {V : Set (List α)}

theorem requestPath_spec {A : ℤ → α} {q : ℕ} (closed : SubstringClosed V)
    (D : Layer V A q) (hq : 0 < q) (per : Function.Periodic A (q : ℤ))
    (letters : ∀ x, [A x] ∈ V) (H : ι → HostedGroup D) (g : κ → ι)
    (R : ∀ i, (H (g i)).Request) (W : ι → List α) (tag : ι → ℕ)
    (htag : Function.Injective tag) (U : List α) (hU : U.length = q) (hUt : PeriodWord.text U = A)
    (hW : ∀ j, (W j).length = (H j).period) (hWt : ∀ j, PeriodWord.text (W j) = (H j).text)
    (child_letters : ∀ j x, [(H j).text x] ∈ V)
    (different : ∀ i j, i ≠ j → ∀ c, (H i).text ≠ fun x => (H j).text (x+c))
    (I : List κ) (i₀ : κ) (hi₀ : i₀ ∈ I)
    (hmin : ∀ i ∈ I, (H (g i₀)).period ≤ (H (g i)).period)
    (hreq : ∀ i ∈ I, g i = g i₀ → (R i₀).stop ≤ (R i).stop) :
    let E := entryOf H g R W tag
    Runs V [] [] (requestPath U (E i₀) (I.map E)) ∧
      cost (requestPath U (E i₀) (I.map E)) ≤ q+(I.map (fun i => (H (g i)).period)).sum ∧
      textWord A (H (g i₀)).start (H (g i₀)).stop ∈ requestPath U (E i₀) (I.map E) ∧
      ∀ i ∈ I, textWord (H (g i)).text (H (g i)).start (R i).stop ∈ requestPath U (E i₀) (I.map E) := by
  classical
  let E := entryOf H g R W tag
  let z := g i₀
  have shifts (j : ι) : ∃ m : ℤ,
      normalDelta q (H j).start (H j).stop (H z).start (H z).stop = m*q ∧
      (H z).start ≤ (H j).start+m*q ∧ (H j).start+m*q ≤ (H z).start+q ∧
      (H z).stop ≤ (H j).stop+m*q ∧ (H j).stop+m*q ≤ (H z).stop+q :=
    normalDelta_spec D hq (H j).first_le (H j).le_last (H z).first_le (H z).le_last
  choose m hm hb using shifts
  have hmz : m z = 0 := by
    have hz := hm z
    rw [normalDelta_self] at hz
    have : (0:ℤ) < q := by omega
    nlinarith
  let H' := fun j => (H j).translate per (m j)
  let R' := fun i => (R i).translate per (m (g i))
  let W' := fun j => PeriodWord.shift (W j) (m j*q)
  let E' := entryOf H' g R' W' tag
  have hW' (j : ι) : (W' j).length = (H' j).period := by simp [W',H',HostedGroup.translate,hW]
  have hWt' (j : ι) : PeriodWord.text (W' j) = (H' j).text := by
    dsimp only [W']
    rw [PeriodWord.text_shift (by rw [hW]; exact (H j).positive),hWt]
    rfl
  have hbase : E' i₀ = E i₀ := by
    simp only [E',E,entryOf,H',R',W',HostedGroup.translate,HostedGroup.Request.translate,
      show g i₀ = z from rfl,hmz,zero_mul,PeriodWord.shift_zero,add_zero]
  have hmap (i : κ) : normalizeEntry U.length (E i₀) (E i) = E' i := by
    simp only [normalizeEntry,E,E',entryOf,Entry.start,Entry.stop,hU,show g i₀ = z from rfl,hm]
    rfl
  have hd : ∀ i j, i ≠ j → ∀ c, (H' i).text ≠ fun x => (H' j).text (x+c) := by
    intro i j hij c he
    apply different i j hij (m i*q+c-m j*q)
    funext x
    have hh := congrFun he (x+m i*q)
    change (H i).text (x+m i*q-m i*q) = (H j).text (x+m i*q+c-m j*q) at hh
    have hx : x+m i*q+c-m j*q = x+(m i*q+c-m j*q) := by omega
    simpa only [add_sub_cancel_right,hx] using hh
  have ho : ∀ i ∈ I,
      (H' (g i₀)).start ≤ (H' (g i)).start ∧ (H' (g i)).start ≤ (H' (g i₀)).start+q ∧
      (H' (g i₀)).stop ≤ (H' (g i)).stop ∧ (H' (g i)).stop ≤ (H' (g i₀)).stop+q := by
    intro i _
    simpa only [H',HostedGroup.translate,show g i₀ = z from rfl,hmz,zero_mul,add_zero] using hb (g i)
  have hrq : ∀ i ∈ I, g i = g i₀ → (R' i₀).stop ≤ (R' i).stop := by
    intro i hi hg
    have hh := hreq i hi hg
    change (R i₀).stop+m (g i₀)*q ≤ (R i).stop+m (g i)*q
    have hm' := congrArg m hg
    rw [hm']
    exact Int.add_le_add_right hh _
  obtain ⟨hr,hc,hb',hv⟩ := normalized_spec closed D hq per letters H' g R' W' tag htag U hU hUt
    hW' hWt' (fun j x => child_letters j (x-m j*q)) hd I i₀ hi₀ hmin hrq ho
  have hpath : requestPath U (E i₀) (I.map E) = normalized U (E' i₀) (I.map E') := by
    unfold requestPath
    rw [List.map_map,hbase]
    apply congrArg (normalized U (E i₀))
    apply List.map_congr_left
    intro i _
    exact hmap i
  change Runs V [] [] (requestPath U (E i₀) (I.map E)) ∧ _
  rw [hpath]
  refine ⟨hr,hc,?_,?_⟩
  · have ha : (H' (g i₀)).start = (H (g i₀)).start := by
      simp only [H',HostedGroup.translate,show g i₀ = z from rfl,hmz,zero_mul,add_zero]
    have hb₀ : (H' (g i₀)).stop = (H (g i₀)).stop := by
      simp only [H',HostedGroup.translate,show g i₀ = z from rfl,hmz,zero_mul,add_zero]
    change textWord A (H' (g i₀)).start (H' (g i₀)).stop ∈ normalized U (E' i₀) (I.map E') at hb'
    rwa [ha,hb₀] at hb'
  · intro i hi
    have hh := hv i hi
    have he : textWord (H' (g i)).text (H' (g i)).start (R' i).stop =
        textWord (H (g i)).text (H (g i)).start (R i).stop := by
      change textWord (fun x => (H (g i)).text (x-m (g i)*q))
        ((H (g i)).start+m (g i)*q) ((R i).stop+m (g i)*q) = _
      simpa only [sub_eq_add_neg,add_neg_cancel_right] using
        textWord_reindex (H (g i)).text (-(m (g i)*q))
          ((H (g i)).start+m (g i)*q) ((R i).stop+m (g i)*q)
    rwa [he] at hh
theorem requestPool_complete {A : ℤ → α} {q : ℕ} (closed : SubstringClosed V)
    (D : Layer V A q) (hq : 0 < q) (per : Function.Periodic A (q : ℤ))
    (letters : ∀ x, [A x] ∈ V) (H : ι → HostedGroup D) (g : κ → ι)
    (R : ∀ i, (H (g i)).Request) (W : ι → List α) (tag : ι → ℕ)
    (htag : Function.Injective tag) (U : List α) (hU : U.length = q) (hUt : PeriodWord.text U = A)
    (hW : ∀ j, (W j).length = (H j).period) (hWt : ∀ j, PeriodWord.text (W j) = (H j).text)
    (child_letters : ∀ j x, [(H j).text x] ∈ V)
    (different : ∀ i j, i ≠ j → ∀ c, (H i).text ≠ fun x => (H j).text (x+c))
    (I : List κ) (hne : I ≠ []) :
    ∃ P ∈ requestPool U (I.map (entryOf H g R W tag)),
      Runs V [] [] P ∧ cost P ≤ q+(I.map (fun i => (H (g i)).period)).sum ∧
      (∃ w ∈ D.Content, w ∈ P) ∧
      ∀ i ∈ I, ∃ w ∈ (R i).layer.Content, w ∈ P := by
  classical
  have hne' : I.toFinset.Nonempty := by
    obtain ⟨i,hi⟩ := List.exists_mem_of_ne_nil I hne
    exact ⟨i,List.mem_toFinset.mpr hi⟩
  obtain ⟨i₀,hi₀,hmin⟩ := I.toFinset.exists_min_image (fun i => (H (g i)).period) hne'
  let J := I.toFinset.filter (fun i => g i = g i₀)
  have hj₀ : i₀ ∈ J := by simp [J,hi₀]
  obtain ⟨i₁,hi₁,hr⟩ := J.exists_min_image (fun i => (R i).stop) ⟨i₀,hj₀⟩
  have hi₁I : i₁ ∈ I := List.mem_toFinset.mp (Finset.mem_filter.mp hi₁).1
  have he : g i₁ = g i₀ := (Finset.mem_filter.mp hi₁).2
  have hm : ∀ i ∈ I, (H (g i₁)).period ≤ (H (g i)).period := by
    intro i hi
    rw [he]
    exact hmin i (List.mem_toFinset.mpr hi)
  have hr' : ∀ i ∈ I, g i = g i₁ → (R i₁).stop ≤ (R i).stop := by
    intro i hi hg
    exact hr i (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hi,hg.trans he⟩)
  obtain ⟨hP,hc,hb,hv⟩ := requestPath_spec closed D hq per letters H g R W tag htag U hU hUt
    hW hWt child_letters different I i₁ hi₁I hm hr'
  refine ⟨_,List.mem_map.mpr ⟨_,List.mem_map.mpr ⟨i₁,hi₁I,rfl⟩,rfl⟩,hP,hc,?_,?_⟩
  · exact ⟨_,⟨_,_,(H (g i₁)).first_le,(H (g i₁)).le_last,rfl⟩,hb⟩
  · intro i hi
    exact ⟨_,⟨_,_,(R i).first_le,(R i).le_last,rfl⟩,hv i hi⟩
end Superstring.HostCode


namespace Superstring.LayerArray
open BitCode Hierarchical WalkCode
variable {α ι : Type} [Inhabited α] [DecidableEq α]
abbrev LayerData (α : Type) := List α × List ℕ

def saturateAll (D : List (LayerData α)) (P : Walk α) : Walk α :=
  fill P (D.map (fun d => turn d.1 d.2))

theorem saturateAll_spec {V : Set (List α)} (closed : SubstringClosed V)
    (A : ι → ℤ → α) (p : ι → ℕ) (L : ∀ i, Layer V (A i) (p i))
    (D : ι → LayerData α) (I : List ι) (rep : ∀ i ∈ I, Represents (D i).1 (D i).2 (L i))
    (pos : ∀ i ∈ I, 0 < p i) (per : ∀ i ∈ I, Function.Periodic (A i) (p i : ℤ))
    {P : Walk α} {s t : List α} (hP : Runs V s t P)
    (touch : ∀ i ∈ I, ∃ w ∈ (L i).Content, w ∈ P) :
    Runs V s t (saturateAll (I.map D) P) ∧
      cost (saturateAll (I.map D) P) = cost P+(I.map p).sum ∧
      (∀ w ∈ P, w ∈ saturateAll (I.map D) P) ∧
      ∀ i ∈ I, ∀ w ∈ (L i).Content, w ∈ saturateAll (I.map D) P := by
  have hturn i hi := turn_spec (rep i hi) closed (pos i hi) (per i hi)
  have hm : (I.map D).map (fun d => turn d.1 d.2) = I.map (fun i => turn (D i).1 (D i).2) := List.map_map ..
  obtain ⟨hF,hFc,hFv⟩ := fill_spec P (I.map (fun i => turn (D i).1 (D i).2)) hP
    (by intro Q hQ; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hQ; exact ⟨_,(hturn i hi).1⟩)
    (by intro Q hQ; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hQ
        obtain ⟨w,hw,hwP⟩ := touch i hi
        exact ⟨w,hwP,(hturn i hi).2.2 w hw⟩)
  unfold saturateAll
  rw [hm]
  refine ⟨hF,?_,fun w hw => (hFv w).mpr (Or.inl hw),?_⟩
  · rw [List.map_map] at hFc
    have hh : I.map (fun i => cost (turn (D i).1 (D i).2)) = I.map p :=
      List.map_congr_left (fun i hi => (hturn i hi).2.1)
    exact hFc.trans (congrArg (fun l : List ℕ => cost P+l.sum) hh)
  · intro i hi w hw
    exact (hFv w).mpr (Or.inr ⟨_,List.mem_map.mpr ⟨i,hi,rfl⟩,(hturn i hi).2.2 w hw⟩)

variable [Coded α]
@[fun_prop] theorem poly_saturateAll : Poly (fun q : List (LayerData α) × Walk α => saturateAll q.1 q.2) := by
  unfold saturateAll
  have ht : Poly (fun D : List (LayerData α) => D.map (fun d => turn d.1 d.2)) := BitCode.Poly.map poly_turn
  fun_prop
end Superstring.LayerArray

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.HostCode
open BitCode Hierarchical WalkCode LayerArray
variable {α ι κ : Type} [Inhabited α] [DecidableEq α] {V : Set (List α)}

def completePool (U : List α) (Z : List ℕ) (E : List (Entry α))
    (D : List (LayerData α)) : List (Walk α) :=
  (requestPool U E).map (saturateAll ((U,Z)::D))

theorem completePool_complete {A : ℤ → α} {q : ℕ} (closed : SubstringClosed V)
    (D : Layer V A q) (hq : 0 < q) (per : Function.Periodic A (q : ℤ))
    (letters : ∀ x, [A x] ∈ V) (H : ι → HostedGroup D) (g : κ → ι)
    (R : ∀ i, (H (g i)).Request) (W : ι → List α) (tag : ι → ℕ)
    (htag : Function.Injective tag) (U : List α) (Z : List ℕ) (hD : Represents U Z D)
    (hW : ∀ j, (W j).length = (H j).period) (hWt : ∀ j, PeriodWord.text (W j) = (H j).text)
    (child_letters : ∀ j x, [(H j).text x] ∈ V)
    (different : ∀ i j, i ≠ j → ∀ c, (H i).text ≠ fun x => (H j).text (x+c))
    (A' : κ → ℤ → α) (L : ∀ i, Layer V (A' i) (H (g i)).period)
    (D' : κ → LayerData α) (I : List κ) (hne : I ≠ [])
    (hL : ∀ i ∈ I, Represents (D' i).1 (D' i).2 (L i))
    (hp : ∀ i ∈ I, Function.Periodic (A' i) ((H (g i)).period : ℤ))
    (hc : ∀ i ∈ I, (L i).Content = (R i).layer.Content) :
    ∃ P ∈ completePool U Z (I.map (entryOf H g R W tag)) (I.map D'),
      Runs V [] [] P ∧ cost P ≤ 2*(q+(I.map (fun i => (H (g i)).period)).sum) ∧
      (∀ w ∈ D.Content, w ∈ P) ∧ ∀ i ∈ I, ∀ w ∈ (L i).Content, w ∈ P := by
  obtain ⟨P,hPin,hP,hPc,hPD,hPi⟩ := requestPool_complete closed D hq per letters H g R W tag htag
    U hD.length_eq hD.text_eq hW hWt child_letters different I hne
  let A₁ : Option κ → ℤ → α := fun i => i.elim A A'
  let p₁ : Option κ → ℕ := fun i => i.elim q (fun j => (H (g j)).period)
  let L₁ : ∀ i, Layer V (A₁ i) (p₁ i) := fun i => by cases i with
    | none => exact D
    | some i => exact L i
  let D₁ : Option κ → LayerData α := fun i => i.elim (U,Z) D'
  let I₁ : List (Option κ) := none :: I.map some
  obtain ⟨hS,hSc,_,hSv⟩ := saturateAll_spec closed A₁ p₁ L₁ D₁ I₁
    (by intro i hi; rcases List.mem_cons.mp hi with rfl|hi
        · exact hD
        · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi; exact hL j hj)
    (by intro i hi; rcases List.mem_cons.mp hi with rfl|hi
        · exact hq
        · obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi; exact (H (g j)).positive)
    (by intro i hi; rcases List.mem_cons.mp hi with rfl|hi
        · exact per
        · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi; exact hp j hj)
    hP
    (by intro i hi; rcases List.mem_cons.mp hi with rfl|hi
        · exact hPD
        · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
          change ∃ w ∈ (L j).Content, w ∈ P
          rw [hc j hj]
          exact hPi j hj)
  have hm : I₁.map D₁ = (U,Z)::I.map D' := by simp only [I₁,List.map_cons,List.map_map,D₁,Option.elim_none,Option.elim_some,Function.comp_def]
  have hsum : (I₁.map p₁).sum = q+(I.map (fun i => (H (g i)).period)).sum := by
    simp only [I₁,List.map_cons,List.sum_cons,List.map_map,p₁,Option.elim_none,Option.elim_some,Function.comp_def]
  rw [hm] at hS hSc hSv
  rw [hsum] at hSc
  refine ⟨_,List.mem_map.mpr ⟨P,hPin,rfl⟩,hS,by omega,?_,?_⟩
  · exact hSv none (List.mem_cons_self ..)
  · intro i hi
    exact hSv (some i) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i,hi,rfl⟩))

variable [Coded α]
@[fun_prop] theorem poly_completePool : Poly (fun t : List α × List ℕ × List (Entry α) × List (LayerData α) =>
    completePool t.1 t.2.1 t.2.2.1 t.2.2.2) := by
  unfold completePool
  exact BitCode.Poly.mapFn
    (f := fun t : (List α × List ℕ × List (Entry α) × List (LayerData α)) × Walk α =>
      saturateAll ((t.1.1,t.1.2.1)::t.1.2.2.2) t.2)
    (by fun_prop) (by fun_prop)
end Superstring.HostCode


namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}
abbrev Request := ℕ × ℕ × List ℕ × RecordCode.Code
namespace Request
def source (r : Request) := r.1
def target (r : Request) := r.2.1
def members (r : Request) := r.2.2.1
def code (r : Request) := r.2.2.2
def reserve (X : Env α) (r : Request) := 2*(r.members.length*per X r.source)
def ids (X : Env α) (r : Request) := r.members.map (fun i => r.source*stride X+i)
def entry (X : Env α) (r : Request) (i : ℕ) : HostCode.Entry α :=
  (r.source,PeriodWord.shift (data X r.source).1 (RecordCode.offset r.code),
    RecordCode.start r.code+RecordCode.offset r.code,
    RecordCode.stop r.code+RecordCode.offset r.code,
    GeoCode.first (exits (data X r.source) i) (RecordCode.start r.code)+RecordCode.offset r.code)
end Request

structure RequestWitness {X : Env α} {C : LayerCollection V G} (h : Model X C) (r : Request) where
  source : G
  target : C.Id
  source_eq : h.group source = r.source
  target_eq : h.encode target = r.target
  record : (C.layerAt target).Record (C.text source)
  offset : record.offset = RecordCode.offset r.code
  start : record.start = RecordCode.start r.code
  stop : record.stop = RecordCode.stop r.code
  foreign : C.text source ≠ fun x => C.text target.1 (x+record.offset)
  nonempty : r.members ≠ []
  nodup : r.members.Nodup
  bound : ∀ i ∈ r.members, i < C.size source
  long : ∀ i ∈ r.members, record.start+C.period source < (h.natLayer source i).first record.start
  margin : ∀ i ∈ r.members, (h.natLayer source i).last record.start < record.stop-C.period source

def ValidRequest {X : Env α} {C : LayerCollection V G} (h : Model X C) (r : Request) : Prop :=
  Nonempty (RequestWitness h r)

namespace RequestWitness
variable {X : Env α} {C : LayerCollection V G} {h : Model X C} {r : Request} (w : RequestWitness h r)
include w in
theorem later : per X r.source < per X (owner X r.target) := by
  obtain ⟨i,hi⟩ := List.exists_mem_of_ne_nil r.members w.nonempty
  have hl := w.long i hi
  have hm := w.margin i hi
  have hh := (h.natLayer w.source i).first_le_last w.record.start
  have hr := w.record.length_lt (C.positive w.source) (C.positive w.target.1)
    (C.periodic w.source) (C.periodic w.target.1) w.foreign
  rw [← w.source_eq,← w.target_eq,h.owner_eq,h.per_eq,h.per_eq]
  omega

def hosted : HostedGroup (C.layerAt w.target) where
  text := fun x => C.text w.source (x-w.record.offset)
  period := C.period w.source
  positive := C.positive w.source
  periodic := fun x => by simpa only [add_sub_right_comm] using C.periodic w.source (x-w.record.offset)
  start := w.record.start+w.record.offset
  stop := w.record.stop+w.record.offset
  first_le := w.record.first_le
  le_last := w.record.le_last
  agree := by
    intro x hx hy
    have hh := w.record.agree (x-w.record.offset) (by omega) (by omega)
    simpa only [sub_add_cancel] using hh
  foreign := by
    intro he
    apply w.foreign
    funext x
    simpa only [add_sub_cancel_right] using congrFun he (x+w.record.offset)

def request (i : {j // j ∈ r.members}) : w.hosted.Request where
  layer := (h.natLayer w.source i.val).translate w.record.offset
  stop := (h.natLayer w.source i.val).first w.record.start+w.record.offset
  first_le := by simp [hosted]
  le_last := by
    simp only [hosted,Layer.translate_last,add_sub_cancel_right]
    have hh := (h.natLayer w.source i.val).first_le_last w.record.start
    omega
  long := by
    have hh := w.long i.val i.property
    change w.record.start+w.record.offset+C.period w.source < _
    omega
  margin := by
    have hh := w.margin i.val i.property
    have hf := (h.natLayer w.source i.val).first_le_last w.record.start
    change _ ≤ w.record.stop+w.record.offset-C.period w.source
    omega

theorem data_rep (i : {j // j ∈ r.members}) :
    Represents (UpperCode.lookup (book X) (r.source*stride X+i.val)).1
      (UpperCode.lookup (book X) (r.source*stride X+i.val)).2 (h.natLayer w.source i.val) := by
  rw [← w.source_eq,lookup_encode X _ _ (h.bound _) (lt_of_lt_of_le (w.bound i.val i.property) (h.capacity _))]
  exact h.nat_rep w.source (w.bound i.val i.property)

theorem entry_eq (i : {j // j ∈ r.members}) : Request.entry X r i.val =
    (r.source,PeriodWord.shift (data X r.source).1 w.record.offset,
      w.hosted.start,w.hosted.stop,(w.request i).stop) := by
  simp only [Request.entry,← w.source_eq,← w.offset,← w.start,← w.stop,hosted,request]
  simp only [GeoCode.first,(h.nat_rep w.source (w.bound i.val i.property)).exit_eq,Layer.first]
end RequestWitness
end Superstring.CollectionCode


namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode BlockClose
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}
abbrev Plan (α : Type) := Walk α × List (BlockClose.Block α) × List Request
def planBudget (X : Env α) (o : Plan α) := cost o.1+(o.2.1.map Block.reserve).sum+(o.2.2.map (Request.reserve X)).sum
def hardPlan (X : Env α) (g cut : ℕ) (v : UpperCode.Param) : Plan α :=
  let o := hard X g cut v
  (o.1,o.2.1,if o.2.2.isEmpty then [] else [(g,v.2.1,o.2.2,v.2.2)])
def Covered (X : Env α) (o : Plan α) (i : ℕ) :=
  (∀ w ∈ ls X i, w ∈ o.1) ∨ (∃ b ∈ o.2.1, i ∈ b.members) ∨ ∃ r ∈ o.2.2, i ∈ r.ids X

def GoodPlan {X : Env α} {C : LayerCollection V G} (h : Model X C) (o : Plan α) : Prop :=
  Runs V [] [] o.1 ∧ (∀ b ∈ o.2.1, ValidBlock V (ids X) (ls X) (owner X) (per X) (rank X) b) ∧
    ∀ r ∈ o.2.2, ValidRequest h r
namespace Model
variable {X : Env α} {C : LayerCollection V G} (h : Model X C)
theorem hardPlan_spec (closed : SubstringClosed V) (g : G) (cut : ℕ) (v : UpperCode.Param)
    (hcut : cut < C.size g) (hv : v.2.1 ∈ ids X)
    (ht : UpperCode.test (data X (h.group g)) (book X) cut (phase X (h.group g)) v = true)
    (hf : UpperCode.foreign (data X (h.group g)) (book X) v = true) :
    let o := hardPlan X (h.group g) cut v
    GoodPlan h o ∧ planBudget X o ≤ 2*((C.size g-cut)*C.period g) ∧
      (∀ i : Fin (C.size g), cut ≤ i.val → Covered X o (h.encode ⟨g,i⟩)) ∧
      (∀ r ∈ o.2.2, r.source = h.group g) ∧ o.2.2.length ≤ 1 := by
  obtain ⟨hr,hb,hblocks,hcov,hsub,d,R,hd,hoff,ha,hb',hne,hm⟩ := h.hard_spec closed g cut v hcut hv ht hf
  let p := hard X (h.group g) cut v
  have hsub' : p.2.2.Sublist (UpperCode.upper (C.size g) cut) := hsub
  have hlength : p.2.2.length*C.period g = p.2.2.length*per X (h.group g) := by rw [h.per_eq]
  by_cases he : p.2.2 = []
  · have hoja : hardPlan X (h.group g) cut v = (p.1,p.2.1,[]) := by simp only [hardPlan,p,he,List.isEmpty_nil,↓reduceIte]
    rw [hoja]
    refine ⟨⟨hr,hblocks,by simp⟩,?_,?_,by simp,by simp⟩
    · simpa only [planBudget,DistributeCode.budget,show (hard X (h.group g) cut v).2.2=[] from he,
        List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.mul_zero,Nat.add_zero] using hb
    · intro i hi
      rcases hcov i hi with hh|hh|hh
      · exact Or.inl hh
      · exact Or.inr (Or.inl hh)
      · simp only [show (hard X (h.group g) cut v).2.2=[] from he,List.not_mem_nil] at hh
  · let r : Request := (h.group g,v.2.1,p.2.2,v.2.2)
    have hoja : hardPlan X (h.group g) cut v = (p.1,p.2.1,[r]) := by
      simp only [hardPlan,show (hard X (h.group g) cut v).2.2=p.2.2 from rfl,
        List.isEmpty_iff,he,↓reduceIte,r,p]
    have hw : ValidRequest h r := ⟨{
      source := g, target := d, source_eq := rfl, target_eq := hd, record := R,
      offset := hoff, start := ha, stop := hb', foreign := hne, nonempty := he,
      nodup := (List.Nodup.filter _ List.nodup_range).sublist hsub',
      bound := fun i hi => (UpperCode.mem_upper _ _ i).mp (hsub'.subset hi) |>.2,
      long := fun i hi => (hm i hi).1,
      margin := fun i hi => (hm i hi).2 }⟩
    rw [hoja]
    refine ⟨⟨hr,hblocks,?_⟩,?_,?_,?_,by simp⟩
    · intro s hs
      exact List.mem_singleton.mp hs ▸ hw
    · simpa only [planBudget,List.map_singleton,List.sum_singleton,Request.reserve,Request.members,Request.source,r,
        h.per_eq,DistributeCode.budget] using hb
    · intro i hi
      rcases hcov i hi with hh|hh|hh
      · exact Or.inl hh
      · exact Or.inr (Or.inl hh)
      · exact Or.inr (Or.inr ⟨r,List.mem_singleton_self _,List.mem_map.mpr ⟨i.val,hh,rfl⟩⟩)
    · intro s hs
      exact List.mem_singleton.mp hs ▸ rfl
end Model
end Superstring.CollectionCode

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode UpperCode
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}
def complete (X : Env α) (g cut M : ℕ) (P : Walk α) : Plan α :=
  let D := data X g
  let m := D.2.length
  let p := D.1.length
  let t := phase X g
  let H := GeoCode.first (exits D (m-1)) t
  let I := upper m cut
  if m ≤ cut then (P,[],[])
  else if H-t ≤ ((m-cut)*p : ℕ) then
    (join P (rootUpper D I (m-1) t),[],[])
  else if 0 < cut ∧ H-GeoCode.exit (exits D (cut-1)) t ≤ ((m-cut)*p : ℕ) then
    (attachBand D I (cut-1) (m-1) P t,[],[])
  else
    let v := choose D (book X) (ids X) cut M t (foreign D (book X))
    let o := hardPlan X g cut v
    (join P o.1,o.2.1,o.2.2)
namespace Model
variable {X : Env α} {C : LayerCollection V G} (h : Model X C)
theorem first_eq (g : G) {i : ℕ} (hi : i < C.size g) (t : ℤ) :
    GeoCode.first (exits (data X (h.group g)) i) t = (h.natLayer g i).first t := by
  simp only [GeoCode.first,(h.nat_rep g hi).exit_eq,Layer.first]
theorem last_eq (g : G) {i : ℕ} (hi : i < C.size g) (t : ℤ) :
    GeoCode.exit (exits (data X (h.group g)) i) t = (h.natLayer g i).last t :=
  congrFun (h.nat_rep g hi).exit_eq t

theorem complete_spec (closed : SubstringClosed V) (supply : C.RecordSupply)
    (M : ℕ) (len : ∀ w ∈ V, w.length ≤ M) (g : G) (cut : ℕ) (hcut : cut ≤ C.size g)
    (P : Walk α) (hP : Runs V [] [] P)
    (hp : ∀ i : Fin (C.size g), i.val < cut → ∀ w ∈ (C.layer g i).Content, w ∈ P) :
    let o := complete X (h.group g) cut M P
    GoodPlan h o ∧ planBudget X o ≤ cost P+2*((C.size g-cut)*C.period g) ∧
      (∀ w ∈ P, w ∈ o.1) ∧
      (∀ i : Fin (C.size g), cut ≤ i.val → Covered X o (h.encode ⟨g,i⟩)) ∧
      (∀ r ∈ o.2.2, r.source = h.group g) ∧ o.2.2.length ≤ 1 := by
  let m := C.size g
  let p := C.period g
  let t := C.distinguished g
  let top : Fin (C.size g) := ⟨C.size g-1,by have := C.nonempty g; omega⟩
  have ht : (h.natLayer g (C.size g-1)) = C.layer g top := by
    exact h.natLayer_fin g top
  have htop : C.size g-1 < C.size g := top.isLt
  let I := upper (C.size g) cut
  have hib (i : ℕ) (hi : i ∈ I) : i < C.size g := ((mem_upper ..).mp hi).2
  have hirep := fun i hi => h.nat_rep g (hib i hi)
  have hie : I.length = C.size g-cut := length_upper ..
  have hu (i : ℕ) (hi : i ∈ I) (x : ℤ) : (h.natLayer g i).z x ≤ (h.natLayer g (C.size g-1)).z x :=
    h.nat_order g (by have := hib i hi; omega) x
  have hrefl (Q : Walk α) (hQ : Runs V [] [] Q) : GoodPlan h (Q,[],[]) := ⟨hQ,by simp,by simp⟩
  have heasy (Q : Walk α) (hQ : Runs V [] [] Q)
      (hc : cost Q ≤ cost P+2*((C.size g-cut)*C.period g))
      (hv : ∀ w ∈ P, w ∈ Q)
      (hi : ∀ i : Fin (C.size g), cut ≤ i.val → ∀ w ∈ (C.layer g i).Content, w ∈ Q) :
      GoodPlan h (Q,[],[]) ∧ planBudget X (Q,[],[]) ≤ cost P+2*((C.size g-cut)*C.period g) ∧
        (∀ w ∈ P, w ∈ Q) ∧
        (∀ i : Fin (C.size g), cut ≤ i.val → Covered X (Q,[],[]) (h.encode ⟨g,i⟩)) ∧
        (∀ r ∈ ([] : List Request), r.source = h.group g) ∧ ([] : List Request).length ≤ 1 := by
    refine ⟨hrefl Q hQ,by simpa only [planBudget,List.map_nil,List.sum_nil,Nat.add_zero] using hc,hv,?_,by simp,by simp⟩
    intro i hi' ; exact Or.inl (fun w hw => hi i hi' w ((h.content_iff ⟨g,i⟩ w).mp hw))
  unfold complete
  simp only [h.size,show (data X (h.group g)).1.length = C.period g from h.per_eq g,h.phase_eq]
  by_cases hem : C.size g ≤ cut
  · rw [ite_eq_left hem]
    apply heasy P hP (by omega) (fun _ hw => hw)
    intro i hi; have := i.isLt; omega
  · rw [ite_eq_right hem]
    have hct : cut < C.size g := by omega
    rw [h.first_eq g htop,ht]
    by_cases he : (C.layer g top).first (C.distinguished g)-C.distinguished g ≤ ((C.size g-cut)*C.period g : ℕ)
    · rw [ite_eq_left he]
      obtain ⟨hr,hc,hv⟩ := rootUpper_spec (h.natLayer g) hirep (h.nat_rep g htop) hu
        closed (C.positive g) (C.periodic g) (C.distinguished g) (by simpa only [hie,ht] using he)
      apply heasy _ (runs_join hP hr)
      · rw [cost_join _ _ [] hP.2.2 hr.2.1]
        rw [hie] at hc
        omega
      · exact fun w hw => (mem_join hP.2.2 hr.2.1).mpr (Or.inl hw)
      · intro i hi w hw
        apply (mem_join hP.2.2 hr.2.1).mpr
        exact Or.inr (hv i.val ((mem_upper ..).mpr ⟨hi,i.isLt⟩) w ((h.natLayer_fin g i).symm ▸ hw))
    · rw [ite_eq_right he]
      by_cases hb : 0 < cut ∧ (C.layer g top).first (C.distinguished g) -
          GeoCode.exit (exits (data X (h.group g)) (cut-1)) (C.distinguished g) ≤ ((C.size g-cut)*C.period g : ℕ)
      · rw [ite_eq_left hb]
        have hl : cut-1 < C.size g := by omega
        have hlo (i : ℕ) (hi : i ∈ I) (x : ℤ) :
            (h.natLayer g (cut-1)).z x ≤ (h.natLayer g i).z x :=
          h.nat_order g (by have := ((mem_upper ..).mp hi).1; omega) x
        have hband := hb.2
        rw [h.last_eq g hl] at hband
        obtain ⟨hr,hc,hv,hi⟩ := attachBand_spec (h.natLayer g) hirep (h.nat_rep g hl) (h.nat_rep g htop)
          hlo hu (h.nat_order g (by omega)) closed (C.positive g) (C.periodic g) (C.letters closed g)
          (C.distinguished g) (by simpa only [ht,hie] using hband) hP
          (by simpa only [h.natLayer_fin g (⟨cut-1,hl⟩ : Fin (C.size g))] using hp ⟨cut-1,hl⟩ (by change cut-1<cut; omega))
        apply heasy _ hr (by simpa only [hie] using hc) hv
        intro i hi' w hw
        exact hi i.val ((mem_upper ..).mpr ⟨hi',i.isLt⟩) w ((h.natLayer_fin g i).symm ▸ hw)
      · rw [ite_eq_right hb]
        have hb' : ¬ ∃ base : Fin (C.size g), base.val+1=cut ∧
            (C.layer g top).first (C.distinguished g)-(C.layer g base).last (C.distinguished g) ≤
              ((C.size g-cut)*C.period g : ℕ) := by
          rintro ⟨base,hbase,hbnd⟩
          apply hb
          have heq : cut-1=base.val := by omega
          refine ⟨by omega,?_⟩
          rw [heq,h.last_eq g base.isLt,h.natLayer_fin]
          exact hbnd
        have hex := supply_params C g supply (data X (h.group g)) (book X) (ids X) h.encode
          (h.size g) (h.rep g) (h.book_rep) (h.id_mem) M len cut hct he hb'
        rw [← h.phase_eq g] at hex
        let v := choose (data X (h.group g)) (book X) (ids X) cut M (phase X (h.group g))
          (foreign (data X (h.group g)) (book X))
        obtain ⟨hv,htest,hforeign⟩ := choose_spec _ _ _ _ _ _ _ hex
        have hvid : v.2.1 ∈ ids X := by
          obtain ⟨k,_,hv⟩ := List.mem_flatMap.mp hv
          obtain ⟨j,hj,hv⟩ := List.mem_flatMap.mp hv
          obtain ⟨r,_,heq⟩ := List.mem_map.mp hv
          have heq' : v.2.1 = j := (congrArg (fun x : UpperCode.Param => x.2.1) heq).symm
          exact heq'.symm ▸ hj
        obtain ⟨hg,hc,hv',hs,hn⟩ := h.hardPlan_spec closed g cut v hct hvid htest hforeign
        rw [← h.phase_eq g]
        change GoodPlan h (join P (hardPlan X (h.group g) cut v).1,_,_) ∧ _
        refine ⟨⟨runs_join hP hg.1,hg.2⟩,?_,?_,?_,hs,hn⟩
        · dsimp only [planBudget] at hc ⊢
          rw [cost_join _ _ [] hP.2.2 hg.1.2.1]
          dsimp only [v] at hc ⊢
          omega
        · exact fun w hw => (mem_join hP.2.2 hg.1.2.1).mpr (Or.inl hw)
        · intro i hi
          rcases hv' i hi with hvis|hblock|hreq
          · exact Or.inl (fun w hw => (mem_join hP.2.2 hg.1.2.1).mpr (Or.inr (hvis w hw)))
          · exact Or.inr (Or.inl hblock)
          · exact Or.inr (Or.inr hreq)
end Model
end Superstring.CollectionCode


namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}
structure RequestAt {X : Env α} {C : LayerCollection V G} (h : Model X C) (d : C.Id) (r : Request) where
  source : G
  source_eq : h.group source = r.source
  record : (C.layerAt d).Record (C.text source)
  offset : record.offset = RecordCode.offset r.code
  start : record.start = RecordCode.start r.code
  stop : record.stop = RecordCode.stop r.code
  foreign : C.text source ≠ fun x => C.text d.1 (x+record.offset)
  nonempty : r.members ≠ []
  nodup : r.members.Nodup
  bound : ∀ i ∈ r.members, i < C.size source
  long : ∀ i ∈ r.members, record.start+C.period source < (h.natLayer source i).first record.start
  margin : ∀ i ∈ r.members, (h.natLayer source i).last record.start < record.stop-C.period source


namespace RequestAt
variable {X : Env α} {C : LayerCollection V G} {h : Model X C} {r : Request} {d : C.Id}
    (w : RequestAt h d r)
def hosted : HostedGroup (C.layerAt d) where
  text := fun x => C.text w.source (x-w.record.offset)
  period := C.period w.source
  positive := C.positive w.source
  periodic := fun x => by simpa only [add_sub_right_comm] using C.periodic w.source (x-w.record.offset)
  start := w.record.start+w.record.offset
  stop := w.record.stop+w.record.offset
  first_le := w.record.first_le
  le_last := w.record.le_last
  agree := by
    intro x hx hy
    have hh := w.record.agree (x-w.record.offset) (by omega) (by omega)
    simpa only [sub_add_cancel] using hh
  foreign := by
    intro he
    apply w.foreign
    funext x
    simpa only [add_sub_cancel_right] using congrFun he (x+w.record.offset)

def request (i : {j // j ∈ r.members}) : w.hosted.Request where
  layer := (h.natLayer w.source i.val).translate w.record.offset
  stop := (h.natLayer w.source i.val).first w.record.start+w.record.offset
  first_le := by simp [hosted]
  le_last := by
    simp only [hosted,Layer.translate_last,add_sub_cancel_right]
    have hh := (h.natLayer w.source i.val).first_le_last w.record.start
    omega
  long := by
    have hh := w.long i.val i.property
    change w.record.start+w.record.offset+C.period w.source < _
    omega
  margin := by
    have hh := w.margin i.val i.property
    have hf := (h.natLayer w.source i.val).first_le_last w.record.start
    change _ ≤ w.record.stop+w.record.offset-C.period w.source
    omega

theorem data_rep (i : {j // j ∈ r.members}) :
    Represents (UpperCode.lookup (book X) (r.source*stride X+i.val)).1
      (UpperCode.lookup (book X) (r.source*stride X+i.val)).2 (h.natLayer w.source i.val) := by
  rw [← w.source_eq,lookup_encode X _ _ (h.bound _) (lt_of_lt_of_le (w.bound i.val i.property) (h.capacity _))]
  exact h.nat_rep w.source (w.bound i.val i.property)

theorem entry_eq (i : {j // j ∈ r.members}) : Request.entry X r i.val =
    (r.source,PeriodWord.shift (data X r.source).1 w.record.offset,
      w.hosted.start,w.hosted.stop,(w.request i).stop) := by
  simp only [Request.entry,← w.source_eq,← w.offset,← w.start,← w.stop,hosted,request]
  simp only [GeoCode.first,(h.nat_rep w.source (w.bound i.val i.property)).exit_eq,Layer.first]
end RequestAt
namespace Model
variable {X : Env α} {C : LayerCollection V G} (h : Model X C)
theorem requestAt {r : Request} (hr : ValidRequest h r) (d : C.Id) (hd : h.encode d = r.target) :
    Nonempty (RequestAt h d r) := by
  obtain ⟨w⟩ := hr
  have he : w.target = d := h.encode_inj (w.target_eq.trans hd.symm)
  cases he
  exact ⟨⟨w.source,w.source_eq,w.record,w.offset,w.start,w.stop,w.foreign,w.nonempty,w.nodup,
    w.bound,w.long,w.margin⟩⟩
end Model
end Superstring.CollectionCode


namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}
def entries (X : Env α) (R : List Request) : List (HostCode.Entry α) :=
  R.flatMap (fun r => r.members.map (Request.entry X r))
def requestedData (X : Env α) (R : List Request) : List (LayerData α) :=
  R.flatMap (fun r => (r.ids X).map (UpperCode.lookup (book X)))
def fibrePool (X : Env α) (t : ℕ) (R : List Request) : List (Walk α) :=
  let D := UpperCode.lookup (book X) t
  HostCode.completePool D.1 D.2 (entries X R) (requestedData X R)

def SourcesDistinct (R : List Request) : Prop :=
  ∀ r ∈ R, ∀ s ∈ R, r.source = s.source → r = s
namespace Model
variable {X : Env α} {C : LayerCollection V G} (h : Model X C)
theorem fibrePool_complete (closed : SubstringClosed V) (d : C.Id) (R : List Request)
    (hne : R ≠ []) (valid : ∀ r ∈ R, ValidRequest h r)
    (target : ∀ r ∈ R, r.target = h.encode d) (distinct : SourcesDistinct R) :
    ∃ P ∈ fibrePool X (h.encode d) R,
      Runs V [] [] P ∧ cost P ≤ 2*C.period d.1+(R.map (Request.reserve X)).sum ∧
        (∀ w ∈ ls X (h.encode d), w ∈ P) ∧
        ∀ r ∈ R, ∀ i ∈ r.ids X, ∀ w ∈ ls X i, w ∈ P := by
  classical
  let J := {r // r ∈ R}
  let W : ∀ j : J, RequestAt h d j.val := fun j => (h.requestAt (valid j.val j.property) d (target j.val j.property).symm).some
  let K := Σ j : J, {i // i ∈ j.val.members}
  let I : List K := R.attach.flatMap (fun j => j.val.members.attach.map (fun i => ⟨j,i⟩))
  let H := fun j : J => (W j).hosted
  let req := fun i : K => (W i.1).request i.2
  let Ws := fun j : J => PeriodWord.shift (data X j.val.source).1 (W j).record.offset
  let D' := fun i : K => UpperCode.lookup (book X) (i.1.val.source*stride X+i.2.val)
  have htag : Function.Injective (fun j : J => j.val.source) := by
    intro j k he
    exact Subtype.ext (distinct j.val j.property k.val k.property he)
  have hdiff (j k : J) (hjk : j ≠ k) (c : ℤ) : (H j).text ≠ fun x => (H k).text (x+c) := by
    intro he
    have hn : (W j).source ≠ (W k).source := by
      intro hs
      apply hjk
      apply htag
      exact (W j).source_eq.symm.trans ((congrArg h.group hs).trans (W k).source_eq)
    apply C.different _ _ hn ((W j).record.offset+c-(W k).record.offset)
    funext x
    have hh := congrFun he (x+(W j).record.offset)
    change C.text (W j).source (x+(W j).record.offset-(W j).record.offset) =
      C.text (W k).source (x+(W j).record.offset+c-(W k).record.offset) at hh
    simpa only [add_sub_cancel_right,show x+(W j).record.offset+c-(W k).record.offset =
      x+((W j).record.offset+c-(W k).record.offset) by omega] using hh
  have hWs (j : J) : (Ws j).length = (H j).period := by
    simp only [Ws,PeriodWord.length_shift,← (W j).source_eq]
    exact h.per_eq (W j).source
  have hWst (j : J) : PeriodWord.text (Ws j) = (H j).text := by
    dsimp only [Ws]
    rw [PeriodWord.text_shift (by rw [← (W j).source_eq]; change 0 < per X (h.group (W j).source); rw [h.per_eq]; exact C.positive (W j).source)]
    simp only [← (W j).source_eq,h.text_eq,H,RequestAt.hosted]
  have hiMem (j : J) (i : {i // i ∈ j.val.members}) : (⟨j,i⟩ : K) ∈ I :=
    List.mem_flatMap.mpr ⟨j,List.mem_attach R j,List.mem_map.mpr ⟨i,List.mem_attach _ i,rfl⟩⟩
  have hine : I ≠ [] := by
    obtain ⟨r,hr⟩ := List.exists_mem_of_ne_nil R hne
    let j : J := ⟨r,hr⟩
    obtain ⟨i,hi⟩ := List.exists_mem_of_ne_nil r.members (W j).nonempty
    exact List.ne_nil_of_mem (hiMem j ⟨i,hi⟩)
  obtain ⟨P,hP,hr,hb,hd,hi⟩ := HostCode.completePool_complete closed (C.layerAt d)
    (C.positive d.1) (C.periodic d.1) (C.letters closed d.1) H Sigma.fst req Ws (fun j => j.val.source)
    htag (UpperCode.lookup (book X) (h.encode d)).1 (UpperCode.lookup (book X) (h.encode d)).2
    (h.book_rep d) hWs hWst
    (fun j x => C.letters closed (W j).source (x-(W j).record.offset)) hdiff
    (fun i : K => C.text (W i.1).source) (fun i : K => h.natLayer (W i.1).source i.2.val)
    D' I hine (fun i _ => (W i.1).data_rep i.2) (fun i _ => C.periodic (W i.1).source)
    (fun i _ => (Layer.translate_content _ _).symm)
  have hent : I.map (HostCode.entryOf H Sigma.fst req Ws (fun j => j.val.source)) = entries X R := by
    simp only [I,entries,List.map_flatMap,List.map_map]
    rw [List.flatMap_subtype (g := fun r : Request => r.members.map (Request.entry X r))]
    · simp
    · intro r hr
      rw [List.map_subtype (g := Request.entry X r)]
      · simp
      · intro i hi
        exact ((W ⟨r,hr⟩).entry_eq ⟨i,hi⟩).symm
  have hdata : I.map D' = requestedData X R := by
    simp only [I,requestedData,List.map_flatMap,List.map_map,Request.ids,D',Function.comp_def]
    rw [List.flatMap_subtype (g := fun r : Request => r.members.map
      (fun i => UpperCode.lookup (book X) (r.source*stride X+i)))]
    · simp
    · intro r hr
      simp
  have sum_flatMap_nat {β : Type} (L : List β) (f : β → List ℕ) :
      (L.flatMap f).sum = (L.map (fun x => (f x).sum)).sum := by
    induction L with
    | nil => simp
    | cons a l ih => simp [ih]
  have hsum : (I.map (fun i => (H i.1).period)).sum = (R.map (fun r => r.members.length*per X r.source)).sum := by
    simp only [I,List.map_flatMap,List.map_map,sum_flatMap_nat]
    congr 1
    rw [List.map_subtype (g := fun r : Request => r.members.length*per X r.source)]
    · simp
    · intro r hr
      change (r.members.attach.map (fun _ => C.period (W ⟨r,hr⟩).source)).sum = _
      simp only [List.map_const',List.sum_replicate,List.length_attach,nsmul_eq_mul,Nat.cast_id,
        ← (W ⟨r,hr⟩).source_eq,h.per_eq]
  refine ⟨P,?_,hr,?_,fun w hw => hd w ((h.content_iff d w).mp hw),?_⟩
  · simpa only [fibrePool,hent,hdata] using hP
  · rw [hsum] at hb
    have he : (R.map (Request.reserve X)).sum = 2*(R.map (fun r => r.members.length*per X r.source)).sum := by
      exact List.sum_map_mul_left R (fun r => r.members.length*per X r.source) 2
    rw [he]
    linarith
  · intro r hr' i hi' w hw
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi'
    let a : J := ⟨r,hr'⟩
    let b : {j // j ∈ a.val.members} := ⟨j,hj⟩
    apply hi ⟨a,b⟩ (hiMem a b) w
    have hbnd := (W a).bound b.val b.property
    change w ∈ ls X (r.source*stride X+j) at hw
    have he : h.group (W a).source = r.source := (W a).source_eq
    rw [← he,ls_encode X _ _ (h.bound _) (lt_of_lt_of_le hbnd (h.capacity _))] at hw
    exact (mem_content (h.nat_rep (W a).source hbnd) (C.positive (W a).source)
      (C.periodic (W a).source) w).mp hw
end Model
end Superstring.CollectionCode

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.BitCode
variable {α : Type} [Inhabited α]
def firstGood (xs : List α) (test : α → Bool) : α := (xs.filter test).headD default
theorem firstGood_mem (xs : List α) (test : α → Bool) (hex : ∃ x ∈ xs, test x = true) :
    firstGood xs test ∈ xs ∧ test (firstGood xs test) = true := by
  have hn : xs.filter test ≠ [] := by
    obtain ⟨x,hx,ht⟩ := hex
    exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨hx,ht⟩)
  have hm : firstGood xs test ∈ xs.filter test := by
    unfold firstGood
    cases he : xs.filter test with
    | nil => exact False.elim (hn he)
    | cons a as => exact List.mem_cons_self ..
  exact List.mem_filter.mp hm
end Superstring.BitCode
namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}
def fibreCheck (vs : Walk α) (X : Env α) (t : ℕ) (R : List Request) (P : Walk α) : Bool :=
  BlockClose.rootedCheck vs P && lessEq (cost P) (2*per X (owner X t)+(R.map (Request.reserve X)).sum) &&
    BlockClose.coversCheck (contents X) (t::R.flatMap (Request.ids X)) P
def fibreSelect (vs : Walk α) (X : Env α) (t : ℕ) (R : List Request) : Walk α :=
  firstGood (fibrePool X t R) (fibreCheck vs X t R)
namespace Model
theorem fibreSelect_spec (vs : Walk α) {X : Env α} {C : LayerCollection {w | w ∈ vs} G}
    (h : Model X C) (closed : SubstringClosed {w | w ∈ vs}) (d : C.Id) (R : List Request)
    (hne : R ≠ []) (valid : ∀ r ∈ R, ValidRequest h r)
    (target : ∀ r ∈ R, r.target = h.encode d) (distinct : SourcesDistinct R) :
    let P := fibreSelect vs X (h.encode d) R
    Runs {w | w ∈ vs} [] [] P ∧ cost P ≤ 2*C.period d.1+(R.map (Request.reserve X)).sum ∧
      (∀ w ∈ ls X (h.encode d), w ∈ P) ∧ ∀ r ∈ R, ∀ i ∈ r.ids X, ∀ w ∈ ls X i, w ∈ P := by
  have hex := h.fibrePool_complete closed d R hne valid target distinct
  have he (P : Walk α) : fibreCheck vs X (h.encode d) R P = true ↔
      Runs {w | w ∈ vs} [] [] P ∧ cost P ≤ 2*C.period d.1+(R.map (Request.reserve X)).sum ∧
        (∀ w ∈ ls X (h.encode d), w ∈ P) ∧ ∀ r ∈ R, ∀ i ∈ r.ids X, ∀ w ∈ ls X i, w ∈ P := by
    simp only [fibreCheck,Bool.and_eq_true,BlockClose.rootedCheck_eq,lessEq,decide_eq_true_eq,
      h.owner_eq,h.per_eq,BlockClose.coversCheck_eq,BlockClose.Covers,List.mem_cons,List.mem_flatMap]
    constructor
    · rintro ⟨⟨hr,hb⟩,hc⟩
      exact ⟨hr,hb,hc _ (Or.inl rfl),fun r hr i hi => hc _ (Or.inr ⟨r,hr,hi⟩)⟩
    · rintro ⟨hr,hb,hd,hcov⟩
      refine ⟨⟨hr,hb⟩,?_⟩
      intro i hi
      rcases hi with rfl|⟨r,hr,hi⟩
      · exact hd
      · exact hcov r hr i hi
  apply (he _).mp
  exact (firstGood_mem _ _ (by obtain ⟨P,hP,hs⟩ := hex; exact ⟨P,hP,(he P).mpr hs⟩)).2
end Model
variable [Coded α]
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_request_reserve : Poly (fun q : Env α × Request => Request.reserve q.1 q.2) := by
  unfold Request.reserve Request.members Request.source
  fun_prop
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_request_ids : Poly (fun q : Env α × Request => Request.ids q.1 q.2) := by
  unfold Request.ids Request.members Request.source
  exact BitCode.Poly.mapFn (f := fun q : (Env α × Request) × ℕ => q.1.2.1*stride q.1.1+q.2)
    (by unfold stride; fun_prop) (by fun_prop)
omit [LinearOrder α] in
@[fun_prop] theorem poly_request_entry : Poly (fun q : (Env α × Request) × ℕ => Request.entry q.1.1 q.1.2 q.2) := by
  unfold Request.entry Request.source Request.code RecordCode.offset RecordCode.start RecordCode.stop
  fun_prop
omit [LinearOrder α] in
@[fun_prop] theorem poly_entries : Poly (fun q : Env α × List Request => entries q.1 q.2) := by
  unfold entries
  apply BitCode.Poly.flatMapFn (f := fun q : (Env α × List Request) × Request => q.2.members.map (Request.entry q.1.1 q.2))
  · exact BitCode.Poly.mapFn (f := fun q : ((Env α × List Request) × Request) × ℕ =>
      Request.entry q.1.1.1 q.1.2 q.2)
      (poly_request_entry.comp (f := fun q : ((Env α × List Request) × Request) × ℕ =>
        ((q.1.1.1,q.1.2),q.2)) (by fun_prop)) (by unfold Request.members; fun_prop)
  · fun_prop
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_requestedData : Poly (fun q : Env α × List Request => requestedData q.1 q.2) := by
  unfold requestedData
  apply BitCode.Poly.flatMapFn (f := fun q : (Env α × List Request) × Request =>
    (q.2.ids q.1.1).map (UpperCode.lookup (book q.1.1)))
  · exact BitCode.Poly.mapFn (f := fun q : ((Env α × List Request) × Request) × ℕ =>
      UpperCode.lookup (book q.1.1.1) q.2) (by fun_prop) (by fun_prop)
  · fun_prop
@[fun_prop] theorem poly_fibrePool : Poly (fun q : Env α × ℕ × List Request => fibrePool q.1 q.2.1 q.2.2) := by
  unfold fibrePool
  fun_prop
@[fun_prop] theorem poly_fibreCheck : Poly (fun q : (Walk α × Env α × ℕ × List Request) × Walk α =>
    fibreCheck q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2) := by
  unfold fibreCheck
  have hm : Poly (fun q : (Walk α × Env α × ℕ × List Request) × Walk α =>
      q.1.2.2.2.map (Request.reserve q.1.2.1)) :=
    BitCode.Poly.mapFn (f := fun q : ((Walk α × Env α × ℕ × List Request) × Walk α) × Request =>
      Request.reserve q.1.1.2.1 q.2) (by fun_prop) (by fun_prop)
  have hi : Poly (fun q : (Walk α × Env α × ℕ × List Request) × Walk α =>
      q.1.2.2.2.flatMap (Request.ids q.1.2.1)) :=
    BitCode.Poly.flatMapFn (f := fun q : ((Walk α × Env α × ℕ × List Request) × Walk α) × Request =>
      Request.ids q.1.1.2.1 q.2) (by fun_prop) (by fun_prop)
  fun_prop
@[fun_prop] theorem poly_fibreSelect : Poly (fun q : Walk α × Env α × ℕ × List Request =>
    fibreSelect q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  unfold fibreSelect firstGood
  have hf : Poly (fun q : Walk α × Env α × ℕ × List Request =>
      (fibrePool q.2.1 q.2.2.1 q.2.2.2).filter (fibreCheck q.1 q.2.1 q.2.2.1 q.2.2.2)) :=
    BitCode.Poly.filterFn poly_fibreCheck (by fun_prop)
  exact (BitCode.Poly.headD default).comp hf
end Superstring.CollectionCode


namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}
def fibre (R : List Request) (t : ℕ) : List Request := R.filter (fun r => equal r.target t)
def recipients (X : Env α) (g : ℕ) (R : List Request) : List ℕ :=
  (List.range (data X g).2.length).filter (fun i => !(fibre R (g*stride X+i)).isEmpty)
def incoming (vs : Walk α) (X : Env α) (g : ℕ) (R : List Request) : Walk α :=
  collect ((recipients X g R).map (fun i => fibreSelect vs X (g*stride X+i) (fibre R (g*stride X+i))))

omit [Inhabited α] [LinearOrder α] in
@[simp] theorem mem_fibre (R : List Request) (t : ℕ) (r : Request) :
    r ∈ fibre R t ↔ r ∈ R ∧ r.target = t := by
  simp only [fibre,List.mem_filter,equal,decide_eq_true_eq]
omit [Inhabited α] [LinearOrder α] in
theorem fibre_ne (R : List Request) (t : ℕ) : fibre R t ≠ [] ↔ ∃ r ∈ R, r.target = t := by
  constructor
  · intro hn
    obtain ⟨r,hr⟩ := List.exists_mem_of_ne_nil _ hn
    exact ⟨r,(mem_fibre ..).mp hr⟩
  · rintro ⟨r,hr,ht⟩
    exact List.ne_nil_of_mem ((mem_fibre ..).mpr ⟨hr,ht⟩)
omit [Inhabited α] [LinearOrder α] in
@[simp] theorem mem_recipients (X : Env α) (g : ℕ) (R : List Request) (i : ℕ) :
    i ∈ recipients X g R ↔ i < (data X g).2.length ∧ ∃ r ∈ R, r.target = g*stride X+i := by
  simp only [recipients,List.mem_filter,List.mem_range,Bool.not_eq_true',List.isEmpty_eq_false_iff,fibre_ne]
omit [Inhabited α] [LinearOrder α] in
theorem nodup_recipients (X : Env α) (g : ℕ) (R : List Request) : (recipients X g R).Nodup :=
  List.Nodup.filter _ List.nodup_range

omit [Inhabited α] [LinearOrder α] in
theorem sum_indicator (J : List ℕ) (hn : J.Nodup) (t v : ℕ) (ht : t ∈ J) :
    (J.map (fun j => if t=j then v else 0)).sum = v := by
  induction J with
  | nil => cases ht
  | cons a J ih =>
    obtain ⟨ha,hJ⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp ht with rfl|ht
    · have hz : (J.map (fun j => if t=j then v else 0)).sum = 0 := by
        apply List.sum_eq_zero
        intro n hn
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hn
        exact ite_eq_right (show t ≠ j by intro he; exact ha (he.symm ▸ hj))
      simp only [List.map_cons,List.sum_cons,ite_true,hz,Nat.add_zero]
    · have htne : t ≠ a := fun he => ha (he ▸ ht)
      simp only [List.map_cons,List.sum_cons,htne,↓reduceIte,Nat.zero_add,ih hJ ht]

omit [Inhabited α] [LinearOrder α] in
theorem fibre_sum (J : List ℕ) (hn : J.Nodup) (R : List Request) (f : Request → ℕ)
    (key : ℕ → ℕ) (inj : Function.Injective key)
    (targets : ∀ r ∈ R, ∃ j ∈ J, r.target = key j) :
    (J.map (fun j => ((fibre R (key j)).map f).sum)).sum = (R.map f).sum := by
  induction R with
  | nil => simp [fibre]
  | cons r R ih =>
    obtain ⟨t,ht,he⟩ := targets r (List.mem_cons_self ..)
    have hf (j : ℕ) : ((fibre (r::R) (key j)).map f).sum =
        (if t=j then f r else 0)+((fibre R (key j)).map f).sum := by
      have heq : equal r.target (key j) = decide (t=j) := by
        simp only [equal,he,inj.eq_iff]
      simp only [fibre,List.filter_cons,heq]
      split <;> simp_all
    simp only [hf,List.sum_map_add,sum_indicator J hn t (f r) ht,List.map_cons,List.sum_cons]
    rw [ih (fun r hr => targets r (List.mem_cons_of_mem _ hr))]

namespace Model
theorem incoming_spec (vs : Walk α) {X : Env α} {C : LayerCollection {w | w ∈ vs} G}
    (h : Model X C) (closed : SubstringClosed {w | w ∈ vs}) (g : G) (R : List Request)
    (valid : ∀ r ∈ R, ValidRequest h r)
    (targets : ∀ r ∈ R, ∃ i : Fin (C.size g), r.target = h.encode ⟨g,i⟩)
    (distinct : SourcesDistinct R) :
    let J := recipients X (h.group g) R
    let P := incoming vs X (h.group g) R
    Runs {w | w ∈ vs} [] [] P ∧ cost P ≤ 2*(J.length*C.period g)+(R.map (Request.reserve X)).sum ∧
      (∀ i : Fin (C.size g), i.val ∈ J → ∀ w ∈ (C.layer g i).Content, w ∈ P) ∧
      ∀ r ∈ R, ∀ i ∈ r.ids X, ∀ w ∈ ls X i, w ∈ P := by
  let J := recipients X (h.group g) R
  let F := fun i => fibreSelect vs X (h.group g*stride X+i) (fibre R (h.group g*stride X+i))
  have hbnd (i : ℕ) (hi : i ∈ J) : i < C.size g := by
    have hh := ((mem_recipients ..).mp hi).1
    rwa [h.size] at hh
  have hF (i : ℕ) (hi : i ∈ J) := h.fibreSelect_spec vs closed ⟨g,⟨i,hbnd i hi⟩⟩
    (fibre R (h.group g*stride X+i)) ((fibre_ne ..).mpr ((mem_recipients ..).mp hi).2)
    (fun r hr => valid r ((mem_fibre ..).mp hr).1)
    (fun r hr => ((mem_fibre ..).mp hr).2)
    (fun r hr s hs he => distinct r ((mem_fibre ..).mp hr).1 s ((mem_fibre ..).mp hs).1 he)
  obtain ⟨hr,hc,hv⟩ := collect_spec (C.empty_mem closed g) (J.map F)
    (by intro P hP; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hP; exact (hF i hi).1)
  have targetJ (r : Request) (hr : r ∈ R) : ∃ i ∈ J, r.target = h.group g*stride X+i := by
    obtain ⟨i,hi⟩ := targets r hr
    exact ⟨i.val,(mem_recipients ..).mpr ⟨by rw [h.size]; exact i.isLt,⟨r,hr,hi⟩⟩,hi⟩
  refine ⟨hr,?_,?_,?_⟩
  · change cost (collect (J.map F)) ≤ _
    rw [hc,List.map_map]
    have hh := List.sum_le_sum (l := J) (f := fun i => cost (F i))
      (g := fun i => 2*C.period g+((fibre R (h.group g*stride X+i)).map (Request.reserve X)).sum)
      (fun i hi => (hF i hi).2.1)
    have he : (J.map (fun i => 2*C.period g+((fibre R (h.group g*stride X+i)).map (Request.reserve X)).sum)).sum =
        2*(J.length*C.period g)+(R.map (Request.reserve X)).sum := by
      rw [List.sum_map_add,fibre_sum J (nodup_recipients ..) R (Request.reserve X)
        (fun i => h.group g*stride X+i) (fun _ _ hh => Nat.add_left_cancel hh) targetJ]
      simp only [List.map_const',List.sum_replicate,nsmul_eq_mul,Nat.cast_id]
      ring
    exact hh.trans_eq he
  · intro i hi w hw
    exact hv (F i.val) (List.mem_map.mpr ⟨i.val,hi,rfl⟩) w
      ((hF i.val hi).2.2.1 w ((h.content_iff ⟨g,i⟩ w).mpr hw))
  · intro r hr' i hi w hw
    obtain ⟨j,hj,ht⟩ := targetJ r hr'
    exact hv (F j) (List.mem_map.mpr ⟨j,hj,rfl⟩) w
      ((hF j hj).2.2.2 r ((mem_fibre ..).mpr ⟨hr',ht⟩) i hi w hw)
end Model
end Superstring.CollectionCode


namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}
def baseIndex (J : List ℕ) : ℕ := J.foldl max 0
def holes (J : List ℕ) : List ℕ := (List.range (baseIndex J+1)).filter (fun i => !(member i J))
def prepare (vs : Walk α) (X : Env α) (g : ℕ) (R : List Request) : ℕ × Walk α :=
  let J := recipients X g R
  let P := incoming vs X g R
  if J.isEmpty then (0,P) else
    let base := baseIndex J
    let r := (fibre R (g*stride X+base)).headD default
    (base+1,below (data X g) (holes J) P
      (RecordCode.start r.code+RecordCode.offset r.code)
      (RecordCode.stop r.code+RecordCode.offset r.code))
def process (vs : Walk α) (X : Env α) (g M : ℕ) (R : List Request) : Plan α :=
  let p := prepare vs X g R
  complete X g p.1 M p.2

omit [Inhabited α] [LinearOrder α] in
theorem maxFold_mem (J : List ℕ) (a : ℕ) : J.foldl max a = a ∨ J.foldl max a ∈ J := by
  induction J generalizing a with
  | nil => exact Or.inl rfl
  | cons b J ih =>
    rcases ih (max a b) with h|h
    · by_cases hab : b ≤ a
      · exact Or.inl (h.trans (max_eq_left hab))
      · exact Or.inr (List.mem_cons.mpr (Or.inl (h.trans (max_eq_right (by omega)))))
    · exact Or.inr (List.mem_cons_of_mem _ h)
omit [Inhabited α] [LinearOrder α] in
theorem base_mem (J : List ℕ) (hn : J ≠ []) : baseIndex J ∈ J := by
  rcases maxFold_mem J 0 with h|h
  · obtain ⟨j,hj⟩ := List.exists_mem_of_ne_nil _ hn
    have hh := le_maxFold J 0 hj
    have he : j = baseIndex J := by change J.foldl max 0 = 0 at h; unfold baseIndex; omega
    exact he ▸ hj
  · exact h
omit [Inhabited α] [LinearOrder α] in
theorem mem_holes (J : List ℕ) (i : ℕ) : i ∈ holes J ↔ i ≤ baseIndex J ∧ i ∉ J := by
  simp [holes,member]
omit [Inhabited α] [LinearOrder α] in
theorem holes_length (J : List ℕ) (hn : J.Nodup) : (holes J).length+J.length=baseIndex J+1 := by
  have hs : J.toFinset ⊆ (Finset.range (baseIndex J+1)) := by
    intro j hj
    have hh := le_maxFold J 0 (List.mem_toFinset.mp hj)
    exact Finset.mem_range.mpr (by change j < J.foldl max 0+1; omega)
  have he : (holes J).toFinset = Finset.range (baseIndex J+1) \ J.toFinset := by
    ext i
    simp only [List.mem_toFinset,mem_holes,Finset.mem_sdiff,Finset.mem_range,Nat.lt_succ_iff]
  have hnd : (holes J).Nodup := List.Nodup.filter _ List.nodup_range
  have hh := Finset.card_sdiff_add_card_eq_card hs
  rwa [← he,List.toFinset_card_of_nodup hnd,List.toFinset_card_of_nodup hn,Finset.card_range] at hh
namespace Model
variable {X : Env α}
theorem prepare_spec (vs : Walk α) {C : LayerCollection {w | w ∈ vs} G}
    (h : Model X C) (closed : SubstringClosed {w | w ∈ vs}) (g : G) (R : List Request)
    (valid : ∀ r ∈ R, ValidRequest h r)
    (targets : ∀ r ∈ R, ∃ i : Fin (C.size g), r.target = h.encode ⟨g,i⟩)
    (distinct : SourcesDistinct R) :
    let p := prepare vs X (h.group g) R
    p.1 ≤ C.size g ∧ Runs {w | w ∈ vs} [] [] p.2 ∧
      cost p.2 ≤ 2*(p.1*C.period g)+(R.map (Request.reserve X)).sum ∧
      (∀ i : Fin (C.size g), i.val < p.1 → ∀ w ∈ (C.layer g i).Content, w ∈ p.2) ∧
      ∀ r ∈ R, ∀ i ∈ r.ids X, ∀ w ∈ ls X i, w ∈ p.2 := by
  obtain ⟨hr,hc,hv,hi⟩ := h.incoming_spec vs closed g R valid targets distinct
  let J := recipients X (h.group g) R
  let P := incoming vs X (h.group g) R
  have hbnd (i : ℕ) (hi : i ∈ J) : i < C.size g := by
    have hh := ((mem_recipients ..).mp hi).1
    rwa [h.size] at hh
  by_cases hn : J = []
  · have he : prepare vs X (h.group g) R = (0,P) := by simp only [prepare,show recipients X (h.group g) R = [] from hn,List.isEmpty_nil,↓reduceIte]; rfl
    rw [he]
    exact ⟨Nat.zero_le _,hr,by simpa only [show recipients X (h.group g) R=[] from hn,List.length_nil] using hc,
      fun i hi => by omega,hi⟩
  · let base := baseIndex J
    have hbJ := base_mem J hn
    have hb := hbnd base hbJ
    let r := (fibre R (h.group g*stride X+base)).headD default
    have hrmem : r ∈ fibre R (h.group g*stride X+base) := by
      have hne := (fibre_ne ..).mpr ((mem_recipients ..).mp hbJ).2
      unfold r
      cases he : fibre R (h.group g*stride X+base) with
      | nil => exact False.elim (hne he)
      | cons a as => exact List.mem_cons_self ..
    obtain ⟨rR,rt⟩ := (mem_fibre ..).mp hrmem
    obtain ⟨w⟩ := h.requestAt (valid r rR) ⟨g,⟨base,hb⟩⟩ rt.symm
    have hlater := (Classical.choice (valid r rR)).later
    have hrec := w.record.length_lt (C.positive w.source) (C.positive g)
      (C.periodic w.source) (C.periodic g) w.foreign
    have hpq : C.period w.source < C.period g := by
      rw [← w.source_eq,rt,owner_encode X _ _ (h.local_lt g ⟨base,hb⟩),h.per_eq,h.per_eq] at hlater
      exact hlater
    have hlen : RecordCode.stop r.code+RecordCode.offset r.code-
        (RecordCode.start r.code+RecordCode.offset r.code) < 2*C.period g := by
      change w.record.stop-w.record.start < (C.period w.source:ℤ)+(C.period g:ℤ) at hrec
      rw [← w.start,← w.stop]; omega
    have hfirst : (h.natLayer g base).first (RecordCode.start r.code+RecordCode.offset r.code) ≤
        RecordCode.stop r.code+RecordCode.offset r.code := by
      rw [h.natLayer_fin g ⟨base,hb⟩,← w.start,← w.stop,← w.offset]
      exact w.record.first_le
    have hlast : RecordCode.stop r.code+RecordCode.offset r.code ≤
        (h.natLayer g base).last (RecordCode.start r.code+RecordCode.offset r.code) := by
      rw [h.natLayer_fin g ⟨base,hb⟩,← w.start,← w.stop,← w.offset]
      exact w.record.le_last
    obtain ⟨hq,hbq,hvp,hiq⟩ := below_spec (h.natLayer g)
      (fun i hi => h.nat_rep g (by have hh := (mem_holes J i).mp hi; omega))
      closed (C.positive g) (C.periodic g) (C.letters closed g) hr
      (by change ∀ w ∈ (h.natLayer g base).Content, _; rw [h.natLayer_fin g ⟨base,hb⟩]; exact hv ⟨base,hb⟩ hbJ)
      (fun i hi => h.nat_order g ((mem_holes J i).mp hi).1) hfirst hlast hlen
    have he : prepare vs X (h.group g) R = (base+1,below (data X (h.group g)) (holes J) P
        (RecordCode.start r.code+RecordCode.offset r.code) (RecordCode.stop r.code+RecordCode.offset r.code)) := by
      simp only [prepare,show recipients X (h.group g) R=J from rfl,List.isEmpty_iff,hn,↓reduceIte]; rfl
    rw [he]
    refine ⟨by omega,hq,?_,?_,fun r hr i hri w hw => hvp w (hi r hr i hri w hw)⟩
    · have hh := holes_length J (nodup_recipients ..)
      have hmul := Nat.add_mul (holes J).length J.length (C.period g)
      rw [hh] at hmul
      dsimp only [P,J,base] at hc hbq hmul ⊢
      omega
    · intro i hi w hw
      by_cases hij : i.val ∈ J
      · exact hvp w (hv i hij w hw)
      · exact hiq i.val ((mem_holes J i.val).mpr ⟨by omega,hij⟩) w ((h.natLayer_fin g i).symm ▸ hw)
theorem process_spec (vs : Walk α) {C : LayerCollection {w | w ∈ vs} G}
    (h : Model X C) (closed : SubstringClosed {w | w ∈ vs}) (supply : C.RecordSupply)
    (M : ℕ) (len : ∀ w ∈ vs, w.length ≤ M) (g : G) (R : List Request)
    (valid : ∀ r ∈ R, ValidRequest h r)
    (targets : ∀ r ∈ R, ∃ i : Fin (C.size g), r.target = h.encode ⟨g,i⟩)
    (distinct : SourcesDistinct R) :
    let o := process vs X (h.group g) M R
    GoodPlan h o ∧ planBudget X o ≤ 2*(C.size g*C.period g)+(R.map (Request.reserve X)).sum ∧
      (∀ i : Fin (C.size g), Covered X o (h.encode ⟨g,i⟩)) ∧
      (∀ r ∈ R, ∀ i ∈ r.ids X, ∀ w ∈ ls X i, w ∈ o.1) ∧
      (∀ r ∈ o.2.2, r.source=h.group g) ∧ o.2.2.length≤1 := by
  obtain ⟨hp,hr,hc,hv,hi⟩ := h.prepare_spec vs closed g R valid targets distinct
  obtain ⟨hg,hb,hv',hi',hs,hn⟩ := h.complete_spec closed supply M len g _ hp _ hr hv
  refine ⟨hg,?_,?_,fun r hri i hii w hw => hv' w (hi r hri i hii w hw),hs,hn⟩
  · have he := Nat.sub_add_cancel hp
    have hm := Nat.add_mul (C.size g-(prepare vs X (h.group g) R).1)
      (prepare vs X (h.group g) R).1 (C.period g)
    rw [he] at hm
    exact (hb.trans (by omega))
  · intro i
    by_cases hh : i.val < (prepare vs X (h.group g) R).1
    · exact Or.inl (fun w hw => hv' w (hv i hh w ((h.content_iff ⟨g,i⟩ w).mp hw)))
    · exact hi' i (by omega)
end Model
end Superstring.CollectionCode

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode BlockClose
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}
def pick (X : Env α) (I : List ℕ) : ℕ := firstGood I (fun g => I.all (fun j => lessEq (per X g) (per X j)))
def without (I : List ℕ) (g : ℕ) : List ℕ := I.filter (fun i => !(equal i g))
def inRequests (X : Env α) (g : ℕ) (R : List Request) : List Request := R.filter (fun r => equal (owner X r.target) g)
def restRequests (X : Env α) (g : ℕ) (R : List Request) : List Request := R.filter (fun r => !(equal (owner X r.target) g))
def charge (X : Env α) (g : ℕ) : ℕ := 2*((data X g).2.length*per X g)
abbrev State (α : Type) := List ℕ × Plan α
def advance (vs : Walk α) (X : Env α) (M : ℕ) (s : State α) : State α :=
  if s.1.isEmpty then s else
  let g := pick X s.1
  let o := process vs X g M (inRequests X g s.2.2.2)
  (without s.1 g,join s.2.1 o.1,s.2.2.1++o.2.1,restRequests X g s.2.2.2++o.2.2)

omit [Inhabited α] [LinearOrder α] in
theorem pick_spec (X : Env α) (I : List ℕ) (hn : I ≠ []) :
    pick X I ∈ I ∧ ∀ j ∈ I, per X (pick X I) ≤ per X j := by
  have hne : I.toFinset.Nonempty := by
    obtain ⟨i,hi⟩ := List.exists_mem_of_ne_nil _ hn
    exact ⟨i,List.mem_toFinset.mpr hi⟩
  obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image I.toFinset (per X) hne
  have hh := firstGood_mem I (fun g => I.all (fun j => lessEq (per X g) (per X j)))
    ⟨i,List.mem_toFinset.mp hi,List.all_eq_true.mpr (fun j hj => by
      simpa only [lessEq,decide_eq_true_eq] using hmin j (List.mem_toFinset.mpr hj))⟩
  exact ⟨hh.1,fun j hj => of_decide_eq_true (List.all_eq_true.mp hh.2 j hj)⟩
omit [Inhabited α] [LinearOrder α] in
@[simp] theorem mem_without (I : List ℕ) (g i : ℕ) : i ∈ without I g ↔ i ∈ I ∧ i ≠ g := by simp [without,equal]
omit [Inhabited α] [LinearOrder α] in
theorem without_lt (I : List ℕ) (g : ℕ) (hg : g ∈ I) : (without I g).length < I.length := by
  exact List.length_filter_lt_length_iff_exists.mpr ⟨g,hg,by simp [equal]⟩
omit [Inhabited α] [LinearOrder α] in
@[simp] theorem mem_inRequests (X : Env α) (g : ℕ) (R : List Request) (r : Request) :
    r ∈ inRequests X g R ↔ r ∈ R ∧ owner X r.target=g := by simp [inRequests,equal]
omit [Inhabited α] [LinearOrder α] in
@[simp] theorem mem_restRequests (X : Env α) (g : ℕ) (R : List Request) (r : Request) :
    r ∈ restRequests X g R ↔ r ∈ R ∧ owner X r.target≠g := by simp [restRequests,equal]
omit [Inhabited α] [LinearOrder α] in
theorem sum_partition {δ : Type} (R : List δ) (p : δ → Bool) (f : δ → ℕ) :
    ((R.filter p).map f).sum+((R.filter (fun r => !(p r))).map f).sum=(R.map f).sum := by
  induction R with
  | nil => simp
  | cons r R ih => cases hp : p r <;> simp only [List.filter_cons,hp,Bool.not_false,Bool.not_true,
      Bool.false_eq_true,↓reduceIte,List.map_cons,List.sum_cons] <;> omega
omit [Inhabited α] [LinearOrder α] in
theorem charge_remove (X : Env α) (I : List ℕ) (hn : I.Nodup) (g : ℕ) (hg : g ∈ I) :
    charge X g+((without I g).map (charge X)).sum=(I.map (charge X)).sum := by
  induction I with
  | nil => simp at hg
  | cons a I ih =>
    obtain ⟨ha,hn⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hg with rfl|hg
    · have he : without I g = I := by
        apply List.filter_eq_self.mpr
        intro j hj
        simpa only [Bool.not_eq_true',equal,decide_eq_false_iff_not] using (show j ≠ g from fun he => ha (he ▸ hj))
      simp only [without,List.filter_cons,equal,decide_true,Bool.not_true,Bool.false_eq_true,↓reduceIte]
      change charge X g+((without I g).map (charge X)).sum=_
      rw [he,List.map_cons,List.sum_cons]
    · have hag : a ≠ g := fun he => ha (he ▸ hg)
      have hh := ih hn hg
      simp only [without,List.filter_cons,equal,decide_eq_false hag,Bool.not_false,↓reduceIte,
        List.map_cons,List.sum_cons]
      change charge X g+(charge X a+((without I g).map (charge X)).sum)=_
      omega

end Superstring.CollectionCode


namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode BlockClose
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}
structure Invariant {X : Env α} {C : LayerCollection V G} (h : Model X C) (s : State α) : Prop where
  todo : s.1.Sublist (gs X)
  good : GoodPlan h s.2
  upward : ∀ g ∈ s.1, ∀ j ∈ gs X, per X g < per X j → j ∈ s.1
  targets : ∀ r ∈ s.2.2.2, owner X r.target ∈ s.1
  sources : ∀ r ∈ s.2.2.2, r.source ∉ s.1
  distinct : SourcesDistinct s.2.2.2
  ready : ∀ i : C.Id, h.group i.1 ∈ s.1 ∨ Covered X s.2 (h.encode i)

def budget (X : Env α) (s : State α) := planBudget X s.2+(s.1.map (charge X)).sum

omit [Inhabited α] [LinearOrder α] in
theorem length_one_same {δ : Type} {L : List δ} (hh : L.length ≤ 1) {a b : δ} (ha : a ∈ L) (hb : b ∈ L) : a=b := by
  cases L with
  | nil => cases ha
  | cons c L =>
    have he : L=[] := by apply List.length_eq_zero_iff.mp; simp only [List.length_cons] at hh; omega
    subst L
    exact (List.mem_singleton.mp ha).trans (List.mem_singleton.mp hb).symm

namespace Model
variable {X : Env α} (vs : Walk α) {C : LayerCollection {w | w ∈ vs} G} (h : Model X C)
theorem advance_spec (closed : SubstringClosed {w | w ∈ vs}) (supply : C.RecordSupply)
    (M : ℕ) (len : ∀ w ∈ vs, w.length ≤ M) (s : State α) (hs : Invariant h s) (hn : s.1 ≠ []) :
    Invariant h (advance vs X M s) ∧ budget X (advance vs X M s) ≤ budget X s ∧
      (advance vs X M s).1.length < s.1.length := by
  let j := pick X s.1
  have hj := (pick_spec X s.1 hn).1
  obtain ⟨g,hg⟩ := (h.groups j).mp (hs.todo.subset hj)
  let R := inRequests X j s.2.2.2
  let T := restRequests X j s.2.2.2
  let o := process vs X j M R
  have hr : ∀ r ∈ R, ValidRequest h r := fun r hr => hs.good.2.2 r ((mem_inRequests ..).mp hr).1
  have htar : ∀ r ∈ R, ∃ i : Fin (C.size g), r.target = h.encode ⟨g,i⟩ := by
    intro r hr'
    obtain ⟨w⟩ := hr r hr'
    have he : h.group w.target.1 = h.group g := by
      rw [← h.owner_eq w.target,w.target_eq,hg]
      exact ((mem_inRequests ..).mp hr').2
    have heg := h.group_inj he
    cases hwt : w.target with
    | mk d i =>
      have hdg : d=g := by simpa only [hwt] using heg
      subst d
      exact ⟨i,by rw [← w.target_eq,hwt]⟩
  have hd : SourcesDistinct R := fun r hr s hs' he => hs.distinct r ((mem_inRequests ..).mp hr).1 s ((mem_inRequests ..).mp hs').1 he
  have hh := h.process_spec vs closed supply M len g R hr htar hd
  rw [hg] at hh
  change GoodPlan h o ∧ _ at hh
  obtain ⟨ho,hcost,hcover,hfulfilled,hsource,hsmall⟩ := hh
  let t : State α := (without s.1 j,join s.2.1 o.1,s.2.2.1++o.2.1,T++o.2.2)
  have he : advance vs X M s = t := by simp only [advance,List.isEmpty_iff,hn,↓reduceIte,t,j,R,T,o]
  rw [he]
  have hmemold : ∀ w ∈ s.2.1, w ∈ t.2.1 := fun w hw => (mem_join hs.good.1.2.2 ho.1.2.1).mpr (Or.inl hw)
  have hmemnew : ∀ w ∈ o.1, w ∈ t.2.1 := fun w hw => (mem_join hs.good.1.2.2 ho.1.2.1).mpr (Or.inr hw)
  have hcovnew (i : ℕ) (hi : Covered X o i) : Covered X t.2 i := by
    rcases hi with hv|⟨b,hb,hi⟩|⟨r,hr,hi⟩
    · exact Or.inl (fun w hw => hmemnew w (hv w hw))
    · exact Or.inr (Or.inl ⟨b,List.mem_append_right _ hb,hi⟩)
    · exact Or.inr (Or.inr ⟨r,List.mem_append_right _ hr,hi⟩)
  have hcovold (i : ℕ) (hi : Covered X s.2 i) : Covered X t.2 i := by
    rcases hi with hv|⟨b,hb,hi⟩|⟨r,hr,hi⟩
    · exact Or.inl (fun w hw => hmemold w (hv w hw))
    · exact Or.inr (Or.inl ⟨b,List.mem_append_left _ hb,hi⟩)
    · by_cases ht : owner X r.target=j
      · exact Or.inl (fun w hw => hmemnew w (hfulfilled r ((mem_inRequests ..).mpr ⟨hr,ht⟩) i hi w hw))
      · exact Or.inr (Or.inr ⟨r,List.mem_append_left _ ((mem_restRequests ..).mpr ⟨hr,ht⟩),hi⟩)
  have hnewtarget (r : Request) (hr : r ∈ o.2.2) : owner X r.target ∈ without s.1 j := by
    obtain ⟨w⟩ := ho.2.2 r hr
    have hl := w.later
    rw [hsource r hr] at hl
    have ht : owner X r.target ∈ gs X := by
      rw [← w.target_eq,h.owner_eq]
      exact (h.groups _).mpr ⟨w.target.1,rfl⟩
    exact (mem_without ..).mpr ⟨hs.upward j hj _ ht hl,fun he => (lt_irrefl _ (he ▸ hl))⟩
  refine ⟨?_,?_,without_lt s.1 j hj⟩
  · refine ⟨(List.filter_sublist).trans hs.todo,?_,?_,?_,?_,?_,?_⟩
    · refine ⟨runs_join hs.good.1 ho.1,?_,?_⟩
      · intro b hb
        rcases List.mem_append.mp hb with hb|hb
        · exact hs.good.2.1 b hb
        · exact ho.2.1 b hb
      · intro r hr
        rcases List.mem_append.mp hr with hr|hr
        · exact hs.good.2.2 r ((mem_restRequests ..).mp hr).1
        · exact ho.2.2 r hr
    · intro a ha b hb hab
      obtain ⟨ha,haj⟩ := (mem_without ..).mp ha
      refine (mem_without ..).mpr ⟨hs.upward a ha b hb hab,?_⟩
      intro he
      subst b
      have hh := (pick_spec X s.1 hn).2 a ha
      change per X j ≤ per X a at hh
      omega
    · intro r hr
      rcases List.mem_append.mp hr with hr|hr
      · obtain ⟨hr,ht⟩ := (mem_restRequests ..).mp hr
        exact (mem_without ..).mpr ⟨hs.targets r hr,ht⟩
      · exact hnewtarget r hr
    · intro r hr hh
      rcases List.mem_append.mp hr with hr|hr
      · exact hs.sources r ((mem_restRequests ..).mp hr).1 ((mem_without ..).mp hh).1
      · exact ((mem_without ..).mp hh).2 (hsource r hr)
    · intro r hr u hu he
      rcases List.mem_append.mp hr with hr|hr <;> rcases List.mem_append.mp hu with hu|hu
      · exact hs.distinct r ((mem_restRequests ..).mp hr).1 u ((mem_restRequests ..).mp hu).1 he
      · exact False.elim (hs.sources r ((mem_restRequests ..).mp hr).1 ((he.trans (hsource u hu)).symm ▸ hj))
      · exact False.elim (hs.sources u ((mem_restRequests ..).mp hu).1 ((he.symm.trans (hsource r hr)).symm ▸ hj))
      · exact length_one_same hsmall hr hu
    · intro i
      rcases hs.ready i with hi|hi
      · by_cases hij : h.group i.1=j
        · have heg : i.1=g := h.group_inj (hij.trans hg.symm)
          obtain ⟨a,k⟩ := i
          change a=g at heg
          subst a
          exact Or.inr (hcovnew _ (hcover k))
        · exact Or.inl ((mem_without ..).mpr ⟨hi,hij⟩)
      · exact Or.inr (hcovold _ hi)
  · have hc := cost_join s.2.1 o.1 [] hs.good.1.2.2 ho.1.2.1
    have hp := sum_partition s.2.2.2 (fun r => equal (owner X r.target) j) (Request.reserve X)
    have hrm := charge_remove X s.1 (h.nodup.sublist hs.todo) j hj
    have hcharge : charge X j = 2*(C.size g*C.period g) := by rw [← hg]; simp only [charge,h.size,h.per_eq]
    simp only [budget,planBudget,t,List.map_append,List.sum_append]
    rw [hc]
    change (R.map (Request.reserve X)).sum+(T.map (Request.reserve X)).sum=(s.2.2.2.map (Request.reserve X)).sum at hp
    unfold planBudget at hcost
    rw [hcharge] at hrm
    dsimp only [o] at hc ⊢
    omega
end Model
end Superstring.CollectionCode

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode UpperCode
variable {α : Type} [Coded α] [Inhabited α] [LinearOrder α]
@[fun_prop] theorem poly_foreign : Poly (fun q : GroupData α × Book α × Param => foreign q.1 q.2.1 q.2.2) := by
  unfold foreign RecordCode.offset
  fun_prop
abbrev ChooseInput (α : Type) := (GroupData α × Book α × List ℕ) × ℕ × ℕ × ℤ
@[fun_prop] theorem poly_choose : Poly (fun q : ChooseInput α =>
    choose q.1.1 q.1.2.1 q.1.2.2 q.2.1 q.2.2.1 q.2.2.2 (foreign q.1.1 q.1.2.1)) := by
  unfold choose
  have hf : Poly (fun q : ChooseInput α =>
      (params q.1.2.1 q.1.2.2 q.1.1.2.length q.2.2.1 q.2.2.2).filter
        (fun v => test q.1.1 q.1.2.1 q.2.1 q.2.2.2 v && foreign q.1.1 q.1.2.1 v)) :=
    BitCode.Poly.filterFn (p := fun q : ChooseInput α × Param =>
      test q.1.1.1 q.1.1.2.1 q.1.2.1 q.1.2.2.2 q.2 && foreign q.1.1.1 q.1.1.2.1 q.2)
      (by fun_prop) (by fun_prop)
  fun_prop
@[fun_prop] theorem poly_hard (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (fun q : Env α × ℕ × ℕ × UpperCode.Param => hard q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  have ph := poly_phase hlt
  unfold hard stride RecordCode.start RecordCode.stop
  exact DistributeCode.poly_record.comp
    (f := fun q : Env α × ℕ × ℕ × UpperCode.Param =>
      ((data q.1 q.2.1,q.2.1,q.2.2.2.2.1,q.2.1*q.1.2),
       (upper (data q.1 q.2.1).2.length q.2.2.1,(data q.1 q.2.1).2.length-q.2.2.2.1,(data q.1 q.2.1).2.length-1),
       (q.2.2.2.2.2.2.1,q.2.2.2.2.2.2.2,phase q.1 q.2.1))) (by fun_prop)
@[fun_prop] theorem poly_hardPlan (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (fun q : Env α × ℕ × ℕ × UpperCode.Param => hardPlan q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  have ph := poly_hard hlt
  unfold hardPlan
  fun_prop
abbrev CompleteInput (α : Type) := Env α × ℕ × ℕ × ℕ × Walk α
@[fun_prop] theorem poly_cond {δ ε : Type} [Coded δ] [Coded ε] {p : δ → Prop} [DecidablePred p]
    {f g : δ → ε} (hp : Poly (fun x => decide (p x))) (hf : Poly f) (hg : Poly g) :
    Poly (fun x => if p x then f x else g x) := by
  simpa only [decide_eq_true_eq] using BitCode.Poly.ite hp hf hg
@[fun_prop] theorem poly_decide_and {δ : Type} [Coded δ] {p q : δ → Prop} [DecidablePred p] [DecidablePred q]
    (hp : Poly (fun x => decide (p x))) (hq : Poly (fun x => decide (q x))) :
    Poly (fun x => decide (p x ∧ q x)) := by
  simpa only [Bool.decide_and,Function.comp_def] using BitCode.Poly.and.comp (hp.pair hq)
def completeRoot (q : CompleteInput α) : Walk α := rootUpper (data q.1 q.2.1)
  (upper (data q.1 q.2.1).2.length q.2.2.1) ((data q.1 q.2.1).2.length-1) (phase q.1 q.2.1)
def completeBand (q : CompleteInput α) : Walk α := attachBand (data q.1 q.2.1)
  (upper (data q.1 q.2.1).2.length q.2.2.1) (q.2.2.1-1) ((data q.1 q.2.1).2.length-1) q.2.2.2.2 (phase q.1 q.2.1)
def completePick (q : CompleteInput α) : UpperCode.Param := choose (data q.1 q.2.1) (book q.1) (ids q.1)
  q.2.2.1 q.2.2.2.1 (phase q.1 q.2.1) (foreign (data q.1 q.2.1) (book q.1))
def completeHard (q : CompleteInput α) : Plan α := hardPlan q.1 q.2.1 q.2.2.1 (completePick q)
def completeM (q : CompleteInput α) : ℕ := (data q.1 q.2.1).2.length
def completeP (q : CompleteInput α) : ℕ := (data q.1 q.2.1).1.length
def completeT (q : CompleteInput α) : ℤ := phase q.1 q.2.1
def completeH (q : CompleteInput α) : ℤ := GeoCode.first (exits (data q.1 q.2.1) (completeM q-1)) (completeT q)
def completeExit (q : CompleteInput α) : ℤ := GeoCode.exit (exits (data q.1 q.2.1) (q.2.2.1-1)) (completeT q)
@[fun_prop] theorem poly_completeRoot (hlt : Poly (fun q : α × α => decide (q.1<q.2))) : Poly (completeRoot (α:=α)) := by
  have ph := poly_phase hlt
  exact poly_rootUpper.comp
    (f := fun q : CompleteInput α => (data q.1 q.2.1,upper (data q.1 q.2.1).2.length q.2.2.1,
      (data q.1 q.2.1).2.length-1,phase q.1 q.2.1)) (by fun_prop)
@[fun_prop] theorem poly_completeBand (hlt : Poly (fun q : α × α => decide (q.1<q.2))) : Poly (completeBand (α:=α)) := by
  have ph := poly_phase hlt
  exact poly_attachBand.comp
    (f := fun q : CompleteInput α => ((data q.1 q.2.1,upper (data q.1 q.2.1).2.length q.2.2.1),
      (q.2.2.1-1,(data q.1 q.2.1).2.length-1),q.2.2.2.2,phase q.1 q.2.1)) (by fun_prop)
@[fun_prop] theorem poly_completePick (hlt : Poly (fun q : α × α => decide (q.1<q.2))) : Poly (completePick (α:=α)) := by
  have ph := poly_phase hlt
  exact poly_choose.comp
    (f := fun q : CompleteInput α => ((data q.1 q.2.1,book q.1,ids q.1),q.2.2.1,q.2.2.2.1,phase q.1 q.2.1)) (by fun_prop)
@[fun_prop] theorem poly_completeHard (hlt : Poly (fun q : α × α => decide (q.1<q.2))) : Poly (completeHard (α:=α)) := by
  have hc := poly_completePick hlt
  exact (poly_hardPlan hlt).comp (f := fun q : CompleteInput α => (q.1,q.2.1,q.2.2.1,completePick q)) (by fun_prop)
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_completeM : Poly (completeM (α:=α)) := by unfold completeM; fun_prop
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_completeP : Poly (completeP (α:=α)) := by unfold completeP; fun_prop
@[fun_prop] theorem poly_completeT (hlt : Poly (fun q : α × α => decide (q.1<q.2))) : Poly (completeT (α:=α)) :=
  (poly_phase hlt).comp (f := fun q : CompleteInput α => (q.1,q.2.1)) (by fun_prop)
@[fun_prop] theorem poly_completeH (hlt : Poly (fun q : α × α => decide (q.1<q.2))) : Poly (completeH (α:=α)) := by
  have ht := poly_completeT hlt
  unfold completeH
  fun_prop
@[fun_prop] theorem poly_completeExit (hlt : Poly (fun q : α × α => decide (q.1<q.2))) : Poly (completeExit (α:=α)) := by
  have ht := poly_completeT hlt
  unfold completeExit
  fun_prop
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_completeTest1 : Poly (fun q : CompleteInput α => decide (completeM q ≤ q.2.2.1)) := by fun_prop
@[fun_prop] theorem poly_completeTest2 (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (fun q : CompleteInput α => decide (completeH q-completeT q ≤ ((completeM q-q.2.2.1)*completeP q : ℕ))) := by
  have hH := poly_completeH hlt
  have ht := poly_completeT hlt
  fun_prop
@[fun_prop] theorem poly_completeTest3 (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (fun q : CompleteInput α => decide (0 < q.2.2.1 ∧
      completeH q-completeExit q ≤ ((completeM q-q.2.2.1)*completeP q : ℕ))) := by
  have hH := poly_completeH hlt
  have he := poly_completeExit hlt
  have h0 : Poly (fun q : CompleteInput α => decide (0 < q.2.2.1)) := by fun_prop
  have hn : Poly (fun q : CompleteInput α => (((completeM q-q.2.2.1)*completeP q : ℕ) : ℤ)) := by fun_prop
  have hs0 := BitCode.Poly.subInt.comp (hH.pair he)
  have hs : Poly (fun q : CompleteInput α => completeH q-completeExit q) := hs0
  have h1 : Poly (fun q : CompleteInput α => decide (completeH q-completeExit q ≤ ((completeM q-q.2.2.1)*completeP q : ℕ))) :=
    BitCode.Poly.leInt.comp (hs.pair hn)
  exact poly_decide_and h0 h1
@[fun_prop] theorem poly_complete (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (fun q : CompleteInput α => complete q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  have hr := poly_completeRoot hlt
  have hb := poly_completeBand hlt
  have hp := poly_completeHard hlt
  have ha : Poly (fun q : CompleteInput α => (q.2.2.2.2,([] : List (BlockClose.Block α)),([] : List Request))) := by fun_prop
  have hb1 : Poly (fun q : CompleteInput α => (join q.2.2.2.2 (completeRoot q),([] : List (BlockClose.Block α)),([] : List Request))) := by fun_prop
  have hb2 : Poly (fun q : CompleteInput α => (completeBand q,([] : List (BlockClose.Block α)),([] : List Request))) := by fun_prop
  have hb3 : Poly (fun q : CompleteInput α => (join q.2.2.2.2 (completeHard q).1,(completeHard q).2)) := by
    exact (WalkCode.poly_join.comp (BitCode.Poly.pair (by fun_prop) (BitCode.Poly.fst.comp hp))).pair (BitCode.Poly.snd.comp hp)
  exact poly_cond poly_completeTest1 ha (poly_cond (poly_completeTest2 hlt) hb1 (poly_cond (poly_completeTest3 hlt) hb2 hb3))
@[fun_prop] theorem poly_fibre : Poly (fun q : List Request × ℕ => fibre q.1 q.2) := by
  unfold fibre Request.target
  exact BitCode.Poly.filterFn (p := fun q : (List Request × ℕ) × Request => equal q.2.2.1 q.1.2)
    (by fun_prop) (by fun_prop)
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_recipients : Poly (fun q : Env α × ℕ × List Request => recipients q.1 q.2.1 q.2.2) := by
  unfold recipients stride
  exact BitCode.Poly.filterFn (p := fun q : (Env α × ℕ × List Request) × ℕ =>
    !(fibre q.1.2.2 (q.1.2.1*q.1.1.2+q.2)).isEmpty) (by fun_prop) (by fun_prop)
@[fun_prop] theorem poly_incoming : Poly (fun q : (Walk α × Env α) × ℕ × List Request => incoming q.1.1 q.1.2 q.2.1 q.2.2) := by
  unfold incoming stride
  have hm : Poly (fun q : (Walk α × Env α) × ℕ × List Request =>
      (recipients q.1.2 q.2.1 q.2.2).map (fun i => fibreSelect q.1.1 q.1.2 (q.2.1*q.1.2.2+i)
        (fibre q.2.2 (q.2.1*q.1.2.2+i)))) :=
    BitCode.Poly.mapFn (f := fun q : ((Walk α × Env α) × ℕ × List Request) × ℕ =>
      fibreSelect q.1.1.1 q.1.1.2 (q.1.2.1*q.1.1.2.2+q.2) (fibre q.1.2.2 (q.1.2.1*q.1.1.2.2+q.2)))
      (by fun_prop) (by fun_prop)
  fun_prop
@[fun_prop] theorem poly_baseIndex : Poly baseIndex := BitCode.Poly.maxFold
@[fun_prop] theorem poly_holes : Poly holes := by
  unfold holes
  exact BitCode.Poly.filterFn (p := fun q : List ℕ × ℕ => !(member q.2 q.1)) (by fun_prop) (by fun_prop)
@[fun_prop] theorem poly_prepare : Poly (fun q : (Walk α × Env α) × ℕ × List Request => prepare q.1.1 q.1.2 q.2.1 q.2.2) := by
  let J := fun q : (Walk α × Env α) × ℕ × List Request => recipients q.1.2 q.2.1 q.2.2
  let r := fun q : (Walk α × Env α) × ℕ × List Request =>
    (fibre q.2.2 (q.2.1*stride q.1.2+baseIndex (J q))).headD (default : Request)
  have hr : Poly r := by unfold r J stride; fun_prop
  have hb : Poly (fun q : (Walk α × Env α) × ℕ × List Request =>
      below (data q.1.2 q.2.1) (holes (J q)) (incoming q.1.1 q.1.2 q.2.1 q.2.2)
        (RecordCode.start (r q).code+RecordCode.offset (r q).code)
        (RecordCode.stop (r q).code+RecordCode.offset (r q).code)) :=
    poly_below.comp (f := fun q : (Walk α × Env α) × ℕ × List Request =>
      ((data q.1.2 q.2.1,holes (J q)),incoming q.1.1 q.1.2 q.2.1 q.2.2,
       RecordCode.start (r q).code+RecordCode.offset (r q).code,
       RecordCode.stop (r q).code+RecordCode.offset (r q).code))
      (by unfold RecordCode.start RecordCode.stop RecordCode.offset Request.code; unfold J; fun_prop)
  unfold prepare
  dsimp only
  fun_prop
abbrev ProcessInput (α : Type) := (Walk α × Env α) × ℕ × ℕ × List Request
@[fun_prop] theorem poly_process (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (fun q : ProcessInput α => process q.1.1 q.1.2 q.2.1 q.2.2.1 q.2.2.2) := by
  have hc := poly_complete hlt
  unfold process
  exact hc.comp (f := fun q : ProcessInput α =>
    (q.1.2,q.2.1,(prepare q.1.1 q.1.2 q.2.1 q.2.2.2).1,q.2.2.1,(prepare q.1.1 q.1.2 q.2.1 q.2.2.2).2)) (by
    have hp := poly_prepare.comp (f := fun q : ProcessInput α => (q.1,q.2.1,q.2.2.2)) (by fun_prop)
    exact (by fun_prop))
end Superstring.CollectionCode


namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode BlockClose
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}

theorem complete_extras (X : Env α) (g cut M : ℕ) (P Q : Walk α) :
    (complete X g cut M P).2 = (complete X g cut M Q).2 := by
  unfold complete
  dsimp only
  split <;> first | rfl | (split <;> first | rfl | (split <;> rfl))

variable [Coded α]
def extraSizes (X : Env α) (M : ℕ) : List ℕ :=
  (gs X).flatMap (fun g => (List.range ((data X g).2.length+1)).map
    (fun cut => bitSize (complete X g cut M [[]]).2))
def maxExtras (X : Env α) (M : ℕ) : ℕ := (extraSizes X M).foldl max 0

theorem extras_le (X : Env α) (M g cut : ℕ) (hg : g ∈ gs X) (hc : cut ≤ (data X g).2.length) (P : Walk α) :
    bitSize (complete X g cut M P).2 ≤ maxExtras X M := by
  rw [complete_extras X g cut M P [[]]]
  exact le_maxFold _ 0 (List.mem_flatMap.mpr ⟨g,hg,List.mem_map.mpr ⟨cut,List.mem_range.mpr (by omega),rfl⟩⟩)

namespace Model
variable {X : Env α} (vs : Walk α) {C : LayerCollection {w | w ∈ vs} G} (h : Model X C)
theorem process_extra_bound (closed : SubstringClosed {w | w ∈ vs})
    (g : G) (R : List Request) (M : ℕ)
    (valid : ∀ r ∈ R, ValidRequest h r)
    (targets : ∀ r ∈ R, ∃ i : Fin (C.size g), r.target=h.encode ⟨g,i⟩)
    (distinct : SourcesDistinct R) :
    bitSize (process vs X (h.group g) M R).2 ≤ maxExtras X M := by
  have hc := (h.prepare_spec vs closed g R valid targets distinct).1
  unfold process
  apply extras_le
  · exact (h.groups _).mpr ⟨g,rfl⟩
  · rwa [h.size]

theorem advance_extra_bound (closed : SubstringClosed {w | w ∈ vs})
    (M : ℕ) (s : State α) (hs : Invariant h s) :
    bitSize (advance vs X M s).2.2 ≤ bitSize s.2.2+maxExtras X M := by
  by_cases hn : s.1=[]
  · simp only [advance,hn,List.isEmpty_nil,↓reduceIte]
    omega
  · let j := pick X s.1
    have hj := (pick_spec X s.1 hn).1
    obtain ⟨g,hg⟩ := (h.groups j).mp (hs.todo.subset hj)
    let R := inRequests X j s.2.2.2
    have hr : ∀ r ∈ R, ValidRequest h r := fun r hr => hs.good.2.2 r ((mem_inRequests ..).mp hr).1
    have htar : ∀ r ∈ R, ∃ i : Fin (C.size g), r.target=h.encode ⟨g,i⟩ := by
      intro r hr'
      obtain ⟨w⟩ := hr r hr'
      have he : h.group w.target.1=h.group g := by
        rw [← h.owner_eq w.target,w.target_eq,hg]
        exact ((mem_inRequests ..).mp hr').2
      have heg := h.group_inj he
      cases hwt : w.target with
      | mk d i =>
        have hdg : d=g := by simpa only [hwt] using heg
        subst d
        exact ⟨i,by rw [← w.target_eq,hwt]⟩
    have hd : SourcesDistinct R := fun r hr u hu he => hs.distinct r ((mem_inRequests ..).mp hr).1 u ((mem_inRequests ..).mp hu).1 he
    have he := h.process_extra_bound vs closed g R M hr htar hd
    rw [hg] at he
    have hB := bitSize_append s.2.2.1 (process vs X j M R).2.1
    have hR := bitSize_append (restRequests X j s.2.2.2) (process vs X j M R).2.2
    have hsR := bitSize_sublist (List.filter_sublist (p := fun r => !(equal (owner X r.target) j)) (l := s.2.2.2))
    change bitSize (restRequests X j s.2.2.2) ≤ bitSize s.2.2.2 at hsR
    have hp := bitSize_prod (process vs X j M R).2.1 (process vs X j M R).2.2
    have hs := bitSize_prod s.2.2.1 s.2.2.2
    simp only [Prod.eta] at hp hs
    simp only [advance,List.isEmpty_iff,hn,↓reduceIte,bitSize_prod]
    change bitSize (s.2.2.1++(process vs X j M R).2.1)+
      bitSize (restRequests X j s.2.2.2++(process vs X j M R).2.2)≤_
    omega
end Model
end Superstring.CollectionCode


namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode BlockClose
variable {α G : Type} [Inhabited α] [LinearOrder α] {V : Set (List α)}
def initial (X : Env α) : State α := (gs X,[[]],[],[])
theorem advance_nil (vs : Walk α) (X : Env α) (M : ℕ) (P : Plan α) : advance vs X M ([],P)=([],P) := by
  simp only [advance,List.isEmpty_nil,↓reduceIte]
namespace Model
variable {X : Env α} (vs : Walk α) {C : LayerCollection {w | w ∈ vs} G} (h : Model X C)
theorem initial_invariant (nil_mem : ([] : List α) ∈ vs) : Invariant h (initial X) := by
  refine { todo := List.Sublist.refl _, good := ?_, upward := ?_, targets := ?_, sources := ?_, distinct := ?_, ready := ?_ }
  · exact ⟨⟨valid_nil [] nil_mem,rfl,rfl⟩,by simp [initial],by simp [initial]⟩
  · intro g hg j hj _; exact hj
  · simp [initial]
  · simp [initial]
  · intro r hr; cases hr
  · intro i; exact Or.inl ((h.groups _).mpr ⟨i.1,rfl⟩)

variable [Coded α]
theorem iterate_advance (closed : SubstringClosed {w | w ∈ vs}) (supply : C.RecordSupply)
    (M : ℕ) (len : ∀ w ∈ vs, w.length ≤ M) (s : State α) (hs : Invariant h s) (n : ℕ) :
    let t := (advance vs X M)^[n] s
    Invariant h t ∧ budget X t ≤ budget X s ∧ t.1.length ≤ s.1.length-n ∧
      bitSize t.2.2 ≤ bitSize s.2.2+n*maxExtras X M := by
  dsimp only
  induction n with
  | zero => exact ⟨hs,le_rfl,by simp,by simp⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    let t := (advance vs X M)^[n] s
    change Invariant h t ∧ budget X t ≤ budget X s ∧ t.1.length ≤ s.1.length-n ∧
      bitSize t.2.2 ≤ bitSize s.2.2+n*maxExtras X M at ih
    change Invariant h (advance vs X M t) ∧ budget X (advance vs X M t) ≤ budget X s ∧
      (advance vs X M t).1.length ≤ s.1.length-(n+1) ∧
      bitSize (advance vs X M t).2.2 ≤ bitSize s.2.2+(n+1)*maxExtras X M
    by_cases hn : t.1=[]
    · have ht : advance vs X M t=t := by rw [← Prod.eta t,hn,advance_nil]
      rw [ht]
      refine ⟨ih.1,ih.2.1,by simp [hn],?_⟩
      have hh := ih.2.2.2
      rw [Nat.succ_mul]
      omega
    · have hh := h.advance_spec vs closed supply M len t ih.1 hn
      have he := h.advance_extra_bound vs closed M t ih.1
      refine ⟨hh.1,hh.2.1.trans ih.2.1,?_,?_⟩
      · have h1 := hh.2.2; have h2 := ih.2.2.1; change (advance vs X M t).1.length ≤ _; omega
      · have h1 := ih.2.2.2; rw [Nat.succ_mul]; omega
end Model
end Superstring.CollectionCode

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode BlockClose
variable {α G : Type} [Inhabited α] [LinearOrder α] [Coded α]
abbrev Context (α : Type) := Walk α × Env α × ℕ
abbrev Input (α : Type) := Context α × State α
def iterStep (q : Input α) : Input α := (q.1,advance q.1.1 q.1.2.1 q.1.2.2 q.2)
def schedulerCapacity (q : Input α) : ℕ :=
  bitSize q.1+bitSize (gs q.1.2.1)+bitSize q.2.2.2+1+
    (2*budget q.1.2.1 q.2+1)*(bitSize q.1.1+1)+(gs q.1.2.1).length*maxExtras q.1.2.1 q.1.2.2
def sweep (q : Context α) : Plan α :=
  let s : Input α := (q,initial q.2.1)
  (((cappedStep iterStep)^[((gs q.2.1).length)] (schedulerCapacity s,s)).2).2.2

omit [Coded α] in
theorem iterate_iterStep (q : Input α) (n : ℕ) :
    iterStep^[n] q = (q.1,(advance q.1.1 q.1.2.1 q.1.2.2)^[n] q.2) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,Function.iterate_succ_apply']; rfl

namespace Model
variable {vs : Walk α} {X : Env α} {C : LayerCollection {w | w ∈ vs} G} (h : Model X C)
theorem state_size (M : ℕ) (s t : State α) (ht : Invariant h t)
    (hc : budget X t ≤ budget X s)
    (he : bitSize t.2.2 ≤ bitSize s.2.2+(gs X).length*maxExtras X M) :
    bitSize (((vs,X,M),t) : Input α) ≤ schedulerCapacity ((vs,X,M),s) := by
  have hi := bitSize_sublist ht.todo
  have hp : cost t.2.1 ≤ budget X s := by
    unfold budget planBudget at hc ⊢
    omega
  have hv : ∀ w ∈ t.2.1, bitSize w ≤ bitSize vs := fun w hw => bitSize_mem (ht.good.1.1.2.1 w hw)
  have hh := bitSize_map_le t.2.1 (fun w => w) (bitSize vs) hv
  change bitSize (List.map (id : List α → List α) t.2.1) ≤ _ at hh
  rw [List.map_id,rooted_length ht.good.1] at hh
  have ht1 := bitSize_prod t.1 t.2
  have ht2 := bitSize_prod t.2.1 t.2.2
  simp only [Prod.eta] at ht1 ht2
  have hm := Nat.mul_le_mul_right (bitSize vs+1) (show 2*cost t.2.1+1 ≤ 2*budget X s+1 by omega)
  simp only [bitSize_prod] at hi he ⊢
  unfold schedulerCapacity
  simp only [bitSize_prod]
  omega

theorem sweep_spec (closed : SubstringClosed {w | w ∈ vs}) (nil_mem : ([] : List α) ∈ vs)
    (supply : C.RecordSupply) (M : ℕ) (len : ∀ w ∈ vs, w.length ≤ M) :
    let o := sweep (vs,X,M)
    GoodPlan h o ∧ planBudget X o ≤ ((gs X).map (charge X)).sum ∧ o.2.2=[] ∧
      ∀ i ∈ ids X, Covered X o i := by
  have hi := h.iterate_advance vs closed supply M len (initial X) (h.initial_invariant vs nil_mem)
  have he := iterate_cappedStep_eq iterStep (gs X).length (schedulerCapacity (((vs,X,M),initial X) : Input α))
    (((vs,X,M),initial X) : Input α) (by
      intro n hn _
      rw [iterate_iterStep]
      apply h.state_size M (initial X) _ (hi n).1 (hi n).2.1
      have hh := (hi n).2.2.2
      have hm := Nat.mul_le_mul_right (maxExtras X M) (show n ≤ (gs X).length by omega)
      omega)
  have hh := hi (gs X).length
  let t := (advance vs X M)^[(gs X).length] (initial X)
  change Invariant h t ∧ _ at hh
  have hz : t.1=[] := by
    apply List.length_eq_zero_iff.mp
    have ht := hh.2.2.1
    change t.1.length ≤ (gs X).length-(gs X).length at ht
    omega
  have hr : t.2.2.2=[] := by
    by_contra hn
    obtain ⟨r,hr⟩ := List.exists_mem_of_ne_nil _ hn
    have ht := hh.1.targets r hr
    rw [hz] at ht
    exact List.not_mem_nil ht
  unfold sweep
  dsimp only
  rw [he,iterate_iterStep]
  change GoodPlan h t.2 ∧ _
  refine ⟨hh.1.good,?_,hr,?_⟩
  · change planBudget X t.2 ≤ _
    have hc := hh.2.1
    change budget X t ≤ budget X (initial X) at hc
    simpa only [budget,hz,initial,planBudget,cost_singleton,List.map_nil,List.sum_nil,Nat.add_zero,Nat.zero_add] using hc
  · intro i hi
    obtain ⟨j,rfl⟩ := (h.mem_ids i).mp hi
    rcases hh.1.ready j with hj|hj
    · rw [hz] at hj; exact False.elim (List.not_mem_nil hj)
    · exact hj
end Model
end Superstring.CollectionCode


namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode BlockClose
variable {α : Type} [Inhabited α] [LinearOrder α] [Coded α]
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_gs : Poly (gs : Env α → List ℕ) := by unfold gs; fun_prop
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_pick : Poly (fun q : Env α × List ℕ => pick q.1 q.2) := by
  unfold pick firstGood
  have hp : Poly (fun q : (Env α × List ℕ) × ℕ => q.1.2.all (fun j => lessEq (per q.1.1 q.2) (per q.1.1 j))) :=
    BitCode.Poly.allFn
      (p := fun q : ((Env α × List ℕ) × ℕ) × ℕ => lessEq (per q.1.1.1 q.1.2) (per q.1.1.1 q.2))
      (by fun_prop) (by fun_prop)
  exact (BitCode.Poly.headD 0).comp (BitCode.Poly.filterFn hp BitCode.Poly.snd)
@[fun_prop] theorem poly_without : Poly (fun q : List ℕ × ℕ => without q.1 q.2) := by
  unfold without
  exact BitCode.Poly.filterFn (p := fun q : (List ℕ × ℕ) × ℕ => !(equal q.2 q.1.2)) (by fun_prop) (by fun_prop)
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_inRequests : Poly (fun q : Env α × ℕ × List Request => inRequests q.1 q.2.1 q.2.2) := by
  unfold inRequests Request.target
  exact BitCode.Poly.filterFn (p := fun q : (Env α × ℕ × List Request) × Request => equal (owner q.1.1 q.2.2.1) q.1.2.1) (by fun_prop) (by fun_prop)
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_restRequests : Poly (fun q : Env α × ℕ × List Request => restRequests q.1 q.2.1 q.2.2) := by
  unfold restRequests Request.target
  exact BitCode.Poly.filterFn (p := fun q : (Env α × ℕ × List Request) × Request => !(equal (owner q.1.1 q.2.2.1) q.1.2.1)) (by fun_prop) (by fun_prop)
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_charge : Poly (fun q : Env α × ℕ => charge q.1 q.2) := by unfold charge; fun_prop
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_requestReserve : Poly (fun q : Env α × Request => q.2.reserve q.1) := by
  unfold Request.reserve Request.members Request.source
  fun_prop
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_planBudget : Poly (fun q : Env α × Plan α => planBudget q.1 q.2) := by
  have hr : Poly (fun q : Env α × Plan α => (q.2.2.2.map (Request.reserve q.1)).sum) :=
    BitCode.Poly.sum.comp (BitCode.Poly.mapFn
      (f := fun q : (Env α × Plan α) × Request => q.2.reserve q.1.1) (by fun_prop) (by fun_prop))
  have hb : Poly (fun q : Env α × Plan α => (q.2.2.1.map Block.reserve).sum) :=
    BlockClose.poly_reserves.comp (by fun_prop)
  unfold planBudget
  fun_prop
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_budget : Poly (fun q : Env α × State α => budget q.1 q.2) := by
  have hr : Poly (fun q : Env α × State α => (q.2.1.map (charge q.1)).sum) :=
    BitCode.Poly.sum.comp (BitCode.Poly.mapFn
      (f := fun q : (Env α × State α) × ℕ => charge q.1.1 q.2) (by fun_prop) (by fun_prop))
  unfold budget
  fun_prop
@[fun_prop] theorem poly_extraSizes (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (fun q : Env α × ℕ => extraSizes q.1 q.2) := by
  have hc := poly_complete hlt
  unfold extraSizes
  apply BitCode.Poly.flatMapFn (f := fun q : (Env α × ℕ) × ℕ =>
    (List.range ((data q.1.1 q.2).2.length+1)).map (fun cut => bitSize (complete q.1.1 q.2 cut q.1.2 [[]]).2))
  · exact BitCode.Poly.mapFn (f := fun q : ((Env α × ℕ) × ℕ) × ℕ =>
      bitSize (complete q.1.1.1 q.1.2 q.2 q.1.1.2 [[]]).2) (by fun_prop) (by fun_prop)
  · fun_prop
@[fun_prop] theorem poly_maxExtras (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (fun q : Env α × ℕ => maxExtras q.1 q.2) :=
  BitCode.Poly.maxFold.comp (poly_extraSizes hlt)
omit [Inhabited α] [LinearOrder α] in
@[fun_prop] theorem poly_initial : Poly (initial : Env α → State α) := by unfold initial; fun_prop
@[fun_prop] theorem poly_advance (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (fun q : Input α => advance q.1.1 q.1.2.1 q.1.2.2 q.2) := by
  have hp := poly_process hlt
  have ho : Poly (fun q : Input α =>
      process q.1.1 q.1.2.1 (pick q.1.2.1 q.2.1) q.1.2.2 (inRequests q.1.2.1 (pick q.1.2.1 q.2.1) q.2.2.2.2)) :=
    hp.comp (f := fun q : Input α => ((q.1.1,q.1.2.1),pick q.1.2.1 q.2.1,q.1.2.2,
      inRequests q.1.2.1 (pick q.1.2.1 q.2.1) q.2.2.2.2)) (by fun_prop)
  unfold advance
  dsimp only
  apply BitCode.Poly.ite (by fun_prop) (by fun_prop)
  fun_prop
@[fun_prop] theorem poly_schedulerStep (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (iterStep : Input α → Input α) := BitCode.Poly.fst.pair (poly_advance hlt)
@[fun_prop] theorem poly_schedulerCapacity (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (schedulerCapacity : Input α → ℕ) := by
  have hm := poly_maxExtras hlt
  unfold schedulerCapacity
  fun_prop
@[fun_prop] theorem poly_sweep (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (sweep : Context α → Plan α) := by
  have hc := poly_schedulerCapacity hlt
  have ht : Poly (fun q : Context α =>
      ((cappedStep iterStep)^[(gs q.2.1).length] (schedulerCapacity (q,initial q.2.1),(q,initial q.2.1))).2) :=
    (BitCode.Poly.cappedIterate (poly_schedulerStep hlt)).comp
      (f := fun q : Context α => ((gs q.2.1).length,(schedulerCapacity (q,initial q.2.1),(q,initial q.2.1)))) (by fun_prop)
  exact BitCode.Poly.snd.comp (BitCode.Poly.snd.comp ht)
end Superstring.CollectionCode


namespace Superstring.CollectionCode
open BitCode Hierarchical LayerArray WalkCode BlockClose
variable {α G : Type} [Inhabited α] [LinearOrder α] [Coded α]
def tour (q : Context α) : Walk α :=
  let o := sweep q
  close ((q.1,contents q.2.1),o.1,o.2.1)
@[fun_prop] theorem poly_tour (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (tour : Context α → Walk α) := by
  have hs := poly_sweep hlt
  exact BlockClose.poly_close.comp
    (f := fun q : Context α => ((q.1,contents q.2.1),(sweep q).1,(sweep q).2.1)) (by fun_prop)
namespace Model
variable {vs : Walk α} {X : Env α} {C : LayerCollection {w | w ∈ vs} G} (h : Model X C)
include h in
theorem tour_spec (closed : SubstringClosed {w | w ∈ vs}) (nil_mem : ([] : List α) ∈ vs)
    (supply : C.RecordSupply) (M : ℕ) (len : ∀ w ∈ vs, w.length ≤ M) :
    Runs {w | w ∈ vs} [] [] (tour (vs,X,M)) ∧
    cost (tour (vs,X,M)) ≤ ((gs X).map (charge X)).sum ∧
    ∀ i ∈ ids X, ∀ w ∈ ls X i, w ∈ tour (vs,X,M) := by
  obtain ⟨hg,hb,hr,hcov⟩ := h.sweep_spec closed nil_mem supply M len
  let o := sweep (vs,X,M)
  have hh := BlockClose.close_spec ((vs,contents X),o.1,o.2.1) closed (ids X) (owner X) (per X) (rank X)
    hg.1 hg.2.1 (by
      intro i hi
      rcases hcov i hi with hh|hh|⟨r,hm,_⟩
      · exact Or.inl hh
      · exact Or.inr hh
      · rw [hr] at hm; exact False.elim (List.not_mem_nil hm))
  change Runs _ [] [] (tour (vs,X,M)) ∧ _ at hh
  refine ⟨hh.1,?_,hh.2.2.2⟩
  have hc := hh.2.1
  change cost (tour (vs,X,M)) ≤ cost o.1+(o.2.1.map Block.reserve).sum at hc
  change planBudget X o ≤ _ at hb
  unfold planBudget at hb
  omega
end Model
end Superstring.CollectionCode

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring.WalkCode
open BitCode Hierarchical
variable {α : Type} [Inhabited α]
def letter (s t : List α) : List α := if s.length<t.length then [t.reverse.headD default] else []
def output (P : Walk α) : List α := (P.zip P.tail).flatMap (fun q => letter q.1 q.2)
@[simp] theorem output_nil : output ([] : Walk α)=[] := rfl
@[simp] theorem output_singleton (s : List α) : output [s]=[] := rfl
@[simp] theorem output_cons_cons (s t : List α) (P : Walk α) :
    output (s::t::P) = letter s t ++ output (t::P) := by simp only [output,List.tail_cons,List.zip_cons_cons,List.flatMap_cons]
@[simp] theorem length_letter (s t : List α) : (letter s t).length = if s.length<t.length then 1 else 0 := by
  unfold letter; split <;> rfl
@[simp] theorem length_output (P : Walk α) : (output P).length = cost P := by
  induction P using List.twoStepInduction with
  | nil => rfl
  | singleton a => rfl
  | cons_cons s t P _ ih => rw [output_cons_cons,List.length_append,length_letter,ih,cost_cons_cons]
theorem letter_up (s : List α) (a : α) : letter s (s++[a])=[a] := by
  simp [letter,List.reverse_append]
theorem letter_down (t : List α) (a : α) : letter (a::t) t=[] := by simp [letter]

theorem visited_output {V : Set (List α)} {s : List α} {P : Walk α} (h : Valid V (s::P))
    {w : List α} (hw : w ∈ s::P) : w <:+: s++output (s::P) := by
  induction P generalizing s with
  | nil => have he := List.mem_singleton.mp hw; subst w; simp
  | cons t P ih =>
    obtain ⟨he,hchain⟩ := List.isChain_cons_cons.mp h.2.2
    rcases List.mem_cons.mp hw with rfl|hw
    · exact List.infix_append_left
    · have ht : Valid V (t::P) := ⟨by simp,fun w hw => h.2.1 w (List.mem_cons_of_mem _ hw),hchain⟩
      have hv := ih ht hw
      rw [output_cons_cons]
      rcases he with ⟨a,rfl⟩|⟨a,rfl⟩
      · simpa only [letter_up,List.append_assoc] using hv
      · simpa only [letter_down,List.nil_append,List.cons_append] using (List.infix_cons hv (a:=a))

theorem rooted_output {V : Set (List α)} {P : Walk α} (h : Runs V [] [] P) :
    ∀ w ∈ P, w <:+: output P := by
  cases P with
  | nil => exact False.elim (h.1.1 rfl)
  | cons s P =>
    have hs : s=[] := by simpa using h.2.1
    subst s
    intro w hw
    simpa using visited_output h.1 hw

variable [Coded α]
@[fun_prop] theorem poly_letter : Poly (fun q : List α × List α => letter q.1 q.2) := by
  unfold letter
  apply CollectionCode.poly_cond (by fun_prop) (by fun_prop) (by fun_prop)
@[fun_prop] theorem poly_output : Poly (output : Walk α → List α) := by
  unfold output
  exact BitCode.Poly.flatMapFn (f := fun q : Walk α × (List α × List α) => letter q.2.1 q.2.2) (by fun_prop) (by fun_prop)
end Superstring.WalkCode


namespace Superstring.CollectionCode.Model
open BitCode Hierarchical LayerArray WalkCode BlockClose
variable {α G : Type} [Inhabited α] [LinearOrder α] [Coded α]
variable {V : Set (List α)} {X : Env α} {C : LayerCollection V G} (h : Model X C)
include h in
theorem tour_spec_general (vs : Walk α) (hv : V={w | w ∈ vs})
    (closed : SubstringClosed V) (nil_mem : ([] : List α) ∈ V)
    (supply : C.RecordSupply) (M : ℕ) (len : ∀ w ∈ vs, w.length ≤ M) :
    Runs V [] [] (tour (vs,X,M)) ∧ cost (tour (vs,X,M)) ≤ ((gs X).map (charge X)).sum ∧
    ∀ i : C.Id, ∀ w ∈ (C.layerAt i).Content, w ∈ tour (vs,X,M) := by
  subst V
  obtain ⟨hp,hc,hcov⟩ := h.tour_spec closed nil_mem supply M len
  exact ⟨hp,hc,fun i w hw => hcov (h.encode i) (h.id_mem i) w ((h.content_iff i w).mpr hw)⟩
include h in
omit [Coded α] in
theorem charge_sum [Fintype G] : ((gs X).map (charge X)).sum = 2*∑ g, C.size g*C.period g := by
  classical
  rw [← List.sum_toFinset _ h.nodup,Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun g _ => h.group g)
  · intro g _; exact List.mem_toFinset.mpr ((h.groups _).mpr ⟨g,rfl⟩)
  · intro a _ b _ he; exact h.group_inj he
  · intro j hj
    obtain ⟨g,hg⟩ := (h.groups _).mp (List.mem_toFinset.mp hj)
    exact ⟨g,Finset.mem_univ _,hg⟩
  · intro g _; simp only [charge,h.size,h.per_eq]
end Superstring.CollectionCode.Model


namespace Superstring.ThreadArray
open BitCode Hierarchical CollectionCode
variable {α : Type} [Coded α] [Inhabited α] [LinearOrder α]
def environment (K : Code α) : Env α :=
  (((List.range K.1.length).map (data K),groups K),K.1.length)

@[simp] theorem environment_rows (K : Code α) : (environment K).1.1.length = K.1.length := by
  simp only [environment,List.length_map,List.length_range]
@[simp] theorem environment_stride (K : Code α) : stride (environment K) = K.1.length := rfl

theorem environment_data (K : Code α) (g : ℕ) (hg : g < K.1.length) :
    CollectionCode.data (environment K) g = data K g := by
  simp only [CollectionCode.data,environment,List.getElem?_map,List.getElem?_range hg,
    Option.map_some,Option.getD_some]

noncomputable def model {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (closed : SubstringClosed V) :
    CollectionCode.Model (environment K) (collection h closed) where
  group := fun g => g.val.val
  group_inj := by intro g d hd; exact Subtype.ext (Fin.ext hd)
  groups := by
    intro j
    change j ∈ groups K ↔ _
    simp only [groups,List.mem_filter,List.mem_range,equal,decide_eq_true_eq]
    constructor
    · rintro ⟨hj,hr⟩
      exact ⟨⟨⟨j,hj⟩,hr⟩,rfl⟩
    · rintro ⟨g,rfl⟩
      exact ⟨g.val.isLt,g.property⟩
  nodup := List.Pairwise.filter _ List.nodup_range
  bound := by intro g; simpa only [environment_rows] using g.val.isLt
  size := by intro g; rw [environment_data K _ g.val.isLt]; exact data_size h g.val
  capacity := by
    intro g
    change Fintype.card (C.Aligned (C.text g.val)) ≤ K.1.length
    rw [← aligned_length h]
    exact aligned_length_le K g.val.val
  rep := by
    intro g i
    rw [environment_data K _ g.val.isLt]
    exact data_represents h closed g.val i
  phase_eq := by
    intro g
    unfold CollectionCode.phase
    rw [environment_data K _ g.val.isLt]
    exact RotationCode.phase_eq_distinguished (collection h closed) g (period_spec h g.val).1
      (layerWord K g.val.val) (length_layerWord h g.val) (text_layerWord h g.val)

@[fun_prop] theorem poly_environment : Poly (environment (α:=α)) := by
  have hm : Poly (fun K : Code α => (List.range K.1.length).map (data K)) :=
    BitCode.Poly.mapFn (f := fun q : Code α × ℕ => data q.1 q.2) poly_data (by fun_prop)
  unfold environment
  fun_prop
end Superstring.ThreadArray


namespace Superstring.Executable
open BitCode Hierarchical ThreadArray
variable {α : Type} [Inhabited α] [LinearOrder α] [Coded α]
abbrev code (S : List (List α)) : ThreadArray.Code α := (Computable.downWords S,Computable.edges S)
def context (S : List (List α)) : CollectionCode.Context α :=
  (Computable.vertices S,ThreadArray.environment (code S),Computable.countDepth S)
def solve (S : List (List α)) : List α := WalkCode.output (CollectionCode.tour (context S))
@[fun_prop] theorem poly_code : Poly (code : List (List α) → ThreadArray.Code α) := by unfold code; fun_prop
@[fun_prop] theorem poly_context : Poly (context : List (List α) → CollectionCode.Context α) :=
  Computable.poly_vertices.pair ((ThreadArray.poly_environment.comp poly_code).pair Computable.poly_countDepth)
@[fun_prop] theorem poly_solve (hlt : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (solve : List (List α) → List α) := by
  unfold solve
  have h := (WalkCode.poly_output (α:=α)).comp ((CollectionCode.poly_tour hlt).comp (f := context) poly_context)
  simp only [Function.comp_def] at h
  exact h

theorem represents (S : List (List α)) : ThreadArray.Represents (code S) (Computable.arrayThreading S) :=
  ⟨fun _ => rfl,fun _ => rfl⟩

omit [Inhabited α] [Coded α] in
theorem vertices_eq (S : List (List α)) : ((Input.data S).vertices : Set (List α)) = {w | w ∈ Computable.vertices S} := by
  ext w
  change w ∈ Input.vertices S ↔ w ∈ Computable.vertices S
  rw [← Computable.vertices_eq S,List.mem_toFinset]

omit [Inhabited α] [Coded α] in
theorem length_vertices (S : List (List α)) (w : List α) (hw : w ∈ Computable.vertices S) :
    w.length ≤ Computable.countDepth S := by
  have h := le_maxFold ((Computable.vertices S).map List.length) 0 (List.mem_map.mpr ⟨w,hw,rfl⟩)
  unfold Computable.countDepth
  omega

omit [Inhabited α] [Coded α] in
theorem closed (S : List (List α)) : SubstringClosed ((Input.data S).vertices : Set (List α)) :=
  Input.closed S

theorem histogram (S : List (List α)) (s : List α) (hs : s ≠ []) :
    Fintype.card (Family.Occurrence (ThreadArray.collection (represents S) (closed S)).layerAt s) =
      (Input.data S).count s := by
  rw [ThreadArray.collection_histogram,← Threading.card_recorded,Computable.arrayThreading_recorded_count S hs]

theorem supply (S : List (List α)) : (ThreadArray.collection (represents S) (closed S)).RecordSupply := by
  apply LayerCollection.recordSupply_of_histogram _ (Input.data S) (Counts.Data.input_wellFormed S) rfl
  · exact histogram S
  · intro g; exact (ThreadArray.period_spec (represents S) g.val).1

theorem solve_spec (S : List (List α)) :
    (∀ s ∈ S, s <:+: solve S) ∧ (solve S).length ≤ 2*(Input.data S).weight := by
  classical
  let C := ThreadArray.collection (represents S) (closed S)
  let h := ThreadArray.model (represents S) (closed S)
  obtain ⟨hp,hc,hcov⟩ := h.tour_spec_general (Computable.vertices S) (vertices_eq S)
    (closed S) (Counts.Data.input_wellFormed S).empty_mem (supply S) (Computable.countDepth S) (length_vertices S)
  have hbudget : ((CollectionCode.gs (ThreadArray.environment (code S))).map
      (CollectionCode.charge (ThreadArray.environment (code S)))).sum = 2*(Input.data S).weight := by
    rw [h.charge_sum]
    have hh := ThreadArray.collection_budget (represents S) (closed S)
    have he : (∑ g, C.size g*C.period g) = (code S).1.length := by
      simpa only [C,Nat.mul_comm] using hh
    change 2*(∑ g, C.size g*C.period g)=_
    rw [he]
    exact congrArg (2*·) (Computable.downWords_length S)
  constructor
  · apply (Input.core_superstring_iff S (solve S)).mp
    intro s hs
    have hsV := Input.required_mem hs
    have hsne := (Input.mem_core.mp hs).2.1
    have hcount := (Input.data S).required_le_count hsV hsne hs
    have hn : 0 < Fintype.card (Family.Occurrence C.layerAt s) := by
      rw [show Fintype.card (Family.Occurrence C.layerAt s)=(Input.data S).count s from histogram S s hsne]
      omega
    obtain ⟨o⟩ := Fintype.card_pos_iff.mp hn
    let L := C.layerAt o.1
    have hpre : s <+: textWord (C.text o.1.1) o.2.val.val (L.last o.2.val.val) :=
      (L.records_iff_prefix s o.2.val.val).mp o.2.property
    have hv := hcov o.1 _ ⟨o.2.val.val,L.last o.2.val.val,L.first_le_last o.2.val.val,le_rfl,rfl⟩
    exact hpre.isInfix.trans (WalkCode.rooted_output hp _ hv)
  · unfold solve
    rw [WalkCode.length_output]
    exact hc.trans_eq hbudget
end Superstring.Executable

end OAI
end
end

section
section
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace OAI

namespace Superstring
open BitCode

theorem bitsList_eq_encodeList {α : Type} [Coded α] (e : α → List Bool)
    (he : ∀ a, bits a = e a) (xs : List α) : bits xs = encodeList e xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change false :: (bits a ++ bits xs) = false :: (e a ++ encodeList e xs)
    rw [he,ih]

theorem bitsSymbol_eq (s : Symbol) : bits s = encodeSymbol s :=
  bitsList_eq_encodeList _ (fun _ => rfl) s

theorem bitsWord_eq (w : Word) : bits w = encodeWord w :=
  bitsList_eq_encodeList _ bitsSymbol_eq w

theorem bitsInstance_eq (S : Instance) : bits S = encodeInstance S :=
  bitsList_eq_encodeList _ bitsWord_eq S

def answer : Instance → Word := Executable.solve

theorem answer_poly : Poly answer := by
  unfold answer
  apply Executable.poly_solve
  convert (Poly.ltList (α:=Bool) Poly.ltBool) using 1
  funext q
  exact decide_eq_decide.mpr Iff.rfl

theorem answer_implementation : HasPolynomialImplementation answer := by
  have hc := RunsInPolyTime.certificate answer_poly
  have hi : (bits : Instance → List Bool) = encodeInstance := funext bitsInstance_eq
  have ho : (bits : Word → List Bool) = encodeWord := funext bitsWord_eq
  change ∃ M : Turing.TM2ComputableInPolyTime bits bits answer, ∀ k : M.tm.K, Finite (M.tm.Γ k) at hc
  rw [hi,ho] at hc
  exact hc

theorem weight_le_opt_with (S : Instance) (d : DecidableEq Symbol) :
    @Counts.Data.weight Symbol d inferInstance (@Input.data Symbol d S) ≤ opt S := by
  have he : d = @instDecidableEqList Bool instDecidableEqBool := Subsingleton.elim _ _
  rw [he]
  exact weight_le_opt S

theorem answer_spec (S : Instance) : IsCommonSuperstring S (answer S) ∧
    (answer S).length ≤ 2*opt S := by
  obtain ⟨ht,hl⟩ := Executable.solve_spec S
  refine ⟨ht, ?_⟩
  apply hl.trans
  exact Nat.mul_le_mul_left 2 (weight_le_opt_with S LinearOrder.toDecidableEq)

/-- The deterministic algorithm with its exact finite-alphabet bit-machine
certificate, contiguous coverage, and factor-two bound in symbols. -/
theorem main_oai : ∃ f : Instance → Word,
    HasPolynomialImplementation f ∧
    ∀ S, IsCommonSuperstring S (f S) ∧ (f S).length ≤ 2 * opt S :=
  ⟨answer, answer_implementation, answer_spec⟩


end Superstring

end OAI
end
end

theorem solution : type_of% @OAI.Superstring.main_oai := @OAI.Superstring.main_oai
