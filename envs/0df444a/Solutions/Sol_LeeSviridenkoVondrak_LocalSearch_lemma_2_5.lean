-- Prove2me | solution 1 for LeeSviridenkoVondrak.LocalSearch.lemma_2_5
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-27T09:14:04.747072+00:00
-- url     : https://prove2.me/submissions/13ad7cc9-7bde-4810-a01d-2ee2c996b5a6

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_LeeSviridenkoVondrak_LocalSearch_Model
import Definitions.Def_LeeSviridenkoVondrak_LocalSearch_Exchange

open scoped symmDiff

namespace S201LSV
open LeeSviridenkoVondrak.LocalSearch

/-- partition matroid on `Fin 3` in which `a` and `b` are parallel -/
def PM (a b : Fin 3) : Matroid (Fin 3) :=
  (IndepMatroid.ofFinset Set.univ (fun S : Finset (Fin 3) => ¬ ({a, b} ⊆ S ∧ a ≠ b))
    (by simp)
    (by intro I J hJ hIJ h; exact hJ ⟨h.1.trans hIJ, h.2⟩)
    (by revert a b; decide)
    (by intro I _; simp)).matroid

lemma PM_indep (a b : Fin 3) (S : Finset (Fin 3)) :
    (PM a b).Indep (↑S : Set (Fin 3)) ↔ ¬ ({a, b} ⊆ S ∧ a ≠ b) := by
  simp [PM]

lemma PM_E (a b : Fin 3) : (PM a b).E = Set.univ := rfl

def M₁ : Matroid (Fin 3) := PM 0 1
def M₂ : Matroid (Fin 3) := PM 1 2
def I0 : Finset (Fin 3) := {1}
def J0 : Finset (Fin 3) := {0, 2}

def okE (x y : Fin 3) : Prop := (x = 1 ∧ y ≠ 1) ∨ (y = 1 ∧ x ≠ 1)

instance (x y : Fin 3) : Decidable (okE x y) := by unfold okE; infer_instance

lemma twoArc_ok (x y : Fin 3) (h : TwoArc M₁ M₂ I0 x y) : okE x y := by
  unfold TwoArc ExchangeArc at h
  unfold okE
  rcases h with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
  · left; simp [I0] at h1 h2; exact ⟨h1, h2⟩
  · right; simp [I0] at h1 h2; exact ⟨h1, h2⟩

def edgesOK (L : List (Fin 3)) (cl : Bool) : Bool :=
  (L.zip L.tail).all (fun p => decide (okE p.1 p.2)) &&
  (!cl || match L.getLast?, L.head? with
    | some x, some y => decide (okE x y)
    | _, _ => true)

def endOK (L : List (Fin 3)) (cl : Bool) : Bool :=
  cl || ((L.head?.all (fun x => decide (x = 1))) && (L.getLast?.all (fun x => decide (x = 1))))

/-- decidable list-level consequence -/
def Q (L : List (Fin 3)) (cl : Bool) : Prop :=
  L.Nodup → edgesOK L cl = true → endOK L cl = true →
  ((0 : Fin 3) ∈ L → (1 : Fin 3) ∈ L ∧ (2 : Fin 3) ∉ L) ∧
  ((2 : Fin 3) ∈ L → (1 : Fin 3) ∈ L ∧ (0 : Fin 3) ∉ L)

instance (L : List (Fin 3)) (cl : Bool) : Decidable (Q L cl) := by unfold Q; infer_instance

lemma Q1 : ∀ (a : Fin 3) (cl : Bool), Q [a] cl := by decide
lemma Q2 : ∀ (a b : Fin 3) (cl : Bool), Q [a, b] cl := by decide
lemma Q3 : ∀ (a b c : Fin 3) (cl : Bool), Q [a, b, c] cl := by decide
lemma no4 : ∀ (a b c d : Fin 3), ¬ [a, b, c, d].Nodup := by decide

lemma Q_all (L : List (Fin 3)) (cl : Bool) : Q L cl := by
  match L with
  | [] => intro _ _ _; simp
  | [a] => exact Q1 a cl
  | [a, b] => exact Q2 a b cl
  | [a, b, c] => exact Q3 a b c cl
  | a :: b :: c :: d :: t =>
    intro hnd
    exact absurd (hnd.sublist (by simp)) (no4 a b c d)

lemma endpoint_one (A : WalkData 3) (hA : FeasibleWalk M₁ M₂ I0 A) (x : Fin 3)
    (hx : A.endpoint x) : x = 1 := by
  obtain ⟨_, _, hsub⟩ := hA
  have hxA : x ∈ A.support := by
    unfold WalkData.support
    rcases hx.2 with h | h
    · exact List.mem_toFinset.mpr (List.mem_of_mem_head? h)
    · exact List.mem_toFinset.mpr (List.mem_of_mem_getLast? h)
  have hB : IsSubpath A ⟨[x], false⟩ := by
    refine ⟨rfl, by simp, by simp, ?_, ?_⟩
    · intro z hz; simp [WalkData.support] at hz; subst hz; exact hxA
    · intro u v huv
      simp [WalkData.edge] at huv
  have h := hsub _ hB (by
    intro z hz
    left
    simp [WalkData.endpoint] at hz
    rcases hz with rfl | rfl <;> exact hx)
  have hs : (⟨[x], false⟩ : WalkData 3).support = {x} := by simp [WalkData.support]
  rw [hs] at h
  obtain ⟨h1, h2⟩ := h
  rw [M₁, PM_indep] at h1
  rw [M₂, PM_indep] at h2
  revert h1 h2
  fin_cases x <;> decide

lemma walk_prop (A : WalkData 3) (hA : FeasibleWalk M₁ M₂ I0 A) :
    ((0 : Fin 3) ∈ A.support → (1 : Fin 3) ∈ A.support ∧ (2 : Fin 3) ∉ A.support) ∧
    ((2 : Fin 3) ∈ A.support → (1 : Fin 3) ∈ A.support ∧ (0 : Fin 3) ∉ A.support) := by
  have hE : ∀ x y, A.edge x y → okE x y := fun x y hxy => twoArc_ok x y (hA.1.2.2.2 x y hxy)
  have hP : ∀ x, A.endpoint x → x = 1 := fun x hx => endpoint_one A hA x hx
  have he : edgesOK A.vertices A.closed = true := by
    unfold edgesOK
    rw [Bool.and_eq_true]
    constructor
    · rw [List.all_eq_true]
      intro p hp
      exact decide_eq_true (hE p.1 p.2 (Or.inl hp))
    · cases hc : A.closed
      · rfl
      · simp only [Bool.not_true, Bool.false_or]
        cases hl : A.vertices.getLast? with
        | none => rfl
        | some x =>
          cases hh : A.vertices.head? with
          | none => rfl
          | some y => exact decide_eq_true (hE x y (Or.inr ⟨hc, hl, hh⟩))
  have hn : endOK A.vertices A.closed = true := by
    unfold endOK
    cases hc : A.closed
    · simp only [Bool.false_or, Bool.and_eq_true, Option.all_eq_true]
      refine ⟨fun x hx => decide_eq_true (hP x ⟨hc, Or.inl hx⟩),
        fun x hx => decide_eq_true (hP x ⟨hc, Or.inr hx⟩)⟩
    · rfl
  have hQ := Q_all A.vertices A.closed hA.1.2.1 he hn
  simpa [WalkData.support] using hQ

lemma I0_indep1 : M₁.Indep (↑I0 : Set (Fin 3)) := by rw [M₁, PM_indep]; decide
lemma I0_indep2 : M₂.Indep (↑I0 : Set (Fin 3)) := by rw [M₂, PM_indep]; decide
lemma J0_indep1 : M₁.Indep (↑J0 : Set (Fin 3)) := by rw [M₁, PM_indep]; decide
lemma J0_indep2 : M₂.Indep (↑J0 : Set (Fin 3)) := by rw [M₂, PM_indep]; decide

end S201LSV

open LeeSviridenkoVondrak.LocalSearch in
theorem solution : ¬ (∀ {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (hE₁ : M₁.E = Set.univ) (hE₂ : M₂.E = Set.univ)
    (I J : Finset (Fin n))
    (hI₁ : M₁.Indep (↑I : Set (Fin n))) (hI₂ : M₂.Indep (↑I : Set (Fin n)))
    (hJ₁ : M₁.Indep (↑J : Set (Fin n))) (hJ₂ : M₂.Indep (↑J : Set (Fin n))),
    ∃ s m : ℕ, ∃ A : Fin m → WalkData n,
      (∀ i, FeasibleWalk M₁ M₂ I (A i) ∧ (A i).support ⊆ I ∆ J) ∧
      ∀ x ∈ I ∆ J, multiplicity (fun i => (A i).support) x = 2 ^ s) := by
  intro H
  obtain ⟨s, m, A, hA, hmult⟩ := H S201LSV.M₁ S201LSV.M₂ rfl rfl S201LSV.I0 S201LSV.J0
    S201LSV.I0_indep1 S201LSV.I0_indep2 S201LSV.J0_indep1 S201LSV.J0_indep2
  have h0 := hmult 0 (by decide)
  have h1 := hmult 1 (by decide)
  have h2 := hmult 2 (by decide)
  unfold LeeSviridenkoVondrak.LocalSearch.multiplicity at h0 h1 h2
  have hsub : (Finset.univ.filter (fun i => (0 : Fin 3) ∈ (A i).support)) ∪
      (Finset.univ.filter (fun i => (2 : Fin 3) ∈ (A i).support)) ⊆
      Finset.univ.filter (fun i => (1 : Fin 3) ∈ (A i).support) := by
    intro i hi
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rcases hi with h | h
    · exact ((S201LSV.walk_prop (A i) (hA i).1).1 h).1
    · exact ((S201LSV.walk_prop (A i) (hA i).1).2 h).1
  have hdisj : Disjoint (Finset.univ.filter (fun i => (0 : Fin 3) ∈ (A i).support))
      (Finset.univ.filter (fun i => (2 : Fin 3) ∈ (A i).support)) := by
    rw [Finset.disjoint_filter]
    intro i _ h
    exact ((S201LSV.walk_prop (A i) (hA i).1).1 h).2
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, h0, h1, h2] at this
  have hp : 0 < 2 ^ s := by positivity
  omega
