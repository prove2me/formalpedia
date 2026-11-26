-- Prove2me | solution 1 for NisanRonen.Rounding.two_jobs_grid_bound_split_choice
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T07:26:37.611826+00:00
-- url     : https://prove2.me/submissions/dbacc179-9404-4099-9768-280072aa6a1f

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private structure FourCosts where
  groupedFirst : ℤ
  firstSplit : ℤ
  secondSplit : ℤ
  groupedLast : ℤ

private def costs (p q r s : ℤ) : FourCosts :=
  ⟨p + q, max q r, max p s, r + s⟩

private def winsFirst (c : FourCosts) : Prop :=
  c.groupedFirst ≤ c.firstSplit ∧ c.groupedFirst ≤ c.secondSplit ∧ c.groupedFirst ≤ c.groupedLast

private def winsFirstSplit (c : FourCosts) : Prop :=
  c.firstSplit < c.groupedFirst ∧ c.firstSplit ≤ c.secondSplit ∧ c.firstSplit ≤ c.groupedLast

private def winsSecondSplit (c : FourCosts) : Prop :=
  c.secondSplit < c.groupedFirst ∧ c.secondSplit < c.firstSplit ∧ c.secondSplit ≤ c.groupedLast

private def winsLast (c : FourCosts) : Prop :=
  c.groupedLast < c.groupedFirst ∧ c.groupedLast < c.firstSplit ∧ c.groupedLast < c.secondSplit

private def preserves (d t : FourCosts) : Prop :=
  (winsFirst d → t.groupedFirst ≤ t.firstSplit ∧ t.groupedFirst ≤ t.secondSplit ∧ t.groupedFirst ≤ t.groupedLast) ∧
  (winsFirstSplit d → t.firstSplit ≤ t.groupedFirst ∧ t.firstSplit ≤ t.secondSplit ∧ t.firstSplit ≤ t.groupedLast) ∧
  (winsSecondSplit d → t.secondSplit ≤ t.groupedFirst ∧ t.secondSplit ≤ t.firstSplit ∧ t.secondSplit ≤ t.groupedLast) ∧
  (winsLast d → t.groupedLast ≤ t.groupedFirst ∧ t.groupedLast ≤ t.firstSplit ∧ t.groupedLast ≤ t.secondSplit)

private def interval (a b z : ℤ) := a ≤ z ∧ z ≤ b

set_option maxHeartbeats 1200000

private theorem outcome1_vs_0
    (a b p q r s P Q R S : ℤ) (ha : 2 ≤ a)
    (hp : interval a b p) (hq : interval a b q) (hr : interval a b r) (hs : interval a b s)
    (hP : interval a b P) (hQ : interval a b Q) (hR : interval a b R) (hS : interval a b S)
    (h0 : ∀ w u, interval a b w → interval a b u →
      preserves (costs P Q w u) (costs p q w u))
    (h1 : ∀ w u, interval a b w → interval a b u →
      preserves (costs w u R S) (costs w u r s)) :
    winsFirstSplit (costs P Q R S) → (costs p q r s).firstSplit ≤ (costs p q r s).groupedFirst + 1 := by
  intro hx
  have check1 (hw : interval a b (a)) (hu : interval a b (a))
      (hwin : winsFirstSplit (costs (a) (a) R S)) :=
    ((h1 (a) (a) hw hu).2.1 hwin).1
  have check2 (hw : interval a b (R)) (hu : interval a b (a))
      (hwin : winsFirstSplit (costs (R) (a) R S)) :=
    ((h1 (R) (a) hw hu).2.1 hwin).1
  have check3 (hw : interval a b (a)) (hu : interval a b (R - a + 1))
      (hwin : winsFirstSplit (costs (a) (R - a + 1) R S)) :=
    ((h1 (a) (R - a + 1) hw hu).2.1 hwin).1
  have check4 (hw : interval a b (b)) (hu : interval a b (p + q + 1))
      (hwin : winsFirstSplit (costs P Q (b) (p + q + 1))) :=
    ((h0 (b) (p + q + 1) hw hu).2.1 hwin).1
  have check5 (hw : interval a b (b)) (hu : interval a b (p + q + 1))
      (hwin : winsSecondSplit (costs P Q (b) (p + q + 1))) :=
    ((h0 (b) (p + q + 1) hw hu).2.2.1 hwin).1
  clear h0 h1
  simp only [interval, costs, winsFirst, winsFirstSplit, winsSecondSplit, winsLast,
    ← max_add_add_right, max_le_iff, le_max_iff, max_lt_iff, lt_max_iff] at *
  grind (splits := 50) only [max_def]

private theorem outcome1_vs_2
    (a b p q r s P Q R S : ℤ) (ha : 2 ≤ a)
    (hp : interval a b p) (hq : interval a b q) (hr : interval a b r) (hs : interval a b s)
    (hP : interval a b P) (hQ : interval a b Q) (hR : interval a b R) (hS : interval a b S)
    (h0 : ∀ w u, interval a b w → interval a b u →
      preserves (costs P Q w u) (costs p q w u))
    (h1 : ∀ w u, interval a b w → interval a b u →
      preserves (costs w u R S) (costs w u r s)) :
    winsFirstSplit (costs P Q R S) → (costs p q r s).firstSplit ≤ (costs p q r s).secondSplit + 1 := by
  intro hx
  have check1 (hw : interval a b (P)) (hu : interval a b (a))
      (hwin : winsFirstSplit (costs P Q (P) (a))) :=
    ((h0 (P) (a) hw hu).2.1 hwin).2.1
  have check2 (hw : interval a b (a)) (hu : interval a b (Q))
      (hwin : winsFirstSplit (costs P Q (a) (Q))) :=
    ((h0 (a) (Q) hw hu).2.1 hwin).2.1
  have check3 (hw : interval a b (R)) (hu : interval a b (a))
      (hwin : winsFirstSplit (costs (R) (a) R S)) :=
    ((h1 (R) (a) hw hu).2.1 hwin).2.1
  have check4 (hw : interval a b (a)) (hu : interval a b (S))
      (hwin : winsFirstSplit (costs (a) (S) R S)) :=
    ((h1 (a) (S) hw hu).2.1 hwin).2.1
  clear h0 h1
  simp only [interval, costs, winsFirst, winsFirstSplit, winsSecondSplit, winsLast,
    ← max_add_add_right, max_le_iff, le_max_iff, max_lt_iff, lt_max_iff] at *
  grind (splits := 50) only [max_def]

private theorem outcome1_vs_3
    (a b p q r s P Q R S : ℤ) (ha : 2 ≤ a)
    (hp : interval a b p) (hq : interval a b q) (hr : interval a b r) (hs : interval a b s)
    (hP : interval a b P) (hQ : interval a b Q) (hR : interval a b R) (hS : interval a b S)
    (h0 : ∀ w u, interval a b w → interval a b u →
      preserves (costs P Q w u) (costs p q w u))
    (h1 : ∀ w u, interval a b w → interval a b u →
      preserves (costs w u R S) (costs w u r s)) :
    winsFirstSplit (costs P Q R S) → (costs p q r s).firstSplit ≤ (costs p q r s).groupedLast + 1 := by
  intro hx
  have check1 (hw : interval a b (a)) (hu : interval a b (Q))
      (hwin : winsFirstSplit (costs P Q (a) (Q))) :=
    ((h0 (a) (Q) hw hu).2.1 hwin).2.2
  have check2 (hw : interval a b (a)) (hu : interval a b (a))
      (hwin : winsFirstSplit (costs P Q (a) (a))) :=
    ((h0 (a) (a) hw hu).2.1 hwin).2.2
  have check3 (hw : interval a b (a)) (hu : interval a b (Q - a))
      (hwin : winsFirstSplit (costs P Q (a) (Q - a))) :=
    ((h0 (a) (Q - a) hw hu).2.1 hwin).2.2
  have check4 (hw : interval a b (b)) (hu : interval a b (R + S))
      (hwin : winsFirstSplit (costs (b) (R + S) R S)) :=
    ((h1 (b) (R + S) hw hu).2.1 hwin).2.2
  have check5 (hw : interval a b (b)) (hu : interval a b (b))
      (hwin : winsFirstSplit (costs (b) (b) R S)) :=
    ((h1 (b) (b) hw hu).2.1 hwin).2.2
  clear h0 h1
  simp only [interval, costs, winsFirst, winsFirstSplit, winsSecondSplit, winsLast,
    ← max_add_add_right, max_le_iff, le_max_iff, max_lt_iff, lt_max_iff] at *
  grind (splits := 50) only [max_def]

private theorem outcome2_vs_0
    (a b p q r s P Q R S : ℤ) (ha : 2 ≤ a)
    (hp : interval a b p) (hq : interval a b q) (hr : interval a b r) (hs : interval a b s)
    (hP : interval a b P) (hQ : interval a b Q) (hR : interval a b R) (hS : interval a b S)
    (h0 : ∀ w u, interval a b w → interval a b u →
      preserves (costs P Q w u) (costs p q w u))
    (h1 : ∀ w u, interval a b w → interval a b u →
      preserves (costs w u R S) (costs w u r s)) :
    winsSecondSplit (costs P Q R S) → (costs p q r s).secondSplit ≤ (costs p q r s).groupedFirst + 1 := by
  intro hx
  have check1 (hw : interval a b (a)) (hu : interval a b (a))
      (hwin : winsSecondSplit (costs (a) (a) R S)) :=
    ((h1 (a) (a) hw hu).2.2.1 hwin).1
  have check2 (hw : interval a b (a)) (hu : interval a b (S - a + 1))
      (hwin : winsSecondSplit (costs (a) (S - a + 1) R S)) :=
    ((h1 (a) (S - a + 1) hw hu).2.2.1 hwin).1
  have check3 (hw : interval a b (b)) (hu : interval a b (p + q + 1))
      (hwin : winsSecondSplit (costs P Q (b) (p + q + 1))) :=
    ((h0 (b) (p + q + 1) hw hu).2.2.1 hwin).1
  have check4 (hw : interval a b (a)) (hu : interval a b (S + 1))
      (hwin : winsSecondSplit (costs (a) (S + 1) R S)) :=
    ((h1 (a) (S + 1) hw hu).2.2.1 hwin).1
  clear h0 h1
  simp only [interval, costs, winsFirst, winsFirstSplit, winsSecondSplit, winsLast,
    ← max_add_add_right, max_le_iff, le_max_iff, max_lt_iff, lt_max_iff] at *
  grind (splits := 50) only [max_def]

private theorem outcome2_vs_1
    (a b p q r s P Q R S : ℤ) (ha : 2 ≤ a)
    (hp : interval a b p) (hq : interval a b q) (hr : interval a b r) (hs : interval a b s)
    (hP : interval a b P) (hQ : interval a b Q) (hR : interval a b R) (hS : interval a b S)
    (h0 : ∀ w u, interval a b w → interval a b u →
      preserves (costs P Q w u) (costs p q w u))
    (h1 : ∀ w u, interval a b w → interval a b u →
      preserves (costs w u R S) (costs w u r s)) :
    winsSecondSplit (costs P Q R S) → (costs p q r s).secondSplit ≤ (costs p q r s).firstSplit + 1 := by
  intro hx
  have check1 (hw : interval a b (P + 1)) (hu : interval a b (a))
      (hwin : winsSecondSplit (costs P Q (P + 1) (a))) :=
    ((h0 (P + 1) (a) hw hu).2.2.1 hwin).2.1
  have check2 (hw : interval a b (a)) (hu : interval a b (P))
      (hwin : winsSecondSplit (costs P Q (a) (P))) :=
    ((h0 (a) (P) hw hu).2.2.1 hwin).2.1
  have check3 (hw : interval a b (r + 1)) (hu : interval a b (a))
      (hwin : winsSecondSplit (costs (r + 1) (a) R S)) :=
    ((h1 (r + 1) (a) hw hu).2.2.1 hwin).2.1
  have check4 (hw : interval a b (a)) (hu : interval a b (q + 1))
      (hwin : winsSecondSplit (costs P Q (a) (q + 1))) :=
    ((h0 (a) (q + 1) hw hu).2.2.1 hwin).2.1
  have check5 (hw : interval a b (S)) (hu : interval a b (a))
      (hwin : winsSecondSplit (costs (S) (a) R S)) :=
    ((h1 (S) (a) hw hu).2.2.1 hwin).2.1
  have check6 (hw : interval a b (a)) (hu : interval a b (S + 1))
      (hwin : winsSecondSplit (costs (a) (S + 1) R S)) :=
    ((h1 (a) (S + 1) hw hu).2.2.1 hwin).2.1
  clear h0 h1
  simp only [interval, costs, winsFirst, winsFirstSplit, winsSecondSplit, winsLast,
    ← max_add_add_right, max_le_iff, le_max_iff, max_lt_iff, lt_max_iff] at *
  grind (splits := 50) only [max_def]

private theorem outcome2_vs_3
    (a b p q r s P Q R S : ℤ) (ha : 2 ≤ a)
    (hp : interval a b p) (hq : interval a b q) (hr : interval a b r) (hs : interval a b s)
    (hP : interval a b P) (hQ : interval a b Q) (hR : interval a b R) (hS : interval a b S)
    (h0 : ∀ w u, interval a b w → interval a b u →
      preserves (costs P Q w u) (costs p q w u))
    (h1 : ∀ w u, interval a b w → interval a b u →
      preserves (costs w u R S) (costs w u r s)) :
    winsSecondSplit (costs P Q R S) → (costs p q r s).secondSplit ≤ (costs p q r s).groupedLast + 1 := by
  intro hx
  have check1 (hw : interval a b (a)) (hu : interval a b (P - a))
      (hwin : winsSecondSplit (costs P Q (a) (P - a))) :=
    ((h0 (a) (P - a) hw hu).2.2.1 hwin).2.2
  have check2 (hw : interval a b (b)) (hu : interval a b (R + S))
      (hwin : winsFirstSplit (costs (b) (R + S) R S)) :=
    ((h1 (b) (R + S) hw hu).2.1 hwin).2.2
  have check3 (hw : interval a b (b)) (hu : interval a b (b))
      (hwin : winsFirstSplit (costs (b) (b) R S)) :=
    ((h1 (b) (b) hw hu).2.1 hwin).2.2
  have check4 (hw : interval a b (a)) (hu : interval a b (a))
      (hwin : winsSecondSplit (costs P Q (a) (a))) :=
    ((h0 (a) (a) hw hu).2.2.1 hwin).2.2
  have check5 (hw : interval a b (P + 1)) (hu : interval a b (a))
      (hwin : winsSecondSplit (costs P Q (P + 1) (a))) :=
    ((h0 (P + 1) (a) hw hu).2.2.1 hwin).2.2
  clear h0 h1
  simp only [interval, costs, winsFirst, winsFirstSplit, winsSecondSplit, winsLast,
    ← max_add_add_right, max_le_iff, le_max_iff, max_lt_iff, lt_max_iff] at *
  grind (splits := 50) only [max_def]

private def FourCosts.atIndex (c : FourCosts) (i : Fin 4) : ℤ :=
  ![c.groupedFirst, c.firstSplit, c.secondSplit, c.groupedLast] i

private def isPreferred (c : FourCosts) (i : Fin 4) : Prop :=
  ∀ j : Fin 4, c.atIndex i ≤ c.atIndex j ∧ (j < i → c.atIndex i < c.atIndex j)

private theorem preferred_first (c : FourCosts) : isPreferred c 0 ↔ winsFirst c := by
  simp [isPreferred, Fin.forall_fin_succ, FourCosts.atIndex, winsFirst]

private theorem preferred_firstSplit (c : FourCosts) : isPreferred c 1 ↔ winsFirstSplit c := by
  simp [isPreferred, Fin.forall_fin_succ, FourCosts.atIndex, winsFirstSplit, and_left_comm]
  omega

private theorem preferred_secondSplit (c : FourCosts) :
    isPreferred c 2 ↔ winsSecondSplit c := by
  simp [isPreferred, Fin.forall_fin_succ, FourCosts.atIndex, winsSecondSplit]
  omega

private theorem preferred_last (c : FourCosts) : isPreferred c 3 ↔ winsLast c := by
  simp [isPreferred, Fin.forall_fin_succ, FourCosts.atIndex, winsLast, and_left_comm]
  omega

private theorem preserves_iff (c d : FourCosts) : preserves c d ↔
    ∀ i : Fin 4, isPreferred c i → ∀ j : Fin 4, d.atIndex i ≤ d.atIndex j := by
  simp [preserves, Fin.forall_fin_succ, FourCosts.atIndex, preferred_first,
    preferred_firstSplit, preferred_secondSplit, preferred_last]

theorem solution (a b p q r s P Q R S : ℤ) :
    let score := fun (p q r s : ℤ) => (![p + q, max q r, max p s, r + s] : Fin 4 → ℤ)
    let preferred := fun (cost : Fin 4 → ℤ) (i : Fin 4) =>
      ∀ j, cost i ≤ cost j ∧ (j < i → cost i < cost j)
    let stable := fun (report truth : Fin 4 → ℤ) =>
      ∀ i, preferred report i → ∀ j, truth i ≤ truth j
    let inBox := fun v : ℤ => a ≤ v ∧ v ≤ b
    2 ≤ a →
    inBox p → inBox q → inBox r → inBox s →
    inBox P → inBox Q → inBox R → inBox S →
    (∀ w u, inBox w → inBox u → stable (score P Q w u) (score p q w u)) →
    (∀ w u, inBox w → inBox u → stable (score w u R S) (score w u r s)) →
    ∀ i j : Fin 4, (i = 1 ∨ i = 2) →
      preferred (score P Q R S) i → score p q r s i ≤ score p q r s j + 1 := by
  dsimp only
  intro ha hp hq hr hs hP hQ hR hS hs0 hs1 i j hshape h
  have h0 (w u : ℤ) (hw : interval a b w) (hu : interval a b u) :
      preserves (costs P Q w u) (costs p q w u) := (preserves_iff _ _).mpr (hs0 w u hw hu)
  have h1 (w u : ℤ) (hw : interval a b w) (hu : interval a b u) :
      preserves (costs w u R S) (costs w u r s) := (preserves_iff _ _).mpr (hs1 w u hw hu)
  change isPreferred (costs P Q R S) i at h
  change (costs p q r s).atIndex i ≤ (costs p q r s).atIndex j + 1
  rcases hshape with rfl | rfl <;> fin_cases j
  all_goals first
  | exact le_add_of_nonneg_right (by decide)
  | exact outcome1_vs_0 a b p q r s P Q R S ha hp hq hr hs hP hQ hR hS h0 h1 ((preferred_firstSplit _).mp h)
  | exact outcome1_vs_2 a b p q r s P Q R S ha hp hq hr hs hP hQ hR hS h0 h1 ((preferred_firstSplit _).mp h)
  | exact outcome1_vs_3 a b p q r s P Q R S ha hp hq hr hs hP hQ hR hS h0 h1 ((preferred_firstSplit _).mp h)
  | exact outcome2_vs_0 a b p q r s P Q R S ha hp hq hr hs hP hQ hR hS h0 h1 ((preferred_secondSplit _).mp h)
  | exact outcome2_vs_1 a b p q r s P Q R S ha hp hq hr hs hP hQ hR hS h0 h1 ((preferred_secondSplit _).mp h)
  | exact outcome2_vs_3 a b p q r s P Q R S ha hp hq hr hs hP hQ hR hS h0 h1 ((preferred_secondSplit _).mp h)
