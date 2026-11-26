-- Prove2me | solution 1 for NisanRonen.Rounding.boundedLoadDP_two_jobs_two_machines_report_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T07:24:23.63788+00:00
-- url     : https://prove2.me/submissions/85762df6-83a1-4197-bbf5-dc75a88387e2

import Theorems.Thm_NisanRonen_Rounding_priority_certificates_of_true_load_bound
import Theorems.Thm_NisanRonen_Rounding_rounding_error_bound
import Theorems.Thm_NisanRonen_Rounding_boundedLoadDP_respects_colex_priority
import Theorems.Thm_NisanRonen_Rounding_boundedLoadDP_exact

open NisanRonen.Rounding

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

private theorem outcome0_vs_1
    (a b p q r s P Q R S : ℤ) (ha : 2 ≤ a)
    (hp : interval a b p) (hq : interval a b q) (hr : interval a b r) (hs : interval a b s)
    (hP : interval a b P) (hQ : interval a b Q) (hR : interval a b R) (hS : interval a b S)
    (h0 : ∀ w u, interval a b w → interval a b u →
      preserves (costs P Q w u) (costs p q w u))
    (h1 : ∀ w u, interval a b w → interval a b u →
      preserves (costs w u R S) (costs w u r s)) :
    winsFirst (costs P Q R S) → (costs p q r s).groupedFirst ≤ (costs p q r s).firstSplit + 1 := by
  intro hx
  have check1 (hw : interval a b (a)) (hu : interval a b (a))
      (hwin : winsFirst (costs (a) (a) R S)) :=
    ((h1 (a) (a) hw hu).1 hwin).1
  have check2 (hw : interval a b (b)) (hu : interval a b (P + Q))
      (hwin : winsFirst (costs P Q (b) (P + Q))) :=
    ((h0 (b) (P + Q) hw hu).1 hwin).2.1
  have check3 (hw : interval a b (a)) (hu : interval a b (r - a + 1))
      (hwin : winsFirst (costs (a) (r - a + 1) R S)) :=
    ((h1 (a) (r - a + 1) hw hu).1 hwin).1
  clear h0 h1
  simp only [interval, costs, winsFirst, winsFirstSplit, winsSecondSplit, winsLast,
    ← max_add_add_right, max_le_iff, le_max_iff, max_lt_iff, lt_max_iff] at *
  grind (splits := 50) only [max_def]

private theorem outcome0_vs_2
    (a b p q r s P Q R S : ℤ) (ha : 2 ≤ a)
    (hp : interval a b p) (hq : interval a b q) (hr : interval a b r) (hs : interval a b s)
    (hP : interval a b P) (hQ : interval a b Q) (hR : interval a b R) (hS : interval a b S)
    (h0 : ∀ w u, interval a b w → interval a b u →
      preserves (costs P Q w u) (costs p q w u))
    (h1 : ∀ w u, interval a b w → interval a b u →
      preserves (costs w u R S) (costs w u r s)) :
    winsFirst (costs P Q R S) → (costs p q r s).groupedFirst ≤ (costs p q r s).secondSplit + 1 := by
  intro hx
  have check1 (hw : interval a b (a)) (hu : interval a b (s - a + 1))
      (hwin : winsFirst (costs (a) (s - a + 1) R S)) :=
    ((h1 (a) (s - a + 1) hw hu).1 hwin).2.1
  have check2 (hw : interval a b (b)) (hu : interval a b (P + Q))
      (hwin : winsFirst (costs P Q (b) (P + Q))) :=
    ((h0 (b) (P + Q) hw hu).1 hwin).2.1
  have check3 (hw : interval a b (a)) (hu : interval a b (a))
      (hwin : winsFirst (costs (a) (a) R S)) :=
    ((h1 (a) (a) hw hu).1 hwin).2.1
  clear h0 h1
  simp only [interval, costs, winsFirst, winsFirstSplit, winsSecondSplit, winsLast,
    ← max_add_add_right, max_le_iff, le_max_iff, max_lt_iff, lt_max_iff] at *
  grind (splits := 50) only [max_def]

private theorem outcome0_vs_3
    (a b p q r s P Q R S : ℤ) (ha : 2 ≤ a)
    (hp : interval a b p) (hq : interval a b q) (hr : interval a b r) (hs : interval a b s)
    (hP : interval a b P) (hQ : interval a b Q) (hR : interval a b R) (hS : interval a b S)
    (h0 : ∀ w u, interval a b w → interval a b u →
      preserves (costs P Q w u) (costs p q w u))
    (h1 : ∀ w u, interval a b w → interval a b u →
      preserves (costs w u R S) (costs w u r s)) :
    winsFirst (costs P Q R S) → (costs p q r s).groupedFirst ≤ (costs p q r s).groupedLast + 1 := by
  intro hx
  have check1 (hw : interval a b (b)) (hu : interval a b (P + Q))
      (hwin : winsFirst (costs P Q (b) (P + Q))) :=
    ((h0 (b) (P + Q) hw hu).1 hwin).2.1
  have check2 (hw : interval a b (a)) (hu : interval a b (r))
      (hwin : winsFirst (costs (a) (r) R S)) :=
    ((h1 (a) (r) hw hu).1 hwin).1
  clear h0 h1
  simp only [interval, costs, winsFirst, winsFirstSplit, winsSecondSplit, winsLast,
    ← max_add_add_right, max_le_iff, le_max_iff, max_lt_iff, lt_max_iff] at *
  grind (splits := 50) only [max_def]

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

private theorem outcome3_vs_0
    (a b p q r s P Q R S : ℤ) (ha : 2 ≤ a)
    (hp : interval a b p) (hq : interval a b q) (hr : interval a b r) (hs : interval a b s)
    (hP : interval a b P) (hQ : interval a b Q) (hR : interval a b R) (hS : interval a b S)
    (h0 : ∀ w u, interval a b w → interval a b u →
      preserves (costs P Q w u) (costs p q w u))
    (h1 : ∀ w u, interval a b w → interval a b u →
      preserves (costs w u R S) (costs w u r s)) :
    winsLast (costs P Q R S) → (costs p q r s).groupedLast ≤ (costs p q r s).groupedFirst + 1 := by
  intro hx
  have check1 (hw : interval a b (a)) (hu : interval a b (a))
      (hwin : winsLast (costs P Q (a) (a))) :=
    ((h0 (a) (a) hw hu).2.2.2 hwin).2.1
  have check2 (hw : interval a b (a)) (hu : interval a b (P))
      (hwin : winsSecondSplit (costs P Q (a) (P))) :=
    ((h0 (a) (P) hw hu).2.2.1 hwin).2.1
  have check3 (hw : interval a b (a)) (hu : interval a b (R + S))
      (hwin : winsSecondSplit (costs (a) (R + S) R S)) :=
    ((h1 (a) (R + S) hw hu).2.2.1 hwin).2.1
  have check4 (hw : interval a b (P)) (hu : interval a b (a))
      (hwin : winsFirstSplit (costs P Q (P) (a))) :=
    ((h0 (P) (a) hw hu).2.1 hwin).2.1
  have check5 (hw : interval a b (a)) (hu : interval a b (a))
      (hwin : winsSecondSplit (costs (a) (a) R S)) :=
    ((h1 (a) (a) hw hu).2.2.1 hwin).1
  have check6 (hw : interval a b (a)) (hu : interval a b (R))
      (hwin : winsSecondSplit (costs (a) (R) R S)) :=
    ((h1 (a) (R) hw hu).2.2.1 hwin).1
  have check7 (hw : interval a b (a)) (hu : interval a b (r))
      (hwin : winsSecondSplit (costs (a) (r) R S)) :=
    ((h1 (a) (r) hw hu).2.2.1 hwin).2.1
  have check8 (hw : interval a b (a)) (hu : interval a b (a))
      (hwin : winsLast (costs P Q (a) (a))) :=
    ((h0 (a) (a) hw hu).2.2.2 hwin).2.2
  have check9 (hw : interval a b (b)) (hu : interval a b (r))
      (hwin : winsLast (costs (b) (r) R S)) :=
    ((h1 (b) (r) hw hu).2.2.2 hwin).2.1
  have check10 (hw : interval a b (a)) (hu : interval a b (p))
      (hwin : winsLast (costs P Q (a) (p))) :=
    ((h0 (a) (p) hw hu).2.2.2 hwin).2.2
  have check11 (hw : interval a b (a)) (hu : interval a b (q))
      (hwin : winsLast (costs P Q (a) (q))) :=
    ((h0 (a) (q) hw hu).2.2.2 hwin).2.1
  have check12 (hw : interval a b (a)) (hu : interval a b (R))
      (hwin : winsFirstSplit (costs (a) (R) R S)) :=
    ((h1 (a) (R) hw hu).2.1 hwin).1
  clear h0 h1
  simp only [interval, costs, winsFirst, winsFirstSplit, winsSecondSplit, winsLast,
    ← max_add_add_right, max_le_iff, le_max_iff, max_lt_iff, lt_max_iff] at *
  grind (splits := 50) only [max_def]

private theorem outcome3_vs_1
    (a b p q r s P Q R S : ℤ) (ha : 2 ≤ a)
    (hp : interval a b p) (hq : interval a b q) (hr : interval a b r) (hs : interval a b s)
    (hP : interval a b P) (hQ : interval a b Q) (hR : interval a b R) (hS : interval a b S)
    (h0 : ∀ w u, interval a b w → interval a b u →
      preserves (costs P Q w u) (costs p q w u))
    (h1 : ∀ w u, interval a b w → interval a b u →
      preserves (costs w u R S) (costs w u r s)) :
    winsLast (costs P Q R S) → (costs p q r s).groupedLast ≤ (costs p q r s).firstSplit + 1 := by
  intro hx
  have check1 (hw : interval a b (a)) (hu : interval a b (a))
      (hwin : winsLast (costs P Q (a) (a))) :=
    ((h0 (a) (a) hw hu).2.2.2 hwin).2.1
  have check2 (hw : interval a b (b)) (hu : interval a b (R + S + 1))
      (hwin : winsLast (costs (b) (R + S + 1) R S)) :=
    ((h1 (b) (R + S + 1) hw hu).2.2.2 hwin).2.1
  have check3 (hw : interval a b (a)) (hu : interval a b (q - a + 1))
      (hwin : winsLast (costs P Q (a) (q - a + 1))) :=
    ((h0 (a) (q - a + 1) hw hu).2.2.2 hwin).2.1
  clear h0 h1
  simp only [interval, costs, winsFirst, winsFirstSplit, winsSecondSplit, winsLast,
    ← max_add_add_right, max_le_iff, le_max_iff, max_lt_iff, lt_max_iff] at *
  grind (splits := 50) only [max_def]

private theorem outcome3_vs_2
    (a b p q r s P Q R S : ℤ) (ha : 2 ≤ a)
    (hp : interval a b p) (hq : interval a b q) (hr : interval a b r) (hs : interval a b s)
    (hP : interval a b P) (hQ : interval a b Q) (hR : interval a b R) (hS : interval a b S)
    (h0 : ∀ w u, interval a b w → interval a b u →
      preserves (costs P Q w u) (costs p q w u))
    (h1 : ∀ w u, interval a b w → interval a b u →
      preserves (costs w u R S) (costs w u r s)) :
    winsLast (costs P Q R S) → (costs p q r s).groupedLast ≤ (costs p q r s).secondSplit + 1 := by
  intro hx
  have check1 (hw : interval a b (a)) (hu : interval a b (p - a + 1))
      (hwin : winsLast (costs P Q (a) (p - a + 1))) :=
    ((h0 (a) (p - a + 1) hw hu).2.2.2 hwin).2.2
  have check2 (hw : interval a b (b)) (hu : interval a b (R + S + 1))
      (hwin : winsLast (costs (b) (R + S + 1) R S)) :=
    ((h1 (b) (R + S + 1) hw hu).2.2.2 hwin).2.1
  have check3 (hw : interval a b (a)) (hu : interval a b (a))
      (hwin : winsLast (costs P Q (a) (a))) :=
    ((h0 (a) (a) hw hu).2.2.2 hwin).2.2
  clear h0 h1
  simp only [interval, costs, winsFirst, winsFirstSplit, winsSecondSplit, winsLast,
    ← max_add_add_right, max_le_iff, le_max_iff, max_lt_iff, lt_max_iff] at *
  grind (splits := 50) only [max_def]

private def choice (c : Fin 4) (j : Fin 2) : Fin 2 :=
  if j = 0 then ⟨c.val % 2, by omega⟩ else ⟨c.val / 2, by omega⟩

private def choiceCode (x : Fin 2 → Fin 2) : Fin 4 :=
  ⟨(x 0).val + 2 * (x 1).val, by omega⟩

private theorem choice_code (x : Fin 2 → Fin 2) : choice (choiceCode x) = x := by
  funext j
  fin_cases j <;> apply Fin.ext <;> simp [choice, choiceCode] <;> omega

private theorem code_choice (c : Fin 4) : choiceCode (choice c) = c := by
  apply Fin.ext
  simp [choiceCode, choice]
  omega

private theorem code_inj : Function.Injective choiceCode := fun x y h => by
  rw [← choice_code x, ← choice_code y, h]

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

private theorem two_jobs_true_cost
    (a b p q r s P Q R S : ℤ) (ha : 2 ≤ a)
    (hp : interval a b p) (hq : interval a b q) (hr : interval a b r) (hs : interval a b s)
    (hP : interval a b P) (hQ : interval a b Q) (hR : interval a b R) (hS : interval a b S)
    (h0 : ∀ w u, interval a b w → interval a b u →
      preserves (costs P Q w u) (costs p q w u))
    (h1 : ∀ w u, interval a b w → interval a b u →
      preserves (costs w u R S) (costs w u r s))
    (i j : Fin 4) (h : isPreferred (costs P Q R S) i) :
    (costs p q r s).atIndex i ≤ (costs p q r s).atIndex j + 1 := by
  fin_cases i <;> fin_cases j
  all_goals first
  | exact le_add_of_nonneg_right (by decide)
  | exact outcome0_vs_1 a b p q r s P Q R S ha hp hq hr hs hP hQ hR hS h0 h1 ((preferred_first _).mp h)
  | exact outcome0_vs_2 a b p q r s P Q R S ha hp hq hr hs hP hQ hR hS h0 h1 ((preferred_first _).mp h)
  | exact outcome0_vs_3 a b p q r s P Q R S ha hp hq hr hs hP hQ hR hS h0 h1 ((preferred_first _).mp h)
  | exact outcome1_vs_0 a b p q r s P Q R S ha hp hq hr hs hP hQ hR hS h0 h1 ((preferred_firstSplit _).mp h)
  | exact outcome1_vs_2 a b p q r s P Q R S ha hp hq hr hs hP hQ hR hS h0 h1 ((preferred_firstSplit _).mp h)
  | exact outcome1_vs_3 a b p q r s P Q R S ha hp hq hr hs hP hQ hR hS h0 h1 ((preferred_firstSplit _).mp h)
  | exact outcome2_vs_0 a b p q r s P Q R S ha hp hq hr hs hP hQ hR hS h0 h1 ((preferred_secondSplit _).mp h)
  | exact outcome2_vs_1 a b p q r s P Q R S ha hp hq hr hs hP hQ hR hS h0 h1 ((preferred_secondSplit _).mp h)
  | exact outcome2_vs_3 a b p q r s P Q R S ha hp hq hr hs hP hQ hR hS h0 h1 ((preferred_secondSplit _).mp h)
  | exact outcome3_vs_0 a b p q r s P Q R S ha hp hq hr hs hP hQ hR hS h0 h1 ((preferred_last _).mp h)
  | exact outcome3_vs_1 a b p q r s P Q R S ha hp hq hr hs hP hQ hR hS h0 h1 ((preferred_last _).mp h)
  | exact outcome3_vs_2 a b p q r s P Q R S ha hp hq hr hs hP hQ hR hS h0 h1 ((preferred_last _).mp h)

private noncomputable def integerCosts (δ : ℝ) (v : Fin 2 → Fin 2 → ℝ) : FourCosts :=
  costs ⌈v 0 0 / δ⌉ ⌈v 0 1 / δ⌉ ⌈v 1 0 / δ⌉ ⌈v 1 1 / δ⌉

private theorem sup_two (g : Fin 2 → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty g = max (g 0) (g 1) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (Finset.le_sup' g (Finset.mem_univ _)) (Finset.le_sup' g (Finset.mem_univ _))

private theorem nonneg_unit {a δ r : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hr : a ≤ r) :
    0 ≤ ⌈r / δ⌉ :=
  Int.ceil_nonneg (div_nonneg (ha.le.trans hr) hδ.le)

private theorem span_two {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (v : Fin 2 → Fin 2 → ℝ) (hv : ∀ i j, a ≤ v i j) (c : Fin 4) :
    roundedMakespan δ (choice c) (corrStar (choice c) v) =
      δ * ((integerCosts δ v).atIndex c : ℝ) := by
  have nn (i j : Fin 2) : 0 ≤ δ * (⌈v i j / δ⌉ : ℤ) :=
    mul_nonneg hδ.le (by exact_mod_cast nonneg_unit ha hδ (hv i j))
  fin_cases c <;>
    simp [roundedMakespan, makespan, sup_two, load, Finset.sum_filter, Fin.sum_univ_two, choice, corrStar,
      costs, integerCosts, FourCosts.atIndex, roundUp, mul_add, mul_max_of_nonneg _ _ hδ.le,
      max_eq_left (add_nonneg (nn 0 0) (nn 0 1)),
      max_eq_right (add_nonneg (nn 1 0) (nn 1 1))]

private theorem preferred_unique {c : FourCosts} {i j : Fin 4}
    (hi : isPreferred c i) (hj : isPreferred c j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim ((not_lt_of_ge (hi j).1) ((hj i).2 h))
  · exact h
  · exact False.elim ((not_lt_of_ge (hj i).1) ((hi j).2 h))

private theorem realize {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    {z : ℤ} (hz : interval ⌈a / δ⌉ ⌈b / δ⌉ z) :
    ∃ w : ℝ, a ≤ w ∧ w ≤ b ∧ ⌈w / δ⌉ = z := by
  refine ⟨min b (δ * (z : ℝ)), le_min hab ?_, min_le_left _ _, ?_⟩
  · have hh : a / δ ≤ (z : ℝ) := (Int.le_ceil _).trans (by exact_mod_cast hz.1)
    exact (div_le_iff₀ hδ).mp hh |>.trans_eq (mul_comm _ _)
  · by_cases hb : δ * (z : ℝ) ≤ b
    · simp [min_eq_right hb, mul_div_cancel_left₀ _ hδ.ne']
    · rw [min_eq_left (le_of_not_ge hb)]
      have hh : b / δ ≤ (z : ℝ) := (div_le_iff₀ hδ).mpr
        ((le_of_not_ge hb).trans_eq (mul_comm _ _))
      exact le_antisymm (Int.ceil_le.mpr hh) hz.2

private theorem unit_interval {a b δ : ℝ} (hδ : 0 < δ) {v : ℝ}
    (h : a ≤ v ∧ v ≤ b) : interval ⌈a / δ⌉ ⌈b / δ⌉ ⌈v / δ⌉ :=
  ⟨Int.ceil_mono (div_le_div_of_nonneg_right h.1 hδ.le),
    Int.ceil_mono (div_le_div_of_nonneg_right h.2 hδ.le)⟩

private theorem two_jobs_execution_certificate {a b δ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hδ : 0 < δ) (hA : 2 ≤ ⌈a / δ⌉)
    (f : List (Fin 2 → ℕ) → List (Fin 2)) (hf : IsExactRoundedSolver f δ a b)
    (hpriority : ∀ v : Fin 2 → Fin 2 → ℝ, (∀ l j, a ≤ v l j ∧ v l j ≤ b) →
      ∀ y : Fin 2 → Fin 2, roundedMakespan δ y (corrStar y v) =
        roundedMakespan δ (allocOf f δ v) (corrStar (allocOf f δ v) v) →
        choiceCode (allocOf f δ v) ≤ choiceCode y)
    (t d : Fin 2 → Fin 2 → ℝ)
    (ht : ∀ l j, a ≤ t l j ∧ t l j ≤ b) (hd : ∀ l j, a ≤ d l j ∧ d l j ≤ b)
    (hop : ∀ i, DeclarationOptimal f δ a b i (t i) (d i))
    (y : Fin 2 → Fin 2) :
    HasAllocationCertificates f δ a b t d (roundedMakespan δ y (corrStar y t) + δ) := by
  classical
  let A := ⌈a / δ⌉
  let B := ⌈b / δ⌉
  let p := ⌈t 0 0 / δ⌉
  let q := ⌈t 0 1 / δ⌉
  let r := ⌈t 1 0 / δ⌉
  let s := ⌈t 1 1 / δ⌉
  let P := ⌈d 0 0 / δ⌉
  let Q := ⌈d 0 1 / δ⌉
  let R := ⌈d 1 0 / δ⌉
  let S := ⌈d 1 1 / δ⌉
  let x := allocOf f δ d
  have bridge (v : Fin 2 → Fin 2 → ℝ) (hv : ∀ l j, a ≤ v l j)
      (z : Fin 2 → Fin 2) :
      roundedMakespan δ z (corrStar z v) =
        δ * ((integerCosts δ v).atIndex (choiceCode z) : ℝ) := by
    conv_lhs => rw [← choice_code z]
    exact span_two ha hδ v hv (choiceCode z)
  have win (v : Fin 2 → Fin 2 → ℝ) (hv : ∀ l j, a ≤ v l j ∧ v l j ≤ b) :
      isPreferred (integerCosts δ v) (choiceCode (allocOf f δ v)) := by
    intro c
    let z := choice c
    have hvlo (i j : Fin 2) := (hv i j).1
    have h0 := (hf 2 v hv).2 z
    rw [bridge v hvlo, bridge v hvlo, code_choice] at h0
    have hle : (integerCosts δ v).atIndex (choiceCode (allocOf f δ v)) ≤
        (integerCosts δ v).atIndex c := by exact_mod_cast le_of_mul_le_mul_left h0 hδ
    refine ⟨hle, fun hlt => lt_of_le_of_ne hle ?_⟩
    intro he
    have heq : roundedMakespan δ z (corrStar z v) =
        roundedMakespan δ (allocOf f δ v) (corrStar (allocOf f δ v) v) := by
      rw [bridge v hvlo, bridge v hvlo, code_choice, he]
    have hp := hpriority v hv z heq
    rw [code_choice] at hp
    exact (not_le_of_gt hlt) hp
  have test (i : Fin 2) (v : Fin 2 → Fin 2 → ℝ) (hv : ∀ l j, a ≤ v l j ∧ v l j ≤ b)
      (hvi : v i = d i) :
      preserves (integerCosts δ v) (integerCosts δ (Function.update v i (t i))) := by
    rw [preserves_iff]
    intro c hc z
    have hx := preferred_unique hc (win v hv)
    have htest := hop i v hv hvi (choice z)
    have hlo (l j : Fin 2) : a ≤ Function.update v i (t i) l j := by
      by_cases hl : l = i
      · subst l
        simpa using (ht i j).1
      · simpa [hl] using (hv l j).1
    rw [bridge _ hlo _, bridge _ hlo _, code_choice, ← hx] at htest
    exact_mod_cast le_of_mul_le_mul_left htest hδ
  have h0 (w u : ℤ) (hw : interval A B w) (hu : interval A B u) :
      preserves (costs P Q w u) (costs p q w u) := by
    obtain ⟨w', hwa, hwb, hw'⟩ := realize hab hδ hw
    obtain ⟨u', hua, hub, hu'⟩ := realize hab hδ hu
    let v : Fin 2 → Fin 2 → ℝ := ![d 0, ![w', u']]
    have hv (i j : Fin 2) : a ≤ v i j ∧ v i j ≤ b := by
      fin_cases i
      · exact hd 0 j
      · fin_cases j
        · exact ⟨hwa, hwb⟩
        · exact ⟨hua, hub⟩
    simpa [v, integerCosts, hw', hu', P, Q, p, q] using test 0 v hv rfl
  have h1 (w u : ℤ) (hw : interval A B w) (hu : interval A B u) :
      preserves (costs w u R S) (costs w u r s) := by
    obtain ⟨w', hwa, hwb, hw'⟩ := realize hab hδ hw
    obtain ⟨u', hua, hub, hu'⟩ := realize hab hδ hu
    let v : Fin 2 → Fin 2 → ℝ := ![![w', u'], d 1]
    have hv (i j : Fin 2) : a ≤ v i j ∧ v i j ≤ b := by
      fin_cases i
      · fin_cases j
        · exact ⟨hwa, hwb⟩
        · exact ⟨hua, hub⟩
      · exact hd 1 j
    simpa [v, integerCosts, hw', hu', R, S, r, s] using test 1 v hv rfl
  let m := (integerCosts δ t).atIndex (choiceCode y) + 1
  have hm : roundedMakespan δ y (corrStar y t) + δ = δ * (m : ℝ) := by
    rw [bridge t (fun i j => (ht i j).1)]
    simp [m, mul_add]
  rw [hm]
  have htrue : roundedMakespan δ x (corrStar x t) ≤ δ * (m : ℝ) := by
    rw [bridge t (fun i j => (ht i j).1) x]
    apply mul_le_mul_of_nonneg_left _ hδ.le
    exact_mod_cast two_jobs_true_cost A B p q r s P Q R S hA
      (unit_interval hδ (ht 0 0)) (unit_interval hδ (ht 0 1))
      (unit_interval hδ (ht 1 0)) (unit_interval hδ (ht 1 1))
      (unit_interval hδ (hd 0 0)) (unit_interval hδ (hd 0 1))
      (unit_interval hδ (hd 1 0)) (unit_interval hδ (hd 1 1))
      h0 h1 (choiceCode x) (choiceCode y) (win d hd)
  have hM0 : 0 ≤ δ * (m : ℝ) := by
    have hnonneg (j : Fin 2) : 0 ≤ roundUp δ (corrStar x t j) :=
      mul_nonneg hδ.le (by exact_mod_cast nonneg_unit ha hδ (ht (x j) j).1)
    have hx0 : 0 ≤ roundedMakespan δ x (corrStar x t) := by
      unfold roundedMakespan makespan load
      have hsum : 0 ≤ ∑ j ∈ Finset.univ.filter (fun j => x j = (0 : Fin 2)),
          roundUp δ (corrStar x t j) := Finset.sum_nonneg (fun j _ => hnonneg j)
      exact hsum.trans (Finset.le_sup' (fun i : Fin 2 =>
        ∑ j ∈ Finset.univ.filter (fun j => x j = i), roundUp δ (corrStar x t j))
        (Finset.mem_univ (0 : Fin 2)))
    exact hx0.trans htrue
  have hentry (i j : Fin 2) : roundUp δ (d i j) ≤ max (δ * (m : ℝ)) (roundUp δ b) := by
    refine le_trans ?_ (le_max_right _ _)
    unfold roundUp
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (unit_interval hδ (hd i j)).2) hδ.le
  have hshape (i : Fin 2) :
      (∑ j ∈ Finset.univ.filter (fun j => x j = i), roundUp δ (d i j)) ≤
        max (δ * (m : ℝ)) (roundUp δ b) ∨
      ∀ l ≠ i,
        (∑ j ∈ Finset.univ.filter (fun j => x j = l), roundUp δ (d l j)) ≤ δ * (m : ℝ) := by
    rw [← choice_code x]
    generalize choiceCode x = c
    fin_cases c <;> fin_cases i <;>
      first
      | apply Or.inr
        intro l hl
        solve | fin_cases l <;> simp_all [Finset.sum_filter, Fin.sum_univ_two, choice]
      | apply Or.inl
        first
        | simpa [Finset.sum_filter, Fin.sum_univ_two, choice] using hentry 0 0
        | simpa [Finset.sum_filter, Fin.sum_univ_two, choice] using hentry 0 1
        | simpa [Finset.sum_filter, Fin.sum_univ_two, choice] using hentry 1 0
        | simpa [Finset.sum_filter, Fin.sum_univ_two, choice] using hentry 1 1
        | simpa [Finset.sum_filter, Fin.sum_univ_two, choice] using hM0.trans
            (le_max_left (δ * (m : ℝ)) (roundUp δ b))
  exact priority_certificates_of_true_load_bound ha hab hδ f hf
    (fun z => (choiceCode z).val) (fun _ _ h => code_inj (Fin.ext h)) hpriority
    t d (fun i j => (ht i j).1) hd m htrue hshape

theorem solution {a b δ ε : ℝ} (ha : 0 < a) (hab : a ≤ b) (hδ : 0 < δ)
    (hδa : δ < a) (hstep : 2 * δ ≤ ε * a)
    (t d : Fin 2 → Fin 2 → ℝ)
    (ht : ∀ l j, a ≤ t l j ∧ t l j ≤ b) (hd : ∀ l j, a ≤ d l j ∧ d l j ≤ b)
    (hop : ∀ i, DeclarationOptimal (boundedLoadDP (n := 2) (⌈b / δ⌉.toNat)) δ a b i (t i) (d i))
    (y : Fin 2 → Fin 2) :
    HasAllocationCertificates (boundedLoadDP (n := 2) (⌈b / δ⌉.toNat)) δ a b t d
      ((1 + ε) * makespan y (corrStar y t)) := by
  classical
  let f := boundedLoadDP (n := 2) (⌈b / δ⌉.toNat)
  have hA : 2 ≤ ⌈a / δ⌉ := by
    have h1 : 1 < a / δ := (lt_div_iff₀ hδ).mpr (by simpa using hδa)
    have h2 : (1 : ℤ) < ⌈a / δ⌉ := by exact_mod_cast h1.trans_le (Int.le_ceil _)
    omega
  have fold_eq (z : Fin 2 → Fin 2) :
      (List.ofFn z).foldr (fun i r => i.val + 2 * r) 0 = (choiceCode z).val := by
    simp [List.ofFn_succ, choiceCode]
  have hp (v : Fin 2 → Fin 2 → ℝ) (hv : ∀ l j, a ≤ v l j ∧ v l j ≤ b)
      (z : Fin 2 → Fin 2)
      (heq : roundedMakespan δ z (corrStar z v) =
        roundedMakespan δ (allocOf f δ v) (corrStar (allocOf f δ v) v)) :
      choiceCode (allocOf f δ v) ≤ choiceCode z := by
    have h := boundedLoadDP_respects_colex_priority (b := b) ha hδ 2 2 v hv z heq
    rwa [fold_eq, fold_eq] at h
  have hcert := two_jobs_execution_certificate ha hab hδ hA f
    (boundedLoadDP_exact ha hδ 2) hp t d ht hd hop y
  let T := makespan y (corrStar y t)
  have hTa : a ≤ T := by
    let j₀ : Fin 2 := 0
    have hsingle : corrStar y t j₀ ≤ load y (corrStar y t) (y j₀) :=
      Finset.single_le_sum (f := corrStar y t) (fun j _ => ha.le.trans (ht (y j) j).1)
        (show j₀ ∈ Finset.univ.filter (fun j => y j = y j₀) by simp)
    exact (ht (y j₀) j₀).1.trans (hsingle.trans (Finset.le_sup' _ (Finset.mem_univ _)))
  have hround := (rounding_error_bound ha hδ y (corrStar y t)
    (fun j => (ht (y j) j).1)).2
  have hcoef : δ / a ≤ ε - δ / a := (div_le_iff₀ ha).2 (by
    rw [sub_mul, div_mul_cancel₀ _ ha.ne']
    linarith)
  have hunit : 1 ≤ T / a := (le_div_iff₀ ha).2 (by simpa using hTa)
  have hadd : δ ≤ (δ / a) * T := by
    rw [div_mul_eq_mul_div, mul_div_assoc]
    simpa using mul_le_mul_of_nonneg_left hunit hδ.le
  have hbound : roundedMakespan δ y (corrStar y t) + δ ≤ (1 + ε) * T := by
    linarith only [hround, hadd, mul_le_mul_of_nonneg_right hcoef (ha.le.trans hTa)]
  intro i hi
  obtain ⟨v, hv, hvi, hx, z, hz⟩ := hcert i hi
  exact ⟨v, hv, hvi, hx, z, hz.trans hbound⟩
