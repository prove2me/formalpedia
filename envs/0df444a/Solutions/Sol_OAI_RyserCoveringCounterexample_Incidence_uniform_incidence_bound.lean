-- Prove2me | solution 1 for OAI.RyserCoveringCounterexample.Incidence.uniform_incidence_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T04:27:32.752646+00:00
-- url     : https://prove2.me/submissions/540c9c59-22ec-4a04-bbda-5a734524fe3e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIW2RY002

section
-- module Solutions.OAIW2_RyserCov.Ryser_Geometry_AffineJoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F]

section Join

variable [DecidableEq F]

theorem eq_joinLine_of_incidence {p q : Point F} {l : AffineLine F}
    (hpq : p ≠ q) (hpl : Incidence p l) (hql : Incidence q l) :
    l = joinLine p q :=
  line_eq_of_two_incident_points hpq hpl hql
    (incidence_joinLine_left p q) (incidence_joinLine_right p q)

theorem existsUnique_lineThrough_pair {p q : Point F} (hpq : p ≠ q) :
    ∃! l : AffineLine F, Incidence p l ∧ Incidence q l := by
  refine ⟨joinLine p q, ⟨incidence_joinLine_left p q,
    incidence_joinLine_right p q⟩, ?_⟩
  intro l hl
  exact eq_joinLine_of_incidence hpq hl.1 hl.2

end Join

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Geometry_Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F]

theorem exists_direction_of_incidence_infinity {p : ProjectivePoint F}
    (h : ProjectiveIncidence p none) : ∃ d, p = Sum.inr d := by
  cases p with
  | inl p => exact h.elim
  | inr d => exact ⟨d, rfl⟩

theorem exists_affine_of_not_incidence_infinity {p : ProjectivePoint F}
    (h : ¬ ProjectiveIncidence p none) : ∃ x, p = Sum.inl x := by
  cases p with
  | inl x => exact ⟨x, rfl⟩
  | inr d => exact (h trivial).elim

theorem exists_slope_of_incidence_infinity_of_ne_vertical {p : ProjectivePoint F}
    (h : ProjectiveIncidence p none) (hne : p ≠ Sum.inr none) :
    ∃ a, p = Sum.inr (some a) := by
  obtain ⟨d, rfl⟩ := exists_direction_of_incidence_infinity h
  cases d with
  | none => exact (hne rfl).elim
  | some a => exact ⟨a, rfl⟩

theorem exists_projectiveTransform_line_to_infinity (l : ProjectiveLine F) :
    ∃ T : ProjectiveTransform F, T.lines l = none := by
  cases l with
  | none => exact ⟨ProjectiveTransform.refl F, rfl⟩
  | some l =>
    rcases l with ⟨d, b⟩
    cases d with
    | none =>
      refine ⟨(translate (-b) 0).trans (swapXZ F), ?_⟩
      simp
    | some a =>
      refine ⟨(((shear (-a)).trans (swapXY F)).trans
        (translate (-b) 0)).trans (swapXZ F), ?_⟩
      simp only [ProjectiveTransform.trans_lines, shear_lines_slope, add_neg_cancel,
        swapXY_lines_slope_zero, translate_lines_vertical, swapXZ_lines_vertical_zero]

theorem exists_projectiveTransform_direction_to_vertical (d : Direction F) :
    ∃ T : ProjectiveTransform F,
      T.points (Sum.inr d) = Sum.inr none ∧
      T.points (Sum.inl (0, 0)) = Sum.inl (0, 0) ∧
      T.lines none = none := by
  cases d with
  | none => exact ⟨ProjectiveTransform.refl F, rfl, rfl, rfl⟩
  | some a =>
    refine ⟨(shear (-a)).trans (swapXY F), ?_, ?_, ?_⟩ <;> simp

theorem exists_projectiveTransform_direction_frame
    (d1 d2 d3 : Direction F) (h12 : d1 ≠ d2) (h13 : d1 ≠ d3)
    (h23 : d2 ≠ d3) :
    ∃ T : ProjectiveTransform F,
      T.points (Sum.inr d1) = Sum.inr (some 0) ∧
      T.points (Sum.inr d2) = Sum.inr none ∧
      T.points (Sum.inr d3) = Sum.inr (some 1) ∧
      T.points (Sum.inl (0, 0)) = Sum.inl (0, 0) := by
  obtain ⟨S, hsecond, horigin, hline⟩ :=
    exists_projectiveTransform_direction_to_vertical d2
  have hinf (d : Direction F) : ProjectiveIncidence (S.points (Sum.inr d)) none := by
    rw [← hline]
    exact (S.incidence (Sum.inr d) none).mpr trivial
  have hfirst : S.points (Sum.inr d1) ≠ Sum.inr none := by
    intro h
    exact h12 (Sum.inr.inj (S.points.injective (h.trans hsecond.symm)))
  have hthird : S.points (Sum.inr d3) ≠ Sum.inr none := by
    intro h
    exact h23 (Sum.inr.inj (S.points.injective (hsecond.trans h.symm)))
  obtain ⟨a, ha⟩ := exists_slope_of_incidence_infinity_of_ne_vertical (hinf d1) hfirst
  obtain ⟨c, hc⟩ := exists_slope_of_incidence_infinity_of_ne_vertical (hinf d3) hthird
  have hac : a ≠ c := by
    intro h
    apply h13
    apply Sum.inr.inj
    apply S.points.injective
    rw [ha, hc, h]
  have hca : c - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hac)
  refine ⟨S.trans ((shear (-a)).trans (scaleY (c - a)⁻¹ (inv_ne_zero hca))),
    ?_, ?_, ?_, ?_⟩
  · simp [ha]
  · simp [hsecond]
  · simp only [ProjectiveTransform.trans_points, hc, shear_points_infinite_slope,
      scaleY_points_infinite_slope, ← sub_eq_add_neg]
    simp [hca]
  · simp [horigin]

theorem exists_projectiveTransform_normalization
    {p1 p2 p3 p4 : ProjectivePoint F} {l : ProjectiveLine F}
    (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : ProjectiveIncidence p1 l) (h2 : ProjectiveIncidence p2 l)
    (h3 : ProjectiveIncidence p3 l) (h4 : ¬ ProjectiveIncidence p4 l) :
    ∃ T : ProjectiveTransform F,
      T.points p1 = Sum.inr (some 0) ∧
      T.points p2 = Sum.inr none ∧
      T.points p3 = Sum.inr (some 1) ∧
      T.points p4 = Sum.inl (0, 0) := by
  obtain ⟨S, hline⟩ := exists_projectiveTransform_line_to_infinity l
  have hfirst : ProjectiveIncidence (S.points p1) none := by
    rw [← hline]
    exact (S.incidence p1 l).mpr h1
  have hsecond : ProjectiveIncidence (S.points p2) none := by
    rw [← hline]
    exact (S.incidence p2 l).mpr h2
  have hthird : ProjectiveIncidence (S.points p3) none := by
    rw [← hline]
    exact (S.incidence p3 l).mpr h3
  have hfourth : ¬ ProjectiveIncidence (S.points p4) none := by
    rw [← hline]
    exact fun h => h4 ((S.incidence p4 l).mp h)
  obtain ⟨d1, hd1⟩ := exists_direction_of_incidence_infinity hfirst
  obtain ⟨d2, hd2⟩ := exists_direction_of_incidence_infinity hsecond
  obtain ⟨d3, hd3⟩ := exists_direction_of_incidence_infinity hthird
  obtain ⟨x, hx⟩ := exists_affine_of_not_incidence_infinity hfourth
  have hd12 : d1 ≠ d2 := by
    intro h
    apply h12
    apply S.points.injective
    rw [hd1, hd2, h]
  have hd13 : d1 ≠ d3 := by
    intro h
    apply h13
    apply S.points.injective
    rw [hd1, hd3, h]
  have hd23 : d2 ≠ d3 := by
    intro h
    apply h23
    apply S.points.injective
    rw [hd2, hd3, h]
  obtain ⟨U, hu1, hu2, hu3, hu4⟩ :=
    exists_projectiveTransform_direction_frame d1 d2 d3 hd12 hd13 hd23
  refine ⟨(S.trans (translate (-x.1) (-x.2))).trans U, ?_, ?_, ?_, ?_⟩
  · simpa only [ProjectiveTransform.trans_points, hd1, translate_points_infinite] using hu1
  · simpa only [ProjectiveTransform.trans_points, hd2, translate_points_infinite] using hu2
  · simpa only [ProjectiveTransform.trans_points, hd3, translate_points_infinite] using hu3
  · simpa only [ProjectiveTransform.trans_points, hx, translate_points_finite,
      add_neg_cancel] using hu4

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Geometry_ProjectiveJoins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F]

theorem existsUnique_projectiveLine_of_ne {p q : ProjectivePoint F}
    (hpq : p ≠ q) :
    ∃! l : ProjectiveLine F, ProjectiveIncidence p l ∧ ProjectiveIncidence q l := by
  classical
  cases p with
  | inl p =>
    cases q with
    | inl q =>
      have hpq' : p ≠ q := fun h => hpq (congrArg Sum.inl h)
      obtain ⟨l, hl, huniq⟩ := existsUnique_lineThrough_pair hpq'
      refine ⟨some l, hl, ?_⟩
      intro m hm
      cases m with
      | none => exact hm.1.elim
      | some m => exact congrArg some (huniq m hm)
    | inr d =>
      refine ⟨some (lineThrough d p), ⟨rfl, rfl⟩, ?_⟩
      intro m hm
      cases m with
      | none => exact hm.1.elim
      | some m =>
        apply congrArg some
        exact line_eq_of_direction_eq_of_incidence hm.2.symm hm.1 rfl
  | inr d =>
    cases q with
    | inl q =>
      refine ⟨some (lineThrough d q), ⟨rfl, rfl⟩, ?_⟩
      intro m hm
      cases m with
      | none => exact hm.2.elim
      | some m =>
        apply congrArg some
        exact line_eq_of_direction_eq_of_incidence hm.1.symm hm.2 rfl
    | inr e =>
      refine ⟨none, ⟨trivial, trivial⟩, ?_⟩
      intro m hm
      cases m with
      | none => rfl
      | some m =>
        have hde : d = e := hm.1.trans hm.2.symm
        exact (hpq (congrArg Sum.inr hde)).elim

theorem eq_projectiveLine_of_common_incidence
    {p q : ProjectivePoint F} {l m : ProjectiveLine F}
    (hpq : p ≠ q)
    (hpl : ProjectiveIncidence p l) (hql : ProjectiveIncidence q l)
    (hpm : ProjectiveIncidence p m) (hqm : ProjectiveIncidence q m) : l = m := by
  obtain ⟨k, _, huniq⟩ := existsUnique_projectiveLine_of_ne hpq
  exact (huniq l ⟨hpl, hql⟩).trans (huniq m ⟨hpm, hqm⟩).symm

theorem eq_projectivePoint_of_common_incidence
    {l m : ProjectiveLine F} {p q : ProjectivePoint F}
    (hlm : l ≠ m)
    (hpl : ProjectiveIncidence p l) (hpm : ProjectiveIncidence p m)
    (hql : ProjectiveIncidence q l) (hqm : ProjectiveIncidence q m) : p = q := by
  obtain ⟨x, _, huniq⟩ := existsUnique_projectivePoint_of_ne hlm
  exact (huniq p ⟨hpl, hpm⟩).trans (huniq q ⟨hql, hqm⟩).symm

end RyserCoveringCounterexample

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_PruningCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Incidence

variable {Pt Ln : Type*} [instDecidableEqPt : DecidableEq Pt] [instDecidableEqLn : DecidableEq Ln]

theorem leftDegree_eq_sum (R : Pt → Ln → Prop) (L : Finset Ln) (p : Pt) :
    leftDegree R L p = ∑ l ∈ L, if R p l then 1 else 0 := let _ := instDecidableEqPt; let _ := instDecidableEqLn; by
  classical
  exact (Finset.sum_boole (R := ℕ) (R p) L).symm

theorem incidenceCount_swap (R : Pt → Ln → Prop) (P : Finset Pt) (L : Finset Ln) :
    incidenceCount R P L = incidenceCount (fun l p => R p l) L P := by
  classical
  simp only [incidenceCount, leftDegree_eq_sum]
  exact Finset.sum_comm

theorem leftDegree_mono (R : Pt → Ln → Prop) {L L' : Finset Ln}
    (hL : L ⊆ L') (p : Pt) : leftDegree R L p ≤ leftDegree R L' p := let _ := instDecidableEqPt; let _ := instDecidableEqLn; by
  classical
  exact Finset.card_le_card (Finset.filter_subset_filter (R p) hL)

theorem rightDegree_mono (R : Pt → Ln → Prop) {P P' : Finset Pt}
    (hP : P ⊆ P') (l : Ln) : rightDegree R P l ≤ rightDegree R P' l :=
  leftDegree_mono (fun l p => R p l) hP l

theorem incidenceCount_erase_left (R : Pt → Ln → Prop) (P : Finset Pt)
    (L : Finset Ln) {p : Pt} (hp : p ∈ P) :
    incidenceCount R (P.erase p) L + leftDegree R L p = incidenceCount R P L := let _ := instDecidableEqLn;
  Finset.sum_erase_add P (leftDegree R L) hp

theorem incidenceCount_erase_right (R : Pt → Ln → Prop) (P : Finset Pt)
    (L : Finset Ln) {l : Ln} (hl : l ∈ L) :
    incidenceCount R P (L.erase l) + rightDegree R P l = incidenceCount R P L := by
  rw [incidenceCount_swap R P (L.erase l), incidenceCount_swap R P L]
  exact incidenceCount_erase_left (fun l p => R p l) L P hl

theorem pruningPotential_le_erase_left (R : Pt → Ln → Prop) (d : ℝ)
    (P : Finset Pt) (L : Finset Ln) {p : Pt} (hp : p ∈ P)
    (hdeg : (leftDegree R L p : ℝ) ≤ d) :
    pruningPotential R d P L ≤ pruningPotential R d (P.erase p) L := by
  have hcount : (incidenceCount R (P.erase p) L : ℝ) + (leftDegree R L p : ℝ) =
      (incidenceCount R P L : ℝ) := by
    exact_mod_cast incidenceCount_erase_left R P L hp
  have hcard : ((P.erase p).card : ℝ) + 1 = (P.card : ℝ) := by
    exact_mod_cast Finset.card_erase_add_one hp
  unfold pruningPotential
  rw [← hcount, ← hcard]
  nlinarith

theorem pruningPotential_le_erase_right (R : Pt → Ln → Prop) (d : ℝ)
    (P : Finset Pt) (L : Finset Ln) {l : Ln} (hl : l ∈ L)
    (hdeg : (rightDegree R P l : ℝ) ≤ d) :
    pruningPotential R d P L ≤ pruningPotential R d P (L.erase l) := by
  have hcount : (incidenceCount R P (L.erase l) : ℝ) + (rightDegree R P l : ℝ) =
      (incidenceCount R P L : ℝ) := by
    exact_mod_cast incidenceCount_erase_right R P L hl
  have hcard : ((L.erase l).card : ℝ) + 1 = (L.card : ℝ) := by
    exact_mod_cast Finset.card_erase_add_one hl
  unfold pruningPotential
  rw [← hcount, ← hcard]
  nlinarith

private theorem exists_degree_core_aux (R : Pt → Ln → Prop) (d : ℝ) (n : ℕ) :
    ∀ (P : Finset Pt) (L : Finset Ln), P.card + L.card = n →
      ∃ P' : Finset Pt, P' ⊆ P ∧ ∃ L' : Finset Ln, L' ⊆ L ∧
        MinimumDegrees R d P' L' ∧ pruningPotential R d P L ≤ pruningPotential R d P' L' := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P L hsize
    by_cases hpmin : ∀ p ∈ P, d ≤ (leftDegree R L p : ℝ)
    · by_cases hlmin : ∀ l ∈ L, d ≤ (rightDegree R P l : ℝ)
      · exact ⟨P, Finset.Subset.refl _, L, Finset.Subset.refl _, ⟨hpmin, hlmin⟩, le_rfl⟩
      · have hex : ∃ l ∈ L, (rightDegree R P l : ℝ) < d := by
          by_contra hnone
          apply hlmin
          intro l hl
          apply le_of_not_gt
          intro hdeg
          exact hnone ⟨l, hl, hdeg⟩
        obtain ⟨l, hl, hdeg⟩ := hex
        have hlt : P.card + (L.erase l).card < n := by
          rw [← hsize]
          exact Nat.add_lt_add_left (Finset.card_erase_lt_of_mem hl) _
        obtain ⟨P', hP', L', hL', hmin, hpot⟩ := ih _ hlt P (L.erase l) rfl
        exact ⟨P', hP', L', hL'.trans (Finset.erase_subset _ _), hmin,
          (pruningPotential_le_erase_right R d P L hl hdeg.le).trans hpot⟩
    · have hex : ∃ p ∈ P, (leftDegree R L p : ℝ) < d := by
        by_contra hnone
        apply hpmin
        intro p hp
        apply le_of_not_gt
        intro hdeg
        exact hnone ⟨p, hp, hdeg⟩
      obtain ⟨p, hp, hdeg⟩ := hex
      have hlt : (P.erase p).card + L.card < n := by
        rw [← hsize]
        exact Nat.add_lt_add_right (Finset.card_erase_lt_of_mem hp) _
      obtain ⟨P', hP', L', hL', hmin, hpot⟩ := ih _ hlt (P.erase p) L rfl
      exact ⟨P', hP'.trans (Finset.erase_subset _ _), L', hL', hmin,
        (pruningPotential_le_erase_left R d P L hp hdeg.le).trans hpot⟩

theorem exists_degree_core (R : Pt → Ln → Prop) (d : ℝ) (P : Finset Pt) (L : Finset Ln) :
    ∃ P' : Finset Pt, P' ⊆ P ∧ ∃ L' : Finset Ln, L' ⊆ L ∧
      MinimumDegrees R d P' L' ∧ pruningPotential R d P L ≤ pruningPotential R d P' L' :=
  exists_degree_core_aux R d (P.card + L.card) P L rfl

theorem degree_core_incidence_lower_bound (R : Pt → Ln → Prop) {d : ℝ} (hd : 0 ≤ d)
    (P P' : Finset Pt) (L L' : Finset Ln)
    (hpot : pruningPotential R d P L ≤ pruningPotential R d P' L') :
    (incidenceCount R P L : ℝ) - d * ((P.card : ℝ) + (L.card : ℝ)) ≤
      (incidenceCount R P' L' : ℝ) := let _ := instDecidableEqPt; let _ := instDecidableEqLn; by
  have hnonneg : 0 ≤ d * ((P'.card : ℝ) + (L'.card : ℝ)) :=
    mul_nonneg hd (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  unfold pruningPotential at hpot
  linarith

end RyserCoveringCounterexample.Incidence

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_AllLineCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Incidence

variable {Pt Ln : Type*} [instDecidableEqPt : DecidableEq Pt] [DecidableEq Ln]

theorem leftDegree_le_erase_add_one (R : Pt → Ln → Prop) (L : Finset Ln)
    (p : Pt) (l : Ln) : leftDegree R L p ≤ leftDegree R (L.erase l) p + 1 := let _ := instDecidableEqPt; by
  classical
  apply (Finset.card_le_card (show L.filter (R p) ⊆
      insert l ((L.erase l).filter (R p)) from ?_)).trans (Finset.card_insert_le _ _)
  intro m hm
  obtain ⟨hmL, hpm⟩ := Finset.mem_filter.mp hm
  apply Finset.mem_insert.mpr
  by_cases he : m = l
  · exact Or.inl he
  · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨he, hmL⟩, hpm⟩)

theorem rightDegree_mul_sub_one_le (R : Pt → Ln → Prop) (P : Finset Pt)
    (L : Finset Ln) {d : ℝ}
    (hmin : ∀ p ∈ P, d ≤ (leftDegree R L p : ℝ))
    (huniq : ∀ l m : Ln, l ≠ m → ∀ p q : Pt,
      R p l → R p m → R q l → R q m → p = q) (l : Ln) :
    (rightDegree R P l : ℝ) * (d - 1) ≤ (L.card : ℝ) := by
  classical
  let Q := P.filter (fun p => R p l)
  have hupper : incidenceCount R Q (L.erase l) ≤ L.card := by
    calc
      incidenceCount R Q (L.erase l) =
          incidenceCount (fun l p => R p l) (L.erase l) Q := incidenceCount_swap R Q _
      _ ≤ ∑ m ∈ L.erase l, 1 := by
        apply Finset.sum_le_sum
        intro m hm
        change (Q.filter (fun p => R p m)).card ≤ 1
        apply Finset.card_le_one.mpr
        intro p hp q hq
        obtain ⟨hpQ, hpm⟩ := Finset.mem_filter.mp hp
        obtain ⟨hqQ, hqm⟩ := Finset.mem_filter.mp hq
        exact huniq m l (Finset.mem_erase.mp hm).1 p q hpm
          (Finset.mem_filter.mp hpQ).2 hqm (Finset.mem_filter.mp hqQ).2
      _ = (L.erase l).card := by simp
      _ ≤ L.card := Finset.card_erase_le
  have hlower : (Q.card : ℝ) * (d - 1) ≤ (incidenceCount R Q (L.erase l) : ℝ) := by
    calc
      (Q.card : ℝ) * (d - 1) = ∑ p ∈ Q, (d - 1) := by simp [mul_sub]
      _ ≤ ∑ p ∈ Q, (leftDegree R (L.erase l) p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hdegree := hmin p (Finset.mem_filter.mp hp).1
        have hdelete : (leftDegree R L p : ℝ) ≤
            (leftDegree R (L.erase l) p : ℝ) + 1 := by
          exact_mod_cast leftDegree_le_erase_add_one R L p l
        linarith
      _ = (incidenceCount R Q (L.erase l) : ℝ) := by
        simp only [incidenceCount, Nat.cast_sum]
  have hupper' : (incidenceCount R Q (L.erase l) : ℝ) ≤ (L.card : ℝ) := by
    exact_mod_cast hupper
  exact hlower.trans hupper'

theorem rightDegree_le_div_sub_one (R : Pt → Ln → Prop) (P : Finset Pt)
    (L : Finset Ln) {d : ℝ} (hd : 1 < d)
    (hmin : ∀ p ∈ P, d ≤ (leftDegree R L p : ℝ))
    (huniq : ∀ l m : Ln, l ≠ m → ∀ p q : Pt,
      R p l → R p m → R q l → R q m → p = q) (l : Ln) :
    (rightDegree R P l : ℝ) ≤ (L.card : ℝ) / (d - 1) :=
  (le_div_iff₀ (sub_pos.mpr hd)).2 (rightDegree_mul_sub_one_le R P L hmin huniq l)

variable {F : Type*} [Field F] [DecidableEq F]

theorem projective_all_line_cap (P : Finset (ProjectivePoint F))
    (L : Finset (ProjectiveLine F)) {d : ℝ} (hd : 1 < d)
    (hmin : ∀ p ∈ P, d ≤ (leftDegree ProjectiveIncidence L p : ℝ))
    (l : ProjectiveLine F) :
    (rightDegree ProjectiveIncidence P l : ℝ) ≤ (L.card : ℝ) / (d - 1) := by
  apply rightDegree_le_div_sub_one ProjectiveIncidence P L hd hmin
  intro l m hlm p q hpl hpm hql hqm
  exact eq_projectivePoint_of_common_incidence hlm hpl hpm hql hqm

end RyserCoveringCounterexample.Incidence

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_CoordinateTransferSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence

variable {F : Type*} [Field F] [instDecidableEqF : DecidableEq F]

theorem goodW_subset (T : ProjectiveTransform F)
    (W : Finset (ProjectivePoint F)) : goodW T W ⊆ W :=
  Finset.filter_subset _ _

theorem transformed_goodW_affine (T : ProjectiveTransform F)
    (W : Finset (ProjectivePoint F)) {w : ProjectivePoint F}
    (hw : w ∈ goodW T W) :
    T.points w = Sum.inl (affinePart (T.points w)) := by
  have hn : ¬ ProjectiveIncidence (T.points w) none := by
    intro h
    apply ((mem_goodW T W w).mp hw).2.1
    apply (T.incidence w (T.lines.symm none)).mp
    simpa only [Equiv.apply_symm_apply] using h
  cases htw : T.points w with
  | inl z => rfl
  | inr d =>
    exact (hn (by simp only [htw, ProjectiveIncidence])).elim

theorem mem_coordinateGraph_iff (T : ProjectiveTransform F)
    (W : Finset (ProjectivePoint F)) (z : Point F) :
    z ∈ coordinateGraph T W ↔
      ∃ w ∈ goodW T W, T.points w = Sum.inl z := by
  constructor
  · intro hz
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hz
    refine ⟨w, hw, ?_⟩
    simpa only [heq] using transformed_goodW_affine T W hw
  · rintro ⟨w, hw, heq⟩
    apply Finset.mem_image.mpr
    refine ⟨w, hw, ?_⟩
    rw [heq]
    rfl

theorem coordinateGraph_nonzero (T : ProjectiveTransform F)
    (W : Finset (ProjectivePoint F)) {z : Point F}
    (hz : z ∈ coordinateGraph T W) : z.1 ≠ 0 ∧ z.2 ≠ 0 := by
  obtain ⟨w, hw, heq⟩ := (mem_coordinateGraph_iff T W z).mp hz
  have hw' := (mem_goodW T W w).mp hw
  constructor
  · intro hx
    apply hw'.2.2.2
    apply (T.incidence w (T.lines.symm (some (none, 0)))).mp
    simpa [heq, ProjectiveIncidence, Incidence, projection] using hx
  · intro hy
    apply hw'.2.2.1
    apply (T.incidence w (T.lines.symm (some (some 0, 0)))).mp
    simpa [heq, ProjectiveIncidence, Incidence, projection] using hy

theorem card_coordinateGraph_eq_goodW (T : ProjectiveTransform F)
    (W : Finset (ProjectivePoint F)) :
    (coordinateGraph T W).card = (goodW T W).card := by
  apply Finset.card_image_of_injOn
  intro w hw v hv h
  change affinePart (T.points w) = affinePart (T.points v) at h
  apply T.points.injective
  rw [transformed_goodW_affine T W hw, transformed_goodW_affine T W hv]
  exact congrArg (fun z : Point F => (Sum.inl z : ProjectivePoint F)) h

theorem coordinateGraph_card_lower
    (P W : Finset (ProjectivePoint F)) (T : ProjectiveTransform F) (H : ℝ)
    (hWP : W ⊆ P)
    (hcap : ∀ l : ProjectiveLine F,
      ((P.filter fun p => ProjectiveIncidence p l).card : ℝ) ≤ H) :
    (W.card : ℝ) - 3 * H ≤ (coordinateGraph T W).card := by
  let A := P.filter fun p => ProjectiveIncidence p (T.lines.symm none)
  let B := P.filter fun p => ProjectiveIncidence p (T.lines.symm (some (some 0, 0)))
  let C := P.filter fun p => ProjectiveIncidence p (T.lines.symm (some (none, 0)))
  have hcover : W ⊆ ((goodW T W ∪ A) ∪ B) ∪ C := by
    intro w hw
    simp only [Finset.mem_union]
    by_cases hA : ProjectiveIncidence w (T.lines.symm none)
    · exact Or.inl (Or.inl (Or.inr (Finset.mem_filter.mpr ⟨hWP hw, hA⟩)))
    by_cases hB : ProjectiveIncidence w (T.lines.symm (some (some 0, 0)))
    · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨hWP hw, hB⟩))
    by_cases hC : ProjectiveIncidence w (T.lines.symm (some (none, 0)))
    · exact Or.inr (Finset.mem_filter.mpr ⟨hWP hw, hC⟩)
    exact Or.inl (Or.inl (Or.inl ((mem_goodW T W w).mpr ⟨hw, hA, hB, hC⟩)))
  have hnat : W.card ≤ (goodW T W).card + A.card + B.card + C.card := by
    calc
      W.card ≤ (((goodW T W ∪ A) ∪ B) ∪ C).card := Finset.card_le_card hcover
      _ ≤ ((goodW T W ∪ A) ∪ B).card + C.card := Finset.card_union_le _ _
      _ ≤ ((goodW T W ∪ A).card + B.card) + C.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ (((goodW T W).card + A.card) + B.card) + C.card :=
        Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
  have hreal := (Nat.cast_le (α := ℝ)).mpr hnat
  simp only [Nat.cast_add] at hreal
  have hA : (A.card : ℝ) ≤ H := hcap (T.lines.symm none)
  have hB : (B.card : ℝ) ≤ H := hcap (T.lines.symm (some (some 0, 0)))
  have hC : (C.card : ℝ) ≤ H := hcap (T.lines.symm (some (none, 0)))
  rw [card_coordinateGraph_eq_goodW T W]
  linarith

end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_Pencils
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence
noncomputable section
variable {F : Type*} [Field F] [instDecidableEqF : DecidableEq F]

private theorem line_mem_of_hasJoin {L : Finset (ProjectiveLine F)}
    {p : ProjectivePoint F} {z : Point F} {l : ProjectiveLine F}
    (hne : p ≠ Sum.inl z) (h : HasJoin L p z)
    (hp : ProjectiveIncidence p l) (hz : ProjectiveIncidence (Sum.inl z) l) :
    l ∈ L := let _ := instDecidableEqF; by
  obtain ⟨m, hm, hpm, hzm⟩ := h
  have heq : l = m := eq_projectiveLine_of_common_incidence hne hp hz hpm hzm
  rw [heq]
  exact hm

theorem normalized_witness_lines {L : Finset (ProjectiveLine F)} {z : Point F}
    (hz : z.1 ≠ 0)
    (hV : HasJoin L (Sum.inr none) z)
    (hH : HasJoin L (Sum.inr (some 0)) z)
    (hD : HasJoin L (Sum.inr (some 1)) z)
    (hO : HasJoin L (Sum.inl (0, 0)) z) :
    some (none, z.1) ∈ L ∧ some (some 0, z.2) ∈ L ∧
      some (some 1, -(z.1 - z.2)) ∈ L ∧
      some (some (z.1 / z.2)⁻¹, 0) ∈ L := by
  have hfinite (d : Direction F) : Sum.inr d ≠ (Sum.inl z : ProjectivePoint F) := by
    intro h
    cases h
  have horigin : (Sum.inl (0, 0) : ProjectivePoint F) ≠ Sum.inl z := by
    intro h
    exact hz (congrArg Prod.fst (Sum.inl.inj h)).symm
  refine ⟨line_mem_of_hasJoin (hfinite none) hV rfl rfl, ?_, ?_, ?_⟩
  · apply line_mem_of_hasJoin (l := some (some 0, z.2)) (hfinite (some 0)) hH rfl
    simp only [ProjectiveIncidence, Incidence, projection, zero_mul, sub_zero]
  · apply line_mem_of_hasJoin (l := some (some 1, -(z.1 - z.2))) (hfinite (some 1)) hD rfl
    simp only [ProjectiveIncidence, Incidence, projection, one_mul, neg_sub]
  · apply line_mem_of_hasJoin horigin hO
    · simp only [ProjectiveIncidence, Incidence, projection, mul_zero, sub_self]
    · change z.2 - (z.1 / z.2)⁻¹ * z.1 = 0
      rw [inv_div, div_mul_cancel₀ _ hz, sub_self]

private theorem card_image_le_pencilSlice
    (G : Finset (Point F)) (L : Finset (ProjectiveLine F))
    (p : ProjectivePoint F) (f : Point F → F) (ell : F → ProjectiveLine F)
    (hinj : Function.Injective ell)
    (hline : ∀ z ∈ G, ell (f z) ∈ L)
    (hp : ∀ a, ProjectiveIncidence p (ell a)) :
    (G.image f).card ≤ (pencilSlice L p).card := by
  apply Finset.card_le_card_of_injOn ell
  · intro a ha
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_filter.mpr ⟨hline z hz, hp (f z)⟩
  · exact fun _ _ _ _ h => hinj h

theorem normalized_coordinate_card_bounds
    (G : Finset (Point F)) (L : Finset (ProjectiveLine F))
    (hnonzero : ∀ z ∈ G, z.1 ≠ 0 ∧ z.2 ≠ 0)
    (hjoins : ∀ z ∈ G,
      HasJoin L (Sum.inr none) z ∧ HasJoin L (Sum.inr (some 0)) z ∧
      HasJoin L (Sum.inr (some 1)) z ∧ HasJoin L (Sum.inl (0, 0)) z) :
    (G.image Prod.fst).card ≤ (pencilSlice L (Sum.inr none)).card ∧
    (G.image Prod.snd).card ≤ (pencilSlice L (Sum.inr (some 0))).card ∧
    (G.image (fun z => z.1 - z.2)).card ≤
      (pencilSlice L (Sum.inr (some 1))).card ∧
    (G.image (fun z => z.1 / z.2)).card ≤
      (pencilSlice L (Sum.inl (0, 0))).card := by
  have hlines (z : Point F) (hz : z ∈ G) := normalized_witness_lines
    (hnonzero z hz).1 (hjoins z hz).1 (hjoins z hz).2.1
      (hjoins z hz).2.2.1 (hjoins z hz).2.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply card_image_le_pencilSlice G L (Sum.inr none) Prod.fst
      (fun a => some (none, a))
    · intro a b h
      exact congrArg Prod.snd (Option.some.inj h)
    · exact fun z hz => (hlines z hz).1
    · exact fun _ => rfl
  · apply card_image_le_pencilSlice G L (Sum.inr (some 0)) Prod.snd
      (fun a => some (some 0, a))
    · intro a b h
      exact congrArg Prod.snd (Option.some.inj h)
    · exact fun z hz => (hlines z hz).2.1
    · exact fun _ => rfl
  · apply card_image_le_pencilSlice G L (Sum.inr (some 1)) (fun z => z.1 - z.2)
      (fun a => some (some 1, -a))
    · intro a b h
      exact neg_injective (congrArg Prod.snd (Option.some.inj h))
    · exact fun z hz => (hlines z hz).2.2.1
    · exact fun _ => rfl
  · apply card_image_le_pencilSlice G L (Sum.inl (0, 0)) (fun z => z.1 / z.2)
      (fun a => some (some a⁻¹, 0))
    · intro a b h
      exact inv_injective (Option.some.inj (congrArg Prod.fst (Option.some.inj h)))
    · exact fun z hz => (hlines z hz).2.2.2
    · intro a
      simp only [ProjectiveIncidence, Incidence, projection, mul_zero, sub_self]

end
end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_CoordinateTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence

noncomputable section

variable {F : Type*} [Field F] [DecidableEq F]

theorem pencilSlice_image_transform (T : ProjectiveTransform F)
    (L : Finset (ProjectiveLine F)) (p : ProjectivePoint F) :
    pencilSlice (L.image T.lines) (T.points p) = (pencilSlice L p).image T.lines := by
  ext l
  constructor
  · intro hl
    obtain ⟨hl, hp⟩ := Finset.mem_filter.mp hl
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hl
    exact Finset.mem_image.mpr ⟨m,
      Finset.mem_filter.mpr ⟨hm, (T.incidence p m).mp hp⟩, rfl⟩
  · intro hl
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨hm, hp⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem T.lines hm,
      (T.incidence p m).mpr hp⟩

theorem card_pencilSlice_image_transform (T : ProjectiveTransform F)
    (L : Finset (ProjectiveLine F)) (p : ProjectivePoint F) :
    (pencilSlice (L.image T.lines) (T.points p)).card = (pencilSlice L p).card := by
  rw [pencilSlice_image_transform]
  exact Finset.card_image_of_injective _ T.lines.injective

theorem hasJoin_image_transform (T : ProjectiveTransform F)
    (L : Finset (ProjectiveLine F)) (p w : ProjectivePoint F) (z : Point F)
    (hw : T.points w = Sum.inl z)
    (hjoin : ∃ l ∈ L, ProjectiveIncidence p l ∧ ProjectiveIncidence w l) :
    HasJoin (L.image T.lines) (T.points p) z := by
  obtain ⟨l, hl, hp, hwl⟩ := hjoin
  refine ⟨T.lines l, Finset.mem_image_of_mem T.lines hl, (T.incidence p l).mpr hp, ?_⟩
  rw [← hw]
  exact (T.incidence w l).mpr hwl

theorem coordinateGraph_hasJoin (T : ProjectiveTransform F)
    (W : Finset (ProjectivePoint F)) (L : Finset (ProjectiveLine F))
    (p : ProjectivePoint F)
    (hjoin : ∀ w ∈ W, ∃ l ∈ L,
      ProjectiveIncidence p l ∧ ProjectiveIncidence w l)
    (z : Point F) (hz : z ∈ coordinateGraph T W) :
    HasJoin (L.image T.lines) (T.points p) z := by
  obtain ⟨w, hw, hTw⟩ := (mem_coordinateGraph_iff T W z).mp hz
  exact hasJoin_image_transform T L p w z hTw
    (hjoin w (goodW_subset T W hw))

theorem coordinate_transfer
    (P W : Finset (ProjectivePoint F)) (L : Finset (ProjectiveLine F))
    (T : ProjectiveTransform F) (p1 p2 p3 p4 : ProjectivePoint F) (H : ℝ)
    (hWP : W ⊆ P)
    (hcap : ∀ l : ProjectiveLine F,
      ((P.filter (fun p => ProjectiveIncidence p l)).card : ℝ) ≤ H)
    (hdegree : ∀ p ∈ P, ((pencilSlice L p).card : ℝ) ≤ H)
    (hp1 : p1 ∈ P) (hp2 : p2 ∈ P) (hp3 : p3 ∈ P) (hp4 : p4 ∈ P)
    (hT1 : T.points p1 = Sum.inr (some 0))
    (hT2 : T.points p2 = Sum.inr none)
    (hT3 : T.points p3 = Sum.inr (some 1))
    (hT4 : T.points p4 = Sum.inl (0, 0))
    (hjoins : ∀ w ∈ W,
      (∃ l ∈ L, ProjectiveIncidence p1 l ∧ ProjectiveIncidence w l) ∧
      (∃ l ∈ L, ProjectiveIncidence p2 l ∧ ProjectiveIncidence w l) ∧
      (∃ l ∈ L, ProjectiveIncidence p3 l ∧ ProjectiveIncidence w l) ∧
      (∃ l ∈ L, ProjectiveIncidence p4 l ∧ ProjectiveIncidence w l)) :
    (W.card : ℝ) - 3 * H ≤ (coordinateGraph T W).card ∧
    (∀ z ∈ coordinateGraph T W, z.1 ≠ 0 ∧ z.2 ≠ 0) ∧
    (((coordinateGraph T W).image Prod.fst).card : ℝ) ≤ H ∧
    (((coordinateGraph T W).image Prod.snd).card : ℝ) ≤ H ∧
    (((coordinateGraph T W).image (fun z => z.1 - z.2)).card : ℝ) ≤ H ∧
    (((coordinateGraph T W).image (fun z => z.1 / z.2)).card : ℝ) ≤ H := by
  have hj1 (z : Point F) (hz : z ∈ coordinateGraph T W) :
      HasJoin (L.image T.lines) (Sum.inr (some 0)) z := by
    simpa only [hT1] using coordinateGraph_hasJoin T W L p1
      (fun w hw => (hjoins w hw).1) z hz
  have hj2 (z : Point F) (hz : z ∈ coordinateGraph T W) :
      HasJoin (L.image T.lines) (Sum.inr none) z := by
    simpa only [hT2] using coordinateGraph_hasJoin T W L p2
      (fun w hw => (hjoins w hw).2.1) z hz
  have hj3 (z : Point F) (hz : z ∈ coordinateGraph T W) :
      HasJoin (L.image T.lines) (Sum.inr (some 1)) z := by
    simpa only [hT3] using coordinateGraph_hasJoin T W L p3
      (fun w hw => (hjoins w hw).2.2.1) z hz
  have hj4 (z : Point F) (hz : z ∈ coordinateGraph T W) :
      HasJoin (L.image T.lines) (Sum.inl (0, 0)) z := by
    simpa only [hT4] using coordinateGraph_hasJoin T W L p4
      (fun w hw => (hjoins w hw).2.2.2) z hz
  have hb := normalized_coordinate_card_bounds (coordinateGraph T W) (L.image T.lines)
    (fun z hz => coordinateGraph_nonzero T W hz)
    (fun z hz => ⟨hj2 z hz, hj1 z hz, hj3 z hz, hj4 z hz⟩)
  have hd1 : ((pencilSlice (L.image T.lines) (Sum.inr (some 0))).card : ℝ) ≤ H := by
    rw [← hT1, card_pencilSlice_image_transform]
    exact hdegree p1 hp1
  have hd2 : ((pencilSlice (L.image T.lines) (Sum.inr none)).card : ℝ) ≤ H := by
    rw [← hT2, card_pencilSlice_image_transform]
    exact hdegree p2 hp2
  have hd3 : ((pencilSlice (L.image T.lines) (Sum.inr (some 1))).card : ℝ) ≤ H := by
    rw [← hT3, card_pencilSlice_image_transform]
    exact hdegree p3 hp3
  have hd4 : ((pencilSlice (L.image T.lines) (Sum.inl (0, 0))).card : ℝ) ≤ H := by
    rw [← hT4, card_pencilSlice_image_transform]
    exact hdegree p4 hp4
  refine ⟨coordinateGraph_card_lower P W T H hWP hcap,
    (fun z hz => coordinateGraph_nonzero T W hz), ?_, ?_, ?_, ?_⟩
  · exact (show (((coordinateGraph T W).image Prod.fst).card : ℝ) ≤
        ((pencilSlice (L.image T.lines) (Sum.inr none)).card : ℝ) by
          exact_mod_cast hb.1).trans hd2
  · exact (show (((coordinateGraph T W).image Prod.snd).card : ℝ) ≤
        ((pencilSlice (L.image T.lines) (Sum.inr (some 0))).card : ℝ) by
          exact_mod_cast hb.2.1).trans hd1
  · exact (show (((coordinateGraph T W).image (fun z => z.1 - z.2)).card : ℝ) ≤
        ((pencilSlice (L.image T.lines) (Sum.inr (some 1))).card : ℝ) by
          exact_mod_cast hb.2.2.1).trans hd3
  · exact (show (((coordinateGraph T W).image (fun z => z.1 / z.2)).card : ℝ) ≤
        ((pencilSlice (L.image T.lines) (Sum.inl (0, 0))).card : ℝ) by
          exact_mod_cast hb.2.2.2).trans hd4

end

end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_DegreeSquares
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Incidence

variable {Pt Ln : Type*} [DecidableEq Pt] [DecidableEq Ln]

private theorem rightDegree_sq_eq_sum (R : Pt → Ln → Prop) (P : Finset Pt) (l : Ln) :
    rightDegree R P l ^ 2 =
      ∑ p ∈ P, ∑ q ∈ P, if R p l ∧ R q l then 1 else 0 := by
  classical
  rw [rightDegree, leftDegree_eq_sum, pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hpl : R p l <;> by_cases hql : R q l <;> simp [hpl, hql]

theorem sum_rightDegree_sq_eq_commonCount (R : Pt → Ln → Prop)
    (P : Finset Pt) (L : Finset Ln) :
    (∑ l ∈ L, rightDegree R P l ^ 2) =
      ∑ p ∈ P, ∑ q ∈ P, (L.filter fun l => R p l ∧ R q l).card := by
  classical
  simp_rw [rightDegree_sq_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  exact Finset.sum_boole (R := ℕ) (fun l => R p l ∧ R q l) L

theorem sum_rightDegree_sq_le_nat (R : Pt → Ln → Prop)
    (P : Finset Pt) (L : Finset Ln)
    (huniq : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → ∀ l ∈ L, ∀ m ∈ L,
      R p l → R q l → R p m → R q m → l = m) :
    (∑ l ∈ L, rightDegree R P l ^ 2) ≤ incidenceCount R P L + P.card ^ 2 := by
  classical
  have hpair (p : Pt) (hp : p ∈ P) (q : Pt) (hq : q ∈ P) :
      (L.filter fun l => R p l ∧ R q l).card ≤
        (if p = q then leftDegree R L p else 0) + 1 := by
    by_cases hpq : p = q
    · subst q
      simp only [and_self]
      change leftDegree R L p ≤ leftDegree R L p + 1
      exact Nat.le_succ _
    · rw [ite_eq_right hpq, zero_add]
      apply Finset.card_le_one.mpr
      intro l hl m hm
      obtain ⟨hlL, hpl, hql⟩ := Finset.mem_filter.mp hl
      obtain ⟨hmL, hpm, hqm⟩ := Finset.mem_filter.mp hm
      exact huniq p hp q hq hpq l hlL m hmL hpl hql hpm hqm
  have hrow (p : Pt) (hp : p ∈ P) :
      (∑ q ∈ P, (L.filter fun l => R p l ∧ R q l).card) ≤
        leftDegree R L p + P.card := by
    calc
      (∑ q ∈ P, (L.filter fun l => R p l ∧ R q l).card) ≤
          ∑ q ∈ P, ((if p = q then leftDegree R L p else 0) + 1) :=
        Finset.sum_le_sum fun q hq => hpair p hp q hq
      _ = leftDegree R L p + P.card := by
        simp [Finset.sum_add_distrib, hp]
  calc
    (∑ l ∈ L, rightDegree R P l ^ 2) =
        ∑ p ∈ P, ∑ q ∈ P, (L.filter fun l => R p l ∧ R q l).card :=
      sum_rightDegree_sq_eq_commonCount R P L
    _ ≤ ∑ p ∈ P, (leftDegree R L p + P.card) :=
      Finset.sum_le_sum fun p hp => hrow p hp
    _ = incidenceCount R P L + P.card ^ 2 := by
      simp [incidenceCount, Finset.sum_add_distrib, pow_two]

theorem sum_rightDegree_sq_le (R : Pt → Ln → Prop)
    (P : Finset Pt) (L : Finset Ln)
    (huniq : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → ∀ l ∈ L, ∀ m ∈ L,
      R p l → R q l → R p m → R q m → l = m) :
    (∑ l ∈ L, (rightDegree R P l : ℝ) ^ 2) ≤
      (incidenceCount R P L : ℝ) + (P.card : ℝ) ^ 2 := by
  exact_mod_cast sum_rightDegree_sq_le_nat R P L huniq

theorem sum_leftDegree_sq_le (R : Pt → Ln → Prop)
    (P : Finset Pt) (L : Finset Ln)
    (huniq : ∀ l ∈ L, ∀ m ∈ L, l ≠ m → ∀ p ∈ P, ∀ q ∈ P,
      R p l → R p m → R q l → R q m → p = q) :
    (∑ p ∈ P, (leftDegree R L p : ℝ) ^ 2) ≤
      (incidenceCount R P L : ℝ) + (L.card : ℝ) ^ 2 := by
  have h := sum_rightDegree_sq_le (fun l p => R p l) L P huniq
  rw [← incidenceCount_swap R P L] at h
  exact h

variable {F : Type*} [Field F] [DecidableEq F]

theorem sum_projective_rightDegree_sq_le
    (P : Finset (ProjectivePoint F)) (L : Finset (ProjectiveLine F)) :
    (∑ l ∈ L, (rightDegree ProjectiveIncidence P l : ℝ) ^ 2) ≤
      (incidenceCount ProjectiveIncidence P L : ℝ) + (P.card : ℝ) ^ 2 := by
  apply sum_rightDegree_sq_le
  intro p hp q hq hpq l hl m hm hpl hql hpm hqm
  exact eq_projectiveLine_of_common_incidence hpq hpl hql hpm hqm

theorem sum_projective_leftDegree_sq_le
    (P : Finset (ProjectivePoint F)) (L : Finset (ProjectiveLine F)) :
    (∑ p ∈ P, (leftDegree ProjectiveIncidence L p : ℝ) ^ 2) ≤
      (incidenceCount ProjectiveIncidence P L : ℝ) + (L.card : ℝ) ^ 2 := by
  apply sum_leftDegree_sq_le
  intro l hl m hm hlm p hp q hq hpl hpm hql hqm
  exact eq_projectivePoint_of_common_incidence hlm hpl hpm hql hqm

end RyserCoveringCounterexample.Incidence

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_WalkCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Incidence

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem neighbors_subset (A : Finset α) (G : Finset (α × β)) (b : β) :
    neighbors A G b ⊆ A := Finset.filter_subset _ _

theorem commonNeighbors_comm (B : Finset β) (G : Finset (α × β)) (a a' : α) :
    commonNeighbors B G a a' = commonNeighbors B G a' a := by
  ext b
  simp only [mem_commonNeighbors, and_comm]

theorem card_fourWalks (A : Finset α) (B : Finset β) (G : Finset (α × β))
    (a a' : α) :
    (fourWalks A B G a a').card =
      ∑ a₂ ∈ A, (commonNeighbors B G a a₂).card * (commonNeighbors B G a₂ a').card := by
  simp only [fourWalks, Finset.card_sigma, Finset.card_product]

theorem card_edges_eq_sum_neighbors (A : Finset α) (B : Finset β)
    (G : Finset (α × β)) (hG : G ⊆ A ×ˢ B) :
    G.card = ∑ b ∈ B, (neighbors A G b).card := by
  have hfilter : (A ×ˢ B).filter (fun e => e ∈ G) = G := by
    ext e
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hG h, h⟩⟩
  calc
    G.card = ((A ×ˢ B).filter (fun e => e ∈ G)).card :=
      congrArg Finset.card hfilter.symm
    _ = ∑ b ∈ B, (neighbors A G b).card := by
      simp only [neighbors, Finset.card_filter, Finset.sum_product_right]

noncomputable section
attribute [local instance] Classical.propDecidable

theorem card_badPairs_eq_sum_badPartners (A : Finset α) (B : Finset β)
    (G : Finset (α × β)) (t : ℝ) :
    (badPairs A B G t).card = ∑ a ∈ A, (badPartners A B G t a).card := by
  simp only [badPairs, badPartners, Finset.card_filter, Finset.sum_product]

theorem sum_localBad_card_eq_sum_common (A : Finset α) (B : Finset β)
    (G : Finset (α × β)) (t : ℝ) :
    (∑ b ∈ B, (localBad A B G t b).card) =
      ∑ p ∈ badPairs A B G t, (commonNeighbors B G p.1 p.2).card := by
  simp only [localBad, commonNeighbors, Finset.card_filter]
  exact Finset.sum_comm

theorem localBad_eq_badPairs_neighbors (A : Finset α) (B : Finset β)
    (G : Finset (α × β)) (t : ℝ) (b : β) :
    localBad A B G t b = badPairs (neighbors A G b) B G t := by
  ext p
  simp only [localBad, badPairs, neighbors, Finset.mem_filter, Finset.mem_product]
  simp only [and_assoc, and_left_comm, and_comm]

end

end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_DenseNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Incidence

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem exists_dense_neighborhood
    (A : Finset α) (B : Finset β) (G : Finset (α × β))
    (hG : G ⊆ A ×ˢ B) {n V : ℝ} (hn : 0 < n) (hV : 2 ≤ V)
    (hA : (A.card : ℝ) ≤ V * n) (hB : (B.card : ℝ) ≤ V * n)
    (hE : n ^ 2 / V ≤ (G.card : ℝ)) :
    ∃ b ∈ B,
      n / (2 * V ^ 2) ≤ ((neighbors A G b).card : ℝ) ∧
      ((badPairs (neighbors A G b) B G (n / (512 * V ^ 8))).card : ℝ) ≤
        ((neighbors A G b).card : ℝ) ^ 2 / 16 := by
  classical
  have hVpos : 0 < V := by linarith
  have hVne : V ≠ 0 := ne_of_gt hVpos
  have hVn : 0 < V * n := mul_pos hVpos hn
  let c : ℝ := n / (2 * V ^ 2)
  let t : ℝ := n / (512 * V ^ 8)
  let U : ℝ := n ^ 2 / (256 * V ^ 4)
  let d : β → ℝ := fun b => ((neighbors A G b).card : ℝ)
  let H : Finset β := B.filter fun b => c ≤ d b
  let L : Finset β := B.filter fun b => ¬c ≤ d b
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  have hU : 0 ≤ U := by
    dsimp [U]
    positivity
  have htwice : n ^ 2 / V = 2 * ((V * n) * c) := by
    dsimp [c]
    field_simp [hVne]
  have havg : (V * n) ^ 2 * t = c * U := by
    dsimp [c, t, U]
    field_simp [hVne]; ring
  have hscale : 64 * U = c ^ 2 := by
    dsimp [c, U]
    field_simp [hVne]; ring
  have hdeg (b : β) : d b ≤ V * n := by
    exact (show ((neighbors A G b).card : ℝ) ≤ (A.card : ℝ) from
      Nat.cast_le.mpr (Finset.card_le_card (neighbors_subset A G b))).trans hA
  have hsum_edges : (G.card : ℝ) = ∑ b ∈ B, d b := by
    simpa only [d, Nat.cast_sum] using
      congrArg (fun k : ℕ => (k : ℝ)) (card_edges_eq_sum_neighbors A B G hG)
  have hsplit : (∑ b ∈ H, d b) + (∑ b ∈ L, d b) = ∑ b ∈ B, d b := by
    exact Finset.sum_filter_add_sum_filter_not B (fun b => c ≤ d b) d
  have hhigh : (∑ b ∈ H, d b) ≤ (H.card : ℝ) * (V * n) := by
    simpa only [nsmul_eq_mul] using
      Finset.sum_le_card_nsmul H d (V * n) (fun b _ => hdeg b)
  have hlow : (∑ b ∈ L, d b) ≤ (V * n) * c := by
    calc
      (∑ b ∈ L, d b) ≤ (L.card : ℝ) * c := by
        simpa only [nsmul_eq_mul] using
          Finset.sum_le_card_nsmul L d c (fun b hb =>
            (lt_of_not_ge (Finset.mem_filter.mp hb).2).le)
      _ ≤ (B.card : ℝ) * c :=
        mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))) hc.le
      _ ≤ (V * n) * c := mul_le_mul_of_nonneg_right hB hc.le
  have htotal : n ^ 2 / V ≤ (H.card : ℝ) * (V * n) + (V * n) * c := by
    calc
      n ^ 2 / V ≤ (G.card : ℝ) := hE
      _ = (∑ b ∈ H, d b) + (∑ b ∈ L, d b) := hsum_edges.trans hsplit.symm
      _ ≤ (H.card : ℝ) * (V * n) + (V * n) * c := add_le_add hhigh hlow
  have hHcard : c ≤ (H.card : ℝ) := by
    apply (mul_le_mul_iff_left₀ hVn).mp
    nlinarith only [htotal, htwice]
  have hH : H.Nonempty :=
    Finset.card_pos.mp (Nat.cast_pos.mp (hc.trans_le hHcard))
  have hbadcard : ((badPairs A B G t).card : ℝ) ≤ (A.card : ℝ) ^ 2 := by
    have hnat : (badPairs A B G t).card ≤ A.card * A.card := by
      calc
        (badPairs A B G t).card ≤ (A ×ˢ A).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = A.card * A.card := Finset.card_product A A
    exact_mod_cast (show (badPairs A B G t).card ≤ A.card ^ 2 by
      simpa only [pow_two] using hnat)
  have hcount :
      (∑ b ∈ B, ((localBad A B G t b).card : ℝ)) =
        ∑ p ∈ badPairs A B G t, ((commonNeighbors B G p.1 p.2).card : ℝ) := by
    simpa only [Nat.cast_sum] using
      congrArg (fun k : ℕ => (k : ℝ)) (sum_localBad_card_eq_sum_common A B G t)
  have hbad : (∑ b ∈ B, ((localBad A B G t b).card : ℝ)) ≤ c * U := by
    calc
      (∑ b ∈ B, ((localBad A B G t b).card : ℝ)) =
          ∑ p ∈ badPairs A B G t, ((commonNeighbors B G p.1 p.2).card : ℝ) := hcount
      _ ≤ ((badPairs A B G t).card : ℝ) * t := by
        simpa only [nsmul_eq_mul] using
          Finset.sum_le_card_nsmul (badPairs A B G t)
            (fun p => ((commonNeighbors B G p.1 p.2).card : ℝ)) t
            (fun p hp => (Finset.mem_filter.mp hp).2.le)
      _ ≤ (A.card : ℝ) ^ 2 * t := mul_le_mul_of_nonneg_right hbadcard ht
      _ ≤ (V * n) ^ 2 * t := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hA 2) ht
      _ = c * U := havg
  have hsmall : (∑ b ∈ H, ((localBad A B G t b).card : ℝ)) ≤ (H.card : ℝ) * U := by
    calc
      (∑ b ∈ H, ((localBad A B G t b).card : ℝ)) ≤
          ∑ b ∈ B, ((localBad A B G t b).card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun b _ _ => Nat.cast_nonneg _)
      _ ≤ c * U := hbad
      _ ≤ (H.card : ℝ) * U := mul_le_mul_of_nonneg_right hHcard hU
  obtain ⟨b, hb, hlocal⟩ := Finset.exists_le_of_sum_le
    (s := H) (f := fun b => ((localBad A B G t b).card : ℝ))
    (g := fun _ => U) hH
    (by simpa only [Finset.sum_const, nsmul_eq_mul] using hsmall)
  have hbB : b ∈ B := (Finset.mem_filter.mp hb).1
  have hcb : c ≤ d b := (Finset.mem_filter.mp hb).2
  have hsquare : c ^ 2 ≤ (d b) ^ 2 := pow_le_pow_left₀ hc.le hcb 2
  have hbound : U ≤ (d b) ^ 2 / 16 := by
    nlinarith only [hscale, hsquare, sq_nonneg (d b)]
  refine ⟨b, hbB, hcb, ?_⟩
  change ((badPairs (neighbors A G b) B G t).card : ℝ) ≤ (d b) ^ 2 / 16
  rw [← localBad_eq_badPairs_neighbors A B G t b]
  exact hlocal.trans hbound

end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_NoApproximateSubfieldNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence

theorem pow_mul_lt_sq_of_popular_lower
    (K s t : ℝ) (j : ℕ) (hK : 0 < K) (hs : 0 < s)
    (ht : s / (2 * K) ≤ t) (hlarge : 4 * K ^ (j + 2) < s) :
    K ^ j * s < t ^ 2 := by
  have hden : 0 < 2 * K := mul_pos (by norm_num) hK
  have hst : s ≤ 2 * K * t := by
    simpa only [mul_comm t] using (div_le_iff₀ hden).mp ht
  have hsq : s ^ 2 ≤ (2 * K * t) ^ 2 := pow_le_pow_left₀ hs.le hst 2
  apply (mul_lt_mul_iff_left₀ (pow_pos hden 2)).mp
  calc
    (K ^ j * s) * (2 * K) ^ 2 = 4 * K ^ (j + 2) * s := by
      rw [pow_add]
      ring
    _ < s ^ 2 := by nlinarith [mul_lt_mul_of_pos_right hlarge hs]
    _ ≤ t ^ 2 * (2 * K) ^ 2 := by nlinarith only [hsq]

theorem noapprox_threshold_numerics
    (K s t : ℝ) (hK : 2 ≤ K) (ht : s / (2 * K) ≤ t)
    (hlarge : 4 * K ^ 127942 < s) :
    0 < s ∧ 2 < t ∧ K ^ 127940 * s < t ^ 2 ∧
      2 * (K ^ 527 * s) < t ^ 2 := by
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hKone : 1 ≤ K := le_trans (by norm_num) hK
  have hs : 0 < s := lt_trans (mul_pos (by norm_num) (pow_pos hKpos _)) hlarge
  have hden : 0 < 2 * K := mul_pos (by norm_num) hKpos
  have hst : s ≤ 2 * K * t := by
    simpa only [mul_comm t] using (div_le_iff₀ hden).mp ht
  have hKpow : K ≤ K ^ 127942 := le_self_pow₀ hKone (by norm_num)
  have htlarge : 2 < t := by
    apply (mul_lt_mul_iff_right₀ hden).mp
    nlinarith only [hlarge, hKpow, hst]
  have hlong : K ^ 127940 * s < t ^ 2 :=
    pow_mul_lt_sq_of_popular_lower K s t 127940 hKpos hs ht hlarge
  have hpow : 2 * K ^ 527 ≤ K ^ 127940 := by
    calc
      2 * K ^ 527 ≤ K * K ^ 527 :=
        mul_le_mul_of_nonneg_right hK (pow_nonneg hKpos.le _)
      _ = K ^ 528 := (pow_succ' K 527).symm
      _ ≤ K ^ 127940 := pow_le_pow_right₀ hKone (by norm_num)
  refine ⟨hs, htlarge, hlong, ?_⟩
  calc
    2 * (K ^ 527 * s) = (2 * K ^ 527) * s := by ring
    _ ≤ K ^ 127940 * s := mul_le_mul_of_nonneg_right hpow hs.le
    _ < t ^ 2 := hlong

theorem cube_lt_of_popular_lower
    (K s t q : ℝ) (hK : 0 < K) (hs : 0 ≤ s)
    (ht : s / (2 * K) ≤ t) (hlarge : 8 * K ^ 3 * q < s ^ 3) :
    q < t ^ 3 := by
  have hden : 0 < 2 * K := mul_pos (by norm_num) hK
  have hst : s ≤ 2 * K * t := by
    simpa only [mul_comm t] using (div_le_iff₀ hden).mp ht
  have hcube : s ^ 3 ≤ (2 * K * t) ^ 3 := pow_le_pow_left₀ hs hst 3
  apply (mul_lt_mul_iff_right₀ (mul_pos (by norm_num : (0 : ℝ) < 8)
    (pow_pos hK 3))).mp
  calc
    8 * K ^ 3 * q < s ^ 3 := hlarge
    _ ≤ (2 * K * t) ^ 3 := hcube
    _ = 8 * K ^ 3 * t ^ 3 := by ring

end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_FiniteSetCovering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence.FiniteSetEstimates

open scoped Pointwise

variable {F : Type*} [AddCommGroup F] [DecidableEq F]

theorem covering_add (A B : Finset F) (hB : B.Nonempty) {K : ℝ}
    (hK : ((A + B).card : ℝ) ≤ K * (B.card : ℝ)) :
    ∃ T ⊆ A, (T.card : ℝ) ≤ K ∧ A ⊆ T + (B - B) := by
  exact Finset.ruzsa_covering_add hB hK

end RyserCoveringCounterexample.Incidence.FiniteSetEstimates

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_FiniteSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Pointwise

namespace RyserCoveringCounterexample.Incidence

variable {F : Type*} [AddCommGroup F] [DecidableEq F]

theorem card_sub_swap (X Y : Finset F) : (X - Y).card = (Y - X).card := by
  calc
    (X - Y).card = (-(X - Y)).card := (Finset.card_neg _).symm
    _ = (Y - X).card := by rw [neg_sub]

theorem triangle_card_le (X Y Z : Finset F) :
    (X - Y).card * Z.card ≤ (X - Z).card * (Z - Y).card := by
  simpa only [card_sub_swap Y Z] using
    FiniteSetEstimates.ruzsa_triangle_inequality_sub_sub_sub X Z Y

theorem covering_sub (X Y : Finset F) (hY : Y.Nonempty) {M : ℝ}
    (hM : ((X - Y).card : ℝ) ≤ M * Y.card) :
    ∃ T ⊆ X, (T.card : ℝ) ≤ M ∧ X ⊆ T + (Y - Y) := by
  obtain ⟨T, hTX, hT, hcover⟩ :=
    FiniteSetEstimates.covering_add X (-Y) hY.neg
      (by simpa only [Finset.card_neg, sub_eq_add_neg] using hM)
  exact ⟨T, hTX, hT, by simpa only [neg_sub_neg] using hcover⟩

theorem multiple_sum_sub_card_le (Y : Finset F) (hY : Y.Nonempty) {M : ℝ}
    (hM : ((Y - Y).card : ℝ) ≤ M * Y.card) (u v : ℕ) :
    ((u • Y - v • Y).card : ℝ) ≤ M ^ (u + v) * Y.card := by
  have hNN := FiniteSetEstimates.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_sub
    (A := Y) hY Y u v
  have hRat : ((u • Y - v • Y).card : ℚ) ≤
      (((Y - Y).card : ℚ) / Y.card) ^ (u + v) * Y.card := by
    exact_mod_cast hNN
  have hReal : ((u • Y - v • Y).card : ℝ) ≤
      (((Y - Y).card : ℝ) / Y.card) ^ (u + v) * Y.card := by
    have hcast := (Rat.cast_le (K := ℝ)).2 hRat
    simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_pow, Rat.cast_div] using hcast
  have hy : (0 : ℝ) < Y.card := Nat.cast_pos.mpr hY.card_pos
  have hr : ((Y - Y).card : ℝ) / Y.card ≤ M := (div_le_iff₀ hy).2 hM
  exact hReal.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hy.le) hr (u + v))
    (Nat.cast_nonneg _))

end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_PopularOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence

open scoped BigOperators

variable {ι α : Type*} [instDecidableEqι : DecidableEq ι] [DecidableEq α]

private theorem sum_membership_indicator
    (A U : Finset α) (hAU : A ⊆ U) :
    (∑ x ∈ U, if x ∈ A then (1 : ℝ) else 0) = (A.card : ℝ) := by
  have hfilter : U.filter (fun x => x ∈ A) = A := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter]
    exact ⟨fun hx => hx.2, fun hx => ⟨hAU hx, hx⟩⟩
  rw [Finset.sum_boole, hfilter]

private theorem sum_overlap_multiplicity
    (I : Finset ι) (T : ι → Finset α) (U : Finset α)
    (hTU : ∀ i ∈ I, T i ⊆ U) :
    (∑ x ∈ U, ∑ i ∈ I, if x ∈ T i then (1 : ℝ) else 0) =
      ∑ i ∈ I, ((T i).card : ℝ) := let _ := instDecidableEqι; by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  exact sum_membership_indicator (T i) U (hTU i hi)

private theorem sum_sq_overlap_multiplicity
    (I : Finset ι) (T : ι → Finset α) (U : Finset α)
    (hTU : ∀ i ∈ I, T i ⊆ U) :
    (∑ x ∈ U, (∑ i ∈ I, if x ∈ T i then (1 : ℝ) else 0) ^ 2) =
      ∑ i ∈ I, ∑ j ∈ I, ((T i ∩ T j).card : ℝ) := let _ := instDecidableEqι; by
  calc
    (∑ x ∈ U, (∑ i ∈ I, if x ∈ T i then (1 : ℝ) else 0) ^ 2) =
        ∑ x ∈ U, ∑ i ∈ I, ∑ j ∈ I,
          (if x ∈ T i then (1 : ℝ) else 0) *
          (if x ∈ T j then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [pow_two, Finset.sum_mul_sum]
    _ = ∑ i ∈ I, ∑ j ∈ I, ∑ x ∈ U,
          (if x ∈ T i then (1 : ℝ) else 0) *
          (if x ∈ T j then (1 : ℝ) else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ i ∈ I, ∑ j ∈ I, ((T i ∩ T j).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      calc
        (∑ x ∈ U,
            (if x ∈ T i then (1 : ℝ) else 0) *
            (if x ∈ T j then (1 : ℝ) else 0)) =
            ∑ x ∈ U, if x ∈ T i ∩ T j then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hxi : x ∈ T i <;> by_cases hxj : x ∈ T j <;>
            simp [Finset.mem_inter, hxi, hxj]
        _ = ((T i ∩ T j).card : ℝ) := by
          apply sum_membership_indicator
          intro x hx
          exact hTU i hi (Finset.mem_inter.mp hx).1

private theorem overlap_energy_lower {β : Type*} (U : Finset β)
    (r : β → ℝ) (s K R : ℝ) (hs : 0 < s) (hK : 0 < K)
    (hmass : (∑ x ∈ U, r x) = s ^ 2)
    (henergy : (∑ x ∈ U, r x ^ 2) = R)
    (hU : (U.card : ℝ) ≤ K * s) : s ^ 3 / K ≤ R := by
  have hR : 0 ≤ R := by
    rw [← henergy]
    exact Finset.sum_nonneg (fun x _ => sq_nonneg (r x))
  have hcs : (s ^ 2) ^ 2 ≤ (U.card : ℝ) * R := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq U (fun _ => (1 : ℝ)) r
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul,
      mul_one, hmass, henergy] using h
  have hscaled : (s ^ 2) ^ 2 ≤ (K * s) * R :=
    hcs.trans (mul_le_mul_of_nonneg_right hU hR)
  apply (div_le_iff₀ hK).2
  refine le_of_mul_le_mul_left (a := s) ?_ hs
  calc
    s * s ^ 3 = (s ^ 2) ^ 2 := by ring
    _ ≤ (K * s) * R := hscaled
    _ = s * (R * K) := by ring

private theorem popular_card_lower (I : Finset ι) (f : ι → ℝ)
    (n a : ℝ) (hn : 0 < n) (ha : 0 ≤ a)
    (hcard : (I.card : ℝ) = n)
    (hupper : ∀ i ∈ I, f i ≤ n)
    (hsum : 2 * n * a ≤ ∑ i ∈ I, f i) :
    a ≤ ((I.filter fun i => a ≤ f i).card : ℝ) := let _ := instDecidableEqι; by
  classical
  have hbound : (∑ i ∈ I, f i) ≤
      ((I.filter fun i => a ≤ f i).card : ℝ) * n + n * a := by
    calc
      (∑ i ∈ I, f i) ≤ ∑ i ∈ I, ((if a ≤ f i then n else 0) + a) := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases h : a ≤ f i
        · rw [ite_eq_left h]
          exact (hupper i hi).trans (le_add_of_nonneg_right ha)
        · rw [ite_eq_right h, zero_add]
          exact (lt_of_not_ge h).le
      _ = ((I.filter fun i => a ≤ f i).card : ℝ) * n + n * a := by
        simp only [Finset.sum_add_distrib, ← Finset.sum_filter,
          Finset.sum_const, nsmul_eq_mul, hcard]
  refine le_of_mul_le_mul_left (a := n) ?_ hn
  nlinarith only [hsum, hbound]

theorem exists_popular_intersections
    (I : Finset ι) (T : ι → Finset α) (U : Finset α) (s : ℕ) (K : ℝ)
    (hI : I.card = s) (hne : I.Nonempty)
    (hT : ∀ i ∈ I, (T i).card = s)
    (hTU : ∀ i ∈ I, T i ⊆ U)
    (hU : (U.card : ℝ) ≤ K * s) (hK : 2 ≤ K) :
    ∃ b ∈ I, ∃ A : Finset ι, A ⊆ I ∧ (s : ℝ) / (2 * K) ≤ A.card ∧
      ∀ a ∈ A, (s : ℝ) / (2 * K) ≤ (T a ∩ T b).card := by
  classical
  have hsNat : 0 < s := by simpa only [hI] using Finset.card_pos.mpr hne
  have hs : (0 : ℝ) < s := Nat.cast_pos.mpr hsNat
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_two hK
  let r (x : α) : ℝ := ∑ i ∈ I, if x ∈ T i then 1 else 0
  let R : ℝ := ∑ i ∈ I, ∑ j ∈ I, ((T i ∩ T j).card : ℝ)
  let row (b : ι) : ℝ := ∑ a ∈ I, ((T a ∩ T b).card : ℝ)
  have hmass : (∑ x ∈ U, r x) = (s : ℝ) ^ 2 := by
    calc
      (∑ x ∈ U, r x) = ∑ i ∈ I, ((T i).card : ℝ) :=
        sum_overlap_multiplicity I T U hTU
      _ = ∑ _i ∈ I, (s : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact congrArg (fun n : ℕ => (n : ℝ)) (hT i hi)
      _ = (s : ℝ) ^ 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul, hI, pow_two]
  have henergy : (∑ x ∈ U, r x ^ 2) = R :=
    sum_sq_overlap_multiplicity I T U hTU
  have hlower : (s : ℝ) ^ 3 / K ≤ R :=
    overlap_energy_lower U r s K R hs hKpos hmass henergy hU
  have hrows : (∑ b ∈ I, row b) = R := by
    dsimp only [row, R]
    exact Finset.sum_comm
  have hmean : (∑ _b ∈ I, (s : ℝ) ^ 2 / K) ≤ ∑ b ∈ I, row b := by
    calc
      (∑ _b ∈ I, (s : ℝ) ^ 2 / K) = (s : ℝ) ^ 3 / K := by
        rw [Finset.sum_const, nsmul_eq_mul, hI]
        ring
      _ ≤ R := hlower
      _ = ∑ b ∈ I, row b := hrows.symm
  obtain ⟨b, hb, hrow⟩ := Finset.exists_le_of_sum_le
    (s := I) (f := fun _ => (s : ℝ) ^ 2 / K) (g := row) hne hmean
  let A := I.filter (fun a => (s : ℝ) / (2 * K) ≤ (T a ∩ T b).card)
  refine ⟨b, hb, A, ?_, ?_, ?_⟩
  · intro a ha
    exact (Finset.mem_filter.mp ha).1
  · apply popular_card_lower I (fun a => ((T a ∩ T b).card : ℝ))
      (s : ℝ) ((s : ℝ) / (2 * K)) hs
    · exact div_nonneg hs.le (mul_nonneg zero_le_two hKpos.le)
    · exact congrArg (fun n : ℕ => (n : ℝ)) hI
    · intro a ha
      apply Nat.cast_le.mpr
      exact (Finset.card_le_card Finset.inter_subset_left).trans_eq (hT a ha)
    · calc
        2 * (s : ℝ) * ((s : ℝ) / (2 * K)) = (s : ℝ) ^ 2 / K := by
          field_simp [ne_of_gt hKpos]
        _ ≤ ∑ a ∈ I, ((T a ∩ T b).card : ℝ) := hrow
  · intro a ha
    exact (Finset.mem_filter.mp ha).2

end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_PopularScalars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Pointwise

namespace RyserCoveringCounterexample.Incidence

variable {F : Type*} [Field F] [DecidableEq F]

private theorem card_field_smul (c : F) (hc : c ≠ 0) (X : Finset F) :
    (c • X).card = X.card := by
  change (X.image (fun x : F => c * x)).card = X.card
  apply Finset.card_image_of_injective
  intro x y h
  exact mul_left_cancel₀ hc h

private theorem field_smul_smul (c d : F) (X : Finset F) :
    c • (d • X) = (c * d) • X := by
  change (X.image (fun x : F => d * x)).image (fun y : F => c * y) =
    X.image (fun x : F => (c * d) * x)
  rw [Finset.image_image]
  apply Finset.image_congr
  intro x hx
  exact (mul_assoc c d x).symm

private theorem field_one_smul (X : Finset F) : (1 : F) • X = X := by
  change X.image (fun x : F => 1 * x) = X
  simp only [one_mul, Finset.image_id']

private theorem field_smul_sub (c : F) (X Y : Finset F) :
    c • (X - Y) = c • X - c • Y := by
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_smul_finset.mp hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_sub.mp hw
    change c * (x - y) ∈ c • X - c • Y
    rw [mul_sub]
    exact Finset.sub_mem_sub (Finset.smul_mem_smul_finset hx)
      (Finset.smul_mem_smul_finset hy)
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_sub.mp hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_smul_finset.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_smul_finset.mp hy
    refine Finset.mem_smul_finset.mpr ⟨u - v, Finset.sub_mem_sub hu hv, ?_⟩
    change c * (u - v) = c * u - c * v
    exact mul_sub c u v

private theorem field_smul_inter (c : F) (hc : c ≠ 0) (X Y : Finset F) :
    c • (X ∩ Y) = c • X ∩ c • Y := by
  change (X ∩ Y).image (fun x : F => c * x) =
    X.image (fun x : F => c * x) ∩ Y.image (fun x : F => c * x)
  apply Finset.image_inter
  intro x y h
  exact mul_left_cancel₀ hc h

private theorem quotient_overlap_card (S : Finset F) (a b : F) (ha : a ≠ 0) :
    ((a⁻¹ • S) ∩ (b⁻¹ • S)).card = (S ∩ (b⁻¹ * a) • S).card := by
  calc
    ((a⁻¹ • S) ∩ (b⁻¹ • S)).card =
        (a • ((a⁻¹ • S) ∩ (b⁻¹ • S))).card :=
      (card_field_smul a ha _).symm
    _ = (S ∩ (b⁻¹ * a) • S).card := by
      rw [field_smul_inter a ha, field_smul_smul, field_smul_smul,
        mul_inv_cancel₀ ha, field_one_smul, mul_comm a b⁻¹]

private theorem popular_difference_bound (S : Finset F) (c : F) (hc : c ≠ 0)
    (K : ℝ) (hS : S.Nonempty) (hK : 0 < K)
    (hsub : ((S - S).card : ℝ) ≤ K * S.card)
    (hoverlap : (S.card : ℝ) / (2 * K) ≤ (S ∩ c • S).card) :
    ((S - c • S).card : ℝ) ≤ 2 * K ^ 3 * S.card := by
  let Z := S ∩ c • S
  have hspos : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have hleftNat : (S - Z).card ≤ (S - S).card :=
    Finset.card_le_card (Finset.sub_subset_sub (fun _ h => h) Finset.inter_subset_left)
  have hrightNat : (Z - c • S).card ≤ (c • S - c • S).card :=
    Finset.card_le_card (Finset.sub_subset_sub Finset.inter_subset_right (fun _ h => h))
  rw [← field_smul_sub c S S, card_field_smul c hc (S - S)] at hrightNat
  have hleft : ((S - Z).card : ℝ) ≤ K * S.card :=
    (show ((S - Z).card : ℝ) ≤ (S - S).card by exact_mod_cast hleftNat).trans hsub
  have hright : ((Z - c • S).card : ℝ) ≤ K * S.card :=
    (show ((Z - c • S).card : ℝ) ≤ (S - S).card by exact_mod_cast hrightNat).trans hsub
  have htriangle : ((S - c • S).card : ℝ) * Z.card ≤
      ((S - Z).card : ℝ) * (Z - c • S).card := by
    exact_mod_cast triangle_card_le S (c • S) Z
  have hproduct : ((S - c • S).card : ℝ) * Z.card ≤
      (K * S.card) * (K * S.card) :=
    htriangle.trans (mul_le_mul hleft hright (Nat.cast_nonneg _)
      (mul_nonneg hK.le (Nat.cast_nonneg _)))
  have hpopular : (S.card : ℝ) ≤ (Z.card : ℝ) * (2 * K) :=
    (div_le_iff₀ (by positivity : 0 < 2 * K)).mp hoverlap
  have hfinal : ((S - c • S).card : ℝ) * S.card ≤
      (2 * K ^ 3 * S.card) * S.card := calc
    ((S - c • S).card : ℝ) * S.card ≤
        ((S - c • S).card : ℝ) * ((Z.card : ℝ) * (2 * K)) :=
      mul_le_mul_of_nonneg_left hpopular (Nat.cast_nonneg _)
    _ = (2 * K) * (((S - c • S).card : ℝ) * Z.card) := by ring
    _ ≤ (2 * K) * ((K * S.card) * (K * S.card)) :=
      mul_le_mul_of_nonneg_left hproduct (by positivity)
    _ = (2 * K ^ 3 * S.card) * S.card := by ring
  exact le_of_mul_le_mul_right hfinal hspos

theorem exists_popular_scalars (S : Finset F) (K : ℝ) (hS : S.Nonempty)
    (hzero : (0 : F) ∉ S) (hK : 2 ≤ K)
    (hsub : ((S - S).card : ℝ) ≤ K * S.card)
    (hdiv : ((S / S).card : ℝ) ≤ K * S.card) :
    ∃ B E : Finset F, E ⊆ B ∧ B.card = S.card ∧
      (S.card : ℝ) / (2 * K) ≤ E.card ∧
      ((B - B).card : ℝ) ≤ K * B.card ∧
      ∀ e ∈ E, ((B - e • B).card : ℝ) ≤ 2 * K ^ 3 * B.card := by
  classical
  have hnonzero : ∀ a ∈ S, a ≠ (0 : F) := by
    rintro a ha rfl
    exact hzero ha
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hquotient : ∀ a ∈ S, a⁻¹ • S ⊆ S / S := by
    intro a ha z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_smul_finset.mp hz
    refine Finset.mem_div.mpr ⟨x, hx, a, ha, ?_⟩
    change x / a = a⁻¹ * x
    rw [div_eq_mul_inv, mul_comm]
  obtain ⟨b, hb, A, hAS, hAcard, hpopular⟩ :=
    exists_popular_intersections S (fun a : F => a⁻¹ • S) (S / S) S.card K
      rfl hS (fun a ha => card_field_smul a⁻¹ (inv_ne_zero (hnonzero a ha)) S)
      hquotient hdiv hK
  have hb0 : b ≠ 0 := hnonzero b hb
  have hBcard : (b⁻¹ • S).card = S.card :=
    card_field_smul b⁻¹ (inv_ne_zero hb0) S
  have hEcard : (b⁻¹ • A).card = A.card :=
    card_field_smul b⁻¹ (inv_ne_zero hb0) A
  refine ⟨b⁻¹ • S, b⁻¹ • A, Finset.smul_finset_subset_smul_finset hAS,
    hBcard, ?_, ?_, ?_⟩
  · simpa only [hEcard] using hAcard
  · rw [← field_smul_sub b⁻¹ S S,
      card_field_smul b⁻¹ (inv_ne_zero hb0) (S - S), hBcard]
    exact hsub
  · intro e he
    obtain ⟨a, ha, hae⟩ := Finset.mem_smul_finset.mp he
    change b⁻¹ * a = e at hae
    subst e
    have ha0 : a ≠ 0 := hnonzero a (hAS ha)
    have he0 : b⁻¹ * a ≠ 0 := mul_ne_zero (inv_ne_zero hb0) ha0
    have hoverlap : (S.card : ℝ) / (2 * K) ≤ (S ∩ (b⁻¹ * a) • S).card := by
      rw [← quotient_overlap_card S a b ha0]
      exact hpopular a ha
    have hbound := popular_difference_bound S (b⁻¹ * a) he0 K hS hKpos hsub hoverlap
    have hscale : b⁻¹ • S - (b⁻¹ * a) • (b⁻¹ • S) =
        b⁻¹ • (S - (b⁻¹ * a) • S) := by
      rw [field_smul_sub]
      congr 1
      rw [field_smul_smul, field_smul_smul, mul_comm (b⁻¹ * a) b⁻¹]
    rw [hscale, card_field_smul b⁻¹ (inv_ne_zero hb0) (S - (b⁻¹ * a) • S), hBcard]
    exact hbound

end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_RatioSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence
noncomputable section
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem card_le_card_ratioSet {E : Finset F} (hE : 2 ≤ E.card) :
    E.card ≤ (ratioSet E).card := by
  obtain ⟨x₀, hx₀, x₁, hx₁, hne⟩ := Finset.one_lt_card.mp hE
  have hden : x₁ - x₀ ≠ 0 := sub_ne_zero.mpr hne.symm
  apply Finset.card_le_card_of_injOn (fun x => (x - x₀) / (x₁ - x₀))
  · intro x hx
    exact mem_ratioSet.mpr ⟨x, hx, x₀, hx₀, x₁, hx₁, x₀, hx₀, hne.symm, rfl⟩
  · intro x hx y hy heq
    have hd : x - x₀ = y - x₀ := (div_left_inj' hden).mp heq
    calc
      x = (x - x₀) + x₀ := (sub_add_cancel x x₀).symm
      _ = (y - x₀) + x₀ := by rw [hd]
      _ = y := sub_add_cancel y x₀

end
end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_ScalarCollisionCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence

open scoped BigOperators

variable {F : Type*} [Field F] [instDecidableEqF : DecidableEq F]

theorem scalarCollision_iff_eq_div (x y x' y' : F) (hy : y ≠ y') (a : F) :
    x + a * y = x' + a * y' ↔ a = (x' - x) / (y - y') := let _ := instDecidableEqF; by
  have hlinear : x + a * y = x' + a * y' ↔ a * (y - y') = x' - x := by
    constructor
    · intro h
      calc
        a * (y - y') = (x + a * y) - (x' + a * y') + (x' - x) := by ring
        _ = x' - x := by rw [h]; ring
    · intro h
      calc
        x + a * y = (a * (y - y') - (x' - x)) + (x' + a * y') := by ring
        _ = x' + a * y' := by rw [h]; ring
  exact hlinear.trans (eq_div_iff (sub_ne_zero.mpr hy)).symm

variable [Fintype F]

private theorem sum_scalarCollision_indicator (x y x' y' : F) :
    (∑ a : F, if x + a * y = x' + a * y' then (1 : ℕ) else 0) +
        (if y = y' then 1 else 0) =
      (if x = x' ∧ y = y' then Fintype.card F else 0) + 1 := by
  by_cases hy : y = y'
  · subst y'
    by_cases hx : x = x'
    · subst x'
      simp
    · simp [hx]
  · simp_rw [scalarCollision_iff_eq_div x y x' y' hy]
    simp [hy]

theorem sum_scalarCollisionCount (E : Finset F) :
    (∑ a : F, scalarCollisionCount E a) + E.card ^ 3 =
      Fintype.card F * E.card ^ 2 + E.card ^ 4 := by
  let Q := (E.product E).product (E.product E)
  have hcount :
      (∑ a : F, scalarCollisionCount E a) =
        ∑ p ∈ Q, ∑ a : F,
          if p.1.1 + a * p.1.2 = p.2.1 + a * p.2.2 then (1 : ℕ) else 0 := by
    simp only [scalarCollisionCount, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hsecond :
      (∑ p ∈ Q, if p.1.2 = p.2.2 then (1 : ℕ) else 0) = E.card ^ 3 := by
    dsimp [Q]
    simp only [Finset.sum_product]
    calc
      (∑ x ∈ E, ∑ y ∈ E, ∑ x' ∈ E, ∑ y' ∈ E,
          if y = y' then (1 : ℕ) else 0) = ∑ x ∈ E, ∑ y ∈ E, E.card := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        simp [hy]
      _ = E.card ^ 3 := by simp; ring
  have hdiagonal :
      (∑ p ∈ Q, if p.1.1 = p.2.1 ∧ p.1.2 = p.2.2
        then Fintype.card F else 0) = Fintype.card F * E.card ^ 2 := by
    dsimp [Q]
    simp only [Finset.sum_product]
    calc
      (∑ x ∈ E, ∑ y ∈ E, ∑ x' ∈ E, ∑ y' ∈ E,
          if x = x' ∧ y = y' then Fintype.card F else 0) =
          ∑ x ∈ E, ∑ y ∈ E, Fintype.card F := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        calc
          (∑ x' ∈ E, ∑ y' ∈ E,
              if x = x' ∧ y = y' then Fintype.card F else 0) =
              ∑ x' ∈ E, if x = x' then Fintype.card F else 0 := by
            apply Finset.sum_congr rfl
            intro x' hx'
            by_cases hxx : x = x'
            · simp [hxx, hy]
            · simp [hxx]
          _ = Fintype.card F := by simp [hx]
      _ = Fintype.card F * E.card ^ 2 := by simp; ring
  have hquadruples : (∑ p ∈ Q, (1 : ℕ)) = E.card ^ 4 := by
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    dsimp [Q]
    rw [Finset.card_product, Finset.card_product]
    ring
  have hsum :
      (∑ p ∈ Q,
        ((∑ a : F, if p.1.1 + a * p.1.2 = p.2.1 + a * p.2.2
          then (1 : ℕ) else 0) + (if p.1.2 = p.2.2 then 1 else 0))) =
      ∑ p ∈ Q,
        ((if p.1.1 = p.2.1 ∧ p.1.2 = p.2.2 then Fintype.card F else 0) + 1) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact sum_scalarCollision_indicator p.1.1 p.1.2 p.2.1 p.2.2
  simp only [Finset.sum_add_distrib] at hsum
  rw [← hcount, hsecond, hdiagonal, hquadruples] at hsum
  exact hsum

end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_ScalarCollisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Pointwise

namespace RyserCoveringCounterexample.Incidence

section Fibers

variable {α β : Type*} [instDecidableEqα : DecidableEq α] [DecidableEq β]

theorem card_collisionPairs_eq_sum_sq (s : Finset α) (f : α → β) :
    ((s.product s).filter (fun p => f p.1 = f p.2)).card =
      ∑ b ∈ s.image f, (s.filter (fun a => f a = b)).card ^ 2 := let _ := instDecidableEqα; by
  classical
  let fibers (b : β) := s.filter (fun a => f a = b)
  have hdisj : (s.image f : Set β).PairwiseDisjoint
      (fun b => (fibers b).product (fibers b)) := by
    intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    intro p hp hpc
    have hpb : f p.1 = b :=
      (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
    have hpc' : f p.1 = c :=
      (Finset.mem_filter.mp (Finset.mem_product.mp hpc).1).2
    exact hbc (hpb.symm.trans hpc')
  have hpartition :
      (s.product s).filter (fun p => f p.1 = f p.2) =
        (s.image f).disjiUnion (fun b => (fibers b).product (fibers b)) hdisj := by
    ext p
    simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product,
      Finset.mem_disjiUnion, fibers]
    constructor
    · rintro ⟨⟨hp1, hp2⟩, hf⟩
      exact ⟨f p.1, Finset.mem_image_of_mem f hp1, ⟨⟨hp1, rfl⟩, ⟨hp2, hf.symm⟩⟩⟩
    · rintro ⟨b, hb, ⟨⟨hp1, hf1⟩, ⟨hp2, hf2⟩⟩⟩
      exact ⟨⟨hp1, hp2⟩, hf1.trans hf2.symm⟩
  rw [hpartition, Finset.card_disjiUnion]
  simp only [Finset.product_eq_sprod, Finset.card_product, fibers, pow_two]

theorem card_sq_le_card_image_mul_collisionPairs (s : Finset α) (f : α → β) :
    s.card ^ 2 ≤ (s.image f).card *
      ((s.product s).filter (fun p => f p.1 = f p.2)).card := by
  calc
    s.card ^ 2 = (∑ b ∈ s.image f, (s.filter (fun a => f a = b)).card) ^ 2 := by
      rw [← Finset.card_eq_sum_card_image f s]
    _ ≤ (s.image f).card *
        ∑ b ∈ s.image f, (s.filter (fun a => f a = b)).card ^ 2 := by
      simpa using Finset.sum_mul_sq_le_sq_mul_sq (R := ℕ) (s.image f)
        (fun _ => 1) (fun b => (s.filter (fun a => f a = b)).card)
    _ = _ := by rw [← card_collisionPairs_eq_sum_sq s f]

end Fibers

variable {F : Type*} [Field F] [DecidableEq F]

theorem image_scalar_add (E : Finset F) (c : F) :
    (E.product E).image (fun p : F × F => p.1 + c * p.2) = dilateSum E c := by
  ext z
  simp only [dilateSum, Finset.product_eq_sprod, Finset.mem_image, Finset.mem_product,
    Finset.mem_add]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, hxy⟩
    exact ⟨x, hx, c * y, ⟨y, hy, rfl⟩, hxy⟩
  · rintro ⟨x, hx, z, ⟨y, hy, rfl⟩, hxy⟩
    exact ⟨(x, y), ⟨hx, hy⟩, hxy⟩

theorem dilateSum_eq_add_smul (E : Finset F) (c : F) :
    dilateSum E c = E + c • E := rfl

theorem card_dilateSum_mul_scalarCollisionCount (E : Finset F) (c : F) :
    E.card ^ 4 ≤ (dilateSum E c).card * scalarCollisionCount E c := by
  have h := card_sq_le_card_image_mul_collisionPairs (E.product E)
    (fun p : F × F => p.1 + c * p.2)
  rw [image_scalar_add E c] at h
  simp only [Finset.product_eq_sprod, Finset.card_product] at h
  simpa only [scalarCollisionCount, Finset.product_eq_sprod, pow_two, pow_succ, pow_zero,
    mul_one, mul_assoc] using h

variable [Fintype F]

theorem card_field_lt_twice_of_dilateSum_card_le_real (E : Finset F) (U : ℝ)
    (hU0 : 0 ≤ U) (hU : ∀ c : F, ((dilateSum E c).card : ℝ) ≤ U)
    (hsmall : 2 * U < (E.card : ℝ) ^ 2) : (Fintype.card F : ℝ) < 2 * U := by
  have hcauchy (c : F) : (E.card : ℝ) ^ 4 ≤
      ((dilateSum E c).card : ℝ) * (scalarCollisionCount E c : ℝ) := by
    exact_mod_cast card_dilateSum_mul_scalarCollisionCount E c
  have hsum : (Fintype.card F : ℝ) * (E.card : ℝ) ^ 4 ≤
      U * ∑ c : F, (scalarCollisionCount E c : ℝ) := by
    calc
      _ = ∑ _c : F, (E.card : ℝ) ^ 4 := by simp
      _ ≤ ∑ c : F, U * (scalarCollisionCount E c : ℝ) := by
        apply Finset.sum_le_sum
        intro c hc
        exact (hcauchy c).trans
          (mul_le_mul_of_nonneg_right (hU c) (Nat.cast_nonneg _))
      _ = _ := (Finset.mul_sum _ _ _).symm
  have htotal : (∑ c : F, (scalarCollisionCount E c : ℝ)) + (E.card : ℝ) ^ 3 =
      (Fintype.card F : ℝ) * (E.card : ℝ) ^ 2 + (E.card : ℝ) ^ 4 := by
    exact_mod_cast sum_scalarCollisionCount E
  have htotal_le : (∑ c : F, (scalarCollisionCount E c : ℝ)) ≤
      (Fintype.card F : ℝ) * (E.card : ℝ) ^ 2 + (E.card : ℝ) ^ 4 := by
    have hcube : 0 ≤ (E.card : ℝ) ^ 3 := pow_nonneg (Nat.cast_nonneg _) _
    linarith
  have hupper := mul_le_mul_of_nonneg_left htotal_le hU0
  have hqpos : 0 < (Fintype.card F : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  have hEpos : 0 < (E.card : ℝ) ^ 2 :=
    lt_of_le_of_lt (mul_nonneg (by norm_num) hU0) hsmall
  by_contra hnot
  have hq : 2 * U ≤ (Fintype.card F : ℝ) := le_of_not_gt hnot
  have h₁ := mul_le_mul_of_nonneg_right hq (sq_nonneg (E.card : ℝ))
  have h₂ := mul_lt_mul_of_pos_right hsmall hqpos
  have hgap : U * (Fintype.card F : ℝ) + U * (E.card : ℝ) ^ 2 <
      (Fintype.card F : ℝ) * (E.card : ℝ) ^ 2 := by nlinarith
  have hstrict := mul_lt_mul_of_pos_right hgap hEpos
  nlinarith

end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_ScalarCoverGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence

open scoped Pointwise

variable {F : Type*} [Field F] [DecidableEq F]

private lemma scalar_cover_neg_mem_diff
    {B : Finset F} {x : F} (hx : x ∈ B - B) :
    -x ∈ B - B := by
  rcases Finset.mem_sub.mp hx with ⟨u, hu, v, hv, rfl⟩
  exact Finset.mem_sub.mpr ⟨v, hv, u, hu, by ring⟩

theorem scalar_cover_add_subset
    {B T U V : Finset F} {a b : F}
    (ha : a • B ⊆ T + (B - B))
    (hb : b • B ⊆ U + (B - B))
    (hH : (B - B) + (B - B) ⊆ V + (B - B)) :
    (a + b) • B ⊆ (T + U + V) + (B - B) := by
  intro z hz
  rcases Finset.mem_smul_finset.mp hz with ⟨x, hx, rfl⟩
  rcases Finset.mem_add.mp (ha (Finset.smul_mem_smul_finset hx)) with
    ⟨t, ht, h, hh, eth⟩
  rcases Finset.mem_add.mp (hb (Finset.smul_mem_smul_finset hx)) with
    ⟨u, hu, k, hk, euk⟩
  change t + h = a * x at eth
  change u + k = b * x at euk
  rcases Finset.mem_add.mp (hH (Finset.add_mem_add hh hk)) with
    ⟨v, hv, d, hd, evd⟩
  refine Finset.mem_add.mpr
    ⟨t + u + v, Finset.add_mem_add (Finset.add_mem_add ht hu) hv,
      d, hd, ?_⟩
  change t + u + v + d = (a + b) * x
  calc
    t + u + v + d = t + u + (v + d) := by ring
    _ = t + u + (h + k) := by rw [evd]
    _ = (t + h) + (u + k) := by ring
    _ = (a + b) * x := by rw [eth, euk]; ring

theorem scalar_cover_sub_subset
    {B T U V : Finset F} {a b : F}
    (ha : a • B ⊆ T + (B - B))
    (hb : b • B ⊆ U + (B - B))
    (hH : (B - B) + (B - B) ⊆ V + (B - B)) :
    (a - b) • B ⊆ (T - U + V) + (B - B) := by
  intro z hz
  rcases Finset.mem_smul_finset.mp hz with ⟨x, hx, rfl⟩
  rcases Finset.mem_add.mp (ha (Finset.smul_mem_smul_finset hx)) with
    ⟨t, ht, h, hh, eth⟩
  rcases Finset.mem_add.mp (hb (Finset.smul_mem_smul_finset hx)) with
    ⟨u, hu, k, hk, euk⟩
  change t + h = a * x at eth
  change u + k = b * x at euk
  rcases Finset.mem_add.mp
      (hH (Finset.add_mem_add hh (scalar_cover_neg_mem_diff hk))) with
    ⟨v, hv, d, hd, evd⟩
  refine Finset.mem_add.mpr
    ⟨t - u + v, Finset.add_mem_add (Finset.sub_mem_sub ht hu) hv,
      d, hd, ?_⟩
  change t - u + v + d = (a - b) * x
  calc
    t - u + v + d = t - u + (v + d) := by ring
    _ = t - u + (h + -k) := by rw [evd]
    _ = (t + h) - (u + k) := by ring
    _ = (a - b) * x := by rw [eth, euk]; ring

theorem scalar_cover_neg_subset
    {B T : Finset F} {a : F}
    (ha : a • B ⊆ T + (B - B)) :
    (-a) • B ⊆ (-T) + (B - B) := by
  intro z hz
  rcases Finset.mem_smul_finset.mp hz with ⟨x, hx, rfl⟩
  rcases Finset.mem_add.mp (ha (Finset.smul_mem_smul_finset hx)) with
    ⟨t, ht, h, hh, eth⟩
  change t + h = a * x at eth
  refine Finset.mem_add.mpr
    ⟨-t, Finset.neg_mem_neg ht,
      -h, scalar_cover_neg_mem_diff hh, ?_⟩
  change -t + -h = (-a) * x
  calc
    -t + -h = -(t + h) := by ring
    _ = -(a * x) := by rw [eth]
    _ = (-a) * x := by ring

theorem scalar_cover_mul_subset
    {B T U V : Finset F} {a b : F}
    (ha : a • B ⊆ T + (B - B))
    (hb : b • B ⊆ U + (B - B))
    (hH : (B - B) + (B - B) ⊆ V + (B - B)) :
    (a * b) • B ⊆ (a • U + T - T + V) + (B - B) := by
  intro z hz
  rcases Finset.mem_smul_finset.mp hz with ⟨x, hx, rfl⟩
  rcases Finset.mem_add.mp (hb (Finset.smul_mem_smul_finset hx)) with
    ⟨u, hu, h, hh, euh⟩
  rcases Finset.mem_sub.mp hh with ⟨y, hy, w, hw, rfl⟩
  change u + (y - w) = b * x at euh
  rcases Finset.mem_add.mp (ha (Finset.smul_mem_smul_finset hy)) with
    ⟨t₁, ht₁, h₁, hh₁, e₁⟩
  rcases Finset.mem_add.mp (ha (Finset.smul_mem_smul_finset hw)) with
    ⟨t₂, ht₂, h₂, hh₂, e₂⟩
  change t₁ + h₁ = a * y at e₁
  change t₂ + h₂ = a * w at e₂
  rcases Finset.mem_add.mp
      (hH (Finset.add_mem_add hh₁ (scalar_cover_neg_mem_diff hh₂))) with
    ⟨v, hv, d, hd, evd⟩
  have hau : a * u ∈ a • U :=
    Finset.mem_smul_finset.mpr ⟨u, hu, rfl⟩
  refine Finset.mem_add.mpr ⟨a * u + t₁ - t₂ + v, ?_, d, hd, ?_⟩
  · exact Finset.add_mem_add
      (Finset.sub_mem_sub (Finset.add_mem_add hau ht₁) ht₂) hv
  · change a * u + t₁ - t₂ + v + d = (a * b) * x
    calc
      a * u + t₁ - t₂ + v + d =
          a * u + (t₁ - t₂) + (v + d) := by ring
      _ = a * u + (t₁ - t₂) + (h₁ + -h₂) := by rw [evd]
      _ = a * u + ((t₁ + h₁) - (t₂ + h₂)) := by ring
      _ = a * u + (a * y - a * w) := by rw [e₁, e₂]
      _ = a * (u + (y - w)) := by ring
      _ = (a * b) * x := by rw [euh]; ring

theorem scalar_cover_inv_sub_identity
    (B : Finset F) {a : F} (ha : a ≠ 0) :
    (-a⁻¹) • (a • B - B) = a⁻¹ • B - B := by
  have hscalar (u v : F) :
      (-a⁻¹) • (a • u - v) = a⁻¹ • v - u := by
    change (-a⁻¹) * (a * u - v) = a⁻¹ * v - u
    calc
      (-a⁻¹) * (a * u - v) =
          a⁻¹ * v - (a⁻¹ * a) * u := by ring
      _ = a⁻¹ * v - u := by rw [inv_mul_cancel₀ ha, one_mul]
  ext z
  constructor
  · intro hz
    rcases Finset.mem_smul_finset.mp hz with ⟨w, hw, rfl⟩
    rcases Finset.mem_sub.mp hw with ⟨u, hu, v, hv, rfl⟩
    rcases Finset.mem_smul_finset.mp hu with ⟨x, hx, rfl⟩
    exact Finset.mem_sub.mpr
      ⟨a⁻¹ • v, Finset.mem_smul_finset.mpr ⟨v, hv, rfl⟩,
        x, hx, (hscalar x v).symm⟩
  · intro hz
    rcases Finset.mem_sub.mp hz with ⟨u, hu, v, hv, rfl⟩
    rcases Finset.mem_smul_finset.mp hu with ⟨x, hx, rfl⟩
    refine Finset.mem_smul_finset.mpr
      ⟨a • v - x, ?_, hscalar v x⟩
    exact Finset.mem_sub.mpr
      ⟨a • v, Finset.mem_smul_finset.mpr ⟨v, hv, rfl⟩,
        x, hx, rfl⟩

end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_ScalarCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Incidence

open scoped Pointwise

variable {F : Type*} [Field F] [DecidableEq F]

private theorem scalar_card_image_le (c : F) (T : Finset F) :
    (c • T).card ≤ T.card := by
  change (T.image (fun x : F => c * x)).card ≤ T.card
  exact Finset.card_image_le

private theorem scalar_card_image_eq (c : F) (hc : c ≠ 0) (T : Finset F) :
    (c • T).card = T.card := by
  change (T.image (fun x : F => c * x)).card = T.card
  apply Finset.card_image_of_injective
  intro x y h
  exact mul_left_cancel₀ hc h

private theorem scalar_zero_image (T : Finset F) (hT : T.Nonempty) :
    (0 : F) • T = (0 : Finset F) := by
  change T.image (fun x : F => 0 * x) = ({0} : Finset F)
  simpa only [zero_mul] using Finset.image_const hT (0 : F)

private theorem scalar_one_image (T : Finset F) : (1 : F) • T = T := by
  change T.image (fun x : F => 1 * x) = T
  simp only [one_mul, Finset.image_id']

private theorem scalar_card_add_le_bounds
    {T U : Finset F} {p q : ℝ}
    (hT : (T.card : ℝ) ≤ p) (hU : (U.card : ℝ) ≤ q) :
    ((T + U).card : ℝ) ≤ p * q := by
  have hcard : ((T + U).card : ℝ) ≤ (T.card : ℝ) * U.card := by
    exact_mod_cast (Finset.card_add_le (s := T) (t := U))
  exact hcard.trans (mul_le_mul hT hU (Nat.cast_nonneg _)
    ((Nat.cast_nonneg _).trans hT))

private theorem scalar_card_sub_le_bounds
    {T U : Finset F} {p q : ℝ}
    (hT : (T.card : ℝ) ≤ p) (hU : (U.card : ℝ) ≤ q) :
    ((T - U).card : ℝ) ≤ p * q := by
  have hcard : ((T - U).card : ℝ) ≤ (T.card : ℝ) * U.card := by
    exact_mod_cast (Finset.card_sub_le (s := T) (t := U))
  exact hcard.trans (mul_le_mul hT hU (Nat.cast_nonneg _)
    ((Nat.cast_nonneg _).trans hT))

variable {B E : Finset F} {K : ℝ} {c d : F} {a b : ℕ}

theorem scalarCovered_mono (hK : 1 ≤ K)
    (h : ScalarCovered B K c a) (hab : a ≤ b) :
    ScalarCovered B K c b := by
  rcases h with ⟨T, hT, hcover⟩
  exact ⟨T, hT.trans (pow_le_pow_right₀ hK hab), hcover⟩

theorem scalarCovered_of_sub_card (hB : B.Nonempty)
    (h : ((c • B - B).card : ℝ) ≤ K ^ a * B.card) :
    ScalarCovered B K c a := by
  obtain ⟨T, _, hT, hcover⟩ := covering_sub (c • B) B hB h
  exact ⟨T, hT, hcover⟩

theorem scalarCover_double_cover (hB : B.Nonempty)
    (hD : ((B - B).card : ℝ) ≤ K * B.card) :
    ∃ V : Finset F, (V.card : ℝ) ≤ K ^ 5 ∧
      (B - B) + (B - B) ⊆ V + (B - B) := by
  have heq : (B - B) + (B - B) - B =
      (2 : ℕ) • B - (3 : ℕ) • B := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul]
    simp only [two_nsmul, one_nsmul, sub_eq_add_neg, neg_add]
    ac_rfl
  have hsmall : (((B - B) + (B - B) - B).card : ℝ) ≤
      K ^ 5 * B.card := by
    rw [heq]
    simpa using multiple_sum_sub_card_le B hB hD 2 3
  obtain ⟨V, _, hV, hcover⟩ :=
    covering_sub ((B - B) + (B - B)) B hB hsmall
  exact ⟨V, hV, hcover⟩

private theorem scalarCover_difference_cost (hB : B.Nonempty)
    (hD : ((B - B).card : ℝ) ≤ K * B.card) :
    (((B - B) - B).card : ℝ) ≤ K ^ 3 * B.card := by
  simpa only [one_nsmul, two_nsmul, sub_eq_add_neg, neg_add, add_assoc]
    using multiple_sum_sub_card_le B hB hD 1 2

private theorem scalarCover_sum_cost (hB : B.Nonempty)
    (hD : ((B - B).card : ℝ) ≤ K * B.card) :
    ((B + (B - B)).card : ℝ) ≤ K ^ 3 * B.card := by
  simpa only [one_nsmul, two_nsmul, sub_eq_add_neg, add_assoc]
    using multiple_sum_sub_card_le B hB hD 2 1

theorem scalarCovered_seed (hB : B.Nonempty) (hK : 2 ≤ K)
    (hD : ((B - B).card : ℝ) ≤ K * B.card)
    (hEB : ∀ e ∈ E, ((B - e • B).card : ℝ) ≤ 2 * K ^ 3 * B.card)
    (hc : c ∈ E ∨ c = 0 ∨ c = 1) :
    ScalarCovered B K c 4 := by
  have hK0 : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 2).trans hK
  have hK1 : 1 ≤ K := one_le_two.trans hK
  rcases hc with hc | rfl | rfl
  · apply scalarCovered_of_sub_card hB
    have hswap : (c • B - B).card = (B - c • B).card := by
      simpa only [neg_sub] using Finset.card_neg (B - c • B)
    have hpow : 2 * K ^ 3 ≤ K ^ 4 := by
      calc
        2 * K ^ 3 ≤ K * K ^ 3 :=
          mul_le_mul_of_nonneg_right hK (pow_nonneg hK0 3)
        _ = K ^ 4 := by ring
    rw [hswap]
    exact (hEB c hc).trans
      (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _))
  · have hzero : ScalarCovered B K (0 : F) 0 := by
      apply scalarCovered_of_sub_card hB
      simp only [scalar_zero_image B hB, zero_sub, Finset.card_neg,
        pow_zero, one_mul, le_refl]
    exact scalarCovered_mono hK1 hzero (by decide)
  · have hone : ScalarCovered B K (1 : F) 1 := by
      apply scalarCovered_of_sub_card hB
      simpa only [scalar_one_image, pow_one] using hD
    exact scalarCovered_mono hK1 hone (by decide)

theorem scalarCovered_neg (h : ScalarCovered B K c a) :
    ScalarCovered B K (-c) a := by
  rcases h with ⟨T, hT, hcover⟩
  refine ⟨-T, ?_, scalar_cover_neg_subset hcover⟩
  simpa only [Finset.card_neg] using hT

theorem scalarCovered_add (hB : B.Nonempty) (hK : 2 ≤ K)
    (hD : ((B - B).card : ℝ) ≤ K * B.card)
    (hc : ScalarCovered B K c a) (hd : ScalarCovered B K d b) :
    ScalarCovered B K (c + d) (a + b + 5) := by
  let _ := hK
  rcases hc with ⟨T, hT, hTc⟩
  rcases hd with ⟨U, hU, hUd⟩
  obtain ⟨V, hV, hVcover⟩ := scalarCover_double_cover hB hD
  refine ⟨T + U + V, ?_, scalar_cover_add_subset hTc hUd hVcover⟩
  calc
    ((T + U + V).card : ℝ) ≤ (K ^ a * K ^ b) * K ^ 5 :=
      scalar_card_add_le_bounds (scalar_card_add_le_bounds hT hU) hV
    _ = K ^ (a + b + 5) := by simp only [pow_add]

theorem scalarCovered_sub (hB : B.Nonempty) (hK : 2 ≤ K)
    (hD : ((B - B).card : ℝ) ≤ K * B.card)
    (hc : ScalarCovered B K c a) (hd : ScalarCovered B K d b) :
    ScalarCovered B K (c - d) (a + b + 5) := by
  let _ := hK
  rcases hc with ⟨T, hT, hTc⟩
  rcases hd with ⟨U, hU, hUd⟩
  obtain ⟨V, hV, hVcover⟩ := scalarCover_double_cover hB hD
  refine ⟨T - U + V, ?_, scalar_cover_sub_subset hTc hUd hVcover⟩
  calc
    ((T - U + V).card : ℝ) ≤ (K ^ a * K ^ b) * K ^ 5 :=
      scalar_card_add_le_bounds (scalar_card_sub_le_bounds hT hU) hV
    _ = K ^ (a + b + 5) := by simp only [pow_add]

theorem scalarCovered_mul (hB : B.Nonempty) (hK : 2 ≤ K)
    (hD : ((B - B).card : ℝ) ≤ K * B.card)
    (hc : ScalarCovered B K c a) (hd : ScalarCovered B K d b) :
    ScalarCovered B K (c * d) (b + 2 * a + 5) := by
  let _ := hK
  rcases hc with ⟨T, hT, hTc⟩
  rcases hd with ⟨U, hU, hUd⟩
  obtain ⟨V, hV, hVcover⟩ := scalarCover_double_cover hB hD
  have hCU : ((c • U).card : ℝ) ≤ K ^ b :=
    (Nat.cast_le.mpr (scalar_card_image_le c U)).trans hU
  refine ⟨c • U + T - T + V, ?_,
    scalar_cover_mul_subset hTc hUd hVcover⟩
  calc
    ((c • U + T - T + V).card : ℝ) ≤
        ((K ^ b * K ^ a) * K ^ a) * K ^ 5 :=
      scalar_card_add_le_bounds
        (scalar_card_sub_le_bounds (scalar_card_add_le_bounds hCU hT) hT) hV
    _ = K ^ (b + 2 * a + 5) := by
      simp only [two_mul, pow_add]
      ring

theorem scalarCovered_card_sub (hB : B.Nonempty) (hK : 2 ≤ K)
    (hD : ((B - B).card : ℝ) ≤ K * B.card)
    (hc : ScalarCovered B K c a) :
    ((c • B - B).card : ℝ) ≤ K ^ (a + 3) * B.card := by
  let _ := hK
  rcases hc with ⟨T, hT, hcover⟩
  have hsub : c • B - B ⊆ T + ((B - B) - B) := by
    simpa only [add_sub_assoc] using Finset.sub_subset_sub_right hcover
  calc
    ((c • B - B).card : ℝ) ≤ ((T + ((B - B) - B)).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ K ^ a * (K ^ 3 * B.card) :=
      scalar_card_add_le_bounds hT (scalarCover_difference_cost hB hD)
    _ = K ^ (a + 3) * B.card := by rw [pow_add]; ring

theorem scalarCovered_inv (hB : B.Nonempty) (hK : 2 ≤ K)
    (hD : ((B - B).card : ℝ) ≤ K * B.card)
    (hc : ScalarCovered B K c a) (hc0 : c ≠ 0) :
    ScalarCovered B K c⁻¹ (a + 3) := by
  have hcard : (c⁻¹ • B - B).card = (c • B - B).card := by
    rw [← scalar_cover_inv_sub_identity B hc0]
    exact scalar_card_image_eq (-c⁻¹) (neg_ne_zero.mpr (inv_ne_zero hc0)) _
  apply scalarCovered_of_sub_card hB
  rw [hcard]
  exact scalarCovered_card_sub hB hK hD hc

theorem scalarCovered_card_add (hB : B.Nonempty) (hK : 2 ≤ K)
    (hD : ((B - B).card : ℝ) ≤ K * B.card)
    (hc : ScalarCovered B K c a) :
    ((B + c • B).card : ℝ) ≤ K ^ (a + 3) * B.card := by
  let _ := hK
  rcases hc with ⟨T, hT, hcover⟩
  have hsub : B + c • B ⊆ T + (B + (B - B)) := by
    calc
      B + c • B ⊆ B + (T + (B - B)) :=
        Finset.add_subset_add_left hcover
      _ = T + (B + (B - B)) := by ac_rfl
  calc
    ((B + c • B).card : ℝ) ≤ ((T + (B + (B - B))).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ K ^ a * (K ^ 3 * B.card) :=
      scalar_card_add_le_bounds hT (scalarCover_sum_cost hB hD)
    _ = K ^ (a + 3) * B.card := by rw [pow_add]; ring

end RyserCoveringCounterexample.Incidence

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_ScalarCoverExpressions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence

open scoped Pointwise

variable {F : Type*} [Field F] [instDecidableEqF : DecidableEq F]

theorem scalarCoverExponent_le_succ (m : ℕ) :
    scalarCoverExponent m ≤ scalarCoverExponent (m + 1) := by
  rw [scalarCoverExponent_succ]
  omega

theorem scalarCoverExponent_monotone :
    Monotone scalarCoverExponent :=
  monotone_nat_of_le_succ scalarCoverExponent_le_succ

private theorem scalarCoverExponent_inv_bound (m : ℕ) :
    scalarCoverExponent m + 3 ≤ scalarCoverExponent (m + 1) := by
  rw [scalarCoverExponent_succ]
  omega

private theorem scalarCoverExponent_add_bound (m n : ℕ) :
    scalarCoverExponent m + scalarCoverExponent n + 5 ≤
      scalarCoverExponent (m + n + 1) := by
  have hm := scalarCoverExponent_monotone
    (show m ≤ m + n by omega)
  have hn := scalarCoverExponent_monotone
    (show n ≤ m + n by omega)
  rw [scalarCoverExponent_succ]
  omega

private theorem scalarCoverExponent_mul_bound (m n : ℕ) :
    scalarCoverExponent n + 2 * scalarCoverExponent m + 5 ≤
      scalarCoverExponent (m + n + 1) := by
  have hm := scalarCoverExponent_monotone
    (show m ≤ m + n by omega)
  have hn := scalarCoverExponent_monotone
    (show n ≤ m + n by omega)
  rw [scalarCoverExponent_succ]
  omega

variable {B E : Finset F} {K : ℝ}

theorem ScalarExpression.scalarCovered
    (hB : B.Nonempty) (hK : 2 ≤ K)
    (hD : ((B - B).card : ℝ) ≤ K * (B.card : ℝ))
    (hEB : ∀ e ∈ E,
      ((B - e • B).card : ℝ) ≤ 2 * K ^ 3 * (B.card : ℝ))
    {c : F} {n : ℕ} (h : ScalarExpression E c n) :
    ScalarCovered B K c (scalarCoverExponent n) := by
  have hK1 : 1 ≤ K := one_le_two.trans hK
  induction h with
  | seed hc =>
      exact scalarCovered_seed hB hK hD hEB hc
  | neg h ih =>
      exact scalarCovered_mono hK1 (scalarCovered_neg ih)
        (scalarCoverExponent_le_succ _)
  | add hc hd ihc ihd =>
      exact scalarCovered_mono hK1
        (scalarCovered_add hB hK hD ihc ihd)
        (scalarCoverExponent_add_bound _ _)
  | sub hc hd ihc ihd =>
      exact scalarCovered_mono hK1
        (scalarCovered_sub hB hK hD ihc ihd)
        (scalarCoverExponent_add_bound _ _)
  | mul hc hd ihc ihd =>
      exact scalarCovered_mono hK1
        (scalarCovered_mul hB hK hD ihc ihd)
        (scalarCoverExponent_mul_bound _ _)
  | inv h hc ih =>
      exact scalarCovered_mono hK1
        (scalarCovered_inv hB hK hD ih hc)
        (scalarCoverExponent_inv_bound _)

theorem ScalarExpression.scalarCovered_of_le
    (hB : B.Nonempty) (hK : 2 ≤ K)
    (hD : ((B - B).card : ℝ) ≤ K * (B.card : ℝ))
    (hEB : ∀ e ∈ E,
      ((B - e • B).card : ℝ) ≤ 2 * K ^ 3 * (B.card : ℝ))
    {c : F} {n m : ℕ}
    (h : ScalarExpression E c n) (hnm : n ≤ m) :
    ScalarCovered B K c (scalarCoverExponent m) :=
  scalarCovered_mono (one_le_two.trans hK)
    (ScalarExpression.scalarCovered hB hK hD hEB h)
    (scalarCoverExponent_monotone hnm)

theorem ScalarExpression.card_add_of_le
    (hB : B.Nonempty) (hK : 2 ≤ K)
    (hD : ((B - B).card : ℝ) ≤ K * (B.card : ℝ))
    (hEB : ∀ e ∈ E,
      ((B - e • B).card : ℝ) ≤ 2 * K ^ 3 * (B.card : ℝ))
    {c : F} {n m : ℕ}
    (h : ScalarExpression E c n) (hnm : n ≤ m) :
    ((B + c • B).card : ℝ) ≤
      K ^ (scalarCoverExponent m + 3) * (B.card : ℝ) :=
  scalarCovered_card_add hB hK hD
    (ScalarExpression.scalarCovered_of_le hB hK hD hEB h hnm)

theorem ScalarExpression.card_add_subset_of_le
    (hB : B.Nonempty) (hK : 2 ≤ K)
    (hD : ((B - B).card : ℝ) ≤ K * (B.card : ℝ))
    (hCost : ∀ e ∈ E,
      ((B - e • B).card : ℝ) ≤ 2 * K ^ 3 * (B.card : ℝ))
    (hEB : E ⊆ B)
    {c : F} {n m : ℕ}
    (h : ScalarExpression E c n) (hnm : n ≤ m) :
    ((E + c • E).card : ℝ) ≤
      K ^ (scalarCoverExponent m + 3) * (B.card : ℝ) := by
  have hsub : E + c • E ⊆ B + c • B :=
    Finset.add_subset_add hEB
      (Finset.smul_finset_subset_smul_finset hEB)
  have hcard :
      ((E + c • E).card : ℝ) ≤ ((B + c • B).card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card hsub)
  exact hcard.trans
    (ScalarExpression.card_add_of_le hB hK hD hCost h hnm)

theorem scalarExpression_ratio
    {x x' y y' : F}
    (hx : x ∈ E) (hx' : x' ∈ E)
    (hy : y ∈ E) (hy' : y' ∈ E)
    (hyy' : y ≠ y') :
    ScalarExpression E ((x - x') / (y - y')) 4 := let _ := instDecidableEqF; by
  have hnum : ScalarExpression E (x - x') 1 :=
    ScalarExpression.sub
      (ScalarExpression.seed (Or.inl hx))
      (ScalarExpression.seed (Or.inl hx'))
  have hden : ScalarExpression E (y - y') 1 :=
    ScalarExpression.sub
      (ScalarExpression.seed (Or.inl hy))
      (ScalarExpression.seed (Or.inl hy'))
  have hinv : ScalarExpression E (y - y')⁻¹ 2 :=
    ScalarExpression.inv hden (sub_ne_zero.mpr hyy')
  simpa only [div_eq_mul_inv] using
    (ScalarExpression.mul hnum hinv)

end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_NoApproximateSubfield
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence

noncomputable section
open scoped Pointwise

variable {F : Type*} [Field F] [DecidableEq F]

theorem scalarExpression_of_mem_ratioSet {E : Finset F} {c : F}
    (hc : c ∈ ratioSet E) : ScalarExpression E c 4 := by
  obtain ⟨x, hx, x', hx', y, hy, y', hy', hyy', hquot⟩ := mem_ratioSet.mp hc
  rw [← hquot]
  exact scalarExpression_ratio hx hx' hy hy' hyy'

theorem no_approximate_subfield_finite [Fintype F]
    (S : Finset F) (K : ℝ) (hzero : (0 : F) ∉ S) (hK : 2 ≤ K)
    (hsub : ((S - S).card : ℝ) ≤ K * (S.card : ℝ))
    (hdiv : ((S / S).card : ℝ) ≤ K * (S.card : ℝ))
    (properSubfields : ∀ L : Subfield F, L ≠ ⊤ →
      (Nat.card L : ℝ) ^ 3 ≤ (Fintype.card F : ℝ))
    (hlarge : 4 * K ^ 127942 < (S.card : ℝ)) :
    (S.card : ℝ) ^ 3 ≤ 8 * K ^ 3 * (Fintype.card F : ℝ) ∨
      (Fintype.card F : ℝ) < 2 * K ^ 527 * (S.card : ℝ) := by
  classical
  by_cases hfirst : (S.card : ℝ) ^ 3 ≤ 8 * K ^ 3 * (Fintype.card F : ℝ)
  · exact Or.inl hfirst
  apply Or.inr
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hspos : 0 < (S.card : ℝ) :=
    lt_trans (mul_pos (by norm_num) (pow_pos hKpos _)) hlarge
  have hS : S.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hspos)
  obtain ⟨B, E, hEB, hBcard, hpopular, hD, hCost⟩ :=
    exists_popular_scalars S K hS hzero hK hsub hdiv
  have hB : B.Nonempty := by
    apply Finset.card_pos.mp
    rw [hBcard]
    exact hS.card_pos
  have hnum := noapprox_threshold_numerics K (S.card : ℝ) (E.card : ℝ)
    hK hpopular hlarge
  have hE : 2 ≤ E.card := by exact_mod_cast hnum.2.1.le
  have hC4 : scalarCoverExponent 4 + 3 = 527 := by decide
  have hC9 : scalarCoverExponent 9 + 3 = 127940 := by decide
  have hratio (r : F) (hr : r ∈ ratioSet E) : ScalarExpression E r 4 :=
    scalarExpression_of_mem_ratioSet hr
  have hsmall (c : F) (hc : ScalarExpression E c 9) :
      (dilateSum E c).card < E.card ^ 2 := by
    have hgrowth := ScalarExpression.card_add_subset_of_le hB hK hD hCost hEB
      hc (show 9 ≤ 9 from le_rfl)
    have hbound : ((dilateSum E c).card : ℝ) ≤ K ^ 127940 * (S.card : ℝ) := by
      rw [dilateSum_eq_add_smul]
      simpa only [hC9, hBcard] using hgrowth
    exact_mod_cast hbound.trans_lt hnum.2.2.1
  have hadd : ∀ r ∈ ratioSet E, ∀ r' ∈ ratioSet E,
      (dilateSum E (r + r')).card < E.card ^ 2 := by
    intro r hr r' hr'
    exact hsmall (r + r') (ScalarExpression.add (hratio r hr) (hratio r' hr'))
  have hmul : ∀ r ∈ ratioSet E, ∀ r' ∈ ratioSet E,
      (dilateSum E (r * r')).card < E.card ^ 2 := by
    intro r hr r' hr'
    exact hsmall (r * r') (ScalarExpression.mul (hratio r hr) (hratio r' hr'))
  let L : Subfield F := ratioSubfield E hE hadd hmul
  have hLcard : Nat.card L = (ratioSet E).card := by
    change Nat.card (ratioSet E) = (ratioSet E).card
    exact Nat.card_eq_finsetCard _
  have hEcard : (E.card : ℝ) ≤ (Nat.card L : ℝ) := by
    rw [hLcard]
    exact_mod_cast card_le_card_ratioSet hE
  have hfieldlt : (Fintype.card F : ℝ) < (E.card : ℝ) ^ 3 :=
    cube_lt_of_popular_lower K (S.card : ℝ) (E.card : ℝ) (Fintype.card F : ℝ)
      hKpos hspos.le hpopular (lt_of_not_ge hfirst)
  have hLtop : L = ⊤ := by
    by_contra hproper
    have hcube : (E.card : ℝ) ^ 3 ≤ (Nat.card L : ℝ) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hEcard 3
    exact (not_lt_of_ge (hcube.trans (properSubfields L hproper))) hfieldlt
  have hallratio (c : F) : c ∈ ratioSet E := by
    have hc : c ∈ L := by rw [hLtop]; exact Subfield.mem_top _
    exact hc
  have hallgrowth (c : F) :
      ((dilateSum E c).card : ℝ) ≤ K ^ 527 * (S.card : ℝ) := by
    have hgrowth := ScalarExpression.card_add_subset_of_le hB hK hD hCost hEB
      (hratio c (hallratio c)) (show 4 ≤ 4 from le_rfl)
    rw [dilateSum_eq_add_smul]
    simpa only [hC4, hBcard] using hgrowth
  have hcollision := card_field_lt_twice_of_dilateSum_card_le_real E
    (K ^ 527 * (S.card : ℝ))
    (mul_nonneg (pow_nonneg hKpos.le _) (Nat.cast_nonneg _))
    hallgrowth hnum.2.2.2
  simpa only [mul_assoc] using hcollision

end
end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_ExtractedContradiction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence

theorem extracted_card_constraints
    (q r V K s : ℝ) (hq : 0 < q) (hr : 0 < r) (hrq : r ^ 2 = q)
    (hV : 0 < V) (hK : 0 ≤ K)
    (hlo : 3 * r / (8 * V ^ 2) ≤ s) (hhi : s ≤ V * r)
    (hfirst : 32 * V ^ 2 * K ^ 127942 < 3 * r)
    (hsecond : 4096 * V ^ 6 * K ^ 3 < 27 * r)
    (hthird : 2 * K ^ 527 * V ≤ r) :
    4 * K ^ 127942 < s ∧ 8 * K ^ 3 * q < s ^ 3 ∧
      2 * K ^ 527 * s ≤ q := by
  let _ := hq
  have hden : 0 < 8 * V ^ 2 := by positivity
  have hlo' : 3 * r ≤ s * (8 * V ^ 2) := (div_le_iff₀ hden).mp hlo
  have hlarge : 4 * K ^ 127942 < s := by
    apply lt_of_lt_of_le _ hlo
    apply (lt_div_iff₀ hden).mpr
    have heq : 4 * K ^ 127942 * (8 * V ^ 2) = 32 * V ^ 2 * K ^ 127942 := by ring
    rw [heq]
    exact hfirst
  have hfactor : 0 < 512 * V ^ 6 := by positivity
  have hcubic : 8 * K ^ 3 * q < s ^ 3 := by
    apply (mul_lt_mul_iff_left₀ hfactor).mp
    calc
      (8 * K ^ 3 * q) * (512 * V ^ 6) < 27 * r ^ 3 := by
        rw [← hrq]
        calc
          (8 * K ^ 3 * r ^ 2) * (512 * V ^ 6) =
              (4096 * V ^ 6 * K ^ 3) * r ^ 2 := by ring
          _ < (27 * r) * r ^ 2 := mul_lt_mul_of_pos_right hsecond (pow_pos hr 2)
          _ = 27 * r ^ 3 := by ring
      _ = (3 * r) ^ 3 := by ring
      _ ≤ (s * (8 * V ^ 2)) ^ 3 :=
        pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 3 * r) hlo' 3
      _ = s ^ 3 * (512 * V ^ 6) := by ring
  refine ⟨hlarge, hcubic, ?_⟩
  calc
    2 * K ^ 527 * s ≤ 2 * K ^ 527 * (V * r) :=
      mul_le_mul_of_nonneg_left hhi (by positivity)
    _ = (2 * K ^ 527 * V) * r := by ring
    _ ≤ r * r := mul_le_mul_of_nonneg_right hthird hr.le
    _ = q := by rw [← pow_two, hrq]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
open scoped Pointwise

theorem extracted_set_contradiction
    (S : Finset F) (r V K : ℝ) (hzero : (0 : F) ∉ S)
    (hK : 2 ≤ K) (hV : 0 < V) (hr : 0 < r)
    (hrq : r ^ 2 = (Fintype.card F : ℝ))
    (hsub : ((S - S).card : ℝ) ≤ K * S.card)
    (hdiv : ((S / S).card : ℝ) ≤ K * S.card)
    (hproper : ∀ L : Subfield F, L ≠ ⊤ →
      (Nat.card L : ℝ) ^ 3 ≤ (Fintype.card F : ℝ))
    (hlo : 3 * r / (8 * V ^ 2) ≤ (S.card : ℝ))
    (hhi : (S.card : ℝ) ≤ V * r)
    (hfirst : 32 * V ^ 2 * K ^ 127942 < 3 * r)
    (hsecond : 4096 * V ^ 6 * K ^ 3 < 27 * r)
    (hthird : 2 * K ^ 527 * V ≤ r) : False := by
  have hq : (0 : ℝ) < Fintype.card F := Nat.cast_pos.mpr Fintype.card_pos
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  obtain ⟨hlarge, hcubic, hupper⟩ := extracted_card_constraints
    (Fintype.card F) r V K S.card hq hr hrq hV hK0 hlo hhi hfirst hsecond hthird
  rcases no_approximate_subfield_finite S K hzero hK hsub hdiv hproper hlarge with h | h
  · exact (not_le_of_gt hcubic) h
  · exact (not_lt_of_ge hupper) h

end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_FourAnchorsCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace RyserCoveringCounterexample.Incidence
attribute [local instance] Classical.propDecidable

variable {Pt Ln : Type*} [DecidableEq Pt] [instDecidableEqLn : DecidableEq Ln]

theorem card_orderedTriples (P : Finset Pt) :
    (orderedTriples P).card = P.card * (P.card - 1) * (P.card - 2) := by
  simp only [orderedTriples, Finset.card_sigma]
  calc
    (∑ a ∈ P, ∑ b ∈ P.erase a, ((P.erase a).erase b).card) =
        ∑ a ∈ P, ((P.card - 1) * (P.card - 2)) := by
      apply Finset.sum_congr rfl
      intro a ha
      have hca := Finset.card_erase_of_mem ha
      calc
        (∑ b ∈ P.erase a, ((P.erase a).erase b).card) =
            ∑ b ∈ P.erase a, (P.card - 2) := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.card_erase_of_mem hb, hca]
          omega
        _ = (P.card - 1) * (P.card - 2) := by
          simp only [Finset.sum_const, Nat.nsmul_eq_mul, hca]
    _ = P.card * (P.card - 1) * (P.card - 2) := by
      simp only [Finset.sum_const, Nat.nsmul_eq_mul]
      ring

theorem card_orderedTriples_real (P : Finset Pt) :
    ((orderedTriples P).card : ℝ) =
      (P.card : ℝ) * ((P.card : ℝ) - 1) * ((P.card : ℝ) - 2) := by
  rw [card_orderedTriples]
  by_cases h : 2 ≤ P.card
  · rw [Nat.cast_mul, Nat.cast_mul,
      Nat.cast_sub (by omega : 1 ≤ P.card), Nat.cast_sub h]
    norm_num
  · have hcases : P.card = 0 ∨ P.card = 1 := by omega
    rcases hcases with h | h <;> simp [h]

theorem two_ninths_cube_le_orderedTriples (P : Finset Pt) (h : 3 ≤ P.card) :
    (2 / 9 : ℝ) * (P.card : ℝ) ^ 3 ≤ ((orderedTriples P).card : ℝ) := by
  rw [card_orderedTriples_real]
  have ht : (3 : ℝ) ≤ P.card := by exact_mod_cast h
  have hprod := mul_nonneg
    (mul_nonneg (sub_nonneg.mpr ht) (by linarith : 0 ≤ 7 * (P.card : ℝ) - 6))
    (Nat.cast_nonneg (α := ℝ) P.card)
  nlinarith

theorem sum_cube_card_sq (I : Finset Ln) (f : Ln → ℝ)
    (hf : ∀ i ∈ I, 0 ≤ f i) :
    (∑ i ∈ I, f i) ^ 3 ≤ (I.card : ℝ) ^ 2 * ∑ i ∈ I, f i ^ 3 := let _ := instDecidableEqLn; by
  by_cases hI : I.Nonempty
  · let m : ℝ := I.card
    let a : ℝ := (∑ i ∈ I, f i) / m
    have hm : 0 < m := by
      dsimp [m]
      exact_mod_cast hI.card_pos
    have ha : 0 ≤ a := div_nonneg (Finset.sum_nonneg hf) hm.le
    have heq : m * a = ∑ i ∈ I, f i := by
      dsimp [a]
      exact mul_div_cancel₀ _ (ne_of_gt hm)
    have hnon : 0 ≤ ∑ i ∈ I, (f i - a) ^ 2 * (f i + 2 * a) :=
      Finset.sum_nonneg fun i hi => mul_nonneg (sq_nonneg _) (by linarith [hf i hi])
    have hexpand : (∑ i ∈ I, (f i - a) ^ 2 * (f i + 2 * a)) =
        (∑ i ∈ I, f i ^ 3) - 3 * a ^ 2 * (∑ i ∈ I, f i) + 2 * m * a ^ 3 := by
      calc
        _ = ∑ i ∈ I, (f i ^ 3 - 3 * a ^ 2 * f i + 2 * a ^ 3) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
          dsimp [m]
          ring
    rw [hexpand] at hnon
    have hc : m * a ^ 3 ≤ ∑ i ∈ I, f i ^ 3 := by
      nlinarith [congrArg (fun z : ℝ => z * a ^ 2) heq]
    have hmul := mul_le_mul_of_nonneg_left hc (sq_nonneg m)
    have hcube := congrArg (fun z : ℝ => z ^ 3) heq
    change (∑ i ∈ I, f i) ^ 3 ≤ m ^ 2 * ∑ i ∈ I, f i ^ 3
    nlinarith
  · have : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    simp [this]

theorem card_anchorConfigurations (R : Pt → Ln → Prop) (P : Finset Pt)
    (L : Finset Ln) :
    (anchorConfigurations R P L).card =
      ∑ l ∈ L, (orderedTriples (P.filter fun p => R p l)).card *
        (P.filter fun p => ¬ R p l).card := let _ := instDecidableEqLn; by
  classical
  simp only [anchorConfigurations, Finset.card_sigma, Finset.card_product]

theorem sum_card_anchorConfigurations_neighbors (R : Pt → Ln → Prop)
    (P : Finset Pt) (L : Finset Ln) :
    (∑ x ∈ P, (anchorConfigurations R (joinedNeighbors R P L x) L).card) =
      ∑ c ∈ anchorConfigurations R P L, (anchorWitnesses R P L c).card := by
  classical
  have heq (x : Pt) : anchorConfigurations R (joinedNeighbors R P L x) L =
      (anchorConfigurations R P L).filter (fun c =>
        c.2.1.1 ∈ joinedNeighbors R P L x ∧
        c.2.1.2.1 ∈ joinedNeighbors R P L x ∧
        c.2.1.2.2 ∈ joinedNeighbors R P L x ∧
        c.2.2 ∈ joinedNeighbors R P L x) := by
    ext c
    have hsub : joinedNeighbors R P L x ⊆ P := Finset.filter_subset _ _
    simp only [mem_anchorConfigurations, Finset.mem_filter]
    constructor
    · rintro ⟨hl, h1, h2, h3, h4, hrest⟩
      exact ⟨⟨hl, hsub h1, hsub h2, hsub h3, hsub h4, hrest⟩, h1, h2, h3, h4⟩
    · rintro ⟨⟨hl, _, _, _, _, hrest⟩, h1, h2, h3, h4⟩
      exact ⟨hl, h1, h2, h3, h4, hrest⟩
  simp_rw [heq, anchorWitnesses, Finset.card_filter]
  exact Finset.sum_comm

end RyserCoveringCounterexample.Incidence

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_FourAnchorsGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace RyserCoveringCounterexample.Incidence

attribute [local instance] Classical.propDecidable

variable {Pt Ln : Type*} [DecidableEq Pt] [instDecidableEqLn : DecidableEq Ln]

theorem joinedNeighbors_card_lower (R : Pt → Ln → Prop)
    (hunique : ∀ {x y : Pt} {l m : Ln}, x ≠ y →
      R x l → R y l → R x m → R y m → l = m)
    (P : Finset Pt) (L : Finset Ln) (x : Pt) (hx : x ∈ P)
    {d : ℝ} (hd : 1 ≤ d)
    (hpoint : d ≤ ((L.filter fun l => R x l).card : ℝ))
    (hlines : ∀ l ∈ L, d ≤ ((P.filter fun p => R p l).card : ℝ)) :
    d * (d - 1) ≤ ((joinedNeighbors R P L x).card : ℝ) := let _ := instDecidableEqLn; by
  classical
  let I := L.filter fun l => R x l
  let S := I.sigma fun l => (P.filter fun p => R p l).erase x
  have hcard : S.card ≤ (joinedNeighbors R P L x).card := by
    apply Finset.card_le_card_of_injOn (fun w : Σ _ : Ln, Pt => w.2)
    · intro w hw
      obtain ⟨hl, hp⟩ := Finset.mem_sigma.mp hw
      obtain ⟨hyx, hy⟩ := Finset.mem_erase.mp hp
      obtain ⟨hyP, hyl⟩ := Finset.mem_filter.mp hy
      obtain ⟨hlL, hxl⟩ := Finset.mem_filter.mp hl
      exact Finset.mem_filter.mpr ⟨hyP, Ne.symm hyx, w.1, hlL, hxl, hyl⟩
    · intro w hw v hv heq
      obtain ⟨hl, hp⟩ := Finset.mem_sigma.mp hw
      obtain ⟨hm, hq⟩ := Finset.mem_sigma.mp hv
      obtain ⟨hyx, hy⟩ := Finset.mem_erase.mp hp
      obtain ⟨_, hz⟩ := Finset.mem_erase.mp hq
      have hlm : w.1 = v.1 := hunique (Ne.symm hyx)
        (Finset.mem_filter.mp hl).2 (Finset.mem_filter.mp hy).2
        (Finset.mem_filter.mp hm).2 (by simpa only [heq] using (Finset.mem_filter.mp hz).2)
      rcases w with ⟨l, y⟩
      rcases v with ⟨m, z⟩
      dsimp at hlm heq
      subst m
      subst z
      rfl
  have hS : (S.card : ℝ) =
      ∑ l ∈ I, (((P.filter fun p => R p l).card : ℝ) - 1) := by
    dsimp [S]
    rw [Finset.card_sigma, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro l hl
    have hxtrace : x ∈ P.filter fun p => R p l :=
      Finset.mem_filter.mpr ⟨hx, (Finset.mem_filter.mp hl).2⟩
    rw [Finset.card_erase_of_mem hxtrace, Nat.cast_sub
      (Finset.one_le_card.mpr ⟨x, hxtrace⟩)]
    norm_num
  calc
    d * (d - 1) ≤ (I.card : ℝ) * (d - 1) :=
      mul_le_mul_of_nonneg_right hpoint (by linarith)
    _ = ∑ _l ∈ I, (d - 1) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ l ∈ I, (((P.filter fun p => R p l).card : ℝ) - 1) := by
      apply Finset.sum_le_sum
      intro l hl
      exact sub_le_sub_right (hlines l (Finset.mem_filter.mp hl).1) 1
    _ = (S.card : ℝ) := hS.symm
    _ ≤ ((joinedNeighbors R P L x).card : ℝ) := by exact_mod_cast hcard

theorem projective_joinedNeighbors_card_lower {F : Type*} [Field F] [DecidableEq F]
    (P : Finset (ProjectivePoint F)) (L : Finset (ProjectiveLine F))
    (x : ProjectivePoint F) (hx : x ∈ P)
    {d : ℝ} (hd : 1 ≤ d)
    (hpoint : d ≤ ((L.filter fun l => ProjectiveIncidence x l).card : ℝ))
    (hlines : ∀ l ∈ L,
      d ≤ ((P.filter fun p => ProjectiveIncidence p l).card : ℝ)) :
    d * (d - 1) ≤ ((joinedNeighbors ProjectiveIncidence P L x).card : ℝ) :=
  joinedNeighbors_card_lower ProjectiveIncidence
    (fun hxy hxl hyl hxm hym => eq_projectiveLine_of_common_incidence hxy hxl hyl hxm hym)
    P L x hx hd
    (by convert hpoint using 1; congr)
    (by
      intro l hl
      convert hlines l hl using 1; congr)

end RyserCoveringCounterexample.Incidence

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_FourAnchorsLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace RyserCoveringCounterexample.Incidence

attribute [local instance] Classical.propDecidable

variable {Pt Ln : Type*} [instDecidableEqPt : DecidableEq Pt] [instDecidableEqLn : DecidableEq Ln]

theorem sum_trace_card_eq_sum_selected_degree (R : Pt → Ln → Prop)
    (N : Finset Pt) (L : Finset Ln) :
    (∑ l ∈ L, ((N.filter fun p => R p l).card : ℝ)) =
      ∑ p ∈ N, ((L.filter fun l => R p l).card : ℝ) := let _ := instDecidableEqPt; let _ := instDecidableEqLn; by
  have h : (∑ l ∈ L, (N.filter fun p => R p l).card) =
      ∑ p ∈ N, (L.filter fun l => R p l).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  exact_mod_cast h

theorem sum_trace_card_ge_min_degree (R : Pt → Ln → Prop)
    (N : Finset Pt) (L : Finset Ln) (d : ℝ)
    (hdegree : ∀ p ∈ N, d ≤ ((L.filter fun l => R p l).card : ℝ)) :
    d * (N.card : ℝ) ≤ ∑ l ∈ L, ((N.filter fun p => R p l).card : ℝ) := by
  rw [sum_trace_card_eq_sum_selected_degree]
  calc
    d * (N.card : ℝ) = ∑ _p ∈ N, d := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := Finset.sum_le_sum hdegree

theorem sum_high_trace_ge_min_degree (R : Pt → Ln → Prop)
    (N : Finset Pt) (L : Finset Ln) (d : ℝ)
    (hdegree : ∀ p ∈ N, d ≤ ((L.filter fun l => R p l).card : ℝ)) :
    d * (N.card : ℝ) - 2 * (L.card : ℝ) ≤
      ∑ l ∈ L, if 3 ≤ (N.filter fun p => R p l).card then
        ((N.filter fun p => R p l).card : ℝ) else 0 := by
  let f : Ln → ℝ := fun l =>
    if 3 ≤ (N.filter fun p => R p l).card then
      ((N.filter fun p => R p l).card : ℝ) else 0
  have hpoint (l : Ln) : ((N.filter fun p => R p l).card : ℝ) ≤ f l + 2 := by
    dsimp only [f]
    split_ifs with h
    · linarith
    · have hsmall : (N.filter fun p => R p l).card ≤ 2 := by omega
      have hsmall' : ((N.filter fun p => R p l).card : ℝ) ≤ 2 := by
        exact_mod_cast hsmall
      simpa only [zero_add] using hsmall'
  have hsum := (sum_trace_card_ge_min_degree R N L d hdegree).trans
    (Finset.sum_le_sum fun l _ => hpoint l)
  have hadd : (∑ l ∈ L, (f l + 2)) =
      (∑ l ∈ L, f l) + 2 * (L.card : ℝ) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hadd] at hsum
  change d * (N.card : ℝ) - 2 * (L.card : ℝ) ≤ ∑ l ∈ L, f l
  linarith

theorem triple_sum_lower_bound (R : Pt → Ln → Prop)
    (N : Finset Pt) (L : Finset Ln) (d : ℝ)
    (hdegree : ∀ p ∈ N, d ≤ ((L.filter fun l => R p l).card : ℝ))
    (hbase : 0 ≤ d * (N.card : ℝ) - 2 * (L.card : ℝ)) :
    (2 / 9 : ℝ) * (d * (N.card : ℝ) - 2 * (L.card : ℝ)) ^ 3 ≤
      (L.card : ℝ) ^ 2 *
        ∑ l ∈ L, ((orderedTriples (N.filter fun p => R p l)).card : ℝ) := by
  let f : Ln → ℝ := fun l =>
    if 3 ≤ (N.filter fun p => R p l).card then
      ((N.filter fun p => R p l).card : ℝ) else 0
  have hf : ∀ l ∈ L, 0 ≤ f l := by
    intro l _
    dsimp only [f]
    split_ifs <;> positivity
  have hhigh : d * (N.card : ℝ) - 2 * (L.card : ℝ) ≤ ∑ l ∈ L, f l :=
    sum_high_trace_ge_min_degree R N L d hdegree
  have hcube := pow_le_pow_left₀ hbase hhigh 3
  have hmean := sum_cube_card_sq L f hf
  have hpoint : ∀ l ∈ L,
      (2 / 9 : ℝ) * f l ^ 3 ≤
        ((orderedTriples (N.filter fun p => R p l)).card : ℝ) := by
    intro l _
    dsimp only [f]
    split_ifs with h
    · exact two_ninths_cube_le_orderedTriples _ h
    · simp only [zero_pow (by decide : 3 ≠ 0), mul_zero]
      exact Nat.cast_nonneg _
  have hsum : (2 / 9 : ℝ) * (∑ l ∈ L, f l ^ 3) ≤
      ∑ l ∈ L, ((orderedTriples (N.filter fun p => R p l)).card : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hpoint
  calc
    (2 / 9 : ℝ) * (d * (N.card : ℝ) - 2 * (L.card : ℝ)) ^ 3 ≤
        (2 / 9 : ℝ) * (∑ l ∈ L, f l) ^ 3 :=
      mul_le_mul_of_nonneg_left hcube (by norm_num)
    _ ≤ (2 / 9 : ℝ) * ((L.card : ℝ) ^ 2 * ∑ l ∈ L, f l ^ 3) :=
      mul_le_mul_of_nonneg_left hmean (by norm_num)
    _ = (L.card : ℝ) ^ 2 * ((2 / 9 : ℝ) * ∑ l ∈ L, f l ^ 3) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (sq_nonneg _)

theorem anchorConfigurations_card_lower (R : Pt → Ln → Prop)
    (N : Finset Pt) (L : Finset Ln) (extra : ℝ) (hextra : 0 ≤ extra)
    (hoff : ∀ l ∈ L, extra ≤ ((N.filter fun p => ¬ R p l).card : ℝ)) :
    extra * (∑ l ∈ L, ((orderedTriples (N.filter fun p => R p l)).card : ℝ)) ≤
      ((anchorConfigurations R N L).card : ℝ) := by
  let _ := hextra
  simp only [card_anchorConfigurations, Nat.cast_sum, Nat.cast_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  calc
    extra * ((orderedTriples (N.filter fun p => R p l)).card : ℝ) =
        ((orderedTriples (N.filter fun p => R p l)).card : ℝ) * extra := mul_comm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (hoff l hl) (Nat.cast_nonneg _)

private theorem card_orderedTriples_le_card_cube (P : Finset Pt) :
    (orderedTriples P).card ≤ P.card ^ 3 := by
  rw [card_orderedTriples]
  calc
    P.card * (P.card - 1) * (P.card - 2) ≤ P.card * P.card * P.card :=
      Nat.mul_le_mul (Nat.mul_le_mul_left P.card (Nat.sub_le P.card 1))
        (Nat.sub_le P.card 2)
    _ = P.card ^ 3 := by ring

theorem anchorConfigurations_card_upper (R : Pt → Ln → Prop)
    (P : Finset Pt) (L : Finset Ln) (H : ℝ) (hH : 0 ≤ H)
    (hcap : ∀ l ∈ L, ((P.filter fun p => R p l).card : ℝ) ≤ H) :
    ((anchorConfigurations R P L).card : ℝ) ≤
      (L.card : ℝ) * H ^ 3 * (P.card : ℝ) := by
  have hterm (l : Ln) (hl : l ∈ L) :
      ((orderedTriples (P.filter fun p => R p l)).card : ℝ) *
        ((P.filter fun p => ¬ R p l).card : ℝ) ≤ H ^ 3 * (P.card : ℝ) := by
    have ht : ((orderedTriples (P.filter fun p => R p l)).card : ℝ) ≤
        ((P.filter fun p => R p l).card : ℝ) ^ 3 := by
      exact_mod_cast card_orderedTriples_le_card_cube (P.filter fun p => R p l)
    have htH : ((orderedTriples (P.filter fun p => R p l)).card : ℝ) ≤ H ^ 3 :=
      ht.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (hcap l hl) 3)
    have hoff : ((P.filter fun p => ¬ R p l).card : ℝ) ≤ (P.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun p => ¬ R p l) P)
    exact mul_le_mul htH hoff (Nat.cast_nonneg _) (pow_nonneg hH 3)
  calc
    ((anchorConfigurations R P L).card : ℝ) =
        ∑ l ∈ L, ((orderedTriples (P.filter fun p => R p l)).card : ℝ) *
          ((P.filter fun p => ¬ R p l).card : ℝ) := by
      simp only [card_anchorConfigurations, Nat.cast_sum, Nat.cast_mul]
    _ ≤ ∑ _l ∈ L, H ^ 3 * (P.card : ℝ) := Finset.sum_le_sum hterm
    _ = (L.card : ℝ) * H ^ 3 * (P.card : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

end RyserCoveringCounterexample.Incidence

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_FourAnchorsNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence

theorem fourAnchors_degree_lower {r U : ℝ} (hr : 0 < r) (hU : 2 ≤ U)
    (hrlarge : 4096 * U ^ 7 ≤ r) :
    2 ≤ r / (8 * U ^ 2) := by
  let _ := hr
  have hUpos : 0 < U := by linarith
  have hUone : 1 ≤ U := by linarith
  have hpow : U ^ 2 ≤ U ^ 7 := pow_le_pow_right₀ hUone (by norm_num)
  apply (le_div_iff₀ (show 0 < 8 * U ^ 2 by positivity)).mpr
  nlinarith only [hrlarge, hpow, sq_nonneg U]

theorem fourAnchors_pair_lower {r U : ℝ} (hr : 0 < r) (hU : 2 ≤ U)
    (hrlarge : 4096 * U ^ 7 ≤ r) :
    r ^ 2 / (128 * U ^ 4) ≤
      (r / (8 * U ^ 2)) * (r / (8 * U ^ 2) - 1) := by
  have hUpos : 0 < U := by linarith
  have hUne : U ≠ 0 := ne_of_gt hUpos
  let d : ℝ := r / (8 * U ^ 2)
  have hd : 2 ≤ d := fourAnchors_degree_lower hr hU hrlarge
  have hd0 : 0 ≤ d := by linarith
  have hd2 : 0 ≤ d - 2 := by linarith
  have hid : r ^ 2 / (128 * U ^ 4) = d ^ 2 / 2 := by
    dsimp [d]
    field_simp [hUne]; ring
  change r ^ 2 / (128 * U ^ 4) ≤ d * (d - 1)
  rw [hid]
  nlinarith only [mul_nonneg hd0 hd2]

theorem fourAnchors_surplus_lower {r U : ℝ} (hr : 0 < r) (hU : 2 ≤ U)
    (hrlarge : 4096 * U ^ 7 ≤ r) {N : ℝ}
    (hN : r ^ 2 / (128 * U ^ 4) ≤ N) :
    r ^ 3 / (2048 * U ^ 6) ≤
      (r / (8 * U ^ 2)) * N - 2 * (U * r ^ 2) := by
  have hUpos : 0 < U := by linarith
  have hUne : U ≠ 0 := ne_of_gt hUpos
  have hcost : 2 * (U * r ^ 2) ≤ r ^ 3 / (2048 * U ^ 6) := by
    apply (le_div_iff₀ (show 0 < 2048 * U ^ 6 by positivity)).mpr
    calc
      2 * (U * r ^ 2) * (2048 * U ^ 6) = (4096 * U ^ 7) * r ^ 2 := by ring
      _ ≤ r * r ^ 2 := mul_le_mul_of_nonneg_right hrlarge (sq_nonneg r)
      _ = r ^ 3 := by ring
  have hmain : (r / (8 * U ^ 2)) * (r ^ 2 / (128 * U ^ 4)) ≤
      (r / (8 * U ^ 2)) * N :=
    mul_le_mul_of_nonneg_left hN (by positivity)
  have hid : (r / (8 * U ^ 2)) * (r ^ 2 / (128 * U ^ 4)) =
      2 * (r ^ 3 / (2048 * U ^ 6)) := by
    field_simp [hUne]; ring
  nlinarith only [hcost, hmain, hid]

theorem fourAnchors_margin_lower {r U : ℝ} (hr : 0 < r) (hU : 2 ≤ U)
    (hrlarge : 4096 * U ^ 7 ≤ r) :
    r ^ 2 / (256 * U ^ 4) ≤
      r ^ 2 / (128 * U ^ 4) - 16 * U ^ 3 * r := by
  have hUpos : 0 < U := by linarith
  have hUne : U ≠ 0 := ne_of_gt hUpos
  have hcost : 16 * U ^ 3 * r ≤ r ^ 2 / (256 * U ^ 4) := by
    apply (le_div_iff₀ (show 0 < 256 * U ^ 4 by positivity)).mpr
    calc
      (16 * U ^ 3 * r) * (256 * U ^ 4) = (4096 * U ^ 7) * r := by ring
      _ ≤ r * r := mul_le_mul_of_nonneg_right hrlarge hr.le
      _ = r ^ 2 := by ring
  have hid : r ^ 2 / (128 * U ^ 4) = 2 * (r ^ 2 / (256 * U ^ 4)) := by
    field_simp [hUne]; ring
  linarith only [hcost, hid]

theorem fourAnchors_count_lower {r U : ℝ} (hr : 0 < r) (hU : 2 ≤ U)
    (hrlarge : 4096 * U ^ 7 ≤ r) {N L T : ℝ}
    (hN : r ^ 2 / (128 * U ^ 4) ≤ N)
    (hL0 : 0 ≤ L) (hL : L ≤ U * r ^ 2) (hT0 : 0 ≤ T)
    (hcount : (2 / 9 : ℝ) *
      ((r / (8 * U ^ 2)) * N - 2 * (U * r ^ 2)) ^ 3 ≤ L ^ 2 * T) :
    r ^ 5 / (9 * 2 ^ 32 * U ^ 20) ≤ T := by
  have hUpos : 0 < U := by linarith
  have hUne : U ≠ 0 := ne_of_gt hUpos
  let a : ℝ := r ^ 3 / (2048 * U ^ 6)
  let k : ℝ := r ^ 5 / (9 * 2 ^ 32 * U ^ 20)
  have ha0 : 0 ≤ a := by
    dsimp [a]
    positivity
  have hsurplus : a ≤ (r / (8 * U ^ 2)) * N - 2 * (U * r ^ 2) :=
    fourAnchors_surplus_lower hr hU hrlarge hN
  have hcube := pow_le_pow_left₀ ha0 hsurplus 3
  have hLsq : L ^ 2 ≤ (U * r ^ 2) ^ 2 := pow_le_pow_left₀ hL0 hL 2
  have hbound : (2 / 9 : ℝ) * a ^ 3 ≤ (U * r ^ 2) ^ 2 * T := by
    calc
      (2 / 9 : ℝ) * a ^ 3 ≤ (2 / 9 : ℝ) *
          ((r / (8 * U ^ 2)) * N - 2 * (U * r ^ 2)) ^ 3 :=
        mul_le_mul_of_nonneg_left hcube (by norm_num)
      _ ≤ L ^ 2 * T := hcount
      _ ≤ (U * r ^ 2) ^ 2 * T := mul_le_mul_of_nonneg_right hLsq hT0
  have hid : (U * r ^ 2) ^ 2 * k = (2 / 9 : ℝ) * a ^ 3 := by
    dsimp [k, a]
    field_simp [hUne]; ring
  change k ≤ T
  apply (mul_le_mul_iff_right₀ (show 0 < (U * r ^ 2) ^ 2 by positivity)).mp
  rw [hid]
  exact hbound

theorem fourAnchors_total_lower {r U : ℝ} (hr : 0 < r) (hU : 2 ≤ U)
    {P extra T total : ℝ}
    (hP : r ^ 2 / (32 * U ^ 4) ≤ P)
    (hExtra : r ^ 2 / (256 * U ^ 4) ≤ extra)
    (hT : r ^ 5 / (9 * 2 ^ 32 * U ^ 20) ≤ T)
    (hTotal : P * extra * T ≤ total) :
    r ^ 9 / (9 * 2 ^ 45 * U ^ 28) ≤ total := by
  have hUpos : 0 < U := by linarith
  have hUne : U ≠ 0 := ne_of_gt hUpos
  have hp0 : 0 ≤ r ^ 2 / (32 * U ^ 4) := by positivity
  have he0 : 0 ≤ r ^ 2 / (256 * U ^ 4) := by positivity
  have ht0 : 0 ≤ r ^ 5 / (9 * 2 ^ 32 * U ^ 20) := by positivity
  have hP0 : 0 ≤ P := hp0.trans hP
  have hExtra0 : 0 ≤ extra := he0.trans hExtra
  have hproduct :
      (r ^ 2 / (32 * U ^ 4)) * (r ^ 2 / (256 * U ^ 4)) *
          (r ^ 5 / (9 * 2 ^ 32 * U ^ 20)) ≤ P * extra * T :=
    mul_le_mul (mul_le_mul hP hExtra he0 hP0) hT ht0 (mul_nonneg hP0 hExtra0)
  calc
    r ^ 9 / (9 * 2 ^ 45 * U ^ 28) =
        (r ^ 2 / (32 * U ^ 4)) * (r ^ 2 / (256 * U ^ 4)) *
          (r ^ 5 / (9 * 2 ^ 32 * U ^ 20)) := by
      field_simp [hUne]; ring
    _ ≤ P * extra * T := hproduct
    _ ≤ total := hTotal

theorem fourAnchors_candidate_upper {r U : ℝ} (hr : 0 < r) (hU : 2 ≤ U)
    {L P : ℝ} (_hL0 : 0 ≤ L) (hL : L ≤ U * r ^ 2)
    (hP0 : 0 ≤ P) (hP : P ≤ U * r ^ 2) :
    L * (16 * U ^ 3 * r) ^ 3 * P ≤ 2 ^ 12 * U ^ 11 * r ^ 7 := by
  have hUpos : 0 < U := by linarith
  have hcap0 : 0 ≤ (16 * U ^ 3 * r) ^ 3 := by positivity
  have hM0 : 0 ≤ U * r ^ 2 := by positivity
  calc
    L * (16 * U ^ 3 * r) ^ 3 * P ≤
        (U * r ^ 2) * (16 * U ^ 3 * r) ^ 3 * P :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL hcap0) hP0
    _ ≤ (U * r ^ 2) * (16 * U ^ 3 * r) ^ 3 * (U * r ^ 2) :=
      mul_le_mul_of_nonneg_left hP (mul_nonneg hM0 hcap0)
    _ = 2 ^ 12 * U ^ 11 * r ^ 7 := by ring

theorem fourAnchors_average_lower {r U : ℝ} (hr : 0 < r) (hU : 2 ≤ U)
    {total candidate W : ℝ}
    (hTotal : r ^ 9 / (9 * 2 ^ 45 * U ^ 28) ≤ total)
    (hCandidate : candidate ≤ 2 ^ 12 * U ^ 11 * r ^ 7)
    (hW : 0 ≤ W) (hLink : total ≤ candidate * W) :
    r ^ 2 / (9 * 2 ^ 57 * U ^ 39) ≤ W := by
  have hUpos : 0 < U := by linarith
  have hUne : U ≠ 0 := ne_of_gt hUpos
  have hcap : 0 < 2 ^ 12 * U ^ 11 * r ^ 7 := by positivity
  apply (mul_le_mul_iff_right₀ hcap).mp
  calc
    (2 ^ 12 * U ^ 11 * r ^ 7) * (r ^ 2 / (9 * 2 ^ 57 * U ^ 39)) =
        r ^ 9 / (9 * 2 ^ 45 * U ^ 28) := by
      field_simp [hUne]
    _ ≤ total := hTotal
    _ ≤ candidate * W := hLink
    _ ≤ (2 ^ 12 * U ^ 11 * r ^ 7) * W := mul_le_mul_of_nonneg_right hCandidate hW

end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_FourAnchors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace RyserCoveringCounterexample.Incidence

attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [DecidableEq F]

theorem fourAnchors_of_pruned_r
    (P : Finset (ProjectivePoint F)) (L : Finset (ProjectiveLine F))
    {r U : ℝ} (hr : 0 < r) (hU : 2 ≤ U) (hrlarge : 4096 * U ^ 7 ≤ r)
    (hPlo : r ^ 2 / (32 * U ^ 4) ≤ (P.card : ℝ))
    (hPup : (P.card : ℝ) ≤ U * r ^ 2)
    (hLup : (L.card : ℝ) ≤ U * r ^ 2)
    (hpoints : ∀ p ∈ P, r / (8 * U ^ 2) ≤
      ((L.filter fun l => ProjectiveIncidence p l).card : ℝ))
    (hlines : ∀ l ∈ L, r / (8 * U ^ 2) ≤
      ((P.filter fun p => ProjectiveIncidence p l).card : ℝ))
    (hcap : ∀ l ∈ L, ((P.filter fun p => ProjectiveIncidence p l).card : ℝ) ≤
      16 * U ^ 3 * r) :
    ∃ c ∈ anchorConfigurations ProjectiveIncidence P L,
      r ^ 2 / (9 * 2 ^ 57 * U ^ 39) ≤
        ((anchorWitnesses ProjectiveIncidence P L c).card : ℝ) := by
  classical
  have hUpos : 0 < U := by linarith
  let d : ℝ := r / (8 * U ^ 2)
  let extra : ℝ := r ^ 2 / (256 * U ^ 4)
  let T0 : ℝ := r ^ 5 / (9 * 2 ^ 32 * U ^ 20)
  have hd : 1 ≤ d := by
    have := fourAnchors_degree_lower hr hU hrlarge
    dsimp [d]
    linarith
  have hextra : 0 ≤ extra := by dsimp [extra]; positivity
  have hlocal (x : ProjectivePoint F) (hx : x ∈ P) :
      extra * T0 ≤
        ((anchorConfigurations ProjectiveIncidence
          (joinedNeighbors ProjectiveIncidence P L x) L).card : ℝ) := by
    let N := joinedNeighbors ProjectiveIncidence P L x
    have hNP : N ⊆ P := by
      intro p hp
      simp only [N, joinedNeighbors, Finset.mem_filter] at hp
      exact hp.1
    have hN : r ^ 2 / (128 * U ^ 4) ≤ (N.card : ℝ) :=
      (fourAnchors_pair_lower hr hU hrlarge).trans
        (projective_joinedNeighbors_card_lower P L x hx hd (hpoints x hx) hlines)
    have hdegree : ∀ p ∈ N, d ≤
        ((L.filter fun l => ProjectiveIncidence p l).card : ℝ) :=
      fun p hp => hpoints p (hNP hp)
    have hsurplus : 0 ≤ d * (N.card : ℝ) - 2 * (U * r ^ 2) := by
      have h := fourAnchors_surplus_lower hr hU hrlarge hN
      have hnon : 0 ≤ r ^ 3 / (2048 * U ^ 6) := by positivity
      exact hnon.trans h
    have hbase : 0 ≤ d * (N.card : ℝ) - 2 * (L.card : ℝ) := by
      linarith
    have htriples : (2 / 9 : ℝ) * (d * (N.card : ℝ) - 2 * (L.card : ℝ)) ^ 3 ≤
        (L.card : ℝ) ^ 2 *
          ∑ l ∈ L, ((orderedTriples (N.filter fun p => ProjectiveIncidence p l)).card : ℝ) := by
      convert triple_sum_lower_bound ProjectiveIncidence N L d
        (by
          intro p hp
          convert hdegree p hp using 1; congr) hbase using 1; congr; funext l; congr
    have hcomparison : d * (N.card : ℝ) - 2 * (U * r ^ 2) ≤
        d * (N.card : ℝ) - 2 * (L.card : ℝ) := by linarith
    have hcount : (2 / 9 : ℝ) * (d * (N.card : ℝ) - 2 * (U * r ^ 2)) ^ 3 ≤
        (L.card : ℝ) ^ 2 *
          ∑ l ∈ L, ((orderedTriples (N.filter fun p => ProjectiveIncidence p l)).card : ℝ) := by
      exact (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hsurplus hcomparison 3) (by norm_num)).trans htriples
    have hT : T0 ≤
        ∑ l ∈ L, ((orderedTriples (N.filter fun p => ProjectiveIncidence p l)).card : ℝ) :=
      fourAnchors_count_lower hr hU hrlarge hN (Nat.cast_nonneg _) hLup
        (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) hcount
    have hoff : ∀ l ∈ L,
        extra ≤ ((N.filter fun p => ¬ ProjectiveIncidence p l).card : ℝ) := by
      intro l hl
      have htrace : ((N.filter fun p => ProjectiveIncidence p l).card : ℝ) ≤
          16 * U ^ 3 * r := by
        apply le_trans _ (hcap l hl)
        exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter (fun p => ProjectiveIncidence p l) hNP)
      have hpartition := Finset.card_filter_add_card_filter_not
        (s := N) (fun p => ProjectiveIncidence p l)
      have hpartition' : ((N.filter fun p => ProjectiveIncidence p l).card : ℝ) +
          ((N.filter fun p => ¬ ProjectiveIncidence p l).card : ℝ) = (N.card : ℝ) := by
        exact_mod_cast hpartition
      have hmargin := fourAnchors_margin_lower hr hU hrlarge
      dsimp [extra]
      linarith
    have hConfig : extra *
        (∑ l ∈ L, ((orderedTriples (N.filter fun p => ProjectiveIncidence p l)).card : ℝ)) ≤
        ((anchorConfigurations ProjectiveIncidence N L).card : ℝ) := by
      convert anchorConfigurations_card_lower ProjectiveIncidence N L extra hextra
        (by
          intro l hl
          convert hoff l hl using 1; congr) using 1; congr; funext l; congr
    exact (mul_le_mul_of_nonneg_left hT hextra).trans hConfig
  let total : ℝ := ∑ x ∈ P,
    ((anchorConfigurations ProjectiveIncidence
      (joinedNeighbors ProjectiveIncidence P L x) L).card : ℝ)
  have hTotal : r ^ 9 / (9 * 2 ^ 45 * U ^ 28) ≤ total := by
    apply fourAnchors_total_lower hr hU hPlo (le_refl extra) (le_refl T0)
    calc
      (P.card : ℝ) * extra * T0 = ∑ _x ∈ P, (extra * T0) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ total := Finset.sum_le_sum hlocal
  let C := anchorConfigurations ProjectiveIncidence P L
  have hExchange : total =
      ∑ c ∈ C, ((anchorWitnesses ProjectiveIncidence P L c).card : ℝ) := by
    dsimp [total, C]
    exact_mod_cast sum_card_anchorConfigurations_neighbors ProjectiveIncidence P L
  have hC : C.Nonempty := by
    by_contra h
    have hEmpty : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [hEmpty] at hExchange
    simp only [Finset.sum_empty] at hExchange
    have hpos : 0 < r ^ 9 / (9 * 2 ^ 45 * U ^ 28) := by positivity
    linarith
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image C
    (fun c => ((anchorWitnesses ProjectiveIncidence P L c).card : ℝ)) hC
  refine ⟨c, hc, ?_⟩
  apply fourAnchors_average_lower hr hU hTotal
  · exact (anchorConfigurations_card_upper ProjectiveIncidence P L
      (16 * U ^ 3 * r) (by positivity)
      (by
        intro l hl
        convert hcap l hl using 1; congr)).trans
        (fourAnchors_candidate_upper hr hU (Nat.cast_nonneg _) hLup
          (Nat.cast_nonneg _) hPup)
  · exact Nat.cast_nonneg _
  · rw [hExchange]
    calc
      (∑ c' ∈ C, ((anchorWitnesses ProjectiveIncidence P L c').card : ℝ)) ≤
          ∑ _c' ∈ C, ((anchorWitnesses ProjectiveIncidence P L c).card : ℝ) :=
        Finset.sum_le_sum fun c' hc' => hmax c' hc'
      _ = (C.card : ℝ) * ((anchorWitnesses ProjectiveIncidence P L c).card : ℝ) := by
        simp only [Finset.sum_const, nsmul_eq_mul]

end RyserCoveringCounterexample.Incidence

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence
noncomputable section
open Filter Topology

theorem graphScaleConstant_pos : 0 < graphScaleConstant := by
  norm_num [graphScaleConstant]

theorem graphScale_pos {U : ℝ} (hU : 0 < U) : 0 < graphScale U :=
  mul_pos graphScaleConstant_pos (pow_pos hU _)
theorem expansionScale_pos {V : ℝ} (hV : 0 < V) : 0 < expansionScale V :=
  mul_pos (by norm_num) (pow_pos hV _)

theorem largeEnough_of_threshold {q : ℕ} (hq : incidenceThreshold ≤ q) :
    LargeEnough (q : ℝ) :=
  Classical.choose_spec exists_threshold_largeEnough q hq

end
end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_GraphParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence

theorem graphScale_bounds {U : ℝ} (hU : 2 ≤ U) :
    2 ≤ graphScale U ∧ 16 * U ^ 3 ≤ graphScale U := by
  have hU1 : 1 ≤ U := le_trans (by norm_num) hU
  have hU0 : 0 ≤ U := le_trans (by norm_num) hU
  have hC : 16 ≤ graphScaleConstant := by norm_num [graphScaleConstant]
  have hpow : 1 ≤ U ^ 39 := one_le_pow₀ hU1
  constructor
  · calc
      2 ≤ graphScaleConstant := le_trans (by norm_num) hC
      _ ≤ graphScaleConstant * U ^ 39 :=
        le_mul_of_one_le_right graphScaleConstant_pos.le hpow
      _ = graphScale U := rfl
  · calc
      16 * U ^ 3 ≤ graphScaleConstant * U ^ 3 :=
        mul_le_mul_of_nonneg_right hC (pow_nonneg hU0 _)
      _ ≤ graphScaleConstant * U ^ 39 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hU1 (by decide))
          graphScaleConstant_pos.le
      _ = graphScale U := rfl

theorem two_le_expansionScale {V : ℝ} (hV : 2 ≤ V) : 2 ≤ expansionScale V := by
  have hV1 : 1 ≤ V := le_trans (by norm_num) hV
  calc
    2 ≤ (2 : ℝ) ^ 23 := by norm_num
    _ ≤ 2 ^ 23 * V ^ 24 :=
      le_mul_of_one_le_right (by norm_num) (one_le_pow₀ hV1)
    _ = expansionScale V := rfl

theorem retained_witness_lower (r U w g : ℝ) (hr : 0 < r) (hU : 2 ≤ U)
    (hW : r ^ 2 / (9 * 2 ^ 57 * U ^ 39) ≤ w)
    (hG : w - 3 * (16 * U ^ 3 * r) ≤ g)
    (hremove : (96 / witnessConstant) * U ^ 42 ≤ r) :
    r ^ 2 / graphScale U ≤ g := by
  have hUpos : 0 < U := lt_of_lt_of_le (by norm_num) hU
  have hVpos := graphScale_pos hUpos
  have hloss : 3 * (16 * U ^ 3 * r) ≤ r ^ 2 / graphScale U := by
    apply (le_div_iff₀ hVpos).mpr
    calc
      3 * (16 * U ^ 3 * r) * graphScale U =
          ((96 / witnessConstant) * U ^ 42) * r := by
        norm_num [graphScale, graphScaleConstant, witnessConstant]
        ring
      _ ≤ r * r := mul_le_mul_of_nonneg_right hremove hr.le
      _ = r ^ 2 := (pow_two r).symm
  have htwice : 2 * (r ^ 2 / graphScale U) ≤ w := by
    convert hW using 1
    dsimp [graphScale, graphScaleConstant]
    field_simp [ne_of_gt hUpos]

  linarith

theorem extraction_expansion_le (r V s : ℝ) (hr : 0 ≤ r) (hV : 0 < V)
    (hlo : 3 * r / (8 * V ^ 2) ≤ s) :
    2 ^ 20 * V ^ 22 * r ≤ expansionScale V * s := by
  have hB : 0 ≤ (2 : ℝ) ^ 20 * V ^ 22 * r := by positivity
  calc
    2 ^ 20 * V ^ 22 * r ≤ 3 * (2 ^ 20 * V ^ 22 * r) := by linarith
    _ = expansionScale V * (3 * r / (8 * V ^ 2)) := by
      dsimp [expansionScale]
      field_simp [ne_of_gt hV]
      norm_num
      ring
    _ ≤ expansionScale V * s :=
      mul_le_mul_of_nonneg_left hlo (expansionScale_pos hV).le

end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_WalkExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Incidence

open scoped Pointwise

theorem walkCard_mul_le_labelCard_pow_four {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (T : Finset α) (D : Finset β) (eval : (β × β) × (β × β) → α) (L : ℝ)
    (hf : ∀ t ∈ T,
      L ≤ ((((D ×ˢ D) ×ˢ (D ×ˢ D)).filter fun q => eval q = t).card : ℝ)) :
    (T.card : ℝ) * L ≤ (D.card : ℝ) ^ 4 := by
  classical
  have hcount := Finset.card_nsmul_le_card_nsmul (R := ℝ)
    (s := T) (t := (D ×ˢ D) ×ˢ (D ×ˢ D)) (m := L) (n := 1)
    (fun t q => eval q = t) hf (by
      intro q _
      have hcard : (T.bipartiteBelow (fun t q => eval q = t) q).card ≤ 1 := by
        apply Finset.card_le_one_iff.mpr
        intro x y hx hy
        exact (Finset.mem_filter.mp hx).2.symm.trans (Finset.mem_filter.mp hy).2
      exact_mod_cast hcard)
  calc
    (T.card : ℝ) * L ≤ (((D ×ˢ D) ×ˢ (D ×ˢ D)).card : ℝ) := by
      simpa only [nsmul_eq_mul, mul_one] using hcount
    _ = (D.card : ℝ) ^ 4 := by
      simp only [Finset.card_product, Nat.cast_mul]
      ring

theorem expansion_bound_of_card_mul_le {c d n V : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hn : 0 < n) (hV : 2 ≤ V)
    (hdV : d ≤ V * n)
    (h : c * (n ^ 3 / (2 ^ 20 * V ^ 18)) ≤ d ^ 4) :
    c ≤ 2 ^ 20 * V ^ 22 * n := by
  let _ := hc
  have hVpos : 0 < V := lt_of_lt_of_le (by norm_num) hV
  have hLpos : 0 < n ^ 3 / (2 ^ 20 * V ^ 18) := by positivity
  apply (mul_le_mul_iff_left₀ hLpos).mp
  calc
    c * (n ^ 3 / (2 ^ 20 * V ^ 18)) ≤ d ^ 4 := h
    _ ≤ (V * n) ^ 4 := pow_le_pow_left₀ hd hdV 4
    _ = (2 ^ 20 * V ^ 22 * n) * (n ^ 3 / (2 ^ 20 * V ^ 18)) := by
      field_simp [ne_of_gt hVpos]

theorem fourWalks_mem_data {F : Type*} [DecidableEq F]
    {A B : Finset F} {G : Finset (F × F)} {a a' : F}
    {w : Σ _ : F, F × F} (hw : w ∈ fourWalks A B G a a') :
    w.1 ∈ A ∧ w.2.1 ∈ B ∧ w.2.2 ∈ B ∧
      (a, w.2.1) ∈ G ∧ (w.1, w.2.1) ∈ G ∧
      (w.1, w.2.2) ∈ G ∧ (a', w.2.2) ∈ G := by
  have h := Finset.mem_sigma.mp hw
  have hp := Finset.mem_product.mp h.2
  have hleft := Finset.mem_filter.mp hp.1
  have hright := Finset.mem_filter.mp hp.2
  exact ⟨h.1, hleft.1, hright.1, hleft.2.1, hleft.2.2,
    hright.2.1, hright.2.2⟩

variable {F : Type*} [Field F] [instDecidableEqF : DecidableEq F]

private theorem differenceWalkLabels_injective (a a' : F) :
    Function.Injective (differenceWalkLabels a a') := let _ := instDecidableEqF; by
  intro w v h
  rcases w with ⟨m, b₁, b₂⟩
  rcases v with ⟨m', c₁, c₂⟩
  have h₁ := congrArg (fun q : (F × F) × (F × F) => q.1.1) h
  have h₂ := congrArg (fun q : (F × F) × (F × F) => q.1.2) h
  have h₃ := congrArg (fun q : (F × F) × (F × F) => q.2.1) h
  change a - b₁ = a - c₁ at h₁
  change m - b₁ = m' - c₁ at h₂
  change m - b₂ = m' - c₂ at h₃
  have hb₁ : b₁ = c₁ := by linear_combination -h₁
  subst c₁
  have hm : m = m' := by linear_combination h₂
  subst m'
  have hb₂ : b₂ = c₂ := by linear_combination -h₃
  subst c₂
  rfl

theorem difference_bound_of_many_fourWalks
    (A B : Finset F) (G : Finset (F × F)) (S : Finset F)
    {n V : ℝ} (hn : 0 < n) (hV : 2 ≤ V)
    (hD : ((edgeDifferences G).card : ℝ) ≤ V * n)
    (hw : ∀ a ∈ S, ∀ a' ∈ S,
      n ^ 3 / (2 ^ 20 * V ^ 18) ≤ ((fourWalks A B G a a').card : ℝ)) :
    ((S - S).card : ℝ) ≤ 2 ^ 20 * V ^ 22 * n := by
  classical
  apply expansion_bound_of_card_mul_le (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hn hV hD
  apply walkCard_mul_le_labelCard_pow_four (S - S) (edgeDifferences G)
    (fun q => q.1.1 - q.1.2 + q.2.1 - q.2.2)
  intro d hd
  obtain ⟨a, ha, a', ha', rfl⟩ := Finset.mem_sub.mp hd
  have hcard : (fourWalks A B G a a').card ≤
      ((((edgeDifferences G ×ˢ edgeDifferences G) ×ˢ
          (edgeDifferences G ×ˢ edgeDifferences G)).filter
        fun q => q.1.1 - q.1.2 + q.2.1 - q.2.2 = a - a').card) := by
    apply Finset.card_le_card_of_injOn (differenceWalkLabels a a')
    · intro w hwmem
      obtain ⟨_, _, _, h₁, h₂, h₃, h₄⟩ := fourWalks_mem_data hwmem
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor
        · apply Finset.mem_product.mpr
          exact ⟨Finset.mem_image.mpr ⟨(a, w.2.1), h₁, rfl⟩,
            Finset.mem_image.mpr ⟨(w.1, w.2.1), h₂, rfl⟩⟩
        · apply Finset.mem_product.mpr
          exact ⟨Finset.mem_image.mpr ⟨(w.1, w.2.2), h₃, rfl⟩,
            Finset.mem_image.mpr ⟨(a', w.2.2), h₄, rfl⟩⟩
      · dsimp [differenceWalkLabels]
        ring
    · exact (differenceWalkLabels_injective a a').injOn
  exact (hw a ha a' ha').trans (by exact_mod_cast hcard)

end RyserCoveringCounterexample.Incidence

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_WalkTrimming
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Incidence

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem exists_trimmed_many_fourWalks
    (A₀ A : Finset α) (B : Finset β) (G : Finset (α × β))
    (hA₀ : A₀ ⊆ A) (t : ℝ) (ht : 0 ≤ t)
    (hm : 0 < (A₀.card : ℝ))
    (hbad : ((badPairs A₀ B G t).card : ℝ) ≤ (A₀.card : ℝ) ^ 2 / 16) :
    ∃ S : Finset α, S ⊆ A₀ ∧
      3 * (A₀.card : ℝ) / 4 ≤ (S.card : ℝ) ∧
      ∀ a ∈ S, ∀ a' ∈ S,
        (A₀.card : ℝ) / 2 * t ^ 2 ≤ ((fourWalks A B G a a').card : ℝ) := by
  classical
  let m : ℝ := A₀.card
  let R : Finset α := A₀.filter fun a =>
    m / 4 < ((badPartners A₀ B G t a).card : ℝ)
  let S : Finset α := A₀ \ R
  have hRsub : R ⊆ A₀ := Finset.filter_subset _ _
  have htotal : (∑ a ∈ A₀, ((badPartners A₀ B G t a).card : ℝ)) =
      ((badPairs A₀ B G t).card : ℝ) := by
    rw [← Nat.cast_sum, ← card_badPairs_eq_sum_badPartners]
  have hRlower : (R.card : ℝ) * (m / 4) ≤
      ∑ a ∈ R, ((badPartners A₀ B G t a).card : ℝ) := by
    simpa only [nsmul_eq_mul] using
      (Finset.card_nsmul_le_sum R
        (fun a => ((badPartners A₀ B G t a).card : ℝ)) (m / 4)
        (fun a ha => le_of_lt (Finset.mem_filter.mp ha).2))
  have hRupper : (∑ a ∈ R, ((badPartners A₀ B G t a).card : ℝ)) ≤
      ((badPairs A₀ B G t).card : ℝ) := by
    calc
      _ ≤ ∑ a ∈ A₀, ((badPartners A₀ B G t a).card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hRsub
          (fun a _ _ => Nat.cast_nonneg _)
      _ = _ := htotal
  have hmpos : 0 < m := hm
  have hRcard : (R.card : ℝ) ≤ m / 4 := by
    have hquarter : 0 < m / 4 := by positivity
    apply (mul_le_mul_iff_left₀ hquarter).mp
    have hbound := hRlower.trans (hRupper.trans hbad)
    change (R.card : ℝ) * (m / 4) ≤ m ^ 2 / 16 at hbound
    nlinarith
  have hsplitNat : S.card + R.card = A₀.card :=
    Finset.card_sdiff_add_card_eq_card hRsub
  have hsplit : (S.card : ℝ) + (R.card : ℝ) = m := by
    simpa only [Nat.cast_add] using
      congrArg (fun n : ℕ => (n : ℝ)) hsplitNat
  have hScard : 3 * m / 4 ≤ (S.card : ℝ) := by linarith
  have hkeep (a : α) (ha : a ∈ S) :
      ((badPartners A₀ B G t a).card : ℝ) ≤ m / 4 := by
    apply le_of_not_gt
    intro hgt
    exact (Finset.mem_sdiff.mp ha).2
      (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp ha).1, hgt⟩)
  refine ⟨S, Finset.sdiff_subset, hScard, ?_⟩
  intro a ha a' ha'
  let U : Finset α := badPartners A₀ B G t a ∪ badPartners A₀ B G t a'
  let C : Finset α := A₀ \ U
  have hUsub : U ⊆ A₀ := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (Finset.mem_filter.mp hx).1
    · exact (Finset.mem_filter.mp hx).1
  have hUcard : (U.card : ℝ) ≤ m / 2 := by
    have hu : (U.card : ℝ) ≤
        ((badPartners A₀ B G t a).card : ℝ) +
          ((badPartners A₀ B G t a').card : ℝ) := by
      simpa only [Nat.cast_add] using
        (Nat.cast_le.mpr (Finset.card_union_le
          (badPartners A₀ B G t a) (badPartners A₀ B G t a')) :
          (((badPartners A₀ B G t a ∪ badPartners A₀ B G t a').card : ℕ) : ℝ) ≤
            (((badPartners A₀ B G t a).card +
              (badPartners A₀ B G t a').card : ℕ) : ℝ))
    linarith [hkeep a ha, hkeep a' ha']
  have hCsplitNat : C.card + U.card = A₀.card :=
    Finset.card_sdiff_add_card_eq_card hUsub
  have hCsplit : (C.card : ℝ) + (U.card : ℝ) = m := by
    simpa only [Nat.cast_add] using
      congrArg (fun n : ℕ => (n : ℝ)) hCsplitNat
  have hCcard : m / 2 ≤ (C.card : ℝ) := by linarith
  have hCsub : C ⊆ A := Finset.Subset.trans Finset.sdiff_subset hA₀
  have hgood (x : α) (hx : x ∈ C) :
      t ≤ ((commonNeighbors B G a x).card : ℝ) ∧
      t ≤ ((commonNeighbors B G x a').card : ℝ) := by
    have hxA : x ∈ A₀ := (Finset.mem_sdiff.mp hx).1
    have hxU : x ∉ U := (Finset.mem_sdiff.mp hx).2
    constructor
    · apply le_of_not_gt
      intro hlt
      exact hxU (Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨hxA, hlt⟩)))
    · have hright : t ≤ ((commonNeighbors B G a' x).card : ℝ) := by
        apply le_of_not_gt
        intro hlt
        exact hxU (Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨hxA, hlt⟩)))
      simpa only [commonNeighbors_comm B G x a'] using hright
  have hwalks : ((fourWalks A B G a a').card : ℝ) =
      ∑ x ∈ A, ((commonNeighbors B G a x).card : ℝ) *
        ((commonNeighbors B G x a').card : ℝ) := by
    rw [card_fourWalks]
    simp only [Nat.cast_sum, Nat.cast_mul]
  calc
    m / 2 * t ^ 2 ≤ (C.card : ℝ) * t ^ 2 :=
      mul_le_mul_of_nonneg_right hCcard (sq_nonneg t)
    _ ≤ ∑ x ∈ C, ((commonNeighbors B G a x).card : ℝ) *
        ((commonNeighbors B G x a').card : ℝ) := by
      simpa only [nsmul_eq_mul] using
        (Finset.card_nsmul_le_sum C
          (fun x => ((commonNeighbors B G a x).card : ℝ) *
            ((commonNeighbors B G x a').card : ℝ)) (t ^ 2) (by
              intro x hx
              rw [pow_two]
              exact mul_le_mul (hgood x hx).1 (hgood x hx).2 ht (Nat.cast_nonneg _)))
    _ ≤ ∑ x ∈ A, ((commonNeighbors B G a x).card : ℝ) *
        ((commonNeighbors B G x a').card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hCsub
        (fun x _ _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ = ((fourWalks A B G a a').card : ℝ) := hwalks.symm

end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_WalkExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Incidence

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem exists_many_fourWalks
    (A : Finset α) (B : Finset β) (G : Finset (α × β))
    (hG : G ⊆ A ×ˢ B) {n V : ℝ} (hn : 0 < n) (hV : 2 ≤ V)
    (hA : (A.card : ℝ) ≤ V * n) (hB : (B.card : ℝ) ≤ V * n)
    (hE : n ^ 2 / V ≤ (G.card : ℝ)) :
    ∃ S : Finset α, S ⊆ A ∧
      3 * n / (8 * V ^ 2) ≤ (S.card : ℝ) ∧
      ∀ a ∈ S, ∀ a' ∈ S,
        n ^ 3 / (2 ^ 20 * V ^ 18) ≤ ((fourWalks A B G a a').card : ℝ) := by
  classical
  have hVpos : 0 < V := by linarith
  have hVne : V ≠ 0 := ne_of_gt hVpos
  obtain ⟨b, _hb, hsize, hbad⟩ :=
    exists_dense_neighborhood A B G hG hn hV hA hB hE
  have hc : 0 < n / (2 * V ^ 2) := by positivity
  have hm : 0 < ((neighbors A G b).card : ℝ) := hc.trans_le hsize
  have ht : 0 ≤ n / (512 * V ^ 8) := by positivity
  obtain ⟨S, hSsub, hScard, hwalks⟩ :=
    exists_trimmed_many_fourWalks (neighbors A G b) A B G
      (neighbors_subset A G b) (n / (512 * V ^ 8)) ht hm hbad
  refine ⟨S, hSsub.trans (neighbors_subset A G b), ?_, ?_⟩
  · calc
      3 * n / (8 * V ^ 2) = 3 * (n / (2 * V ^ 2)) / 4 := by
        field_simp [hVne]; ring
      _ ≤ 3 * ((neighbors A G b).card : ℝ) / 4 := by linarith
      _ ≤ (S.card : ℝ) := hScard
  · intro a ha a' ha'
    calc
      n ^ 3 / (2 ^ 20 * V ^ 18) =
          (n / (2 * V ^ 2)) / 2 * (n / (512 * V ^ 8)) ^ 2 := by
        field_simp [hVne]; ring
      _ ≤ ((neighbors A G b).card : ℝ) / 2 * (n / (512 * V ^ 8)) ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      _ ≤ ((fourWalks A B G a a').card : ℝ) := hwalks a ha a' ha'

end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_WalkQuotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence

open scoped Pointwise

variable {F : Type*} [Field F] [instDecidableEqF : DecidableEq F]

theorem div_mem_edgeQuotients {G : Finset (F × F)} {a b : F}
    (h : (a, b) ∈ G) : a / b ∈ edgeQuotients G :=
  Finset.mem_image.mpr ⟨(a, b), h, rfl⟩

theorem walkQuotientLabels_injective_at {a a' : F}
    {w v : Σ _ : F, F × F}
    (ha : a ≠ 0) (hm : w.1 ≠ 0) (hb : w.2.1 ≠ 0)
    (h : walkQuotientLabels a a' w = walkQuotientLabels a a' v) :
    w = v := let _ := instDecidableEqF; by
  rcases w with ⟨m, b₁, b₂⟩
  rcases v with ⟨n, c₁, c₂⟩
  have h₁ : a / b₁ = a / c₁ :=
    congrArg (fun q : (F × F) × (F × F) => q.1.1) h
  have hb₁ : b₁ = c₁ := by
    simpa only [div_eq_mul_inv, mul_right_inj' ha, inv_inj] using h₁
  have h₂ : m / b₁ = n / c₁ :=
    congrArg (fun q : (F × F) × (F × F) => q.1.2) h
  rw [← hb₁] at h₂
  have hmn : m = n := (div_left_inj' hb).mp h₂
  have h₃ : m / b₂ = n / c₂ :=
    congrArg (fun q : (F × F) × (F × F) => q.2.1) h
  rw [← hmn] at h₃
  have hb₂ : b₂ = c₂ := by
    simpa only [div_eq_mul_inv, mul_right_inj' hm, inv_inj] using h₃
  cases hmn
  cases hb₁
  cases hb₂
  rfl

theorem quotientWalkEval_labels {a a' : F} {w : Σ _ : F, F × F}
    (hm : w.1 ≠ 0) (hb₁ : w.2.1 ≠ 0) (hb₂ : w.2.2 ≠ 0) :
    quotientWalkEval (walkQuotientLabels a a' w) = a / a' := let _ := instDecidableEqF; by
  unfold quotientWalkEval walkQuotientLabels
  rw [mul_div_mul_comm, div_div_div_cancel_right₀ hb₁,
    div_div_div_cancel_right₀ hb₂, div_mul_div_cancel₀ hm]

theorem walkQuotientLabels_mem {A B : Finset F} {G : Finset (F × F)}
    {a a' : F} {w : Σ _ : F, F × F}
    (hw : w ∈ fourWalks A B G a a') :
    walkQuotientLabels a a' w ∈
      (edgeQuotients G ×ˢ edgeQuotients G) ×ˢ
        (edgeQuotients G ×ˢ edgeQuotients G) := by
  obtain ⟨_, _, _, h₁, h₂, h₃, h₄⟩ := fourWalks_mem_data hw
  exact Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr
      ⟨div_mem_edgeQuotients h₁, div_mem_edgeQuotients h₂⟩,
      Finset.mem_product.mpr
      ⟨div_mem_edgeQuotients h₃, div_mem_edgeQuotients h₄⟩⟩

theorem quotient_bound_of_many_fourWalks
    (A B : Finset F) (G : Finset (F × F)) (S : Finset F)
    (hS : S ⊆ A) (hA0 : ∀ a ∈ A, a ≠ 0) (hB0 : ∀ b ∈ B, b ≠ 0)
    {n V : ℝ} (hn : 0 < n) (hV : 2 ≤ V)
    (hD : ((edgeQuotients G).card : ℝ) ≤ V * n)
    (hw : ∀ a ∈ S, ∀ a' ∈ S,
      n ^ 3 / (2 ^ 20 * V ^ 18) ≤ ((fourWalks A B G a a').card : ℝ)) :
    ((S / S).card : ℝ) ≤ 2 ^ 20 * V ^ 22 * n := by
  have hcount : ((S / S).card : ℝ) * (n ^ 3 / (2 ^ 20 * V ^ 18)) ≤
      ((edgeQuotients G).card : ℝ) ^ 4 := by
    apply walkCard_mul_le_labelCard_pow_four
      (S / S) (edgeQuotients G) quotientWalkEval
      (n ^ 3 / (2 ^ 20 * V ^ 18))
    intro t ht
    obtain ⟨a, ha, a', ha', rfl⟩ := Finset.mem_div.mp ht
    have hc : (fourWalks A B G a a').card ≤
        (((edgeQuotients G ×ˢ edgeQuotients G) ×ˢ
          (edgeQuotients G ×ˢ edgeQuotients G)).filter
            (fun q => quotientWalkEval q = a / a')).card := by
      refine Finset.card_le_card_of_injOn (walkQuotientLabels a a') ?_ ?_
      · intro w hw'
        have hwdata := fourWalks_mem_data hw'
        exact Finset.mem_filter.mpr
          ⟨walkQuotientLabels_mem hw',
            quotientWalkEval_labels (hA0 _ hwdata.1)
              (hB0 _ hwdata.2.1) (hB0 _ hwdata.2.2.1)⟩
      · intro w hw' v _ heq
        have hwdata := fourWalks_mem_data hw'
        exact walkQuotientLabels_injective_at
          (hA0 _ (hS ha)) (hA0 _ hwdata.1) (hB0 _ hwdata.2.1) heq
    exact (hw a ha a' ha').trans (Nat.cast_le.mpr hc)
  exact expansion_bound_of_card_mul_le
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hn hV hD hcount

theorem exists_simultaneous_small_difference_quotient
    (A B : Finset F) (G : Finset (F × F)) (hG : G ⊆ A ×ˢ B)
    (hA0 : ∀ a ∈ A, a ≠ 0) (hB0 : ∀ b ∈ B, b ≠ 0)
    {n V : ℝ} (hn : 0 < n) (hV : 2 ≤ V)
    (hA : (A.card : ℝ) ≤ V * n) (hB : (B.card : ℝ) ≤ V * n)
    (hE : n ^ 2 / V ≤ (G.card : ℝ))
    (hD : ((edgeDifferences G).card : ℝ) ≤ V * n)
    (hQ : ((edgeQuotients G).card : ℝ) ≤ V * n) :
    ∃ S : Finset F, S ⊆ A ∧
      3 * n / (8 * V ^ 2) ≤ (S.card : ℝ) ∧
      (S.card : ℝ) ≤ V * n ∧
      ((S - S).card : ℝ) ≤ 2 ^ 20 * V ^ 22 * n ∧
      ((S / S).card : ℝ) ≤ 2 ^ 20 * V ^ 22 * n := by
  obtain ⟨S, hS, hScard, hw⟩ :=
    exists_many_fourWalks A B G hG hn hV hA hB hE
  exact ⟨S, hS, hScard,
    (Nat.cast_le.mpr (Finset.card_le_card hS)).trans hA,
    difference_bound_of_many_fourWalks A B G S hn hV hD hw,
    quotient_bound_of_many_fourWalks A B G S hS hA0 hB0 hn hV hQ hw⟩

end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_PrunedContradiction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence
noncomputable section
open scoped Pointwise
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem pruned_incidence_impossible
    (P : Finset (ProjectivePoint F)) (L : Finset (ProjectiveLine F))
    (r U : ℝ) (hr : 0 < r) (hrq : r ^ 2 = (Fintype.card F : ℝ))
    (hU : 2 ≤ U) (hlarge : 4096 * U ^ 7 ≤ r)
    (hremove : (96 / witnessConstant) * U ^ 42 ≤ r)
    (hfirst : 32 * (graphScale U) ^ 2 * (expansionScale (graphScale U)) ^ 127942 < 3 * r)
    (hsecond : 4096 * (graphScale U) ^ 6 * (expansionScale (graphScale U)) ^ 3 < 27 * r)
    (hthird : 2 * (expansionScale (graphScale U)) ^ 527 * graphScale U ≤ r)
    (hproper : ∀ M : Subfield F, M ≠ ⊤ →
      (Nat.card M : ℝ) ^ 3 ≤ (Fintype.card F : ℝ))
    (hPlo : r ^ 2 / (32 * U ^ 4) ≤ (P.card : ℝ))
    (hPup : (P.card : ℝ) ≤ U * r ^ 2)
    (hLup : (L.card : ℝ) ≤ U * r ^ 2)
    (hpoints : ∀ p ∈ P, r / (8 * U ^ 2) ≤
      ((L.filter fun l => ProjectiveIncidence p l).card : ℝ))
    (hlines : ∀ l ∈ L, r / (8 * U ^ 2) ≤
      ((P.filter fun p => ProjectiveIncidence p l).card : ℝ))
    (hmax : ∀ p ∈ P, ((L.filter fun l => ProjectiveIncidence p l).card : ℝ) ≤
      16 * U ^ 3 * r)
    (hcap : ∀ l, ((P.filter fun p => ProjectiveIncidence p l).card : ℝ) ≤
      16 * U ^ 3 * r) : False := by
  classical
  obtain ⟨c, hc, hwitnesses⟩ := fourAnchors_of_pruned_r P L hr hU hlarge
    hPlo hPup hLup hpoints hlines (fun l _ => hcap l)
  rcases c with ⟨ell, triple, p4⟩
  rcases triple with ⟨p1, p2, p3⟩
  obtain ⟨hell, hp1, hp2, hp3, hp4, hi1, hi2, hi3, hnot4, h21, h31, h32⟩ :=
    (mem_anchorConfigurations ProjectiveIncidence P L
      ⟨ell, (⟨p1, p2, p3⟩, p4)⟩).mp hc
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ :=
    exists_projectiveTransform_normalization h21.symm h31.symm h32.symm hi1 hi2 hi3 hnot4
  let W := anchorWitnesses ProjectiveIncidence P L ⟨ell, (⟨p1, p2, p3⟩, p4)⟩
  have hWP : W ⊆ P := by
    intro w hw
    exact (Finset.mem_filter.mp hw).1
  have hj {w p : ProjectivePoint F}
      (h : p ∈ joinedNeighbors ProjectiveIncidence P L w) :
      ∃ l ∈ L, ProjectiveIncidence p l ∧ ProjectiveIncidence w l := by
    simp only [joinedNeighbors, Finset.mem_filter] at h
    obtain ⟨_, _, l, hl, hwl, hpl⟩ := h
    exact ⟨l, hl, hpl, hwl⟩
  have hjoins (w : ProjectivePoint F) (hw : w ∈ W) :
      (∃ l ∈ L, ProjectiveIncidence p1 l ∧ ProjectiveIncidence w l) ∧
      (∃ l ∈ L, ProjectiveIncidence p2 l ∧ ProjectiveIncidence w l) ∧
      (∃ l ∈ L, ProjectiveIncidence p3 l ∧ ProjectiveIncidence w l) ∧
      (∃ l ∈ L, ProjectiveIncidence p4 l ∧ ProjectiveIncidence w l) := by
    have hh := (Finset.mem_filter.mp hw).2
    exact ⟨hj hh.1, hj hh.2.1, hj hh.2.2.1, hj hh.2.2.2⟩
  obtain ⟨hretained, hnonzero, hleft, hright, hdiff, hquot⟩ :=
    coordinate_transfer P W L T p1 p2 p3 p4 (16 * U ^ 3 * r) hWP hcap
      (fun p hp => hmax p hp) hp1 hp2 hp3 hp4 hT1 hT2 hT3 hT4 hjoins
  let G := coordinateGraph T W
  let A := G.image Prod.fst
  let B := G.image Prod.snd
  let V := graphScale U
  let K := expansionScale V
  have hUpos : 0 < U := lt_of_lt_of_le (by norm_num) hU
  have hVpos : 0 < V := graphScale_pos hUpos
  have hV : 2 ≤ V := (graphScale_bounds hU).1
  have hK : 2 ≤ K := two_le_expansionScale hV
  have hdegree : 16 * U ^ 3 * r ≤ V * r :=
    mul_le_mul_of_nonneg_right (graphScale_bounds hU).2 hr.le
  have hGcard : r ^ 2 / V ≤ (G.card : ℝ) :=
    retained_witness_lower r U W.card G.card hr hU hwitnesses hretained hremove
  have hG : G ⊆ A ×ˢ B := by
    intro z hz
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem Prod.fst hz, Finset.mem_image_of_mem Prod.snd hz⟩
  have hA0 (a : F) (ha : a ∈ A) : a ≠ 0 := by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ha
    exact (hnonzero z hz).1
  have hB0 (b : F) (hb : b ∈ B) : b ≠ 0 := by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hb
    exact (hnonzero z hz).2
  obtain ⟨S, hSA, hSlo, hShi, hSdiff, hSquot⟩ :=
    exists_simultaneous_small_difference_quotient A B G hG hA0 hB0 hr hV
      (hleft.trans hdegree) (hright.trans hdegree) hGcard
      (hdiff.trans hdegree) (hquot.trans hdegree)
  have hS0 : (0 : F) ∉ S := by
    intro h
    exact hA0 0 (hSA h) rfl
  have hexpand : 2 ^ 20 * V ^ 22 * r ≤ K * (S.card : ℝ) :=
    extraction_expansion_le r V S.card hr.le hVpos hSlo
  exact extracted_set_contradiction S r V K hS0 hK hVpos hr hrq
    (hSdiff.trans hexpand) (hSquot.trans hexpand) hproper hSlo hShi
    hfirst hsecond hthird

end
end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_PruningHigh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Incidence

variable {Pt Ln : Type*} [instDecidableEqPt : DecidableEq Pt] [instDecidableEqLn : DecidableEq Ln]

theorem high_degree_sum_le {A : Type*} (S : Finset A) (deg : A → ℕ)
    {H B : ℝ} (hH : 0 < H) (hB : (∑ a ∈ S, (deg a : ℝ) ^ 2) ≤ B) :
    (∑ a ∈ S.filter (fun a => ¬ (deg a : ℝ) ≤ H), (deg a : ℝ)) ≤ B / H := by
  classical
  apply (le_div_iff₀ hH).2
  rw [Finset.sum_mul]
  calc
    (∑ a ∈ S.filter (fun a => ¬ (deg a : ℝ) ≤ H), (deg a : ℝ) * H) ≤
        ∑ a ∈ S.filter (fun a => ¬ (deg a : ℝ) ≤ H), (deg a : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      have hlarge := (Finset.mem_filter.mp ha).2
      have hnonneg : 0 ≤ (deg a : ℝ) := Nat.cast_nonneg _
      nlinarith [lt_of_not_ge hlarge]
    _ ≤ ∑ a ∈ S, (deg a : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by
        intro a _ _
        exact sq_nonneg _)
    _ ≤ B := hB

theorem high_degree_truncation (R : Pt → Ln → Prop) (P : Finset Pt) (L : Finset Ln)
    {H BP BL : ℝ} (hH : 0 < H)
    (hBP : (∑ p ∈ P, (leftDegree R L p : ℝ) ^ 2) ≤ BP)
    (hBL : (∑ l ∈ L, (rightDegree R P l : ℝ) ^ 2) ≤ BL) :
    let P₀ := P.filter (fun p => (leftDegree R L p : ℝ) ≤ H)
    let L₀ := L.filter (fun l => (rightDegree R P l : ℝ) ≤ H)
    (incidenceCount R P L : ℝ) - BP / H - BL / H ≤ (incidenceCount R P₀ L₀ : ℝ) := by
  classical
  dsimp only
  let P₀ := P.filter (fun p => (leftDegree R L p : ℝ) ≤ H)
  let L₀ := L.filter (fun l => (rightDegree R P l : ℝ) ≤ H)
  let Pbad := P.filter (fun p => ¬ (leftDegree R L p : ℝ) ≤ H)
  let Lbad := L.filter (fun l => ¬ (rightDegree R P l : ℝ) ≤ H)
  have hleft : (incidenceCount R P₀ L : ℝ) +
      (∑ p ∈ Pbad, (leftDegree R L p : ℝ)) = (incidenceCount R P L : ℝ) := by
    simpa only [P₀, Pbad, incidenceCount, Nat.cast_sum] using
      Finset.sum_filter_add_sum_filter_not P
        (fun p => (leftDegree R L p : ℝ) ≤ H) (fun p => (leftDegree R L p : ℝ))
  have hright : (incidenceCount R P₀ L₀ : ℝ) +
      (∑ l ∈ Lbad, (rightDegree R P₀ l : ℝ)) = (incidenceCount R P₀ L : ℝ) := by
    rw [incidenceCount_swap R P₀ L₀, incidenceCount_swap R P₀ L]
    simpa only [L₀, Lbad, incidenceCount, rightDegree, Nat.cast_sum] using
      Finset.sum_filter_add_sum_filter_not L
        (fun l => (rightDegree R P l : ℝ) ≤ H) (fun l => (rightDegree R P₀ l : ℝ))
  have hbadP : (∑ p ∈ Pbad, (leftDegree R L p : ℝ)) ≤ BP / H :=
    high_degree_sum_le P (leftDegree R L) hH hBP
  have hbadL : (∑ l ∈ Lbad, (rightDegree R P₀ l : ℝ)) ≤ BL / H := by
    calc
      _ ≤ ∑ l ∈ Lbad, (rightDegree R P l : ℝ) := by
        apply Finset.sum_le_sum
        intro l _
        exact_mod_cast rightDegree_mono R (Finset.filter_subset _ _) l
      _ ≤ BL / H := high_degree_sum_le L (rightDegree R P) hH hBL
  change (incidenceCount R P L : ℝ) - BP / H - BL / H ≤
    (incidenceCount R P₀ L₀ : ℝ)
  linarith

theorem exists_pruned_core (R : Pt → Ln → Prop) (P : Finset Pt) (L : Finset Ln)
    {d H BP BL : ℝ} (hd : 0 ≤ d) (hH : 0 < H)
    (hBP : (∑ p ∈ P, (leftDegree R L p : ℝ) ^ 2) ≤ BP)
    (hBL : (∑ l ∈ L, (rightDegree R P l : ℝ) ^ 2) ≤ BL) :
    ∃ P' : Finset Pt, P' ⊆ P ∧ ∃ L' : Finset Ln, L' ⊆ L ∧
      MinimumDegrees R d P' L' ∧
      (∀ p ∈ P', (leftDegree R L' p : ℝ) ≤ H) ∧
      (∀ l ∈ L', (rightDegree R P' l : ℝ) ≤ H) ∧
      (incidenceCount R P L : ℝ) - BP / H - BL / H -
        d * ((P.card : ℝ) + (L.card : ℝ)) ≤ (incidenceCount R P' L' : ℝ) := by
  classical
  let P₀ := P.filter (fun p => (leftDegree R L p : ℝ) ≤ H)
  let L₀ := L.filter (fun l => (rightDegree R P l : ℝ) ≤ H)
  have hP₀ : P₀ ⊆ P := Finset.filter_subset _ _
  have hL₀ : L₀ ⊆ L := Finset.filter_subset _ _
  obtain ⟨P', hP', L', hL', hmin, hpot⟩ := exists_degree_core R d P₀ L₀
  refine ⟨P', hP'.trans hP₀, L', hL'.trans hL₀, hmin, ?_, ?_, ?_⟩
  · intro p hp
    have hdeg := (Finset.mem_filter.mp (hP' hp)).2
    have hmono : (leftDegree R L' p : ℝ) ≤ (leftDegree R L p : ℝ) := by
      exact_mod_cast leftDegree_mono R (hL'.trans hL₀) p
    exact hmono.trans hdeg
  · intro l hl
    have hdeg := (Finset.mem_filter.mp (hL' hl)).2
    have hmono : (rightDegree R P' l : ℝ) ≤ (rightDegree R P l : ℝ) := by
      exact_mod_cast rightDegree_mono R (hP'.trans hP₀) l
    exact hmono.trans hdeg
  · have hhigh := high_degree_truncation R P L hH hBP hBL
    change (incidenceCount R P L : ℝ) - BP / H - BL / H ≤
      (incidenceCount R P₀ L₀ : ℝ) at hhigh
    have hlow := degree_core_incidence_lower_bound R hd P₀ P' L₀ L' hpot
    have hcardP : (P₀.card : ℝ) ≤ (P.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hP₀
    have hcardL : (L₀.card : ℝ) ≤ (L.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hL₀
    have hcharge := mul_le_mul_of_nonneg_left (add_le_add hcardP hcardL) hd
    linarith

end RyserCoveringCounterexample.Incidence

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_PruningNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence

theorem upperDegreeCutoff_pos {U q : ℝ} (hU : 0 < U) (hq : 0 < q) :
    0 < upperDegreeCutoff U q :=
  mul_pos (mul_pos (by norm_num) (pow_pos hU _)) (Real.sqrt_pos.mpr hq)

theorem lowerDegreeCutoff_pos {U q : ℝ} (hU : 0 < U) (hq : 0 < q) :
    0 < lowerDegreeCutoff U q :=
  div_pos (Real.sqrt_pos.mpr hq) (mul_pos (by norm_num) (pow_pos hU _))

private theorem pruning_budget_identity (U q t : ℝ) (hU : U ≠ 0) (ht : t ≠ 0)
    (hsq : t ^ 2 = q) :
    q * t / U - (2 * U ^ 2 * q ^ 2) / (16 * U ^ 3 * t) -
      (2 * U ^ 2 * q ^ 2) / (16 * U ^ 3 * t) -
      (t / (8 * U ^ 2)) * (2 * U * q) = q * t / (2 * U) := by
  rw [← hsq]
  field_simp [hU, ht]
  ring

theorem pruning_budget_exact {U q : ℝ} (hU : 0 < U) (hq : 0 < q) :
    q * Real.sqrt q / U - (2 * U ^ 2 * q ^ 2) / upperDegreeCutoff U q -
      (2 * U ^ 2 * q ^ 2) / upperDegreeCutoff U q -
      lowerDegreeCutoff U q * (2 * U * q) = q * Real.sqrt q / (2 * U) := by
  exact pruning_budget_identity U q (Real.sqrt q) hU.ne'
    (Real.sqrt_pos.mpr hq).ne' (Real.sq_sqrt hq.le)

theorem pruned_card_ratio {U q : ℝ} (hU : 0 < U) (hq : 0 < q) :
    (q * Real.sqrt q / (2 * U)) / upperDegreeCutoff U q = q / (32 * U ^ 4) := by
  have ht := (Real.sqrt_pos.mpr hq).ne'
  have hU' := hU.ne'
  unfold upperDegreeCutoff
  field_simp [hU', ht]
  ring

theorem cutoff_product {U q : ℝ} (hU : 0 < U) (hq : 0 ≤ q) :
    upperDegreeCutoff U q * lowerDegreeCutoff U q = 2 * U * q := by
  have hU' := hU.ne'
  unfold upperDegreeCutoff lowerDegreeCutoff
  calc
    16 * U ^ 3 * Real.sqrt q * (Real.sqrt q / (8 * U ^ 2)) =
        2 * U * (Real.sqrt q) ^ 2 := by
      field_simp [hU']
      ring
    _ = 2 * U * q := by rw [Real.sq_sqrt hq]

theorem all_line_cap_numeric {U q n : ℝ} (hU : 0 < U) (hq : 0 < q)
    (hd : 2 ≤ lowerDegreeCutoff U q) (hn : n ≤ U * q) :
    n / (lowerDegreeCutoff U q - 1) ≤ upperDegreeCutoff U q := by
  have hH := upperDegreeCutoff_pos hU hq
  have hproduct := cutoff_product hU hq.le
  have hhalf : upperDegreeCutoff U q ≤ U * q := by nlinarith
  apply (div_le_iff₀ (show 0 < lowerDegreeCutoff U q - 1 by linarith)).2
  nlinarith

end RyserCoveringCounterexample.Incidence

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_Pruning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Incidence

variable {Pt Ln : Type*} [instDecidableEqPt : DecidableEq Pt] [instDecidableEqLn : DecidableEq Ln]

theorem incidenceCount_le_card_mul (R : Pt → Ln → Prop) (P : Finset Pt)
    (L : Finset Ln) : incidenceCount R P L ≤ P.card * L.card := let _ := instDecidableEqPt; let _ := instDecidableEqLn; by
  calc
    incidenceCount R P L ≤ ∑ p ∈ P, L.card := by
      apply Finset.sum_le_sum
      intro p _
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = P.card * L.card := by simp

theorem incidenceCount_le_card_mul_max (R : Pt → Ln → Prop) (P : Finset Pt)
    (L : Finset Ln) {H : ℝ} (hmax : ∀ p ∈ P, (leftDegree R L p : ℝ) ≤ H) :
    (incidenceCount R P L : ℝ) ≤ (P.card : ℝ) * H := let _ := instDecidableEqPt; let _ := instDecidableEqLn; by
  calc
    (incidenceCount R P L : ℝ) = ∑ p ∈ P, (leftDegree R L p : ℝ) := by
      simp only [incidenceCount, Nat.cast_sum]
    _ ≤ ∑ p ∈ P, H := Finset.sum_le_sum hmax
    _ = (P.card : ℝ) * H := by simp

variable {F : Type*} [Field F] [DecidableEq F]

theorem exists_projective_pruning_sqrt (P : Finset (ProjectivePoint F))
    (L : Finset (ProjectiveLine F)) {U q : ℝ} (hU : 2 ≤ U) (hq : 0 < q)
    (hd : 2 ≤ lowerDegreeCutoff U q)
    (hP : (P.card : ℝ) ≤ U * q) (hL : (L.card : ℝ) ≤ U * q)
    (hI : q * Real.sqrt q / U ≤ (incidenceCount ProjectiveIncidence P L : ℝ)) :
    ∃ P' : Finset (ProjectivePoint F), P' ⊆ P ∧
      ∃ L' : Finset (ProjectiveLine F), L' ⊆ L ∧
        q * Real.sqrt q / (2 * U) ≤ (incidenceCount ProjectiveIncidence P' L' : ℝ) ∧
        q / (32 * U ^ 4) ≤ (P'.card : ℝ) ∧
        q / (32 * U ^ 4) ≤ (L'.card : ℝ) ∧
        (P'.card : ℝ) ≤ U * q ∧ (L'.card : ℝ) ≤ U * q ∧
        MinimumDegrees ProjectiveIncidence (lowerDegreeCutoff U q) P' L' ∧
        (∀ p ∈ P', (leftDegree ProjectiveIncidence L' p : ℝ) ≤ upperDegreeCutoff U q) ∧
        (∀ l ∈ L', (rightDegree ProjectiveIncidence P' l : ℝ) ≤ upperDegreeCutoff U q) ∧
        (∀ l : ProjectiveLine F,
          (rightDegree ProjectiveIncidence P' l : ℝ) ≤ upperDegreeCutoff U q) := by
  classical
  have hUpos : 0 < U := lt_of_lt_of_le (by norm_num) hU
  have hUq : 0 ≤ U * q := mul_nonneg hUpos.le hq.le
  have hIcard : (incidenceCount ProjectiveIncidence P L : ℝ) ≤
      (P.card : ℝ) * (L.card : ℝ) := by
    exact_mod_cast incidenceCount_le_card_mul ProjectiveIncidence P L
  have hprod : (P.card : ℝ) * (L.card : ℝ) ≤ (U * q) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hP hL (Nat.cast_nonneg _) hUq
  have hPsq : (P.card : ℝ) ^ 2 ≤ (U * q) ^ 2 :=
    (sq_le_sq₀ (Nat.cast_nonneg _) hUq).2 hP
  have hLsq : (L.card : ℝ) ^ 2 ≤ (U * q) ^ 2 :=
    (sq_le_sq₀ (Nat.cast_nonneg _) hUq).2 hL
  have hBP : (∑ p ∈ P, (leftDegree ProjectiveIncidence L p : ℝ) ^ 2) ≤
      2 * U ^ 2 * q ^ 2 := by
    have hs := sum_projective_leftDegree_sq_le P L
    nlinarith
  have hBL : (∑ l ∈ L, (rightDegree ProjectiveIncidence P l : ℝ) ^ 2) ≤
      2 * U ^ 2 * q ^ 2 := by
    have hs := sum_projective_rightDegree_sq_le P L
    nlinarith
  have hHpos := upperDegreeCutoff_pos hUpos hq
  have hdpos := lowerDegreeCutoff_pos hUpos hq
  obtain ⟨P', hP', L', hL', hmin, hmaxP, hmaxL, hloss⟩ :=
    exists_pruned_core ProjectiveIncidence P L hdpos.le hHpos hBP hBL
  have hPbound : (P'.card : ℝ) ≤ U * q := by
    have hsub : (P'.card : ℝ) ≤ (P.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hP'
    exact hsub.trans hP
  have hLbound : (L'.card : ℝ) ≤ U * q := by
    have hsub : (L'.card : ℝ) ≤ (L.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hL'
    exact hsub.trans hL
  have hIbound : q * Real.sqrt q / (2 * U) ≤
      (incidenceCount ProjectiveIncidence P' L' : ℝ) := by
    have hcharge := mul_le_mul_of_nonneg_left (add_le_add hP hL) hdpos.le
    have hbudget := pruning_budget_exact hUpos hq
    linarith
  have hPcard : q / (32 * U ^ 4) ≤ (P'.card : ℝ) := by
    rw [← pruned_card_ratio hUpos hq]
    apply (div_le_iff₀ hHpos).2
    exact hIbound.trans (incidenceCount_le_card_mul_max ProjectiveIncidence P' L' hmaxP)
  have hLcard : q / (32 * U ^ 4) ≤ (L'.card : ℝ) := by
    rw [← pruned_card_ratio hUpos hq]
    apply (div_le_iff₀ hHpos).2
    have hswap : (incidenceCount ProjectiveIncidence P' L' : ℝ) =
        (incidenceCount (fun l p => ProjectiveIncidence p l) L' P' : ℝ) := by
      rw [incidenceCount_swap]
    rw [hswap] at hIbound
    exact hIbound.trans (incidenceCount_le_card_mul_max
      (fun l p => ProjectiveIncidence p l) L' P' hmaxL)
  refine ⟨P', hP', L', hL', hIbound, hPcard, hLcard, hPbound, hLbound,
    hmin, hmaxP, hmaxL, ?_⟩
  intro l
  exact (projective_all_line_cap P' L' (by linarith) hmin.1 l).trans
    (all_line_cap_numeric hUpos hq hd hLbound)

theorem exists_projective_pruning (P : Finset (ProjectivePoint F))
    (L : Finset (ProjectiveLine F)) {U q r : ℝ} (hU : 2 ≤ U) (hq : 0 < q)
    (hsq : r ^ 2 = q) (hr : 16 * U ^ 2 ≤ r)
    (hP : (P.card : ℝ) ≤ U * q) (hL : (L.card : ℝ) ≤ U * q)
    (hI : q * r / U ≤ (incidenceCount ProjectiveIncidence P L : ℝ)) :
    ∃ P' : Finset (ProjectivePoint F), P' ⊆ P ∧
      ∃ L' : Finset (ProjectiveLine F), L' ⊆ L ∧
        q * r / (2 * U) ≤ (incidenceCount ProjectiveIncidence P' L' : ℝ) ∧
        q / (32 * U ^ 4) ≤ (P'.card : ℝ) ∧
        q / (32 * U ^ 4) ≤ (L'.card : ℝ) ∧
        (P'.card : ℝ) ≤ U * q ∧ (L'.card : ℝ) ≤ U * q ∧
        MinimumDegrees ProjectiveIncidence (r / (8 * U ^ 2)) P' L' ∧
        (∀ p ∈ P', (leftDegree ProjectiveIncidence L' p : ℝ) ≤ 16 * U ^ 3 * r) ∧
        (∀ l ∈ L', (rightDegree ProjectiveIncidence P' l : ℝ) ≤ 16 * U ^ 3 * r) ∧
        (∀ l : ProjectiveLine F, (rightDegree ProjectiveIncidence P' l : ℝ) ≤
          16 * U ^ 3 * r) := by
  have hUpos : 0 < U := lt_of_lt_of_le (by norm_num) hU
  have hrnonneg : 0 ≤ r := (mul_nonneg (by norm_num) (sq_nonneg U)).trans hr
  have hsqrt : Real.sqrt q = r := (Real.sqrt_eq_iff_eq_sq hq.le hrnonneg).2 hsq.symm
  have hd : 2 ≤ lowerDegreeCutoff U q := by
    unfold lowerDegreeCutoff
    rw [hsqrt]
    apply (le_div_iff₀ (mul_pos (by norm_num) (pow_pos hUpos 2))).2
    nlinarith
  have hI' : q * Real.sqrt q / U ≤ (incidenceCount ProjectiveIncidence P L : ℝ) := by
    simpa only [hsqrt] using hI
  simpa only [lowerDegreeCutoff, upperDegreeCutoff, hsqrt] using
    exists_projective_pruning_sqrt P L hU hq hd hP hL hI'

end RyserCoveringCounterexample.Incidence

end

end OAI
end

section
-- module Solutions.OAIW2_RyserCov.Ryser_Incidence_Uniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RyserCoveringCounterexample.Incidence
noncomputable section

theorem cardinality_scale_eq {q : ℝ} (hq : 0 < q) :
    q ^ (1 + savingExponent) = densityScale q * q := by
  rw [Real.rpow_add hq, Real.rpow_one]
  exact mul_comm _ _

theorem incidence_scale_eq {q : ℝ} (hq : 0 < q) :
    q ^ ((3 : ℝ) / 2 - savingExponent) = q * Real.sqrt q / densityScale q := by
  rw [Real.rpow_sub hq]
  congr 1
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hq,
    Real.rpow_one, Real.sqrt_eq_rpow]

theorem uniform_incidence_bound_oai (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hq : incidenceThreshold ≤ Fintype.card F) (hsub : SmallProperSubfields F)
    (P : Finset (ProjectivePoint F)) (L : Finset (ProjectiveLine F))
    (hP : (P.card : ℝ) ≤ (Fintype.card F : ℝ) ^ (1 + savingExponent))
    (hL : (L.card : ℝ) ≤ (Fintype.card F : ℝ) ^ (1 + savingExponent)) :
    (incidenceCount ProjectiveIncidence P L : ℝ) ≤
      (Fintype.card F : ℝ) ^ ((3 : ℝ) / 2 - savingExponent) := by
  classical
  let q : ℝ := Fintype.card F
  let U := densityScale q
  let r := Real.sqrt q
  obtain ⟨hqpos, hU, hdegree, hlarge, hremove, hfirst, hsecond, hthird⟩ :=
    largeEnough_of_threshold hq
  have hr : 0 < r := Real.sqrt_pos.2 hqpos
  have hrq : r ^ 2 = q := Real.sq_sqrt hqpos.le
  have hP' : (P.card : ℝ) ≤ U * q := by
    simpa only [cardinality_scale_eq hqpos] using hP
  have hL' : (L.card : ℝ) ≤ U * q := by
    simpa only [cardinality_scale_eq hqpos] using hL
  by_contra hnot
  have hI : q * r / U ≤ (incidenceCount ProjectiveIncidence P L : ℝ) := by
    have hstrict := lt_of_not_ge hnot
    rw [incidence_scale_eq hqpos] at hstrict
    exact hstrict.le
  obtain ⟨P', _, L', _, _, hPlo, _, hPup, hLup, hmin, hmax, _, hcap⟩ :=
    exists_projective_pruning P L hU hqpos hrq hdegree hP' hL' hI
  have hproper : ∀ M : Subfield F, M ≠ ⊤ →
      (Nat.card M : ℝ) ^ 3 ≤ (Fintype.card F : ℝ) := by
    intro M hM
    exact_mod_cast hsub M hM
  have hleft (p : ProjectivePoint F) : leftDegree ProjectiveIncidence L' p =
      (L'.filter fun l => ProjectiveIncidence p l).card := by
    unfold leftDegree
    apply congrArg Finset.card
    ext l
    simp only [Finset.mem_filter]
  have hright (l : ProjectiveLine F) : rightDegree ProjectiveIncidence P' l =
      (P'.filter fun p => ProjectiveIncidence p l).card := by
    unfold rightDegree leftDegree
    apply congrArg Finset.card
    ext p
    simp only [Finset.mem_filter]
  apply pruned_incidence_impossible P' L' r U hr hrq hU hlarge hremove
    hfirst hsecond hthird hproper
  · simpa only [hrq] using hPlo
  · simpa only [hrq] using hPup
  · simpa only [hrq] using hLup
  · intro p hp
    simpa only [hleft] using hmin.1 p hp
  · intro l hl
    simpa only [hright] using hmin.2 l hl
  · intro p hp
    simpa only [hleft] using hmax p hp
  · intro l
    simpa only [hright] using hcap l

end
end RyserCoveringCounterexample.Incidence

end OAI
end

theorem solution.{u_1} : type_of% @OAI.RyserCoveringCounterexample.Incidence.uniform_incidence_bound_oai.{u_1} := @OAI.RyserCoveringCounterexample.Incidence.uniform_incidence_bound_oai.{u_1}
