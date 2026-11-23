-- Prove2me | solution 1 for MultiAccessLogspace.Halting.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T04:01:55.762888+00:00
-- url     : https://prove2.me/submissions/8c0ceb44-2301-4664-ad4b-c89625ec30f7

import Mathlib
import Definitions.Def_MultiAccessLogspace_Halting_Rulers

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MultiAccessLogspace.Halting

private def hcWindow (h : List ℕ) (j : ℕ) : Finset ℕ :=
  (Finset.Icc (lastGreater h j + 1) j).filter fun k => entry h k = entry h j

private lemma entry_append_right (p q : List ℕ) {k : ℕ} (hk : 1 ≤ k) :
    entry (p ++ q) (p.length + k) = entry q k := by
  unfold entry
  rw [List.getD_append_right p q 0 (p.length + k - 1) (by omega)]
  have he : p.length + k - 1 - p.length = k - 1 := by omega
  rw [he]

private lemma entry_append_left (p q : List ℕ) {k : ℕ} (hk : 1 ≤ k) (hkp : k ≤ p.length) :
    entry (p ++ q) k = entry p k := by
  unfold entry
  rw [List.getD_append p q 0 (k - 1) (by omega)]

private lemma le_lastGreater (h : List ℕ) {i j : ℕ} (hi : i ∈ Finset.Icc 1 j)
    (hgt : entry h j < entry h i) : i ≤ lastGreater h j := by
  unfold lastGreater
  exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨hi, hgt⟩)

private lemma hcWindow_prefix (p q : List ℕ) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ p.length) :
    hcWindow (p ++ q) j = hcWindow p j := by
  unfold hcWindow
  have hlg : lastGreater (p ++ q) j = lastGreater p j := by
    unfold lastGreater
    have hsets : (Finset.Icc 1 j).filter (fun k => entry (p ++ q) j < entry (p ++ q) k) =
        (Finset.Icc 1 j).filter (fun k => entry p j < entry p k) := by
      apply Finset.filter_congr
      intro i hi
      have hiI := Finset.mem_Icc.mp hi
      rw [entry_append_left p q hiI.1 (by omega), entry_append_left p q hj1 hj]
    rw [hsets]
  rw [hlg]
  apply Finset.filter_congr
  intro k hk
  have hkI := Finset.mem_Icc.mp hk
  rw [entry_append_left p q (by omega) (by omega), entry_append_left p q hj1 hj]

private lemma hyporulerCondition_prefix {b : ℕ} {p q : List ℕ}
    (hc : HyporulerCondition b (p ++ q)) : HyporulerCondition b p := by
  intro j hj
  have hjI := Finset.mem_Icc.mp hj
  have hjp : j ≤ p.length := hjI.2
  have hjlen : j ≤ (p ++ q).length := by simp only [List.length_append]; omega
  have hq := hc j (Finset.mem_Icc.mpr ⟨hjI.1, hjlen⟩)
  change (hcWindow (p ++ q) j).card ≤ b - 1 at hq
  change (hcWindow p j).card ≤ b - 1
  rw [hcWindow_prefix p q hjI.1 hjp] at hq
  exact hq

private lemma card_range_filter_getD (h : List ℕ) (a : ℕ) :
    ((Finset.range h.length).filter fun k => h.getD k 0 = a).card = h.count a := by
  classical
  induction h using List.reverseRecOn with
  | nil => simp
  | append_singleton h x ih =>
      calc
        ((Finset.range (h ++ [x]).length).filter fun k => (h ++ [x]).getD k 0 = a).card
            = ∑ k ∈ Finset.range (h.length + 1), if (h ++ [x]).getD k 0 = a then 1 else 0 := by
              simp only [List.length_append, List.length_singleton, Finset.card_filter]
        _ = (∑ k ∈ Finset.range h.length, if (h ++ [x]).getD k 0 = a then 1 else 0) +
                if (h ++ [x]).getD h.length 0 = a then 1 else 0 := Finset.sum_range_succ _ _
        _ = (∑ k ∈ Finset.range h.length, if h.getD k 0 = a then 1 else 0) + if x = a then 1 else 0 := by
              congr 1
              · apply Finset.sum_congr rfl
                intro k hk
                rw [List.getD_append h [x] 0 k (Finset.mem_range.mp hk)]
              · rw [List.getD_append_right h [x] 0 h.length (by omega)]; simp
        _ = ((Finset.range h.length).filter fun k => h.getD k 0 = a).card + if x = a then 1 else 0 := by rw [Finset.card_filter]
        _ = h.count a + if x = a then 1 else 0 := by rw [ih]
        _ = (h ++ [x]).count a := by
              simp only [List.count_append]; congr 1
              by_cases hx : x = a
              · subst x; simp
              · simp [hx]

private lemma card_indices (h : List ℕ) (a : ℕ) :
    ((Finset.Icc 1 h.length).filter fun k => entry h k = a).card = h.count a := by
  classical
  rw [← card_range_filter_getD h a]
  apply Finset.card_bij (fun k _ => k - 1)
  · intro k hk
    have hk' := Finset.mem_filter.mp hk
    have hkI := Finset.mem_Icc.mp hk'.1
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by omega), hk'.2⟩
  · intro k hk l hl hkl
    have hkI := Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1
    have hlI := Finset.mem_Icc.mp (Finset.mem_filter.mp hl).1
    omega
  · intro k hk
    have hk' := Finset.mem_filter.mp hk
    have hkI := Finset.mem_range.mp hk'.1
    refine ⟨k + 1, ?_, by omega⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hk'.2⟩

private lemma count_le_of_condition_max {b a : ℕ} :
    ∀ {h : List ℕ}, HyporulerCondition b h → (∀ x ∈ h, x ≤ a) → h.count a ≤ b - 1 := by
  intro h
  induction h using List.reverseRecOn with
  | nil => intro _ _; simp
  | append_singleton h x ih =>
      intro hc hmax
      have hmaxh : ∀ y ∈ h, y ≤ a := by
        intro y hy
        exact hmax y (List.mem_append_left [x] hy)
      by_cases hx : x = a
      · subst x
        have hj := hc (h ++ [a]).length (by simp)
        have heend : entry (h ++ [a]) (h ++ [a]).length = a := by
          rw [show (h ++ [a]).length = h.length + 1 by simp]
          rw [entry_append_right h [a] (k := 1) (by omega)]
          rfl
        have hlg : lastGreater (h ++ [a]) (h ++ [a]).length = 0 := by
          apply Finset.sup_eq_zero.mpr
          intro i hi
          simp only [id_eq]
          exfalso
          have hiI := Finset.mem_Icc.mp (Finset.mem_filter.mp hi).1
          have hgt := (Finset.mem_filter.mp hi).2
          have heq : entry (h ++ [a]) i = (h ++ [a])[i - 1]'(by omega) := by
            unfold entry List.getD
            simp only [List.getElem?_eq_getElem (by omega : i - 1 < (h ++ [a]).length)]
            rfl
          have he : entry (h ++ [a]) i ∈ h ++ [a] := by
            rw [heq]
            exact List.getElem_mem _
          have hle := hmax _ he
          omega
        change ((Finset.Icc (lastGreater (h ++ [a]) (h ++ [a]).length + 1) (h ++ [a]).length).filter
          fun k => entry (h ++ [a]) k = entry (h ++ [a]) (h ++ [a]).length).card ≤ b - 1 at hj
        rw [hlg] at hj
        simp only [Nat.zero_add] at hj
        rw [heend, card_indices] at hj
        exact hj
      · rw [List.count_append]
        have hcx : a ∉ [x] := by simpa [Ne.symm hx]
        have hc0 : [x].count a = 0 := List.count_eq_zero.mpr hcx
        rw [hc0, Nat.add_zero]
        exact ih (hyporulerCondition_prefix (p := h) (q := [x]) hc) hmaxh

private lemma intercalate_splitOnP_nat (sep : ℕ) (h : List ℕ) :
    List.intercalate [sep] (h.splitOnP (fun a => decide (a = sep))) = h := by
  induction h with
  | nil =>
      change List.intercalate [sep] [[]] = ([] : List ℕ)
      simp
  | cons x xs ih =>
      rw [List.splitOnP_cons]
      by_cases hx : decide (x = sep) = true
      · have hxs : x = sep := of_decide_eq_true hx
        subst x
        rw [if_pos hx]
        generalize hsp : List.splitOnP (fun a => decide (a = sep)) xs = bs at ih ⊢
        cases bs with
        | nil => exact absurd hsp (List.splitOnP_ne_nil _ _)
        | cons B bs =>
            rw [List.intercalate_cons_cons]
            simp only [List.nil_append, List.cons_append, List.cons.injEq, true_and]
            exact ih
      · have hxf : decide (x = sep) = false := Bool.eq_false_of_not_eq_true hx
        rw [if_neg hx]
        generalize hsp : List.splitOnP (fun a => decide (a = sep)) xs = bs at ih ⊢
        cases bs with
        | nil => exact absurd hsp (List.splitOnP_ne_nil _ _)
        | cons B bs =>
            cases bs with
            | nil => simpa using congrArg (List.cons x) ih
            | cons C bs =>
                simp only [List.modifyHead_cons, List.intercalate_cons_cons, List.cons_append,
                  List.cons.injEq, true_and]
                simpa only [List.intercalate_cons_cons] using ih

private lemma not_sep_of_mem_splitOnP_nat (sep : ℕ) :
    ∀ {l : List ℕ} {B : List ℕ} {a : ℕ},
      B ∈ List.splitOnP (fun x => decide (x = sep)) l → a ∈ B → a ≠ sep := by
  intro l
  induction l with
  | nil =>
      intro B a hB ha
      change B ∈ [[]] at hB
      simp at hB
      subst B
      simp at ha
  | cons x xs ih =>
      intro B a hB ha
      rw [List.splitOnP_cons] at hB
      by_cases hx : decide (x = sep) = true
      · simp only [hx, if_true, List.mem_cons] at hB
        rcases hB with hB | hB
        · subst B
          simp at ha
        · exact ih hB ha
      · have hxf : decide (x = sep) = false := Bool.eq_false_of_not_eq_true hx
        rw [if_neg hx] at hB
        generalize hsp : List.splitOnP (fun x => decide (x = sep)) xs = bs at hB
        cases bs with
        | nil => exact absurd hsp (List.splitOnP_ne_nil _ _)
        | cons C bs =>
            simp only [List.modifyHead_cons, List.mem_cons] at hB
            rcases hB with hB | hB
            · subst B
              simp only [List.mem_cons] at ha
              rcases ha with ha | ha
              · subst a
                exact of_decide_eq_false hxf
              · apply ih (B := C) (a := a) _ ha
                rw [hsp]
                exact List.mem_cons_self
            · apply ih (B := B) (a := a) _ ha
              rw [hsp]
              exact List.mem_cons_of_mem C hB

private lemma mem_intercalate_of_mem (sep : ℕ) :
    ∀ {blocks : List (List ℕ)} {B : List ℕ} {a : ℕ},
      B ∈ blocks → a ∈ B → a ∈ List.intercalate [sep] blocks := by
  intro blocks
  induction blocks with
  | nil => intro B a hB; simp at hB
  | cons C blocks ih =>
      intro B a hB ha
      cases blocks with
      | nil =>
          have hBC : B = C := by simpa using hB
          subst B
          simpa [List.intercalate] using ha
      | cons D blocks =>
          rw [List.intercalate_cons_cons]
          rcases List.mem_cons.mp hB with rfl | hB
          · exact List.mem_append_left _ (List.mem_append_left _ ha)
          · apply List.mem_append_right (C ++ [sep])
            exact ih hB ha

private lemma mem_of_mem_splitOnP_nat (sep : ℕ) {l B : List ℕ} {a : ℕ}
    (hB : B ∈ l.splitOnP (fun x => decide (x = sep))) (ha : a ∈ B) : a ∈ l := by
  rw [← intercalate_splitOnP_nat sep l]
  exact mem_intercalate_of_mem sep hB ha

private lemma intercalate_bounds (d : ℕ) :
    ∀ {blocks : List (List ℕ)}, (∀ B ∈ blocks, ∀ x ∈ B, 1 ≤ x ∧ x ≤ d) →
      ∀ x ∈ List.intercalate [d + 1] blocks, 1 ≤ x ∧ x ≤ d + 1 := by
  intro blocks
  induction blocks with
  | nil => intro _ x; simp [List.intercalate]
  | cons B blocks ih =>
      intro hB x hx
      cases blocks with
      | nil =>
          have hxB : x ∈ B := by simpa [List.intercalate] using hx
          have hx' := hB B (by simp) x hxB
          exact ⟨hx'.1, by omega⟩
      | cons C blocks =>
          rw [List.intercalate_cons_cons] at hx
          rcases List.mem_append.mp hx with hx | hx
          · rcases List.mem_append.mp hx with hx | hx
            · have hx' := hB B (by simp) x hx
              exact ⟨hx'.1, by omega⟩
            · have hx' : x = d + 1 := List.mem_singleton.mp hx
              subst x; omega
          · exact ih (fun D hD => hB D (List.mem_cons_of_mem B hD)) x hx

private lemma hyporuler_bounds {b : ℕ} :
    ∀ {d : ℕ} {h : List ℕ}, IsHyporuler b d h → ∀ a ∈ h, 1 ≤ a ∧ a ≤ d := by
  intro d
  induction d with
  | zero =>
      intro h hh
      rw [hh]
      simp
  | succ d ih =>
      intro h hh
      rcases hh with ⟨blocks, hne, hlen, hbl, rfl⟩
      exact intercalate_bounds d (fun B hB a ha => ih (hbl B hB) a ha)

private lemma entry_mem (h : List ℕ) {j : ℕ} (hj : j ∈ Finset.Icc 1 h.length) :
    entry h j ∈ h := by
  have hjI := Finset.mem_Icc.mp hj
  unfold entry
  rw [List.getD_eq_getElem h 0 (by omega)]
  exact List.getElem_mem (by omega)

private lemma count_intercalate_singleton_self (d : ℕ) (blocks : List (List ℕ))
    (hno : ∀ B ∈ blocks, ∀ a ∈ B, a ≤ d) :
    (List.intercalate [d + 1] blocks).count (d + 1) = blocks.length - 1 := by
  induction blocks with
  | nil => simp [List.intercalate]
  | cons B blocks ih =>
      have hB : B.count (d + 1) = 0 := by
        rw [List.count_eq_zero]
        intro hm
        have := hno B (by simp) _ hm
        omega
      cases blocks with
      | nil => simp [List.intercalate, hB]
      | cons C blocks =>
          have hi : (List.intercalate [d + 1] (C :: blocks)).count (d + 1) =
              (C :: blocks).length - 1 :=
            ih (fun D hD => hno D (List.mem_cons_of_mem B hD))
          rw [List.intercalate_cons_cons, List.count_append, List.count_append, hi]
          simp [hB, Nat.add_comm]

private lemma hcWindow_append_eq_right {d : ℕ} (p' q : List ℕ) :
    ∀ {j : ℕ}, 1 ≤ j → j ≤ q.length → entry q j < d + 1 →
      (hcWindow (p' ++ [d + 1] ++ q) ((p' ++ [d + 1]).length + j)).card = (hcWindow q j).card := by
  intro j hj1 hjlen hqj
  let P := (p' ++ [d + 1]).length
  let H := p' ++ [d + 1] ++ q
  have hP : 1 ≤ P := by dsimp [P]; simp
  have hsep : entry H P = d + 1 := by
    dsimp [H, P]
    rw [show (p' ++ [d + 1]).length = p'.length + 1 by simp]
    rw [List.append_assoc]
    rw [entry_append_right p' ([d + 1] ++ q) (k := 1) (by omega)]
    rfl
  have hmain : entry H (P + j) = entry q j := by
    exact entry_append_right (p' ++ [d + 1]) q hj1
  have hlg : lastGreater H (P + j) = P + lastGreater q j := by
    apply le_antisymm
    · apply Finset.sup_le
      intro i hi
      simp only [id_eq]
      have hiF := Finset.mem_filter.mp hi
      have hiI := Finset.mem_Icc.mp hiF.1
      by_cases hiP : i ≤ P
      · omega
      · have hip : P + 1 ≤ i := by omega
        obtain ⟨i', rfl⟩ : ∃ i', i = P + i' := ⟨i - P, by omega⟩
        have hi'1 : 1 ≤ i' := by omega
        have hi'le : i' ≤ j := by omega
        have hg : entry H (P + j) < entry H (P + i') := hiF.2
        rw [hmain, entry_append_right (p' ++ [d + 1]) q hi'1] at hg
        have hle := le_lastGreater q (Finset.mem_Icc.mpr ⟨hi'1, hi'le⟩) hg
        omega
    · by_cases hl : lastGreater q j = 0
      · rw [hl, Nat.add_zero]
        apply le_lastGreater H (i := P)
        · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        · rw [hmain, hsep]
          exact hqj
      · have hne : ((Finset.Icc 1 j).filter fun k => entry q j < entry q k).Nonempty := by
          by_contra hn
          have hempty : (Finset.Icc 1 j).filter (fun k => entry q j < entry q k) = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp hn
          apply hl
          unfold lastGreater
          rw [hempty]
          simp
        obtain ⟨i, hi, hisup⟩ := Finset.exists_mem_eq_sup
          ((Finset.Icc 1 j).filter fun k => entry q j < entry q k) hne id
        have hiF := Finset.mem_filter.mp hi
        have hiI := Finset.mem_Icc.mp hiF.1
        have hle : P + i ≤ lastGreater H (P + j) := by
          apply le_lastGreater H
          · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
          · rw [hmain, entry_append_right (p' ++ [d + 1]) q hiI.1]
            exact hiF.2
        change P + lastGreater q j ≤ lastGreater H (P + j)
        have hii : lastGreater q j = i := by
          unfold lastGreater
          simpa only [id_eq] using hisup
        omega
  unfold hcWindow
  change ((Finset.Icc (lastGreater H (P + j) + 1) (P + j)).filter
    fun k => entry H k = entry H (P + j)).card = ((Finset.Icc (lastGreater q j + 1) j).filter
    fun k => entry q k = entry q j).card
  rw [hlg, hmain]
  have hadd : P + lastGreater q j + 1 = P + (lastGreater q j + 1) := by omega
  rw [hadd]
  symm
  apply Finset.card_bij (fun k _ => P + k)
  · intro k hk
    have hkF := Finset.mem_filter.mp hk
    have hkI := Finset.mem_Icc.mp hkF.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    rw [entry_append_right (p' ++ [d + 1]) q (by omega)]
    exact hkF.2
  · intro k hk l hl hkl
    omega
  · intro k hk
    have hkF := Finset.mem_filter.mp hk
    have hkI := Finset.mem_Icc.mp hkF.1
    have hkP : P < k := by omega
    obtain ⟨k', rfl⟩ : ∃ k', k = P + k' := ⟨k - P, by omega⟩
    have hk'1 : 1 ≤ k' := by omega
    have hk'low : lastGreater q j + 1 ≤ k' := by omega
    have hk'le : k' ≤ j := by omega
    refine ⟨k', ?_, by omega⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hk'low, hk'le⟩, ?_⟩
    rw [entry_append_right (p' ++ [d + 1]) q hk'1] at hkF
    exact hkF.2

private lemma decompose_intercalate_entry (d : ℕ) (blocks : List (List ℕ)) :
    ∀ {j : ℕ}, 1 ≤ j → j ≤ (List.intercalate [d + 1] blocks).length →
      entry (List.intercalate [d + 1] blocks) j ≠ d + 1 →
      ∃ p B s C j', B ∈ blocks ∧
        List.intercalate [d + 1] blocks = p ++ B ++ s ++ C ∧
        (s = [] ∨ s = [d + 1]) ∧ (p = [] ∨ ∃ p', p = p' ++ [d + 1]) ∧
        1 ≤ j' ∧ j' ≤ B.length ∧ j = p.length + j' := by
  induction blocks with
  | nil => intro j hj hj'; simp at hj'; omega
  | cons B blocks ih =>
      intro j hj hj' he
      by_cases hjB : j ≤ B.length
      · cases blocks with
        | nil =>
            refine ⟨[], B, [], [], j, by simp, ?_, Or.inl rfl, Or.inl rfl, hj, hjB, by simp⟩
            simp [List.intercalate]
        | cons C blocks =>
            refine ⟨[], B, [d + 1], List.intercalate [d + 1] (C :: blocks), j, by simp, ?_, Or.inr rfl,
              Or.inl rfl, hj, hjB, by simp⟩
            simp only [List.intercalate_cons_cons]
            simp [List.append_assoc]
      · have hjge : B.length + 1 ≤ j := by omega
        obtain ⟨j', rfl⟩ : ∃ j', j = B.length + 1 + j' := ⟨j - (B.length + 1), by omega⟩
        cases blocks with
        | nil => simp [List.intercalate] at hj'; omega
        | cons C blocks =>
            have hjpos : 1 ≤ j' := by
              by_contra hn
              have hj0 : j' = 0 := by omega
              subst j'
              apply he
              rw [List.intercalate_cons_cons]
              simpa [entry] using entry_append_right B ([d + 1] ++ List.intercalate [d + 1] (C :: blocks))
                (k := 1) (by omega)
            have hjbound : j' ≤ (List.intercalate [d + 1] (C :: blocks)).length := by
              simp only [List.intercalate_cons_cons, List.length_append, List.length_cons,
                List.length_singleton, List.length_nil] at hj'
              omega
            have hetail : entry (List.intercalate [d + 1] (C :: blocks)) j' ≠ d + 1 := by
              intro hh
              apply he
              rw [List.intercalate_cons_cons]
              rw [show B.length + 1 + j' = (B ++ [d + 1]).length + j' by simp]
              rw [entry_append_right (B ++ [d + 1]) (List.intercalate [d + 1] (C :: blocks)) hjpos]
              exact hh
            obtain ⟨p, D, s, E, j'', hD, hEq, hs, hp, hj1, hj2, hjindex⟩ :=
              ih hjpos hjbound hetail
            refine ⟨B ++ [d + 1] ++ p, D, s, E, j'', List.mem_cons_of_mem B hD, ?_, hs, ?_, hj1, hj2, ?_⟩
            · rw [List.intercalate_cons_cons, hEq]
              simp [List.append_assoc]
            · right
              rcases hp with hp | hp
              · subst p
                exact ⟨B, by simp⟩
              · obtain ⟨p', rfl⟩ := hp
                exact ⟨B ++ [d + 1] ++ p', by simp [List.append_assoc]⟩
            · simp only [List.length_append, List.length_singleton] at hjindex ⊢
              omega

private lemma block_decomposition (d : ℕ) :
    ∀ {blocks : List (List ℕ)} {B : List ℕ}, B ∈ blocks →
      ∃ p s C, List.intercalate [d + 1] blocks = p ++ B ++ s ++ C ∧
        (p = [] ∨ ∃ p', p = p' ++ [d + 1]) := by
  intro blocks
  induction blocks with
  | nil => intro B hB; simp at hB
  | cons D blocks ih =>
      intro B hB
      rcases List.mem_cons.mp hB with rfl | hB
      · cases blocks with
        | nil => exact ⟨[], [], [], by simp [List.intercalate], Or.inl rfl⟩
        | cons C blocks =>
            exact ⟨[], [d + 1], List.intercalate [d + 1] (C :: blocks), by
              simp only [List.intercalate_cons_cons]; simp [List.append_assoc], Or.inl rfl⟩
      · obtain ⟨p, s, C, hEq, hp⟩ := ih hB
        have hmain : List.intercalate [d + 1] (D :: blocks) = D ++ [d + 1] ++ (p ++ B ++ s ++ C) := by
          cases blocks with
          | nil => simp at hB
          | cons E blocks => rw [List.intercalate_cons_cons, hEq]
        rcases hp with hp | hp
        · subst p
          refine ⟨D ++ [d + 1], s, C, ?_, Or.inr ⟨D, by simp⟩⟩
          simpa [List.append_assoc] using hmain
        · obtain ⟨p', rfl⟩ := hp
          refine ⟨D ++ [d + 1] ++ p' ++ [d + 1], s, C, ?_, Or.inr ⟨D ++ [d + 1] ++ p', by simp [List.append_assoc]⟩⟩
          simpa [List.append_assoc] using hmain

private lemma condition_of_intercalate {b d : ℕ} (hb : 1 ≤ b) (blocks : List (List ℕ))
    (hlen : blocks.length ≤ b) (hcond : ∀ B ∈ blocks, HyporulerCondition b B)
    (hbounds : ∀ B ∈ blocks, ∀ a ∈ B, 1 ≤ a ∧ a ≤ d) :
    HyporulerCondition b (List.intercalate [d + 1] blocks) := by
  intro j hj
  change (hcWindow (List.intercalate [d + 1] blocks) j).card ≤ b - 1
  by_cases he : entry (List.intercalate [d + 1] blocks) j = d + 1
  · have hsub : hcWindow (List.intercalate [d + 1] blocks) j ⊆
        (Finset.Icc 1 (List.intercalate [d + 1] blocks).length).filter
          fun k => entry (List.intercalate [d + 1] blocks) k = d + 1 := by
      intro k hk
      have hkF := Finset.mem_filter.mp hk
      have hkI := Finset.mem_Icc.mp hkF.1
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, le_trans hkI.2 (Finset.mem_Icc.mp hj).2⟩, hkF.2.trans he⟩
    have hc := Finset.card_le_card hsub
    rw [card_indices, count_intercalate_singleton_self d blocks
      (fun B hB a ha => (hbounds B hB a ha).2)] at hc
    exact le_trans hc (Nat.sub_le_sub_right hlen 1)
  · obtain ⟨p, B, s, C, j', hB, hEq, hs, hp, hj1, hj2, hjindex⟩ :=
      decompose_intercalate_entry d blocks (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 he
    have hlocal : j' ∈ Finset.Icc 1 B.length := Finset.mem_Icc.mpr ⟨hj1, hj2⟩
    have hentr : entry (p ++ B ++ s ++ C) (p.length + j') = entry B j' := by
      rw [show p ++ B ++ s ++ C = p ++ (B ++ (s ++ C)) by simp [List.append_assoc]]
      rw [entry_append_right p (B ++ (s ++ C)) hj1, entry_append_left B (s ++ C) hj1 hj2]
    have heB : entry B j' ≠ d + 1 := by
      intro hh
      apply he
      rw [hEq, hjindex]
      exact hentr.trans hh
    have hqj : entry B j' < d + 1 := by
      have hle := (hbounds B hB _ (entry_mem B hlocal)).2
      omega
    have hgpre : hcWindow (List.intercalate [d + 1] blocks) j = hcWindow (p ++ B) j := by
      rw [hEq, hjindex]
      rw [show p ++ B ++ s ++ C = (p ++ B) ++ (s ++ C) by simp [List.append_assoc]]
      exact hcWindow_prefix (p ++ B) (s ++ C) (by omega) (by simp only [List.length_append]; omega)
    have hcapp : (hcWindow (p ++ B) (p.length + j')).card = (hcWindow B j').card := by
      rcases hp with hp | hp
      · subst p; simp
      · obtain ⟨p', rfl⟩ := hp
        exact hcWindow_append_eq_right p' B hj1 hj2 hqj
    rw [hgpre, hjindex, hcapp]
    exact hcond B hB j' hlocal

private lemma condition_block_of_intercalate {b d : ℕ} (blocks : List (List ℕ))
    (hc : HyporulerCondition b (List.intercalate [d + 1] blocks))
    (hbounds : ∀ B ∈ blocks, ∀ a ∈ B, 1 ≤ a ∧ a ≤ d) :
    ∀ B ∈ blocks, HyporulerCondition b B := by
  intro B hB j hj
  obtain ⟨p, s, C, hEq, hp⟩ := block_decomposition d hB
  have hjI := Finset.mem_Icc.mp hj
  have hjglobal : p.length + j ∈ Finset.Icc 1 (List.intercalate [d + 1] blocks).length := by
    apply Finset.mem_Icc.mpr
    constructor
    · rcases hp with hp | hp
      · subst p; simpa using hjI.1
      · obtain ⟨p', rfl⟩ := hp
        simp only [List.length_append, List.length_singleton]
        omega
    · rw [hEq]
      simp only [List.length_append]
      omega
  have hcj := hc _ hjglobal
  change (hcWindow (List.intercalate [d + 1] blocks) (p.length + j)).card ≤ b - 1 at hcj
  change (hcWindow B j).card ≤ b - 1
  have hgpre : hcWindow (List.intercalate [d + 1] blocks) (p.length + j) =
      hcWindow (p ++ B) (p.length + j) := by
    rw [hEq]
    rw [show p ++ B ++ s ++ C = (p ++ B) ++ (s ++ C) by simp [List.append_assoc]]
    exact hcWindow_prefix (p ++ B) (s ++ C) (by omega) (by simp only [List.length_append]; omega)
  have hqj : entry B j < d + 1 := by
    have hle := (hbounds B hB _ (entry_mem B hj)).2
    omega
  have hcapp : (hcWindow (p ++ B) (p.length + j)).card = (hcWindow B j).card := by
    rcases hp with hp | hp
    · subst p; simp
    · obtain ⟨p', rfl⟩ := hp
      exact hcWindow_append_eq_right p' B hjI.1 hjI.2 hqj
  rw [hgpre, hcapp] at hcj
  exact hcj

end MultiAccessLogspace.Halting

open MultiAccessLogspace.Halting

/-- Lemma 3.3 (Characterizing hyporulers). -/
theorem solution (d b : ℕ) (hb : 1 ≤ b) (h : List ℕ) (hd : ∀ a ∈ h, 1 ≤ a ∧ a ≤ d) :
    IsHyporuler b d h ↔ HyporulerCondition b h := by
  classical
  induction d generalizing h with
  | zero =>
      constructor
      · intro hh
        subst h
        intro j hj
        simp at hj
      · intro hc
        have he : h = [] := by
          cases h with
          | nil => rfl
          | cons x xs =>
              have hx := hd x (by simp)
              omega
        exact he
  | succ d ih =>
      constructor
      · rintro ⟨blocks, hne, hlen, hbl, rfl⟩
        have hbs : ∀ B ∈ blocks, ∀ a ∈ B, 1 ≤ a ∧ a ≤ d :=
          fun B hB => hyporuler_bounds (hbl B hB)
        apply condition_of_intercalate hb blocks hlen
        · intro B hB
          exact (ih B (hbs B hB)).mp (hbl B hB)
        · exact hbs
      · intro hc
        let blocks := h.splitOnP (fun a => decide (a = d + 1))
        have hEq : List.intercalate [d + 1] blocks = h := intercalate_splitOnP_nat (d + 1) h
        have hbounds : ∀ B ∈ blocks, ∀ a ∈ B, 1 ≤ a ∧ a ≤ d := by
          intro B hB a ha
          have hmem := mem_of_mem_splitOnP_nat (d + 1) hB ha
          have hx := hd a hmem
          have hne := not_sep_of_mem_splitOnP_nat (d + 1) hB ha
          exact ⟨hx.1, by omega⟩
        have hcond : HyporulerCondition b (List.intercalate [d + 1] blocks) := by
          rw [hEq]
          exact hc
        have hbl : ∀ B ∈ blocks, IsHyporuler b d B := by
          intro B hB
          exact (ih B (hbounds B hB)).mpr
            (condition_block_of_intercalate blocks hcond hbounds B hB)
        refine ⟨blocks, List.splitOnP_ne_nil _ _, ?_, hbl, hEq.symm⟩
        · have hmax : ∀ x ∈ h, x ≤ d + 1 := by
            intro x hx
            exact (hd x hx).2
          have hcount : h.count (d + 1) ≤ b - 1 := count_le_of_condition_max hc hmax
          have hcount' : blocks.length - 1 ≤ b - 1 := by
            rw [← count_intercalate_singleton_self d blocks
              (fun B hB a ha => (hbounds B hB a ha).2), hEq]
            exact hcount
          have hn := List.splitOnP_ne_nil (fun a : ℕ => decide (a = d + 1)) h
          have hbpos : 1 ≤ blocks.length := List.length_pos_iff.mpr hn
          omega
