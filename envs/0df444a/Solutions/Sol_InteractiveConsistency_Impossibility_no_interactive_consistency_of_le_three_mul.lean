-- Prove2me | solution 1 for InteractiveConsistency.Impossibility.no_interactive_consistency_of_le_three_mul
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:07:45.668125+00:00
-- url     : https://prove2.me/submissions/bdbf151a-c732-4167-a6eb-16bf9510456d

import Mathlib
import Definitions.Def_InteractiveConsistency_Impossibility_Scenario
import Definitions.Def_InteractiveConsistency_Impossibility_Construction



namespace InteractiveConsistency.Impossibility

section ICcore
variable {α V : Type*} [DecidableEq α] (A B C : Finset α) (v v' : V)

lemma ic_lastIn_cons_cons (x y : α) (s : List α) :
    lastIn C (x :: y :: s) = lastIn C (y :: s) := by
  simp [lastIn, List.getLast?_cons_cons]

lemma ic_core_alpha_long (p y z : α) (w : List α) :
    core A B C v v' .alpha (p :: y :: z :: w) =
      if lastIn C (z :: w) then
        (if y ∈ B then core A B C v v' .beta (y :: z :: w)
          else core A B C v v' .alpha (y :: z :: w))
      else v := by
  rw [core]

lemma ic_core_beta_long (p y z : α) (w : List α) :
    core A B C v v' .beta (p :: y :: z :: w) =
      if lastIn C (z :: w) then
        (if y ∈ A then core A B C v v' .alpha (y :: z :: w)
          else core A B C v v' .beta (y :: z :: w))
      else v := by
  rw [core]

lemma ic_core_sigma_long (p y z : α) (w : List α) :
    core A B C v v' .sigma (p :: y :: z :: w) =
      if lastIn C (z :: w) then
        (if y ∈ C then
          (if p ∈ A then core A B C v v' .alpha (y :: z :: w)
            else if p ∈ B then core A B C v v' .beta (y :: z :: w)
            else core A B C v v' .sigma (y :: z :: w))
          else core A B C v v' .sigma (y :: z :: w))
      else v := by
  rw [core]

lemma ic_core_of_not_lastIn (k : Which) :
    ∀ s : List α, lastIn C s = false → core A B C v v' k s = v
  | [], _ => by cases k <;> simp [core]
  | [x], h => by cases k <;> simp_all [core, lastIn]
  | [x, y], h => by cases k <;> simp_all [core, lastIn]
  | x :: y :: z :: w, h => by
      have h' : lastIn C (z :: w) = false := by
        rw [ic_lastIn_cons_cons, ic_lastIn_cons_cons] at h; exact h
      cases k
      · rw [ic_core_alpha_long]; simp [h']
      · rw [ic_core_beta_long]; simp [h']
      · rw [ic_core_sigma_long]; simp [h']

lemma ic_cons_alpha {q : α} (hq : q ∉ B) (p : α) (w : List α) :
    core A B C v v' .alpha (p :: q :: w) = core A B C v v' .alpha (q :: w) := by
  cases w with
  | nil => simp [core]
  | cons z w' =>
    by_cases h : lastIn C (z :: w') = true
    · rw [ic_core_alpha_long]; simp [h, hq]
    · have h' : lastIn C (z :: w') = false := by simpa using h
      rw [ic_core_alpha_long, ic_core_of_not_lastIn A B C v v' .alpha (q :: z :: w')
        (by rw [ic_lastIn_cons_cons]; exact h')]
      simp [h']

lemma ic_cons_beta {q : α} (hq : q ∉ A) (p : α) (w : List α) :
    core A B C v v' .beta (p :: q :: w) = core A B C v v' .beta (q :: w) := by
  cases w with
  | nil => simp [core]
  | cons z w' =>
    by_cases h : lastIn C (z :: w') = true
    · rw [ic_core_beta_long]; simp [h, hq]
    · have h' : lastIn C (z :: w') = false := by simpa using h
      rw [ic_core_beta_long, ic_core_of_not_lastIn A B C v v' .beta (q :: z :: w')
        (by rw [ic_lastIn_cons_cons]; exact h')]
      simp [h']

lemma ic_cons_sigma {q : α} (hq : q ∉ C) (p : α) (w : List α) :
    core A B C v v' .sigma (p :: q :: w) = core A B C v v' .sigma (q :: w) := by
  cases w with
  | nil => simp [core, hq]
  | cons z w' =>
    by_cases h : lastIn C (z :: w') = true
    · rw [ic_core_sigma_long]; simp [h, hq]
    · have h' : lastIn C (z :: w') = false := by simpa using h
      rw [ic_core_sigma_long, ic_core_of_not_lastIn A B C v v' .sigma (q :: z :: w')
        (by rw [ic_lastIn_cons_cons]; exact h')]
      simp [h']

lemma ic_scen_cons (P : Finset α) (k : Which) (p q : α) (w : List α)
    (hp : p ∈ P) (hq : q ∈ P) (hw : IsString P w)
    (h : core A B C v v' k (p :: q :: w) = core A B C v v' k (q :: w)) :
    scen P A B C v v' k (p :: q :: w) = scen P A B C v v' k (q :: w) := by
  have h1 : IsString P (q :: w) := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hq
    · exact hw x hx
  have h2 : IsString P (p :: q :: w) := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hp
    · exact h1 x hx
  simp only [scen, if_pos h1, if_pos h2]
  exact h

lemma construction_consistent_core (P A B C : Finset α) (v v' : V)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) (hP : A ∪ B ∪ C = P) :
    ConsistentWith P (A ∪ C) (alphaScen P A B C v v') ∧
    ConsistentWith P (B ∪ C) (betaScen P A B C v v') ∧
    ConsistentWith P (A ∪ B) (sigmaScen P A B C v v') := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq p hp w hw
    have hqB : q ∉ B := by
      intro hb
      rcases Finset.mem_union.1 hq with h | h
      · exact Finset.disjoint_left.1 hAB h hb
      · exact Finset.disjoint_left.1 hBC hb h
    have hqP : q ∈ P := by
      rw [← hP]; rcases Finset.mem_union.1 hq with h | h <;> simp [h]
    exact ic_scen_cons A B C v v' P _ p q w hp hqP hw (ic_cons_alpha A B C v v' hqB p w)
  · intro q hq p hp w hw
    have hqA : q ∉ A := by
      intro ha
      rcases Finset.mem_union.1 hq with h | h
      · exact Finset.disjoint_left.1 hAB ha h
      · exact Finset.disjoint_left.1 hAC ha h
    have hqP : q ∈ P := by
      rw [← hP]; rcases Finset.mem_union.1 hq with h | h <;> simp [h]
    exact ic_scen_cons A B C v v' P _ p q w hp hqP hw (ic_cons_beta A B C v v' hqA p w)
  · intro q hq p hp w hw
    have hqC : q ∉ C := by
      intro hc
      rcases Finset.mem_union.1 hq with h | h
      · exact Finset.disjoint_left.1 hAC h hc
      · exact Finset.disjoint_left.1 hBC h hc
    have hqP : q ∈ P := by
      rw [← hP]; rcases Finset.mem_union.1 hq with h | h <;> simp [h]
    exact ic_scen_cons A B C v v' P _ p q w hp hqP hw (ic_cons_sigma A B C v v' hqC p w)

lemma ic_indist_core (P A B C : Finset α) (v v' : V)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) (hP : A ∪ B ∪ C = P) :
    ∀ w : List α, IsString P w →
      (∀ a ∈ A, core A B C v v' .alpha (a :: w) = core A B C v v' .sigma (a :: w)) ∧
      (∀ b ∈ B, core A B C v v' .beta (b :: w) = core A B C v v' .sigma (b :: w)) := by
  intro w
  induction w with
  | nil =>
    intro _
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · simp [core]
    · have : b ∉ C := fun h => Finset.disjoint_left.1 hBC hb h
      simp [core, this]
  | cons y t ih =>
    intro hw
    have hy : y ∈ A ∪ B ∪ C := by rw [hP]; exact hw y (by simp)
    have ht : IsString P t := fun x hx => hw x (by simp [hx])
    cases t with
    | nil =>
      refine ⟨fun a ha => ?_, fun b hb => ?_⟩
      · have : a ∉ B := fun h => Finset.disjoint_left.1 hAB ha h
        simp [core, this]
      · simp [core, hb]
    | cons z w' =>
      have IH := ih ht
      refine ⟨fun a ha => ?_, fun b hb => ?_⟩
      · have haB : a ∉ B := fun h => Finset.disjoint_left.1 hAB ha h
        rw [ic_core_alpha_long, ic_core_sigma_long]
        by_cases hl : lastIn C (z :: w') = true
        · simp only [hl, if_true]
          rcases Finset.mem_union.1 hy with hy | hyC
          · rcases Finset.mem_union.1 hy with hyA | hyB
            · have hyC : y ∉ C := fun h => Finset.disjoint_left.1 hAC hyA h
              have hyB : y ∉ B := fun h => Finset.disjoint_left.1 hAB hyA h
              simp only [hyC, hyB, if_false]
              exact (IH.1 y hyA)
            · have hyC : y ∉ C := fun h => Finset.disjoint_left.1 hBC hyB h
              simp only [hyC, hyB, if_false, if_true]
              exact (IH.2 y hyB)
          · have hyB : y ∉ B := fun h => Finset.disjoint_left.1 hBC h hyC
            simp only [hyC, hyB, if_false, if_true, ha]
        · simp [hl]
      · have hbA : b ∉ A := fun h => Finset.disjoint_left.1 hAB h hb
        rw [ic_core_beta_long, ic_core_sigma_long]
        by_cases hl : lastIn C (z :: w') = true
        · simp only [hl, if_true]
          rcases Finset.mem_union.1 hy with hy | hyC
          · rcases Finset.mem_union.1 hy with hyA | hyB
            · have hyC : y ∉ C := fun h => Finset.disjoint_left.1 hAC hyA h
              simp only [hyC, hyA, if_false, if_true]
              exact (IH.1 y hyA)
            · have hyC : y ∉ C := fun h => Finset.disjoint_left.1 hBC hyB h
              have hyA : y ∉ A := fun h => Finset.disjoint_left.1 hAB h hyB
              simp only [hyC, hyA, if_false]
              exact (IH.2 y hyB)
          · have hyA : y ∉ A := fun h => Finset.disjoint_left.1 hAC h hyC
            simp only [hyC, hyA, hbA, hb, if_false, if_true]
        · simp [hl]

lemma construction_indistinguishable_core (P A B C : Finset α) (v v' : V)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) (hP : A ∪ B ∪ C = P) :
    (∀ a ∈ A, restrict (alphaScen P A B C v v') a = restrict (sigmaScen P A B C v v') a) ∧
    (∀ b ∈ B, restrict (betaScen P A B C v v') b = restrict (sigmaScen P A B C v v') b) := by
  have key := ic_indist_core P A B C v v' hAB hAC hBC hP
  have memP : ∀ x, x ∈ A ∨ x ∈ B → x ∈ P := by
    intro x hx; rw [← hP]; rcases hx with h | h <;> simp [h]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · funext w
    simp only [restrict, scen]
    by_cases hw : IsString P w
    · have : IsString P (a :: w) := by
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact memP _ (Or.inl ha)
        · exact hw x hx
      simp only [if_pos this]
      exact (key w hw).1 a ha
    · have : ¬ IsString P (a :: w) := fun h => hw (fun x hx => h x (by simp [hx]))
      simp only [if_neg this]
  · funext w
    simp only [restrict, scen]
    by_cases hw : IsString P w
    · have : IsString P (b :: w) := by
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact memP _ (Or.inr hb)
        · exact hw x hx
      simp only [if_pos this]
      exact (key w hw).2 b hb
    · have : ¬ IsString P (b :: w) := fun h => hw (fun x hx => h x (by simp [hx]))
      simp only [if_neg this]


lemma partition_core {α : Type*} [DecidableEq α] (P : Finset α) (m : ℕ)
    (h3 : 3 ≤ P.card) (hn : P.card ≤ 3 * m) :
    ∃ A B C : Finset α,
      A.Nonempty ∧ B.Nonempty ∧ C.Nonempty ∧
      Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧
      A ∪ B ∪ C = P ∧
      A.card ≤ m ∧ B.card ≤ m ∧ C.card ≤ m := by
  obtain ⟨A, hAP, hA⟩ := Finset.exists_subset_card_eq (s := P) (n := min m (P.card - 2)) (by omega)
  have hcard : (P \ A).card = P.card - A.card := Finset.card_sdiff_of_subset hAP
  obtain ⟨B, hBP, hB⟩ := Finset.exists_subset_card_eq (s := P \ A)
    (n := min m (P.card - A.card - 1)) (by omega)
  have hBc : ((P \ A) \ B).card = (P \ A).card - B.card := Finset.card_sdiff_of_subset hBP
  refine ⟨A, B, (P \ A) \ B, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Finset.card_pos]; omega
  · rw [← Finset.card_pos]; omega
  · rw [← Finset.card_pos]; omega
  · exact Finset.disjoint_left.2 fun x hxA hxB => (Finset.mem_sdiff.1 (hBP hxB)).2 hxA
  · exact Finset.disjoint_left.2 fun x hxA hxC =>
      (Finset.mem_sdiff.1 (Finset.mem_sdiff.1 hxC).1).2 hxA
  · exact Finset.disjoint_left.2 fun x hxB hxC => (Finset.mem_sdiff.1 hxC).2 hxB
  · ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ((h | h) | h)
      · exact hAP h
      · exact (Finset.mem_sdiff.1 (hBP h)).1
      · exact h.1.1
    · intro hx
      by_cases hxA : x ∈ A
      · exact Or.inl (Or.inl hxA)
      · by_cases hxB : x ∈ B
        · exact Or.inl (Or.inr hxB)
        · exact Or.inr ⟨⟨hx, hxA⟩, hxB⟩
  · omega
  · omega
  · omega


lemma ic_scen_singleton {α V : Type*} [DecidableEq α] (P A B C : Finset α) (v v' : V) (k : Which)
    (c : α) (hc : c ∈ P) :
    scen P A B C v v' k [c] = core A B C v v' k [c] := by
  have : IsString P [c] := by
    intro x hx
    rw [List.mem_singleton.1 hx]; exact hc
  simp [scen, this]

theorem no_ic_core {α V : Type*} [DecidableEq α]
    (P : Finset α) (m : ℕ) (hV : ∃ v v' : V, v ≠ v')
    (h3 : 3 ≤ P.card) (hn : P.card ≤ 3 * m) :
    ∀ F : α → (List α → V) → α → V, ¬ AssuresIC P m F := by
  intro F hF
  obtain ⟨v, v', hvv⟩ := hV
  obtain ⟨A, B, C, hA, hB, hC, hAB, hAC, hBC, hP, hAm, hBm, hCm⟩ :=
    partition_core P m h3 hn
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  obtain ⟨c, hc⟩ := hC
  have hsub : ∀ x, x ∈ A ∨ x ∈ B ∨ x ∈ C → x ∈ P := by
    intro x hx; rw [← hP]; rcases hx with h | h | h <;> simp [h]
  have haP := hsub a (Or.inl ha)
  have hbP := hsub b (Or.inr (Or.inl hb))
  have hcP := hsub c (Or.inr (Or.inr hc))
  obtain ⟨hcα, hcβ, hcσ⟩ := construction_consistent_core P A B C v v' hAB hAC hBC hP
  obtain ⟨hia, hib⟩ := construction_indistinguishable_core P A B C v v' hAB hAC hBC hP
  have hcardAC : (A ∪ C).card = A.card + C.card := Finset.card_union_of_disjoint hAC
  have hcardBC : (B ∪ C).card = B.card + C.card := Finset.card_union_of_disjoint hBC
  have hcardAB : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hAB
  have hPc : P.card = A.card + B.card + C.card := by
    rw [← hP, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint hAB]
    exact Finset.disjoint_union_left.2 ⟨hAC, hBC⟩
  have hs1 : A ∪ C ⊆ P := by
    intro x hx; rcases Finset.mem_union.1 hx with h | h
    · exact hsub x (Or.inl h)
    · exact hsub x (Or.inr (Or.inr h))
  have hs2 : B ∪ C ⊆ P := by
    intro x hx; rcases Finset.mem_union.1 hx with h | h
    · exact hsub x (Or.inr (Or.inl h))
    · exact hsub x (Or.inr (Or.inr h))
  have hs3 : A ∪ B ⊆ P := by
    intro x hx; rcases Finset.mem_union.1 hx with h | h
    · exact hsub x (Or.inl h)
    · exact hsub x (Or.inr (Or.inl h))
  have h1 := hF (A ∪ C) hs1 (by omega) _ hcα
  have h2 := hF (B ∪ C) hs2 (by omega) _ hcβ
  have h3' := hF (A ∪ B) hs3 (by omega) _ hcσ
  have e1 := h1.1 a (Finset.mem_union_left _ ha) c (Finset.mem_union_right _ hc)
  have e2 := h2.1 b (Finset.mem_union_left _ hb) c (Finset.mem_union_right _ hc)
  have e3 := (h3'.2 a (Finset.mem_union_left _ ha) b (Finset.mem_union_right _ hb) c hcP)
  rw [← hia a ha] at e3
  rw [← hib b hb] at e3
  rw [e1, e2] at e3
  simp only [alphaScen, betaScen] at e3
  rw [ic_scen_singleton P A B C v v' _ c hcP, ic_scen_singleton P A B C v v' _ c hcP] at e3
  simp [core, hc] at e3
  exact hvv e3

end ICcore

end InteractiveConsistency.Impossibility

open InteractiveConsistency.Impossibility


theorem solution {α V : Type*} [DecidableEq α]
    (P : Finset α) (m : ℕ) (hV : ∃ v v' : V, v ≠ v')
    (h3 : 3 ≤ P.card) (hn : P.card ≤ 3 * m) :
    ∀ F : α → (List α → V) → α → V, ¬ AssuresIC P m F := by
  exact no_ic_core P m hV h3 hn
