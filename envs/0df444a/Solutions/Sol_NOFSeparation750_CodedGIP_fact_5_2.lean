-- Prove2me | solution 1 for NOFSeparation750.CodedGIP.fact_5_2
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T05:26:37.064678+00:00
-- url     : https://prove2.me/submissions/44773323-f0f5-4be2-abff-a8d2a404f84d

import Mathlib
import Definitions.Def_NOFSeparation750_CodedGIP_Cylinders

open NOFSeparation750.CodedGIP

private theorem interCylinder {k : ℕ} {X : Fin k → Type}
    {A B : Set (Input X)} {i : Fin k}
    (hA : IsCylinderIntersection A) (hB : IsCylinder i B) :
    IsCylinderIntersection (A ∩ B) := by
  classical
  obtain ⟨C, hC, rfl⟩ := hA
  refine ⟨fun j => if j = i then C j ∩ B else C j, ?_, ?_⟩
  · intro j
    by_cases he : j = i
    · subst j
      simp only [if_true]
      intro x y h
      exact and_congr (hC i x y h) (hB x y h)
    · simpa only [if_neg he] using hC j
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hx, hb⟩ j
      split_ifs <;> simp [hx j, hb]
    · intro hx
      refine ⟨fun j => ?_, ?_⟩
      · by_cases h : j = i
        · simpa [h] using (show x ∈ C i from (by simpa using hx i : x ∈ C i ∩ B).1)
        · simpa [h] using hx j
      · exact (show x ∈ C i ∩ B by simpa using hx i).2

private theorem boundedAcceptingSets {k : ℕ} {X : Fin k → Type}
    (c : ℕ) (P : BitProtocol X) :
    ∃ S : Finset (Set (Input X)), S.card ≤ 2 ^ c ∧
      (∀ A ∈ S, IsCylinderIntersection A) ∧
      ∀ x, ((P.run x).1 = true ∧ (P.run x).2 ≤ c) ↔ ∃ A ∈ S, x ∈ A := by
  classical
  induction c generalizing P with
  | zero =>
    cases P with
    | leaf b =>
      cases b
      · exact ⟨∅, by simp, by simp, by simp [BitProtocol.run]⟩
      · refine ⟨{Set.univ}, by simp only [Finset.card_singleton]; exact Nat.one_le_pow _ _ (by decide), ?_, by simp [BitProtocol.run]⟩
        intro A hA
        obtain rfl := Finset.mem_singleton.mp hA
        exact ⟨fun _ => Set.univ, fun _ _ _ _ => Iff.rfl, by simp⟩
    | send i f P₀ P₁ =>
      exact ⟨∅, by simp, by simp, fun x => by simp [BitProtocol.run]⟩
  | succ c ih =>
    cases P with
    | leaf b =>
      cases b
      · exact ⟨∅, by simp, by simp, by simp [BitProtocol.run]⟩
      · refine ⟨{Set.univ}, by simp only [Finset.card_singleton]; exact Nat.one_le_pow _ _ (by decide), ?_, by simp [BitProtocol.run]⟩
        intro A hA
        obtain rfl := Finset.mem_singleton.mp hA
        exact ⟨fun _ => Set.univ, fun _ _ _ _ => Iff.rfl, by simp⟩
    | send i f P₀ P₁ =>
      obtain ⟨S₀, hc₀, hS₀, e₀⟩ := ih P₀
      obtain ⟨S₁, hc₁, hS₁, e₁⟩ := ih P₁
      let B (b : Bool) : Set (Input X) := {x | f (visible i x) = b}
      have hB (b : Bool) : IsCylinder i (B b) := by
        intro x y h
        have huv : visible i x = visible i y := funext fun j => h j.val j.property
        simp [B, huv]
      let S := S₀.image (fun A => A ∩ B false) ∪ S₁.image (fun A => A ∩ B true)
      refine ⟨S, ?_, ?_, ?_⟩
      · calc
          _ ≤ (S₀.image (fun A => A ∩ B false)).card +
                (S₁.image (fun A => A ∩ B true)).card := Finset.card_union_le _ _
          _ ≤ 2 ^ c + 2 ^ c :=
            Nat.add_le_add (Finset.card_image_le.trans hc₀) (Finset.card_image_le.trans hc₁)
          _ = _ := by rw [pow_succ]; omega
      · intro A hA
        simp only [S, Finset.mem_union, Finset.mem_image] at hA
        rcases hA with ⟨D, hD, rfl⟩ | ⟨D, hD, rfl⟩
        · exact interCylinder (hS₀ D hD) (hB false)
        · exact interCylinder (hS₁ D hD) (hB true)
      · intro x
        have himg (T : Finset (Set (Input X))) (b : Bool) :
            (∃ A ∈ T.image (fun A => A ∩ B b), x ∈ A) ↔
              (∃ A ∈ T, x ∈ A) ∧ f (visible i x) = b := by
          constructor
          · rintro ⟨A, hA, hx⟩
            obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hA
            exact ⟨⟨D, hD, hx.1⟩, hx.2⟩
          · rintro ⟨⟨D, hD, hx⟩, hb⟩
            exact ⟨_, Finset.mem_image_of_mem _ hD, hx, hb⟩
        simp only [S, Finset.mem_union, or_and_right, exists_or, himg]
        cases he : f (visible i x) <;> simp [BitProtocol.run, he, e₀, e₁]

theorem solution (k : ℕ) (X : Fin k → Type)
    (F : Input X → Bool) (P : NondetProtocol X) (d : ℕ)
    (hCorrect : P.Correct F) (hCost : P.Bounded d) :
    AcceptingCover F d := by
  classical
  obtain ⟨c, hc, hBound⟩ := hCost
  choose S hS hC hRun using fun z : Bits P.certificateBits => boundedAcceptingSets c (P.verifier z)
  let T := (Finset.univ : Finset (Bits P.certificateBits)).biUnion S
  have hTc : T.card ≤ 2 ^ d := by
    calc
      T.card ≤ ∑ z : Bits P.certificateBits, (S z).card := Finset.card_biUnion_le
      _ ≤ ∑ _ : Bits P.certificateBits, 2 ^ c := Finset.sum_le_sum fun z _ => hS z
      _ = 2 ^ (P.certificateBits + c) := by simp [pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) hc
  have hAccept (x : Input X) : F x = true ↔ ∃ A ∈ T, x ∈ A := by
    rw [hCorrect x]
    simp only [T, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨z, hz⟩
      obtain ⟨A, hA, hx⟩ := (hRun z x).mp ⟨hz, hBound z x⟩
      exact ⟨A, ⟨z, hA⟩, hx⟩
    · rintro ⟨A, ⟨z, hA⟩, hx⟩
      exact ⟨z, ((hRun z x).mpr ⟨A, hA, hx⟩).1⟩
  let e : {A // A ∈ T} ≃ Fin T.card := (Fintype.equivFin _).trans
    (finCongr (Fintype.card_coe T))
  refine ⟨T.card, hTc, fun a => (e.symm a).val, ?_, ?_⟩
  · intro a
    have hA := (e.symm a).property
    obtain ⟨z, _, hz⟩ := Finset.mem_biUnion.mp hA
    exact ⟨hC z _ hz, fun x hx => (hAccept x).mpr ⟨_, hA, hx⟩⟩
  · ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    rw [hAccept]
    constructor
    · rintro ⟨A, hA, hx⟩
      exact ⟨e ⟨A, hA⟩, by simpa using hx⟩
    · rintro ⟨a, hx⟩
      exact ⟨_, (e.symm a).property, hx⟩

#print axioms solution
