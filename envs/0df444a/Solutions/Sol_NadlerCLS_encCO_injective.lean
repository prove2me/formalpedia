-- Prove2me | solution 1 for NadlerCLS.encCO_injective
-- status  : ACCEPTED   (prove)
-- author  : @utkuokur
-- created : 2026-11-12T19:55:22.248594+00:00
-- url     : https://prove2.me/submissions/bed207f8-06b1-46fa-9d3f-6118374ee9f4

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_NadlerCLS_COInstance

set_option autoImplicit false

open NetworkEquilibriumCLS.LinearNash

namespace NadlerCLS.EncInj

/-- A code is *uniquely readable* if a code word followed by arbitrary further data determines
both the encoded object and the remaining data.  (In particular the code is injective and
prefix-free.) -/
def Uniq {α : Type*} (enc : α → List Bool) : Prop :=
  ∀ (a b : α) (r r' : List Bool), enc a ++ r = enc b ++ r' → a = b ∧ r = r'

/-- A unary block `true … true false` in front of data determines its length and the data. -/
theorem unary_inj (m m' : ℕ) (u u' : List Bool)
    (h : List.replicate m true ++ false :: u = List.replicate m' true ++ false :: u') :
    m = m' ∧ u = u' := by
  induction m generalizing m' with
  | zero =>
    cases m' with
    | zero => simpa using h
    | succ k => simp [List.replicate_succ] at h
  | succ k ih =>
    cases m' with
    | zero => simp [List.replicate_succ] at h
    | succ k' =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨h1, h2⟩ := ih k' h
      exact ⟨by omega, h2⟩

/-- The binary digit list determines the number. -/
theorem bits_inj {a b : ℕ} (h : a.bits = b.bits) : a = b := by
  have h2 : Nat.digits 2 a = Nat.digits 2 b := by
    rw [Nat.digits_two_eq_bits, Nat.digits_two_eq_bits, h]
  exact Nat.digits_inj_iff.mp h2

theorem uniq_encNat : Uniq encNat := by
  intro a b r r' h
  simp only [encNat, List.append_assoc, List.cons_append] at h
  obtain ⟨hlen, h2⟩ := unary_inj _ _ _ _ h
  obtain ⟨h3, h4⟩ := List.append_inj h2 hlen
  exact ⟨bits_inj h3, h4⟩

theorem uniq_encInt : Uniq encInt := by
  intro a b r r' h
  simp only [encInt, List.cons_append, List.cons.injEq] at h
  obtain ⟨hs, h2⟩ := h
  obtain ⟨h3, h4⟩ := uniq_encNat _ _ _ _ h2
  refine ⟨?_, h4⟩
  have hs' : a < 0 ↔ b < 0 := by simpa using hs
  omega

theorem uniq_encRat : Uniq encRat := by
  intro a b r r' h
  simp only [encRat, List.append_assoc] at h
  obtain ⟨h1, h2⟩ := uniq_encInt _ _ _ _ h
  obtain ⟨h3, h4⟩ := uniq_encNat _ _ _ _ h2
  exact ⟨Rat.ext h1 h3, h4⟩

theorem uniq_gateCode : Uniq gateCode := by
  intro g g' r r' h
  cases g <;> cases g' <;> simp only [gateCode, List.append_assoc] at h <;>
    obtain ⟨htag, hrest⟩ := uniq_encNat _ _ _ _ h <;>
    first
      | (exfalso; omega)
      | (obtain ⟨h1, hrest1⟩ := uniq_encNat _ _ _ _ hrest
         obtain ⟨h2, hrest2⟩ := uniq_encNat _ _ _ _ hrest1
         exact ⟨by rw [h1, h2], hrest2⟩)
      | (obtain ⟨h1, hrest1⟩ := uniq_encNat _ _ _ _ hrest
         exact ⟨by rw [h1], hrest1⟩)
      | (obtain ⟨h1, hrest1⟩ := uniq_encRat _ _ _ _ hrest
         exact ⟨by rw [h1], hrest1⟩)

/-- Concatenated code words of two lists of the same length determine the lists. -/
theorem flatMap_inj {α : Type*} (f : α → List Bool) (hf : Uniq f) (xs ys : List α)
    (r r' : List Bool) (hlen : xs.length = ys.length)
    (h : xs.flatMap f ++ r = ys.flatMap f ++ r') : xs = ys ∧ r = r' := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simpa using h
    | cons y ys => simp at hlen
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.flatMap_cons, List.append_assoc] at h
      obtain ⟨h1, h2⟩ := hf _ _ _ _ h
      obtain ⟨h3, h4⟩ := ih ys (by simpa using hlen) h2
      exact ⟨by rw [h1, h3], h4⟩

theorem uniq_encList {α : Type*} (f : α → List Bool) (hf : Uniq f) : Uniq (encList f) := by
  intro xs ys r r' h
  simp only [encList, List.append_assoc] at h
  obtain ⟨hlen, h2⟩ := uniq_encNat _ _ _ _ h
  exact flatMap_inj f hf xs ys r r' hlen h2

theorem uniq_encCirc : Uniq encCirc := by
  intro C C' r r' h
  simp only [encCirc, List.append_assoc] at h
  obtain ⟨h1, h2⟩ := uniq_encList gateCode uniq_gateCode _ _ _ _ h
  obtain ⟨h3, h4⟩ := uniq_encList encNat uniq_encNat _ _ _ _ h2
  refine ⟨?_, h4⟩
  cases C
  cases C'
  simp_all

end NadlerCLS.EncInj

open NadlerCLS in
theorem solution (n : ℕ) : Function.Injective (encCO : COInstance n → List Bool) := by
  intro I J h
  have h' : encCO I ++ [] = encCO J ++ [] := by rw [h]
  simp only [encCO, List.append_assoc] at h'
  obtain ⟨h1, h2⟩ := EncInj.uniq_encCirc _ _ _ _ h'
  obtain ⟨h3, h4⟩ := EncInj.uniq_encCirc _ _ _ _ h2
  obtain ⟨h5, h6⟩ := EncInj.uniq_encRat _ _ _ _ h4
  obtain ⟨h7, -⟩ := EncInj.uniq_encRat _ _ _ _ h6
  cases I
  cases J
  simp_all
