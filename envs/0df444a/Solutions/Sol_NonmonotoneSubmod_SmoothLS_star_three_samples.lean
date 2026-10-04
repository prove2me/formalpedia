-- Prove2me | solution 1 for NonmonotoneSubmod.SmoothLS.star_three_samples
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T00:12:28.935422+00:00
-- url     : https://prove2.me/submissions/308077c4-371e-4810-8399-7db7944df7e6

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

set_option autoImplicit false

namespace P4ee9dc16

open NonmonotoneSubmod.Shared

variable {X : Type} [Fintype X] [DecidableEq X]

def wt (p : ℝ) (A S : Finset X) : ℝ := p ^ S.card * (1 - p) ^ (A \ S).card

lemma wt_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (A S : Finset X) : 0 ≤ wt p A S := by
  unfold wt
  exact mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)

lemma sub_comp (f : Finset X → ℝ) (hf : Submodular f) (φ : Finset X → Finset X)
    (hu : ∀ T U, φ (T ∪ U) = φ T ∪ φ U) (hi : ∀ T U, φ (T ∩ U) = φ T ∩ φ U) :
    Submodular (fun T => f (φ T)) := by
  intro S T
  simp only
  rw [hu, hi]
  exact hf _ _

lemma one_sample (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Finset X) :
    ∀ g : Finset X → ℝ, Submodular g →
    (1 - p) * g ∅ + p * g A ≤ ∑ S ∈ A.powerset, wt p A S * g S := by
  induction A using Finset.induction_on with
  | empty => intro g _; simp [wt]; exact le_of_eq (by ring)
  | insert a B haB ih =>
    intro g hg
    rw [Finset.sum_powerset_insert haB]
    have e1 : ∀ t ∈ B.powerset, wt p (insert a B) t * g t = (1 - p) * (wt p B t * g t) := by
      intro t ht
      have hat : a ∉ t := fun h => haB (Finset.mem_powerset.mp ht h)
      have hBt : a ∉ B \ t := fun h => haB (Finset.mem_sdiff.mp h).1
      rw [wt, wt, Finset.insert_sdiff_of_notMem B hat, Finset.card_insert_of_notMem hBt]
      ring
    have e2 : ∀ t ∈ B.powerset,
        wt p (insert a B) (insert a t) * g (insert a t) = p * (wt p B t * g (insert a t)) := by
      intro t ht
      have hat : a ∉ t := fun h => haB (Finset.mem_powerset.mp ht h)
      rw [wt, wt, Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem haB,
        Finset.card_insert_of_notMem hat]
      ring
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 := ih g hg
    have h2 := ih (fun T => g (insert a T))
      (sub_comp g hg (insert a) (fun T U => Finset.insert_union_distrib a T U)
        (fun T U => Finset.insert_inter_distrib T U a))
    simp only [LawfulSingleton.insert_empty_eq] at h2
    have hs := hg B {a}
    have hu : B ∪ {a} = insert a B := by
      rw [Finset.union_comm]; rfl
    have hi : B ∩ {a} = ∅ := by
      ext x; simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
      rintro ⟨hx, rfl⟩; exact haB hx
    rw [hu, hi] at hs
    have hp' : 0 ≤ 1 - p := by linarith
    have hpp : 0 ≤ p * (1 - p) := mul_nonneg hp0 hp'
    nlinarith [mul_le_mul_of_nonneg_left h1 hp', mul_le_mul_of_nonneg_left h2 hp0,
      mul_le_mul_of_nonneg_left hs hpp]

lemma lhs_eq (f : Finset X → ℝ) (A : Fin 3 → Finset X) (p : Fin 3 → ℝ) :
    ∑ I : Finset (Fin 3), (∏ i ∈ I, p i) * (∏ i ∈ Iᶜ, (1 - p i)) * f (I.biUnion A) =
      (1 - p 2) * (1 - p 1) * ((1 - p 0) * f ∅ + p 0 * f (A 0))
      + (1 - p 2) * p 1 * ((1 - p 0) * f (A 1) + p 0 * f (A 0 ∪ A 1))
      + p 2 * (1 - p 1) * ((1 - p 0) * f (A 2) + p 0 * f (A 0 ∪ A 2))
      + p 2 * p 1 * ((1 - p 0) * f (A 1 ∪ A 2) + p 0 * f (A 0 ∪ A 1 ∪ A 2)) := by
  have hU : (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  have c0 : (∅ : Finset (Fin 3))ᶜ = {0, 1, 2} := by decide
  have c1 : ({0} : Finset (Fin 3))ᶜ = {1, 2} := by decide
  have c2 : ({1} : Finset (Fin 3))ᶜ = {0, 2} := by decide
  have c3 : ({2} : Finset (Fin 3))ᶜ = {0, 1} := by decide
  have c4 : ({0, 1} : Finset (Fin 3))ᶜ = {2} := by decide
  have c5 : ({0, 2} : Finset (Fin 3))ᶜ = {1} := by decide
  have c6 : ({1, 2} : Finset (Fin 3))ᶜ = {0} := by decide
  have c7 : ({0, 1, 2} : Finset (Fin 3))ᶜ = ∅ := by decide
  rw [hU]
  simp (config := {decide := true}) only [Finset.sum_insert, Finset.sum_singleton,
    Finset.mem_insert, Finset.mem_singleton, c0, c1, c2, c3, c4, c5, c6, c7,
    Finset.prod_insert, Finset.prod_singleton, Finset.prod_empty, Finset.biUnion_insert,
    Finset.singleton_biUnion, Finset.biUnion_empty, Finset.union_empty, ← Finset.union_assoc,
    not_false_eq_true, Finset.notMem_empty]
  ring

end P4ee9dc16

theorem solution {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f) (A : Fin 3 → Finset X) (p : Fin 3 → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    ∑ I : Finset (Fin 3), (∏ i ∈ I, p i) * (∏ i ∈ Iᶜ, (1 - p i)) * f (I.biUnion A) ≤
      ∑ S₁ ∈ (A 0).powerset, ∑ S₂ ∈ (A 1).powerset, ∑ S₃ ∈ (A 2).powerset,
        (p 0 ^ S₁.card * (1 - p 0) ^ (A 0 \ S₁).card) *
          (p 1 ^ S₂.card * (1 - p 1) ^ (A 1 \ S₂).card) *
          (p 2 ^ S₃.card * (1 - p 2) ^ (A 2 \ S₃).card) * f (S₁ ∪ S₂ ∪ S₃) := by
  have eR : (∑ S₁ ∈ (A 0).powerset, ∑ S₂ ∈ (A 1).powerset, ∑ S₃ ∈ (A 2).powerset,
        (p 0 ^ S₁.card * (1 - p 0) ^ (A 0 \ S₁).card) *
          (p 1 ^ S₂.card * (1 - p 1) ^ (A 1 \ S₂).card) *
          (p 2 ^ S₃.card * (1 - p 2) ^ (A 2 \ S₃).card) * f (S₁ ∪ S₂ ∪ S₃)) =
      ∑ S₁ ∈ (A 0).powerset, P4ee9dc16.wt (p 0) (A 0) S₁ * ∑ S₂ ∈ (A 1).powerset,
        P4ee9dc16.wt (p 1) (A 1) S₂ * ∑ S₃ ∈ (A 2).powerset, P4ee9dc16.wt (p 2) (A 2) S₃ * f (S₁ ∪ S₂ ∪ S₃) := by
    simp only [Finset.mul_sum, P4ee9dc16.wt]
    refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl
      (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring)))
  rw [eR, P4ee9dc16.lhs_eq]
  have hsh : ∀ B C : Finset X, NonmonotoneSubmod.Shared.Submodular (fun T => f (B ∪ T ∪ C)) :=
    fun B C => P4ee9dc16.sub_comp f hf (fun T => B ∪ T ∪ C)
      (fun T U => by ext x; simp only [Finset.mem_union]; tauto)
      (fun T U => by ext x; simp only [Finset.mem_union, Finset.mem_inter]; tauto)
  have key : ∀ (i : Fin 3) (B C : Finset X), (1 - p i) * f (B ∪ C) + p i * f (B ∪ A i ∪ C) ≤
      ∑ S ∈ (A i).powerset, P4ee9dc16.wt (p i) (A i) S * f (B ∪ S ∪ C) := by
    intro i B C
    have := P4ee9dc16.one_sample (p i) (hp0 i) (hp1 i) (A i) _ (hsh B C)
    simpa only [Finset.union_empty] using this
  have key0 : ∀ (i : Fin 3) (B : Finset X), (1 - p i) * f B + p i * f (B ∪ A i) ≤
      ∑ S ∈ (A i).powerset, P4ee9dc16.wt (p i) (A i) S * f (B ∪ S) := by
    intro i B
    simpa only [Finset.union_empty] using key i B ∅
  have keyL : ∀ (i : Fin 3) (C : Finset X), (1 - p i) * f C + p i * f (A i ∪ C) ≤
      ∑ S ∈ (A i).powerset, P4ee9dc16.wt (p i) (A i) S * f (S ∪ C) := by
    intro i C
    simpa only [Finset.empty_union] using key i ∅ C
  have hw : ∀ i S, 0 ≤ P4ee9dc16.wt (p i) (A i) S := fun i S => P4ee9dc16.wt_nonneg (hp0 i) (hp1 i) _ _
  have q0 : ∀ i, 0 ≤ 1 - p i := fun i => by linarith [hp1 i]
  -- inner bound for fixed S₁
  have hin : ∀ S₁ : Finset X,
      (1 - p 2) * ((1 - p 1) * f S₁ + p 1 * f (S₁ ∪ A 1))
        + p 2 * ((1 - p 1) * f (S₁ ∪ A 2) + p 1 * f (S₁ ∪ A 1 ∪ A 2)) ≤
      ∑ S₂ ∈ (A 1).powerset, P4ee9dc16.wt (p 1) (A 1) S₂ *
        ∑ S₃ ∈ (A 2).powerset, P4ee9dc16.wt (p 2) (A 2) S₃ * f (S₁ ∪ S₂ ∪ S₃) := by
    intro S₁
    have a := key0 1 S₁
    have b := key 1 S₁ (A 2)
    have c : ∑ S₂ ∈ (A 1).powerset, P4ee9dc16.wt (p 1) (A 1) S₂ *
          ((1 - p 2) * f (S₁ ∪ S₂) + p 2 * f (S₁ ∪ S₂ ∪ A 2)) ≤
        ∑ S₂ ∈ (A 1).powerset, P4ee9dc16.wt (p 1) (A 1) S₂ *
          ∑ S₃ ∈ (A 2).powerset, P4ee9dc16.wt (p 2) (A 2) S₃ * f (S₁ ∪ S₂ ∪ S₃) :=
      Finset.sum_le_sum (fun S₂ _ => mul_le_mul_of_nonneg_left (key0 2 (S₁ ∪ S₂)) (hw 1 S₂))
    have e : ∑ S₂ ∈ (A 1).powerset, P4ee9dc16.wt (p 1) (A 1) S₂ *
          ((1 - p 2) * f (S₁ ∪ S₂) + p 2 * f (S₁ ∪ S₂ ∪ A 2)) =
        (1 - p 2) * ∑ S₂ ∈ (A 1).powerset, P4ee9dc16.wt (p 1) (A 1) S₂ * f (S₁ ∪ S₂)
          + p 2 * ∑ S₂ ∈ (A 1).powerset, P4ee9dc16.wt (p 1) (A 1) S₂ * f (S₁ ∪ S₂ ∪ A 2) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    nlinarith [mul_le_mul_of_nonneg_left a (q0 2), mul_le_mul_of_nonneg_left b (hp0 2)]
  have c : ∑ S₁ ∈ (A 0).powerset, P4ee9dc16.wt (p 0) (A 0) S₁ *
        ((1 - p 2) * ((1 - p 1) * f S₁ + p 1 * f (S₁ ∪ A 1))
          + p 2 * ((1 - p 1) * f (S₁ ∪ A 2) + p 1 * f (S₁ ∪ A 1 ∪ A 2))) ≤
      ∑ S₁ ∈ (A 0).powerset, P4ee9dc16.wt (p 0) (A 0) S₁ * ∑ S₂ ∈ (A 1).powerset, P4ee9dc16.wt (p 1) (A 1) S₂ *
        ∑ S₃ ∈ (A 2).powerset, P4ee9dc16.wt (p 2) (A 2) S₃ * f (S₁ ∪ S₂ ∪ S₃) :=
    Finset.sum_le_sum (fun S₁ _ => mul_le_mul_of_nonneg_left (hin S₁) (hw 0 S₁))
  have e : ∑ S₁ ∈ (A 0).powerset, P4ee9dc16.wt (p 0) (A 0) S₁ *
        ((1 - p 2) * ((1 - p 1) * f S₁ + p 1 * f (S₁ ∪ A 1))
          + p 2 * ((1 - p 1) * f (S₁ ∪ A 2) + p 1 * f (S₁ ∪ A 1 ∪ A 2))) =
      (1 - p 2) * (1 - p 1) * ∑ S₁ ∈ (A 0).powerset, P4ee9dc16.wt (p 0) (A 0) S₁ * f S₁
      + (1 - p 2) * p 1 * ∑ S₁ ∈ (A 0).powerset, P4ee9dc16.wt (p 0) (A 0) S₁ * f (S₁ ∪ A 1)
      + p 2 * (1 - p 1) * ∑ S₁ ∈ (A 0).powerset, P4ee9dc16.wt (p 0) (A 0) S₁ * f (S₁ ∪ A 2)
      + p 2 * p 1 * ∑ S₁ ∈ (A 0).powerset, P4ee9dc16.wt (p 0) (A 0) S₁ * f (S₁ ∪ A 1 ∪ A 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have k1 : (1 - p 0) * f ∅ + p 0 * f (A 0) ≤
      ∑ S₁ ∈ (A 0).powerset, P4ee9dc16.wt (p 0) (A 0) S₁ * f S₁ := by
    simpa only [Finset.union_empty] using keyL 0 ∅
  have k2 := keyL 0 (A 1)
  have k3 := keyL 0 (A 2)
  have k4 := keyL 0 (A 1 ∪ A 2)
  simp only [← Finset.union_assoc] at k4
  have m00 : 0 ≤ (1 - p 2) * (1 - p 1) := mul_nonneg (q0 2) (q0 1)
  have m01 : 0 ≤ (1 - p 2) * p 1 := mul_nonneg (q0 2) (hp0 1)
  have m10 : 0 ≤ p 2 * (1 - p 1) := mul_nonneg (hp0 2) (q0 1)
  have m11 : 0 ≤ p 2 * p 1 := mul_nonneg (hp0 2) (hp0 1)
  nlinarith [mul_le_mul_of_nonneg_left k1 m00, mul_le_mul_of_nonneg_left k2 m01,
    mul_le_mul_of_nonneg_left k3 m10, mul_le_mul_of_nonneg_left k4 m11]
