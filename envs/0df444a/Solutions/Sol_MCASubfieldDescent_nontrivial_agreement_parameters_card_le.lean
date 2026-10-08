-- Prove2me | solution 1 for MCASubfieldDescent.nontrivial_agreement_parameters_card_le
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-04T15:13:05.192991+00:00
-- url     : https://prove2.me/submissions/2f31de4c-a9a1-44a9-a6dd-1c1f1cff8f24

import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.LinearCombination

namespace MCASubfieldDescent

open Polynomial

variable {F K : Type*} [Field F] [Field K]

/-- An element outside the embedded base field has no nontrivial affine relation over it. -/
theorem affine_relation_eq_zero
    (f : F →+* K) (γ : K) (hγ : γ ∉ Set.range f) (a b : F)
    (h : f a + γ * f b = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra hb
    have hfb : f b ≠ 0 := by
      intro hfb
      apply hb
      exact f.injective (by simpa only [map_zero] using hfb)
    apply hγ
    refine ⟨-a / b, ?_⟩
    rw [map_div₀, map_neg]
    apply (div_eq_iff hfb).2
    exact neg_eq_iff_add_eq_zero.mpr h
  refine ⟨?_, hb⟩
  apply f.injective
  simpa [hb] using h

/-- An outside-base-field agreement polynomial forces both original words to interpolate
on the entire agreement set, not only the `w+1` nodes used to construct the interpolants. -/
theorem basefield_interpolants_of_parameter_not_mem_range
    {ι : Type*} (f : F →+* K) (T : Finset ι) (x u₀ u₁ : ι → F)
    (w : ℕ) (hT : w < T.card) (hx : Set.InjOn x T)
    (γ : K) (hγ : γ ∉ Set.range f) (P : Polynomial K)
    (hP : P.natDegree ≤ w)
    (hagrees : ∀ i ∈ T, P.eval (f (x i)) = f (u₀ i) + γ * f (u₁ i)) :
    ∃ P₀ P₁ : Polynomial F,
      P₀.natDegree ≤ w ∧ P₁.natDegree ≤ w ∧
      (∀ i ∈ T, P₀.eval (x i) = u₀ i ∧ P₁.eval (x i) = u₁ i) ∧
      P = P₀.map f + C γ * P₁.map f := by
  classical
  obtain ⟨S, hST, hS⟩ := Finset.exists_subset_card_eq
    (show w + 1 ≤ T.card from Nat.succ_le_of_lt hT)
  have hxS : Set.InjOn x S := fun _ hi _ hj hij ↦ hx (hST hi) (hST hj) hij
  let P₀ : Polynomial F := Lagrange.interpolate S x u₀
  let P₁ : Polynomial F := Lagrange.interpolate S x u₁
  have h₀ : P₀.natDegree ≤ w := by
    apply natDegree_le_of_degree_le
    simpa only [hS, Nat.add_sub_cancel] using Lagrange.degree_interpolate_le u₀ hxS
  have h₁ : P₁.natDegree ≤ w := by
    apply natDegree_le_of_degree_le
    simpa only [hS, Nat.add_sub_cancel] using Lagrange.degree_interpolate_le u₁ hxS
  have hQ : (P₀.map f + C γ * P₁.map f).natDegree ≤ w := by
    apply (natDegree_add_le _ _).trans
    exact max_le (natDegree_map_le.trans h₀)
      ((natDegree_C_mul_le γ _).trans (natDegree_map_le.trans h₁))
  have hxK : Set.InjOn (fun i ↦ f (x i)) S :=
    fun _ hi _ hj hij ↦ hxS hi hj (f.injective hij)
  have hws : w < S.card := by omega
  have degree_lt (Q : Polynomial K) (hQ : Q.natDegree ≤ w) :
      Q.degree < (S.card : WithBot ℕ) :=
    lt_of_le_of_lt degree_le_natDegree
      (WithBot.coe_lt_coe.mpr (hQ.trans_lt hws))
  have heq : P = P₀.map f + C γ * P₁.map f := by
    apply eq_of_degrees_lt_of_eval_index_eq S hxK (degree_lt P hP) (degree_lt _ hQ)
    intro i hi
    have h₀i : P₀.eval (x i) = u₀ i := Lagrange.eval_interpolate_at_node u₀ hxS hi
    have h₁i : P₁.eval (x i) = u₁ i := Lagrange.eval_interpolate_at_node u₁ hxS hi
    simpa only [eval_add, eval_mul, eval_C, eval_map_apply, h₀i, h₁i]
      using hagrees i (hST hi)
  refine ⟨P₀, P₁, h₀, h₁, ?_, heq⟩
  intro i hi
  have hi' : f (P₀.eval (x i)) + γ * f (P₁.eval (x i)) =
      f (u₀ i) + γ * f (u₁ i) := by
    simpa only [heq, eval_add, eval_mul, eval_C, eval_map_apply] using hagrees i hi
  have hz : f (P₀.eval (x i) - u₀ i) + γ * f (P₁.eval (x i) - u₁ i) = 0 := by
    rw [map_sub, map_sub]
    linear_combination hi'
  obtain ⟨h₀i, h₁i⟩ := affine_relation_eq_zero f γ hγ _ _ hz
  exact ⟨sub_eq_zero.mp h₀i, sub_eq_zero.mp h₁i⟩

/-- Failure of simultaneous interpolation makes an agreement parameter a base-field element. -/
theorem parameter_mem_range_of_not_simultaneously_interpolable
    {ι : Type*} (f : F →+* K) (T : Finset ι) (x u₀ u₁ : ι → F)
    (w : ℕ) (hT : w < T.card) (hx : Set.InjOn x T)
    (γ : K) (P : Polynomial K) (hP : P.natDegree ≤ w)
    (hagrees : ∀ i ∈ T, P.eval (f (x i)) = f (u₀ i) + γ * f (u₁ i))
    (hnot : ¬∃ P₀ P₁ : Polynomial F,
      P₀.natDegree ≤ w ∧ P₁.natDegree ≤ w ∧
      ∀ i ∈ T, P₀.eval (x i) = u₀ i ∧ P₁.eval (x i) = u₁ i) :
    γ ∈ Set.range f := by
  by_contra hγ
  obtain ⟨P₀, P₁, h₀, h₁, hi, _⟩ :=
    basefield_interpolants_of_parameter_not_mem_range f T x u₀ u₁ w hT hx γ hγ P hP hagrees
  exact hnot ⟨P₀, P₁, h₀, h₁, hi⟩

theorem card_le_basefield_of_mem_range [Fintype F]
    (f : F →+* K) (Γ : Finset K) (hΓ : ∀ γ ∈ Γ, γ ∈ Set.range f) :
    Γ.card ≤ Fintype.card F := by
  classical
  have hsub : Γ ⊆ Finset.univ.image f := by
    intro γ hγ
    obtain ⟨a, rfl⟩ := hΓ γ hγ
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
  exact (Finset.card_le_card hsub).trans
    (Finset.card_image_le.trans (by simp))

end MCASubfieldDescent

open Polynomial MCASubfieldDescent

theorem solution {F K : Type*} [Field F] [Field K] [Fintype F]
    {ι : Type*} (f : F →+* K) (x u₀ u₁ : ι → F) (w : ℕ) (Γ : Finset K)
    (hΓ : ∀ γ ∈ Γ, ∃ T : Finset ι, ∃ P : Polynomial K,
      w < T.card ∧ Set.InjOn x T ∧ P.natDegree ≤ w ∧
      (∀ i ∈ T, P.eval (f (x i)) = f (u₀ i) + γ * f (u₁ i)) ∧
      ¬∃ P₀ P₁ : Polynomial F,
        P₀.natDegree ≤ w ∧ P₁.natDegree ≤ w ∧
        ∀ i ∈ T, P₀.eval (x i) = u₀ i ∧ P₁.eval (x i) = u₁ i) :
    Γ.card ≤ Fintype.card F := by
  apply card_le_basefield_of_mem_range f Γ
  intro γ hγ
  obtain ⟨T, P, hT, hx, hP, hagrees, hnot⟩ := hΓ γ hγ
  exact parameter_mem_range_of_not_simultaneously_interpolable
    f T x u₀ u₁ w hT hx γ P hP hagrees hnot

