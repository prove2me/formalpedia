-- Prove2me | solution 1 for LocalLemma.lll_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:23:34.96512+00:00
-- url     : https://prove2.me/submissions/b2713e94-f044-4ea9-b2c6-f500c854989f

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin
public import Definitions.Def_LocalLemmaLib_LocalLemma
public import Theorems.Thm_LocalLemma_measureReal_avoid_insert

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma
namespace LocalLemma
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] {n : ℕ}
    (A : Fin n → Set Ω) (hA : ∀ i, MeasurableSet (A i)) (x : Fin n → ℝ) (hx1 : ∀ i, x i < 1)
    (S : Finset (Fin n))
    (hH : ∀ T ⊂ S, ∀ i ∉ T, μ.real (avoid A T ∩ A i) ≤ x i * μ.real (avoid A T)) :
    ∀ V ⊆ S, (∏ j ∈ V, (1 - x j)) * μ.real (avoid A (S \ V)) ≤ μ.real (avoid A S) := by
  intro V
  induction V using Finset.induction_on with
  | empty => intro _; simp
  | insert j V hjV ih =>
    intro hsub
    have hj : j ∈ S := hsub (Finset.mem_insert_self _ _)
    have hV : V ⊆ S := (Finset.subset_insert _ _).trans hsub
    have hjU : j ∉ S \ insert j V := by simp
    have hUS : S \ insert j V ⊂ S :=
      (Finset.ssubset_iff_of_subset Finset.sdiff_subset).2 ⟨j, hj, hjU⟩
    have hU : S \ V = insert j (S \ insert j V) := by
      ext y; simp only [Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2⟩; by_cases hy : y = j
        · exact Or.inl hy
        · exact Or.inr ⟨h1, by tauto⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨hj, hjV⟩
        · exact ⟨h1, by tauto⟩
    have key := hH _ hUS j hjU
    have e := measureReal_avoid_insert μ A hA (S \ insert j V) j
    have ih' := ih hV
    rw [hU, e] at ih'
    have hprod : 0 ≤ ∏ j ∈ V, (1 - x j) :=
      Finset.prod_nonneg fun i _ => by linarith [hx1 i]
    rw [Finset.prod_insert hjV]
    calc (1 - x j) * (∏ j ∈ V, (1 - x j)) * μ.real (avoid A (S \ insert j V))
        = (∏ j ∈ V, (1 - x j)) * ((1 - x j) * μ.real (avoid A (S \ insert j V))) := by ring
      _ ≤ (∏ j ∈ V, (1 - x j)) * (μ.real (avoid A (S \ insert j V)) -
            μ.real (avoid A (S \ insert j V) ∩ A j)) := by
          apply mul_le_mul_of_nonneg_left _ hprod; linarith
      _ ≤ _ := ih'
end LocalLemma
