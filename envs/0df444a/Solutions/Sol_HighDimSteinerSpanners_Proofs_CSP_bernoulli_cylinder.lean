-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.bernoulli_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:49:15.256341+00:00
-- url     : https://prove2.me/submissions/63772684-73d0-4c79-bf03-44fb8b817428

module
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessProjection
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Bernoulli

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) : ∀ S : Finset ι,
    ∑ ω : ι → Bool, (if ∀ i ∈ S, ω i = true then bernWeight p ω else 0) = ∏ i ∈ S, p i := by
  intro S
  let T : ι → Finset Bool := fun i => if i ∈ S then {true} else Finset.univ
  let g : ι → Bool → ℝ := fun i b => if b = true then p i else 1 - p i
  have hfilt : Finset.univ.filter (fun ω : ι → Bool => ∀ i ∈ S, ω i = true) =
      Fintype.piFinset T := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, T]
    constructor
    · intro h i
      by_cases hi : i ∈ S
      · rw [if_pos hi, h i hi]
        exact Finset.mem_singleton_self true
      · rw [if_neg hi]
        exact Finset.mem_univ (ω i)
    · intro h i hi
      have hi' := h i
      rw [if_pos hi] at hi'
      exact Finset.mem_singleton.mp hi'
  have hsum1 : ∑ ω : ι → Bool, (if ∀ i ∈ S, ω i = true then bernWeight p ω else 0) =
      ∑ ω ∈ Fintype.piFinset T, ∏ i : ι, g i (ω i) := by
    rw [← Finset.sum_filter, hfilt]
    rfl
  rw [hsum1, ← Finset.prod_univ_sum T g]
  have hfiber : ∀ i : ι, ∑ b ∈ T i, g i b = if i ∈ S then p i else 1 := by
    intro i
    by_cases hi : i ∈ S
    · simp only [T, if_pos hi, Finset.sum_singleton, g, ↓reduceIte]
    · simp only [T, if_neg hi]
      rw [Fintype.sum_bool]
      dsimp [g]
      ring
  have hprod : (∏ i : ι, ∑ b ∈ T i, g i b) = ∏ i ∈ Finset.univ, if i ∈ S then p i else 1 :=
    Finset.prod_congr rfl (fun i _ => hfiber i)
  rw [hprod, Finset.prod_ite_mem Finset.univ S p, Finset.univ_inter]
end HighDimSteinerSpanners.Proofs.CSP
