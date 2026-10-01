-- Prove2me | solution 2 for MilnorDynamics.either_limit_avoids_or_diverges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T22:50:18.090422+00:00
-- url     : https://prove2.me/submissions/2db155ae-f73b-4e8f-b354-69cf0978af77

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies
import Theorems.Thm_MilnorDynamics_limit_avoids_or_const
import Theorems.Thm_MilnorDynamics_diverges_of_tendsto_const_puncture

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- Repair of the second variant, with the same cause fixed: the two omission
facts are extracted separately from `MapsTo` by applying it to the membership
proof alone, and the constant branches are written out one by one. -/
theorem solution (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({0, 1}ᶜ : Set ℂ))
    (g : ℂ → ℂ) (hg : ContinuousOn g U)
    (hc : TendstoLocallyUniformlyOn f g atTop U) :
    MapsTo g U ({0, 1}ᶜ : Set ℂ) ∨
      DivergesLocallyUniformlyFrom f U ({0, 1}ᶜ : Set ℂ) := by
  have hne0 : ∀ n, ∀ z ∈ U, f n z ≠ 0 := by
    intro n z hz hmem
    have h : f n z ∈ ({0, 1}ᶜ : Set ℂ) := (hf n).2 hz
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h
    exact h.1 hmem
  have hne1 : ∀ n, ∀ z ∈ U, f n z ≠ 1 := by
    intro n z hz hmem
    have h : f n z ∈ ({0, 1}ᶜ : Set ℂ) := (hf n).2 hz
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h
    exact h.2 hmem
  have hf0 : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({0}ᶜ : Set ℂ) :=
    fun n => ⟨(hf n).1, fun z hz hmem => hne0 n z hz (by simpa using hmem)⟩
  have hf1 : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({1}ᶜ : Set ℂ) :=
    fun n => ⟨(hf n).1, fun z hz hmem => hne1 n z hz (by simpa using hmem)⟩
  have hconst0 : (∀ z ∈ U, g z = 0) → TendstoLocallyUniformlyOn f (fun _ => (0 : ℂ)) atTop U := by
    intro hg0
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
    intro K hKU hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hc K hKU hK)) ε hε] with n hn
    intro x hx
    simpa [hg0 x (hKU hx)] using hn x hx
  have hconst1 : (∀ z ∈ U, g z = 1) → TendstoLocallyUniformlyOn f (fun _ => (1 : ℂ)) atTop U := by
    intro hg1
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
    intro K hKU hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hc K hKU hK)) ε hε] with n hn
    intro x hx
    simpa [hg1 x (hKU hx)] using hn x hx
  rcases limit_avoids_or_const U hU hUc f 0 hf0 g hg hc with h0 | h0
  · rcases limit_avoids_or_const U hU hUc f 1 hf1 g hg hc with h1 | h1
    · refine Or.inl ?_
      intro z hz
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (h | h)
      · exact h0 z hz h
      · exact h1 z hz h
    · exact Or.inr (diverges_of_tendsto_const_puncture U hU f 1 (hconst1 h1) (by simp))
  · exact Or.inr (diverges_of_tendsto_const_puncture U hU f 0 (hconst0 h0) (by simp))
