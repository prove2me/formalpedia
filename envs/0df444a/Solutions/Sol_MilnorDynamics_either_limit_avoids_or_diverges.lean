-- Prove2me | solution 1 for MilnorDynamics.either_limit_avoids_or_diverges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T22:50:12.055898+00:00
-- url     : https://prove2.me/submissions/d0cca9f6-d5ea-4f2a-a160-fa2efe535658

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies
import Theorems.Thm_MilnorDynamics_limit_avoids_or_const
import Theorems.Thm_MilnorDynamics_diverges_of_tendsto_const_puncture

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- Repair of the first variant: `MapsTo` carries an implicit argument, so the
membership hypothesis `(hf n).2` is applied to `hz` alone and the point is
recovered by unification against the ascribed goal. -/
theorem solution (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({0, 1}ᶜ : Set ℂ))
    (g : ℂ → ℂ) (hg : ContinuousOn g U)
    (hc : TendstoLocallyUniformlyOn f g atTop U) :
    MapsTo g U ({0, 1}ᶜ : Set ℂ) ∨
      DivergesLocallyUniformlyFrom f U ({0, 1}ᶜ : Set ℂ) := by
  have hne : ∀ n, ∀ z ∈ U, f n z ≠ 0 ∧ f n z ≠ 1 := by
    intro n z hz
    have h : f n z ∈ ({0, 1}ᶜ : Set ℂ) := (hf n).2 hz
    simpa only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using h
  have hf0 : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({0}ᶜ : Set ℂ) :=
    fun n => ⟨(hf n).1, fun z hz hmem => (hne n z hz).1 (by simpa using hmem)⟩
  have hf1 : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({1}ᶜ : Set ℂ) :=
    fun n => ⟨(hf n).1, fun z hz hmem => (hne n z hz).2 (by simpa using hmem)⟩
  have hconst : ∀ c : ℂ, (∀ z ∈ U, g z = c) →
      TendstoLocallyUniformlyOn f (fun _ => c) atTop U := by
    intro c hgc
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
    intro K hKU hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hc K hKU hK)) ε hε] with n hn
    intro x hx
    simpa [hgc x (hKU hx)] using hn x hx
  rcases limit_avoids_or_const U hU hUc f 0 hf0 g hg hc with h0 | h0
  · rcases limit_avoids_or_const U hU hUc f 1 hf1 g hg hc with h1 | h1
    · refine Or.inl ?_
      intro z hz
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨h0 z hz, h1 z hz⟩
    · exact Or.inr (diverges_of_tendsto_const_puncture U hU f 1 (hconst 1 h1) (by simp))
  · exact Or.inr (diverges_of_tendsto_const_puncture U hU f 0 (hconst 0 h0) (by simp))
