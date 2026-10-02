-- Prove2me | solution 1 for MilnorDynamics.montel_reduce_to_normalized_open
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T17:46:00.879742+00:00
-- url     : https://prove2.me/submissions/66441818-fd0f-49f0-895c-821fd0f17db3

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies
import Theorems.Thm_MilnorDynamics_exists_gl_normalising
import Theorems.Thm_MilnorDynamics_gl_action_continuous
import Theorems.Thm_MilnorDynamics_gl_action_uniformContinuous
import Theorems.Thm_MilnorDynamics_isHolomorphicOn_smul_gl_open

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- Mobius normalisation.  Postcompose the family by the invertible matrix `g₀` that carries
`a, b, c` to `0, 1, ∞`; the new family omits `0, 1, ∞`, is again sphere-holomorphic, and its
normality transfers back because `g₀` and `g₀⁻¹` act continuously and uniformly continuously
in the chordal metric. -/
theorem solution (a b c : OnePoint ℂ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (U : Set ℂ) (hU : IsOpen U) (𝓕 : Set (ℂ → OnePoint ℂ))
    (h𝓕 : ∀ f ∈ 𝓕, IsHolomorphicOn U f ∧ ∀ z ∈ U, f z ≠ a ∧ f z ≠ b ∧ f z ≠ c) :
    ∃ 𝓖 : Set (ℂ → OnePoint ℂ),
      (∀ g ∈ 𝓖, IsHolomorphicOn U g ∧
        ∀ z ∈ U, g z ≠ ((0 : ℂ) : OnePoint ℂ) ∧ g z ≠ ((1 : ℂ) : OnePoint ℂ) ∧ g z ≠ ∞) ∧
      (IsNormalFamily U 𝓖 → IsNormalFamily U 𝓕) := by
  obtain ⟨g₀, hg₀a, hg₀b, hg₀c⟩ := exists_gl_normalising a b c hab hac hbc
  have hinj : ∀ {x y : OnePoint ℂ}, g₀ • x = g₀ • y → x = y := by
    intro x y h
    have h' := congrArg (fun t : OnePoint ℂ => g₀⁻¹ • t) h
    simpa using h'
  refine ⟨(fun f : ℂ → OnePoint ℂ => fun z => g₀ • f z) '' 𝓕, ?_, ?_⟩
  · rintro h ⟨f, hf, rfl⟩
    obtain ⟨hhol, homit⟩ := h𝓕 f hf
    refine ⟨isHolomorphicOn_smul_gl_open g₀ U hU f hhol, ?_⟩
    intro z hz
    obtain ⟨hza, hzb, hzc⟩ := homit z hz
    refine ⟨fun hc => hza (hinj (hc.trans hg₀a.symm)),
            fun hc => hzb (hinj (hc.trans hg₀b.symm)),
            fun hc => hzc (hinj (hc.trans hg₀c.symm))⟩
  · intro hnorm u hu
    have hmem : ∀ n, (fun z => g₀ • u n z) ∈ (fun f : ℂ → OnePoint ℂ => fun z => g₀ • f z) '' 𝓕 :=
      fun n => ⟨u n, hu n, rfl⟩
    obtain ⟨φ, hφ, g', hg'cont, hg'conv⟩ := hnorm (fun n z => g₀ • u n z) hmem
    refine ⟨φ, hφ, fun z => g₀⁻¹ • g' z, ?_, ?_⟩
    · exact (gl_action_continuous g₀).2.comp_continuousOn hg'cont
    · intro K hKU hK ε hε
      obtain ⟨δ, hδpos, hδc⟩ := (gl_action_uniformContinuous g₀).2 ε hε
      filter_upwards [hg'conv K hKU hK δ hδpos] with n hn
      intro x hx
      have hstep := hδc (g₀ • u (φ n) x) (g' x) (hn x hx)
      simpa using hstep
