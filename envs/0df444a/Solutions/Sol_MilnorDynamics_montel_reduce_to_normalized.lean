-- Prove2me | solution 1 for MilnorDynamics.montel_reduce_to_normalized
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T03:25:48.698246+00:00
-- url     : https://prove2.me/submissions/31790150-fcbf-4e36-822a-641ceaab5444
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies
import Theorems.Thm_MilnorDynamics_exists_gl_normalising
import Theorems.Thm_MilnorDynamics_gl_action_continuous
import Theorems.Thm_MilnorDynamics_gl_action_uniformContinuous
import Theorems.Thm_MilnorDynamics_isHolomorphicOn_smul_gl

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- Mobius normalisation, reduced to the four published Mobius children: an
invertible matrix carrying `a,b,c` to `0,1,∞`, continuity and chordal uniform
continuity of the induced sphere map, and preservation of sphere-holomorphy
under postcomposition. -/
theorem solution (a b c : OnePoint ℂ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (U : Set ℂ) (𝓕 : Set (ℂ → OnePoint ℂ))
    (h𝓕 : ∀ f ∈ 𝓕, IsHolomorphicOn U f ∧ ∀ z ∈ U, f z ≠ a ∧ f z ≠ b ∧ f z ≠ c) :
    ∃ 𝓖 : Set (ℂ → OnePoint ℂ),
      (∀ g ∈ 𝓖, IsHolomorphicOn U g ∧
        ∀ z ∈ U, g z ≠ ((0 : ℂ) : OnePoint ℂ) ∧ g z ≠ ((1 : ℂ) : OnePoint ℂ) ∧ g z ≠ ∞) ∧
      (IsNormalFamily U 𝓖 → IsNormalFamily U 𝓕) := by
  obtain ⟨g₀, hg₀a, hg₀b, hg₀c⟩ := exists_gl_normalising a b c hab hac hbc
  have hinj : ∀ {x y : OnePoint ℂ}, g₀ • x = g₀ • y → x = y := by
    intro x y h
    have h' := congrArg (fun t => g₀⁻¹ • t) h
    simpa [inv_smul_smul] using h'
  refine ⟨(fun f => fun z => g₀ • f z) '' 𝓕, ?_, ?_⟩
  · rintro h ⟨f, hf, rfl⟩
    obtain ⟨hhol, homit⟩ := h𝓕 f hf
    refine ⟨isHolomorphicOn_smul_gl g₀ U f hhol, ?_⟩
    intro z hz
    obtain ⟨hza, hzb, hzc⟩ := homit z hz
    refine ⟨?_, ?_, ?_⟩
    · intro hc
      simp only [] at hc
      exact hza (hinj (by rw [hc, hg₀a]))
    · intro hc
      simp only [] at hc
      exact hzb (hinj (by rw [hc, hg₀b]))
    · intro hc
      simp only [] at hc
      exact hzc (hinj (by rw [hc, hg₀c]))
  · intro hnorm u hu
    have hmem : ∀ n, (fun z => g₀ • u n z) ∈ (fun f => fun z => g₀ • f z) '' 𝓕 :=
      fun n => ⟨u n, hu n, rfl⟩
    obtain ⟨φ, hφ, g', hg'cont, hg'conv⟩ := hnorm (fun n z => g₀ • u n z) hmem
    refine ⟨φ, hφ, fun z => g₀⁻¹ • g' z, ?_, ?_⟩
    · exact (gl_action_continuous g₀).2.comp_continuousOn hg'cont
    · intro K hKU hK ε hε
      obtain ⟨δ, hδpos, hδc⟩ := (gl_action_uniformContinuous g₀).2 ε hε
      filter_upwards [hg'conv K hKU hK δ hδpos] with n hn
      intro x hx
      have hstep := hδc (g₀ • u (φ n) x) (g' x) (hn x hx)
      simpa [inv_smul_smul] using hstep
