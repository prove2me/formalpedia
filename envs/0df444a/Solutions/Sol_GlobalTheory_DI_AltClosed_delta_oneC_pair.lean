-- Prove2me | solution 1 for GlobalTheory.DI.AltClosed.delta_oneC_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:08:15.504536+00:00
-- url     : https://prove2.me/submissions/bd761918-4fba-421e-8554-14dad4622515

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_AlternatingProductCocycle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI GlobalTheory.DI.AltClosed
variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι]
namespace GlobalTheory.DI.AltClosed
theorem _root_.solution {x y : ι} (h : x < y) :
    delta (oneC : Finset ι → ExteriorAlgebra K V) {x, y} = 0 := by
  have hne : x ≠ y := ne_of_lt h
  simp only [delta]
  rw [Finset.sum_pair hne]
  have e1 : ({x, y} : Finset ι).erase x = {y} := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, hz' | hz'⟩
      · exact absurd hz' hz
      · exact hz'
    · rintro rfl
      exact ⟨hne.symm, Or.inr rfl⟩
  have e2 : ({x, y} : Finset ι).erase y = {x} := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, hz' | hz'⟩
      · exact hz'
      · exact absurd hz' hz
    · rintro rfl
      exact ⟨hne, Or.inl rfl⟩
  have s1 : GlobalTheory.cubeSign ({x, y} : Finset ι) x = 1 := by
    unfold GlobalTheory.cubeSign
    have : ({z ∈ ({x, y} : Finset ι) | z < x}) = ∅ := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
      rintro (rfl | rfl) hz
      · exact lt_irrefl _ hz
      · exact lt_asymm h hz
    rw [this]
    simp
  have s2 : GlobalTheory.cubeSign ({x, y} : Finset ι) y = -1 := by
    unfold GlobalTheory.cubeSign
    have : ({z ∈ ({x, y} : Finset ι) | z < y}) = {x} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hz⟩
        · rfl
        · exact absurd hz (lt_irrefl _)
      · rintro rfl
        exact ⟨Or.inl rfl, h⟩
    rw [this]
    simp
  rw [e1, e2, s1, s2]
  simp [oneC]
end GlobalTheory.DI.AltClosed
