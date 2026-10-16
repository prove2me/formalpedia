-- Prove2me | solution 1 for GroverWiki.phaseOracle_reflection_perp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T13:01:06.397328+00:00
-- url     : https://prove2.me/submissions/172ef1cd-352d-475e-be93-1239841b406f

import Mathlib
import Definitions.Def_GroverWiki_Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix

open GroverWiki

theorem solution {N : ℕ} (f : Fin N → Fin 2) (ω : Fin N)
    (hω : ∀ x, f x = 1 ↔ x = ω) (a b : ℂ) :
    phaseOracle f *ᵥ (a • ket ω + b • perpState ω) = (-a) • ket ω + b • perpState ω := by
  classical
  ext i
  by_cases hi : i = ω
  · subst i
    have hf : f ω = 1 := (hω ω).2 rfl
    simp [phaseOracle, mulVec_diagonal, hf, ket, perpState]
  · have hf : f i = 0 := by
      have hn : f i ≠ 1 := fun he => hi ((hω i).1 he)
      apply Fin.ext
      have hv := (f i).isLt
      have hnval : (f i).val ≠ 1 := by
        intro he
        apply hn
        apply Fin.ext
        exact he
      change (f i).val = 0
      omega
    simp [phaseOracle, mulVec_diagonal, hf, ket, perpState, hi, Ne.symm hi]
