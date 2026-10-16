-- Prove2me | solution 1 for GroverWiki.phaseOracle_eq_householder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T19:04:58.748514+00:00
-- url     : https://prove2.me/submissions/72e961b9-907f-4b4a-9769-96b09413b3db

import Mathlib
import Definitions.Def_GroverWiki_Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix

open GroverWiki

theorem solution {N : ℕ} (f : Fin N → Fin 2) (ω : Fin N)
    (hω : ∀ x, f x = 1 ↔ x = ω) :
    phaseOracle f = 1 - (2 : ℂ) • vecMulVec (ket ω) (star (ket ω)) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i = ω
    · subst i
      have hf : f ω = 1 := (hω ω).2 rfl
      norm_num [phaseOracle, ket, hf, vecMulVec, Matrix.one_apply]
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
      simp [phaseOracle, ket, hf, vecMulVec, Matrix.one_apply, hi, Ne.symm hi]
  · by_cases hi : i = ω
    · subst i
      simp [phaseOracle, ket, vecMulVec, Matrix.one_apply, hij, Ne.symm hij]
    · simp [phaseOracle, ket, vecMulVec, Matrix.one_apply, hi, Ne.symm hi,
        hij, Ne.symm hij]
