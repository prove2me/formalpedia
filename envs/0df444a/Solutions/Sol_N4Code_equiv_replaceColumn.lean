-- Prove2me | solution 1 for N4Code.equiv_replaceColumn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:30:37.482382+00:00
-- url     : https://prove2.me/submissions/6411c64a-d723-4a52-8ce1-ecf1163df2b7

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} {C C0 : Code n} (h : Equivalent C C0) (t : Fin n)
    (s' : Column) :
    ∃ t' : Fin n, ∃ s'' : Column,
      Equivalent (replaceColumn C t s') (replaceColumn C0 t' s'') := by
  rcases h with ⟨ρ, p, f, hh⟩
  refine ⟨p t, rowPermute ρ (if f t then flipCol s' else s'), ?_⟩
  refine ⟨ρ, p, f, ?_⟩
  intro u
  by_cases hu : u = t
  · subst u
    simp [replaceColumn]
  · have hpu : p u ≠ p t := by
      intro h
      exact hu (p.injective h)
    simp [replaceColumn, hu, hpu, hh u]
end N4Code
