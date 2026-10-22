-- Prove2me | solution 1 for GeomDL.Sets.eq_6_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T19:33:53.322441+00:00
-- url     : https://prove2.me/submissions/19cbee79-daf6-42cb-b530-e7f2e79a6c4e

import Mathlib
import Definitions.Def_GeomDL_Sets_Defs

open GeomDL.Sets

theorem solution {n d : ℕ} {M Y : Type*} [AddCommMonoid M] (φ : M → Y)
    (ψ : (Fin d → ℝ) → M) :
    IsPermInvariant (sumReadout φ ψ : Matrix (Fin n) (Fin d) ℝ → Y) := by
  intro σ X
  unfold sumReadout permRows
  congr 1
  exact Equiv.sum_comp σ.symm (fun u => ψ (X u))
