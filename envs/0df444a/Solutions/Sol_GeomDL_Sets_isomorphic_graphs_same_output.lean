-- Prove2me | solution 1 for GeomDL.Sets.isomorphic_graphs_same_output
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T19:37:59.440342+00:00
-- url     : https://prove2.me/submissions/3d5b4d7c-c565-4e26-978b-6e5c6c7ce51e

import Mathlib
import Definitions.Def_GeomDL_Sets_Defs

open GeomDL.Sets

theorem solution {n d d' : ℕ} {Y : Type*}
    (f : Matrix (Fin n) (Fin d) ℝ → Matrix (Fin n) (Fin n) ℝ → Y)
    (F : Matrix (Fin n) (Fin d) ℝ → Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin d') ℝ)
    (hf : IsGraphPermInvariant f) (hF : IsGraphPermEquivariant F)
    (σ : Equiv.Perm (Fin n)) (X X' : Matrix (Fin n) (Fin d) ℝ) (A A' : Matrix (Fin n) (Fin n) ℝ)
    (hA : A' = permAdj σ A) (hX : X' = permRows σ X) :
    f X' A' = f X A ∧ ∀ u : Fin n, F X' A' (σ u) = F X A u := by
  subst hA hX
  refine ⟨hf σ X A, fun u => ?_⟩
  rw [hF σ X A]
  ext j
  simp [permRows]
