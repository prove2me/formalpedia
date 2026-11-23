-- Prove2me | solution 1 for GrothendieckConstant.affine_constraint_transfer
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:26:21.384706+00:00
-- url     : https://prove2.me/submissions/2af21cb9-ade9-479c-be6e-d20eb2fabf97
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GrothendieckConstantDefs
import Definitions.Def_KrivineSchemeDefs
import Theorems.Thm_GrothendieckLB_lemma_10_2
import Theorems.Thm_GrothendieckLB_majorant_barrier
import Theorems.Thm_GrothendieckLB_limiting_mixed_affine_constraint

open Filter Topology
open GrothendieckConstant

theorem solution (lam : ℝ) (hlam : 1 / 2 ≤ lam)
    (hcon : ∀ (k : ℕ) (S : KrivineScheme k),
      (1 + lam) * coeffLinear S - (lam + 5 / 6) ≤ coeffCubic S) :
    Real.pi * (1 + lam) / (2 * (lam + 5 / 6)) ≤ grothendieckConst := by
  let Γ : ℝ := (lam + 5 / 6) / (1 + lam)
  have hA : 0 < 1 + lam := by linarith
  have hC : 0 < lam + 5 / 6 := by linarith
  have hΓ : 0 < Γ := div_pos hC hA
  obtain ⟨H, γ, hdata, hγlim, hKGlim⟩ := GrothendieckLB.lemma_10_2
  have hbound : ∀ k, γ k ≤ Γ := by
    intro k
    rcases hdata k with ⟨hodd, han, hlim, hadm, hγupper⟩
    have hb := GrothendieckLB.limiting_mixed_affine_constraint lam hcon (H k) hlim
    apply GrothendieckLB.majorant_barrier lam hlam hodd han ?_ hb.2 hb.1 hadm
    simpa [GrothendieckLB.taylorCoeff] using hadm.2.2.1
  have hpoint : ∀ k, Real.pi / (2 * Γ) ≤ Real.pi / (2 * γ k) := by
    intro k
    have hγ : 0 < γ k := (hdata k).2.2.2.1.2.2.2.1
    have hle := hbound k
    gcongr
  have hfinal : Real.pi / (2 * Γ) ≤ grothendieckConst :=
    ge_of_tendsto hKGlim (Filter.Eventually.of_forall hpoint)
  have heq : Real.pi / (2 * Γ) = Real.pi * (1 + lam) / (2 * (lam + 5 / 6)) := by
    dsimp [Γ]
    field_simp
  rw [← heq]
  exact hfinal
