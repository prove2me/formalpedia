-- Prove2me | solution 1 for GlobalTheory.SmulMemOfMemSpan.main
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T04:24:07.779592+00:00
-- url     : https://prove2.me/submissions/2bc41a08-1d65-44fb-b63d-8408927b5c13

import Mathlib


theorem solution : ∀ {R K V : Type} [inst : CommRing R] [IsDomain R] [inst_2 : Field K] [inst_3 : Algebra R K] [IsFractionRing R K] [inst_5 : AddCommGroup V] [inst_6 : Module R V] [inst_7 : Module K V] [IsScalarTower R K V] (M : Submodule R V) {v : V}, v ∈ Submodule.span K (↑M : Set V) → ∃ (a : R), a ≠ (0 : R) ∧ a • v ∈ M := by
  intro R K V _ _ _ _ _ _ _ _ _ M v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1,one_ne_zero,by simpa using hx⟩
  | zero => exact ⟨1,one_ne_zero,by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a,ha,hx⟩ := hx; obtain ⟨b,hb,hy⟩ := hy
    refine ⟨a*b,mul_ne_zero ha hb,?_⟩; rw [smul_add]
    exact M.add_mem (by simpa [smul_smul,mul_comm] using M.smul_mem b hx) (by simpa [smul_smul] using M.smul_mem a hy)
  | smul c x _ hx =>
    obtain ⟨a,ha,hx⟩ := hx
    obtain ⟨b, d, hd⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors R) c
    refine ⟨a*b.val,mul_ne_zero ha (mem_nonZeroDivisors_iff_ne_zero.mp b.property),?_⟩
    rw [mul_smul, ← smul_assoc b.val c x, ← hd, algebraMap_smul, smul_comm a d x]; exact M.smul_mem d hx
