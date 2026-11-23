-- Prove2me | solution 1 for GlobalTheory.LatticeBoundedAction.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:03.267006+00:00
-- url     : https://prove2.me/submissions/72bc710a-e6cf-493d-b5f5-262892ef8f60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LatticeBoundedAction
namespace GlobalTheory.LatticeBoundedAction
theorem _root_.solution {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {V : Type} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (Λ : Submodule R V) :
    ∀ v ∈ Submodule.span K (↑Λ : Set V), ∃ (d : R), d ≠ (0 : R) ∧ d • v ∈ Λ := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem _ h₁
    · rw [mul_smul]; exact Λ.smul_mem _ h₂
  | smul c x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) c
    have hb : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
    have key : (b : R) • (c • x) = a • x := by
      rw [← smul_assoc, Algebra.smul_def, ← hab, mul_comm, IsLocalization.mk'_spec, algebraMap_smul]
    refine ⟨d * b, mul_ne_zero hd hb, ?_⟩
    rw [mul_smul, key, smul_comm]
    exact Λ.smul_mem a h
end GlobalTheory.LatticeBoundedAction
