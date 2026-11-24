-- Prove2me | solution 1 for GlobalTheory.SmulMemOfMemSpan.exists_smul_mem_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:53:40.122667+00:00
-- url     : https://prove2.me/submissions/7a1115cf-7901-4771-bcfe-5ce8665fea3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SmulMemOfMemSpan
namespace GlobalTheory.SmulMemOfMemSpan
theorem _root_.solution {R K V : Type} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V]
    [IsScalarTower R K V] (M : Submodule R V) {v : V}
    (hv : v ∈ Submodule.span K (M : Set V)) : ∃ a : R, a ≠ 0 ∧ a • v ∈ M := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm a b, mul_smul]; exact M.smul_mem b hax
    · rw [mul_smul]; exact M.smul_mem a hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors R) c
    dsimp only at hnd
    refine ⟨d * a, mul_ne_zero (nonZeroDivisors.ne_zero d.2) ha, ?_⟩
    have key : (d : R) • c • x = n • x := by
      rw [← algebraMap_smul K (d : R) (c • x), smul_smul, mul_comm, hnd, algebraMap_smul]
    rw [mul_comm (d : R) a, mul_smul, key, smul_comm a n x]
    exact M.smul_mem n hax
end GlobalTheory.SmulMemOfMemSpan
