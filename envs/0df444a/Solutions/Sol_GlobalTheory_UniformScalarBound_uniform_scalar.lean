-- Prove2me | solution 1 for GlobalTheory.UniformScalarBound.uniform_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:22:41.144187+00:00
-- url     : https://prove2.me/submissions/fd39bc32-48ab-40ca-884d-83d1ec6d09f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UniformScalarBound
namespace GlobalTheory.UniformScalarBound
theorem _root_.solution {R V : Type} [CommRing R] [IsDomain R] [AddCommGroup V] [Module R V]
    (A B : Submodule R V) (hA : A.FG) (h : ∀ x ∈ A, ∃ s : R, s ≠ 0 ∧ s • x ∈ B) :
    ∃ s : R, s ≠ 0 ∧ ∀ x ∈ A, s • x ∈ B := by
  classical
  obtain ⟨S, rfl⟩ := hA
  choose! f hf0 hfB using fun x (hx : x ∈ S) => h x (Submodule.subset_span hx)
  refine ⟨∏ g ∈ S, f g, Finset.prod_ne_zero_iff.mpr (fun g hg => hf0 g hg), ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rw [← Finset.mul_prod_erase S f hy, mul_comm, mul_smul]
    exact B.smul_mem _ (hfB y hy)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact B.add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact B.smul_mem a hx
end GlobalTheory.UniformScalarBound
