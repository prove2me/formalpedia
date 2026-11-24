-- Prove2me | solution 1 for GlobalTheory.matrix_commutant_lift_mod_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:28:13.323657+00:00
-- url     : https://prove2.me/submissions/d2aab6e9-efa9-4222-bd1a-eb49bb406752

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommutantLiftModStableSelfAdjoint
import Theorems.Thm_GlobalTheory_matrix_exists_sub_mem_trace_orthogonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : Set (Matrix ι ι ℂ))
      (N : Submodule ℂ (Matrix ι ι ℂ)), (∀ x ∈ S, xᴴ ∈ S) →
      (∀ x ∈ S, ∀ y ∈ N, x * y - y * x ∈ N) → ∀ M : Matrix ι ι ℂ,
      (∀ x ∈ S, x * M - M * x ∈ N) →
      ∃ M₀ : Matrix ι ι ℂ, M - M₀ ∈ N ∧ ∀ x ∈ S, x * M₀ = M₀ * x := by
  intro ι _ _ S N hS hN M hM
  obtain ⟨M₀, h1, h2⟩ := matrix_exists_sub_mem_trace_orthogonal N M
  refine ⟨M₀, h1, fun x hx => ?_⟩
  have hw : x * M₀ - M₀ * x ∈ N := by
    have := N.sub_mem (hM x hx) (hN x hx _ h1)
    convert this using 1
    noncomm_ring
  set w := x * M₀ - M₀ * x with hwdef
  have h3 := h2 _ (hN _ (hS x hx) w hw)
  have h4 : (wᴴ * w).trace = 0 := by
    rw [← h3]
    have : (wᴴ * (M₀ * x)).trace = (x * wᴴ * M₀).trace := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    conv_lhs => rw [hwdef, Matrix.mul_sub, ← hwdef]
    rw [Matrix.trace_sub, this]
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.sub_mul, Matrix.mul_assoc]
  open scoped ComplexOrder in
  exact sub_eq_zero.1 (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h4)
end GlobalTheory
