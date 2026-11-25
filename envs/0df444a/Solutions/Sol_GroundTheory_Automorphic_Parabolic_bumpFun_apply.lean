-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.bumpFun_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:40.865133+00:00
-- url     : https://prove2.me/submissions/3561d0f2-7749-495b-995d-c43412558599

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {β : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)
variable {σ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {x : GL (Fin n) F} {K : Subgroup (GL (Fin n) F)} {v : W}
    (hv : ∀ p : blockUpper F n β, (p : GL (Fin n) F) ∈ K.map (MulAut.conj x).toMonoidHom →
      inflateTwist F n β σ p v = v)
    (p : blockUpper F n β) {k : GL (Fin n) F} (hk : k ∈ K) :
    bumpFun σ x K v ((p : GL (Fin n) F) * x * k) = inflateTwist F n β σ p v := by
  unfold bumpFun
  have h : ∃ p' : blockUpper F n β, ∃ k' ∈ K,
      (p : GL (Fin n) F) * x * k = (p' : GL (Fin n) F) * x * k' := ⟨p, k, hk, rfl⟩
  rw [dif_pos h]
  obtain ⟨k', hk', he⟩ := h.choose_spec
  set p' := h.choose
  have hmem : ((p'⁻¹ * p : blockUpper F n β) : GL (Fin n) F) ∈
      K.map (MulAut.conj x).toMonoidHom := by
    refine ⟨k' * k⁻¹, K.mul_mem hk' (K.inv_mem hk), ?_⟩
    show x * (k' * k⁻¹) * x⁻¹ = (p' : GL (Fin n) F)⁻¹ * p
    have : (p : GL (Fin n) F) = p' * x * k' * k⁻¹ * x⁻¹ := by
      rw [← he]
      group
    rw [this]
    group
  calc inflateTwist F n β σ p' v
      = inflateTwist F n β σ p' (inflateTwist F n β σ (p'⁻¹ * p) v) := by rw [hv _ hmem]
    _ = inflateTwist F n β σ p v := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
end GroundTheory.Automorphic.Parabolic
