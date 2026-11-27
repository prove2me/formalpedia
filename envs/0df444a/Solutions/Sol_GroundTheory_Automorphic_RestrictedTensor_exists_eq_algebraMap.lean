-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.exists_eq_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:44:41.685996+00:00
-- url     : https://prove2.me/submissions/4e151efc-39a7-4765-87d5-e76977b6eb22

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Module
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable [FiniteDimensional ℂ M]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {T : Set (End ℂ M)} (h : IsSimpleUnder T) {φ : End ℂ M}
    (hφ : ∀ t ∈ T, Commute φ t) : ∃ c : ℂ, φ = algebraMap ℂ (End ℂ M) c := by
  have := h.1
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue φ
  refine ⟨c, ?_⟩
  have hst : IsStable T (LinearMap.ker (φ - algebraMap ℂ (End ℂ M) c)) := by
    intro t ht x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have h1 : (φ - algebraMap ℂ (End ℂ M) c) * t = t * (φ - algebraMap ℂ (End ℂ M) c) :=
      ((hφ t ht).sub_left (Algebra.commutes' c t)).eq
    have := congrArg (fun g : End ℂ M => g x) h1
    simp only [Module.End.mul_apply, hx, map_zero] at this
    exact this
  rcases h.2 _ hst with h0 | h0
  · exfalso
    apply hc.exists_hasEigenvector.elim
    intro x hx
    have hx1 : x ∈ LinearMap.ker (φ - algebraMap ℂ (End ℂ M) c) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, hx.apply_eq_smul]
      simp [Algebra.algebraMap_eq_smul_one]
    rw [h0, Submodule.mem_bot] at hx1
    exact hx.2 hx1
  · ext x
    have hx : x ∈ LinearMap.ker (φ - algebraMap ℂ (End ℂ M) c) := by rw [h0]; trivial
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hx
    exact hx
end GroundTheory.Automorphic.RestrictedTensor
