-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.exists_eq_smul_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:57:52.636115+00:00
-- url     : https://prove2.me/submissions/d104a678-9ae9-4689-b126-049c051b4627

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow

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
open Module Set
variable {M : Type*} [Monoid M] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]
variable (ρ : Representation ℂ M V)
variable {ρ} {e : End ℂ V}
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution [ρ.IsIrreducible] (he : IsWinProj ρ e)
    (hne : LinearMap.range e ≠ ⊥) [FiniteDimensional ℂ (LinearMap.range e)] {T : End ℂ V}
    (hTρ : ∀ m, T * ρ m = ρ m * T) (hTe : T * e = e * T) : ∃ c : ℂ, T = c • 1 := by
  have : Nontrivial (LinearMap.range e) := Submodule.nontrivial_iff_ne_bot.2 hne
  let T' : End ℂ (LinearMap.range e) := LinearMap.codRestrict _ (T ∘ₗ (LinearMap.range e).subtype)
    fun x => by
      obtain ⟨w, hw⟩ := x.2
      refine ⟨T w, ?_⟩
      rw [← Module.End.mul_apply, ← hTe, Module.End.mul_apply, hw]
      rfl
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T'
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  refine ⟨c, ?_⟩

  let Y : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker (T - c • 1)
      apply_mem_toSubmodule := fun m v hv => by
        rw [LinearMap.mem_ker] at hv ⊢
        rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, ← Module.End.mul_apply,
          hTρ, Module.End.mul_apply, ← map_smul, ← map_sub]
        rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hv
        rw [hv, map_zero] }
  have hxY : (x : V) ∈ Y.toSubmodule := by
    have := hx.apply_eq_smul
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero]
    exact congrArg Subtype.val this
  rcases IsSimpleOrder.eq_bot_or_eq_top Y with h | h
  · exfalso
    rw [h] at hxY
    exact hx.2 (Subtype.ext hxY)
  · ext v
    have : v ∈ Y.toSubmodule := by rw [h]; trivial
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
end GroundTheory.Automorphic.RestrictedTensor
