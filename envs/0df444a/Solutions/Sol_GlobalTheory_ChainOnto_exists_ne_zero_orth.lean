-- Prove2me | solution 1 for GlobalTheory.ChainOnto.exists_ne_zero_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:32:16.485437+00:00
-- url     : https://prove2.me/submissions/3c17fe9a-3207-4df0-a6a7-82849e7d3d21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SurjectiveOfAdjointSeparatesLabelledParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.ChainOnto
namespace GlobalTheory.ChainOnto
theorem _root_.solution {A : Type} [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
    (ipA : A →ₗ[ℂ] A →ₗ⋆[ℂ] ℂ) (hsym : ∀ x y, ipA x y = conj (ipA y x))
    (S : Submodule ℂ A) (hS : S ≠ ⊤) : ∃ u : A, u ≠ 0 ∧ ∀ s ∈ S, ipA s u = 0 := by
  classical
  let b := Module.finBasis ℂ S
  let f : A →ₗ[ℂ] (Fin (Module.finrank ℂ S) → ℂ) :=
    { toFun := fun u i => ipA u (b i : A)
      map_add' := by intro x y; ext i; simp
      map_smul' := by intro a x; ext i; simp }
  have hlt : Module.finrank ℂ (Fin (Module.finrank ℂ S) → ℂ) < Module.finrank ℂ A := by
    rw [Module.finrank_fin_fun]
    exact Submodule.finrank_lt hS
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := f) hlt
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp hker
  refine ⟨u, hu0, fun s hs => ?_⟩
  have hzero : (ipA u).comp S.subtype = 0 := by
    refine b.ext fun i => ?_
    have := congrFun (LinearMap.mem_ker.mp hu) i
    simpa [f] using this
  have : ipA u s = 0 := by
    have := LinearMap.congr_fun hzero ⟨s, hs⟩
    simpa using this
  rw [hsym, this, map_zero]
end GlobalTheory.ChainOnto
