-- Prove2me | solution 1 for GlobalTheory.LatticeRep.exists_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:04:38.855421+00:00
-- url     : https://prove2.me/submissions/f17d8e37-8e0a-4b85-85c0-a75ab2c55f73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqSelfOfTrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.LatticeRep
variable {R X M Γ : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] [Group Γ]
variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} {lam : ℕ →* ℂ} {A : Submodule R X}
  {ρ : Γ →* Module.End R X} {Om : Γ →* Module.End ℂ M}
namespace GlobalTheory.LatticeRep
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (N : Submodule ℂ V) (O : Γ →* Module.End ℂ N) :
    ∃ om : Γ →* Module.End ℂ V, ∀ g (m : N), om g m = O g m := by
  obtain ⟨C, hC⟩ := N.exists_isCompl
  let e := Submodule.prodEquivOfIsCompl N C hC
  let P : Γ →* Module.End ℂ (N × C) :=
    { toFun := fun g => (O g).prodMap LinearMap.id
      map_one' := by rw [map_one]; exact LinearMap.prodMap_one
      map_mul' := fun g k => by rw [map_mul, LinearMap.prodMap_mul]; rfl }
  refine ⟨(e.conjRingEquiv.toMonoidHom).comp P, fun g m => ?_⟩
  show e (P g (e.symm m)) = _
  rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
  simp [P, e]
end GlobalTheory.LatticeRep
