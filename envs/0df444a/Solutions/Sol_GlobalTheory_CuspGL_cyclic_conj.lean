-- Prove2me | solution 1 for GlobalTheory.CuspGL.cyclic_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:06:52.781793+00:00
-- url     : https://prove2.me/submissions/61fb6a40-bc53-4e54-af7c-04df265de9ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassMulParabolicInductionTrivialStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FinsumCardCyclicVectorsInvariantSubspacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassOfCharpolyCardCyclicVectorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyEndomorphismDensityGLRecursion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution {F : Type} [Field F] {V V' : Type} [AddCommGroup V] [Module F V]
    [AddCommGroup V'] [Module F V'] (e : V ≃ₗ[F] V') (g : Module.End F V) (v : V) :
    (∀ U : Submodule F V, (∀ x ∈ U, g x ∈ U) → v ∈ U → U = ⊤) ↔
      (∀ U : Submodule F V', (∀ x ∈ U, (e.conj g) x ∈ U) → e v ∈ U → U = ⊤) := by
  constructor
  · intro h U hU hv
    have h1 : U.comap (e : V →ₗ[F] V') = ⊤ := by
      refine h _ (fun x hx => ?_) hv
      have := hU (e x) hx
      simpa [LinearEquiv.conj_apply] using this
    refine eq_top_iff.2 fun y _ => ?_
    have : e.symm y ∈ U.comap (e : V →ₗ[F] V') := h1 ▸ Submodule.mem_top
    simpa using this
  · intro h U hU hv
    have h1 : U.comap (e.symm : V' →ₗ[F] V) = ⊤ := by
      refine h _ (fun x hx => ?_) (by simpa using hv)
      have := hU (e.symm x) hx
      simpa [LinearEquiv.conj_apply] using this
    refine eq_top_iff.2 fun y _ => ?_
    have : e y ∈ U.comap (e.symm : V' →ₗ[F] V) := h1 ▸ Submodule.mem_top
    simpa using this
end GlobalTheory.CuspGL
