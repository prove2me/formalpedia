-- Prove2me | solution 1 for GlobalTheory.CuspGL.mass_eq_mass_pi_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:05:39.622673+00:00
-- url     : https://prove2.me/submissions/87fb58bd-604c-40f6-9717-d77d17dc41f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassEqOfLinearEquivInvariant

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
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Φ : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V], Module.End F V → ℂ), (∀ (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (e : V ≃ₗ[F] V') (g : Module.End F V), Φ V' (e.conj g) = Φ V g) → ∀ P : F[X], P.natDegree = Module.finrank F V → mass (Φ V) P = mass (Φ (Fin P.natDegree → F)) P := by
  intro F _ _ V _ _ _ Φ hΦ P hP
  let e : V ≃ₗ[F] (Fin P.natDegree → F) := LinearEquiv.ofFinrankEq _ _ (by simp [hP])
  unfold mass
  refine finsum_mem_eq_of_bijOn (fun g => e.conj g) ⟨?_, ?_, ?_⟩ ?_
  · intro g hg
    simpa using hg
  · intro g _ h _ hgh
    simpa using congrArg e.symm.conj hgh
  · intro h hh
    refine ⟨e.symm.conj h, ?_, by simp⟩
    simpa using hh
  · intro g _
    exact (hΦ V _ e g).symm
end GlobalTheory.CuspGL
