-- Prove2me | solution 1 for GlobalTheory.T.endomorphismMass_eq_of_linearEquiv_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:23:51.044948+00:00
-- url     : https://prove2.me/submissions/e01da06e-3dd5-43c5-b36f-89dddcd58fed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassEqOfLinearEquivInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassEqOfLinearEquivInvariantStatement
import Theorems.Thm_GlobalTheory_CuspGL_mass_eq_mass_pi_of_invariant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Φ : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V], Module.End F V → ℂ), (∀ (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (e : V ≃ₗ[F] V') (g : Module.End F V), Φ V' (e.conj g) = Φ V g) → ∀ P : F[X], P.natDegree = Module.finrank F V → mass (Φ V) P = mass (Φ (Fin P.natDegree → F)) P := by
  first | exact @GlobalTheory.CuspGL.mass_eq_mass_pi_of_invariant | exact GlobalTheory.CuspGL.mass_eq_mass_pi_of_invariant | (intros; apply GlobalTheory.CuspGL.mass_eq_mass_pi_of_invariant <;> assumption)
end _root_.GlobalTheory.T
