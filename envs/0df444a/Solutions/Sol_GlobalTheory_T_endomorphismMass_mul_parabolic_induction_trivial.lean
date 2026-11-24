-- Prove2me | solution 1 for GlobalTheory.T.endomorphismMass_mul_parabolic_induction_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:14:34.292804+00:00
-- url     : https://prove2.me/submissions/3a027d3a-8a3d-489d-a8f2-bdb9692bef0b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassMulParabolicInductionTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassMulParabolicInductionTrivialStatement
import Theorems.Thm_GlobalTheory_CuspGL_MassMult_mass_mult


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
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Φ : ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V], Module.End F V → ℂ), (∀ (V V' : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (e : V ≃ₗ[F] V') (g : Module.End F V), Φ V' (e.conj g) = Φ V g) → ∀ P : F[X], P.Monic → P.natDegree = Module.finrank F V → mass (fun g : Module.End F V => ∑ᶠ W : {W : Submodule F V // ∀ x ∈ W, g x ∈ W}, Φ W.1 (g.restrict W.2)) P / glCard F P.natDegree = conv (fun D => mass (Φ (Fin D.natDegree → F)) D / glCard F D.natDegree) mu P := by
  first | exact @GlobalTheory.CuspGL.MassMult.mass_mult | exact GlobalTheory.CuspGL.MassMult.mass_mult | (intros; apply GlobalTheory.CuspGL.MassMult.mass_mult <;> assumption)
end _root_.GlobalTheory.T
