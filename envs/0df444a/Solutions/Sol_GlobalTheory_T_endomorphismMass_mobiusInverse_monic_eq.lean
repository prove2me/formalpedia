-- Prove2me | solution 1 for GlobalTheory.T.endomorphismMass_mobiusInverse_monic_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:03:25.000804+00:00
-- url     : https://prove2.me/submissions/c5d668c4-c5ad-4df6-80ac-2f27ef72add8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassMobiusInverseMonicEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EndomorphismMassMobiusInverseMonicEqStatement
import Theorems.Thm_GlobalTheory_CuspGL_mass_psi_eq_glCard_mul_mangoldt_div


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
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → ∀ P : F[X], P.Monic → P.natDegree = Module.finrank F V → mass (psi s V) P = glCard F P.natDegree * mangoldt s P / ((Nat.card F : ℂ) ^ P.natDegree - 1) := by
  first | exact @GlobalTheory.CuspGL.mass_psi_eq_glCard_mul_mangoldt_div | exact GlobalTheory.CuspGL.mass_psi_eq_glCard_mul_mangoldt_div | (intros; apply GlobalTheory.CuspGL.mass_psi_eq_glCard_mul_mangoldt_div <;> assumption)
end _root_.GlobalTheory.T
