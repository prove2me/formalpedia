-- Prove2me | solution 1 for GlobalTheory.T.innerProduct_rootPowerSum_eq_of_frobenius_modEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:21:18.549802+00:00
-- url     : https://prove2.me/submissions/44f3ee1d-1326-430e-914d-1583c6c3ae1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InnerProductRootPowerSumEqOfFrobeniusModEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InnerProductRootPowerSumEqOfFrobeniusModEqStatement
import Theorems.Thm_GlobalTheory_CuspGL_ipGL_rootSum_eq_of_modEq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ) (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → 0 < Module.finrank F V → ∀ k l i : ℕ, k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ Module.finrank F V - 1)] → ipGL φ (fun g : Module.End F V => rootSum θ k (LinearMap.charpoly g)) = ipGL φ (fun g : Module.End F V => rootSum θ l (LinearMap.charpoly g)) := by
  first | exact @GlobalTheory.CuspGL.ipGL_rootSum_eq_of_modEq | exact GlobalTheory.CuspGL.ipGL_rootSum_eq_of_modEq | (intros; apply GlobalTheory.CuspGL.ipGL_rootSum_eq_of_modEq <;> assumption)
end _root_.GlobalTheory.T
