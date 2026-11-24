-- Prove2me | solution 1 for GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_mobius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:23:51.93287+00:00
-- url     : https://prove2.me/submissions/2dd0ae65-59e2-4168-9080-0892161ff2fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndInnerProductRootPowerSumMobius
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndInnerProductRootPowerSumMobiusStatement
import Theorems.Thm_GlobalTheory_CuspGL_ipGL_psi_rootSum


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
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → 0 < Module.finrank F V → ∀ k l : ℕ, ipGL (psi (rootSum θ k) V) (fun g : Module.End F V => rootSum θ l (LinearMap.charpoly g)) = glCard F (Module.finrank F V) * (((Finset.range (Module.finrank F V)).filter (fun i => k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ Module.finrank F V - 1)])).card : ℂ) := by
  first | exact @GlobalTheory.CuspGL.ipGL_psi_rootSum | exact GlobalTheory.CuspGL.ipGL_psi_rootSum | (intros; apply GlobalTheory.CuspGL.ipGL_psi_rootSum <;> assumption)
end _root_.GlobalTheory.T
