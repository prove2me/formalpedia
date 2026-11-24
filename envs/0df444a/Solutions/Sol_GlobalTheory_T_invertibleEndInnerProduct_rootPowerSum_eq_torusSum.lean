-- Prove2me | solution 1 for GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_eq_torusSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:43:56.702806+00:00
-- url     : https://prove2.me/submissions/a76fe5a1-cd22-417d-a470-767d51ec3c78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndInnerProductRootPowerSumEqTorusSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InvertibleEndInnerProductRootPowerSumEqTorusSumStatement
import Theorems.Thm_GlobalTheory_CuspGL_ipGL_rootSum_eq_sum_torus


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
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ) (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → 0 < Module.finrank F V → ∀ l : ℕ, ipGL φ (fun g : Module.End F V => rootSum θ l (LinearMap.charpoly g)) = ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ Module.finrank F V - 1) = 1}, ((Module.finrank F V / (minpoly F α).natDegree : ℕ) : ℂ) * mass φ (minpoly F α ^ (Module.finrank F V / (minpoly F α).natDegree)) * star (θ α ^ l) := by
  first | exact @GlobalTheory.CuspGL.ipGL_rootSum_eq_sum_torus | exact GlobalTheory.CuspGL.ipGL_rootSum_eq_sum_torus | (intros; apply GlobalTheory.CuspGL.ipGL_rootSum_eq_sum_torus <;> assumption)
end _root_.GlobalTheory.T
