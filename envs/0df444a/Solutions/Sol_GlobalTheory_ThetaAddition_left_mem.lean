-- Prove2me | solution 1 for GlobalTheory.ThetaAddition.left_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:48:45.149801+00:00
-- url     : https://prove2.me/submissions/dee5efe8-e3d9-4660-93e6-e9c56f6e4eb3

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_SpanEvalEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AdditionLevelTwoMul
import Theorems.Thm_ReciprocityTheory_PTheta_eC_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaAddition
namespace GlobalTheory.ThetaAddition
theorem _root_.solution {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (N : ℕ) {f f' : (Fin g → ℂ) → ℂ}
    (hf : f ∈ thetaLevel N τ) (hf' : f' ∈ thetaLevel N τ) (w : Fin g → ℂ) :
    (fun z => f (z + w) * f' (z - w)) ∈ thetaLevel (2 * N) τ := by
  refine ⟨(hf.1.comp (by fun_prop)).mul (hf'.1.comp (by fun_prop)), fun n n' z => ?_⟩
  have e1 : z + τ *ᵥ ofIntVec n + ofIntVec n' + w = (z + w) + τ *ᵥ ofIntVec n + ofIntVec n' := by
    abel
  have e2 : z + τ *ᵥ ofIntVec n + ofIntVec n' - w = (z - w) + τ *ᵥ ofIntVec n + ofIntVec n' := by
    abel
  show f _ * f' _ = _ * (f _ * f' _)
  rw [e1, e2, hf.2, hf'.2, mul_mul_mul_comm, ← eC_add]
  congr 2
  rw [dotProduct_add, dotProduct_sub]; push_cast; ring
end GlobalTheory.ThetaAddition
