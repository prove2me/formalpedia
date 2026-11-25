-- Prove2me | solution 1 for GlobalTheory.IsUnitMulMonomialOn.hasLogGrowth_logWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:08:41.700144+00:00
-- url     : https://prove2.me/submissions/5629e1ef-f798-465b-a6fa-b81ded18b1e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_notMem_coordDivisor
import Theorems.Thm_GlobalTheory_HasLogGrowth_log_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set Filter
open scoped ComplexOrder MatrixOrder Kronecker Topology
open GlobalTheory
variable {κ κ' X X' E F : Type*} [TopologicalSpace X] [TopologicalSpace X']
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
variable {S : Finset κ} {w : X → κ → ℂ} {U : Set X}
open GlobalTheory.IsUnitMulMonomialOn
variable {S' : Finset κ'} {w' : X' → κ' → ℂ} {U' : Set X'} {v : X' → κ → ℂ}
namespace GlobalTheory.IsUnitMulMonomialOn
theorem _root_.solution (h : IsUnitMulMonomialOn S v S' w' U') :
    HasLogGrowth S' w' U' fun x => lwP₂ S (v x) := by
  refine (HasLogGrowth.const 1).add (HasLogGrowth.sum (f := fun j x => |Real.log ‖v x j‖|)
    fun j hj => ?_)
  obtain ⟨u, m, hc, hu⟩ := h j hj
  have h1 : HasLogGrowth S' w' U' fun x => Real.log ‖u x‖ :=
    .of_continuousOn (hc.norm.log fun x hx => norm_ne_zero_iff.2 (hu x hx).1)
  have h2 : HasLogGrowth S' w' U' fun x => ∑ i ∈ S', (m i : ℝ) * Real.log ‖w' x i‖ :=
    .sum (f := fun i x => (m i : ℝ) * Real.log ‖w' x i‖)
      fun i hi => (HasLogGrowth.const _).mul (.log_norm hi)
  refine (h1.add h2).norm.congr fun x hx hB => ?_
  rw [notMem_coordDivisor] at hB
  have h3 : ∀ i ∈ S', ‖w' x i ^ m i‖ ≠ 0 := fun i hi => norm_ne_zero_iff.2 (pow_ne_zero _ (hB i hi))
  rw [(hu x hx).2, norm_mul, norm_prod, Real.log_mul (norm_ne_zero_iff.2 (hu x hx).1)
    (Finset.prod_ne_zero_iff.2 h3), Real.log_prod h3]
  simp
end GlobalTheory.IsUnitMulMonomialOn
