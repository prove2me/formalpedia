-- Prove2me | solution 1 for GlobalTheory.isLogBounded_iff_exists_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:57:55.004333+00:00
-- url     : https://prove2.me/submissions/8f8014f6-ea72-448c-b0af-e449a2bce12c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_inv_le_inv_of_posDef_of_le
import Theorems.Thm_GlobalTheory_inv_real_smul_of_posDef
import Theorems.Thm_GlobalTheory_le_re_trace_smul_one_of_posSemidef


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
variable {κ κ' X X' m n : Type*} [TopologicalSpace X] [TopologicalSpace X']
variable [DecidableEq n] [DecidableEq m] {S : Finset κ} {w : X → κ → ℂ} {U : Set X}
  {G G' : X → Matrix n n ℂ} {H : X → Matrix m m ℂ}
variable [Fintype n]
namespace GlobalTheory
theorem _root_.solution : IsLogBounded S w U G ↔
    ∃ g : X → ℝ, IsLogBoundedScalar S w U g ∧ ∀ x ∈ U, x ∉ coordDivisor S w →
      (g x)⁻¹ • (1 : Matrix n n ℂ) ≤ G x ∧ G x ≤ g x • (1 : Matrix n n ℂ) := by
  refine ⟨fun h => ?_, fun ⟨g, hg, h⟩ =>
    .of_le hg.hasLogGrowth fun x hx hB => ⟨hg.pos hx hB, h x hx hB⟩⟩
  have hp : ∀ x, 1 ≤ 1 + ‖(G x).trace‖ + ‖(G x)⁻¹.trace‖ := fun x => by
    linarith [norm_nonneg (G x).trace, norm_nonneg (G x)⁻¹.trace]
  refine ⟨fun x => 1 + ‖(G x).trace‖ + ‖(G x)⁻¹.trace‖, isLogBoundedScalar_iff.2
    ⟨fun x _ _ => one_pos.trans_le (hp x), ((HasLogGrowth.const (1 : ℝ)).add
      h.hasLogGrowthEntries.trace.norm).add h.hasLogGrowthEntries_inv.trace.norm,
      (HasLogGrowth.const (1 : ℝ)).of_le fun x _ _ => ?_⟩, fun x hx hB => ?_⟩
  · rw [Real.norm_of_nonneg (inv_nonneg.2 (zero_le_one.trans (hp x)))]
    exact inv_le_one_of_one_le₀ (hp x)
  have hG := h.posDef hx hB
  let _ := hG.isUnit.invertible
  refine ⟨?_, (le_re_trace_smul_one_of_posSemidef hG.posSemidef).trans
    (real_smul_one_le_real_smul_one ?_)⟩
  · have h3 : (G x)⁻¹ ≤ (1 + ‖(G x).trace‖ + ‖(G x)⁻¹.trace‖) • (1 : Matrix n n ℂ) :=
      (le_re_trace_smul_one_of_posSemidef hG.inv.posSemidef).trans
        (real_smul_one_le_real_smul_one (by
          linarith [RCLike.re_le_norm (G x)⁻¹.trace, norm_nonneg (G x).trace]))
    have h4 := inv_le_inv_of_posDef_of_le hG.inv h3
    rwa [inv_real_smul_of_posDef PosDef.one (one_pos.trans_le (hp x)).ne', inv_one,
      inv_inv_of_invertible] at h4
  · linarith [RCLike.re_le_norm (G x).trace, norm_nonneg (G x)⁻¹.trace]
end GlobalTheory
