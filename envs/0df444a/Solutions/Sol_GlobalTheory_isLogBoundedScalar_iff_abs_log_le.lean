-- Prove2me | solution 1 for GlobalTheory.isLogBoundedScalar_iff_abs_log_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:57:53.545954+00:00
-- url     : https://prove2.me/submissions/5535f825-af9b-4800-9166-ff8a8cb01cbe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues

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
variable {κ κ' X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']
variable {S : Finset κ} {w : X → κ → ℂ} {U : Set X} {g g' : X → ℝ}
namespace GlobalTheory
theorem _root_.solution : IsLogBoundedScalar S w U g ↔
    (∀ x ∈ U, x ∉ coordDivisor S w → 0 < g x) ∧ ∀ K ⊆ U, IsCompact K → ∃ (C : ℝ) (N : ℕ),
      ∀ x ∈ K, x ∉ coordDivisor S w →
        |Real.log (g x)| ≤ C + N * Real.log (lwP₂ S (w x)) := by
  refine ⟨fun h => ⟨fun x => h.pos, fun K hKU hK => ?_⟩, fun ⟨h0, h⟩ K hKU hK => ?_⟩
  · obtain ⟨C, N, hC, h'⟩ := h K hKU hK
    refine ⟨Real.log C, N, fun x hx hB => ?_⟩
    have hw := pow_pos (logWeight_pos S (w x)) N
    rw [← Real.log_pow, ← Real.log_mul hC.ne' hw.ne', abs_le, ← Real.log_inv]
    exact ⟨Real.log_le_log (inv_pos.2 (mul_pos hC hw)) (h' x hx hB).1,
      Real.log_le_log (h.pos (hKU hx) hB) (h' x hx hB).2⟩
  · obtain ⟨C, N, h'⟩ := h K hKU hK
    refine ⟨Real.exp C, N, Real.exp_pos C, fun x hx hB => ?_⟩
    have hw := pow_pos (logWeight_pos S (w x)) N
    have hl := mul_pos (Real.exp_pos C) hw
    have h3 := h' x hx hB
    rw [← Real.log_pow, ← Real.log_exp C, ← Real.log_mul (Real.exp_pos C).ne' hw.ne', abs_le,
      ← Real.log_inv] at h3
    exact ⟨(Real.log_le_log_iff (inv_pos.2 hl) (h0 x (hKU hx) hB)).1 h3.1,
      (Real.log_le_log_iff (h0 x (hKU hx) hB) hl).1 h3.2⟩
end GlobalTheory
