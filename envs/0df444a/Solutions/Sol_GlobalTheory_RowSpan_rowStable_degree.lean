-- Prove2me | solution 1 for GlobalTheory.RowSpan.rowStable_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:15:38.953558+00:00
-- url     : https://prove2.me/submissions/d14f0f3b-7fcd-4c94-8d40-4b1c6b092115

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_EqZeroOfFischSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowSpan
open MvPolynomial Formalism.L2.Pj
variable {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k]
namespace GlobalTheory.RowSpan
theorem _root_.solution (D : ℕ) : RowStable (restrictTotalDegree (Letter T r n) k D) := by
  intro g _ P hP
  rw [← sum_homogeneousComponent P, map_sum]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [mem_restrictTotalDegree] at hP ⊢
  have h : (rowAct g (homogeneousComponent i P)).IsHomogeneous (1 * i) :=
    (homogeneousComponent_isHomogeneous i P).aeval _ fun ℓ =>
      IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_X k _).C_mul _
  have := h.totalDegree_le
  rw [Finset.mem_range] at hi
  omega
end GlobalTheory.RowSpan
