-- Prove2me | solution 1 for GlobalTheory.RowSpan.rowStable_harmK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:25:55.906814+00:00
-- url     : https://prove2.me/submissions/b6b74b3e-8958-4575-a486-d21fd63b014e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_EqZeroOfFischSelf
import Theorems.Thm_GlobalTheory_RowSpan_pderiv_rowAct
import Theorems.Thm_GlobalTheory_RowSpan_mem_harmK_iff
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Wick.dividedContraction_one



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowSpan
open MvPolynomial Formalism.L2.Pj
variable {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k]
namespace GlobalTheory.RowSpan
theorem _root_.solution (cc : T → T) (isX : T → Prop) : RowStable (harmK r n k cc isX (fun _ => 1)) := by
  intro g _ P hP
  rw [mem_harmK_iff] at hP ⊢
  intro τ hτ i i'
  simp only [pderiv_rowAct, map_sum, Derivation.map_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j' _ => ?_
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp only [← Finset.smul_sum, ← map_sum, hP τ hτ, map_zero, smul_zero, Finset.sum_const_zero]
end GlobalTheory.RowSpan
