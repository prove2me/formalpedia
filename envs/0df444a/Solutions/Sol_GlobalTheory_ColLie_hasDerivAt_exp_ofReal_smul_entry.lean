-- Prove2me | solution 1 for GlobalTheory.ColLie.hasDerivAt_exp_ofReal_smul_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:31:53.08266+00:00
-- url     : https://prove2.me/submissions/0680803f-c588-4e54-94c5-bd47a9cf2d7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColDerApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasDerivAtCoeffFockColumnSubstitutionExp
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.ColLie
open GlobalTheory.MinorFrame
variable {ι : Type} [DecidableEq ι]
namespace GlobalTheory.ColLie
theorem _root_.solution {a : ℕ} (S : Matrix (Fin a) (Fin a) ℂ) (i j : Fin a) :
    HasDerivAt (fun h : ℝ => NormedSpace.exp ((h : ℂ) • S) i j) (S i j) 0 := by
  open scoped Matrix.Norms.Operator in
  have h2 := ((Matrix.entryLinearMap ℝ ℂ i j).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) S 0)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  simp only [Complex.coe_smul]
  exact h2
end GlobalTheory.ColLie
