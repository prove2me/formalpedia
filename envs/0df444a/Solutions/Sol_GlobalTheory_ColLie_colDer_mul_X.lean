-- Prove2me | solution 1 for GlobalTheory.ColLie.colDer_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:31:43.217379+00:00
-- url     : https://prove2.me/submissions/640a9357-db5e-4ae1-9afc-6c4295108e1e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColDerApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasDerivAtCoeffFockColumnSubstitutionExp
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_ColLie_colDer_apply
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
theorem _root_.solution {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) (R : Pol ι d a) (v : Var ι d a) :
    colDer τ S (R * X v) = colDer τ S R * X v + R * colDer τ S (X v) := by
  simp only [colDer_apply, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [pderiv_mul]
  simp only [smul_eq_C_mul]
  ring
end GlobalTheory.ColLie
