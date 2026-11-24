-- Prove2me | solution 1 for GlobalTheory.DiscrJacobianBlocks.sum_ite_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:30:17.334022+00:00
-- url     : https://prove2.me/submissions/55acab86-4e47-48db-a42a-c61a26d86ac2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrEqJacobianOfIntegralPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsFactorAssociatedJacobian
import Theorems.Thm_GlobalTheory_DiscrJacobian_der_tmul
import Theorems.Thm_GlobalTheory_DiscrJacobian_mu_tmul
import Theorems.Thm_GlobalTheory_DiscrJacobian_pairing_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.DiscrJacobian.der_tmul
attribute [local simp] GlobalTheory.DiscrJacobian.mu_tmul
attribute [local simp] GlobalTheory.DiscrJacobian.pairing_tmul



set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.DiscrJacobianBlocks
namespace GlobalTheory.DiscrJacobianBlocks
theorem _root_.solution {M Y : Type} [AddCommMonoid M] [DecidableEq Y] {d : ℕ} (p : Fin d → Y)
    (y : Y) (f : Fin d → M) :
    (∑ a, if y = p a then f a else 0) = ∑ x : {a // p a = y}, f x.1 := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun a => by simp [eq_comm]) f
end GlobalTheory.DiscrJacobianBlocks
