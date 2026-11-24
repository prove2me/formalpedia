-- Prove2me | solution 1 for GlobalTheory.MinorFrame.colSub_scalAt_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:17:49.542682+00:00
-- url     : https://prove2.me/submissions/96178bbb-c25d-45f7-889d-1a4df40e271e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralDetCharacterFockColumnSubstitutionEqZero
import Theorems.Thm_GlobalTheory_MinorFrame_colSub_scalAt_X
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
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
open Classical MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.MinorFrame
open MvPolynomial
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.MinorFrame
theorem _root_.solution {d a : ℕ} (τ₀ : ι) (ζ : ℂ) (t : Var ι d a →₀ ℕ) (c : ℂ) :
    colSub (scalAt τ₀ ζ) (monomial t c : Pol ι d a) = monomial t (c * ζ ^ degAt τ₀ t) := by
  unfold colSub
  rw [aeval_monomial]
  simp only [colSub_scalAt_X, mul_pow, Finsupp.prod_mul]
  have h1 : (t.prod fun y k => (C (if y.1 = τ₀ then ζ else 1) : Pol ι d a) ^ k) = C (ζ ^ degAt τ₀ t) := by
    unfold Finsupp.prod degAt Finsupp.sum
    rw [← Finset.prod_pow_eq_pow_sum, map_prod]
    refine Finset.prod_congr rfl fun y _ => ?_
    beta_reduce
    split_ifs <;> simp
  rw [h1, ← monomial_eq, algebraMap_eq, C_mul_monomial]
end GlobalTheory.MinorFrame
