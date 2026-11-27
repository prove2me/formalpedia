-- Prove2me | solution 1 for GlobalTheory.RegSS.eq_sum_of_commute_cols
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T06:25:27.510224+00:00
-- url     : https://prove2.me/submissions/70fabacc-12e5-451d-a859-e913a4966822

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RegularSemisimpleTensorCommutant
import Theorems.Thm_GlobalTheory_RegSS_colMat_mulVec
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.RegSS
theorem _root_.solution {c : n → Matrix n n A} {v : n → A} (hB : IsUnit (colMat c v))
    (hc : ∀ i j, c i * c j = c j * c i) {N : Matrix n n A} (hN : ∀ j, N * c j = c j * N) :
    ∃ a : n → A, ∑ j, a j • c j = N := by
  obtain ⟨a, ha⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hB (N *ᵥ v)
  refine ⟨a, Matrix.toLin'.injective (LinearMap.ext fun y => ?_)⟩
  obtain ⟨t, rfl⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hB y
  have ha' : (∑ j, a j • c j) *ᵥ v = N *ᵥ v := by rw [← colMat_mulVec]; exact ha
  have h1 : N * (∑ j, t j • c j) = (∑ j, t j • c j) * N := by
    simp [Finset.mul_sum, Finset.sum_mul, hN]
  have h2 : (∑ j, a j • c j) * (∑ j, t j • c j) = (∑ j, t j • c j) * (∑ j, a j • c j) :=
    Commute.sum_left _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ =>
      (Commute.smul_left (Commute.smul_right (hc i j) _) _)
  simp only [Matrix.toLin'_apply, colMat_mulVec, Matrix.mulVec_mulVec]
  rw [h1, h2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha']
end GlobalTheory.RegSS
