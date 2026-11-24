-- Prove2me | solution 1 for GlobalTheory.RegSS.CycAlg.exists_lowPoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:55:11.373067+00:00
-- url     : https://prove2.me/submissions/f1fd4ebe-60d6-4dcc-bc80-d48b19b661c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorGeneratedAlgebraStructure
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
open Matrix Polynomial GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open GlobalTheory GlobalTheory.RegSS GlobalTheory.RegSS.CycAlg
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.RegSS.CycAlg
theorem _root_.solution (M : Matrix n n A) (p : A[X]) :
    ∃ c : n → A, p %ₘ M.charpoly = lowPoly c := by
  nontriviality A
  have h : (p %ₘ M.charpoly).degree < Fintype.card n := by
    rw [← Matrix.charpoly_degree_eq_dim M]
    exact degree_modByMonic_lt p M.charpoly_monic
  refine ⟨fun j => (p %ₘ M.charpoly).coeff (Fintype.equivFin n j), ?_⟩
  conv_lhs => rw [← Polynomial.sum_C_mul_X_pow_eq (p %ₘ M.charpoly),
    Polynomial.sum_fin _ (by simp) h |>.symm]
  rw [lowPoly, ← Equiv.sum_comp (Fintype.equivFin n)]
  simp [Polynomial.smul_eq_C_mul]
end GlobalTheory.RegSS.CycAlg
