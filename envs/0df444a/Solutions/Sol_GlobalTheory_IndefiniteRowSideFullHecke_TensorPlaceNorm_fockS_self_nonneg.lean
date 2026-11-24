-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.TensorPlaceNorm.fockS_self_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:39:47.086264+00:00
-- url     : https://prove2.me/submissions/0c4dd6a0-b77b-4487-960a-0201c54f33b9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TensorPlaceNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.TensorPlaceNorm
open Formalism.BasicNotions Formalism.L2.DIV
variable {ι : Type} [Fintype ι] {n n' : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorPlaceNorm
theorem _root_.solution {σ : Type} (f : MvPolynomial σ ℂ) : ∃ r : ℝ, 0 ≤ r ∧ fockS f f = r := by
  refine ⟨∑ m ∈ f.support, ‖f.coeff m‖ ^ 2 * (mfact m : ℝ), by positivity, ?_⟩
  unfold fockS
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Complex.conj_mul']
  rfl
end GlobalTheory.IndefiniteRowSideFullHecke.TensorPlaceNorm
