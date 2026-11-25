-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.TensorPlaceNorm.fockF_eq_fockS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:55:38.662438+00:00
-- url     : https://prove2.me/submissions/2c2e409a-bc59-4985-933e-f76e7bb1af61

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
theorem _root_.solution {σ : Type} (f : MvPolynomial σ ℂ) : Formalism.REAL.fockF f f = fockS f f := by
  unfold Formalism.REAL.fockF fockS mfact
  refine Finset.sum_congr rfl fun m _ => ?_
  ring
end GlobalTheory.IndefiniteRowSideFullHecke.TensorPlaceNorm
