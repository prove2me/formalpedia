-- Prove2me | solution 1 for GlobalTheory.TensorNormCompare.extremal_fock_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:25:36.507564+00:00
-- url     : https://prove2.me/submissions/286f920e-d38e-4e2b-8cc0-be130e9ea7e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TensorPlaceNorm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TensorNormBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TensorNormLeIffTensorNormBound
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwNe


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
open GlobalTheory GlobalTheory.TensorNormCompare
open Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke
variable {ι : Type} [Fintype ι] {n n' : ℕ}
namespace GlobalTheory.TensorNormCompare
theorem _root_.solution (lam : DomWeight n) : 0 < (fockS (extremal ℂ n lam) (extremal ℂ n lam)).re :=
  fockS_re_pos' (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl lam.natW)
end GlobalTheory.TensorNormCompare
