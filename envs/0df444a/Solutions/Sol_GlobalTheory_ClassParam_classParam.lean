-- Prove2me | solution 1 for GlobalTheory.ClassParam.classParam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:30:43.161975+00:00
-- url     : https://prove2.me/submissions/5ea47eb7-a9cc-44bd-8fc9-2200ba20f307

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Theorems.Thm_GlobalTheory_ClassParam_classParamCM
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PlusPolynomialInclusion_classParam_of_CM


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix Formalism.UG
open GlobalTheory GlobalTheory.ClassParam
namespace GlobalTheory.ClassParam
theorem _root_.solution : GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion.ClassParam :=
  GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion.classParam_of_CM classParamCM
end GlobalTheory.ClassParam
