-- Prove2me | solution 1 for GlobalTheory.ClassParam.classParamCM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:12:06.06405+00:00
-- url     : https://prove2.me/submissions/05887dab-ac69-43a6-87d7-5afff15b6666

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Theorems.Thm_GlobalTheory_ClassParam_classParamAt
import Theorems.Thm_GlobalTheory_ClassParam_discAt
import Theorems.Thm_GlobalTheory_ClassParam_quad_facts

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
theorem _root_.solution : GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion.ClassParamCM := by
  intro F E _ _ _ _ _ _ _ h2 c hc1 r P hP
  obtain ⟨hc, hF⟩ := quad_facts h2 hc1
  exact ⟨⟨classParamAt _ hP hc, discAt _ hP hc hc1 hF⟩,
    fun _ => ⟨classParamAt _ hP hc, discAt _ hP hc hc1 hF⟩,
    fun _ => ⟨classParamAt _ hP hc, discAt _ hP hc hc1 hF⟩⟩
end GlobalTheory.ClassParam
