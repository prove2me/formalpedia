-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Sandwich.exists_smul_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:40:38.106813+00:00
-- url     : https://prove2.me/submissions/8cb4dd04-4cfa-45e2-a654-0bc4b8ad5542

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTraceMulOfSeparableGenerated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmulMemOfSpanEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullLatticeSandwichBetweenIntegralElements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Sandwich
variable {K : UQ} (B : InvAlg K)
namespace GlobalTheory.UnitLemma.Sandwich
theorem _root_.solution (x : B.A) : ∃ d : K.O, d ≠ 0 ∧ IsIntegral K.O (d • x) := by
  have h : IsAlgebraic K.E x := Algebra.IsAlgebraic.isAlgebraic x
  have h' : IsAlgebraic K.O x := (IsFractionRing.isAlgebraic_iff K.O K.E B.A).2 h
  obtain ⟨d, hd, hi⟩ := h'.exists_integral_multiple
  exact ⟨d, hd, hi⟩
end GlobalTheory.UnitLemma.Sandwich
