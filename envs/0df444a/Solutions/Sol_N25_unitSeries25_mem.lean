-- Prove2me | solution 1 for N25.unitSeries25_mem
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:56.875323+00:00
-- url     : https://prove2.me/submissions/47525529-7572-405a-a76b-a5ed78480d2c

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_unitNumeratorForm25
import Theorems.Thm_N25_unitDenominatorForm25
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Theorems.Thm_N25_unitDenominatorSeries25_ne_zero
import Definitions.Def_N25_UnitSeries

set_option autoImplicit false

namespace N25

/-- The frozen unpowered Laurent quotient belongs to the literal carrier. -/
theorem _root_.solution (K : Type*) [Field K] (i : Fin 5) :
    unitSeries25 K i ∈ ModularCurve.xHFunctionFieldC K 25 N25.H25 := by
  obtain ⟨F, _, hF⟩ := unitNumeratorForm25 i
  obtain ⟨G, _, hG⟩ := unitDenominatorForm25
  exact ModularCurve.div_mem_qExpFunctionFieldC F G hF hG (unitDenominatorSeries25_ne_zero K)

end N25
