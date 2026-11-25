-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.etaProd_eq_of_everywhereNorm_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:18:25.529816+00:00
-- url     : https://prove2.me/submissions/d676d234-d4b8-4e8e-b916-ddef1f86e84f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AlmostNormFinDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IndexTwoOfFiniteReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsEverywhereNormDivOfEtaProdEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsBasisOfIsQuadraticExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EvenCardOfNotLone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsAlmostNormEtaProdEqNegOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EtaProdEqOfEverywhereNormDiv
import Theorems.Thm_GlobalTheory_QuadSymbol_eta_eq_of_div_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.QuadSymbol
namespace GlobalTheory.QuadSymbol
theorem _root_.solution {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    {x x' : FinFam K} {y y' : InfFam K} (h : EverywhereNorm K L (x / x') (y / y')) :
    etaProd K L x y = etaProd K L x' y' := by
  unfold etaProd
  congr 1
  · exact finprod_congr fun v => eta_eq_of_div_mem (h.1 v)
  · exact Finset.prod_congr rfl fun w _ => eta_eq_of_div_mem (h.2 w)
end GlobalTheory.QuadSymbol
