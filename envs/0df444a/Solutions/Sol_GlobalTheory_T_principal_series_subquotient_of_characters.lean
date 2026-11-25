-- Prove2me | solution 1 for GlobalTheory.T.principal_series_subquotient_of_characters
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:24:48.360744+00:00
-- url     : https://prove2.me/submissions/c7c423f9-6bf3-43c8-9c07-a4a3b0f34ce3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PrincipalSeriesSubquotientOfCharacters
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviEmbMulSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PrincipalSeriesSubquotientOfCharactersStatement
import Theorems.Thm_GlobalTheory_PrinProd_isSubquotient_prinSeries_multiProd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (χ : Fin N → kˣ →* ℂˣ), IsSubquotient (prinSeries χ) (multiProd (Equiv.sigmaUnique (Fin N) fun _ => Fin 1) fun i => detRep (Fin 1) (χ i)) := by
  first | exact @GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd | exact GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd | (intros; apply GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd <;> assumption)
end _root_.GlobalTheory.T
