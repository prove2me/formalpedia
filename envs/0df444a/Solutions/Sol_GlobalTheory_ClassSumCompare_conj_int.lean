-- Prove2me | solution 1 for GlobalTheory.ClassSumCompare.conj_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:29:31.895835+00:00
-- url     : https://prove2.me/submissions/60984427-b0ec-4b71-9ffb-4ba83abb4452

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdelicNormWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNatMulInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassSumCompare
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight
open scoped TensorProduct nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
namespace GlobalTheory.ClassSumCompare
theorem _root_.solution (a : 𝓞 E) : ∃ b : 𝓞 E, (b : E) = IsCMField.complexConj E (a : E) :=
  ⟨RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv a, rfl⟩
end GlobalTheory.ClassSumCompare
