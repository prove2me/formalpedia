-- Prove2me | solution 1 for GlobalTheory.ClassSumCompare.incl_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:26:44.382261+00:00
-- url     : https://prove2.me/submissions/23c0ea04-c3f0-4c89-b420-73c76b17899b

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
theorem _root_.solution {a : AdF E} (ha : ∀ v : Plc E, a v ∈ v.adicCompletionIntegers (maximalRealSubfield E)) :
    inclF E a ∈ intAd E := Subring.subset_closure (Or.inl ⟨a, ha, rfl⟩)
end GlobalTheory.ClassSumCompare
