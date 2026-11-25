-- Prove2me | solution 1 for GlobalTheory.LocalTraceSum.mem_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:31:12.009232+00:00
-- url     : https://prove2.me/submissions/1d43065d-2545-4700-a059-9a4d0ffd9146

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TraceEqSumLocalTracesAbovePrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.LocalTraceSum
open Filter Topology TensorProduct
variable {F : Type} [Field F] [NumberField F] {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω]
namespace GlobalTheory.LocalTraceSum
theorem _root_.solution (σ : F →+* Ω) (a : 𝓞 F) : a ∈ ker σ ↔ ‖σ a‖ < 1 := Iff.rfl
end GlobalTheory.LocalTraceSum
