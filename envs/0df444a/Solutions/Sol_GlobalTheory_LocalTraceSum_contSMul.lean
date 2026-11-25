-- Prove2me | solution 1 for GlobalTheory.LocalTraceSum.contSMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:30:35.982414+00:00
-- url     : https://prove2.me/submissions/04cadbc6-91d8-4ea8-acdf-bd5d965f6c14

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
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {l : ℕ} [Fact l.Prime] [Algebra ℚ_[l] K]
namespace GlobalTheory.LocalTraceSum
theorem _root_.solution (hc : Continuous (algebraMap ℚ_[l] K)) : ContinuousSMul ℚ_[l] K :=
  continuousSMul_of_algebraMap _ _ hc
end GlobalTheory.LocalTraceSum
