-- Prove2me | solution 1 for GlobalTheory.LocalTraceSum.continuous_algHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:41:46.351811+00:00
-- url     : https://prove2.me/submissions/1e6a5fff-f270-43b3-841e-f4c7924d254b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TraceEqSumLocalTracesAbovePrime
import Theorems.Thm_GlobalTheory_LocalTraceSum_t2
import Theorems.Thm_GlobalTheory_LocalTraceSum_contSMul

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
variable {Ω : Type} [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]
namespace GlobalTheory.LocalTraceSum
theorem _root_.solution [FiniteDimensional ℚ_[l] K] (hc : Continuous (algebraMap ℚ_[l] K))
    (τ : K →ₐ[ℚ_[l]] Ω) : Continuous τ := by
  have := contSMul hc
  have : T2Space K := t2
  exact τ.toLinearMap.continuous_of_finiteDimensional
end GlobalTheory.LocalTraceSum
