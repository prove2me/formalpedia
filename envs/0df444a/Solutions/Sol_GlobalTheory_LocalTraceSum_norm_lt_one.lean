-- Prove2me | solution 1 for GlobalTheory.LocalTraceSum.norm_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:51:14.942802+00:00
-- url     : https://prove2.me/submissions/72a38b13-fd26-4196-8ab4-542180f1d14b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TraceEqSumLocalTracesAbovePrime
import Theorems.Thm_GlobalTheory_LocalTraceSum_tendsto_pow
import Theorems.Thm_GlobalTheory_LocalTraceSum_continuous_algHom
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



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
    (τ : K →ₐ[ℚ_[l]] Ω) {x : K} (h : valuation K x < 1) : ‖τ x‖ < 1 := by
  have h1 := ((continuous_algHom hc τ).tendsto 0).comp (tendsto_pow h)
  rw [← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
  simpa [Function.comp_def] using h1
end GlobalTheory.LocalTraceSum
