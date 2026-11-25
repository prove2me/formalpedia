-- Prove2me | solution 1 for GlobalTheory.LocalTraceSum.norm_l_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:27:54.195718+00:00
-- url     : https://prove2.me/submissions/6439a5b4-664e-42bd-aba0-d9f1fc716ac9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TraceEqSumLocalTracesAbovePrime
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
variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime]
  {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra ℚ_[l] K] {Ω : Type} [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]
namespace GlobalTheory.LocalTraceSum
theorem _root_.solution : ‖(l : Ω)‖ < 1 := by
  have : (l : Ω) = algebraMap ℚ_[l] Ω l := by simp
  rw [this, norm_algebraMap']
  exact Padic.norm_p_lt_one
end GlobalTheory.LocalTraceSum
