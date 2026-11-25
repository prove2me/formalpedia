-- Prove2me | solution 1 for GlobalTheory.LastSteps.lastTwoSteps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:21:39.929938+00:00
-- url     : https://prove2.me/submissions/078f66ec-2ad6-444b-983a-8098eb721db1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DualLiftInvariance
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactQLat
import Theorems.Thm_GlobalTheory_LastSteps_latInd_eq_finsum
import Theorems.Thm_GlobalTheory_LastSteps_term_eq_finsum
import Theorems.Thm_GlobalTheory_LastSteps_term_zero
import Theorems.Thm_GlobalTheory_LastSteps_compInd_zero
import Theorems.Thm_GlobalTheory_LastSteps_compInd_eq_phiOne
import Theorems.Thm_GlobalTheory_LastSteps_term_ne_zero
import Theorems.Thm_GlobalTheory_LastSteps_sum_mainDatum
import Theorems.Thm_GlobalTheory_LastSteps_latInd_mul
import Theorems.Thm_GlobalTheory_LastSteps_sum_latInd
import Theorems.Thm_GlobalTheory_LastSteps_lift_latInd
import Theorems.Thm_GlobalTheory_LastSteps_lift_mainDatum
import Theorems.Thm_GlobalTheory_LastSteps_volQ_pos
import Theorems.Thm_GlobalTheory_LastSteps_datumHat_eq
import Theorems.Thm_GlobalTheory_LastSteps_datum_eq
import Theorems.Thm_GlobalTheory_LastSteps_phiOne_last
import Theorems.Thm_P2M_GlobalTheory_LastSteps_phiOne_last__fde6c3287ccb
import Theorems.Thm_GlobalTheory_LastSteps_sum_main_last
import Theorems.Thm_GlobalTheory_LastSteps_sum_datumHat
import Theorems.Thm_GlobalTheory_LastSteps_lift_datumHat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData
noncomputable section
open GlobalTheory GlobalTheory.LastSteps
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' n'' : Type}
namespace GlobalTheory.LastSteps
theorem _root_.solution : LastTwoSteps := by
  intro k _ _ _ _ _ _ n n' n'' _ _ _ _
  refine ⟨fun q ψ hψ ε μ _ P LY _ => ⟨datum_eq q P LY, volQ_pos q μ LY, datumHat_eq q hψ μ LY ε P⟩,
    fun q ψ hψ ε P LY _ => ⟨fun fW x₀ => ⟨latInd_eq_finsum fW, term_eq_finsum q _ _ P fW⟩, term_zero q _ _ P,
      fun fW => ⟨compInd_zero fW, compInd_eq_phiOne fW, term_ne_zero q _ _ P fW⟩, fun L hL =>
        ⟨fun g hg => latInd_mul hg L, fun M _ _ φ hφ => ⟨sum_latInd hφ P.ker L, fun π A _ _ θ he hθ => ?_⟩⟩⟩,
    fun q ψ hψ ε L _ Q M _ _ φ _ => ⟨sum_mainDatum q _ _ L Q φ,
      fun π A _ _ θ he hθ P P' hP hP' => lift_mainDatum q _ _ he hθ Q hP hP'⟩,
    fun q LY _ L'' _ => ⟨fun fW x' η => ⟨phiOne_last q LY L'' fW x' η, phiOne_last' q LY L'' x' η fW⟩,
      fun ψ hψ ε L _ M _ _ φ hφ x' η => ⟨sum_main_last q LY L'' x' η _ _ L φ, fun μ _ =>
        ⟨sum_datumHat q LY L'' x' η hψ ε μ hφ,
          fun π A _ _ θ he hθ P P' hP hP' => lift_datumHat q LY L'' x' η hψ ε μ hφ he hθ hP hP'⟩⟩⟩⟩
  haveI : L.IsLattice k := by
    rcases hL with rfl | ⟨fW, rfl⟩ <;> infer_instance
  exact lift_latInd P hφ he hθ L
end GlobalTheory.LastSteps
