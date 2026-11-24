-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolPQ.continuous_hs_umat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:18:59.509454+00:00
-- url     : https://prove2.me/submissions/9d4bc981-8afe-44df-a2de-956f98b91074

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_OneAddHsInvPowLintegralLtTop
import Theorems.Thm_Formalism_REAL_continuous_coeMatrix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Finset PI.UpqRep
open scoped InnerProductSpace ENNReal ComplexOrder
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolPQ
namespace GlobalTheory.CompanionTheory.HolPQ
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) :
    Continuous fun g : UJ ε => hs (umat g) := by
  have hc : Continuous (coeMatrixAlt ε) := continuous_coeMatrix ε
  unfold hs
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact (Continuous.matrix_elem hc i j).norm.pow 2
end GlobalTheory.CompanionTheory.HolPQ
