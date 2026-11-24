-- Prove2me | solution 1 for GlobalTheory.T.mvPowerSeries_exists_polynomial_totalDegree_le_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:19:34.60681+00:00
-- url     : https://prove2.me/submissions/fd500e9f-7a4e-4354-9f24-4ecc2780934a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesExistsPolynomialTotalDegreeLeSubMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesExistsPolynomialTotalDegreeLeSubMemStatement
import Theorems.Thm_GlobalTheory_CompleteBaseChange_exists_polynomial_totalDegree_le_sub_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (J : Ideal R), J.FG → IsAdicComplete J R → ∀ (σ ι : Type) [Finite σ] [Finite ι] (f : ι → MvPowerSeries σ R) (M : ℕ), Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ^ M ≤ Ideal.span (Set.range f) ⊔ Ideal.map (MvPowerSeries.C : R →+* MvPowerSeries σ R) J → ∀ g : MvPowerSeries σ R, ∃ P : MvPolynomial σ R, P.totalDegree ≤ M ∧ g - (P : MvPowerSeries σ R) ∈ Ideal.span (Set.range f) := by
  first | exact @GlobalTheory.CompleteBaseChange.exists_polynomial_totalDegree_le_sub_mem | exact GlobalTheory.CompleteBaseChange.exists_polynomial_totalDegree_le_sub_mem | (intros; apply GlobalTheory.CompleteBaseChange.exists_polynomial_totalDegree_le_sub_mem <;> assumption)
end _root_.GlobalTheory.T
