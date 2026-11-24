-- Prove2me | solution 1 for GlobalTheory.HeckeSeries.ord_det_of_mem_KO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:08.470843+00:00
-- url     : https://prove2.me/submissions/c4474768-6702-4151-aafc-20e1faa48deb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PowDvdOfHermMatEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesBorelSphericalIntegralCosets
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SatakeTrivialRangeBound_one_lt_resCard
import Theorems.Thm_GlobalTheory_LGrp_nabs_det_of_mem_KO
import Theorems.Thm_GlobalTheory_LGrp_nabs_eq_zpow
import Theorems.Thm_GlobalTheory_SplitWeil_one_lt_resCard


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling
noncomputable section
open GlobalTheory GlobalTheory.HeckeSeries
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {p : 𝒪[k]}
namespace GlobalTheory.HeckeSeries
theorem _root_.solution {y : GL (Fin n) k} (hy : y ∈ KO k (Fin n)) :
    ord k (Matrix.GeneralLinearGroup.det y) = 0 := by
  have hq : (1 : ℝ) < resCard k := by exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.one_lt_resCard k
  have h1 := GlobalTheory.LGrp.nabs_eq_zpow (Matrix.GeneralLinearGroup.det y)
  rw [GlobalTheory.LGrp.nabs_det_of_mem_KO hy] at h1
  have h2 : ((resCard k : ℝ)) ^ (-ord k (Matrix.GeneralLinearGroup.det y)) = (resCard k : ℝ) ^ (0 : ℤ) := by
    rw [← h1, zpow_zero]
  exact neg_eq_zero.1 (zpow_right_injective₀ (by positivity) hq.ne' h2)
end GlobalTheory.HeckeSeries
