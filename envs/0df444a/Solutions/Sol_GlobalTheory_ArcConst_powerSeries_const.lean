-- Prove2me | solution 1 for GlobalTheory.ArcConst.powerSeries_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:58:34.480048+00:00
-- url     : https://prove2.me/submissions/afc97cd2-4aae-4aee-a662-d4d093d60ea7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsIntegralElemOfIsAlgebraicInt
import Theorems.Thm_GlobalTheory_ArcConst_AlgZ_map
import Theorems.Thm_GlobalTheory_ArcConst_AlgZ_sub
import Theorems.Thm_GlobalTheory_ArcConst_isIntegralElem_of_isAlgebraic_int
import Theorems.Thm_GlobalTheory_ArcConst_isUnit_of_isIntegralElem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
noncomputable section
open GlobalTheory GlobalTheory.ArcConst
namespace GlobalTheory.ArcConst
theorem _root_.solution {K : Type} [Field K] [CharZero K] {p : PowerSeries K} (hp : AlgZ p) :
    ∃ x : K, p = PowerSeries.C (R := K) x := by
  refine ⟨PowerSeries.constantCoeff p, ?_⟩
  by_contra hne
  have h1 : AlgZ (PowerSeries.C (R := K) (PowerSeries.constantCoeff p)) :=
    (hp.map (PowerSeries.constantCoeff (R := K))).map (PowerSeries.C (R := K))
  have h2 := isUnit_of_isIntegralElem _
    (isIntegralElem_of_isAlgebraic_int (PowerSeries.C (R := K)) (hp.sub h1)) (sub_ne_zero.2 hne)
  have h3 := h2.map (PowerSeries.constantCoeff (R := K))
  simp at h3
end GlobalTheory.ArcConst
