-- Prove2me | solution 1 for GlobalTheory.ChartCount.fdeg_and_nd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:30:34.906666+00:00
-- url     : https://prove2.me/submissions/34fa8253-bd4c-4528-8d26-e5fe53b15ff5

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__TamagawaSpecialUnitary_320f37a25cd91d38
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PhaseFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TotallyRealDegreeAndChartDimensionEq
import Theorems.Thm_GlobalTheory_ChartCount_card_strictLower
import Theorems.Thm_GlobalTheory_ChartCount_two_mul_card_Psi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal
open GlobalTheory GlobalTheory.ChartCount
namespace GlobalTheory.ChartCount
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    fdeg E = X.Ψ.card ∧ nd X = X.Ψ.card * (r * (r - 1) / 2) := by
  intro E _ _ _ r X
  refine ⟨?_, ?_⟩
  · have h := two_mul_card_Psi X
    unfold fdeg
    omega
  · unfold nd
    rw [Fintype.card_prod, Fintype.card_coe, card_strictLower]
end GlobalTheory.ChartCount
