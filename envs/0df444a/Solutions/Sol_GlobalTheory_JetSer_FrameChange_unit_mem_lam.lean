-- Prove2me | solution 1 for GlobalTheory.JetSer.FrameChange.unit_mem_lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:23:30.723068+00:00
-- url     : https://prove2.me/submissions/fcb5feb2-4b2b-417d-909e-6aaae6f4adb6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EvalStandardPointsThree
import Theorems.Thm_P2M_GlobalTheory_JetSer_FrameChange_lift_lam__1e26ca842b72

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε)
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer GlobalTheory.JetSer.FrameChange
variable {S : Scheme.{0}} (G : Over S) [GrpObj G]
variable {G}
namespace GlobalTheory.JetSer.FrameChange
theorem _root_.solution (L : LB G.left) (j : L.ι) (hj : ⊤ ≤ η[G].left ⁻¹ᵁ L.U j) :
    ⊤ ≤ (lift η[G] η[G]).left ⁻¹ᵁ (LB.LinComb L (lamφ G) lamε).U (fun _ => j) := by
  have e : η[G] = (1 : 𝟙_ (Over S) ⟶ G) := by simp [Hom.one_def]
  intro z hz
  refine Set.mem_iInter.2 fun k => ?_
  have h1 : (lift η[G] η[G]).left ≫ lamφ G k = η[G].left := by
    rw [lift_lamφ, e]
    fin_cases k <;> simp
  have h2 : z ∈ ((lift η[G] η[G]).left ≫ lamφ G k) ⁻¹ᵁ L.U j := by rw [h1]; exact hj hz
  exact h2
end GlobalTheory.JetSer.FrameChange
