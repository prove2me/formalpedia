-- Prove2me | solution 1 for GlobalTheory.ChartCmp.CarryCalc.carries_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:01:17.611583+00:00
-- url     : https://prove2.me/submissions/cc30bd90-021c-4390-9e27-d2529d3cc620

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CarriesLinCombGeneratorCalculus
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_maps_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.CarryCalc
variable {X X' Y : Scheme.{0}} {L' : LB X'} {L : LB X} {F : X' ⟶ X} {K : Type} [Fintype K]
namespace GlobalTheory.ChartCmp.CarryCalc
theorem _root_.solution (w : LB.Iso L' (L.pull F)) (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε))
    (g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)) :
    Carries L F w φ ε g g' ↔ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
      r z ∈ LB.wchart L (fun k => φ k ≫ F) p → r z ∈ LB.wchart L' φ q →
        gm r z (LB.wchart L (fun k => φ k ≫ F) p) (g'.s p) = pw w φ ε r z p q * gm r z (LB.wchart L' φ q) (g.s q) := by
  refine (maps_iff w φ (fun k => φ k ≫ F) ε g g' (𝟙 Y) (flatGen L F φ ε g')
    (fun j x hx => wchart_pull_le L F φ j hx) (fun j => rfl)).trans ⟨fun H Z r z p q hp hq => ?_, fun H Z r z p q hp hq => ?_⟩
  · have := H Z r z p q (Set.mem_iInter.1 hp) (Set.mem_iInter.1 hq)
    rw [Category.comp_id] at this
    exact this
  · rw [Category.comp_id]
    exact H Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)
end GlobalTheory.ChartCmp.CarryCalc
