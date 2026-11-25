-- Prove2me | solution 1 for GlobalTheory.ChartCmp.CarryCalc.carries_of_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:06:27.804381+00:00
-- url     : https://prove2.me/submissions/63dc1b02-4f26-42f5-8f60-3e5a874b3cd3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CarriesLinCombGeneratorCalculus
import Theorems.Thm_GlobalTheory_ChartCmp_CarryCalc_carries_iff
import Theorems.Thm_GlobalTheory_ChartCmp_CarryCalc_val_of_carries
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_up
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


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
theorem _root_.solution {w : LB.Iso L' (L.pull F)} (hL' : L'.IsLB) (hL : L.IsLB) (hw : w.IsGen) {φ : K → (Y ⟶ X')}
    {ε : K → ℤ} {g : LB.Gen (LB.LinComb L' φ ε)} {g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)} (hg : g.IsGen)
    (hg' : g'.IsGen) (h : ∀ (y : Y) J J', Good L y J → Good L' y J' →
      val g' (𝟙 Y) y J = (∏ k, fac w y J J' (𝟙 Y ≫ φ k) ^ ε k) * val g (𝟙 Y) y J') : Carries L F w φ ε g g' := by
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff w).1 hw) hL hL' g hg
  have hc := (carries_iff w φ ε g t).2 hv
  have e : ∀ j, g'.s j = t.s j := fun j => unit_ext fun y hy => by
    choose J hJ using fun ψ : Y ⟶ X => exists_chart hL (ψ y)
    choose J' hJ' using fun ψ : Y ⟶ X' => exists_chart hL' (ψ y)
    have v' : val g' (𝟙 Y) y J = val t (𝟙 Y) y J := (h y J J' hJ hJ').trans (val_of_carries hc (𝟙 Y) hJ hJ').symm
    exact (gen_trans hg' (𝟙 Y) y hy (Good.mem hJ _ (𝟙 Y))).trans ((congrArg _ v').trans
      (gen_trans ht (𝟙 Y) y hy (Good.mem hJ _ (𝟙 Y))).symm)
  obtain ⟨s⟩ := g'
  obtain ⟨s'⟩ := t
  obtain rfl : s = s' := funext e
  exact hc
end GlobalTheory.ChartCmp.CarryCalc
