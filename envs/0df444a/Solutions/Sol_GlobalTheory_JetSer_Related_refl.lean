-- Prove2me | solution 1 for GlobalTheory.JetSer.Related.refl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:50:21.024814+00:00
-- url     : https://prove2.me/submissions/407c07c6-d467-45db-9d2c-eef8838b1d90

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_comp1_pt_right


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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer
variable {R : Type} [CommRing R]
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair)
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
namespace GlobalTheory.JetSer
namespace Related
theorem _root_.solution {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O) :
    Related B B (pt R (n := 1) d 0) (pt R (n := 1) d 0) 1 := by
  have c : ∀ {n : ℕ} (j : Fin n), comp1 (pt R (n := 1) d 0) (pt R (n := n) d j) = pt R d j :=
    fun j => gt_comp1_pt _ (gp_pt j)
  have e : ∀ {n : ℕ} (f : PS R n d), ev (fun j => pt R (n := n) d j) f = f := fun f => by
    unfold ev
    exact congrFun MvPowerSeries.subst_self f
  have e2 : ∀ f : PS R 2 d, ev (n := 2) ![pt R d 0, pt R d 1] f = f := fun f => by
    have : (![pt R d 0, pt R d 1] : Fin 2 → Pt R 2 d) = fun j => pt R d j := by
      funext j; fin_cases j <;> rfl
    rw [this, e]
  have e3 : ∀ f : PS R 3 d, ev (n := 3) ![pt R d 0, pt R d 1, pt R d 2] f = f := fun f => by
    have : (![pt R d 0, pt R d 1, pt R d 2] : Fin 3 → Pt R 3 d) = fun j => pt R d j := by
      funext j; fin_cases j <;> rfl
    rw [this, e]
  refine ⟨⟨gp_pt 0, gp_pt 0, c 0, c 0⟩, ev_one _, ev_one _, fun i => ?_, fun a => ?_, ?_, ?_, ?_, fun a => ?_⟩
  · have hF : addOf B.G.F (pt R (n := 2) d 0) (pt R (n := 2) d 1) = B.G.F := funext fun l => e2 _
    unfold transF
    rw [c, c, hF]
    exact (congrFun (gt_comp1_pt (n := 2) B.G.F B.G.const) i).symm
  · rw [gt_comp1_pt_right, gt_comp1_pt _ (B.A.const a)]
  · simp only [ev_one, c, e3, _root_.mul_one]
  · simp only [ev_one, c, e3, _root_.mul_one]
  · simp only [ev_one, c, e2, _root_.mul_one]
  · simp only [ev_one, c, e2, _root_.mul_one]
end Related
end GlobalTheory.JetSer
