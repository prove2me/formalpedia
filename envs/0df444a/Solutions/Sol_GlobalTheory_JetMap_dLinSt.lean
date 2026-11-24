-- Prove2me | solution 1 for GlobalTheory.JetMap.dLinSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:40:01.194347+00:00
-- url     : https://prove2.me/submissions/1975a77c-e6bb-42c6-9c13-1ecf7d6fb7ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ToJetOneEqSum
import Theorems.Thm_GlobalTheory_JetMap_toJet_one_eq_sum
import Theorems.Thm_GlobalTheory_JetSer_toJet_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetLift_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_spec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt
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
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetMap
namespace GlobalTheory.JetMap
theorem _root_.solution (hR : RepSt) : DLinSt := by
  intro R _ G _ G' _ d x x' hx hx' f φ hφ w hw hw'
  obtain ⟨y₀, hy₀, -⟩ := (hR R G d x hx (Fin 1 × Fin d)).1
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt R (n := 1) d 0) (gp_pt 0)
  have h' := hφ.2 1 _ _ hy₀
  rw [gt_comp1_pt_right] at h'
  obtain ⟨ψ₀, hψ₀, e₀⟩ := hy₀.2 1
  obtain ⟨ψ', hψ', e'⟩ := h'.2 1
  set c := tcoord hx w hw with hc
  let l : JetR R (Fin 1 × Fin d) 1 →ₐ[R] DualNumber R :=
    jetLift R (RingHom.ker (fstD R)) kerD_sq (fun p => TrivSqZeroExt.inr (c p.2)) (fun _ => inr_mem_kerD _)
  have hl : ∀ p, l (zR 1 p) = TrivSqZeroExt.inr (c p.2) := fun p => jetLift_zR _ _ _ _ p
  have e1 : l.comp ψ₀ = dualLift c := jet_ext fun j => by
    rw [AlgHom.comp_apply, hψ₀, dualLift_zR]
    exact (congrArg l (toJet_X 1 _)).trans (hl _)
  have e2 : l.comp ψ' = dualLift ((dLin φ).mulVec c) := jet_ext fun j => by
    rw [AlgHom.comp_apply, hψ', dualLift_zR, toJet_one_eq_sum _ (hφ.1 j), map_sum]
    simp only [map_smul, hl, ← TrivSqZeroExt.inr_smul, smul_eq_mul]
    rw [← TrivSqZeroExt.inr_sum, Fintype.sum_prod_type, Fin.sum_univ_one]
    rfl
  apply tcoord_eq
  have e'' : y₀ 1 ≫ f = spMap ψ' ≫ x' 1 := e'
  rw [← e2, ← spMap_comp, Category.assoc, ← e'', e₀, ← Category.assoc, ← Category.assoc, spMap_comp, e1,
    ← tcoord_spec hx w hw]
end GlobalTheory.JetMap
