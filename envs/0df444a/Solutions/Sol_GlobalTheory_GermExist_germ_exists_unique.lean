-- Prove2me | solution 1 for GlobalTheory.GermExist.germ_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:36:33.898199+00:00
-- url     : https://prove2.me/submissions/c29b122f-5f1c-427f-b5d5-221e2a9dee51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_TopLePreimageWchart
import Theorems.Thm_GlobalTheory_GermExist_isUnit_of_isSer1
import Theorems.Thm_GlobalTheory_GermExist_top_le_preimage_wchart
import Theorems.Thm_P2M_GlobalTheory_GermExist_unit_comp_prim__a51190ddb949

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
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GermExist
namespace GlobalTheory.GermExist
theorem _root_.solution : JetAlgSt → RepSt → SerSt → SerExSt → GermExSt := by
  intro _ hrep hser hex R _ G _ L _ w hw ρ d x hx j hj m s
  obtain ⟨h1, -⟩ := hex R G d x hx
  obtain ⟨σ, hσ, uσ⟩ := h1 (LB.wchart L (K := PUnit) (fun _ => 𝟙 G.left) (fun _ => j))
    (top_le_preimage_wchart L _ j _ (fun _ => by rw [Category.comp_id]; exact hj)) (s.f (fun _ => j))
  obtain ⟨r, hr, ur⟩ := h1 (LB.wchart L (primφ w) (fun _ => j))
    (top_le_preimage_wchart L _ j _ (fun k => by rw [unit_comp_primφ w hw k]; exact hj)) (ρ.s (fun _ => j)).val
  have hu : IsUnit (r ^ m) := (isUnit_of_isSer1 hrep hser hx (Units.isUnit _) hr).pow m
  obtain ⟨v, hv⟩ := hu
  refine ⟨σ * (v⁻¹).val, ⟨σ, r, hσ, hr, by rw [← hv, Units.inv_mul_cancel_right]⟩, ?_⟩
  rintro f ⟨σ', r', hσ', hr', hf⟩
  rw [uσ σ' hσ', ur r' hr', ← hv] at hf
  rw [← hf, Units.mul_inv_cancel_right]
end GlobalTheory.GermExist
