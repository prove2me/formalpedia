-- Prove2me | solution 1 for GlobalTheory.NormRos.exists_gen_of_lbIso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:22.842548+00:00
-- url     : https://prove2.me/submissions/5288b759-bdb2-4fbe-a303-f035201db020

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGenRosati
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_div
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


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
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (LBIso)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.NormRos
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.NormRos
theorem _root_.solution {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (H : LBIso (LB.LinComb L φ ε) (LB.LinComb L φ' ε')) :
    ∃ t : LB.Gen (LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' (fun k => - ε k))), t.IsGen := by
  obtain ⟨w, hw⟩ := H
  have le : ∀ j : K' ⊕ K → L.ι, LB.wchart L (Sum.elim φ' φ) j ≤
      LB.wchart L φ' (j ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inr) := fun j y hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k),
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k)⟩
  refine ⟨⟨fun j => res (le j) (w.s (j ∘ Sum.inl, j ∘ Sum.inr))⟩,
    fun (p q : K' ⊕ K → L.ι) => unit_ext fun y hy => ?_⟩
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ' (p ∘ Sum.inl) ⊓ LB.wchart L φ (p ∘ Sum.inr) ⊓
      (LB.wchart L φ' (q ∘ Sum.inl) ⊓ LB.wchart L φ (q ∘ Sum.inr)) := ⟨le p hy.1, le q hy.2⟩
  have e := congrArg (gm (𝟙 Y) y (LB.wchart L φ' (p ∘ Sum.inl) ⊓ LB.wchart L φ (p ∘ Sum.inr) ⊓
      (LB.wchart L φ' (q ∘ Sum.inl) ⊓ LB.wchart L φ (q ∘ Sum.inr))))
    (hw (p ∘ Sum.inl, p ∘ Sum.inr) (q ∘ Sum.inl, q ∘ Sum.inr))
  have e' := (gm_res (𝟙 Y) y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div (LB.LinComb L φ ε) (LB.LinComb L φ' ε') (𝟙 Y) y (p ∘ Sum.inl, p ∘ Sum.inr) (q ∘ Sum.inl, q ∘ Sum.inr) hm)
    (gm_res (𝟙 Y) y _ hm _))))
  refine ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le p) hy.1 _)).trans (e'.trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L _ _ (𝟙 Y) y p q hy.1 hy.2).trans ?_)
    ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le q) hy.2 _)))
  refine (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (gm_linComb L φ' ε' (𝟙 Y) y _ _ hm.1.1 hm.2.1).symm ?_)
  refine Eq.trans ?_ (congrArg (·⁻¹) (gm_linComb L φ ε (𝟙 Y) y _ _ hm.1.2 hm.2.2).symm)
  simp only [Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, Function.comp_apply]
end GlobalTheory.NormRos
