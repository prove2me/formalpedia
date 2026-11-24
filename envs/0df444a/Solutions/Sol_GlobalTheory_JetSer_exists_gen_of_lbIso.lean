-- Prove2me | solution 1 for GlobalTheory.JetSer.exists_gen_of_lbIso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:53.749972+00:00
-- url     : https://prove2.me/submissions/61dcbe5e-d208-4347-869d-5ae3482255ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniqueNormPrim
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
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
open GlobalTheory GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.JetSer
theorem _root_.solution {X : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (X ⟶ X)) (ε : K → ℤ)
    (H : LBIso L (LB.LinComb L φ ε)) :
    ∃ t : LB.Gen (LB.LinComb L (K := K ⊕ PUnit) (Sum.elim φ (fun _ => 𝟙 X)) (Sum.elim ε (fun _ => -1))), t.IsGen := by
  obtain ⟨v, hv⟩ := H
  have le : ∀ j : K ⊕ PUnit → L.ι, LB.wchart L (Sum.elim φ (fun _ : PUnit => 𝟙 X)) j ≤
      LB.wchart L φ (j ∘ Sum.inl) ⊓ L.U (j (Sum.inr PUnit.unit)) := fun j y hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inl k), Set.mem_iInter.1 hy (Sum.inr PUnit.unit)⟩
  refine ⟨⟨fun j => res (le j) (v.s (j ∘ Sum.inl, j (Sum.inr PUnit.unit)))⟩,
    fun (p q : K ⊕ PUnit → L.ι) => unit_ext fun y hy => ?_⟩
  have hm : (𝟙 X : X ⟶ X) y ∈ LB.wchart L φ (p ∘ Sum.inl) ⊓ L.U (p (Sum.inr PUnit.unit)) ⊓
      (LB.wchart L φ (q ∘ Sum.inl) ⊓ L.U (q (Sum.inr PUnit.unit))) := ⟨le p hy.1, le q hy.2⟩
  have e := congrArg (gm (𝟙 X) y (LB.wchart L φ (p ∘ Sum.inl) ⊓ L.U (p (Sum.inr PUnit.unit)) ⊓
      (LB.wchart L φ (q ∘ Sum.inl) ⊓ L.U (q (Sum.inr PUnit.unit)))))
    (hv (p ∘ Sum.inl, p (Sum.inr PUnit.unit)) (q ∘ Sum.inl, q (Sum.inr PUnit.unit)))
  have e' := (gm_res _ y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((gm_div L (LB.LinComb L φ ε) (𝟙 X) y (p ∘ Sum.inl, p (Sum.inr PUnit.unit))
      (q ∘ Sum.inl, q (Sum.inr PUnit.unit)) hm).trans (congrArg₂ (· * ·)
        (gm_linComb L φ ε (𝟙 X) y _ _ hm.1.1 hm.2.1) rfl)) (gm_res _ y _ hm _))))
  refine ((gm_res (𝟙 X) y _ hy _).trans (gm_res (𝟙 X) y (le p) hy.1 _)).trans (e'.trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L _ _ (𝟙 X) y p q hy.1 hy.2).trans ?_)
    ((gm_res (𝟙 X) y _ hy _).trans (gm_res (𝟙 X) y (le q) hy.2 _)))
  exact DVR.prod_sum₂ (K := K) (K' := PUnit) _ rfl ((Fintype.prod_unique _).trans (zpow_neg_one _))
end GlobalTheory.JetSer
