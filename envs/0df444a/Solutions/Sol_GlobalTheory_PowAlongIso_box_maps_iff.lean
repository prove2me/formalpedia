-- Prove2me | solution 1 for GlobalTheory.PowAlongIso.box_maps_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:35:04.306088+00:00
-- url     : https://prove2.me/submissions/dc39a612-71f4-4e2a-ada9-2d28a22c6d31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_UniformizationPowerGroup
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gm_linCombIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mem_finf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
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
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PowAlongIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.DVR (bw gm_linCombIso mem_finf)
variable {X X' X'' Y Y' Y₀ Z : Scheme.{0}}
variable {M : LB X} {M' : LB X'} {M'' : LB X''} {j : ℕ} {pr : Fin j → (X' ⟶ X)}
namespace GlobalTheory.PowAlongIso
theorem _root_.solution (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K]
    {φ' : K → (Y ⟶ X')} {φ : Fin j → K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) (t' : LB.Gen (LB.LinComb M' φ' ε))
    (t : ∀ i, LB.Gen (LB.LinComb M (φ i) ε)) :
    LB.Gen.Maps (LB.linCombIso w φ' ε) t'
      (GeneratorPullback.boxGen M pr φ' ε (fun i => GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i))) ↔
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (jN : K → Fin j → M.ι) (jM : K → M'.ι),
      r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM →
      ∏ i, gm (r ≫ ρ i) z (LB.wchart M (φ i) (fun a => jN a i)) ((t i).s (fun a => jN a i)) =
        (∏ a, bw w (r ≫ φ' a) z (jN a) (jM a) ^ ε a) * gm r z (LB.wchart M' φ' jM) (t'.s jM) := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (jN : K → Fin j → M.ι) (jM : K → M'.ι)
      (hm : r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM),
      gm r z (LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM) (res inf_le_left
        ((GeneratorPullback.boxGen M pr φ' ε (fun i => GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i))).s jN)) =
        ∏ i, gm (r ≫ ρ i) z (LB.wchart M (φ i) (fun a => jN a i)) ((t i).s (fun a => jN a i)) := by
    intro Z r z jN jM hm
    refine (gm_res r z inf_le_left hm _).trans ((map_prod (gm r z (LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN))
      (fun i => res (GeneratorPullback.box_le M pr φ' jN i)
        ((GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i)).s (fun a _ => jN a i))) Finset.univ).trans
      (Finset.prod_congr rfl fun i _ => ?_))
    have m := GeneratorPullback.box_le M pr φ' jN i hm.1
    have l := GeneratorPullback.pullAlong_le M (pr i) (ρ i) (φ i) φ' (hψ i) (fun a _ => jN a i)
    exact (gm_res r z (GeneratorPullback.box_le M pr φ' jN i) hm.1 _).trans ((gm_res r z l m _).trans (gm_pull r (ρ i) z _ (l m) _))
  constructor
  · intro H Z r z jN jM hm
    have E := congrArg (gm r z (LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM)) (H (jN, jM))
    exact (key Z r z jN jM hm).symm.trans (E.trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) (gm_linCombIso w φ' ε r z _ _ hm) (gm_res r z inf_le_right hm _))))
  · rintro H ⟨jN, jM⟩
    refine unit_ext fun y hy => ?_
    exact (key _ (𝟙 Y) y jN jM hy).trans ((H _ (𝟙 Y) y jN jM hy).trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) (gm_linCombIso w φ' ε (𝟙 Y) y _ _ hy) (gm_res (𝟙 Y) y inf_le_right hy _))).symm)
end GlobalTheory.PowAlongIso
