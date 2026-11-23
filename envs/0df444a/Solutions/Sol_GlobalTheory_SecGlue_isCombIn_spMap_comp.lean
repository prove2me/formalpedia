-- Prove2me | solution 1 for GlobalTheory.SecGlue.isCombIn_spMap_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:15.800836+00:00
-- url     : https://prove2.me/submissions/f4c68a7c-15e1-4285-a681-2607e87e9615

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Theorems.Thm_GlobalTheory_SecGlue_preimage_spMap_comp_eq_top
import Theorems.Thm_GlobalTheory_SecGlue_chartHom_spMap_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SecGlue
namespace GlobalTheory.SecGlue
theorem _root_.solution (Y : Scheme.{0}) (V : Y.Opens) (S S' : Type) [CommRing S] [CommRing S']
    (g : S →+* S') (ι : Type) [Fintype ι]
    (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S) (hC : IsCombIn V u c w a) :
    IsCombIn V (spMap g ≫ u) (spMap g ≫ c) (fun i => spMap g ≫ w i) (fun i => g (a i)) := by
  obtain ⟨hu, hc, hw, hx⟩ := hC
  refine ⟨preimage_spMap_comp_eq_top g hu, preimage_spMap_comp_eq_top g hc,
    fun i => preimage_spMap_comp_eq_top g (hw i), fun x => ?_⟩
  rw [chartHom_spMap_comp V g c hc, chartHom_spMap_comp V g u hu, hx x, map_add, map_sum]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [chartHom_spMap_comp V g (w i) (hw i), map_mul, map_sub]
end GlobalTheory.SecGlue
