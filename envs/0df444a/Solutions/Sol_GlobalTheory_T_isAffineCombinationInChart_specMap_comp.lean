-- Prove2me | solution 1 for GlobalTheory.T.isAffineCombinationInChart_specMap_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:17.274027+00:00
-- url     : https://prove2.me/submissions/4cad3fcb-a493-4351-89aa-f00ae68c6cac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapCompStatement
import Theorems.Thm_GlobalTheory_SecGlue_isCombIn_spMap_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (Y : Scheme.{0}) (V : Y.Opens) (S S' : Type) [CommRing S] [CommRing S'] (g : S →+* S') (ι : Type) [Fintype ι]
    (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S), GlobalTheory.SecGlue.IsCombIn V u c w a →
    GlobalTheory.SecGlue.IsCombIn V (spMap g ≫ u) (spMap g ≫ c) (fun i => spMap g ≫ w i) (fun i => g (a i)) := by
  first | exact @GlobalTheory.SecGlue.isCombIn_spMap_comp | exact GlobalTheory.SecGlue.isCombIn_spMap_comp | (intros; apply GlobalTheory.SecGlue.isCombIn_spMap_comp <;> assumption)
end _root_.GlobalTheory.T
