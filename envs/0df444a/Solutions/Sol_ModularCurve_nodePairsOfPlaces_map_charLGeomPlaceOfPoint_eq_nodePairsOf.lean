-- Prove2me | solution 1 for ModularCurve.nodePairsOfPlaces_map_charLGeomPlaceOfPoint_eq_nodePairsOf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/3faa782d-349d-5a2a-a1b0-9755f8e908fb

import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_nodePairsOfPlaces_map_charLGeomPlaceOfPoint_eq_nodePairsOf

set_option autoImplicit false

open AlgebraicCurve ModularCurve

private theorem bridgeHand_smulNodePair_eq_frobNodePair {K : Type*} [Field K] (q : ℕ)
    (g : SemilinearAut K (modularFunctionFieldC K 1))
    (hid : ∀ a : K, g • charLGeomPlaceOfPoint K a = charLGeomPlaceOfPoint K (a ^ q))
    (a : K) :
    smulNodePair g (charLGeomPlaceOfPoint K a) = frobNodePair q a :=
  Prod.ext rfl (hid a)

theorem solution
    {K : Type*} [Field K] (q : ℕ) (g : SemilinearAut K (modularFunctionFieldC K 1))
    (hid : ∀ a : K, g • charLGeomPlaceOfPoint K a = charLGeomPlaceOfPoint K (a ^ q))
    (S : Finset K) :
    nodePairsOfPlaces g
        (S.map ⟨charLGeomPlaceOfPoint K, charLGeomPlaceOfPoint_injective K⟩)
      = nodePairsOf q S := by
  unfold nodePairsOfPlaces nodePairsOf
  rw [Finset.map_map]
  congr 1
  refine DFunLike.ext _ _ (fun a => ?_)
  exact bridgeHand_smulNodePair_eq_frobNodePair q g hid a

end S_ModularCurve_nodePairsOfPlaces_map_charLGeomPlaceOfPoint_eq_nodePairsOf
end P2MW
export P2MW.S_ModularCurve_nodePairsOfPlaces_map_charLGeomPlaceOfPoint_eq_nodePairsOf (solution)
