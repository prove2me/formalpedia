-- Prove2me | solution 1 for N25.Endgame.pG25_isCusp
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:57:52.148096+00:00
-- url     : https://prove2.me/submissions/99b1d748-48b5-4260-9dc8-c55a6702342b

import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_N25_Endgame_cuspChoice25_spec
import Theorems.Thm_N25_Endgame_pQ25_j_order
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

namespace N25.Endgame

/-- The normalized rational-order comparison makes every selected geometric
place a pole of the coefficient-embedded j-function. -/
theorem _root_.solution (i : Fin 5) :
    ModularCurve.IsCusp (emb25 j25) (pG25 i) := by
  let g := (SemilinearAut.ofAlgAut gammaF25)^i.val
  have he : (pG25 i).ord (emb25 j25) = -1 :=
    (cuspChoice25_spec.2.2.2.2.2 i j25).trans (pQ25_j_order i)
  change emb25 j25 ∉ (g • qInftyPlaceBar Qbar FG cuspChoice25.hG).toValuationSubring
  intro hm
  rw [SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hm
  have hn : 0 ≤ (qSeriesBar Qbar FG (g⁻¹ • emb25 j25)).order := hm
  have hv := SemilinearAut.ord_smul g (qInftyPlaceBar Qbar FG cuspChoice25.hG)
    (g⁻¹ • emb25 j25)
  rw [smul_inv_smul, ord_qInftyPlaceBar] at hv
  have ho : (qSeriesBar Qbar FG (g⁻¹ • emb25 j25)).order = -1 := hv.symm.trans he
  rw [ho] at hn
  omega

end N25.Endgame
