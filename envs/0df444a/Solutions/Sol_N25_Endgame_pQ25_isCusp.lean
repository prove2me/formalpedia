-- Prove2me | solution 1 for N25.Endgame.pQ25_isCusp
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:57:52.858173+00:00
-- url     : https://prove2.me/submissions/f9ef6059-afbe-47c6-ac5d-9fdcfd462369

import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_N25_Endgame_pQ25_j_order
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

namespace N25.Endgame

/-- Every selected rational orbit place is a cusp of the actual j-function. -/
theorem _root_.solution (i : Fin 5) : ModularCurve.IsCusp j25 (pQ25 i) := by
  let g := (SemilinearAut.ofAlgAut cuspChoice25.tauQ)^i.val
  change j25 ∉ (g • qInftyPlaceRat FQ cuspChoice25.hQ).toValuationSubring
  intro hm
  rw [SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hm
  have hn : 0 ≤ (qSeriesBar ℚ FQ (g⁻¹ • j25)).order := hm
  have hv := SemilinearAut.ord_smul g (qInftyPlaceRat FQ cuspChoice25.hQ) (g⁻¹ • j25)
  rw [smul_inv_smul] at hv
  have hb : (qInftyPlaceRat FQ cuspChoice25.hQ).ord (g⁻¹ • j25) =
      (qSeriesBar ℚ FQ (g⁻¹ • j25)).order := ord_qInftyPlaceBar ℚ cuspChoice25.hQ _
  have he : (qSeriesBar ℚ FQ (g⁻¹ • j25)).order = -1 :=
    hb.symm.trans (hv.symm.trans (pQ25_j_order i))
  rw [he] at hn
  omega

end N25.Endgame
