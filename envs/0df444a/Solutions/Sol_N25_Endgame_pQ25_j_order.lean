-- Prove2me | solution 1 for N25.Endgame.pQ25_j_order
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:57:51.501196+00:00
-- url     : https://prove2.me/submissions/5ded24dd-edd3-4ab1-b10d-2ee59235707d

import Mathlib
import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_N25_Endgame_cuspChoice25_spec
import Theorems.Thm_N25_diamondField_fixes_jq
import Definitions.Def_N25
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

namespace N25.Endgame

private theorem tauQ_fixes_j25 : cuspChoice25.tauQ j25 = j25 := by
  apply emb25.injective
  have hd := N25.diamondField_fixes_jq (ZMod.unitOfCoprime 13 (by decide)) j25 rfl
  exact (cuspChoice25_spec.1 j25).symm.trans hd

private theorem tauQ_power_fixes_j25 (n : ℕ) :
    (SemilinearAut.ofAlgAut cuspChoice25.tauQ)^n • j25 = j25 := by
  have h : SemilinearAut.ofAlgAut cuspChoice25.tauQ • j25 = j25 := tauQ_fixes_j25
  induction n with
  | zero => exact one_smul _ _
  | succ n ih => rw [pow_succ, mul_smul, h, ih]

/-- The selected rational cusps are simple poles of the actual j-series. -/
theorem _root_.solution (i : Fin 5) : (pQ25 i).ord j25 = -1 := by
  have h := SemilinearAut.ord_smul ((SemilinearAut.ofAlgAut cuspChoice25.tauQ)^i.val)
    (qInftyPlaceRat FQ cuspChoice25.hQ) j25
  rw [tauQ_power_fixes_j25] at h
  have hb : (qInftyPlaceRat FQ cuspChoice25.hQ).ord j25 =
      (qSeriesBar ℚ FQ j25).order := ord_qInftyPlaceBar ℚ cuspChoice25.hQ j25
  apply h.trans
  rw [hb]
  change (jqModC ℚ).order = -1
  rw [jqModC_rat]
  exact order_jq

end N25.Endgame
