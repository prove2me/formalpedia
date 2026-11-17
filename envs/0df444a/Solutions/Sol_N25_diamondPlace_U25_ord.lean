-- Prove2me | solution 1 for N25.diamondPlace_U25_ord
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:53:01.045167+00:00
-- url     : https://prove2.me/submissions/03f6a5e4-9116-4fed-a932-1e4b3fae1cac

import Mathlib
import Definitions.Def_N25_Units
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_N25_diamondField_U25
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Definitions.Def_N25_UnitSeries
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply

set_option autoImplicit false

open ModularCurve AlgebraicCurve

namespace N25

private theorem ord_neg (P : N25.Endgame.GPlace) (f : N25.Endgame.FG) :
    P.ord (-f) = P.ord f := by
  unfold AlgebraicCurve.Place.ord
  rw [Valuation.map_neg]

/-- Forward action on a geometric place advances the unit value index by
one; the exact function-covariance sign contributes no normalized order. -/
theorem _root_.solution (i : Fin 5) (P : N25.Endgame.GPlace) :
    let γ := ModularCurve.diamondAutHBar 25 N25.H25 (ZMod.unitOfCoprime 13 (by decide))
    (AlgebraicCurve.SemilinearAut.ofAlgAut γ • P).ord (N25.Endgame.emb25 (U25 i)) =
      P.ord (N25.Endgame.emb25 (U25 (i+1))) := by
  let γ := diamondAutHBar 25 N25.H25 (ZMod.unitOfCoprime 13 (by decide))
  have h := SemilinearAut.ord_smul (SemilinearAut.ofAlgAut γ) P
    (N25.Endgame.emb25 (U25 (i+1)))
  rw [SemilinearAut.ofAlgAut_smul, diamondField_U25] at h
  have hidx : (i+1)-1 = i := by fin_cases i <;> decide
  have heps (j : Fin 5) : (![-1,-1,1,-1,-1] : Fin 5 → N25.Endgame.FG) j =
      if j=2 then 1 else -1 := by
    fin_cases j <;> norm_num <;> decide
  rw [hidx, heps] at h
  by_cases hi : (i+1 : Fin 5)=2
  · simpa only [if_pos hi, one_mul] using h
  · simpa only [if_neg hi, neg_one_mul, ord_neg] using h

end N25
