-- Prove2me | solution 1 for N25.Endgame.genusFF_goodPrime25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:00.268535+00:00
-- url     : https://prove2.me/submissions/30d0b67e-f7fe-499a-baf2-de398ecc6291

import Mathlib
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_N25_Endgame_xH25C_isCurveOver
import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_N25_Endgame_xH25C_finitelyGenerated
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_N25_Endgame_xH25C_constantsAreBase
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ModularCurve_deg_qInftyPlaceBar
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_N25_Endgame_FBaseCoeffMap25_generates
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Theorems.Thm_N25_Endgame_FBaseCoeffMap25_frobenius_prime
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed
import Theorems.Thm_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd
import Theorems.Thm_N25_genus_four
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_ModularCurve_two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

noncomputable section

namespace N25.Endgame

/-- Every good prime-field form of the level-25 curve has genus four. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (hgood : ¬ p ∣ 25) :
    AlgebraicCurve.genusFF (ZMod p) (FBase (ZMod p)) = 4 := by
  let K := AlgebraicClosure (ZMod p)
  let : Algebra (FBase (ZMod p)) (FBase K) :=
    (FBaseCoeffMap25 (ZMod p) K).toAlgebra
  let : AlgebraicCurve.IsCurveOver (ZMod p) (FBase (ZMod p)) :=
    xH25C_isCurveOver (ZMod p)
  let : AlgebraicCurve.IsCurveOver K (FBase K) := xH25C_isCurveOver K
  have h := AlgebraicCurve.genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed
    (ZMod p) K (FBase (ZMod p)) (FBase K)
    (xH25C_finitelyGenerated (ZMod p))
    (FBaseCoeffMap25_generates (ZMod p) K)
    (ModularCurve.qExpFrobeniusModL K Γ25 p)
    (fun x => by
      change ModularCurve.qExpFrobeniusModL K Γ25 p
          (FBaseCoeffMap25 (ZMod p) K x) =
        FBaseCoeffMap25 (ZMod p) K (x ^ Nat.card (ZMod p))
      rw [Nat.card_eq_fintype_card, ZMod.card]
      exact FBaseCoeffMap25_frobenius_prime p K x)
    (xH25C_constantsAreBase (ZMod p))
  exact h.symm.trans
    ((ModularCurve.genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd
      25 N25.H25 hgood K).trans N25.genus_four)

end N25.Endgame
