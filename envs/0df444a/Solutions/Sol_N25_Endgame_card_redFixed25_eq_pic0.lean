-- Prove2me | solution 1 for N25.Endgame.card_redFixed25_eq_pic0
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:28:52.805496+00:00
-- url     : https://prove2.me/submissions/13a7d884-030c-4a4d-ae89-4bcc4e10b97c

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
import Theorems.Thm_N25_Endgame_qExpFrobeniusPushforward25_mk
import Theorems.Thm_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental
import Theorems.Thm_ValuationSubring_exists_pow_pow_eq_self_residueField_of_liesOverPrime
import Theorems.Thm_AlgebraicCurve_Pic0_natCard_fixedPoints_eq_natCard_pic0_of_pushforwardAlong_frobenius
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

noncomputable section

namespace N25.Endgame

/-- The Frobenius-fixed special Picard group has the cardinality of its prime-field form. -/
theorem _root_.solution
    (ℓ : ℕ) [Fact ℓ.Prime] (_hgood : ¬ ℓ ∣ 25)
    (D : RedDatum25 ℓ) :
    Nat.card ↥(RedFixed25 D) =
      Nat.card (AlgebraicCurve.Pic0 (ZMod ℓ) (FBase (ZMod ℓ))) := by
  let : IsAlgClosed (κ D.A) := inferInstance
  let : Algebra (ZMod ℓ) (κ D.A) := ZMod.algebra _ _
  let : Algebra (FBase (ZMod ℓ)) (FSpecial D.A) :=
    (FBaseCoeffMap25 (ZMod ℓ) (κ D.A)).toAlgebra
  let : AlgebraicCurve.IsCurveOver (ZMod ℓ) (FBase (ZMod ℓ)) :=
    xH25C_isCurveOver (ZMod ℓ)
  let : AlgebraicCurve.IsCurveOver (κ D.A) (FSpecial D.A) :=
    xH25C_isCurveOver (κ D.A)
  have h := AlgebraicCurve.Pic0.natCard_fixedPoints_eq_natCard_pic0_of_pushforwardAlong_frobenius
    (ZMod ℓ) (κ D.A) (FBase (ZMod ℓ)) (FSpecial D.A)
    (xH25C_finitelyGenerated (ZMod ℓ))
    (xH25C_constantsAreBase (ZMod ℓ))
    (FBaseCoeffMap25_generates (ZMod ℓ) (κ D.A))
    (fun a => by
      simpa only [Nat.card_eq_fintype_card, ZMod.card] using
        ValuationSubring.exists_pow_pow_eq_self_residueField_of_liesOverPrime
          D.A Fact.out D.hA a)
    (ModularCurve.qExpFrobeniusModL (κ D.A) Γ25 ℓ)
    (ModularCurve.qExpFrobeniusModL_isIntegral (κ D.A) Γ25 ℓ)
    (fun x => by
      change ModularCurve.qExpFrobeniusModL (κ D.A) Γ25 ℓ
          (FBaseCoeffMap25 (ZMod ℓ) (κ D.A) x) =
        FBaseCoeffMap25 (ZMod ℓ) (κ D.A) (x ^ Nat.card (ZMod ℓ))
      rw [Nat.card_eq_fintype_card, ZMod.card]
      exact FBaseCoeffMap25_frobenius_prime ℓ (κ D.A) x)
    (frobPic25 D)
    (fun E => qExpFrobeniusPushforward25_mk ℓ (κ D.A) E)
  exact (Nat.card_congr (redFixedEquivFixedPoints25 D)).trans h.2

end N25.Endgame
