-- Prove2me | solution 1 for GlobalTheory.SecGlue.Pair.equiv_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:36:56.218582+00:00
-- url     : https://prove2.me/submissions/618e1c3c-90cf-496c-ae49-53bea5f27616

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSqZeroExtendLocalizationAwayPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquareZeroLiftBasicOpenPairAgree

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
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.Pair
namespace GlobalTheory.SecGlue.Pair
theorem _root_.solution {R : Type} [CommRing R] (a b : R)
    (eP : Localization.Away (a * b) ≃ₐ[R] Localization.Away (algebraMap R (Localization.Away a) b))
    (ρ : Localization.Away a →+* Localization.Away (a * b))
    (hρ : ρ.comp (algebraMap R (Localization.Away a)) = algebraMap R (Localization.Away (a * b)))
    (y : Localization.Away a) :
    eP (ρ y) = algebraMap (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b)) y := by
  have e : (eP.toAlgHom : Localization.Away (a * b) →+* _).comp ρ =
      algebraMap (Localization.Away a) (Localization.Away (algebraMap R (Localization.Away a) b)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    rw [RingHom.comp_assoc, hρ, eP.toAlgHom.comp_algebraMap]
    exact IsScalarTower.algebraMap_eq _ _ _
  exact RingHom.congr_fun e y
end GlobalTheory.SecGlue.Pair
