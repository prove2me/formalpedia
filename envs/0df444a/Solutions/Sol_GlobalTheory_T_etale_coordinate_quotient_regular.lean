-- Prove2me | solution 1 for GlobalTheory.T.etale_coordinate_quotient_regular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:19:13.918876+00:00
-- url     : https://prove2.me/submissions/b613c531-176c-4954-b633-a565f47be8d3

import Mathlib
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtaleCoordinateQuotientRegular
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_EtaleCoordinateQuotientRegular
import Theorems.Thm_GlobalTheory_isRegularRing_quotient_etaleCoordinate


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale → ∀ j : Fin n, IsRegularRing (A ⧸ Ideal.span {t j}) := by
  first | exact @_root_.GlobalTheory.isRegularRing_quotient_etaleCoordinate | exact _root_.GlobalTheory.isRegularRing_quotient_etaleCoordinate | (intros; apply _root_.GlobalTheory.isRegularRing_quotient_etaleCoordinate <;> assumption)
end _root_.GlobalTheory.T
