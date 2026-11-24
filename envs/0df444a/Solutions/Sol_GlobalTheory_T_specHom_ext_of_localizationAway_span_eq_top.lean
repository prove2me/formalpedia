-- Prove2me | solution 1 for GlobalTheory.T.specHom_ext_of_localizationAway_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:22:24.493944+00:00
-- url     : https://prove2.me/submissions/1e2d3e63-7f7d-4f9c-9469-1b2c9d8829df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecHomExtOfLocalizationAwaySpanEqTop
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecHomExtOfLocalizationAwaySpanEqTopStatement
import Theorems.Thm_GlobalTheory_SecGlue_hom_ext_of_span_eq_top


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
theorem _root_.solution : ∀ (S : Type) [CommRing S] (ι : Type) (s : ι → S), Ideal.span (Set.range s) = ⊤ →
    ∀ (Y : Scheme.{0}) (a b : Sp S ⟶ Y),
    (∀ i, spMap (algebraMap S (Localization.Away (s i))) ≫ a = spMap (algebraMap S (Localization.Away (s i))) ≫ b) →
    a = b := by
  first | exact @GlobalTheory.SecGlue.hom_ext_of_span_eq_top | exact GlobalTheory.SecGlue.hom_ext_of_span_eq_top | (intros; apply GlobalTheory.SecGlue.hom_ext_of_span_eq_top <;> assumption)
end _root_.GlobalTheory.T
