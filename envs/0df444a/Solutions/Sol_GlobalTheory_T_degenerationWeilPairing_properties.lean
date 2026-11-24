-- Prove2me | solution 1 for GlobalTheory.T.degenerationWeilPairing_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:13:40.511831+00:00
-- url     : https://prove2.me/submissions/af26c3ff-c37b-419c-a0b9-01fc98d5d311

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingProperties
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Theorems.Thm_GlobalTheory_Ex_WpPairing_wp_pairing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (k : ℕ) (p p' p'' : N.QT k), N.wp (p * p') p'' = N.wp p p'' * N.wp p' p'' ∧ N.wp p p = 1 ∧ N.wp p p' * N.wp p' p = 1 ∧ N.wp p p' ^ k = 1 ∧ (N.QEq p p' → N.wp p p'' = N.wp p' p'') ∧ (p.1.1 = 1 → p.1.2.b = 1 → N.wp p p' = p.1.2.s p'.1.1.toAdd) ∧ (p.1.1 = 1 → p'.1.1 = 1 → N.wp p p' = N.weil k p.1.2.b p'.1.2.b) := by
  first | exact @GlobalTheory.Ex.WpPairing.wp_pairing | exact GlobalTheory.Ex.WpPairing.wp_pairing | (intros; apply GlobalTheory.Ex.WpPairing.wp_pairing <;> assumption)
end _root_.GlobalTheory.T
