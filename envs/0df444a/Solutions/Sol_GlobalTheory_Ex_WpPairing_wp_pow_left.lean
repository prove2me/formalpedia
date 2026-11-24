-- Prove2me | solution 1 for GlobalTheory.Ex.WpPairing.wp_pow_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:43:49.517155+00:00
-- url     : https://prove2.me/submissions/a78866aa-2a29-4de1-aafc-ec26345dbd73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingProperties

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
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.WpPairing
variable {O : Type} [CommRing O] (N : NumD O)
open scoped BigOperators
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O)
namespace GlobalTheory.Ex.WpPairing
namespace _root_.GlobalTheory.Ex.WpPairing
theorem _root_.solution {k : ℕ} (p q : N.QT k) (n : ℕ) : N.wp (p ^ n) q = N.wp p q ^ n :=
  map_pow (_root_.GlobalTheory.Ex.WpPairing.wpHom N q) p n
end _root_.GlobalTheory.Ex.WpPairing
end GlobalTheory.Ex.WpPairing
