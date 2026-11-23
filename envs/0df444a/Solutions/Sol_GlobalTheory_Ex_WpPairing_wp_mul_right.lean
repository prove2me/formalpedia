-- Prove2me | solution 1 for GlobalTheory.Ex.WpPairing.wp_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:27.972496+00:00
-- url     : https://prove2.me/submissions/c95fc322-fe93-4737-a66a-5d9b4efaab9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingProperties
import Theorems.Thm_GlobalTheory_Ex_NumD_wp_swap


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
theorem _root_.solution {k : ℕ} (p p' p'' : N.QT k) : N.wp p (p' * p'') = N.wp p p' * N.wp p p'' := by
  rw [N.wp_swap (p' * p'') p, _root_.GlobalTheory.Ex.WpPairing.wp_mul_left, mul_inv, ← N.wp_swap p' p, ← N.wp_swap p'' p]
end _root_.GlobalTheory.Ex.WpPairing
end GlobalTheory.Ex.WpPairing
