-- Prove2me | solution 1 for GlobalTheory.T.exists_glue_functions_affineOpen_from_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:08:10.900005+00:00
-- url     : https://prove2.me/submissions/a250bdaf-08e8-48f4-b6e9-2f72aec2cbe3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlueFunctionsAffineOpenFromPairs
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlueFunctionsAffineOpenFromPairsStatement
import Theorems.Thm_GlobalTheory_CechDR_pair_glue


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR Opposite KaehlerDifferential
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (W : X'.affineOpens) (k : ∀ p : Pair φ, p.1.1 ≤ W → (OAff s').obj (op p.1.1)), (∀ (p q : Pair φ) (hp : p.1.1 ≤ W) (hq : q.1.1 ≤ W) (hqp : q ≤ p), mp (OAff s') (homOfLE (Pair.le_fst hqp)).op (k p hp) = k q hq) → ∃ G : (OAff s').obj (op W), ∀ (p : Pair φ) (hp : p.1.1 ≤ W), mp (OAff s') (homOfLE hp).op G = k p hp := by
  first | exact @GlobalTheory.CechDR.pair_glue | exact GlobalTheory.CechDR.pair_glue | (intros; apply GlobalTheory.CechDR.pair_glue <;> assumption)
end _root_.GlobalTheory.T
