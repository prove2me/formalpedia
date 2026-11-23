-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.Form.div_add_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:16.131089+00:00
-- url     : https://prove2.me/submissions/70a9a987-480f-45ce-bb29-fd83e3d04f5b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTerms

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
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.NumD
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.Ex.NumD
namespace Form
theorem _root_.solution {N : NumD O} {k : ℕ} (β : N.Form k) {j : ℕ} (hj : j ∣ k) (x y z : N.X) :
    β.be (x + y) z / j = β.be x z / j + β.be y z / j := by
  rw [β.symm, β.div_add hj, β.symm z, β.symm z]
end Form
end GlobalTheory.Ex.NumD
