-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.Form.div_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:44:52.693808+00:00
-- url     : https://prove2.me/submissions/c13c8e9e-edc5-4441-9021-8d82d31fc73e

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
theorem _root_.solution {N : NumD O} {k : ℕ} (β : N.Form k) {j : ℕ} (hj : j ∣ k) (m : ℕ) (x y : N.X) :
    β.be x (m • y) / j = β.be x y / j * m := by
  induction m with
  | zero => simp
  | succ m ih => rw [succ_nsmul, β.div_add hj, ih]; push_cast; ring
end Form
end GlobalTheory.Ex.NumD
