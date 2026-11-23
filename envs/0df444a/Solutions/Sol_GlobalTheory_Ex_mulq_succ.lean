-- Prove2me | solution 1 for GlobalTheory.Ex.mulq_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:38:06.637287+00:00
-- url     : https://prove2.me/submissions/f69bc362-15c8-43c8-a30d-a4d4fbaa0d9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CubNSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLaws

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
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}
namespace GlobalTheory.Ex
theorem _root_.solution (θ : A → A → A → U) (σ : A → U) (n : ℕ) (x : A) :
    mulq θ σ (n + 1) x = mulq θ σ n x * (cubN θ n 1 x x / dbl θ σ x ^ n) := by
  rw [mulq, Finset.prod_range_succ, mulq]
end GlobalTheory.Ex
