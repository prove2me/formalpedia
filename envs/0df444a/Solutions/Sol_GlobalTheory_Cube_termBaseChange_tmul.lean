-- Prove2me | solution 1 for GlobalTheory.Cube.termBaseChange_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:02:46.052801+00:00
-- url     : https://prove2.me/submissions/8f0382ae-2e16-4cff-b552-48ce2c05028b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
open GlobalTheory
open TensorProduct
variable {ι : Type} {R : Type u} [CommRing R]
variable (S : Type u') [CommRing S] [Algebra R S]
namespace GlobalTheory
namespace Cube
theorem _root_.solution (A : Cube.{v} ι R) (p : ℕ) (c : S) (x : Cube.Term A p)
    (s : {s : Finset ι // s.card = p}) :
    Cube.termBaseChange S A p (c ⊗ₜ[R] x) s = c ⊗ₜ[R] x s := rfl
end Cube
end GlobalTheory
