-- Prove2me | solution 1 for GlobalTheory.NearlyPrimitive.map_dpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:02:55.410478+00:00
-- url     : https://prove2.me/submissions/dcfc50a0-521f-49a3-997e-b1177f3a9e49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormSmulLeOneOfPrimitiveBoundedPowers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NearlyPrimitive
open Finset Filter Topology
namespace GlobalTheory.NearlyPrimitive
theorem _root_.solution {C : Type} [Field C] {B B' : Type} [CommRing B] [Algebra C B] [CommRing B']
    [Algebra C B'] (f : B →ₐ[C] B') (n : ℕ) (x : B) : f (dpow C n x) = dpow C n (f x) := by
  simp [dpow]
end GlobalTheory.NearlyPrimitive
