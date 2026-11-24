-- Prove2me | solution 1 for GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:21:32.571251+00:00
-- url     : https://prove2.me/submissions/f2825c1f-66ad-4816-a5f2-26ab85f47cb4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RootsOfUnityInj
import Theorems.Thm_GlobalTheory_RootsOfUnityInjectiveInertiaEigenvalues_rootsOfUnity_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues
namespace GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues
theorem _root_.solution : ∀ {O k : Type} [inst : CommRing O] [IsDomain O] [inst_2 : Field k] (f : O →+* k) {M : ℕ},
    (↑M : k) ≠ (0 : k) → ∀ {x y : O}, x ^ M = (1 : O) → y ^ M = (1 : O) →
      (f : O → k) x = (f : O → k) y → x = y :=
  fun f _ hM _ _ hx hy hf => rootsOfUnity_inj f hM hx hy hf
end GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues
