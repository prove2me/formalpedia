-- Prove2me | solution 1 for GlobalTheory.mem_ideal_smul_top_iff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:21:19.456727+00:00
-- url     : https://prove2.me/submissions/e9515f04-6840-43b7-9e2c-5dbeeca1f6c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HenselRootsCompatible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {V : Type} [CommRing V] (I : Ideal V) (x : V) :
    x ∈ I • (⊤ : Submodule V V) ↔ x ∈ I := by
  rw [smul_eq_mul, Ideal.mul_top]
end GlobalTheory
