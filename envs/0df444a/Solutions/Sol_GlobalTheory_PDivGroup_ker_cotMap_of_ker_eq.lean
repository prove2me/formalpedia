-- Prove2me | solution 1 for GlobalTheory.PDivGroup.ker_cotMap_of_ker_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:04:31.863876+00:00
-- url     : https://prove2.me/submissions/f35d5008-5d6e-4229-b845-6acec1404a55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DUnitMemRangeOfMemKerIdeal
import Theorems.Thm_GlobalTheory_PDiv_ker_cotMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Coalgebra Bialgebra WithConv
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv
variable {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O)
namespace GlobalTheory.PDivGroup
theorem _root_.solution {m n : ℕ} {f : G.A n →ₐc[O] G.A m} (hf : Function.Surjective f)
    (hk : RingHom.ker f = torsionIdeal O _ (p ^ m)) :
    LinearMap.ker (cotMap f) = Ideal.span {(p : O) ^ m} • (⊤ : Submodule O (Cot O (G.A n))) := by
  rw [ker_cotMap hf hk, Nat.cast_pow]
end GlobalTheory.PDivGroup
