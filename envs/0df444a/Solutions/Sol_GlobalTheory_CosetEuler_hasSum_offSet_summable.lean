-- Prove2me | solution 1 for GlobalTheory.CosetEuler.hasSum_offSet_summable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:19:39.526924+00:00
-- url     : https://prove2.me/submissions/1a1fc121-da57-4d7c-ab67-a2ec6db13c74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumCosetsEulerProduct
import Theorems.Thm_GlobalTheory_CosetEuler_hasSum_step
import Theorems.Thm_GlobalTheory_CosetEuler_hasSum_base

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CosetEuler
variable {G ι : Type} [Group G] {L : ι → Type} [∀ v, Group (L v)]
variable [DecidableEq ι] {e : ∀ v, L v →* G} {p : ∀ v, G →* L v} {K : ∀ v, Subgroup (L v)}
    {J H : Subgroup G}
    (hJH : J ≤ H) (hpe : ∀ v a, p v (e v a) = a) (hpe' : ∀ u v, u ≠ v → ∀ a, p u (e v a) = 1)
    (he : ∀ v a, e v a ∈ H) (hJ : ∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v)
include hJH hJ
include hpe hpe' he
namespace GlobalTheory.CosetEuler
theorem _root_.solution {E : Type} [NormedField E] [CompleteSpace E] (f : G → E)
    (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g) (Z : ι → E)
    (hZ : ∀ v, ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => f (g * e v a.out)) (Z v * f g))
    (hsum : Summable fun y : H ⧸ J.subgroupOf H => f ((y.out : H) : G)) (T : Finset ι) :
    HasSum ((offSet p K J H T).indicator fun y => f ((y.out : H) : G)) ((∏ v ∈ T, Z v) * f 1) := by
  induction T using Finset.induction_on with
  | empty => simpa using hasSum_base hJH hJ f hf
  | @insert v T hv ih =>
    rw [Finset.prod_insert hv, mul_assoc]
    exact hasSum_step hJH hpe hpe' he hJ f hf (Z v) T v hv (hZ v) ih (hsum.indicator _)
end GlobalTheory.CosetEuler
