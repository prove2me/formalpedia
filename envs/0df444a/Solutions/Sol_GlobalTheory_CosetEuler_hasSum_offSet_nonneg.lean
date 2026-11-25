-- Prove2me | solution 1 for GlobalTheory.CosetEuler.hasSum_offSet_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:19:25.079325+00:00
-- url     : https://prove2.me/submissions/215b027a-d830-4673-aa88-a8db057a38ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumCosetsEulerProduct
import Theorems.Thm_GlobalTheory_CosetEuler_hasSum_step
import Theorems.Thm_GlobalTheory_CosetEuler_summable_step
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
theorem _root_.solution (f : G → ℝ) (hf0 : ∀ g ∈ H, 0 ≤ f g)
    (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g) (A : ι → ℝ)
    (hA : ∀ v, ∀ g ∈ H, p v g = 1 → HasSum (fun a : L v ⧸ K v => f (g * e v a.out)) (A v * f g))
    (T : Finset ι) :
    HasSum ((offSet p K J H T).indicator fun y => f ((y.out : H) : G)) ((∏ v ∈ T, A v) * f 1) := by
  induction T using Finset.induction_on with
  | empty => simpa using hasSum_base hJH hJ f hf
  | @insert v T hv ih =>
    rw [Finset.prod_insert hv, mul_assoc]
    exact hasSum_step hJH hpe hpe' he hJ f hf (A v) T v hv (hA v) ih
      (summable_step hJH hpe hpe' he hJ f hf0 hf (A v) T v hv (hA v) ih)
end GlobalTheory.CosetEuler
