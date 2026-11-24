-- Prove2me | solution 1 for GlobalTheory.isSemisimpleRepresentation_of_invariant_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:18:47.866416+00:00
-- url     : https://prove2.me/submissions/1adef47e-43e8-48a8-8aa0-874e3fddf77c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
import Theorems.Thm_GlobalTheory_isSemisimpleRepresentation_of_norm_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace ComplexConjugate
open GlobalTheory
variable {𝕜 : Type*} [RCLike 𝕜]
namespace GlobalTheory
theorem _root_.solution {G V : Type*} [Group G] [AddCommGroup V]
    [Module 𝕜 V] [FiniteDimensional 𝕜 V] (ρ : Representation 𝕜 G V)
    (c : InnerProductSpace.Core 𝕜 V) (hc : ∀ k u v, c.inner (ρ k u) (ρ k v) = c.inner u v) :
    ρ.IsSemisimpleRepresentation := by
  let _ : NormedAddCommGroup V := c.toNormedAddCommGroup
  let _ : InnerProductSpace 𝕜 V := InnerProductSpace.ofCore c.toCore
  refine isSemisimpleRepresentation_of_norm_map ρ fun k v => ?_
  rw [@norm_eq_sqrt_re_inner 𝕜, @norm_eq_sqrt_re_inner 𝕜]
  exact congrArg (fun z : 𝕜 => √(RCLike.re z)) (hc k v v)
end GlobalTheory
