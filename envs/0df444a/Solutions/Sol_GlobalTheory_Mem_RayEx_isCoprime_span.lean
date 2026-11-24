-- Prove2me | solution 1 for GlobalTheory.Mem.RayEx.isCoprime_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:47:45.631479+00:00
-- url     : https://prove2.me/submissions/5555c5a0-f8a5-43a7-b48d-e672e1a64e18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayDataNonempty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.RayEx
open NumberField IsDedekindDomain
variable {R : Type} [CommRing R] [IsDedekindDomain R] (m : Ideal R)
variable {m}
namespace GlobalTheory.Mem.RayEx
theorem _root_.solution {a : R} (ha : a - 1 ∈ m) : IsCoprime (Ideal.span {a}) m := by
  refine Ideal.isCoprime_iff_exists.mpr ⟨a, Ideal.mem_span_singleton_self a, -(a - 1), m.neg_mem ha, by ring⟩
end GlobalTheory.Mem.RayEx
