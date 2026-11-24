-- Prove2me | solution 1 for GroundTheory.Automorphic.injective_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:37.707565+00:00
-- url     : https://prove2.me/submissions/5ab1e9c9-ec60-4d0d-ac7d-78f415fcdb8e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Polynomial Cardinal
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}
namespace GroundTheory.Automorphic
theorem _root_.solution [ρ.IsIrreducible] {f : Representation.IntertwiningMap ρ ρ}
    (hf : f ≠ 0) : Function.Injective f :=
  ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf).1
end GroundTheory.Automorphic
