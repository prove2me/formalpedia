-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.mem_rightStab
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:40.276104+00:00
-- url     : https://prove2.me/submissions/d4995f44-5908-4ad4-a9c9-2e8893fad2de

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Set
variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
omit [AddCommGroup W] [Module ℂ W]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {f : G → W} {g : G} : g ∈ rightStab f ↔ ∀ x, f (x * g) = f x :=
  Iff.rfl
end GroundTheory.Automorphic.Parabolic
