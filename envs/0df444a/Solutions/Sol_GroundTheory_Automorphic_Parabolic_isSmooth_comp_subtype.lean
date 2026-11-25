-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isSmooth_comp_subtype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:15:48.779544+00:00
-- url     : https://prove2.me/submissions/96e7cd39-b9e5-4355-a321-da378e16f999

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Induction
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic

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
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal Topology Filter Set MeasureTheory Measure
open scoped NNReal
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {G : Type*} [Group G] [TopologicalSpace G] {V : Type*}
    [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V} (hπ : IsSmooth π)
    (H : Subgroup G) : IsSmooth (π.comp H.subtype) := by
  intro v
  have : (stabilizerOf (π.comp H.subtype) v : Set H) =
      Subtype.val ⁻¹' (stabilizerOf π v : Set G) := by
    ext h
    rfl
  rw [this]
  exact (hπ v).preimage continuous_subtype_val
end GroundTheory.Automorphic.Parabolic
