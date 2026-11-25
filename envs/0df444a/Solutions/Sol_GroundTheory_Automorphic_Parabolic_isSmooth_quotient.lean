-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isSmooth_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:48:13.032096+00:00
-- url     : https://prove2.me/submissions/6a255e08-9c62-49c3-ae4e-b051e0daa528

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible

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
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set MeasureTheory Measure
variable {G : Type*} [Group G] {U : Type*} [AddCommGroup U] [Module ℂ U]
  {τ : Representation ℂ G U}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution [TopologicalSpace G] [IsTopologicalGroup G] (hτ : IsSmooth τ) (Y : Submodule ℂ U)
    (hY : ∀ g, Y ≤ Y.comap (τ g)) : IsSmooth (Representation.quotient τ Y hY) := by
  intro x
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective Y x
  refine Subgroup.isOpen_mono (fun g hg => ?_) (hτ u)
  show Representation.quotient τ Y hY g (Submodule.Quotient.mk u) = Submodule.Quotient.mk u
  rw [Representation.quotient_apply, Submodule.mapQ_apply, mem_stabilizerOf.1 hg]
end GroundTheory.Automorphic.Parabolic
