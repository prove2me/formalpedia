-- Prove2me | solution 1 for GlobalTheory.GroupAlg.faithfullyFlat_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:49.715665+00:00
-- url     : https://prove2.me/submissions/d6738415-549b-4f7d-a75f-7b8e513e8cf6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinitePresentationOfInjective
import Theorems.Thm_GlobalTheory_GroupAlg_free_of_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.GroupAlg
variable (R : Type*) [CommRing R] {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (u : Y →+ X)
namespace GlobalTheory.GroupAlg
theorem _root_.solution (hu : Function.Injective u) :
    (mapDomainRingHom R u).FaithfullyFlat := by
  letI := mapAlgebra R u
  have := free_of_injective R u hu
  change Module.FaithfullyFlat R[Y] R[X]
  rcases subsingleton_or_nontrivial R with h | h
  · have : Subsingleton R[Y] := Module.subsingleton R _
    exact ⟨fun m hm => (hm.ne_top (Subsingleton.elim _ _)).elim⟩
  · infer_instance
end GlobalTheory.GroupAlg
