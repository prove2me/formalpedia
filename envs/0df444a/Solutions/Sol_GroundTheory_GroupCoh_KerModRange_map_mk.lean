-- Prove2me | solution 1 for GroundTheory.GroupCoh.KerModRange.map_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:46.961903+00:00
-- url     : https://prove2.me/submissions/e0f62640-60fb-441f-a47a-18f0bdd67c51

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.GroupCoh
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
namespace GroundTheory.GroupCoh
namespace KerModRange
theorem _root_.solution {fA gA : A →+ A} {fB gB : B →+ B} (i : A →+ B)
    (hf : ∀ a, i (fA a) = fB (i a)) (hg : ∀ a, i (gA a) = gB (i a)) (a : fA.ker) :
    KerModRange.map i hf hg (QuotientAddGroup.mk a : KerModRange fA gA) =
      (QuotientAddGroup.mk (kerMap i hf a) : KerModRange fB gB) :=
  rfl
end KerModRange
end GroundTheory.GroupCoh
