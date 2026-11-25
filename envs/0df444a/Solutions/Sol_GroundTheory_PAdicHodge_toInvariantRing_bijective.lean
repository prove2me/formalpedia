-- Prove2me | solution 1 for GroundTheory.PAdicHodge.toInvariantRing_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:23:19.558345+00:00
-- url     : https://prove2.me/submissions/e6650000-37fc-47f4-a97d-47c4fbf66624

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_Admissible
import Definitions.Def_GroundTheory_PAdicHodge_AdmissibleField
import Theorems.Thm_GroundTheory_PAdicHodge_coe_toInvariantRing
import Theorems.Thm_GroundTheory_PAdicHodge_IsRegular_coe_basisOfIsAdmissible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.IsRegular.coe_basisOfIsAdmissible


attribute [local simp] GroundTheory.PAdicHodge.coe_toInvariantRing

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open TensorProduct Module
variable (G F K B : Type*) [Group G] [Field F] [Field K] [CommRing B] [Algebra F K] [Algebra K B]
  [Algebra F B] [IsScalarTower F K B] [MulSemiringAction G B] [SMulCommClass G F B]
  [SMulCommClass G K B]
variable {V : Type*} [AddCommGroup V] [Module F V] (ρ : Representation F G V)
variable {G F K B}
omit [Algebra F K] [IsScalarTower F K B]
namespace GroundTheory.PAdicHodge
theorem _root_.solution [Nontrivial B]
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) :
    Function.Bijective (toInvariantRing G F K B) := by
  refine ⟨fun a b hab => (algebraMap K B).injective ?_, fun e => ?_⟩
  · simpa using congrArg Subtype.val hab
  · obtain ⟨k, hk⟩ := hK e e.2
    exact ⟨k, Subtype.ext hk⟩
end GroundTheory.PAdicHodge
