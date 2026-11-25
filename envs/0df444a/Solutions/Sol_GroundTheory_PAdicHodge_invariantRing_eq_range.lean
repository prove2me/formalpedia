-- Prove2me | solution 1 for GroundTheory.PAdicHodge.invariantRing_eq_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:18:07.963806+00:00
-- url     : https://prove2.me/submissions/bf1d0e8b-0cc8-4306-8f0f-5d699a04153e

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
namespace GroundTheory.PAdicHodge
theorem _root_.solution
    (hK : ∀ b : B, (∀ g : G, g • b = b) → ∃ k : K, algebraMap K B k = b) :
    invariantRing G F B = (IsScalarTower.toAlgHom F K B).range := by
  ext b
  constructor
  · intro hb
    obtain ⟨k, hk⟩ := hK b hb
    exact ⟨k, hk⟩
  · rintro ⟨k, rfl⟩ g
    exact smul_algebraMap g k
end GroundTheory.PAdicHodge
