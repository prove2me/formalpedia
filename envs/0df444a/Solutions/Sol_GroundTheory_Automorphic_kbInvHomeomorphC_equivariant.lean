-- Prove2me | solution 1 for GroundTheory.Automorphic.kbInvHomeomorphC_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:02:55.678788+00:00
-- url     : https://prove2.me/submissions/2aa7ad50-a2ff-439a-b70f-2d0b6db49adc

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsPolar
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsKAK
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsHaar
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawaHaar
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroups
import Theorems.Thm_GroundTheory_Automorphic_coe_iwasawaHomeomorph_apply
import Theorems.Thm_GroundTheory_Automorphic_kbHomeomorph_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.coe_iwasawaHomeomorph_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix Set
open scoped ComplexOrder
set_option linter.unusedSectionVars false
variable {n : Type*} [Fintype n] [LinearOrder n]
open MeasureTheory Measure
open scoped ENNReal NNReal Matrix.Norms.L2Operator
variable [WellFoundedLT n] [LocallyFiniteOrderBot n]
namespace GroundTheory.Automorphic
theorem _root_.solution (q : unitaryGroup n ℂ × upperPosSubgroup n ℂ) (g : GL n ℂ) :
    kbInvHomeomorphC (Unitary.toUnits q.1 * g * ((q.2 : GL n ℂ))⁻¹) = q * kbInvHomeomorphC g := by
  obtain ⟨p, rfl⟩ := kbHomeomorph.surjective g
  have e : Unitary.toUnits q.1 * kbHomeomorph p * ((q.2 : GL n ℂ))⁻¹ =
      kbHomeomorph (q.1 * p.1, p.2 * q.2⁻¹) := by
    simp only [kbHomeomorph_apply, map_mul, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
  rw [e]
  simp only [kbInvHomeomorphC, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  refine Prod.ext rfl ?_
  show (p.2 * q.2⁻¹)⁻¹ = q.2 * p.2⁻¹
  rw [_root_.mul_inv_rev, inv_inv]
end GroundTheory.Automorphic
