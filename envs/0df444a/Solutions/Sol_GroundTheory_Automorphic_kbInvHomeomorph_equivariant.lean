-- Prove2me | solution 1 for GroundTheory.Automorphic.kbInvHomeomorph_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:02:56.36647+00:00
-- url     : https://prove2.me/submissions/ac2d50a6-7327-4170-98c1-dc6d9706bc5f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsHaar
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawaHaar
import Theorems.Thm_GroundTheory_Automorphic_kbHomeomorph_apply
import Theorems.Thm_GroundTheory_Automorphic_coe_iwasawaHomeomorph_apply
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
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n]
open MeasureTheory Measure
open scoped ENNReal NNReal Matrix.Norms.L2Operator
variable [WellFoundedLT n] [LocallyFiniteOrderBot n]
namespace GroundTheory.Automorphic
theorem _root_.solution (q : unitaryGroup n ℝ × upperPosSubgroup n ℝ) (g : GL n ℝ) :
    kbInvHomeomorph (Unitary.toUnits q.1 * g * ((q.2 : GL n ℝ))⁻¹) = q * kbInvHomeomorph g := by
  obtain ⟨p, rfl⟩ := kbHomeomorph.surjective g
  have e : Unitary.toUnits q.1 * kbHomeomorph p * ((q.2 : GL n ℝ))⁻¹ =
      kbHomeomorph (q.1 * p.1, p.2 * q.2⁻¹) := by
    simp only [kbHomeomorph_apply, map_mul, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
  rw [e]
  simp only [kbInvHomeomorph, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  refine Prod.ext rfl ?_
  show (p.2 * q.2⁻¹)⁻¹ = q.2 * p.2⁻¹
  rw [_root_.mul_inv_rev, inv_inv]
end GroundTheory.Automorphic
