-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.rowOp_comm_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:57:53.550409+00:00
-- url     : https://prove2.me/submissions/18ecd41c-cdf3-4462-82fd-af003420b32b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Fischer
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowOp_X
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowDer_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_zero_left
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_fischer_zero_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.fischer_zero_left
attribute [local simp] GroundTheory.Automorphic.HarishChandra.fischer_zero_right



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (a i j : Fin n) :
    rowOp a a * rowOp i j =
      rowOp i j * rowOp a a + ((if i = a then 1 else 0) - (if j = a then 1 else 0) : ℂ) • rowOp i j := by
  have key : ⁅rowDer a a, rowDer i j⁆ =
      ((if i = a then 1 else 0) - (if j = a then 1 else 0) : ℂ) • rowDer i j := by
    apply MvPolynomial.derivation_ext
    rintro ⟨b, c⟩
    rw [Derivation.commutator_apply, Derivation.smul_apply, rowDer_apply, rowDer_apply,
      rowDer_apply, rowDer_apply]
    by_cases hbj : b = j <;> by_cases hba : b = a <;> by_cases hia : i = a <;>
      simp_all [rowOp_X]
  refine LinearMap.ext fun f => ?_
  have h := congrArg (fun D : Derivation ℂ (Poly n) (Poly n) => D f) key
  simp only [Derivation.commutator_apply, Derivation.smul_apply, rowDer_apply] at h
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply]
  rw [← h]
  abel
end GroundTheory.Automorphic.HarishChandra
