-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.canon_notUpper_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:44:00.581883+00:00
-- url     : https://prove2.me/submissions/34d9bd20-5457-4bf4-8227-72a48678b2ce

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_ConstantCoeffRhoOneCanonMonomial
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_lowL
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_diagL
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_upL
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_blockW_congr
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_blockW_eq_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_eq_blocks
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcEmb_X
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_diagExp_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_isUpper_of_mem_support
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_not_upper_of_lower
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_not_upper_of_diag
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_expand_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_pbw_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_append
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HarishChandra.canon_zero
attribute [local simp] GroundTheory.Automorphic.HarishChandra.expand_zero
attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_nil
attribute [local simp] GroundTheory.Automorphic.HarishChandra.pbw_apply
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_append
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_nil


attribute [local simp] GroundTheory.Automorphic.HarishChandra.hcEmb_X
attribute [local simp] GroundTheory.Automorphic.HarishChandra.diagExp_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
open scoped IsMulCommutative
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution {m m' : Fin n × Fin n →₀ ℕ} (hm' : ∀ a ∈ m'.support, IsUpper a) :
    word (blockW (lowL n) m) * word (blockW (diagL n) m) * canon m' = canon (notUpper m + m') := by
  have hlow : ∀ a ∈ lowL n, m' a = 0 := fun a ha =>
    isUpper_of_mem_support hm' (not_upper_of_lower (mem_lowL.1 ha))
  have hdiag : ∀ a ∈ diagL n, m' a = 0 := fun a ha =>
    isUpper_of_mem_support hm' (not_upper_of_diag (mem_diagL.1 ha))
  rw [canon_eq_blocks m', blockW_eq_nil hlow, blockW_eq_nil hdiag, canon_eq_blocks (notUpper m + m')]
  simp only [word_nil, one_mul]
  congr 2
  · refine congrArg word (blockW_congr fun a ha => ?_)
    have h := mem_lowL.1 ha
    simp [notUpper, not_upper_of_lower h, hlow a ha]
  · refine congrArg word (blockW_congr fun a ha => ?_)
    have h := mem_diagL.1 ha
    simp [notUpper, not_upper_of_diag h, hdiag a ha]
  · refine blockW_congr fun a ha => ?_
    have h := mem_upL.1 ha
    simp [notUpper, h]
end GroundTheory.Automorphic.HarishChandra
