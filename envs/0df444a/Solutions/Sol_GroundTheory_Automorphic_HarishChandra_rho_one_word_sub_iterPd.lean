-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.rho_one_word_sub_iterPd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:08:10.215898+00:00
-- url     : https://prove2.me/submissions/689a6c9e-ed56-478f-8271-488499100788

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rho_one_e_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_geDeg_anti
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_pderiv_mem_geDeg
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowOp_mem_geDeg
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_mem_geDeg
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_U_induction
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
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_append
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_cons
attribute [local simp] GroundTheory.Automorphic.HarishChandra.word_nil


attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_nil
attribute [local simp] GroundTheory.Automorphic.HarishChandra.iterPd_cons

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (w : List (Fin n × Fin n)) {t : ℕ} {f : Poly n}
    (hw : w.length ≤ t) (hf : f ∈ geDeg t) :
    rho 1 (word w) f - iterPd w f ∈ geDeg (t - w.length + 1) := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [List.length_cons] at hw ⊢
    have ih := ih (by omega)
    rw [word_cons, map_mul, Module.End.mul_apply, iterPd_cons]
    obtain ⟨i, j⟩ := a
    rw [rho_one_e_apply]
    set g := rho 1 (word w) f
    have e1 : pderiv (j, i) g + rowOp i j g - pderiv (j, i) (iterPd w f) =
        pderiv (j, i) (g - iterPd w f) + rowOp i j (g - iterPd w f) + rowOp i j (iterPd w f) := by
      rw [map_sub, map_sub]; abel
    rw [e1]
    have ht : t - (w.length + 1) + 1 = t - w.length := by omega
    rw [ht]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · have := pderiv_mem_geDeg (j, i) ih
      rwa [Nat.add_sub_cancel] at this
    · exact geDeg_anti (by omega) (rowOp_mem_geDeg i j ih)
    · exact rowOp_mem_geDeg i j (iterPd_mem_geDeg w hf)
end GroundTheory.Automorphic.HarishChandra
