-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.rowOp_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:08:04.059489+00:00
-- url     : https://prove2.me/submissions/093386fe-daba-45a9-a684-efa448d7095e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Fischer
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowOp_comm_self
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowWt_eq_of_eigen
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_wtProj_eq_self_iff
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowOp_self_of_wtProj
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
theorem _root_.solution {μ : Fin n → ℕ} {v : Poly n} (hv : wtProj μ v = v) {i j : Fin n} (hij : i < j)
    (hne : rowOp i j v ≠ 0) :
    ∃ μ' : Fin n → ℕ, wtProj μ' (rowOp i j v) = rowOp i j v ∧ ∑ a, μ' a = ∑ a, μ a ∧
      wtHeight μ < wtHeight μ' := by
  classical
  set w := rowOp i j v
  have heig : ∀ a, rowOp a a w =
      ((μ a : ℂ) + ((if i = a then 1 else 0) - (if j = a then 1 else 0))) • w := by
    intro a
    have h1 := congrArg (fun S : Module.End ℂ (Poly n) => S v) (rowOp_comm_self a i j)
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply] at h1
    rw [h1, rowOp_self_of_wtProj μ v a hv, map_smul, add_smul]
  obtain ⟨m, hm⟩ : ∃ m, m ∈ w.support := by
    by_contra h
    push_neg at h
    exact hne (MvPolynomial.support_eq_empty.1 (Finset.eq_empty_of_forall_notMem h))
  have hwt : ∀ m' ∈ w.support, ∀ a, ((rowWt m' a : ℕ) : ℤ) =
      (μ a : ℤ) + ((if i = a then 1 else 0) - (if j = a then 1 else 0)) := by
    intro m' hm' a
    have := rowWt_eq_of_eigen heig hm' a
    have : ((rowWt m' a : ℤ) : ℂ) = (((μ a : ℤ) + ((if i = a then 1 else 0) -
        (if j = a then 1 else 0)) : ℤ) : ℂ) := by
      push_cast; rw [this]
    exact_mod_cast this
  refine ⟨rowWt m, ?_, ?_, ?_⟩
  · rw [wtProj_eq_self_iff]
    intro m' hm'
    funext a
    have h1 := hwt m' hm' a
    have h2 := hwt m hm a
    omega
  · have : ∀ a, ((rowWt m a : ℕ) : ℤ) = (μ a : ℤ) + ((if i = a then 1 else 0) - (if j = a then 1 else 0)) :=
      hwt m hm
    have hs : ((∑ a, rowWt m a : ℕ) : ℤ) = ((∑ a, μ a : ℕ) : ℤ) := by
      push_cast
      rw [Finset.sum_congr rfl fun a _ => this a, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp
    exact_mod_cast hs
  · have hsum : wtHeight (rowWt m) = wtHeight μ + (((n : ℤ) - i) - ((n : ℤ) - j)) := by
      unfold wtHeight
      simp_rw [hwt m hm]
      simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have : ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by exact_mod_cast hij
    rw [hsum]
    linarith
end GroundTheory.Automorphic.HarishChandra
