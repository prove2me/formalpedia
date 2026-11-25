-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.word_blockW_diagL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:30:48.106822+00:00
-- url     : https://prove2.me/submissions/817a2c89-5ff3-4440-88a0-b4a9a79474b2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_ConstantCoeffRhoOneCanonMonomial
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_diagL
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_nodup_allL
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcEmb_X
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_diagExp_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_expand_zero
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_iterPd_nil
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_pbw_apply
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_append
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_cons
import Theorems.Thm_GroundTheory_Automorphic_HarishChandra_word_flatMap_replicate
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
theorem _root_.solution (m : Fin n × Fin n →₀ ℕ) :
    word (blockW (diagL n) m) = hcEmb (monomial (diagExp m) 1) := by
  classical
  let g : Fin n × Fin n → cartanSub n := fun a =>
    if h : a.1 = a.2 then ⟨e (a.1, a.1), Algebra.subset_adjoin (s := cartanSet n) (Set.mem_range_self a.1)⟩ ^ m a else 1
  have hg : ∀ a ∈ diagL n, ((g a : cartanSub n) : U n) = e a ^ m a := by
    intro a ha
    have h : a.1 = a.2 := mem_diagL.1 ha
    simp only [g, dif_pos h, SubmonoidClass.coe_pow]
    congr 2
    exact Prod.ext rfl h
  have hnodup : (diagL n).Nodup := nodup_allL.filter _
  have hfin : (diagL n).toFinset = Finset.univ.filter fun a : Fin n × Fin n => a.1 = a.2 := by
    ext a; simp [mem_diagL, IsDiag]
  have h1 : word (blockW (diagL n) m) = (((diagL n).map g).prod : cartanSub n) := by
    rw [blockW, word_flatMap_replicate, SubmonoidClass.coe_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun a ha => (hg a ha).symm)
  have h2 : ((diagL n).map g).prod = ∏ i : Fin n, g (i, i) := by
    refine (List.prod_toFinset g hnodup).symm.trans ?_
    rw [hfin, Finset.prod_filter, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
    simp [g]
  rw [h1, h2, hcEmb, AlgHom.comp_apply, aeval_monomial, map_one, one_mul,
    Finsupp.prod_fintype _ _ (by simp)]
  simp only [Subalgebra.coe_val, diagExp_apply, g]
  rfl
end GroundTheory.Automorphic.HarishChandra
