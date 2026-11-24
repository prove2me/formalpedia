-- Prove2me | solution 1 for GlobalTheory.DualLabel.roots_reverse_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:03:40.140824+00:00
-- url     : https://prove2.me/submissions/1fb632c3-c92b-4250-bb22-fbbcc08ecfe6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootsReverseProd
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply



set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory
open GlobalTheory GlobalTheory.DualLabel
namespace GlobalTheory.DualLabel
theorem _root_.solution {K : Type} [Field K] (s : Multiset K) (hs : (0 : K) ∉ s) :
    ((s.map fun x => X - C x).prod.reverse).roots = s.map (·⁻¹) := by
  induction s using Multiset.induction_on with
  | empty => simp [reverse]
  | cons a s ih =>
    rw [Multiset.mem_cons, not_or] at hs
    have ha : a ≠ 0 := fun h => hs.1 h.symm
    have hX : (X : K[X]).reverse = 1 := by simp [reverse]
    have e : (X - C a : K[X]).reverse = C (-a) * (X - C a⁻¹) := by
      rw [sub_eq_add_neg, ← C_neg, reverse_add_C, natDegree_X, hX, mul_sub, ← C_mul, neg_mul,
        mul_inv_cancel₀ ha]
      simp [add_comm]
    have hm : (s.map fun x => X - C x).prod ≠ 0 :=
      (monic_multiset_prod_of_monic _ _ fun x _ => monic_X_sub_C x).ne_zero
    rw [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain, e, roots_mul, roots_C_mul _ (neg_ne_zero.2 ha),
      roots_X_sub_C, ih hs.2, Multiset.map_cons, Multiset.singleton_add]
    exact mul_ne_zero (mul_ne_zero (C_ne_zero.2 (neg_ne_zero.2 ha)) (X_sub_C_ne_zero _))
      (by rwa [Ne, reverse_eq_zero])
end GlobalTheory.DualLabel
