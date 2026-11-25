-- Prove2me | solution 1 for GroundTheory.ProfCoh.nestedHomeomorph_d_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:24:54.191962+00:00
-- url     : https://prove2.me/submissions/8c810c00-3b66-46ed-bdcd-86ae454cf391

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_BridgeNested
import Theorems.Thm_GroundTheory_ProfCoh_nestedHomeomorph_succ_apply
import Theorems.Thm_GroundTheory_ProfCoh_nestedLinearEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.nestedLinearEquiv_apply

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory TopRep ContRepresentation
universe u v w
variable {k G : Type u} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]
variable (X : TopRep.{u} k G)
namespace GroundTheory.ProfCoh
theorem _root_.solution (m : ℕ) (a : resolutionX X m) (x : Fin (m + 1) → G) :
    nestedHomeomorph X (m + 1) ((d X m).hom a) x =
      ∑ i : Fin (m + 1), (-1 : k) ^ (i : ℕ) • nestedHomeomorph X m a (fun j => x (i.succAbove j)) := by
  induction m with
  | zero =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    simp only [Fin.val_zero, pow_zero, one_smul]
    rfl
  | succ m ih =>
    have h1 : ((d X (m + 1)).hom a : C(G, resolutionX X (m + 1))) (x 0) =
        a - (d X m).hom ((a : C(G, resolutionX X m)) (x 0)) := by
      rw [hom_d_succ]
      rfl
    rw [nestedHomeomorph_succ_apply, h1,
      show nestedHomeomorph X (m + 1) (a - (d X m).hom ((a : C(G, resolutionX X m)) (x 0))) =
        nestedHomeomorph X (m + 1) a -
          nestedHomeomorph X (m + 1) ((d X m).hom ((a : C(G, resolutionX X m)) (x 0))) from
        map_sub (nestedLinearEquiv X (m + 1)) _ _,
      ContinuousMap.sub_apply, ih, Fin.sum_univ_succ (n := m + 1)]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero, Fin.val_succ, pow_succ,
      mul_neg_one, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]
    congr 1
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [nestedHomeomorph_succ_apply X m a, Fin.succ_succAbove_zero]
    congr 1
    funext j
    simp only [Fin.tail, Fin.succ_succAbove_succ]
end GroundTheory.ProfCoh
