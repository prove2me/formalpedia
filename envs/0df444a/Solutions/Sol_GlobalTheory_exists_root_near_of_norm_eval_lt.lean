-- Prove2me | solution 1 for GlobalTheory.exists_root_near_of_norm_eval_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:46:56.568889+00:00
-- url     : https://prove2.me/submissions/44487c8b-5e72-4e0c-96c5-7787e03d3d6e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsEmbeddingsOverInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (p : Polynomial ℂ) (hp : p.Monic) (x : ℂ) (δ : ℝ)
    (hδ : 0 < δ) (h : ‖p.eval x‖ < δ ^ p.natDegree) : ∃ r, p.IsRoot r ∧ ‖r - x‖ < δ := by
  by_contra hcon
  push Not at hcon
  have hs := IsAlgClosed.splits p
  rw [hs.eval_eq_prod_roots_of_monic hp, hs.natDegree_eq_card_roots] at h
  have key : ∀ s : Multiset ℂ, (∀ r ∈ s, δ ≤ ‖r - x‖) →
      δ ^ s.card ≤ ‖(s.map fun r => x - r).prod‖ := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      intro hs
      simp only [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, norm_mul, pow_succ']
      refine mul_le_mul ?_ (ih fun r hr => hs r (Multiset.mem_cons_of_mem hr)) (by positivity)
        (norm_nonneg _)
      rw [norm_sub_rev]
      exact hs a (Multiset.mem_cons_self _ _)
  exact absurd h (not_lt.2 (key _ fun r hr => hcon r (Polynomial.isRoot_of_mem_roots hr)))
end GlobalTheory
