-- Prove2me | solution 1 for GlobalTheory.continuousMultilinearMap_ext_hilbertBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T06:04:01.816162+00:00
-- url     : https://prove2.me/submissions/200d2107-8e6e-4d54-8c85-37130f52d7c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SplitHeightSummableExpNegAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousMultilinearMapExtHilbertBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (ι : Type) [Fintype ι] [DecidableEq ι]
    (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)]
    (J : ι → Type) (e : ∀ i, HilbertBasis (J i) ℂ (Hs i)) (F : Type) [NormedAddCommGroup F]
    [NormedSpace ℂ F] (f g : ContinuousMultilinearMap ℂ Hs F)
    (h : ∀ j : ∀ i, J i, f (fun i => e i (j i)) = g (fun i => e i (j i))) : f = g := by
  have key : ∀ s : Finset ι, ∀ y : ∀ i, Hs i,
      (∀ i, i ∉ s → y i ∈ Set.range (e i)) → f y = g y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro y hy
      choose j hj using fun i => hy i (by simp)
      have hy' : y = fun i => e i (j i) := funext fun i => (hj i).symm
      rw [hy']
      exact h j
    | insert a s ha ih =>
      intro y hy
      let L : Hs a →L[ℂ] F := (f - g).toContinuousLinearMap y a
      have hL : Set.EqOn (L : Hs a → F) (0 : Hs a →L[ℂ] F) (Set.range (e a)) := by
        intro z hz
        simp only [L, ContinuousMultilinearMap.toContinuousLinearMap_apply,
          ContinuousMultilinearMap.sub_apply, ContinuousLinearMap.zero_apply, sub_eq_zero]
        apply ih
        intro i hi
        by_cases hia : i = a
        · subst hia
          simpa using hz
        · rw [Function.update_of_ne hia]
          exact hy i (by simp [hia, hi])
      have hdense : Dense (Submodule.span ℂ (Set.range (e a)) : Set (Hs a)) := by
        exact Submodule.dense_iff_topologicalClosure_eq_top.mpr (e a).dense_span
      have hL0 : L = 0 := ContinuousLinearMap.ext_on hdense hL
      have hya := congrArg (fun M : Hs a →L[ℂ] F => M (y a)) hL0
      simp only [L, ContinuousMultilinearMap.toContinuousLinearMap_apply,
        ContinuousMultilinearMap.sub_apply, ContinuousLinearMap.zero_apply, sub_eq_zero,
        Function.update_eq_self] at hya
      exact hya
  ext y
  exact key Finset.univ y (by simp)
end GlobalTheory
