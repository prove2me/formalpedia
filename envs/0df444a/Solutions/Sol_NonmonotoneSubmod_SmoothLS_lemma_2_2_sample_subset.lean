-- Prove2me | solution 1 for NonmonotoneSubmod.SmoothLS.lemma_2_2_sample_subset
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:21:33.227057+00:00
-- url     : https://prove2.me/submissions/32078f2e-5314-43aa-b049-e654003551b7

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

namespace NonmonotoneSubmod.SmoothLS

theorem aux_l22s_main {X : Type} [Fintype X] [DecidableEq X] (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Finset X) :
    ∀ g : Finset X → ℝ, NonmonotoneSubmod.Shared.Submodular g →
    (1 - p) * g ∅ + p * g A ≤
      ∑ T ∈ A.powerset, p ^ T.card * (1 - p) ^ (A \ T).card * g T := by
  induction A using Finset.induction_on with
  | empty =>
    intro g _
    simp only [Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty, pow_zero,
      Finset.sdiff_self, one_mul]
    linarith
  | @insert a A ha ih =>
    intro g hg
    have hh : NonmonotoneSubmod.Shared.Submodular (fun S => g (insert a S)) := by
      intro S T
      have := hg (insert a S) (insert a T)
      rw [← Finset.insert_union_distrib, ← Finset.insert_inter_distrib] at this
      exact this
    have ih1 := ih g hg
    have ih2 := ih (fun S => g (insert a S)) hh
    have hsub := hg A {a}
    have hunion : A ∪ {a} = insert a A := by
      rw [Finset.union_comm]; rfl
    have hinter : A ∩ {a} = ∅ := by
      rw [Finset.inter_singleton_of_notMem ha]
    rw [hunion, hinter] at hsub
    rw [Finset.sum_powerset_insert ha]
    have e1 : ∑ T ∈ A.powerset, p ^ T.card * (1 - p) ^ (insert a A \ T).card * g T
        = (1 - p) * ∑ T ∈ A.powerset, p ^ T.card * (1 - p) ^ (A \ T).card * g T := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro T hT
      have haT : a ∉ T := fun h => ha (Finset.mem_powerset.mp hT h)
      rw [Finset.insert_sdiff_of_notMem _ haT]
      have : a ∉ A \ T := fun h => ha (Finset.mem_sdiff.mp h).1
      rw [Finset.card_insert_of_notMem this]
      ring
    have e2 : ∑ T ∈ A.powerset,
          p ^ (insert a T).card * (1 - p) ^ (insert a A \ insert a T).card * g (insert a T)
        = p * ∑ T ∈ A.powerset, p ^ T.card * (1 - p) ^ (A \ T).card * g (insert a T) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro T hT
      have haT : a ∉ T := fun h => ha (Finset.mem_powerset.mp hT h)
      rw [Finset.card_insert_of_notMem haT, Finset.insert_sdiff_insert,
        Finset.sdiff_insert_of_notMem ha]
      ring
    rw [e1, e2]
    beta_reduce at ih2
    rw [show (insert a (∅ : Finset X)) = {a} from by simp] at ih2
    have hq : 0 ≤ 1 - p := by linarith
    have hpq : 0 ≤ p * (1 - p) := mul_nonneg hp0 hq
    nlinarith [mul_le_mul_of_nonneg_left ih1 hq, mul_le_mul_of_nonneg_left ih2 hp0,
      mul_le_mul_of_nonneg_left hsub hpq]

end NonmonotoneSubmod.SmoothLS

open NonmonotoneSubmod.SmoothLS

theorem solution {X : Type} [Fintype X] [DecidableEq X]
    (g : Finset X → ℝ) (hg : NonmonotoneSubmod.Shared.Submodular g) (A : Finset X) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * g ∅ + p * g A ≤
      ∑ T ∈ A.powerset, p ^ T.card * (1 - p) ^ (A \ T).card * g T := by
  exact aux_l22s_main p hp0 hp1 A g hg
