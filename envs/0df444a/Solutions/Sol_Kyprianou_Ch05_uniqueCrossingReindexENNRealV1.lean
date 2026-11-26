-- Prove2me | solution 1 for Kyprianou.Ch05.uniqueCrossingReindexENNRealV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:26:51.071284+00:00
-- url     : https://prove2.me/submissions/6fabb3f3-77ed-43ad-a611-baed421b837d

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false
theorem solution
    {I T : Type} (clock : I → T) (C : I → Prop) (D : T → Prop)
    (g : T → ENNReal)
    (hmap : ∀ i, C i → D (clock i))
    (hinj : ∀ i j, C i → C j → clock i = clock j → i = j)
    (huniq : ∀ t u, D t → D u → t = u)
    (hsurj : ∀ t, D t → ∃ i, C i ∧ clock i = t) :
    (∑' i, if C i then g (clock i) else 0) =
      ∑' t, if D t then g t else 0 := by
  classical
  by_cases h : ∃ t, D t
  · obtain ⟨t,ht⟩ := h
    obtain ⟨i,hi,hit⟩ := hsurj t ht
    have hz₁ (j : I) (hji : j ≠ i) : (if C j then g (clock j) else 0) = 0 := by
      apply if_neg
      intro hj
      exact hji (hinj j i hj hi ((huniq _ _ (hmap j hj) ht).trans hit.symm))
    have hz₂ (u : T) (hut : u ≠ t) : (if D u then g u else 0) = 0 :=
      if_neg fun hu => hut (huniq u t hu ht)
    rw [tsum_eq_single i hz₁,tsum_eq_single t hz₂,if_pos hi,if_pos ht,hit]
  · have hc : ∀ i, ¬ C i := fun i hi => h ⟨clock i,hmap i hi⟩
    have hd : ∀ t, ¬ D t := fun t ht => h ⟨t,ht⟩
    rw [ENNReal.tsum_eq_zero.mpr (fun i => if_neg (hc i)),
      ENNReal.tsum_eq_zero.mpr (fun t => if_neg (hd t))]
