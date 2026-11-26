-- Prove2me | solution 1 for Kyprianou.Ch05.positivePoissonCrossingAtomicSumV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:59:57.585808+00:00
-- url     : https://prove2.me/submissions/82d8ed24-6e90-4e9e-afb9-ac193ad6d1fe

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_activePositivePoissonMarkIsJumpV1
import Theorems.Thm_Kyprianou_Ch05_positivePoissonJumpHasActiveMarkV1
import Theorems.Thm_Kyprianou_Ch05_uniqueCrossingReindexENNRealV1
import Theorems.Thm_Kyprianou_Ch05_monotoneMarkedCrossingClockUniqueV1
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
    {Omega : Type} (K : ℕ → Omega → ℕ) (Z : ℕ → ℕ → Omega → ℝ × ℝ)
    (w : Omega) (f : NNReal → ℝ)
    (hinj : ∀ i j : ℕ × ℕ, i.2 < K i.1 w → j.2 < K j.1 w →
      (Z i.1 i.2 w).1 = (Z j.1 j.2 w).1 → i = j)
    (hj : ∀ t : NNReal, 0 < t → f t - Function.leftLim f t =
      (∫⁻ z in {(t : ℝ)} ×ˢ Ioi (0 : ℝ), ENNReal.ofReal z.2
        ∂(poissonRandomMeasure K Z w)).toReal)
    (hm : Monotone f) (eta x : ℝ) (A B : Set ℝ) :
    (∑' i : ℕ × ℕ, if i.2 < K i.1 w then
      (if 0 < (Z i.1 i.2 w).1 ∧
        Function.leftLim f (Z i.1 i.2 w).1.toNNReal ∈ Icc (0 : ℝ) x ∧
        x - Function.leftLim f (Z i.1 i.2 w).1.toNNReal < (Z i.1 i.2 w).2 ∧
        (Z i.1 i.2 w).2 - (x - Function.leftLim f (Z i.1 i.2 w).1.toNNReal) ∈ A ∧
        x - Function.leftLim f (Z i.1 i.2 w).1.toNNReal ∈ B
        then ENNReal.ofReal (Real.exp (-eta*(Z i.1 i.2 w).1)) else 0) else 0) =
    ∑' t : NNReal, if 0 < t ∧ f t > x ∧ Function.leftLim f t ∈ Icc (0 : ℝ) x ∧
      f t-x ∈ A ∧ x-Function.leftLim f t ∈ B then
      ENNReal.ofReal (Real.exp (-eta*(t : ℝ))) else 0 := by
  classical
  let a (i : ℕ × ℕ) := Z i.1 i.2 w
  let c (i : ℕ × ℕ) := (a i).1.toNNReal
  let L := Function.leftLim f
  let C (i : ℕ × ℕ) := i.2 < K i.1 w ∧ 0 < (a i).1 ∧ L (c i) ∈ Icc (0 : ℝ) x ∧
    x-L (c i) < (a i).2 ∧ (a i).2-(x-L (c i)) ∈ A ∧ x-L (c i) ∈ B
  let D (t : NNReal) := 0 < t ∧ f t > x ∧ L t ∈ Icc (0 : ℝ) x ∧
    f t-x ∈ A ∧ x-L t ∈ B
  let g (t : NNReal) := ENNReal.ofReal (Real.exp (-eta*(t : ℝ)))
  have hmap (i : ℕ × ℕ) (hi : C i) : D (c i) := by
    have hp : 0 < (a i).2 := by linarith [hi.2.2.1.2,hi.2.2.2.1]
    have h := activePositivePoissonMarkIsJumpV1 K Z w f hinj hj i hi.1 hi.2.1 hp
    change f (c i)-L (c i) = (a i).2 at h
    refine ⟨Real.toNNReal_pos.mpr hi.2.1,by linarith [hi.2.2.2.1],hi.2.2.1,?_,hi.2.2.2.2.2⟩
    rw [show f (c i)-x = (a i).2-(x-L (c i)) by linarith]
    exact hi.2.2.2.2.1
  have hinj' (i j : ℕ × ℕ) (hi : C i) (hj' : C j) (h : c i = c j) : i = j := by
    have hc := congrArg (fun t : NNReal => (t : ℝ)) h
    simp only [c,Real.coe_toNNReal _ hi.2.1.le,Real.coe_toNNReal _ hj'.2.1.le] at hc
    exact hinj i j hi.1 hj'.1 hc
  have huniq (t u : NNReal) (ht : D t) (hu : D u) : t = u := by
    have h1 := monotoneMarkedCrossingClockUniqueV1 f hm x t ht.1 ht.2.1 ht.2.2.1.2
    have h2 := monotoneMarkedCrossingClockUniqueV1 f hm x u hu.1 hu.2.1 hu.2.2.1.2
    exact ENNReal.coe_injective (h1.symm.trans h2)
  have hsurj (t : NNReal) (ht : D t) : ∃ i, C i ∧ c i = t := by
    have hp : 0 < f t-L t := by linarith [ht.2.1,ht.2.2.1.2]
    obtain ⟨i,hi,hit,hz⟩ := positivePoissonJumpHasActiveMarkV1 K Z w f hinj hj t ht.1 hp
    have htime : 0 < (a i).1 := by change 0 < (Z i.1 i.2 w).1; rw [hit]; exact_mod_cast ht.1
    have hc : c i = t := by change (Z i.1 i.2 w).1.toNNReal = t; rw [hit,Real.toNNReal_coe]
    refine ⟨i,⟨hi,htime,?_,?_,?_,?_⟩,hc⟩
    · rw [hc]; exact ht.2.2.1
    · rw [hc]; change x-L t < (Z i.1 i.2 w).2; rw [hz]; linarith [ht.2.1]
    · rw [hc]; change (Z i.1 i.2 w).2-(x-L t) ∈ A
      rw [hz,show f t-L t-(x-L t) = f t-x by ring]; exact ht.2.2.2.1
    · rw [hc]; exact ht.2.2.2.2
  have he := uniqueCrossingReindexENNRealV1 c C D g hmap hinj' huniq hsurj
  calc
    _ = ∑' i, @ite ENNReal (C i) (Classical.propDecidable (C i)) (g (c i)) 0 := by
      apply tsum_congr
      intro i
      by_cases hi : C i
      · have ht : 0 < (a i).1 := hi.2.1
        simp only [if_pos hi,if_pos hi.1,g,c,Real.coe_toNNReal _ ht.le]
        exact if_pos (show 0 < (Z i.1 i.2 w).1 ∧
          Function.leftLim f (Z i.1 i.2 w).1.toNNReal ∈ Icc (0 : ℝ) x ∧
          x-Function.leftLim f (Z i.1 i.2 w).1.toNNReal < (Z i.1 i.2 w).2 ∧
          (Z i.1 i.2 w).2-(x-Function.leftLim f (Z i.1 i.2 w).1.toNNReal) ∈ A ∧
          x-Function.leftLim f (Z i.1 i.2 w).1.toNNReal ∈ B from hi.2)
      · simp only [if_neg hi]
        split_ifs with h₁ h₂
        · exact (hi ⟨h₁,h₂⟩).elim
        · rfl
        · rfl
    _ = ∑' t, @ite ENNReal (D t) (Classical.propDecidable (D t)) (g t) 0 := he
    _ = _ := by
      apply tsum_congr
      intro t
      by_cases ht : D t
      · rw [if_pos ht]
        exact (if_pos (show 0 < t ∧ f t > x ∧ Function.leftLim f t ∈ Icc (0 : ℝ) x ∧
          f t-x ∈ A ∧ x-Function.leftLim f t ∈ B from ht)).symm
      · rw [if_neg ht]
        exact (if_neg (show ¬ (0 < t ∧ f t > x ∧ Function.leftLim f t ∈ Icc (0 : ℝ) x ∧
          f t-x ∈ A ∧ x-Function.leftLim f t ∈ B) from ht)).symm
