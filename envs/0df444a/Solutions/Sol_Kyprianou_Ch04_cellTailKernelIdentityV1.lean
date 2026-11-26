-- Prove2me | solution 1 for Kyprianou.Ch04.cellTailKernelIdentityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:41:27.871844+00:00
-- url     : https://prove2.me/submissions/c3aed6b4-770c-4983-9836-c0c7bc66fc44

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch04_predictableTailBoxDifferenceV1
open MeasureTheory ProbabilityTheory Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false


/-- Signed tail boxes reproduce the finite-cell kernel. -/
theorem solution {Ω ι : Type} [DecidableEq ι]
    (s : Finset ι) (T : NNReal) (a b : ι → NNReal)
    (B : ι → Set ℝ) (H : ι → Ω → ℝ)
    (hab : ∀ i ∈ s, a i ≤ b i) (hbT : ∀ i ∈ s, b i ≤ T)
    (ω : Ω) (z : ℝ × ℝ) :
    (∑ i ∈ s.product (Finset.univ : Finset Bool),
      (Ioc ((if i.2 then a i.1 else b i.1 : NNReal) : ℝ) (T : ℝ) ×ˢ B i.1).indicator
        (fun _ => if i.2 then H i.1 ω else -H i.1 ω) z) =
      ∑ i ∈ s, (Ioc (a i : ℝ) (b i : ℝ) ×ˢ B i).indicator (fun _ => H i ω) z := by
  classical
  change (∑ i ∈ (s ×ˢ (Finset.univ : Finset Bool)), _) = _
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Fintype.sum_bool]
  simp only [Bool.false_eq_true, if_false, if_true]
  have hab' : (a i : ℝ) ≤ (b i : ℝ) := by exact_mod_cast hab i hi
  have hbt' : (b i : ℝ) ≤ (T : ℝ) := by exact_mod_cast hbT i hi
  rw [Kyprianou.Ch04.predictableTailBoxDifferenceV1 _ _ _ hab' hbt']
  by_cases h : z ∈ Ioc (b i : ℝ) (T : ℝ) ×ˢ B i <;> simp [Set.indicator,h] <;> ring
