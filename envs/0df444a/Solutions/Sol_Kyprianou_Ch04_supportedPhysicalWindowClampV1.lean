-- Prove2me | solution 1 for Kyprianou.Ch04.supportedPhysicalWindowClampV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:24:37.689667+00:00
-- url     : https://prove2.me/submissions/3acb70f5-6d99-45b5-9147-4abf633aa61d

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_supportedSetIntegrals
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

/-- Finite-mark support and nonnegative window time allow a predictable kernel to be clamped at the horizon. -/
theorem solution {Ω : Type} (R : Measure (ℝ × ℝ)) (T : NNReal)
    (B : Set ℝ) (hB : MeasurableSet B)
    (g : (NNReal × Ω) × ℝ → ℝ) (hs : ∀ p, p.2 ∉ B → g p = 0) (ω : Ω) :
    (∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set ℝ),
      g ((z.1.toNNReal,ω),z.2) ∂ R) =
    ∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ B, g ((min z.1.toNNReal T,ω),z.2) ∂ R := by
  rw [Kyprianou.Ch04.supportedSetIntegrals R _ _ (measurableSet_Icc.prod hB)
    (measurableSet_Icc.prod MeasurableSet.univ)
    (Set.prod_mono subset_rfl (subset_univ B)) _ (fun z hz h => hs _ (fun hBz => h ⟨hz.1,hBz⟩))]
  apply setIntegral_congr_fun (measurableSet_Icc.prod hB)
  intro z hz
  have ht : z.1.toNNReal ≤ T := by
    exact Real.toNNReal_le_iff_le_coe.mpr hz.1.2
  simp only [min_eq_left ht]
