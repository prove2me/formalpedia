-- Prove2me | solution 1 for Kyprianou.Ch03.setIntegralEqualityPiSystemV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:38:37.42903+00:00
-- url     : https://prove2.me/submissions/b8c672f3-b104-42d9-a1ae-4b8075679ac0

import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.Integral.Bochner.Set
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem solution
    {Omega : Type} [mΩ : MeasurableSpace Omega]
    (P : Measure Omega) (j : MeasurableSpace Omega) (hj : j ≤ mΩ)
    (R : Set (Set Omega)) (hgen : j = MeasurableSpace.generateFrom R) (hpi : IsPiSystem R)
    (f q : Omega → ℝ) (hf : Integrable f P) (hq : Integrable q P)
    (htotal : (∫ x, q x ∂P) = ∫ x, f x ∂P)
    (hR : ∀ S ∈ R, (∫ x in S, q x ∂P) = ∫ x in S, f x ∂P) :
    ∀ S : Set Omega, MeasurableSet[j] S → (∫ x in S, q x ∂P) = ∫ x in S, f x ∂P := by
  refine @MeasurableSpace.induction_on_inter Omega j
    (fun S _ => (∫ x in S, q x ∂P) = ∫ x in S, f x ∂P)
    R hgen hpi (by simp) hR ?_ ?_
  · intro S hS ih
    rw [setIntegral_compl (hj _ hS) hq, setIntegral_compl (hj _ hS) hf, htotal, ih]
  · intro T hd hT ih
    rw [integral_iUnion (fun i => hj _ (hT i)) hd hq.integrableOn,
      integral_iUnion (fun i => hj _ (hT i)) hd hf.integrableOn]
    exact tsum_congr ih
