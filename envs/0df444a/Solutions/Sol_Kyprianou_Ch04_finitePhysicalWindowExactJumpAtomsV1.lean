-- Prove2me | solution 1 for Kyprianou.Ch04.finitePhysicalWindowExactJumpAtomsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:23:41.45192+00:00
-- url     : https://prove2.me/submissions/3a95a85e-16d2-4410-85b9-5e77934496dd

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_pathJumpMeasureCountV1
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A finite physical window consists exactly of its original marked jump times, with unit mass. -/
theorem solution {Ω : Type} (X L : NNReal → Ω → ℝ) (ω : Ω)
    (hX : Measurable (fun t => X t ω)) (hL : Measurable (fun t => L t ω))
    (R : Set (ℝ × ℝ)) (hR : MeasurableSet R)
    (hfin : Kyprianou.Ch04.pathJumpMeasure X L ω R < ⊤) :
    ∃ S : Finset NNReal,
      (∀ t, t ∈ S ↔ 0 < t ∧ X t ω ≠ L t ω ∧ ((t : ℝ),X t ω - L t ω) ∈ R) ∧
      (Kyprianou.Ch04.pathJumpMeasure X L ω).restrict R =
        ∑ t ∈ S, Measure.dirac ((t : ℝ), X t ω - L t ω) := by
  classical
  let p := fun t : NNReal => ((t : ℝ),X t ω - L t ω)
  let J : Set NNReal := {t | 0 < t ∧ X t ω ≠ L t ω ∧ p t ∈ R}
  have hf : J.Finite := by
    rw [Kyprianou.Ch04.pathJumpMeasureCountV1 X L ω hX hL R hR] at hfin
    apply Set.encard_lt_top_iff.mp
    exact_mod_cast hfin
  let S := hf.toFinset
  refine ⟨S,fun t => hf.mem_toFinset,?_⟩
  ext A hA
  rw [Measure.restrict_apply hA,Kyprianou.Ch04.pathJumpMeasureCountV1 X L ω hX hL
    (A ∩ R) (hA.inter hR),Measure.finsetSum_apply S (fun t => Measure.dirac (p t)) A]
  let F := S.filter (fun t => p t ∈ A)
  have he : {t : NNReal | 0 < t ∧ X t ω ≠ L t ω ∧ p t ∈ A ∩ R} = (F : Set NNReal) := by
    ext t
    simp [F,S,J, and_assoc,and_left_comm,and_comm]
  change (↑({t : NNReal | 0 < t ∧ X t ω ≠ L t ω ∧ p t ∈ A ∩ R}.encard) : ENNReal) = _
  rw [he,Set.encard_coe_eq_coe_finsetCard]
  simp only [Measure.dirac_apply' _ hA]
  simpa [F,Set.indicator_apply] using (Finset.sum_boole (R := ENNReal) (fun t => p t ∈ A) S).symm
