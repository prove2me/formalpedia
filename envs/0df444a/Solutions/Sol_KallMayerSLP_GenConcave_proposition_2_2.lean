-- Prove2me | solution 1 for KallMayerSLP.GenConcave.proposition_2_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:14:42.896349+00:00
-- url     : https://prove2.me/submissions/0a51e097-9997-48a8-9baa-636947335245

import Mathlib
import Definitions.Def_KallMayerSLP_GenConcave_IsGammaConcaveFun
import Definitions.Def_KallMayerSLP_GenConcave_IsGammaConcaveMeasure

open MeasureTheory

open scoped Pointwise

open KallMayerSLP.GenConcave in
theorem solution {r : ℕ} (γ : EReal) (μ : Measure (Fin r → ℝ))
    (hμ : IsGammaConcaveMeasure γ μ) (A : Set (Fin r → ℝ)) (hA : Convex ℝ A)
    (hAc : IsClosed A) :
    IsGammaConcaveFun γ (fun y : Fin r → ℝ => (μ (A + {y})).toReal) := by
  refine ⟨fun y => ENNReal.toReal_nonneg, fun x y lam hlam => ?_⟩
  have hcl : ∀ z : Fin r → ℝ, IsClosed (A + {z}) := by
    intro z
    rw [Set.add_singleton]
    exact (Homeomorph.addRight z).isClosedMap A hAc
  have hcv : ∀ z : Fin r → ℝ, Convex ℝ (A + {z}) := fun z => hA.add (convex_singleton z)
  have hset : lam • (A + {x}) + (1 - lam) • (A + {y}) = A + {lam • x + (1 - lam) • y} := by
    rw [smul_add, smul_add, Set.smul_set_singleton, Set.smul_set_singleton, add_add_add_comm,
      ← hA.add_smul hlam.1 (sub_nonneg.mpr hlam.2), add_sub_cancel, one_smul,
      Set.singleton_add_singleton]
  have h := hμ.2 (A + {x}) (A + {y}) (hcv x) (hcv y) (hcl x).measurableSet
    (hcl y).measurableSet lam hlam (by rw [hset]; exact (hcl _).measurableSet)
  rw [hset] at h
  exact h
