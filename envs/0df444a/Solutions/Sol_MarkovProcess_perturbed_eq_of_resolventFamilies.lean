-- Prove2me | solution 1 for MarkovProcess.perturbed_eq_of_resolventFamilies
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:44:37.986984+00:00
-- url     : https://prove2.me/submissions/f7f7763f-5bc7-4da3-8b6b-e4ed6cdf6aca

import Definitions.Def_MarkovProcess_V3H_Kernel_Operator_8b41d3bf
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Theorems.Thm_MarkovProcess_perturbed_unique
import Theorems.Thm_MarkovProcess_resolventFamily_eq_of_eventually

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Uniqueness for resolvents on bounded measurable functions

This file proves three elementary contraction principles for maps acting on bounded measurable
real functions. The first gives uniqueness for a bounded multiplicative perturbation equation.
The second propagates equality of two resolvent families from all sufficiently large shifts to
every positive shift by the resolvent identity. The third combines the first two principles.

Main results: `perturbed_unique`, `resolventFamily_eq_of_eventually`, and
`perturbed_eq_of_resolventFamilies`.

The operators are plain maps on functions; no Banach-space carrier or continuity is asserted.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter

namespace MarkovProcess

noncomputable section



variable {alpha : Type*} [MeasurableSpace alpha] [Nonempty alpha]







end

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Uniqueness for resolvents on bounded measurable functions

This file proves three elementary contraction principles for maps acting on bounded measurable
real functions. The first gives uniqueness for a bounded multiplicative perturbation equation.
The second propagates equality of two resolvent families from all sufficiently large shifts to
every positive shift by the resolvent identity. The third combines the first two principles.

Main results: `perturbed_unique`, `resolventFamily_eq_of_eventually`, and
`perturbed_eq_of_resolventFamilies`.

The operators are plain maps on functions; no Banach-space carrier or continuity is asserted.
-/

open Filter





variable {alpha : Type*} [MeasurableSpace alpha] [Nonempty alpha]





namespace MarkovProcess

end MarkovProcess
open MarkovProcess
theorem solution
    (R X Y : ℝ → (alpha → ℝ) → alpha → ℝ) {q : alpha → ℝ} {C : ℝ}
    (hR_add : ∀ {lam : ℝ}, C < lam → 0 < lam → ∀ {f g : alpha → ℝ},
      Measurable f → Measurable g → (∃ D, ∀ x, |f x| ≤ D) →
      (∃ D, ∀ x, |g x| ≤ D) → R lam (f + g) = R lam f + R lam g)
    (hR_bound : ∀ {lam : ℝ}, C < lam → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → ∀ {D : ℝ}, (∀ x, |f x| ≤ D) →
      ∀ x, |R lam f x| ≤ D / lam)
    (hq : Measurable q) (hq0 : ∀ x, 0 ≤ q x) (hqC : ∀ x, q x ≤ C)
    (hX_add : ∀ {lam : ℝ}, 0 < lam → ∀ {f g : alpha → ℝ},
      Measurable f → Measurable g → (∃ D, ∀ x, |f x| ≤ D) →
      (∃ D, ∀ x, |g x| ≤ D) → X lam (f + g) = X lam f + X lam g)
    (hX_meas : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → Measurable (X lam f))
    (hY_meas : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → Measurable (Y lam f))
    (hX_bound : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      ∀ {D : ℝ}, (∀ x, |f x| ≤ D) → ∀ x, |X lam f x| ≤ D / lam)
    (hY_bound : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → ∃ D, ∀ x, |Y lam f x| ≤ D)
    (hX_resolvent : ∀ {mu lam : ℝ}, 0 < mu → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      X mu f = X lam f + (lam - mu) • X lam (X mu f))
    (hY_resolvent : ∀ {mu lam : ℝ}, 0 < mu → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Y mu f = Y lam f + (lam - mu) • Y lam (Y mu f))
    (hX_fixed : ∀ {lam : ℝ}, C < lam → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      X lam f = R lam f - R lam (fun x ↦ q x * X lam f x))
    (hY_fixed : ∀ {lam : ℝ}, C < lam → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Y lam f = R lam f - R lam (fun x ↦ q x * Y lam f x))
    {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ} (hf : Measurable f)
    {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    X lam f = Y lam f := by
  apply resolventFamily_eq_of_eventually X Y C hX_add hX_meas hY_meas
    hX_bound hY_bound hX_resolvent hY_resolvent _ hlam hf hfD
  intro mu hCmu hmu g hg hgb
  obtain ⟨E, hgE⟩ := hgb
  exact perturbed_unique (R mu) (X mu) (Y mu) (hR_add hCmu hmu)
    (hR_bound hCmu hmu) hq hq0 hqC hCmu (hX_meas hmu) (hY_meas hmu)
    (fun hf' hf'b ↦ by
      obtain ⟨E', hfE'⟩ := hf'b
      exact ⟨E' / mu, hX_bound hmu hf' hfE'⟩)
    (hY_bound hmu)
    (hX_fixed hCmu hmu) (hY_fixed hCmu hmu) hg hgE
