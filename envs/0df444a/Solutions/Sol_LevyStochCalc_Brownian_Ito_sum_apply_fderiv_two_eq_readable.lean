-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.sum_apply_fderiv_two_eq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:18:24.066926+00:00
-- url     : https://prove2.me/submissions/5b5413d9-5126-44a3-ae75-4851ce0a7506

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_CoordDerivative
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoFormulaDecomp

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/CoordDerivative.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open ContinuousLinearMap
variable {n : ℕ}
section Expansion
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- A continuous linear map on `Fin n → ℝ` is the sum of its values on the standard basis,
weighted by the coordinates. -/
theorem LevyStochCalc.clm_apply_pi (L : (Fin n → ℝ) →L[ℝ] F) (v : Fin n → ℝ) :
    L v = ∑ p, v p • L (Pi.single p 1) := by
  have hsingle : ∀ p : Fin n, (Pi.single p (v p) : Fin n → ℝ) = v p • Pi.single p (1 : ℝ) := by
    intro p
    rw [← Pi.single_smul']
    simp
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  exact Finset.sum_congr rfl fun p _ => by rw [hsingle p, map_smul]
/-- The scalar form of `clm_apply_pi`. -/
theorem LevyStochCalc.clm_apply_pi_real (L : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) :
    L v = ∑ p, v p * L (Pi.single p 1) := by
  simpa [smul_eq_mul] using clm_apply_pi L v
end Expansion
section Coord
variable {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
/-- The second-order term of a Taylor expansion in coordinates. -/
theorem LevyStochCalc.apply₂_eq_sum_coordDeriv₂ (x v : Fin n → ℝ) :
    f'' x v v = ∑ p, ∑ q, v p * v q * coordDeriv₂ f'' p q x := by
  have houter : f'' x v = ∑ p, v p • f'' x (Pi.single p 1) := clm_apply_pi (f'' x) v
  rw [houter, _root_.sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [_root_.smul_apply, smul_eq_mul, clm_apply_pi_real (f'' x (Pi.single p 1)) v,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by rw [coordDeriv₂]; ring
end Coord
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoFormulaDecomp.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
section Reindex
variable {n d : ℕ}
/-- Reordering a triple sum over two state indices and the grid. -/
theorem LevyStochCalc.Brownian.Ito.sum_range_sum_sum_comm (m : ℕ) (E : Fin n → Fin n → ℕ → ℝ) :
    ∑ i ∈ Finset.range m, ∑ p : Fin n, ∑ q : Fin n, E p q i
      = ∑ p : Fin n, ∑ q : Fin n, ∑ i ∈ Finset.range m, E p q i := by
  calc ∑ i ∈ Finset.range m, ∑ p : Fin n, ∑ q : Fin n, E p q i
      = ∑ p : Fin n, ∑ i ∈ Finset.range m, ∑ q : Fin n, E p q i := Finset.sum_comm
    _ = ∑ p : Fin n, ∑ q : Fin n, ∑ i ∈ Finset.range m, E p q i :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
end Reindex
section TaylorSums
variable {n : ℕ}
/-- The second-order Taylor sum along a sequence, in coordinates. -/
theorem solution (f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ)
    (Y : ℕ → Fin n → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range m, f'' (Y i) (Y (i + 1) - Y i) (Y (i + 1) - Y i) / 2
      = 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∑ i ∈ Finset.range m,
          LevyStochCalc.coordDeriv₂ f'' p q (Y i) * ((Y (i + 1) p - Y i p) * (Y (i + 1) q - Y i q)) := by
  have hstep : ∀ i ∈ Finset.range m,
      f'' (Y i) (Y (i + 1) - Y i) (Y (i + 1) - Y i) / 2
        = (∑ p : Fin n, ∑ q : Fin n,
            LevyStochCalc.coordDeriv₂ f'' p q (Y i)
              * ((Y (i + 1) p - Y i p) * (Y (i + 1) q - Y i q))) / 2 := by
    intro i _
    rw [LevyStochCalc.apply₂_eq_sum_coordDeriv₂]
    congr 1
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    simp only [Pi.sub_apply]
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_div,
    LevyStochCalc.Brownian.Ito.sum_range_sum_sum_comm m fun p q i =>
      LevyStochCalc.coordDeriv₂ f'' p q (Y i) * ((Y (i + 1) p - Y i p) * (Y (i + 1) q - Y i q))]
  ring
