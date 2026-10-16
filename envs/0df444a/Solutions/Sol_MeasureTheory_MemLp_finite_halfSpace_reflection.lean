-- Prove2me | solution 1 for MeasureTheory.MemLp.finite_halfSpace_reflection
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T09:38:03.831998+00:00
-- url     : https://prove2.me/submissions/47013d91-a21d-4d70-9b5d-fd034444c9c1

import Theorems.Thm_MeasureTheory_MemLp_comp_continuousLinearEquiv_volume
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.Analysis.Normed.Module.FiniteDimension

open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem solution {n N : ℕ} (i : Fin n) (p : ℝ≥0∞)
    (b c : Fin N → ℝ) (hb : ∀ j, 0 < b j)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : MemLp f p (volume.restrict {x | 0 < x i})) :
    MemLp (fun x => if 0 < x i then f x else
      ∑ j : Fin N, c j * f (WithLp.toLp 2
        (Function.update (fun l => x l) i (-b j * x i)))) p volume := by
  classical
  let H : Set (EuclideanSpace ℝ (Fin n)) := {x | 0 < x i}
  have hH : MeasurableSet H :=
    (isOpen_lt continuous_const (EuclideanSpace.proj i).continuous).measurableSet
  let F := H.indicator f
  have hF : MemLp F p volume := (memLp_indicator_iff_restrict hH).2 hf
  let e (j : Fin N) : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).trans
      ((LinearEquiv.piCongrRight fun l : Fin n =>
        LinearEquiv.smulOfNeZero ℝ ℝ (if l = i then -b j else 1)
          (by split_ifs <;> simp [ne_of_gt (hb j)] )).trans
        (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm)).toContinuousLinearEquiv
  have he (j : Fin N) (x : EuclideanSpace ℝ (Fin n)) :
      e j x = WithLp.toLp 2 (Function.update (fun l => x l) i (-b j * x i)) := by
    ext l
    by_cases hl : l = i <;>
      simp [e, LinearEquiv.piCongrRight_apply, LinearEquiv.smulOfNeZero, LinearEquiv.smulOfUnit, hl]
  have hcopies (j : Fin N) : MemLp (fun x => c j * F (e j x)) p volume :=
    (MeasureTheory.MemLp.comp_continuousLinearEquiv_volume (e j) p F hF).const_mul (c j)
  have hsum : MemLp (fun x => ∑ j : Fin N, c j * F (e j x)) p volume :=
    memLp_finsetSum _ (fun j _ => hcopies j)
  have hpiece := (hF.restrict H).piecewise hH (hsum.restrict Hᶜ)
  let L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ := (EuclideanSpace.proj i).toLinearMap
  have hker : L.ker ≠ ⊤ := by
    intro h
    have : EuclideanSpace.single i (1 : ℝ) ∈ L.ker := by rw [h]; trivial
    simpa [L, LinearMap.mem_ker] using this
  have hnull : volume {x : EuclideanSpace ℝ (Fin n) | x i = 0} = 0 :=
    Measure.addHaar_submodule volume L.ker hker
  have hae : ∀ᵐ x : EuclideanSpace ℝ (Fin n) ∂volume, x i ≠ 0 := by
    simpa only [ae_iff, not_not] using hnull
  apply hpiece.ae_eq
  filter_upwards [hae] with x hx
  by_cases hpos : 0 < x i
  · simp [H, F, hpos]
  · have hneg : x i < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hx
    have hmem (j : Fin N) : e j x ∈ H := by
      simpa [H, he] using mul_pos_of_neg_of_neg (neg_neg_of_pos (hb j)) hneg
    simp only [Set.piecewise, H, Set.mem_setOf_eq, hpos, ↓reduceIte]
    apply Finset.sum_congr rfl
    intro j _
    rw [show F (e j x) = f (e j x) from Set.indicator_of_mem (hmem j) f, he]
