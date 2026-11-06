-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.sixth_power_rows_within_norm_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:47:35.878212+00:00
-- url     : https://prove2.me/submissions/f58decfd-c78c-48e8-ba47-a5ccf06e4c46

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Theorems.Thm_OAI_ActualEisensteinCubic_principal_absNorm_pow

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    {β : Type*} (selected : Finset β) (p : β → O) (rows : Finset O)
    (D : ℕ) (hD : 1 ≤ D)
    (hupper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (D : ℝ) ^ (11 / 60 : ℝ))
    (hcover : ∀ u : O,
      (Ideal.absNorm (Ideal.span {u}) : ℝ) ≤
        (D : ℝ) ^ (11 / 10 : ℝ) → u ∈ rows) :
    selected.image (fun i => p i ^ 6) ⊆ rows := by
  classical
  intro u hu
  rcases Finset.mem_image.mp hu with ⟨i, hi, rfl⟩
  apply hcover
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  calc
    (Ideal.absNorm (Ideal.span {p i ^ 6}) : ℝ) =
        (Ideal.absNorm (Ideal.span {p i}) : ℝ) ^ 6 := by
          exact_mod_cast principal_absNorm_pow (p i) 6
    _ ≤ ((D : ℝ) ^ (11 / 60 : ℝ)) ^ 6 := by
          gcongr
          exact hupper i hi
    _ = (D : ℝ) ^ (11 / 10 : ℝ) := by
          rw [← Real.rpow_mul_natCast hDpos.le (11 / 60 : ℝ) 6]
          congr 1
          norm_num
end OAI.ActualEisensteinCubic
