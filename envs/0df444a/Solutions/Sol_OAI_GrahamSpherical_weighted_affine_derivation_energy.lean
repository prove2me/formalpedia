-- Prove2me | solution 1 for OAI.GrahamSpherical.weighted_affine_derivation_energy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T10:15:14.374849+00:00
-- url     : https://prove2.me/submissions/c8d48e6e-c9e8-40da-9011-bb50a790fba8

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SphericalRamsey/EnergyIdentity.lean:L40-L59
-- (upload_full_project.md Phase 4): solution for node OAI.GrahamSpherical.weighted_affine_derivation_energy. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_GrahamSpherical
import Definitions.Def_OAI_Combinatorics_SphericalRamsey_Model
import Theorems.Thm_OAI_GrahamSpherical_derivation_rotation_coordinates

-- ---- from OAI.Combinatorics.SphericalRamsey.EnergyIdentity ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace GrahamSpherical

theorem rotation_norm_sq : u ^ 2 + v ^ 2 = 1 := by
  have hden : (1 + parameter ^ 2 : ℝ) ≠ 0 := by positivity
  unfold u v
  field_simp [hden]
  ring

theorem derivation_u_v (D : Derivation ℤ ℝ ℝ)
    (hD : D parameter = (1 + parameter ^ 2) / 2) :
    D u = -v ∧ D v = u :=
  derivation_rotation_coordinates D parameter hD

/-- The translation and orientation-derivative coefficients are arbitrary. -/
theorem weighted_coordinate_square (D : Derivation ℤ ℝ ℝ)
    (hD : D parameter = (1 + parameter ^ 2) / 2)
    (p a b c d : ℝ) :
    ∑ i : Label, (weight i : ℝ) *
      (p + a * coordinates i 0 + b * coordinates i 1 +
        c * D (coordinates i 0) + d * D (coordinates i 1)) ^ 2 =
        4 * (c ^ 2 + d ^ 2) := by
  obtain ⟨hu, hv⟩ := derivation_u_v D hD
  calc
    _ = 4 * (u ^ 2 + v ^ 2) * (c ^ 2 + d ^ 2) +
        4 * (u ^ 2 + v ^ 2 - 1) * (a ^ 2 + b ^ 2) := by
      simp [Fintype.sum_prod_type, Fin.sum_univ_succ, coordinates,
        squareCoordinate, weight, map_neg, hu, hv]
      ring
    _ = _ := by rw [rotation_norm_sq]; ring

/-- Weighted derivative energy for an actual affine placement.  The mixed
orthogonality condition is not needed after the exact moment cancellation. -/
theorem weighted_affine_derivation_energy {n : ℕ}
    (D : Derivation ℤ ℝ ℝ)
    (hD : D parameter = (1 + parameter ^ 2) / 2)
    (z A B : Fin n → ℝ)
    (hA : ∑ j, A j ^ 2 = 1) (hB : ∑ j, B j ^ 2 = 1) :
    ∑ i : Label, (weight i : ℝ) * ∑ j : Fin n,
      (D (z j + coordinates i 0 * A j + coordinates i 1 * B j)) ^ 2 = 8 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have he (i : Label) (j : Fin n) :
      D (z j + coordinates i 0 * A j + coordinates i 1 * B j) =
      D (z j) + D (A j) * coordinates i 0 + D (B j) * coordinates i 1 +
        A j * D (coordinates i 0) + B j * D (coordinates i 1) := by
    simp only [map_add, Derivation.leibniz, smul_eq_mul]
    ring
  simp_rw [he, weighted_coordinate_square D hD]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, hA, hB]
  norm_num

end GrahamSpherical

end

end OAI

-- ---- platform node ----
open OAI OAI.GrahamSpherical
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.GrahamSpherical.weighted_affine_derivation_energy := @_root_.OAI.GrahamSpherical.weighted_affine_derivation_energy
