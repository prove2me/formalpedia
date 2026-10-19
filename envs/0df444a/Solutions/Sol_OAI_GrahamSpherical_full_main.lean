-- Prove2me | solution 1 for OAI.GrahamSpherical.full_main
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-17T00:38:52.471358+00:00
-- url     : https://prove2.me/submissions/ca1002af-8448-4662-bc15-824edb42bace

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.BigOperators
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

set_option backward.isDefEq.respectTransparency.types false


-- ===== from OAI/Combinatorics/SphericalRamsey/Model.lean =====
-- omitted (Definitions.Def_GrahamSpherical supplies these): AvoidsCopy, EuclideanRamsey, FullAuthoredResult, Label, Point, coordinates, parameter, squareCoordinate, u, v, vertex, witness
namespace OAI

/-!
The explicit twelve-point witness and the ordinary Euclidean Ramsey property.
These definitions contain no proof-specific field derivation or affine-placement assumption.
-/
noncomputable section
namespace GrahamSpherical
def weight (i : Label) : ℤ := if i.1 = 2 then -2 else 1
end GrahamSpherical
end

/-! Independent statement of the full authored result. -/
namespace GrahamSpherical.Specification
end GrahamSpherical.Specification
end OAI

-- ===== from OAI/Combinatorics/SphericalRamsey/Specification.lean =====

-- ===== from OAI/Combinatorics/SphericalRamsey/Ramsey.lean =====
namespace OAI
namespace GrahamSpherical

/-- Fixed fifty-color avoidance in every positive dimension contradicts the
ordinary Ramsey quantifier, without assuming any copy exists. -/
theorem not_euclideanRamsey_of_fifty_colorings
    (havoid : ∀ n : ℕ, 0 < n →
      ∃ color : Point n → Fin 50, AvoidsCopy witness color) :
    ¬ EuclideanRamsey witness := by
  intro hRamsey
  obtain ⟨n, hn, hall⟩ := hRamsey 50 (by decide)
  obtain ⟨color, hc⟩ := havoid n hn
  exact hc (hall color)

/-- The geometric and coloring properties jointly imply the spherical
non-Ramsey conclusion. -/
theorem assemble_full_result
    (hcard : witness.ncard = 12)
    (hsphere : witness ⊆ Metric.sphere (0 : Point 2) 1)
    (havoid : ∀ n : ℕ, 0 < n →
      ∃ color : Point n → Fin 50, AvoidsCopy witness color) :
    Specification.FullAuthoredResult :=
  ⟨hcard, hsphere, havoid, not_euclideanRamsey_of_fifty_colorings havoid⟩
end GrahamSpherical
end OAI

-- ===== from OAI/Combinatorics/SphericalRamsey/Coloring.lean =====
namespace OAI
noncomputable section
open scoped BigOperators
namespace GrahamSpherical

/-- The actual fifty-residue rounding obstruction. No nonnegativity or
geometric surrogate is required of the twelve input energies. -/
theorem rounding_obstruction (e : (Fin 3 × Fin 4) → ℝ)
    (henergy : ∑ i, (if i.1 = 2 then (-2 : ℝ) else 1) * e i = 8) :
    ∃ i j, (Int.floor (3 * e i)) % 50 ≠ (Int.floor (3 * e j)) % 50 := by
  classical
  by_contra h
  push Not at h
  let f : (Fin 3 × Fin 4) → ℤ := fun i => Int.floor (3 * e i)
  have hr (i : Fin 3 × Fin 4) : f i % 50 = f (0, 0) % 50 := h i (0, 0)
  have heq (i : Fin 3 × Fin 4) : f i = 50 * (f i / 50) + f (0, 0) % 50 := by
    have hi := Int.emod_add_mul_ediv (f i) 50
    rw [hr i] at hi
    omega
  let S : ℤ := f (0, 0) + f (0, 1) + f (0, 2) + f (0, 3) + f (1, 0) + f (1, 1) + f (1, 2) + f (1, 3) - 2 * (f (2, 0) + f (2, 1) + f (2, 2) + f (2, 3))
  let q : (Fin 3 × Fin 4) → ℤ := fun i => f i / 50
  let Q : ℤ := q (0, 0) + q (0, 1) + q (0, 2) + q (0, 3) + q (1, 0) + q (1, 1) + q (1, 2) + q (1, 3) - 2 * (q (2, 0) + q (2, 1) + q (2, 2) + q (2, 3))
  have hdiv : S = 50 * Q := by
    conv_lhs =>
      dsimp [S]
      rw [heq (0, 0), heq (0, 1), heq (0, 2), heq (0, 3), heq (1, 0), heq (1, 1), heq (1, 2), heq (1, 3), heq (2, 0), heq (2, 1), heq (2, 2), heq (2, 3)]
    dsimp [Q, q]
    ring
  have henergy' : e (0, 0) + (e (0, 1) + (e (0, 2) + e (0, 3))) +
      (e (1, 0) + (e (1, 1) + (e (1, 2) + e (1, 3))) +
        (-(2 * e (2, 0)) + (-(2 * e (2, 1)) + (-(2 * e (2, 2)) + -(2 * e (2, 3)))))) = 8 := by
    simpa [Fintype.sum_prod_type, Fin.sum_univ_succ, Fin.ext_iff] using henergy
  have hl00 : (f (0, 0) : ℝ) ≤ 3 * e (0, 0) := Int.floor_le _
  have hu00 : 3 * e (0, 0) < (f (0, 0) : ℝ) + 1 := Int.lt_floor_add_one _
  have hl01 : (f (0, 1) : ℝ) ≤ 3 * e (0, 1) := Int.floor_le _
  have hu01 : 3 * e (0, 1) < (f (0, 1) : ℝ) + 1 := Int.lt_floor_add_one _
  have hl02 : (f (0, 2) : ℝ) ≤ 3 * e (0, 2) := Int.floor_le _
  have hu02 : 3 * e (0, 2) < (f (0, 2) : ℝ) + 1 := Int.lt_floor_add_one _
  have hl03 : (f (0, 3) : ℝ) ≤ 3 * e (0, 3) := Int.floor_le _
  have hu03 : 3 * e (0, 3) < (f (0, 3) : ℝ) + 1 := Int.lt_floor_add_one _
  have hl10 : (f (1, 0) : ℝ) ≤ 3 * e (1, 0) := Int.floor_le _
  have hu10 : 3 * e (1, 0) < (f (1, 0) : ℝ) + 1 := Int.lt_floor_add_one _
  have hl11 : (f (1, 1) : ℝ) ≤ 3 * e (1, 1) := Int.floor_le _
  have hu11 : 3 * e (1, 1) < (f (1, 1) : ℝ) + 1 := Int.lt_floor_add_one _
  have hl12 : (f (1, 2) : ℝ) ≤ 3 * e (1, 2) := Int.floor_le _
  have hu12 : 3 * e (1, 2) < (f (1, 2) : ℝ) + 1 := Int.lt_floor_add_one _
  have hl13 : (f (1, 3) : ℝ) ≤ 3 * e (1, 3) := Int.floor_le _
  have hu13 : 3 * e (1, 3) < (f (1, 3) : ℝ) + 1 := Int.lt_floor_add_one _
  have hl20 : (f (2, 0) : ℝ) ≤ 3 * e (2, 0) := Int.floor_le _
  have hu20 : 3 * e (2, 0) < (f (2, 0) : ℝ) + 1 := Int.lt_floor_add_one _
  have hl21 : (f (2, 1) : ℝ) ≤ 3 * e (2, 1) := Int.floor_le _
  have hu21 : 3 * e (2, 1) < (f (2, 1) : ℝ) + 1 := Int.lt_floor_add_one _
  have hl22 : (f (2, 2) : ℝ) ≤ 3 * e (2, 2) := Int.floor_le _
  have hu22 : 3 * e (2, 2) < (f (2, 2) : ℝ) + 1 := Int.lt_floor_add_one _
  have hl23 : (f (2, 3) : ℝ) ≤ 3 * e (2, 3) := Int.floor_le _
  have hu23 : 3 * e (2, 3) < (f (2, 3) : ℝ) + 1 := Int.lt_floor_add_one _
  have hSl : (16 : ℝ) < (S : ℝ) := by
    dsimp [S]
    push_cast
    linarith
  have hSu : (S : ℝ) < (32 : ℝ) := by
    dsimp [S]
    push_cast
    linarith
  have hSl' : (16 : ℤ) < S := by exact_mod_cast hSl
  have hSu' : S < (32 : ℤ) := by exact_mod_cast hSu
  omega
end GrahamSpherical
end
end OAI

-- ===== from OAI/Combinatorics/SphericalRamsey/DerivationCoordinates.lean =====
namespace OAI
namespace GrahamSpherical

/-- Only the algebraic quotient rule is used; no continuity or differentiation
of the infinite series defining the parameter is involved. -/
theorem derivation_rotation_coordinates (D : Derivation ℤ ℝ ℝ) (t : ℝ)
    (ht : D t = (1 + t ^ 2) / 2) :
    D ((1 - t ^ 2) / (1 + t ^ 2)) = -(2 * t / (1 + t ^ 2)) ∧
      D (2 * t / (1 + t ^ 2)) = (1 - t ^ 2) / (1 + t ^ 2) := by
  have hden : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
  have htwo : D (2 : ℝ) = 0 := D.map_natCast 2
  have hpow : D (t ^ 2) = 2 * t * D t := by
    simp [Derivation.leibniz_pow, smul_eq_mul, two_smul]
    ring
  constructor
  · rw [D.leibniz_div, map_sub, map_add, D.map_one_eq_zero, hpow, ht]
    simp only [smul_eq_mul]
    field_simp [hden]
    ring
  · rw [D.leibniz_div, D.leibniz, map_add, D.map_one_eq_zero, htwo, hpow, ht]
    simp only [smul_eq_mul]
    field_simp [hden]
    ring
end GrahamSpherical
end OAI

-- ===== from OAI/Combinatorics/SphericalRamsey/EnergyIdentity.lean =====
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

-- ===== from OAI/Combinatorics/SphericalRamsey/MonochromaticObstruction.lean =====
namespace OAI
noncomputable section
open scoped BigOperators
namespace GrahamSpherical

/-- The actual finite squared Euclidean energy of the entrywise derivation. -/
def derivationEnergy {n : ℕ} (D : Derivation ℤ ℝ ℝ) (y : Point n) : ℝ :=
  ∑ j : Fin n, (D (y j)) ^ 2

/-- Native integer floor and Euclidean remainder, reindexed into Fin 50. -/
def energyColor {n : ℕ} (e : Point n → ℝ) (y : Point n) : Fin 50 :=
  ⟨((Int.floor (3 * e y)) % 50).toNat, by
    have h0 := Int.emod_nonneg (Int.floor (3 * e y)) (by norm_num : (50 : ℤ) ≠ 0)
    have hlt := Int.emod_lt_of_pos (Int.floor (3 * e y)) (by norm_num : (0 : ℤ) < 50)
    omega⟩
theorem energyColor_eq_implies_residue_eq {n : ℕ} (e : Point n → ℝ)
    (x y : Point n) (h : energyColor e x = energyColor e y) :
    (Int.floor (3 * e x)) % 50 = (Int.floor (3 * e y)) % 50 := by
  have he := congrArg Fin.val h
  change ((Int.floor (3 * e x)) % 50).toNat =
    ((Int.floor (3 * e y)) % 50).toNat at he
  have hx := Int.emod_nonneg (Int.floor (3 * e x)) (by norm_num : (50 : ℤ) ≠ 0)
  have hy := Int.emod_nonneg (Int.floor (3 * e y)) (by norm_num : (50 : ℤ) ≠ 0)
  omega

/-- Every copy here is an actual isometry of the literal witness subtype.
The energy identity is an explicit intermediate premise, discharged separately. -/
theorem energyColor_avoids_of_invariant {n : ℕ} (e : Point n → ℝ)
    (hinvariant : ∀ (f : witness → Point n), Isometry f →
      ∑ i : Label, (weight i : ℝ) * e (f ⟨vertex i, ⟨i, rfl⟩⟩) = 8) :
    AvoidsCopy witness (energyColor e) := by
  rintro ⟨f, hf, c, hc⟩
  have hi := hinvariant f hf
  obtain ⟨i, j, hij⟩ := rounding_obstruction
    (fun i : Label => e (f ⟨vertex i, ⟨i, rfl⟩⟩)) (by
      simpa [weight] using hi)
  apply hij
  apply energyColor_eq_implies_residue_eq e
  exact (hc ⟨vertex i, ⟨i, rfl⟩⟩).trans (hc ⟨vertex j, ⟨j, rfl⟩⟩).symm
end GrahamSpherical
end
end OAI

-- ===== from OAI/Combinatorics/SphericalRamsey/AffineCopyCore.lean =====
namespace OAI
noncomputable section
open scoped RealInnerProductSpace
namespace GrahamSpherical

/-- Polarization in the actual real Euclidean inner product. -/
lemma inner_sub_self (n : ℕ) (x y : Point n) :
    (inner ℝ (x-y) (x-y)) = (inner ℝ (x) (x)) - 2*(inner ℝ (x) (y)) + (inner ℝ (y) (y)) := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm y x]
  ring

/-- An orthonormal pair reconstructs a vector once its two coordinates account
for its full squared norm. No dimension assumption is imposed on the codomain. -/
lemma vector_eq_of_orthonormal_coordinates {n : ℕ} (A B z : Point n) (a b : ℝ)
    (hAA : (inner ℝ (A) (A)) = 1) (hBB : (inner ℝ (B) (B)) = 1) (hAB : (inner ℝ (A) (B)) = 0)
    (hzA : (inner ℝ (z) (A)) = a) (hzB : (inner ℝ (z) (B)) = b)
    (hzz : (inner ℝ (z) (z)) = a^2+b^2) : z = a • A + b • B := by
  have hBA : (inner ℝ (B) (A)) = 0 := (real_inner_comm A B).trans hAB
  have hAz : (inner ℝ (A) (z)) = a := (real_inner_comm z A).trans hzA
  have hBz : (inner ℝ (B) (z)) = b := (real_inner_comm z B).trans hzB
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hAA, hBB, hAB, hBA,
    hzA, hzB, hAz, hBz, hzz]
  ring

/-- The three-anchor Gram data determine a common affine Euclidean frame. -/
lemma affine_frame_of_anchor_gram {ι : Type*} {n : ℕ}
    (y : ι → Point n) (a b : ι → ℝ) (p : Point n) (d e : Point n)
    (hdd : (inner ℝ (d) (d)) = 4) (hee : (inner ℝ (e) (e)) = 2) (hde : (inner ℝ (d) (e)) = 2)
    (hzz : ∀ i, (inner ℝ (y i-p) (y i-p)) = (a i-1)^2+(b i)^2)
    (hzd : ∀ i, (inner ℝ (y i-p) (d)) = 2*(1-a i))
    (hze : ∀ i, (inner ℝ (y i-p) (e)) = 1-a i+b i) :
    ∃ c A B : Point n, (inner ℝ (A) (A)) = 1 ∧ (inner ℝ (B) (B)) = 1 ∧
      (inner ℝ (A) (B)) = 0 ∧ ∀ i, y i = c + a i • A + b i • B := by
  let A : Point n := (-1/2 : ℝ) • d
  let B : Point n := e - (1/2 : ℝ) • d
  let c : Point n := p + (1/2 : ℝ) • d
  have hed : (inner ℝ (e) (d)) = 2 := (real_inner_comm d e).trans hde
  have hAA : (inner ℝ (A) (A)) = 1 := by
    dsimp [A]
    simp only [real_inner_smul_left, real_inner_smul_right, hdd]
    norm_num
  have hBB : (inner ℝ (B) (B)) = 1 := by
    dsimp [B]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hdd, hee, hde, hed]
    norm_num
  have hAB : (inner ℝ (A) (B)) = 0 := by
    dsimp [A,B]
    simp only [inner_sub_right, real_inner_smul_left, real_inner_smul_right, hdd, hde]
    norm_num
  refine ⟨c,A,B,hAA,hBB,hAB,?_⟩
  intro i
  have hzA : (inner ℝ (y i-p) (A)) = a i-1 := by
    dsimp [A]
    rw [real_inner_smul_right, hzd]
    ring
  have hzB : (inner ℝ (y i-p) (B)) = b i := by
    dsimp [B]
    rw [inner_sub_right, real_inner_smul_right, hze, hzd]
    ring
  have hv := vector_eq_of_orthonormal_coordinates A B (y i-p) (a i-1) (b i)
    hAA hBB hAB hzA hzB (hzz i)
  calc
    y i = p + (y i-p) := by abel
    _ = p + ((a i-1) • A + b i • B) := by rw [hv]
    _ = c + a i • A + b i • B := by dsimp [c,A]; module
end GrahamSpherical
end
end OAI

-- ===== from OAI/Combinatorics/SphericalRamsey/AffineCopy.lean =====
namespace OAI
noncomputable section
open scoped RealInnerProductSpace BigOperators
namespace GrahamSpherical
lemma dist_vertex_sq (i j : Label) :
    dist (vertex i) (vertex j) ^ 2 =
      (coordinates i 0-coordinates j 0)^2 + (coordinates i 1-coordinates j 1)^2 := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  simp [vertex, Fin.sum_univ_two]
lemma inner_sub_self_eq_dist_sq {n : ℕ} (x y : Point n) :
    (inner ℝ (x-y) (x-y)) = dist x y ^ 2 := by
  rw [real_inner_self_eq_norm_sq, dist_eq_norm]

/-- Every literal distance-preserving placement of the twelve points has one
common affine expression with an orthonormal pair. No affine hypothesis or
ambient-dimension lower bound is assumed. -/
theorem affine_copy {n : ℕ} (y : Label → Point n)
    (hy : ∀ i j, dist (y i) (y j) = dist (vertex i) (vertex j)) :
    ∃ c A B : Point n, (inner ℝ (A) (A)) = 1 ∧ (inner ℝ (B) (B)) = 1 ∧
      (inner ℝ (A) (B)) = 0 ∧ ∀ i, y i = c + coordinates i 0 • A + coordinates i 1 • B := by
  let p : Label := (2,0)
  let m : Label := (2,1)
  let q : Label := (2,2)
  have hp0 : coordinates p 0 = 1 := by norm_num [p, coordinates, squareCoordinate, Fin.ext_iff]
  have hp1 : coordinates p 1 = 0 := by norm_num [p, coordinates, squareCoordinate, Fin.ext_iff]
  have hm0 : coordinates m 0 = -1 := by norm_num [m, coordinates, squareCoordinate, Fin.ext_iff]
  have hm1 : coordinates m 1 = 0 := by norm_num [m, coordinates, squareCoordinate, Fin.ext_iff]
  have hq0 : coordinates q 0 = 0 := by norm_num [q, coordinates, squareCoordinate, Fin.ext_iff]
  have hq1 : coordinates q 1 = 1 := by norm_num [q, coordinates, squareCoordinate, Fin.ext_iff]
  have hd (i j : Label) : (inner ℝ (y i-y j) (y i-y j)) =
      (coordinates i 0-coordinates j 0)^2 + (coordinates i 1-coordinates j 1)^2 := by
    rw [inner_sub_self_eq_dist_sq, hy, dist_vertex_sq]
  have hdd : (inner ℝ (y m-y p) (y m-y p)) = 4 := by
    rw [hd, hm0, hm1, hp0, hp1]; norm_num
  have hee : (inner ℝ (y q-y p) (y q-y p)) = 2 := by
    rw [hd, hq0, hq1, hp0, hp1]; norm_num
  have hde : (inner ℝ (y m-y p) (y q-y p)) = 2 := by
    have h := hd m q
    rw [hm0, hm1, hq0, hq1] at h
    have he : (y m-y p)-(y q-y p) = y m-y q := by abel
    have hh := inner_sub_self n (y m-y p) (y q-y p)
    rw [he, h, hdd, hee] at hh
    nlinarith
  apply affine_frame_of_anchor_gram y (fun i => coordinates i 0)
    (fun i => coordinates i 1) (y p) (y m-y p) (y q-y p) hdd hee hde
  · intro i
    simpa only [hp0, hp1, sub_zero] using hd i p
  · intro i
    have h := hd i m
    rw [hm0, hm1, sub_zero] at h
    have hz := hd i p
    rw [hp0, hp1, sub_zero] at hz
    have he : (y i-y p)-(y m-y p) = y i-y m := by abel
    have hh := inner_sub_self n (y i-y p) (y m-y p)
    rw [he, h, hz, hdd] at hh
    nlinarith
  · intro i
    have h := hd i q
    rw [hq0, hq1, sub_zero] at h
    have hz := hd i p
    rw [hp0, hp1, sub_zero] at hz
    have he : (y i-y p)-(y q-y p) = y i-y q := by abel
    have hh := inner_sub_self n (y i-y p) (y q-y p)
    rw [he, h, hz, hee] at hh
    nlinarith

/-- Coordinate-square normalization for the derivative-energy calculation. -/
lemma sum_sq_eq_inner {n : ℕ} (A : Point n) :
    (∑ j : Fin n, A j ^ 2) = (inner ℝ (A) (A)) := by
  rw [real_inner_self_eq_norm_sq, EuclideanSpace.real_norm_sq_eq]
end GrahamSpherical
end
end OAI

-- ===== from OAI/Combinatorics/SphericalRamsey/CopyInvariant.lean =====
namespace OAI
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace GrahamSpherical

/-- All distance-preserving copies, with no affine-form or dimension premise. -/
theorem weighted_copy_derivation_energy {n : ℕ}
    (D : Derivation ℤ ℝ ℝ)
    (hD : D parameter = (1 + parameter ^ 2) / 2)
    (f : witness → Point n) (hf : Isometry f) :
    ∑ i : Label, (weight i : ℝ) *
      derivationEnergy D (f ⟨vertex i, ⟨i, rfl⟩⟩) = 8 := by
  let y : Label → Point n := fun i => f ⟨vertex i, ⟨i, rfl⟩⟩
  have hy : ∀ i j, dist (y i) (y j) = dist (vertex i) (vertex j) := by
    intro i j
    exact hf.dist_eq ⟨vertex i, ⟨i, rfl⟩⟩ ⟨vertex j, ⟨j, rfl⟩⟩
  obtain ⟨z, A, B, hA, hB, _hAB, hform⟩ := affine_copy y hy
  have hAs : ∑ j : Fin n, A j ^ 2 = 1 := (sum_sq_eq_inner A).trans hA
  have hBs : ∑ j : Fin n, B j ^ 2 = 1 := (sum_sq_eq_inner B).trans hB
  have hpoint (i : Label) (j : Fin n) :
      y i j = z j + coordinates i 0 * A j + coordinates i 1 * B j := by
    have h := congrArg (fun x : Point n => x j) (hform i)
    simpa using h
  have henergy (i : Label) : derivationEnergy D (y i) =
      ∑ j : Fin n, (D (z j + coordinates i 0 * A j + coordinates i 1 * B j)) ^ 2 := by
    unfold derivationEnergy
    simp_rw [hpoint]
  change (∑ i : Label, (weight i : ℝ) * derivationEnergy D (y i)) = 8
  simp_rw [henergy]
  exact weighted_affine_derivation_energy D hD z A B hAs hBs
theorem derivationColor_avoids {n : ℕ}
    (D : Derivation ℤ ℝ ℝ)
    (hD : D parameter = (1 + parameter ^ 2) / 2) :
    AvoidsCopy witness (energyColor (derivationEnergy (n := n) D)) :=
  energyColor_avoids_of_invariant _ (weighted_copy_derivation_energy D hD)
end GrahamSpherical
end
end OAI

-- ===== from OAI/Combinatorics/SphericalRamsey/RealTranscendenceBasis.lean =====
namespace OAI
noncomputable section
namespace GrahamSpherical

/-- The designated transcendental real is retained in the actual maximal
algebraically independent subset of the real field. -/
theorem exists_real_transcendenceBasis_containing (a : ℝ)
    (ha : Transcendental ℚ a) :
    ∃ B : Set ℝ, a ∈ B ∧ IsTranscendenceBasis ℚ (fun b : B => (b : ℝ)) := by
  have hs : AlgebraicIndepOn ℚ id ({a} : Set ℝ) := by
    exact (algebraicIndependent_singleton_iff
      (R := ℚ) (x := fun b : ({a} : Set ℝ) => (b : ℝ)) ⟨a, by simp⟩).2 ha
  obtain ⟨B, hsub, hB⟩ := exists_isTranscendenceBasis_superset hs
  exact ⟨B, hsub (by simp), hB⟩
end GrahamSpherical
end
end OAI

-- ===== from OAI/Combinatorics/SphericalRamsey/BasisDerivation.lean =====
namespace OAI
noncomputable section
namespace GrahamSpherical
private abbrev Poly (ι : Type*) := MvPolynomial ι ℚ
private abbrev RatFun (ι : Type*) := FractionRing (Poly ι)
private def tangentCoefficient {ι : Type*} :
    ℚ →+* TrivSqZeroExt (RatFun ι) (RatFun ι) :=
  (TrivSqZeroExt.inlHom _ _).comp (algebraMap ℚ (RatFun ι))
private def tangentVariable {ι : Type*} (i j : ι) :
    TrivSqZeroExt (RatFun ι) (RatFun ι) := by
  classical
  exact (algebraMap (Poly ι) (RatFun ι) (MvPolynomial.X j),
    if j = i then 1 else 0)
private def polynomialTangent {ι : Type*} (i : ι) :
    Poly ι →+* TrivSqZeroExt (RatFun ι) (RatFun ι) :=
  MvPolynomial.eval₂Hom tangentCoefficient (tangentVariable i)
private theorem polynomialTangent_X {ι : Type*} (i j : ι) :
    polynomialTangent i (MvPolynomial.X j) = tangentVariable i j :=
  MvPolynomial.eval₂Hom_X' tangentCoefficient (tangentVariable i) j
private theorem polynomialTangent_fst {ι : Type*} (i : ι) (p : Poly ι) :
    (polynomialTangent i p).fst = algebraMap (Poly ι) (RatFun ι) p := by
  classical
  have h : (TrivSqZeroExt.fstHom (RatFun ι) (RatFun ι) (RatFun ι)).toRingHom.comp
      (polynomialTangent i) = algebraMap (Poly ι) (RatFun ι) := by
    ext j
    · simp [polynomialTangent, tangentCoefficient, IsScalarTower.algebraMap_eq ℚ (Poly ι) (RatFun ι)]
    · exact congrArg TrivSqZeroExt.fst (polynomialTangent_X i j)
  exact RingHom.congr_fun h p
private theorem polynomialTangent_units {ι : Type*} (i : ι)
    (y : nonZeroDivisors (Poly ι)) : IsUnit (polynomialTangent i y) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, polynomialTangent_fst]
  exact IsFractionRing.isUnit_map_of_injective (IsFractionRing.injective (Poly ι) (RatFun ι)) y
private def fractionTangent {ι : Type*} (i : ι) :
    RatFun ι →+* TrivSqZeroExt (RatFun ι) (RatFun ι) :=
  IsLocalization.lift (polynomialTangent_units i)
private theorem fractionTangent_fst {ι : Type*} (i : ι) (x : RatFun ι) :
    (fractionTangent i x).fst = x := by
  have h : (TrivSqZeroExt.fstHom (RatFun ι) (RatFun ι) (RatFun ι)).toRingHom.comp
      (fractionTangent i) = RingHom.id (RatFun ι) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (Poly ι))
    apply RingHom.ext
    intro p
    change (fractionTangent i (algebraMap (Poly ι) (RatFun ι) p)).fst =
      algebraMap (Poly ι) (RatFun ι) p
    rw [fractionTangent, IsLocalization.lift_eq, polynomialTangent_fst]
  exact RingHom.congr_fun h x
private def fractionDerivation {ι : Type*} (i : ι) :
    Derivation ℤ (RatFun ι) (RatFun ι) where
  toFun x := (fractionTangent i x).snd
  map_add' x y := congrArg TrivSqZeroExt.snd (map_add (fractionTangent i) x y)
  map_smul' n x := by
    simp only [RingHom.id_apply, OreLocalization.zsmul_eq_zsmul]
    exact congrArg TrivSqZeroExt.snd (map_zsmul (fractionTangent i) n x)
  map_one_eq_zero' := congrArg TrivSqZeroExt.snd (map_one (fractionTangent i))
  leibniz' x y := by
    change (fractionTangent i (x * y)).snd =
      x * (fractionTangent i y).snd + y * (fractionTangent i x).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, fractionTangent_fst, fractionTangent_fst]
    change x * (fractionTangent i y).snd + (fractionTangent i x).snd * y =
      x * (fractionTangent i y).snd + y * (fractionTangent i x).snd
    rw [mul_comm (fractionTangent i x).snd y]
private theorem fractionDerivation_X {ι : Type*} (i : ι) :
    fractionDerivation i (algebraMap (Poly ι) (RatFun ι) (MvPolynomial.X i)) = 1 := by
  classical
  change (fractionTangent i (algebraMap (Poly ι) (RatFun ι) (MvPolynomial.X i))).snd = 1
  rw [fractionTangent, IsLocalization.lift_eq]
  have h := congrArg TrivSqZeroExt.snd (polynomialTangent_X i i)
  simpa [tangentVariable] using h

/-- A selected algebraically independent coordinate admits a unit-valued derivation
on the field generated by all coordinates. -/
theorem exists_derivation_adjoin_coordinate {ι : Type*} (b : ι → ℝ)
    (hb : AlgebraicIndependent ℚ b) (i : ι) :
    ∃ D : Derivation ℤ (IntermediateField.adjoin ℚ (Set.range b))
      (IntermediateField.adjoin ℚ (Set.range b)),
      D ⟨b i, IntermediateField.subset_adjoin ℚ (Set.range b) ⟨i, rfl⟩⟩ = 1 := by
  letI : Algebra ℚ (FractionRing (MvPolynomial ι ℚ)) := OreLocalization.instAlgebra
  let e := hb.aevalEquivField
  let D : Derivation ℤ (IntermediateField.adjoin ℚ (Set.range b))
      (IntermediateField.adjoin ℚ (Set.range b)) :=
    { toFun := fun x => e (fractionDerivation i (e.symm x))
      map_add' := fun x y => by simp
      map_smul' := fun n x => by simp
      map_one_eq_zero' := by simp
      leibniz' := fun x y => by simp [Derivation.leibniz, smul_eq_mul] }
  refine ⟨D, ?_⟩
  have hx : e (algebraMap (Poly ι) (RatFun ι) (MvPolynomial.X i)) =
      ⟨b i, IntermediateField.subset_adjoin ℚ (Set.range b) ⟨i, rfl⟩⟩ := by
    apply Subtype.ext
    simp [e, hb.aevalEquivField_algebraMap_apply_coe]
  rw [← hx]
  change e (fractionDerivation i (e.symm (e _))) = 1
  rw [e.symm_apply_apply, fractionDerivation_X, map_one]
end GrahamSpherical
end
end OAI

-- ===== from OAI/Combinatorics/SphericalRamsey/AlgebraicExtension.lean =====
namespace OAI
namespace GrahamSpherical.AlgebraicExtension
open IntermediateField
open scoped Differential
variable {F K : Type*} [Field F] [Field K] [CharZero F]
  [Algebra F K] [Algebra.IsAlgebraic F K] [Differential F]
local instance finiteSimple (x : K) : FiniteDimensional F F⟮x⟯ :=
  IntermediateField.adjoin.finiteDimensional
    (Algebra.IsIntegral.isIntegral (R := F) x)

/-- The value forced by the native derivation on a finite simple subextension. -/
noncomputable def value (x : K) : K :=
  ((Differential.deriv (⟨x, mem_adjoin_simple_self F x⟩ : F⟮x⟯) : F⟮x⟯) : K)

/-- All finite subextensions compute the same derivative of a given element. -/
theorem value_eq (L : IntermediateField F K) [FiniteDimensional F L]
    (x : K) (hx : x ∈ L) :
    value (F := F) x = ((Differential.deriv (⟨x, hx⟩ : L) : L) : K) := by
  have hle : F⟮x⟯ ≤ L := adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hx)
  have h := Differential.algHom_deriv' (inclusion hle) (inclusion_injective hle)
    (⟨x, mem_adjoin_simple_self F x⟩ : F⟮x⟯)
  exact congrArg (fun z : L => (z : K)) h
theorem value_zero : value (F := F) (0 : K) = 0 := by
  rw [value_eq (F⟮(0 : K)⟯) 0 (zero_mem _)]
  change ((Differential.deriv (0 : F⟮(0 : K)⟯) : F⟮(0 : K)⟯) : K) = 0
  simp
theorem value_add (x y : K) :
    value (F := F) (x + y) = value (F := F) x + value (F := F) y := by
  let L : IntermediateField F K := F⟮x⟯ ⊔ F⟮y⟯
  have hx : x ∈ L := (show F⟮x⟯ ≤ L from le_sup_left) (mem_adjoin_simple_self F x)
  have hy : y ∈ L := (show F⟮y⟯ ≤ L from le_sup_right) (mem_adjoin_simple_self F y)
  rw [value_eq L (x + y) (L.add_mem hx hy), value_eq L x hx, value_eq L y hy]
  exact congrArg (fun z : L => (z : K))
    (map_add Differential.deriv (⟨x, hx⟩ : L) (⟨y, hy⟩ : L))
theorem value_mul (x y : K) :
    value (F := F) (x * y) = x * value (F := F) y + y * value (F := F) x := by
  let L : IntermediateField F K := F⟮x⟯ ⊔ F⟮y⟯
  have hx : x ∈ L := (show F⟮x⟯ ≤ L from le_sup_left) (mem_adjoin_simple_self F x)
  have hy : y ∈ L := (show F⟮y⟯ ≤ L from le_sup_right) (mem_adjoin_simple_self F y)
  rw [value_eq L (x * y) (L.mul_mem hx hy), value_eq L x hx, value_eq L y hy]
  have hm : (⟨x, hx⟩ : L) * (⟨y, hy⟩ : L) = ⟨x * y, L.mul_mem hx hy⟩ := by
    apply Subtype.ext
    exact L.coe_mul _ _
  have hd := Derivation.leibniz Differential.deriv (⟨x, hx⟩ : L) (⟨y, hy⟩ : L)
  rw [hm] at hd
  simpa only [smul_eq_mul, IntermediateField.coe_add, IntermediateField.coe_mul,
    Subtype.coe_mk] using congrArg (fun z : L => (z : K)) hd

/-- Extension to an arbitrary algebraic field extension in characteristic zero. -/
@[instance_reducible]
noncomputable def differentialAlgebraic : Differential K where
  deriv := Derivation.mk'
    (AddMonoidHom.toIntLinearMap
      { toFun := value (F := F), map_zero' := value_zero, map_add' := value_add })
    (by intro x y; exact value_mul x y)
theorem value_algebraMap (x : F) :
    value (F := F) (algebraMap F K x) = algebraMap F K (Differential.deriv x) := by
  let L : IntermediateField F K := F⟮algebraMap F K x⟯
  rw [value_eq L _ (L.algebraMap_mem x)]
  change ((Differential.deriv (algebraMap F L x) : L) : K) = _
  rw [deriv_algebraMap]
  rfl
theorem differentialAlgebraAlgebraic :
    let := differentialAlgebraic (F := F) (K := K)
    DifferentialAlgebra F K := by
  let := differentialAlgebraic (F := F) (K := K)
  exact ⟨value_algebraMap⟩
omit [Differential F] in
/-- Explicit derivation interface, avoiding any preexisting derivative on the target. -/
theorem exists_extension (D : Derivation ℤ F F) :
    ∃ E : Derivation ℤ K K,
      ∀ x : F, E (algebraMap F K x) = algebraMap F K (D x) := by
  let : Differential F := ⟨D⟩
  exact ⟨(differentialAlgebraic (F := F) (K := K)).deriv, value_algebraMap⟩
end GrahamSpherical.AlgebraicExtension
end OAI

-- ===== from OAI/Combinatorics/SphericalRamsey/RealDerivation.lean =====
namespace OAI
noncomputable section
namespace GrahamSpherical

/-- Prescribe a derivation at any transcendental real, with an arbitrary real
value. The final scalar need not belong to the rational-function subfield. -/
theorem exists_real_derivation (a c : ℝ) (ha : Transcendental ℚ a) :
    ∃ D : Derivation ℤ ℝ ℝ, D a = c := by
  classical
  obtain ⟨B, haB, hB⟩ := exists_real_transcendenceBasis_containing a ha
  let b : B → ℝ := fun x => (x : ℝ)
  let i : B := ⟨a, haB⟩
  let F := IntermediateField.adjoin ℚ (Set.range b)
  let : Algebra.IsAlgebraic F ℝ := hB.isAlgebraic_field
  obtain ⟨δ, hδ⟩ := exists_derivation_adjoin_coordinate b hB.1 i
  obtain ⟨D, hD⟩ := AlgebraicExtension.exists_extension (K := ℝ) δ
  let x : F := ⟨b i, IntermediateField.subset_adjoin ℚ (Set.range b) ⟨i, rfl⟩⟩
  have hδx : δ x = 1 := by
    exact hδ
  have hDa : D a = 1 := by
    have h := hD x
    rw [hδx, map_one] at h
    exact h
  refine ⟨c • D, ?_⟩
  simp [Derivation.smul_apply, hDa]
end GrahamSpherical
end
end OAI

-- ===== from OAI/Combinatorics/SphericalRamsey/Parameter.lean =====
namespace OAI
noncomputable section
namespace GrahamSpherical

/-- The native series includes the additional factorial-zero term. -/
theorem parameter_add_tenth :
    (1 : ℝ) / 10 + parameter = liouvilleNumber 10 := by
  simpa [LiouvilleNumber.partialSum, LiouvilleNumber.remainder, parameter] using
    (LiouvilleNumber.partialSum_add_remainder (m := (10 : ℝ)) (by norm_num) 0)
theorem parameter_eq_liouville_sub :
    parameter = liouvilleNumber 10 - (1 : ℝ) / 10 := by
  linarith [parameter_add_tenth]

/-- Transcendence of the factorial-series parameter, over the rational field. -/
theorem parameter_transcendental : Transcendental ℚ parameter := by
  intro hp
  have hrat : IsAlgebraic ℚ ((1 : ℝ) / 10) := by
    simpa using (isAlgebraic_ratCast ℚ (1 / 10 : ℚ) :
      IsAlgebraic ℚ ((1 / 10 : ℚ) : ℝ))
  have hsum : IsAlgebraic ℚ (liouvilleNumber 10) := by
    rw [← parameter_add_tenth]
    exact hrat.add hp
  have hint : IsAlgebraic ℤ (liouvilleNumber 10) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr hsum
  exact (transcendental_liouvilleNumber (m := 10) (by norm_num)) hint

/-- The strict rational bounds stated for the literal factorial series. -/
theorem parameter_bounds :
    (11 : ℝ) / 100 < parameter ∧ parameter < 12 / 100 := by
  have hsplit := LiouvilleNumber.partialSum_add_remainder
    (m := (10 : ℝ)) (by norm_num) 2
  have hpos := LiouvilleNumber.remainder_pos (m := (10 : ℝ)) (by norm_num) 2
  have hupp := LiouvilleNumber.remainder_lt (m := (10 : ℝ)) 2 (by norm_num)
  norm_num [LiouvilleNumber.partialSum, Finset.sum_range_succ, Nat.factorial] at hsplit hupp
  constructor <;> linarith [parameter_add_tenth]
end GrahamSpherical
end
end OAI

-- ===== from OAI/Combinatorics/SphericalRamsey/WitnessScalars.lean =====
namespace OAI
noncomputable section
namespace GrahamSpherical
theorem parameter_den_pos : 0 < 1 + parameter ^ 2 := by positivity
theorem u_sq_add_v_sq : u ^ 2 + v ^ 2 = 1 := by
  unfold u v
  field_simp [ne_of_gt parameter_den_pos]
  ring
theorem v_pos : 0 < v := by
  have ht : 0 < parameter := by linarith [parameter_bounds.1]
  exact div_pos (mul_pos (by norm_num) ht) parameter_den_pos
theorem v_lt_u : v < u := by
  apply (div_lt_div_iff_of_pos_right parameter_den_pos).2
  have ht := parameter_bounds
  have hprod : 0 ≤ (12 / 100 - parameter) * (12 / 100 + parameter) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith
theorem u_lt_one : u < 1 := by
  change (1 - parameter ^ 2) / (1 + parameter ^ 2) < 1
  apply (div_lt_one parameter_den_pos).2
  have ht : 0 < parameter := by linarith [parameter_bounds.1]
  nlinarith [sq_pos_of_pos ht]
theorem u_pos : 0 < u := lt_trans v_pos v_lt_u
end GrahamSpherical
end
end OAI

-- ===== from OAI/Combinatorics/SphericalRamsey/WitnessCoordinates.lean =====
namespace OAI
noncomputable section
namespace GrahamSpherical
theorem vertex_injective : Function.Injective vertex := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h0 := congrArg (fun x : Point 2 => x 0) h
  have h1 := congrArg (fun x : Point 2 => x 1) h
  have hp := v_pos
  have hpu := u_pos
  have hlt := v_lt_u
  have hu := u_lt_one
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  all_goals norm_num [vertex, coordinates, squareCoordinate, Fin.ext_iff] at h0
  all_goals norm_num [vertex, coordinates, squareCoordinate, Fin.ext_iff] at h1
  all_goals first | rfl | linarith
theorem vertex_norm (i : Label) : ‖vertex i‖ = 1 := by
  have hs : ‖vertex i‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    rcases i with ⟨a,b⟩
    fin_cases a <;> fin_cases b <;>
      simp [vertex, coordinates, squareCoordinate, Fin.ext_iff, Fin.sum_univ_two, u_sq_add_v_sq,
        add_comm (v ^ 2) (u ^ 2)]
  nlinarith [norm_nonneg (vertex i)]
theorem witness_subset_sphere : witness ⊆ Metric.sphere (0 : Point 2) 1 := by
  rintro x ⟨i, rfl⟩
  simpa [Metric.mem_sphere, dist_zero_right] using vertex_norm i
theorem witness_ncard : witness.ncard = 12 := by
  rw [witness, Set.ncard_range_of_injective vertex_injective]
  norm_num [Label]
end GrahamSpherical
end
end OAI

-- ===== from OAI/Combinatorics/SphericalRamsey/Main.lean =====
namespace OAI
noncomputable section
namespace GrahamSpherical

/-- A single actual real derivation defines avoiding colorings in all dimensions. -/
theorem exists_common_derivation_colorings :
    ∃ D : Derivation ℤ ℝ ℝ,
      D parameter = (1 + parameter ^ 2) / 2 ∧
      ∀ n : ℕ, AvoidsCopy witness (energyColor (derivationEnergy (n := n) D)) := by
  obtain ⟨D, hD⟩ := exists_real_derivation parameter
    ((1 + parameter ^ 2) / 2) parameter_transcendental
  exact ⟨D, hD, fun _ => derivationColor_avoids D hD⟩

/-- The literal twelve-point spherical witness defeats fifty colors in every
positive dimension, hence is not Euclidean Ramsey. No auxiliary premise remains. -/
theorem full_main : Specification.FullAuthoredResult := by
  obtain ⟨D, _hD, hcolors⟩ := exists_common_derivation_colorings
  apply assemble_full_result witness_ncard witness_subset_sphere
  intro n _hn
  exact ⟨energyColor (derivationEnergy (n := n) D), hcolors n⟩
end GrahamSpherical
end
end OAI

/-- Target: top-level `solution`, statement identical to `OAI.GrahamSpherical.full_main`.
Proof translated from openai/math@adc7f124 lean/OAI/Combinatorics/SphericalRamsey/Main.lean. -/
theorem solution : OAI.GrahamSpherical.Specification.FullAuthoredResult := by
  obtain ⟨D, _hD, hcolors⟩ := OAI.GrahamSpherical.exists_common_derivation_colorings
  exact OAI.GrahamSpherical.assemble_full_result OAI.GrahamSpherical.witness_ncard
      OAI.GrahamSpherical.witness_subset_sphere (fun n _hn =>
        ⟨OAI.GrahamSpherical.energyColor (OAI.GrahamSpherical.derivationEnergy (n := n) D), hcolors n⟩)
