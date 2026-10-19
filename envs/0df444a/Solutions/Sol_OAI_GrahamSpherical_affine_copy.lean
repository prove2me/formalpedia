-- Prove2me | solution 1 for OAI.GrahamSpherical.affine_copy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T10:16:44.509518+00:00
-- url     : https://prove2.me/submissions/21a55a9d-a331-4a48-916f-0ac65334e21d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SphericalRamsey/AffineCopy.lean:L19-L70
-- (upload_full_project.md Phase 4): solution for node OAI.GrahamSpherical.affine_copy. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_SphericalRamsey_MonochromaticObstruction
import Theorems.Thm_OAI_GrahamSpherical_affine_frame_of_anchor_gram

-- ---- from OAI.Combinatorics.SphericalRamsey.AffineCopyCore ----
namespace OAI

noncomputable section
open scoped RealInnerProductSpace
namespace GrahamSpherical

/-- Polarization in the actual real Euclidean inner product. -/
lemma inner_sub_self (n : ℕ) (x y : Point n) :
    (inner ℝ (x-y) (x-y)) = (inner ℝ (x) (x)) - 2*(inner ℝ (x) (y)) + (inner ℝ (y) (y)) := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm y x]
  ring

end GrahamSpherical

end

end OAI

-- ---- from OAI.Combinatorics.SphericalRamsey.AffineCopy ----
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

end GrahamSpherical

end

end OAI

-- ---- platform node ----
open OAI OAI.GrahamSpherical
open scoped RealInnerProductSpace BigOperators


theorem solution : type_of% @_root_.OAI.GrahamSpherical.affine_copy := @_root_.OAI.GrahamSpherical.affine_copy
