-- Prove2me | solution 1 for LipschitzOnWith.exists_cover_image_unitCube
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:15:50.767441+00:00
-- url     : https://prove2.me/submissions/299f6261-ca63-40ca-bdc3-b396f281420a

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.MetricSpace.HausdorffDimension

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Lipschitz-parametrizable sets

A set is Lipschitz parametrizable in dimension `d` when finitely many Lipschitz images of the
unit `d`-cube cover it.  This is the boundary regularity condition used in lattice-point counting:
a codimension-one parametrization gives quantitative control on how many lattice cells can meet a
boundary.

This file supplies the elementary API needed to assemble parametrizations: the property is
monotone in the set, is preserved by Lipschitz images, by locally Lipschitz images, by products
and by finite unions, and holds for finite sets.
It also supplies the way in from smoothness: a map that is `C¹` on the compact cube is Lipschitz
there, so the image of a cube of the right dimension is a single chart.
It also records the basic dimension consequence.  A Lipschitz-parametrizable subset of a
finite-dimensional real normed space has additive Haar measure zero whenever the parameter
dimension is strictly smaller than the ambient dimension.  The proof compares additive Haar
measure with Hausdorff measure and uses the fact that Lipschitz maps do not increase Hausdorff
dimension.

It also records the quantitative form of a single chart: cutting the unit `d`-cube into `m ^ d`
subcubes of side `1 / m` covers a Lipschitz image of it by `m ^ d` pieces of diameter `C / m`.
That is what turns a parametrization in a given dimension into a count.

## Main declarations

* `TauCeti.IsLipschitzParametrizable`: finite Lipschitz parametrizability by a
  unit cube;
* `TauCeti.isLipschitzParametrizable_iff`: the finite-chart characterization of the predicate;
* `TauCeti.IsLipschitzParametrizable.union`: closure under binary unions;
* `TauCeti.IsLipschitzParametrizable.image`: closure under Lipschitz images;
* `TauCeti.IsLipschitzParametrizable.image_of_locallyLipschitz`: closure under locally Lipschitz
  images, which is what a chart-by-chart compactness argument buys over `image`;
* `TauCeti.IsLipschitzParametrizable.iUnion`: closure under unions over a finite index type;
* `TauCeti.IsLipschitzParametrizable.prod`: a product is parametrized in the sum of the
  dimensions;
* `TauCeti.IsLipschitzParametrizable.image_unitCube_of_contDiffOn`: a unit cube's image under a
  map that is `C¹` on it is parametrized by that cube;
* `TauCeti.IsLipschitzParametrizable.of_isBounded`: a bounded subset of a finite-dimensional real
  normed space is parametrized in the ambient dimension;
* `TauCeti.IsLipschitzParametrizable.of_isBounded_of_subset_ker`: a bounded subset of a hyperplane
  is parametrized in codimension one;
* `TauCeti.IsLipschitzParametrizable.measure_zero`: a parametrized set has
  additive Haar measure zero below the ambient dimension;
* `LipschitzOnWith.exists_cover_image_unitCube`: a Lipschitz image of the unit `d`-cube is
  covered by `m ^ d` pieces of arbitrarily small diameter.

## References

* S. Lang, *Algebraic Number Theory*, Chapter VI, Section 2, which the definition and its use in
  the lattice-point estimate follow.
* C. Birkbeck, [*AINTLIB*](https://github.com/CBirkbeck/AINTLIB) at commit
  `db14b34cc5e3d79603e67c205dfa86b7b989000c` (Apache-2.0),
  `projects/Chebotarev/CebotarevDensity/ForMathlib/IdealCongruenceCount.lean`, whose
  `exists_lipschitz_cube_cover_hyperplane_slab` is the concrete precursor of
  `of_isBounded` and `of_isBounded_of_subset_ker`: it covers a bounded slab of a coordinate
  hyperplane of `ι → ℝ` by a single chart, through the same affine rescaling
  `c ↦ 2 * M * c - M` of the unit cube onto the box `[-M, M]`. The two lemmas here say the
  same thing without reference to coordinates, for any finite-dimensional real normed space
  and any hyperplane in it.
-/

 section

open MeasureTheory Set

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti





namespace TauCeti.IsLipschitzParametrizable
end TauCeti.IsLipschitzParametrizable
section IsLipschitzParametrizable
open TauCeti TauCeti.IsLipschitzParametrizable

variable {E F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]
  {d : ℕ} {S T : Set E}





























end IsLipschitzParametrizable

end TauCeti

namespace LipschitzOnWith
end LipschitzOnWith
section LipschitzOnWith
open LipschitzOnWith

variable {E : Type*} [PseudoMetricSpace E]

/-- A map that is Lipschitz with constant `C` on the unit cube `Icc 0 1` of `Fin d → ℝ` carries
that cube into a union of `m ^ d` pieces — one for each subcube of side `1 / m` — each of
diameter at most `C / m`.

This is the quantitative content of a chart of a Lipschitz parametrization: cutting the cube
finely enough covers the image by a prescribed number of arbitrarily small pieces, which is what
bounds the number of lattice cells such an image can meet. -/
theorem solution {d : ℕ} {C : _root_.NNReal} {f : (_root_.Fin d → ℝ) → E}
    (hf : _root_.LipschitzOnWith C f (_root_.Set.Icc 0 1)) {m : ℕ} (hm : 0 < m) :
    ∃ T : (_root_.Fin d → _root_.Fin m) → _root_.Set E,
      (f '' _root_.Set.Icc (0 : _root_.Fin d → ℝ) 1 ⊆ ⋃ k, T k) ∧
        ∀ k, ∀ x ∈ T k, ∀ y ∈ T k, _root_.Dist.dist x y ≤ C / m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  -- `Q k` is the subcube of side `1 / m` with lower corner `k / m`.
  set Q : (_root_.Fin d → _root_.Fin m) → _root_.Set (_root_.Fin d → ℝ) :=
    fun k ↦ {x | ∀ i, x i ∈ _root_.Set.Icc (((k i : ℕ) : ℝ) / m) ((((k i : ℕ) : ℝ) + 1) / m)}
  have hQsub : ∀ k, Q k ⊆ _root_.Set.Icc (0 : _root_.Fin d → ℝ) 1 := by
    intro k x hx
    simp only [_root_.Set.mem_Icc, _root_.Pi.le_def, _root_.Pi.zero_apply, _root_.Pi.one_apply]
    refine ⟨fun i ↦ _root_.le_trans (by positivity) (hx i).1, fun i ↦ (hx i).2.trans ?_⟩
    rw [_root_.div_le_one hmR]
    exact_mod_cast (_root_.Nat.succ_le_of_lt (k i).isLt : (k i : ℕ) + 1 ≤ m)
  have hQcov : _root_.Set.Icc (0 : _root_.Fin d → ℝ) 1 ⊆ ⋃ k, Q k := by
    intro x hx
    simp only [_root_.Set.mem_Icc, _root_.Pi.le_def, _root_.Pi.zero_apply, _root_.Pi.one_apply] at hx
    -- The subcube containing `x` is indexed by the integer parts of the scaled coordinates,
    -- capped at `m - 1` so that the coordinate `1` lands in the last subcube.
    refine _root_.Set.mem_iUnion.2 ⟨fun i ↦ ⟨_root_.Min.min ⌊x i * m⌋₊ (m - 1),
      _root_.lt_of_le_of_lt (_root_.min_le_right _ _) (_root_.Nat.sub_lt hm _root_.Nat.one_pos)⟩, fun i ↦ ?_⟩
    -- Evaluate the index family just chosen at `i`.
    dsimp only
    have hx0 : 0 ≤ x i := hx.1 i
    have hx1 : x i ≤ 1 := hx.2 i
    have hfloor : ((_root_.Min.min ⌊x i * m⌋₊ (m - 1) : ℕ) : ℝ) ≤ x i * m :=
      _root_.le_trans (by exact_mod_cast _root_.min_le_left ⌊x i * m⌋₊ (m - 1))
        (_root_.Nat.floor_le (by positivity))
    refine ⟨(_root_.div_le_iff₀ hmR).2 hfloor, (_root_.le_div_iff₀ hmR).2 ?_⟩
    rcases _root_.le_total ⌊x i * m⌋₊ (m - 1) with h | h
    · rw [_root_.min_eq_left h]
      exact (_root_.Nat.lt_floor_add_one _).le
    · rw [_root_.min_eq_right h, _root_.Nat.cast_sub hm, _root_.Nat.cast_one, _root_.sub_add_cancel]
      nlinarith
  have hQdist : ∀ k, ∀ x ∈ Q k, ∀ y ∈ Q k, _root_.Dist.dist x y ≤ 1 / m := by
    intro k x hx y hy
    refine (_root_.dist_pi_le_iff (by positivity)).2 fun i ↦ ?_
    refine (_root_.Real.dist_le_of_mem_Icc (hx i) (hy i)).trans_eq ?_
    ring
  refine ⟨fun k ↦ f '' Q k, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := _root_.Set.mem_iUnion.1 (hQcov hx)
    exact _root_.Set.mem_iUnion.2 ⟨k, x, hk, _root_.rfl⟩
  · rintro k _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    calc _root_.Dist.dist (f x) (f y) ≤ (C : ℝ) * _root_.Dist.dist x y :=
          hf.dist_le_mul x (hQsub k hx) y (hQsub k hy)
      _ ≤ (C : ℝ) * (1 / m) := by gcongr; exact hQdist k x hx y hy
      _ = (C : ℝ) / m := by ring

end LipschitzOnWith

end
end
