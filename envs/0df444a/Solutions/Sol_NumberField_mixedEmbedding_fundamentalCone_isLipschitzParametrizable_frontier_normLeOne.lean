-- Prove2me | solution 1 for NumberField.mixedEmbedding.fundamentalCone.isLipschitzParametrizable_frontier_normLeOne
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:29:49.136352+00:00
-- url     : https://prove2.me/submissions/84e95138-283a-4e97-901d-f9ad5bbfb8a1

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_CanonicalEmbedding_NormLeOneLipschitz
import Definitions.Def_TauCeti_Topology_MetricSpace_LipschitzParametrizable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Theorems.Thm_TauCeti_IsLipschitzParametrizable_image_of_locallyLipschitz
import Theorems.Thm_TauCeti_IsLipschitzParametrizable_image_unitCube_of_contDiffOn
import Theorems.Thm_TauCeti_IsLipschitzParametrizable_prod
import Theorems.Thm_TauCeti_IsLipschitzParametrizable_union

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



/-- A set is Lipschitz parametrizable in dimension `d` if and only if finitely many unit-cube
charts, all Lipschitz with a common constant on the unit cube, cover it. -/
theorem isLipschitzParametrizable_iff {E : Type*} [PseudoEMetricSpace E] {d : ℕ} {S : Set E} :
    IsLipschitzParametrizable d S ↔
      ∃ (n : ℕ) (C : NNReal) (f : Fin n → (Fin d → ℝ) → E),
        (∀ i, LipschitzOnWith C (f i) (Icc (0 : Fin d → ℝ) 1)) ∧
          S ⊆ ⋃ i, f i '' Icc (0 : Fin d → ℝ) 1 :=
  Iff.rfl

namespace IsLipschitzParametrizable

variable {E F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]
  {d : ℕ} {S T : Set E}

/-- Every subset of a Lipschitz-parametrizable set is Lipschitz parametrizable with the same
charts. -/
theorem mono (hT : IsLipschitzParametrizable d T) (hST : S ⊆ T) :
    IsLipschitzParametrizable d S := by
  obtain ⟨n, C, f, hf, hT⟩ := isLipschitzParametrizable_iff.1 hT
  exact isLipschitzParametrizable_iff.2 ⟨n, C, f, hf, hST.trans hT⟩

/-- The empty set is Lipschitz parametrizable in every dimension. -/
@[simp]
theorem empty : IsLipschitzParametrizable d (∅ : Set E) := by
  exact isLipschitzParametrizable_iff.2 ⟨0, 0, Fin.elim0, fun i ↦ i.elim0, Set.empty_subset _⟩

/-- A singleton is Lipschitz parametrizable in every dimension. -/
@[simp]
theorem singleton (x : E) : IsLipschitzParametrizable d ({x} : Set E) := by
  refine isLipschitzParametrizable_iff.2 ⟨1, 0, fun (_ : Fin 1) (_ : Fin d → ℝ) ↦ x,
    fun _ ↦ (LipschitzWith.const (α := Fin d → ℝ) x).lipschitzOnWith, ?_⟩
  intro y hy
  have hyx : y = x := Set.mem_singleton_iff.mp hy
  subst y
  refine Set.mem_iUnion.2 ⟨0, ?_⟩
  exact ⟨0, by simp⟩



/-- A finite union of sets parametrized in the same dimension is Lipschitz parametrizable. -/
theorem biUnion_finset {I : Type*} (s : Finset I) {A : I → Set E}
    (hA : ∀ i ∈ s, IsLipschitzParametrizable d (A i)) :
    IsLipschitzParametrizable d (⋃ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.set_biUnion_insert]
      exact (hA i (Finset.mem_insert_self i s)).union
        (ih fun j hj ↦ hA j (Finset.mem_insert_of_mem hj))

/-- A union over a finite index type of sets parametrized in dimension `d` is Lipschitz
parametrizable in dimension `d`. -/
theorem iUnion {I : Type*} [Finite I] {A : I → Set E}
    (hA : ∀ i, IsLipschitzParametrizable d (A i)) :
    IsLipschitzParametrizable d (⋃ i, A i) := by
  classical
  cases nonempty_fintype I
  rw [← Set.biUnion_univ, ← Finset.coe_univ, Finset.set_biUnion_coe]
  exact biUnion_finset Finset.univ fun i _ ↦ hA i

















end IsLipschitzParametrizable

end TauCeti

namespace LipschitzOnWith

variable {E : Type*} [PseudoMetricSpace E]



end LipschitzOnWith

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Elementary frontier lemmas

Facts about `frontier` that carry no structure of their own: straddling, splitting a domain in
two, clinging to it from inside, the frontier of an image, and the frontier of a finite union.
Each is the topological core of a step that a boundary argument would otherwise carry out inside
a concrete space. The list is open-ended; nothing below depends on how many entries it has.

## A connected set that straddles a set meets its frontier

A preconnected set that meets both a set `V` and its complement must meet `frontier V`: it cannot
cross from the inside of `V` to the outside without touching the boundary. This is the
intermediate-value principle in its purely topological form, and it is the mechanism by which a
*path* leaving a set produces a *boundary point* of that set.

Mathlib records the two extreme cases — `frontier_eq_empty_iff` and `nonempty_frontier_iff` say
that in a preconnected *space* the frontier of `V` is empty exactly when `V` is `∅` or `univ` — but
not this relative form, which is the one an argument along a segment or a path needs. No hypothesis
is placed on `V`; only preconnectedness of the straddling set is used.

The proof is the standard clopen argument: the complement of `frontier V` is the disjoint union of
the two open sets `interior V` and `interior Vᶜ` (`compl_frontier_eq_union_interior`), so a
preconnected set avoiding the frontier lies inside one of them, and then it misses `V` entirely or
is contained in `V` entirely.

## Where the boundary of the image of one side of a split domain can lie

Split a set `U` into two pieces `s` and `t` that a map `f` sends to *disjoint open* sets, plus a
remainder `u`. Then `frontier (f '' s) ⊆ f '' u ∪ frontier (f '' U)`
(`TauCeti.frontier_image_subset_image_union_frontier_image`): the boundary of the image of one side
consists of images of the remainder — the cut — and of boundary points of the whole image, and of
nothing else.

The proof is a three-way case split. A point `p` of `frontier (f '' s)` lies in `closure (f '' U)`,
so if it is not on `frontier (f '' U)` it is a value `f w` with `w` in one of the three covering
sets. It cannot come from `s`, since `f '' s` is open and therefore disjoint from its own frontier;
and it cannot come from `t`, since `f '' t` is then an open neighbourhood of `p`, which must meet
`f '' s`, contradicting disjointness of the two images. So `w ∈ u`.

The source carries no topology; the sides enter topologically only through their images, which are
asked to be open and disjoint, and that is all the argument uses of them. What is asked of the
sides themselves is purely set-theoretic: `s ⊆ U` and the covering `U ⊆ s ∪ t ∪ u`. In particular
`t` need not lie in `U`, and neither side need be open or disjoint from the other. A consumer whose
map is open and injective on two disjoint open sides supplies both image hypotheses, as the
conformal one below does through the open mapping theorem and `Disjoint.image`.

## What a set's frontier sees of a subset

A subset `A` of a set `V` cannot reach `frontier V` except through its own frontier:

> `frontier V ∩ closure A = frontier V ∩ frontier A`

(`TauCeti.frontier_inter_closure_eq_frontier_inter_frontier`). The reason is that `closure A` is
`A ∪ frontier A`, and a point of `A` on `frontier V` is already on `frontier A`: it is adherent to
`A` and, since `interior A ⊆ interior V`, it is not interior to `A`. So the part of `frontier V`
that `A` clings to has two interchangeable descriptions — as the reach of `closure A`, and as the
meeting of two frontiers. The first is the one an argument about limits of points of `A` produces;
the second is the one a diameter estimate consumes, `frontier` being where the estimates of a
domain-splitting argument live.

## Consumers

The straddling, splitting and clinging lemmas serve Carathéodory's boundary correspondence for
conformal maps. The first does so through `TauCeti/Analysis/Normed/Module/DiamFrontier.lean`: a
ray leaving a bounded set crosses its frontier, which is what makes the frontier of such a set as
wide as the set itself. The second is the splitting step of
`TauCeti/Analysis/Complex/Conformal/CutDiameter.lean`, where `s` and `t` are the two sides of a
circular crosscut of a domain and `u` is the crosscut arc. The third is what lets
`TauCeti/Analysis/Complex/Conformal/ClusterSet.lean` identify the boundary piece that one side of
such a crosscut cuts off, whose description as a union of cluster sets is naturally a statement
about a closure. The image and finite-union lemmas are used quite differently, for a partial
homeomorphism of a real coordinate space and for the frontier of a finite union of unit translates
of a lattice region. Nothing here is specific to any of those uses; no lemma mentions a metric,
let alone a holomorphic map.

## Main results

* `IsPreconnected.inter_frontier_nonempty` — a preconnected set meeting both a set and its
  complement meets the frontier of that set.
* `TauCeti.frontier_image_subset_image_union_frontier_image` — for a set split into two sides with
  disjoint open images plus a remainder, the frontier of the image of the side lying in that set
  lies on the image of the remainder and on the frontier of the image of the whole.
* `TauCeti.frontier_inter_closure_eq_frontier_inter_frontier` — the frontier of a set meets the
  closure of a subset exactly where it meets that subset's frontier.
* `TauCeti.frontier_image_subset_of_closure_subset` — for an open injective map whose image
  closure adds at most a set `t`, the frontier of an image lies on the image of the frontier,
  together with `t`.
* `TauCeti.frontier_iUnion_subset` — the frontier of a union over a finite index type lies in the
  union of the frontiers.
-/

 section

namespace TauCeti

open Set

section Straddle

variable {X : Type*} [TopologicalSpace X] {S V : Set X}



end Straddle

section ImageSplit

variable {X Y : Type*} [TopologicalSpace Y] {f : X → Y} {U s t u : Set X}



end ImageSplit

section Inside

variable {X : Type*} [TopologicalSpace X] {A V : Set X}



end Inside

section OpenInjectiveImage

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {s : Set X}
  {t : Set Y}

/-- **The frontier of an image lies on the image of the frontier, plus whatever the closure adds.**
For an open injective `f` whose image closure satisfies `closure (f '' s) ⊆ f '' closure s ∪ t`,

> `frontier (f '' s) ⊆ f '' frontier s ∪ t`.

The extra set `t` absorbs whatever an unbounded direction of `s` escapes to: without it the
inclusion would say that the frontier of an image is the image of a frontier, which fails as soon
as `f` sends a divergent sequence somewhere convergent. A consumer supplies `t` together with the
closure hypothesis, typically from a compactness statement about the image; it is often a single
point, but nothing in the argument needs that.

Openness and injectivity are both used, and neither can be dropped: openness keeps the image of
the interior inside the interior of the image, and injectivity is what turns a difference of
images into the image of a difference. -/
theorem frontier_image_subset_of_closure_subset (hf : IsOpenMap f) (hfi : Function.Injective f)
    (hcl : closure (f '' s) ⊆ f '' closure s ∪ t) :
    frontier (f '' s) ⊆ f '' frontier s ∪ t := by
  refine (Set.sdiff_subset_sdiff hcl (hf.image_interior_subset s)).trans ?_
  rw [Set.union_sdiff_distrib, ← Set.image_sdiff hfi]
  exact Set.union_subset_union_right _ Set.sdiff_subset

end OpenInjectiveImage

section FiniteUnion

variable {X : Type*} [TopologicalSpace X]



end FiniteUnion

end TauCeti

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Dirichlet's unit theorem in structural form

Mathlib's `NumberField.Units.exist_unique_eq_mul_prod` states that every unit of `𝓞 F` has a
unique decomposition as a root of unity times a product of powers of the fundamental system.
This file packages that unique decomposition as a multiplicative equivalence

`(𝓞 F)ˣ ≃* torsion F × Multiplicative (Fin (rank F) → ℤ)`,

exhibiting the unit group as the product of its (finite cyclic) torsion subgroup and a free
abelian group of Dirichlet rank. This structural form is what downstream counting arguments
consume — for instance the exact number of unit square classes in
`TauCeti.NumberTheory.NumberField.Units.ElementaryTwoQuotient`.

## Main results

* `NumberField.unitsMulEquivTorsionProdMultiplicative`: the unit group as the product of
  its torsion subgroup and the free abelian group on the fundamental system.
* `NumberField.rank_eq_one_of_finrank_eq_two_of_isReal`: a quadratic field with a real place
  has unit rank one.
* `NumberField.rank_add_nrComplexPlaces_add_one`: the unit rank plus the number of complex
  places plus one is the degree.
-/

 section

open scoped NumberField

open Module NumberField NumberField.Units

namespace NumberField

variable (F : Type*) [Field F] [NumberField F]













open scoped Classical in
/-- **The unit rank, the complex places and one exhaust the degree.** Dirichlet's rank is
`#(InfinitePlace F) - 1` while the degree is `r₁ + 2 * r₂`, so restoring the complex places and
the one place the rank drops recovers `finrank ℚ F`.

Stated as an addition rather than as `rank F + nrComplexPlaces F = finrank ℚ F - 1`: the
subtraction on `ℕ` is truncated, and the additive form needs no positivity side condition. -/
theorem rank_add_nrComplexPlaces_add_one :
    rank F + InfinitePlace.nrComplexPlaces F + 1 = finrank ℚ F := by
  have h₁ := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
  have h₂ := InfinitePlace.card_add_two_mul_card_eq_rank F
  -- `rank` is a truncated subtraction, so the count of places must be known to be positive.
  have h₃ : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
  simp only [Units.rank]
  omega



end NumberField

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# A Lipschitz parametrization of the frontier of the norm-≤-one region

`TauCeti.NumberTheory.GeometryOfNumbers.LatticePointCount` counts lattice points in a dilated
region with a power-saving error, but only for regions whose frontier is Lipschitz
parametrizable: `exists_abs_ncard_smul_inter_vadd_sub_le` takes
`IsLipschitzParametrizable (finrank ℝ E - 1) (frontier D)` as a hypothesis. Mathlib proves that
`frontier (normLeOne K)` is *null* (`volume_frontier_normLeOne`), which is what a rate-free limit
needs and is strictly weaker: a null frontier does not provide a quantitative or power-saving
error bound.

This file discharges that hypothesis for `normLeOne K`. Mathlib presents the region through
`expMapBasis`, a partial homeomorphism of `realSpace K` whose image of the box
`paramSet K = univ.pi fun w ↦ if w = w₀ then Iic 0 else Ico 0 1` is the norm-≤-one region up to
`normAtAllPlaces`. The frontier of a box is the union of its faces, so a Lipschitz cover of the
image reduces to parametrizing the image of each face — which is what the maps here do.

The `w₀` face is where the unbounded `Iic 0` direction is pinned at its endpoint; the side faces
pin one of the bounded `Ico 0 1` directions, and there the substitution `t = exp (x w₀)` turns the
unbounded direction into the freed cube coordinate.

## Main results

* `isLipschitzParametrizable_frontier_normLeOne`: the frontier of `normLeOne K` is Lipschitz
  parametrizable in dimension `finrank ℝ (mixedSpace K) - 1`, one less than that of the mixed
  space.
* `frontier_normLeOne_subset_preimage`: that frontier lies over the frontier of the box image,
  through `normAtAllPlaces`.
* `isLipschitzParametrizable_frontier_image_paramSet`: the frontier of the box image is Lipschitz
  parametrizable in dimension `rank K`, one less than that of `realSpace K`.
* `contDiff_expMapBasis`: the box parametrization is smooth.
* `closure_image_paramSet_subset`: the closure of the box image adds only the origin.
* `frontier_image_paramSet_subset`: the frontier of the box image lies in the image of the box's
  frontier, together with the origin.

The face maps that decompose the box's frontier, the lifts that cover the fibres of
`normAtAllPlaces`, and the lemmas supporting them, are `private`: they implement the
parametrization and are not independently reusable.

## References

* C. Birkbeck, [*AINTLIB*](https://github.com/CBirkbeck/AINTLIB) at commit
  `db14b34cc5e3d79603e67c205dfa86b7b989000c` (Apache-2.0),
  `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean`, from which the face
  decomposition is adapted: `faceMapZero`, `faceMapSide`, `contDiff_faceMapZero`,
  `contDiff_faceMapSide`, `frontier_image_subset_of_closure_subset` and
  `frontier_image_paramSet_subset` follow that file's declarations of the same names.
  `isLipschitzParametrizable_frontier_normLeOne` is that file's
  `normLeOne_frontier_lipschitz_cover`, and the circle direction of `liftMap` follows its
  `lipschitzWith_exp_ofReal_mul_I`; the sign and angle bookkeeping is arranged differently here,
  through a single globally `C¹` lift rather than that file's `cubeRelabel` scaffolding.
-/

 section

open Finset Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.Units dirichletUnitTheorem
open scoped NumberField

namespace NumberField.mixedEmbedding.fundamentalCone
end NumberField.mixedEmbedding.fundamentalCone
section NumberField.mixedEmbedding.fundamentalCone
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K]

/-- `expMapBasis` is `C^n` for every `n`: it is an exponential in the `w₀` coordinate times a
product of real powers of the positive reals `w (fundSystem ...)` in the others. -/
theorem NumberField.mixedEmbedding.fundamentalCone.contDiff_expMapBasis {n : _root_.WithTop ℕ∞} : _root_.ContDiff ℝ n (⇑(_root_.NumberField.mixedEmbedding.fundamentalCone.expMapBasis (K := K))) := by
  classical
  simp_rw [_root_.funext _root_.NumberField.mixedEmbedding.fundamentalCone.expMapBasis_apply']
  fun_prop (disch := exact fun x ↦ (InfinitePlace.pos_iff.mpr (by simp)).ne')





open scoped Classical in
/-- The `w₀` face map is `C¹`. -/
private theorem NumberField.mixedEmbedding.fundamentalCone.contDiff_faceMapZero : _root_.ContDiff ℝ 1 (_root_.NumberField.mixedEmbedding.fundamentalCone.faceMapZero K) := by
  refine (_root_.NumberField.mixedEmbedding.fundamentalCone.contDiff_expMapBasis K).comp (contDiff_pi.mpr fun w ↦ ?_)
  by_cases hw : w = _root_.NumberField.Units.dirichletUnitTheorem.w₀
  · simpa [hw] using _root_.contDiff_const
  · simpa [hw] using _root_.contDiff_apply ℝ ℝ _

open scoped Classical in
/-- A side face map is `C¹`. -/
private theorem NumberField.mixedEmbedding.fundamentalCone.contDiff_faceMapSide (i : {w : _root_.NumberField.InfinitePlace K // w ≠ _root_.NumberField.Units.dirichletUnitTheorem.w₀}) (a : ℝ) :
    _root_.ContDiff ℝ 1 (_root_.NumberField.mixedEmbedding.fundamentalCone.faceMapSide K i a) := by
  refine (_root_.contDiff_apply ℝ ℝ i).smul ((_root_.NumberField.mixedEmbedding.fundamentalCone.contDiff_expMapBasis K).comp (contDiff_pi.mpr fun w ↦ ?_))
  by_cases hw : w = _root_.NumberField.Units.dirichletUnitTheorem.w₀
  · simpa [hw] using _root_.contDiff_const
  · simp only [hw, ↓_root_.reduceDIte]
    by_cases hi : (⟨w, hw⟩ : {w : _root_.NumberField.InfinitePlace K // w ≠ _root_.NumberField.Units.dirichletUnitTheorem.w₀}) = i
    · simpa [hi] using _root_.contDiff_const
    · simpa [hi] using _root_.contDiff_apply ℝ ℝ _

/-- **The closure of the box image adds only the origin.** The origin is what the `w₀` coordinate
escapes to as it runs to `-∞`, and it is the sole reason the closure of the image is not the image
of the closure. -/
theorem NumberField.mixedEmbedding.fundamentalCone.closure_image_paramSet_subset :
    _root_.closure (_root_.NumberField.mixedEmbedding.fundamentalCone.expMapBasis '' _root_.NumberField.mixedEmbedding.fundamentalCone.paramSet K) ⊆ _root_.NumberField.mixedEmbedding.fundamentalCone.expMapBasis '' _root_.closure (_root_.NumberField.mixedEmbedding.fundamentalCone.paramSet K) ∪ {0} := by
  rw [← _root_.NumberField.mixedEmbedding.fundamentalCone.compactSet_eq_union]
  exact (_root_.NumberField.mixedEmbedding.fundamentalCone.isCompact_compactSet K).isClosed.closure_subset_iff.mpr
    ((_root_.Set.image_mono _root_.subset_closure).trans (_root_.NumberField.mixedEmbedding.fundamentalCone.expMapBasis_closure_subset_compactSet K))

/-- **The frontier of the box image lies in the image of the box boundary, plus the origin.**
This is the reduction the Lipschitz cover runs on: the boundary of a product of intervals is a
finite union of faces, so parametrizing it reduces to parametrizing each face. -/
theorem NumberField.mixedEmbedding.fundamentalCone.frontier_image_paramSet_subset :
    _root_.frontier (_root_.NumberField.mixedEmbedding.fundamentalCone.expMapBasis '' _root_.NumberField.mixedEmbedding.fundamentalCone.paramSet K) ⊆
      _root_.NumberField.mixedEmbedding.fundamentalCone.expMapBasis '' _root_.frontier (_root_.NumberField.mixedEmbedding.fundamentalCone.paramSet K) ∪ {0} :=
  _root_.TauCeti.frontier_image_subset_of_closure_subset
    (fun _ hs ↦ expMapBasis.isOpen_image_of_subset_source hs (by simp [_root_.NumberField.mixedEmbedding.fundamentalCone.expMapBasis_source]))
    (_root_.NumberField.mixedEmbedding.fundamentalCone.injective_expMapBasis K) (_root_.NumberField.mixedEmbedding.fundamentalCone.closure_image_paramSet_subset K)

variable {K}

open scoped Classical in
/-- **A point of the `w₀` face is hit by `faceMapZero`.** Its cube coordinates are the point's own
coordinates away from `w₀`, which lie in `Icc 0 1` because the point is in the closed box; the
pinned coordinate agrees because the point sits at the face's endpoint `x w₀ = 0`. -/
private theorem NumberField.mixedEmbedding.fundamentalCone.expMapBasis_mem_image_faceMapZero {x : _root_.NumberField.mixedEmbedding.realSpace K} (hx : x ∈ _root_.closure (_root_.NumberField.mixedEmbedding.fundamentalCone.paramSet K))
    (hx₀ : x _root_.NumberField.Units.dirichletUnitTheorem.w₀ = 0) :
    _root_.NumberField.mixedEmbedding.fundamentalCone.expMapBasis x ∈ _root_.NumberField.mixedEmbedding.fundamentalCone.faceMapZero K '' _root_.Set.Icc (0 : {w : _root_.NumberField.InfinitePlace K // w ≠ _root_.NumberField.Units.dirichletUnitTheorem.w₀} → ℝ) 1 := by
  rw [_root_.NumberField.mixedEmbedding.fundamentalCone.closure_paramSet, _root_.Set.mem_univ_pi] at hx
  have hmem : ∀ i : {w : _root_.NumberField.InfinitePlace K // w ≠ _root_.NumberField.Units.dirichletUnitTheorem.w₀}, x i ∈ _root_.Set.Icc (0 : ℝ) 1 :=
    fun i ↦ by simpa [i.2] using hx i
  refine ⟨fun i ↦ x i, ⟨fun i ↦ (hmem i).1, fun i ↦ (hmem i).2⟩, ?_⟩
  exact _root_.congrArg _root_.NumberField.mixedEmbedding.fundamentalCone.expMapBasis (_root_.funext fun w ↦ by by_cases hw : w = _root_.NumberField.Units.dirichletUnitTheorem.w₀ <;> simp [hw, hx₀])

open scoped Classical in
/-- **A point of the side face pinning `i` is hit by `faceMapSide`.** The substitution
`t = exp (x w₀) ∈ (0, 1]` moves the unbounded `w₀` direction into the cube coordinate freed by
pinning `i`, so the cube point is the original coordinates with `i` replaced by `t`. -/
private theorem NumberField.mixedEmbedding.fundamentalCone.expMapBasis_mem_image_faceMapSide {x : _root_.NumberField.mixedEmbedding.realSpace K} (hx : x ∈ _root_.closure (_root_.NumberField.mixedEmbedding.fundamentalCone.paramSet K))
    (i : {w : _root_.NumberField.InfinitePlace K // w ≠ _root_.NumberField.Units.dirichletUnitTheorem.w₀}) :
    _root_.NumberField.mixedEmbedding.fundamentalCone.expMapBasis x ∈
      _root_.NumberField.mixedEmbedding.fundamentalCone.faceMapSide K i (x i) '' _root_.Set.Icc (0 : {w : _root_.NumberField.InfinitePlace K // w ≠ _root_.NumberField.Units.dirichletUnitTheorem.w₀} → ℝ) 1 := by
  rw [_root_.NumberField.mixedEmbedding.fundamentalCone.closure_paramSet, _root_.Set.mem_univ_pi] at hx
  have hx₀ : x _root_.NumberField.Units.dirichletUnitTheorem.w₀ ≤ 0 := by simpa using hx _root_.NumberField.Units.dirichletUnitTheorem.w₀
  have hmem : ∀ j : {w : _root_.NumberField.InfinitePlace K // w ≠ _root_.NumberField.Units.dirichletUnitTheorem.w₀}, x j ∈ _root_.Set.Icc (0 : ℝ) 1 :=
    fun j ↦ by simpa [j.2] using hx j
  refine ⟨_root_.Function.update (fun j : {w : _root_.NumberField.InfinitePlace K // w ≠ _root_.NumberField.Units.dirichletUnitTheorem.w₀} ↦ x j) i (_root_.Real.exp (x _root_.NumberField.Units.dirichletUnitTheorem.w₀)),
    ⟨fun j ↦ ?_, fun j ↦ ?_⟩, ?_⟩
  · rcases _root_.eq_or_ne j i with rfl | hj
    · simpa using (_root_.Real.exp_pos (x _root_.NumberField.Units.dirichletUnitTheorem.w₀)).le
    · simpa [_root_.Function.update_of_ne hj] using (hmem j).1
  · rcases _root_.eq_or_ne j i with rfl | hj
    · simpa using _root_.Real.exp_le_one_iff.2 hx₀
    · simpa [_root_.Function.update_of_ne hj] using (hmem j).2
  · rw [_root_.NumberField.mixedEmbedding.fundamentalCone.faceMapSide, _root_.Function.update_self, _root_.NumberField.mixedEmbedding.fundamentalCone.expMapBasis_apply'' x]
    refine _root_.congrArg (fun z : _root_.NumberField.mixedEmbedding.realSpace K ↦ _root_.Real.exp (x _root_.NumberField.Units.dirichletUnitTheorem.w₀) • _root_.NumberField.mixedEmbedding.fundamentalCone.expMapBasis z) (_root_.funext fun w ↦ ?_)
    by_cases hw : w = _root_.NumberField.Units.dirichletUnitTheorem.w₀
    · simp [hw]
    · by_cases hwi : (⟨w, hw⟩ : {w : _root_.NumberField.InfinitePlace K // w ≠ _root_.NumberField.Units.dirichletUnitTheorem.w₀}) = i
      · simp [hw, hwi, ← Subtype.ext_iff.mp hwi]
      · simp [hw, hwi]

variable (K)

open scoped Classical in
/-- **The boundary of the box is covered by the faces.** A point of the closed box that misses the
open box has some coordinate at an endpoint: the `w₀` coordinate at `0`, or a bounded coordinate at
`0` or `1`. Those are exactly the faces parametrized by `faceMapZero` and `faceMapSide`. -/
private theorem NumberField.mixedEmbedding.fundamentalCone.image_frontier_paramSet_subset :
    _root_.NumberField.mixedEmbedding.fundamentalCone.expMapBasis '' _root_.frontier (_root_.NumberField.mixedEmbedding.fundamentalCone.paramSet K) ⊆
      _root_.NumberField.mixedEmbedding.fundamentalCone.faceMapZero K '' _root_.Set.Icc (0 : {w : _root_.NumberField.InfinitePlace K // w ≠ _root_.NumberField.Units.dirichletUnitTheorem.w₀} → ℝ) 1 ∪
        ⋃ p : {w : _root_.NumberField.InfinitePlace K // w ≠ _root_.NumberField.Units.dirichletUnitTheorem.w₀} × _root_.Bool,
          _root_.NumberField.mixedEmbedding.fundamentalCone.faceMapSide K p.1 (if p.2 then 1 else 0) ''
            _root_.Set.Icc (0 : {w : _root_.NumberField.InfinitePlace K // w ≠ _root_.NumberField.Units.dirichletUnitTheorem.w₀} → ℝ) 1 := by
  rintro _ ⟨x, ⟨hxc, hxi⟩, rfl⟩
  have hbox := (_root_.NumberField.mixedEmbedding.fundamentalCone.closure_paramSet K).subset hxc
  rw [_root_.Set.mem_univ_pi] at hbox
  rw [_root_.NumberField.mixedEmbedding.fundamentalCone.interior_paramSet] at hxi
  have hsome : ∃ w : _root_.NumberField.InfinitePlace K,
      x w ∉ (if w = _root_.NumberField.Units.dirichletUnitTheorem.w₀ then _root_.Set.Iio (0 : ℝ) else _root_.Set.Ioo 0 1) := by
    by_contra hcon
    push _root_.Not at hcon
    exact hxi (_root_.Set.mem_univ_pi.2 hcon)
  obtain ⟨w, hw⟩ := hsome
  by_cases hw₀ : w = _root_.NumberField.Units.dirichletUnitTheorem.w₀
  · subst hw₀
    have hge : (0 : ℝ) ≤ x _root_.NumberField.Units.dirichletUnitTheorem.w₀ := by simpa using hw
    exact _root_.Or.inl (_root_.NumberField.mixedEmbedding.fundamentalCone.expMapBasis_mem_image_faceMapZero hxc
      (_root_.le_antisymm (by simpa using hbox _root_.NumberField.Units.dirichletUnitTheorem.w₀) hge))
  · have hnot : x w ∉ _root_.Set.Ioo (0 : ℝ) 1 := by simpa [hw₀] using hw
    have hmem : x w ∈ _root_.Set.Icc (0 : ℝ) 1 := by simpa [hw₀] using hbox w
    rw [_root_.Set.mem_Ioo, _root_.not_and_or, _root_.not_lt, _root_.not_lt] at hnot
    refine _root_.Or.inr ?_
    rcases hnot with h | h
    · exact _root_.Set.mem_iUnion.2 ⟨(⟨w, hw₀⟩, _root_.Bool.false), by
        simpa [_root_.le_antisymm h hmem.1] using _root_.NumberField.mixedEmbedding.fundamentalCone.expMapBasis_mem_image_faceMapSide hxc ⟨w, hw₀⟩⟩
    · exact _root_.Set.mem_iUnion.2 ⟨(⟨w, hw₀⟩, _root_.Bool.true), by
        simpa [_root_.le_antisymm hmem.2 h] using _root_.NumberField.mixedEmbedding.fundamentalCone.expMapBasis_mem_image_faceMapSide hxc ⟨w, hw₀⟩⟩

private theorem NumberField.mixedEmbedding.fundamentalCone.isLipschitzParametrizable_image_frontier_paramSet :
    _root_.TauCeti.IsLipschitzParametrizable (_root_.NumberField.Units.rank K)
      (_root_.NumberField.mixedEmbedding.fundamentalCone.expMapBasis '' _root_.frontier (_root_.NumberField.mixedEmbedding.fundamentalCone.paramSet K)) := by
  classical
  have hcard : _root_.Fintype.card {w : _root_.NumberField.InfinitePlace K // w ≠ _root_.NumberField.Units.dirichletUnitTheorem.w₀} = _root_.NumberField.Units.rank K :=
    (_root_.Fintype.card_congr _root_.NumberField.mixedEmbedding.fundamentalCone.equivFinRank).symm.trans (_root_.Fintype.card_fin _)
  refine .mono ?_ (_root_.NumberField.mixedEmbedding.fundamentalCone.image_frontier_paramSet_subset K)
  refine .union
    (.image_unitCube_of_contDiffOn hcard (_root_.ContDiff.contDiffOn (_root_.NumberField.mixedEmbedding.fundamentalCone.contDiff_faceMapZero K))) ?_
  exact .iUnion fun p ↦ .image_unitCube_of_contDiffOn hcard
    (_root_.ContDiff.contDiffOn (_root_.NumberField.mixedEmbedding.fundamentalCone.contDiff_faceMapSide K p.1 _))

/-- **The frontier of the box image is Lipschitz parametrizable in codimension one.** This is the
hypothesis `TauCeti.IsLipschitzParametrizable.exists_ncard_smul_add_inter_le` needs to turn a
lattice-point count into a count with a power-saving error term; Mathlib's
`volume_frontier_normLeOne` gives only that the frontier is null, which yields a rate-free
asymptotic but no quantitative error bound.

The dimension is `rank K = #(InfinitePlace K) - 1`, one less than that of `realSpace K`. -/
theorem NumberField.mixedEmbedding.fundamentalCone.isLipschitzParametrizable_frontier_image_paramSet :
    _root_.TauCeti.IsLipschitzParametrizable (_root_.NumberField.Units.rank K) (_root_.frontier (_root_.NumberField.mixedEmbedding.fundamentalCone.expMapBasis '' _root_.NumberField.mixedEmbedding.fundamentalCone.paramSet K)) :=
  .mono ((_root_.NumberField.mixedEmbedding.fundamentalCone.isLipschitzParametrizable_image_frontier_paramSet K).union (.singleton 0)) <|
    _root_.NumberField.mixedEmbedding.fundamentalCone.frontier_image_paramSet_subset K

/-- **The frontier of the norm-≤-one region sits over the frontier of the box image.**
`normLeOne K` is the preimage of `expMapBasis '' paramSet K` under the continuous
`normAtAllPlaces`, and the frontier of a preimage lies in the preimage of the frontier. -/
theorem NumberField.mixedEmbedding.fundamentalCone.frontier_normLeOne_subset_preimage :
    _root_.frontier (_root_.NumberField.mixedEmbedding.fundamentalCone.normLeOne K) ⊆ _root_.NumberField.mixedEmbedding.normAtAllPlaces ⁻¹' _root_.frontier (_root_.NumberField.mixedEmbedding.fundamentalCone.expMapBasis '' _root_.NumberField.mixedEmbedding.fundamentalCone.paramSet K) := by
  rw [_root_.NumberField.mixedEmbedding.fundamentalCone.normLeOne_eq_preimage]
  exact (_root_.NumberField.mixedEmbedding.continuous_normAtAllPlaces K).frontier_preimage_subset _



open scoped Classical in
/-- Each lift is `C¹`: it is linear at the real places, and a product of a coordinate with a
complex exponential at the complex ones. -/
private theorem NumberField.mixedEmbedding.fundamentalCone.contDiff_liftMap (s : {w : _root_.NumberField.InfinitePlace K // _root_.NumberField.InfinitePlace.IsReal w} → _root_.Bool) :
    _root_.ContDiff ℝ 1 (_root_.NumberField.mixedEmbedding.fundamentalCone.liftMap K s) := by
  unfold _root_.NumberField.mixedEmbedding.fundamentalCone.liftMap
  fun_prop

omit [_root_.NumberField K] in
/-- **The lifts cover every fibre of `normAtAllPlaces`.** A point of the mixed space is recovered
from its vector of norms by choosing a sign at each real place and an argument at each complex
place, so the preimage of any `S` is covered by the `2 ^ r₁` lifts of `S` times the cube of
angles. -/
private theorem NumberField.mixedEmbedding.fundamentalCone.preimage_subset_iUnion_image_liftMap (S : _root_.Set (_root_.NumberField.mixedEmbedding.realSpace K)) :
    _root_.NumberField.mixedEmbedding.normAtAllPlaces ⁻¹' S ⊆ ⋃ s : {w : _root_.NumberField.InfinitePlace K // _root_.NumberField.InfinitePlace.IsReal w} → _root_.Bool,
      _root_.NumberField.mixedEmbedding.fundamentalCone.liftMap K s '' (S ×ˢ _root_.Set.Icc (0 : {w : _root_.NumberField.InfinitePlace K // _root_.NumberField.InfinitePlace.IsComplex w} → ℝ) 1) := by
  intro x hx
  have hpi : (0 : ℝ) < 2 * _root_.Real.pi := by positivity
  -- The sign bit at `w` records whether `x` is nonnegative there, and the cube coordinate at a
  -- complex place is the argument of `x w`, rescaled from `[-π, π]` to `[0, 1]`.
  refine _root_.Set.mem_iUnion.2 ⟨fun w ↦ _root_.Decidable.decide (0 ≤ x.1 w), ⟨_root_.NumberField.mixedEmbedding.normAtAllPlaces x,
    fun w ↦ (_root_.Complex.arg (x.2 w) + _root_.Real.pi) / (2 * _root_.Real.pi)⟩, ⟨hx, ⟨fun w ↦ ?_, fun w ↦ ?_⟩⟩, ?_⟩
  · exact _root_.div_nonneg (by linarith [_root_.Complex.neg_pi_lt_arg (x.2 w)]) hpi.le
  · exact (_root_.div_le_one hpi).2 (by linarith [_root_.Complex.arg_le_pi (x.2 w)])
  refine _root_.Prod.ext (_root_.funext fun w ↦ ?_) (_root_.funext fun w ↦ ?_)
  · have hnorm : _root_.NumberField.mixedEmbedding.normAtAllPlaces x w.1 = ‖x.1 w‖ := _root_.NumberField.mixedEmbedding.normAtPlace_apply_of_isReal w.2 x
    by_cases h : 0 ≤ x.1 w
    · simp [_root_.NumberField.mixedEmbedding.fundamentalCone.liftMap, hnorm, h, _root_.Real.norm_of_nonneg h]
    · simp [_root_.NumberField.mixedEmbedding.fundamentalCone.liftMap, hnorm, h, _root_.Real.norm_of_nonpos (_root_.not_le.1 h).le]
  · have hnorm : _root_.NumberField.mixedEmbedding.normAtAllPlaces x w.1 = ‖x.2 w‖ := _root_.NumberField.mixedEmbedding.normAtPlace_apply_of_isComplex w.2 x
    have hang : 2 * _root_.Real.pi * ((_root_.Complex.arg (x.2 w) + _root_.Real.pi) / (2 * _root_.Real.pi)) - _root_.Real.pi
        = _root_.Complex.arg (x.2 w) := by
      field_simp
      ring
    simp only [_root_.NumberField.mixedEmbedding.fundamentalCone.liftMap, hnorm, hang, _root_.Complex.real_smul]
    exact _root_.Complex.norm_mul_exp_arg_mul_I _

open scoped Classical in
/-- **The frontier of the norm-≤-one region is Lipschitz parametrizable in codimension one.**
This discharges the boundary hypothesis of `TauCeti.exists_abs_ncard_smul_inter_vadd_sub_le` for
`normLeOne K`, whose frontier Mathlib knows only to be null (`volume_frontier_normLeOne`) — a
null frontier supports a rate-free limit but gives no quantitative or power-saving error bound.

The frontier lies over the frontier of the box image, which is parametrizable in dimension
`rank K`; each fibre of `normAtAllPlaces` adds the `r₂` angles at the complex places and a choice
of sign at each of the `r₁` real places, and `rank K + r₂ = finrank ℝ (mixedSpace K) - 1`. -/
theorem solution :
    _root_.TauCeti.IsLipschitzParametrizable (_root_.Module.finrank ℝ (_root_.NumberField.mixedEmbedding.mixedSpace K) - 1) (_root_.frontier (_root_.NumberField.mixedEmbedding.fundamentalCone.normLeOne K)) := by
  have hcube : _root_.TauCeti.IsLipschitzParametrizable (_root_.NumberField.InfinitePlace.nrComplexPlaces K)
      (_root_.Set.Icc (0 : {w : _root_.NumberField.InfinitePlace K // _root_.NumberField.InfinitePlace.IsComplex w} → ℝ) 1) := by
    simpa using _root_.TauCeti.IsLipschitzParametrizable.image_unitCube_of_contDiffOn
      (d := _root_.NumberField.InfinitePlace.nrComplexPlaces K) (f := _root_.id) _root_.rfl _root_.contDiffOn_id
  -- `rank K + r₂` is the codimension-one dimension: the identity is
  -- `NumberField.rank_add_nrComplexPlaces_add_one`, transported across `mixedEmbedding.finrank`.
  have hdim : _root_.NumberField.Units.rank K + _root_.NumberField.InfinitePlace.nrComplexPlaces K = _root_.Module.finrank ℝ (_root_.NumberField.mixedEmbedding.mixedSpace K) - 1 := by
    rw [_root_.NumberField.mixedEmbedding.finrank, ← _root_.NumberField.rank_add_nrComplexPlaces_add_one K]
    omega
  rw [← hdim]
  refine .mono (.iUnion fun s ↦ .image_of_locallyLipschitz (_root_.NumberField.mixedEmbedding.fundamentalCone.contDiff_liftMap K s).locallyLipschitz
    ((_root_.NumberField.mixedEmbedding.fundamentalCone.isLipschitzParametrizable_frontier_image_paramSet K).prod hcube)) ?_
  exact (_root_.NumberField.mixedEmbedding.fundamentalCone.frontier_normLeOne_subset_preimage K).trans
    (_root_.NumberField.mixedEmbedding.fundamentalCone.preimage_subset_iUnion_image_liftMap K _)

end NumberField.mixedEmbedding.fundamentalCone

end
end
