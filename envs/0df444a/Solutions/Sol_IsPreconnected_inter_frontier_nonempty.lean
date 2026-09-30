-- Prove2me | solution 1 for IsPreconnected.inter_frontier_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:15:47.593542+00:00
-- url     : https://prove2.me/submissions/37f3b242-11e7-4d82-a19c-080d72d00a1e

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Topology.Connected.Basic

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
end TauCeti
section TauCeti
open TauCeti

open Set

section Straddle

variable {X : Type*} [TopologicalSpace X] {S V : Set X}

/-- **A preconnected set that meets both a set and its complement meets its frontier.** If `S` is
preconnected and contains a point of `V` and a point outside `V`, then `S` meets `frontier V`.

Nothing is assumed about `V`; the argument is that `(frontier V)ᶜ` is the union of the two disjoint
open sets `interior V` and `interior Vᶜ`, so a preconnected set missing the frontier is confined to
one of them and therefore cannot straddle `V`. -/
theorem solution (hS : _root_.IsPreconnected S)
    (h₁ : (S ∩ V).Nonempty) (h₂ : (S \ V).Nonempty) : (S ∩ _root_.frontier V).Nonempty := by
  by_contra hcon
  have hsub : S ⊆ _root_.interior V ∪ _root_.interior Vᶜ := by
    rw [← _root_.compl_frontier_eq_union_interior]
    exact fun x hx hxf => hcon ⟨x, hx, hxf⟩
  have hdisj : _root_.Disjoint (_root_.interior V) (_root_.interior Vᶜ) :=
    disjoint_compl_right.mono _root_.interior_subset _root_.interior_subset
  rcases hS.subset_or_subset _root_.isOpen_interior _root_.isOpen_interior hdisj hsub with h | h
  · obtain ⟨x, hxS, hxV⟩ := h₂
    exact hxV (_root_.interior_subset (h hxS))
  · obtain ⟨x, hxS, hxV⟩ := h₁
    exact _root_.interior_subset (h hxS) hxV

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



end OpenInjectiveImage

section FiniteUnion

variable {X : Type*} [TopologicalSpace X]



end FiniteUnion

end TauCeti

end
end
