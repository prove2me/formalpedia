-- Prove2me | solution 1 for MazurTransfer.order13_actual_mixed_quadratic_curve_proper
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T04:28:05.288448+00:00
-- url     : https://prove2.me/submissions/af058d05-275d-4068-a613-52ba8a5c4a75

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Copyright (c) 2026 Vas and contributors.
Released under Apache-2.0. Authors: Vasily Ilin.
Complete gluing, preimage, finite-morphism and properness proofs adapted
from the pinned WIP-compatible XOneThirteenHyperellipticMap.lean.
The coefficient ring is an arbitrary commutative ring, with no field or
characteristic restriction. No Noetherianity conclusion is asserted for
an arbitrary base ring. The independent adaptation uses the campaign
Mathlib pin and does not alter the core or separate Tau Ceti package pins.
Design boundary: the actual whole integral hyperelliptic map is finite,
and the actual glued mixed quadratic curve is proper over its base ring.
Named downstream consumer: the actual smooth proper integral curve family
and its compatible Picard family at two.
This file changes the affine equations and gluing object explicitly; it
does not assert a whole rational-fibre comparison with the old curve.
-/
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalFiniteHyperellipticMapAndProperCurveDataDistinctProjectiveLineNamespaceV320261019
noncomputable section
open CategoryTheory AlgebraicGeometry MazurTransfer
open Order13MixedQuadraticGluedCurve
universe u
namespace MazurTransfer.ActualMixedQuadraticCurveProperOriginalInterface20261019
end MazurTransfer.ActualMixedQuadraticCurveProperOriginalInterface20261019
theorem solution : ∀ (R : Type u) [CommRing R], IsProper (curveToBase R) := by
  exact MazurTransfer.Order13MixedQuadraticProperCurve.curveToBase_isProper
#print axioms solution
