-- Prove2me | solution 1 for MazurTransfer.order13_actual_place_of_point_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T02:47:53.438792+00:00
-- url     : https://prove2.me/submissions/51fd2306-8521-4915-baab-a138a80bc7d9

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Exact place-bijection proof from the checked actual good-characteristic
curve foundation. Original official Anthropic FLT dependencies retain
Apache-2.0 and commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Design boundary: closed points of the actual curve identify bijectively
with places of its actual function field. Named downstream consumer:
construction of the actual CurveModel for Abel-Jacobi injectivity. -/
import Definitions.Def_MazurTransfer_Order13GoodCharacteristicPlaceFoundation
import Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
universe u
variable (K : Type u) [Field K] [Fact ((104 : K) ≠ 0)]
theorem solution : Function.Bijective (actualPlaceOfPoint K) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact _root_.AlgebraicCurve.eq_of_range_stalk_eq (curveToBase K) x.1 y.1
      (by rw [actualPlaceOfPoint_stalk_range, actualPlaceOfPoint_stalk_range, hxy])
  · intro v
    obtain ⟨x, hx, hrange⟩ :=
      _root_.AlgebraicCurve.exists_closedPoint_range_stalk_eq (curveToBase K) v
    refine ⟨⟨x, mem_closedPoints_iff.mpr hx⟩, Place.ext ?_⟩
    apply ValuationSubring.toSubring_injective
    rw [← actualPlaceOfPoint_stalk_range, hrange]
#print axioms solution
