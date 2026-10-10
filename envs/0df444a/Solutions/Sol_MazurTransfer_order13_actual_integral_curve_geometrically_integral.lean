-- Prove2me | solution 1 for MazurTransfer.order13_actual_integral_curve_geometrically_integral
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T02:34:23.943111+00:00
-- url     : https://prove2.me/submissions/37818b57-79b8-4681-bc5b-549ddd009336

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: geometric integrality of the actual integral curve,
using accepted whole-curve base change and actual good-characteristic
field geometry. Named downstream consumer: integral Picard representability.
No fibre identifications or geometric-integrality hypotheses are supplied.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometry_and_finite_field_points
import Theorems.Thm_MazurTransfer_order13_actual_whole_curve_base_change_isomorphism

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve

theorem solution.{u}
    (R : Type u) [CommRing R] (h104 : IsUnit (104 : R)) :
    GeometricallyIntegral (curveToBase R) := by
  constructor
  intro K _ y Z fst snd hp
  let f : R →+* K := (Spec.preimage y).hom
  letI : Algebra R K := f.toAlgebra
  have hy : Spec.map (CommRingCat.ofHom (algebraMap R K)) = y :=
    Spec.map_preimage y
  have hu : IsUnit (104 : K) := by
    simpa only [map_ofNat] using h104.map f
  letI : IsIntegral (curveScheme K) :=
    (MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1 K hu.ne_zero).1
  obtain ⟨e, φA, φB, he⟩ :=
    MazurTransfer.order13_actual_whole_curve_base_change_isomorphism R K
  have hpf : IsPullback snd fst y (curveToBase R) := hp.flip
  rw [← hy] at hpf
  exact IsIntegral.of_isIso (hpf.isoPullback ≪≫ e).inv

#print axioms solution
