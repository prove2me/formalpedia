-- Prove2me | solution 1 for MazurTransfer.order13_actual_mixed_whole_curve_basechange_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T05:00:39.14938+00:00
-- url     : https://prove2.me/submissions/c0d272c6-6e5f-4d09-b7a6-0b8605e65d57

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapted from the complete checked Order13WholeCurveBaseChangeIsomorphism proof,
with the actual mixed quadratic rings and gluing object throughout.
Design boundary: for arbitrary commutative base rings, the whole literal
order-thirteen glued curve over the new ring is the scheme-theoretic base
change of the original curve. Named downstream consumer: the compatible
actual integral curve family and its Picard family used in good reduction.
No chart dictionary, isomorphism, or fibre compatibility is assumed.
-/
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalWholeCurveBaseChangeData20261019
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MazurTransfer
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve Order13MixedQuadraticCoefficientBaseChange Order13MixedQuadraticAffineBaseChange Order13MixedQuadraticActualCurveBaseChange
universe u
namespace MazurTransfer.Order13OriginalMixedWholeCurveBaseChangeInterface20261019
end MazurTransfer.Order13OriginalMixedWholeCurveBaseChangeInterface20261019
theorem solution : (∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S],
    IsPullback (curveMap R S) (curveToBase S) (curveToBase R)
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))) ∧ (∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S],
    (wholeCurveBaseChangeIso R S).inv = curveBaseChangeLift R S) ∧ (∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S], IsIso (curveBaseChangeLift R S)) ∧ (∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S],
    (wholeCurveBaseChangeIso R S).inv ≫ pullback.fst _ _ = curveToBase S) ∧ (∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S],
    (wholeCurveBaseChangeIso R S).inv ≫ pullback.snd _ _ = curveMap R S) := by
  exact ⟨wholeCurve_isPullback,wholeCurveBaseChangeIso_inv_eq,curveBaseChangeLift_isIso,wholeCurveBaseChangeIso_inv_fst,wholeCurveBaseChangeIso_inv_snd⟩
#print axioms solution
