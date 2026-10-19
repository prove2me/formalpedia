-- Prove2me | solution 1 for MazurTransfer.Order13SameIntegralPicardFamilyRationalReductionMaps.actual_same_integral_picard_family_rational_reduction_maps
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T09:25:18.596212+00:00
-- url     : https://prove2.me/submissions/aacb44e9-8827-4e7f-acd1-bed9bbcd3df8

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: one actual Picard abelian scheme over Z[1/104] has
rational specialization homomorphisms to its mod-three/mod-five groups
of cardinality nineteen; each map is specified by actual local extension.
Named downstream consumer: torsion injectivity and rational torsion bounds.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13SameIntegralPicardFamilyFiniteFibres
import Definitions.Def_MazurTransfer_Order13ActualRationalPicardSpecialization
import Theorems.Thm_MazurTransfer_Order13ActualRationalPicardSpecialization_rationalSpecializationHom_has_integral_lift
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer MazurTransfer.Order13IntegralSections MazurTransfer.Order13IntegralBase
open MazurTransfer.Order13SameIntegralPicardFamilyFiniteFibres
open MazurTransfer.Order13LocalIntegralCoefficientMaps
open MazurTransfer.Order13ActualRationalPicardSpecialization
theorem solution :
    ∃ (D : RelativePic0Designation BaseRing (curveToBase BaseRing))
      (h : RepresentsRelSubPic (curveToBase BaseRing) (positiveInfinitySection BaseRing)
        (algEquivZeroCut (curveToBase BaseRing) (positiveInfinitySection BaseRing)) D),
      AbelianSchemePropertyBundle BaseRing D.toBase ∧
      ∀ (q : ℕ) (hq : q=3 ∨ q=5),
        letI : Fact q.Prime := ⟨by rcases hq with rfl | rfl <;> decide⟩
        let L := (show RepresentsRelSubPic (curveToBase BaseRing) (positiveInfinitySection BaseRing)
          (algEquivZeroGroupCut (curveToBase BaseRing) (positiveInfinitySection BaseRing)).toSubPicCondition
            D from h).relativeGroupLaw
        letI := L.pointGroup (Spec.map (CommRingCat.ofHom canonicalRationalMap))
        letI := L.pointGroup (Spec.map (CommRingCat.ofHom (canonicalFiniteFieldMap q hq)))
        ∃ r : SchemeHomOver (Spec.map (CommRingCat.ofHom canonicalRationalMap)) D.toBase →*
            SchemeHomOver (Spec.map (CommRingCat.ofHom (canonicalFiniteFieldMap q hq))) D.toBase,
          Finite (SchemeHomOver (Spec.map (CommRingCat.ofHom (canonicalFiniteFieldMap q hq))) D.toBase) ∧
          Nat.card (SchemeHomOver (Spec.map (CommRingCat.ofHom (canonicalFiniteFieldMap q hq))) D.toBase) = 19 ∧
          ∀ a, ∃ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (localBaseMap q hq))) D.toBase,
            Spec.map (CommRingCat.ofHom (algebraMap (LocalRing q) ℚ)) ≫ x.val = a.val ∧
            (r a).val = Spec.map (CommRingCat.ofHom (localFiniteFieldMap q)) ≫ x.val := by
  obtain ⟨D,h,hb,hfinite⟩ := actual_same_integral_picard_family_finite_fibres
  refine ⟨D,h,hb,?_⟩
  intro q hq
  letI : Fact q.Prime := ⟨by rcases hq with rfl | rfl <;> decide⟩
  let L := (show RepresentsRelSubPic (curveToBase BaseRing) (positiveInfinitySection BaseRing)
    (algEquivZeroGroupCut (curveToBase BaseRing) (positiveInfinitySection BaseRing)).toSubPicCondition
      D from h).relativeGroupLaw
  letI : IsProper D.toBase := hb.proper
  letI := L.pointGroup (Spec.map (CommRingCat.ofHom canonicalRationalMap))
  letI := L.pointGroup (Spec.map (CommRingCat.ofHom (canonicalFiniteFieldMap q hq)))
  letI : Algebra BaseRing (ZMod q) := (canonicalFiniteFieldMap q hq).toAlgebra
  obtain ⟨hf,hcard⟩ := hfinite q hq
  exact ⟨rationalSpecializationHom q hq D L,hf,hcard,
    fun a => rationalSpecializationHom_has_integral_lift q hq D L a⟩
#print axioms solution
