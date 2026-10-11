-- Prove2me | solution 1 for MazurTransfer.affine_open_chart_function_field_is_fraction_ring
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T13:23:21.928981+00:00
-- url     : https://prove2.me/submissions/85a97a10-d58b-4627-8f70-e84980ab32b4

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: an integral affine open chart supplies its actual coordinate
algebra as a fraction-ring base for the scheme's existing function field.
Named downstream consumer: the two order-13 chart embeddings and the Pell
principal divisor. This constructs the maps from the open immersion's stalk
isomorphism at the generic point, without a supplied field equivalence.
-/
import Mathlib

noncomputable section
universe u
namespace MazurTransfer.PublicAffineOpenChartFieldProof
open AlgebraicGeometry CategoryTheory
variable (A : CommRingCat.{u}) [IsDomain A] {X : Scheme.{u}} [IsIntegral X]
    (j : Spec A ⟶ X) [IsOpenImmersion j]

def functionFieldIso : X.functionField ≅ (Spec A).functionField :=
  eqToIso (congrArg X.presheaf.stalk (genericPoint_eq_of_isOpenImmersion j).symm) ≪≫
    asIso (j.stalkMap (genericPoint (Spec A)))

def coordinateEmbedding : A →+* X.functionField :=
  (functionFieldIso A j).inv.hom.comp (algebraMap A (Spec A).functionField)

def coordinateAlgebra : Algebra A X.functionField := (coordinateEmbedding A j).toAlgebra

theorem coordinateEmbedding_injective : Function.Injective (coordinateEmbedding A j) :=
  (ConcreteCategory.bijective_of_isIso (functionFieldIso A j).inv).1.comp
    (IsFractionRing.injective A (Spec A).functionField)

theorem coordinate_isFractionRing :
    letI := coordinateAlgebra A j
    IsFractionRing A X.functionField := by
  letI := coordinateAlgebra A j
  apply IsFractionRing.of_algEquiv (R := A) (K := (Spec A).functionField)
  refine AlgEquiv.ofRingEquiv (f := (functionFieldIso A j).symm.commRingCatIsoToRingEquiv) ?_
  intro a
  rfl

end MazurTransfer.PublicAffineOpenChartFieldProof

open AlgebraicGeometry CategoryTheory

theorem solution
    (A : CommRingCat.{u}) [IsDomain A] {X : Scheme.{u}} [IsIntegral X]
    (j : Spec A ⟶ X) [IsOpenImmersion j] :
    ∃ φ : A →+* X.functionField,
      Function.Injective φ ∧ (letI := φ.toAlgebra; IsFractionRing A X.functionField) := by
  refine ⟨MazurTransfer.PublicAffineOpenChartFieldProof.coordinateEmbedding A j,
    MazurTransfer.PublicAffineOpenChartFieldProof.coordinateEmbedding_injective A j, ?_⟩
  exact MazurTransfer.PublicAffineOpenChartFieldProof.coordinate_isFractionRing A j

#print axioms solution
