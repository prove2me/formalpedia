-- Prove2me | solution 1 for MazurTransfer.FiniteRationalFibreGeometricPoints.finite_preimages
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T22:31:21.030633+00:00
-- url     : https://prove2.me/submissions/1ef34f5e-22ab-4175-b996-4ebfba60ca4b

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: geometric lifts of a rational point under a finite
morphism form a finite type, through the literal pullback fibre.
Named downstream consumer: finite actual norm kernels and preimage fields.
-/
import Definitions.Def_MazurTransfer_GaloisFixedOverPointScalarExtensionData
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_MazurTransfer_FiniteSchemeGeometricPointCardinality_finite_points
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open MazurTransfer.FieldAutomorphismOverPointAction MazurTransfer.GaloisFixedOverPointDescent
theorem solution (F K : Type) [Field F] [Field K] [Algebra F K]
    {X Y : Scheme.{0}} (tX : X ⟶ Spec (CommRingCat.of F)) (tY : Y ⟶ Spec (CommRingCat.of F)) (φ : Over.mk tX ⟶ Over.mk tY) [IsFinite φ.left]
    (a : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ Over.mk tY) :
    Finite {b : Over.mk (fieldBase F K) ⟶ Over.mk tX // b ≫ φ = scalarOverMap F K ≫ a} := by
  let T : Scheme := pullback φ.left a.left
  let t : T ⟶ Spec (CommRingCat.of F) := pullback.snd φ.left a.left
  let encode (b : {b : Over.mk (fieldBase F K) ⟶ Over.mk tX //
      b ≫ φ = scalarOverMap F K ≫ a}) : SchemeHomOver (fieldBase F K) t :=
    ⟨pullback.lift b.val.left (fieldBase F K) (congrArg Over.Hom.left b.property),
      pullback.lift_snd _ _ _⟩
  have hinj : Function.Injective encode := by
    intro b c h
    apply Subtype.ext
    apply Over.OverMorphism.ext
    have hl := congrArg (fun z => z.val ≫ pullback.fst φ.left a.left) h
    dsimp only [encode] at hl
    erw [pullback.lift_fst, pullback.lift_fst] at hl
    exact hl
  letI : Finite (SchemeHomOver (fieldBase F K) t) :=
    MazurTransfer.FiniteSchemeGeometricPointCardinality.finite_points F K T t
  exact Finite.of_injective encode hinj

#print axioms solution
