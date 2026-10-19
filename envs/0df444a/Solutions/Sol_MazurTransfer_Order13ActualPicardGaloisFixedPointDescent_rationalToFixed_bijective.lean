-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardGaloisFixedPointDescent.rationalToFixed_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T22:27:25.070913+00:00
-- url     : https://prove2.me/submissions/7f1bb802-0c92-44d9-878c-207590788c95

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: rational points of the SAME represented Picard are
exactly its Galois-fixed geometric points, with their actual group law.
Named downstream consumer: algebraic norm Kummer injectivity.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardRationalFixedPointGroupData
import Definitions.Def_MazurTransfer_GaloisFixedOverPointScalarExtensionData
import Theorems.Thm_MazurTransfer_Order13ActualPicardGaloisFixedPointDescent_fixed_point_descends
noncomputable section
namespace MazurTransfer.ActualPicardRationalFixedBijectionScalarHelpers20261017
open CategoryTheory AlgebraicGeometry
open MazurTransfer.FieldAutomorphismOverPointAction MazurTransfer.GaloisFixedOverPointDescent
variable (F K : Type) [Field F] [Field K] [Algebra F K]

theorem scalarMap_epi : Epi (fieldBase F K) := by
  letI : Surjective (fieldBase F K) := ⟨fun y => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective (fieldBase F K)

variable {F K} {X : Scheme.{0}} (t : X ⟶ Spec (CommRingCat.of F))

theorem scalarExtension_injective : Function.Injective
    (fun a : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ Over.mk t => scalarOverMap F K ≫ a) := by
  letI : Epi (fieldBase F K) := scalarMap_epi F K
  intro a a' h
  apply Over.OverMorphism.ext
  apply (cancel_epi (fieldBase F K)).mp
  exact congrArg Over.Hom.left h

end MazurTransfer.ActualPicardRationalFixedBijectionScalarHelpers20261017
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualRationalFixedBijectionProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualRationalFixedBijectionProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualRationalFixedBijectionProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualRationalFixedBijectionProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open MazurTransfer.Order13ActualPicardGaloisFixedPointDescent
namespace MazurTransfer.ActualPicardRationalFixedBijectionPointHelpers20261017
variable (K : Type) [Field K] [CharZero K]
theorem rationalPoint_injective : Function.Injective (rationalPoint K) :=
  MazurTransfer.ActualPicardRationalFixedBijectionScalarHelpers20261017.scalarExtension_injective (K := K) actualPicard.toBase

end MazurTransfer.ActualPicardRationalFixedBijectionPointHelpers20261017
theorem solution (K : Type) [Field K] [CharZero K] [IsGalois ℚ K] : Function.Bijective (rationalToFixed K) := by
  constructor
  · intro a a' h
    apply MazurTransfer.ActualPicardRationalFixedBijectionPointHelpers20261017.rationalPoint_injective K
    exact congrArg Subtype.val h
  · intro b
    obtain ⟨a, ha, -⟩ := fixed_point_descends K b.val b.property
    exact ⟨a, Subtype.ext ha⟩

#print axioms solution
