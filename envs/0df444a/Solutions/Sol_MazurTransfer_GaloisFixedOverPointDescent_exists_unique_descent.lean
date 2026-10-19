-- Prove2me | solution 1 for MazurTransfer.GaloisFixedOverPointDescent.exists_unique_descent
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T22:12:28.70001+00:00
-- url     : https://prove2.me/submissions/d990f321-e2b2-4326-9bdd-dad53ee6af0f

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: fixed points over a Galois extension descend uniquely
as points over the base, preserving the given structure morphism.
Named downstream consumer: rational points of the actual Picard and
injectivity of the algebraic norm Kummer map.
-/
import Definitions.Def_MazurTransfer_GaloisFixedOverPointScalarExtensionData
import Theorems.Thm_MazurTransfer_GaloisFixedSchemePointDescent_exists_descent
noncomputable section
namespace MazurTransfer.GaloisFixedOverPointDescentHelpers20261017
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

end MazurTransfer.GaloisFixedOverPointDescentHelpers20261017
open CategoryTheory AlgebraicGeometry
open MazurTransfer.FieldAutomorphismOverPointAction MazurTransfer.GaloisFixedOverPointDescent
theorem solution {F K : Type} [Field F] [Field K] [Algebra F K]
    {X : Scheme.{0}} (t : X ⟶ Spec (CommRingCat.of F)) [IsGalois F K]
    (b : Over.mk (fieldBase F K) ⟶ Over.mk t)
    (hb : ∀ σ : K ≃ₐ[F] K, fieldAut F K σ ≫ b = b) :
    ∃! a : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ Over.mk t,
      scalarOverMap F K ≫ a = b := by
  obtain ⟨a, ha⟩ := MazurTransfer.GaloisFixedSchemePointDescent.exists_descent F K X b.left
    (fun σ => congrArg Over.Hom.left (hb σ))
  letI : Epi (fieldBase F K) := MazurTransfer.GaloisFixedOverPointDescentHelpers20261017.scalarMap_epi F K
  have hwa : a ≫ t = 𝟙 _ := by
    apply (cancel_epi (fieldBase F K)).mp
    change fieldBase F K ≫ (a ≫ t) = fieldBase F K ≫ 𝟙 _
    rw [← Category.assoc, ha, Category.comp_id]
    exact Over.w b
  let a' : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ Over.mk t := Over.homMk a hwa
  have ha' : scalarOverMap F K ≫ a' = b := by
    apply Over.OverMorphism.ext
    exact ha
  refine ⟨a', ha', ?_⟩
  intro a'' ha''
  apply MazurTransfer.GaloisFixedOverPointDescentHelpers20261017.scalarExtension_injective (K := K) t
  exact ha''.trans ha'.symm

#print axioms solution
