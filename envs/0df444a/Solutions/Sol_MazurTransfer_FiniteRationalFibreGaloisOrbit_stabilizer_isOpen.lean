-- Prove2me | solution 1 for MazurTransfer.FiniteRationalFibreGaloisOrbit.stabilizer_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T23:27:32.019558+00:00
-- url     : https://prove2.me/submissions/515e51df-3be0-4a23-92f1-40ec4d7c5046

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a field-valued preimage of a rational point under a
finite morphism has an open Galois stabilizer. The literal pullback
fibre is used. Named downstream consumer: actual norm kernels and
continuous preimage cocycles.
-/
import Theorems.Thm_MazurTransfer_FiniteSchemeGeometricPointOpenStabilizer_stabilizer_isOpen
import Definitions.Def_MazurTransfer_FieldPointActionsAndNormPreimageDifferenceData
import Definitions.Def_MazurTransfer_GaloisFixedOverPointScalarExtensionData

noncomputable section
namespace MazurTransfer.FiniteRationalFibreGaloisOrbit
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FieldAutomorphismOverPointAction GaloisFixedOverPointDescent
variable (F K : Type) [Field F] [Field K] [Algebra F K] [Algebra.IsIntegral F K]
variable {X Y : Scheme.{0}} (tX : X ⟶ Spec (CommRingCat.of F)) (tY : Y ⟶ Spec (CommRingCat.of F))

abbrev pointAction : MulAction (K ≃ₐ[F] K) (Over.mk (fieldBase F K) ⟶ Over.mk tX) where
  smul := act tX
  one_smul := act_one tX
  mul_smul := act_mul tX

end MazurTransfer.FiniteRationalFibreGaloisOrbit
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTransfer.FieldAutomorphismOverPointAction MazurTransfer.GaloisFixedOverPointDescent
open MazurTransfer.FiniteRationalFibreGaloisOrbit
local instance publicFiniteRationalFibrePointAction20261017
    (F K : Type) [Field F] [Field K] [Algebra F K] {X : Scheme.{0}}
    (tX : X ⟶ Spec (CommRingCat.of F)) :
    MulAction (K ≃ₐ[F] K) (Over.mk (fieldBase F K) ⟶ Over.mk tX) := pointAction F K tX

theorem solution (F K : Type) [Field F] [Field K] [Algebra F K] [Algebra.IsIntegral F K]
    {X Y : Scheme.{0}} (tX : X ⟶ Spec (CommRingCat.of F)) (tY : Y ⟶ Spec (CommRingCat.of F)) (φ : Over.mk tX ⟶ Over.mk tY) [IsFinite φ.left]
    (a : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ Over.mk tY)
    (b : Over.mk (fieldBase F K) ⟶ Over.mk tX) (hb : b ≫ φ = scalarOverMap F K ≫ a) :
    IsOpen {σ : K ≃ₐ[F] K | fieldAut F K σ ≫ b = b} := by
  let T : Scheme := pullback φ.left a.left
  let t : T ⟶ Spec (CommRingCat.of F) := pullback.snd φ.left a.left
  have hbl : b.left ≫ φ.left = fieldBase F K ≫ a.left := congrArg Over.Hom.left hb
  let c : Spec (CommRingCat.of K) ⟶ T := pullback.lift b.left (fieldBase F K) hbl
  have hc : c ≫ t = fieldBase F K := pullback.lift_snd _ _ _
  have hopen : IsOpen {σ : K ≃ₐ[F] K | Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ c = c} :=
    MazurTransfer.FiniteSchemeGeometricPointOpenStabilizer.stabilizer_isOpen F K T t c hc
  have hone : (1 : K ≃ₐ[F] K) ∈
      {σ : K ≃ₐ[F] K | Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ c = c} := by
    have h : Spec.map (CommRingCat.ofHom ((1 : K ≃ₐ[F] K).toRingHom)) = 𝟙 _ :=
      congrArg Over.Hom.left (fieldAut_one F K)
    rw [Set.mem_setOf_eq, h, Category.id_comp]
  have hsubset : {σ : K ≃ₐ[F] K | Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ c = c} ⊆
      {σ : K ≃ₐ[F] K | fieldAut F K σ ≫ b = b} := by
    intro σ hσ
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ b.left = b.left
    have hp := congrArg (fun q : Spec (CommRingCat.of K) ⟶ T => q ≫ pullback.fst φ.left a.left) hσ
    simpa only [c, Category.assoc, pullback.lift_fst] using hp
  change IsOpen (MulAction.stabilizer (K ≃ₐ[F] K) b : Set (K ≃ₐ[F] K))
  apply Subgroup.isOpen_of_mem_nhds
  exact Filter.mem_of_superset (hopen.mem_nhds hone) hsubset

#print axioms solution
