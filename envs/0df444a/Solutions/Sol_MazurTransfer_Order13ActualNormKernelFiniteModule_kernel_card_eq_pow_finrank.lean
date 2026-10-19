-- Prove2me | solution 1 for MazurTransfer.Order13ActualNormKernelFiniteModule.kernel_card_eq_pow_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T22:58:54.170988+00:00
-- url     : https://prove2.me/submissions/50103c9a-20d0-4079-9fcb-169799bfab15

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual geometric norm kernels are finite groups,
and their exponent nineteen makes them finite modules over F19.
Named downstream consumer: finite splitting fields and Galois module
structure needed for the actual norm Selmer bound.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelFiniteF19ModuleWithOriginalExponentFactsData20261017
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardNormKummerCocycles
open Order13ActualPicardNormKernelGaloisAction Order13ActualPicardGaloisFixedPointDescent
open scoped CategoryTheory.MonObj
local instance actualNormKernelCardF19Provider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualNormKernelCardF19Provider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
open MazurTransfer.Order13ActualNormKernelFiniteModule
local instance actualNormKernelCardFiniteProvider20261017 (K : Type) [Field K] [CharZero K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] :
    Finite (Kernel K φ) := kernel_finite K φ
local instance actualNormKernelCardModuleProvider20261017 (K : Type) [Field K] [CharZero K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] : Module (ZMod 19) (Additive (Kernel K φ)) := kernelZModModule K φ
local instance actualNormKernelCardPrimeProvider20261017 : Fact (Nat.Prime 19) := ⟨by decide⟩
theorem solution (K : Type) [Field K] [CharZero K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left]
    [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] :
    Nat.card (Kernel K φ) = 19 ^ Module.finrank (ZMod 19) (Additive (Kernel K φ)) := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 19) (V := Additive (Kernel K φ))
  rw [Nat.card_zmod] at h
  exact (Nat.card_congr (show Kernel K φ ≃ Additive (Kernel K φ) from
    ⟨Additive.ofMul, Additive.toMul, fun _ => rfl, fun _ => rfl⟩)).trans h

#print axioms solution
