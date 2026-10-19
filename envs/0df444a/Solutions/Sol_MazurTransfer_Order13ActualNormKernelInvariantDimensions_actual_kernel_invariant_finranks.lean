-- Prove2me | solution 1 for MazurTransfer.Order13ActualNormKernelInvariantDimensions.actual_kernel_invariant_finranks
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T20:19:12.313986+00:00
-- url     : https://prove2.me/submissions/7a4becdb-b76a-4384-910d-b2fa1380e5a3

import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormFiniteEtaleIsogenies_actual_norm_factors_are_finite_etale_surjective
/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the invariant F19-subspaces of the two actual geometric
norm kernels have dimensions zero and one, using genuine rational
fixed-point descent and the exact nineteen torsion counts.
Named downstream consumer: actual kernel Galois module structure and Selmer bounds. -/
import Definitions.Def_MazurTransfer_Order13InvariantFixedEquivalenceOriginalDataAndCardinalityCertificateMinimalPublicNamespacesV220261018
import Theorems.Thm_MazurTransfer_Order13ActualNormKernelFixedPartIdentification_actual_kernel_galois_action_fixed_cards

noncomputable section
open MazurTransfer
open Order13ActualNormKernelInvariantDimensions
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance actualInvariantFinrankOriginalProvider120261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualInvariantFinrankOriginalProvider220261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualInvariantFinrankOriginalProvider320261018 : IsMonHom schemePi := schemePi_isMonHom
local instance actualInvariantFinrankOriginalProvider420261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
local instance actualInvariantFinrankOriginalProvider520261018 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ


open Order13ActualPicardNormAlgebraicCohomology


open Order13ActualNormKernelFiniteModule
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
local instance actualInvariantFinrankOriginalProvider620261018 : Finite (Kernel K φ) := kernel_finite K φ
local instance actualInvariantFinrankOriginalProvider720261018 : Module (ZMod 19) (Additive (Kernel K φ)) := kernelZModModule K φ


open Order13ActualNormKernelF19Representation Order13ActualKernelActionFixedSubgroup
local instance actualInvariantFinrankOriginalProvider820261018 : Fact (Nat.Prime 19) := ⟨by decide⟩
local instance actualInvariantFinrankOriginalProvider920261018 : Module.Finite (ZMod 19) (Additive (Kernel K φ)) := kernel_module_finite K φ

local instance actualInvariantFinrankOriginalProvider1020261018 : IsFinite schemePi.left := Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective.1.1
local instance actualInvariantFinrankOriginalProvider1120261018 : IsFinite schemePiConjugate.left := Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective.2.1
local instance actualInvariantFinrankOriginalProvider1220261018 : Fact (∀ z : Kernel K schemePi, z ^ 19 = 1) := ⟨pi_kernel_exponent_nineteen K⟩
local instance actualInvariantFinrankOriginalProvider1320261018 : Fact (∀ z : Kernel K schemePiConjugate, z ^ 19 = 1) := ⟨piConjugate_kernel_exponent_nineteen K⟩
local instance actualInvariantFinrankOriginalProvider1420261018 : Module (ZMod 19) (Additive (Kernel K schemePi)) := kernelZModModule K schemePi
local instance actualInvariantFinrankOriginalProvider1520261018 : Module (ZMod 19) (Additive (Kernel K schemePiConjugate)) := kernelZModModule K schemePiConjugate

theorem solution (𝒱 : (curveScheme ℚ).TwoAffineOpenCover) :
    Module.finrank (ZMod 19) (kernelRepresentation K schemePi).invariants = 0 ∧
      Module.finrank (ZMod 19) (kernelRepresentation K schemePiConjugate).invariants = 1 := by
  have hc := Order13ActualNormKernelFixedPartIdentification.actual_kernel_galois_action_fixed_cards K 𝒱
  have hp := fixed_card_eq_pow_invariant_finrank K schemePi
  have hb := fixed_card_eq_pow_invariant_finrank K schemePiConjugate
  rw [hc.1] at hp
  rw [hc.2] at hb
  constructor
  · apply Nat.pow_right_injective (by decide : 1 < 19)
    exact hp.symm
  · apply Nat.pow_right_injective (by decide : 1 < 19)
    simpa only [pow_one] using hb.symm

#print axioms solution
