-- Prove2me | solution 1 for MazurTransfer.order13_actual_tensorUnit_curveEulerChar
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T14:18:36.730304+00:00
-- url     : https://prove2.me/submissions/bc6986f6-597e-4e6b-be1a-987949ef8667

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.

Design boundary: every base-field point of the actual order-13 represented
Picard scheme has a genuine degree-zero arithmetic divisor presentation.
Named downstream consumer: the map to the computed function-field Pic0 over
F₃ and F₅, followed by its still-required injectivity and surjectivity proofs.
Curve source: MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c.
Presentation, sheaf and Picard interfaces: official Anthropic FLT at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Theorems.Thm_MazurTransfer_FieldDivisorComparison_riemannRoch_of_constantsAreBase
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero
import Definitions.Def_MazurTransfer_Order13PublicFunctionFieldInvariants
import Definitions.Def_MazurTransfer_LineBundleGeometricDegreeZeroData
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.LineBundleFieldComparison

theorem solution
    (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
    (𝒱 : (curveScheme K).TwoAffineOpenCover) :
    curveEulerChar (curveToBase K) 𝒱 (𝟙_ (curveScheme K).Modules) = -1 := by
  obtain ⟨φ, _, hnat, hsmul, hinj, hrange⟩ :=
    Scheme.Modules.exists_unit_range_eq_lSpaceOn_zero (curveToBase K)
  obtain ⟨_, _, _, _, hχ⟩ :=
    MazurTransfer.FieldDivisorComparison.riemannRoch_of_constantsAreBase 𝒱 (curveToBase K)
      (actual_constantsAreBase_good_characteristic K) (𝟙_ (curveScheme K).Modules) 0
      φ hnat hsmul hinj hrange
  rw [actual_genusFF_eq_two_good_characteristic K] at hχ
  change curveEulerChar (curveToBase K) 𝒱 (𝟙_ (curveScheme K).Modules) = _ at hχ
  simpa using hχ

#print axioms solution
