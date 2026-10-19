-- Prove2me | solution 1 for MazurTransfer.RationalPlacePicardInjection.pointClass_injective
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T01:36:46.807326+00:00
-- url     : https://prove2.me/submissions/d6aab9de-b3c1-41a2-802f-bd656dbc3b2a

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
The pole and independent-power argument reuses official Anthropic FLT at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0. The original canonical-
differential genus theorem is unchanged; this separate perfect-field bridge
uses the checked Weil-canonical Riemann–Roch formula for genusFF instead.
Design boundary: distinct rational places have distinct Abel–Jacobi divisor
classes on a positive-genus function field. Named downstream consumer: the
literal order-13 rational-point injection into its actual arithmetic Pic0.
-/
import Mathlib
import Definitions.Def_MazurTransfer_RationalPlacePicardPointClass
import Theorems.Thm_MazurTransfer_RationalPlacePicardInjection_genusFF_eq_zero_of_principal_single_sub_single
open AlgebraicCurve Polynomial MazurTransfer.RationalPlacePicardInjection
universe u v

theorem solution {K : Type u} {F : Type v} [Field K] [PerfectField K] [Field F]
    [Algebra K F] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (hC : ConstantsAreBase K F) (hgen : 0 < genusFF K F)
    (Q : {v : AlgebraicCurve.Place K F // v.deg = 1}) :
    Function.Injective (pointClass Q) := by
  intro P R hPR
  apply Subtype.ext
  by_contra hne
  have hp := QuotientAddGroup.eq_iff_sub_mem.mp hPR
  change Divisor.IsPrincipal ((Finsupp.single P.1 1 - Finsupp.single Q.1 1) -
    (Finsupp.single R.1 1 - Finsupp.single Q.1 1)) at hp
  have hpr : Divisor.IsPrincipal (Finsupp.single P.1 1 - Finsupp.single R.1 1) := by
    convert hp using 1 <;> abel
  have hg := genusFF_eq_zero_of_principal_single_sub_single hC hne R.2 hpr
  omega
#print axioms solution
