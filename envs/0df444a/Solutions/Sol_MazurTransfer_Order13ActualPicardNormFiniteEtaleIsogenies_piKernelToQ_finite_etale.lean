-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardNormFiniteEtaleIsogenies.piKernelToQ_finite_etale
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T21:31:43.761056+00:00
-- url     : https://prove2.me/submissions/5bf62c88-6896-47af-9fb0-aa24573ce44e

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: finite etaleness of the actual pullback kernel of an
original norm factor on the same rational Picard scheme.
Named downstream consumer: the actual finite norm-kernel module and
nineteen-isogeny descent. The original kernel statement and main proof
are retained; its two factor facts are projections of the accepted
original six-property factor theorem. Official Anthropic FLT geometry
interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKernelSchemesData
import Theorems.Thm_MazurTransfer_Order13ActualPicardNormFiniteEtaleIsogenies_actual_norm_factors_are_finite_etale_surjective

noncomputable section
open CategoryTheory AlgebraicGeometry
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardSchemeNineteenNorm
open MazurTransfer.Order13ActualPicardNormFiniteEtaleIsogenies

namespace MazurTransfer.ActualPiKernelFiniteEtaleHelpers20261017
theorem schemePi_isFinite : IsFinite schemePi.left :=
  (MazurTransfer.Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective).1.1

theorem schemePi_etale : Etale schemePi.left :=
  (MazurTransfer.Order13ActualPicardNormFiniteEtaleIsogenies.actual_norm_factors_are_finite_etale_surjective).1.2.1

end MazurTransfer.ActualPiKernelFiniteEtaleHelpers20261017
open MazurTransfer.ActualPiKernelFiniteEtaleHelpers20261017
theorem solution : IsFinite piKernelToQ ∧ Etale piKernelToQ := by
  letI : IsFinite schemePi.left := schemePi_isFinite
  letI : Etale schemePi.left := schemePi_etale
  change IsFinite (CategoryTheory.Limits.pullback.snd schemePi.left actualPicard.zeroSection) ∧
    Etale (CategoryTheory.Limits.pullback.snd schemePi.left actualPicard.zeroSection)
  exact ⟨inferInstance, inferInstance⟩


#print axioms solution
