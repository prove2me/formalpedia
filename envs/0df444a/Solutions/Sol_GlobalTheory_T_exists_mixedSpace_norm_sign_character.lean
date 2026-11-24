-- Prove2me | solution 1 for GlobalTheory.T.exists_mixedSpace_norm_sign_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:08:09.702968+00:00
-- url     : https://prove2.me/submissions/e2f5f73e-ad03-4bd7-b1fe-c2e446985170

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMixedSpaceNormSignCharacter
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMixedSpaceNormSignCharacterStatement
import Theorems.Thm_GlobalTheory_NormSign_exists_normSign


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (ε : ℂ), ε * ε = 1 → ∃ φ : mixedSpace K → ℂ, (∀ x y, φ (x * y) = φ x * φ y) ∧ (∀ (t : ℝ) x, 0 < t → φ (t • x) = φ x) ∧ ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} ∧ (∀ x, mixedEmbedding.norm x ≠ 0 → ‖φ x‖ = 1) ∧ ∀ β : 𝓞 K, β ≠ 0 → φ (mixedEmbedding K β) = if 0 < Algebra.norm ℤ β then 1 else ε := by
  first | exact @GlobalTheory.NormSign.exists_normSign | exact GlobalTheory.NormSign.exists_normSign | (intros; apply GlobalTheory.NormSign.exists_normSign <;> assumption)
end _root_.GlobalTheory.T
