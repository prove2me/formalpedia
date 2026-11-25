-- Prove2me | solution 1 for GlobalTheory.log_pi_sub_log_latticeNormDisc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:59:56.24006+00:00
-- url     : https://prove2.me/submissions/b1f92046-e8c0-4dfc-96f2-c19e06a6dab6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SumLogNormEmbeddingEqFinrankMulLogAbsNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MeanLogCovolumeEqMeanClassGroup
import Theorems.Thm_GlobalTheory_latticeNormDisc_eq
import Theorems.Thm_GlobalTheory_latticeNormDisc_pos
import Theorems.Thm_GlobalTheory_IsHomothetic_latticeNormDisc_eq
import Theorems.Thm_GlobalTheory_latticeNormDisc_eq_eta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex NumberField
open scoped nonZeroDivisors Real UpperHalfPlane
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {L : PeriodPair} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
    (h : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x) :
    Real.log π - Real.log (|(L.ω₁ * starRingEnd ℂ L.ω₂).im| ^ 6 *
        ‖L.g₂ ^ 3 - 27 * L.g₃ ^ 2‖) / 6 =
      -Real.log (4 * π * τ.im * ‖ModularForm.eta τ‖ ^ 4) := by
  have hpos := latticeNormDisc_pos L
  rw [← latticeNormDisc_eq]
  rw [latticeNormDisc_eq_eta ha h] at hpos ⊢
  have hne : 4 * π * τ.im * ‖ModularForm.eta τ‖ ^ 4 ≠ 0 := by
    intro h0
    rw [show 4 * π ^ 2 * τ.im * ‖ModularForm.eta τ‖ ^ 4 =
      π * (4 * π * τ.im * ‖ModularForm.eta τ‖ ^ 4) by ring, h0] at hpos
    simp at hpos
  rw [Real.log_pow, show 4 * π ^ 2 * τ.im * ‖ModularForm.eta τ‖ ^ 4 =
      π * (4 * π * τ.im * ‖ModularForm.eta τ‖ ^ 4) by ring, Real.log_mul Real.pi_ne_zero hne]
  push_cast
  ring
end GlobalTheory
