-- Prove2me | solution 1 for GlobalTheory.latticeNormDisc_eq_eta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:22:51.284626+00:00
-- url     : https://prove2.me/submissions/6e7678bb-e7ce-47d2-8f3b-c3c1eddc9938

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SumLogNormEmbeddingEqFinrankMulLogAbsNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MeanLogCovolumeEqMeanClassGroup
import Theorems.Thm_GlobalTheory_latticeNormDisc_eq
import Theorems.Thm_GlobalTheory_IsHomothetic_latticeNormDisc_eq
import Theorems.Thm_GlobalTheory_invariants_of_periods_eq
import Theorems.Thm_GlobalTheory_mem_lattice_iff_of_periods_eq


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
    latticeNormDisc L = (4 * π ^ 2 * τ.im * ‖ModularForm.eta τ‖ ^ 4) ^ 6 := by
  have hp : ((periodsOfUpperHalfPlane τ).ω₁ = 1 ∧ (periodsOfUpperHalfPlane τ).ω₂ = τ) ∨
      ((periodsOfUpperHalfPlane τ).ω₁ = τ ∧ (periodsOfUpperHalfPlane τ).ω₂ = 1) := by
    simp [periodsOfUpperHalfPlane]
  have H : IsHomothetic a (periodsOfUpperHalfPlane τ) L := by
    intro x
    rw [h, mem_lattice_iff_of_periods_eq hp]
    simp [ha]
  rw [H.latticeNormDisc_eq, latticeNormDisc, latticeArea_periodsOfUpperHalfPlane,
    (invariants_of_periods_eq hp).2.1]
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Complex.norm_ofNat]
  ring
end GlobalTheory
