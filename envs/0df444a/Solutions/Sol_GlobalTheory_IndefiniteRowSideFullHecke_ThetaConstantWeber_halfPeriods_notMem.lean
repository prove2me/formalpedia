-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.halfPeriods_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:25:52.846899+00:00
-- url     : https://prove2.me/submissions/504107f1-4a99-4b96-b340-fb61c40046a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Theorems.Thm_GlobalTheory_mem_lattice_periodPairOfTau


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Polynomial
open UpperHalfPlane hiding I
open scoped Real
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber
open Complex Polynomial
open UpperHalfPlane hiding I
open scoped Real
namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber
theorem _root_.solution (τ : ℍ) :
    (1 / 2 : ℂ) ∉ (_root_.GlobalTheory.periodPairOfTau τ).lattice ∧
      (τ : ℂ) / 2 ∉ (_root_.GlobalTheory.periodPairOfTau τ).lattice ∧
      (1 + (τ : ℂ)) / 2 ∉ (_root_.GlobalTheory.periodPairOfTau τ).lattice := by
  have hpos := τ.im_pos
  refine ⟨?_, ?_, ?_⟩ <;> rw [_root_.GlobalTheory.mem_lattice_periodPairOfTau] <;>
    rintro ⟨m, n, h⟩ <;> have him := congrArg Complex.im h <;> have hre := congrArg Complex.re h <;>
    simp at him hre
  · rcases him with hm' | hm
    · subst hm'
      have h1 : (((2 * n - 1 : ℤ)) : ℝ) = 0 := by push_cast at hre ⊢; linarith
      have h2 : 2 * n - 1 = 0 := by exact_mod_cast h1
      omega
    · linarith
  · have h0 : (((2 * m - 1 : ℤ)) : ℝ) * τ.im = 0 := by push_cast; linarith
    rcases mul_eq_zero.1 h0 with hm | hm
    · have h2 : 2 * m - 1 = 0 := by exact_mod_cast hm
      omega
    · linarith
  · have h0 : (((2 * m - 1 : ℤ)) : ℝ) * τ.im = 0 := by push_cast; linarith
    rcases mul_eq_zero.1 h0 with hm | hm
    · have h2 : 2 * m - 1 = 0 := by exact_mod_cast hm
      omega
    · linarith
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber
end GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber
