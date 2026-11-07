-- Prove2me | solution 1 for OAI.OscSpecial.dualGaussian_eq_dualVarTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:29:38.726811+00:00
-- url     : https://prove2.me/submissions/74571c10-26d1-4463-841e-4ca7db84fa77

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_RationalApproximation
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_AbelPhaseLimit
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_OscSpecial_dualGaussian_explicit
import Theorems.Thm_OAI_OscSpecial_r_pos
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open OAI.OscSpecial
open scoped Topology
open Filter
namespace OAI.OscSpecial
theorem _root_.solution {η a b : ℝ}
    (hη : 0 < η) (hq : 0 < q a b) (z : ℤ × ℤ) :
    RankTwoComplex.dualGaussian (A η a b) (B η a b) (D η a b) z =
      dualVarTerm η a b z := by
  rw [dualGaussian_explicit hη hq z]
  have hQ :
      ((z.1 : ℂ) ^ 2 + (z.1 : ℂ) * (z.2 : ℂ) + (z.2 : ℂ) ^ 2) =
        (dualQ z : ℂ) := by
    dsimp [dualQ]
    push_cast
    ring
  have hT :
      (((a-b : ℝ) : ℂ) * (z.1 : ℂ) ^ 2 +
        2 * (a : ℂ) * (z.1 : ℂ) * (z.2 : ℂ) +
        (b : ℂ) * (z.2 : ℂ) ^ 2) =
        (dualTrace a b z : ℂ) := by
    dsimp [dualTrace]
    push_cast
    ring
  rw [hQ, hT]
  have hrC : (r η a b : ℂ) ≠ 0 := by
    exact_mod_cast (r_pos hη hq).ne'
  have harg :
      -(Real.pi : ℂ) *
        ((η : ℂ) * (q a b : ℂ) / (4 * (r η a b : ℂ)) *
          (dualQ z : ℂ) +
          Complex.I / (2 * (r η a b : ℂ)) * (dualTrace a b z : ℂ)) =
      (((-Real.pi * (η * q a b / (4 * r η a b)) * dualQ z : ℝ) : ℂ)) +
        Complex.I * ((phaseAngle a b z / r η a b : ℝ) : ℂ) := by
    dsimp [phaseAngle]
    push_cast
    field_simp [hrC]
    ring
  rw [harg, Complex.exp_add, ← Complex.ofReal_exp]
  rfl
end OAI.OscSpecial
