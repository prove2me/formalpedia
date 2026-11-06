-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.sixth_power_rows_in_rowNormBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:48:57.064928+00:00
-- url     : https://prove2.me/submissions/3d3bc61a-581a-47b0-9886-794f765c43b0

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Theorems.Thm_OAI_ActualEisensteinCubic_sixth_power_rows_within_norm_cutoff
import Theorems.Thm_OAI_ShortDraftLatticeCount_mem_rowNormBall_of_absNorm_le

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
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    {β : Type*} (selected : Finset β) (p : β → O)
    (D H : ℕ) (hD : 1 ≤ D)
    (hupper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (D : ℝ) ^ (11 / 60 : ℝ))
    (hH : (D : ℝ) ^ (11 / 10 : ℝ) ≤ (H : ℝ)) :
    selected.image (fun i => p i ^ 6) ⊆
      ShortDraftLatticeCount.rowNormBall H := by
  apply sixth_power_rows_within_norm_cutoff selected p
    (ShortDraftLatticeCount.rowNormBall H) D hD hupper
  intro u hu
  apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le H
  exact_mod_cast hu.trans hH
end OAI.ActualEisensteinCubic
