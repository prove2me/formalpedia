-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.qNat_eq_absNorm_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:26:05.234431+00:00
-- url     : https://prove2.me/submissions/9159aa01-ae03-4e4c-915b-f53c1171e7ea

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Theorems.Thm_OAI_ActualEisensteinCubic_algebraNorm_eq_coordinate_norm
import Theorems.Thm_OAI_ShortDraftLatticeCount_qO_nonneg


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
open ActualEisensteinCoordinates ShortDraftLatticeCount
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (p : O) :
    qNat p = Ideal.absNorm (Ideal.span {p}) := by
  rw [Ideal.absNorm_span_singleton, algebraNorm_eq_coordinate_norm]
  unfold qNat
  apply Nat.cast_injective (R := ℤ)
  rw [Int.toNat_of_nonneg (qO_nonneg p),
    Int.natAbs_of_nonneg (qO_nonneg p)]
end OAI.ActualEisensteinCubic
