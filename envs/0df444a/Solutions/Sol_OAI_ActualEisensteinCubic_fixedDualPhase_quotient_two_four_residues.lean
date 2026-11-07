-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.fixedDualPhase_quotient_two_four_residues
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:31:26.064759+00:00
-- url     : https://prove2.me/submissions/ccb3634f-2f23-40b1-b5f3-b3af70065918

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_RationalApproximation
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_AbelPhaseLimit
import Theorems.Thm_OAI_ActualEisensteinCubic_fixedDualPhase_eq_of_mod_two
import Theorems.Thm_OAI_ActualEisensteinCubic_rationalCoordEquiv_apply
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span
import Theorems.Thm_OAI_GaussianShiftedPartition_representative_spec
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


section
namespace OAI
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
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
private theorem sum_zmod_two_square (f : ZMod 2 × ZMod 2 → ℂ) :
    (∑ p : ZMod 2 × ZMod 2, f p) =
      f (0,0) + f (0,1) + f (1,0) + f (1,1) := by
  rw [Fintype.sum_prod_type]
  have hu : (Finset.univ : Finset (ZMod 2)) = {0,1} := rfl
  simp [hu]
  ring
end ActualEisensteinCubic
namespace OscSpecial
open scoped Topology
open Filter
end OscSpecial
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT
end ActualEisensteinCubic
open Filter
open scoped Topology
namespace ActualEisensteinCubic
section
open EisensteinEmbedding ConcreteTraceCRT Complex
end
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
end
end OAI
end

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
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (c : O) :
    letI : Finite (O ⧸ Ideal.span {(2 : O)}) :=
      finite_quotient_span (by norm_num : (2 : O) ≠ 0)
    letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
    (∑ r : O ⧸ Ideal.span {(2 : O)},
      fixedDualPhase c (GaussianShiftedPartition.representative 2 r)) =
      fixedDualPhase c (ActualEisensteinCoordinates.eval 0 0) +
      fixedDualPhase c (ActualEisensteinCoordinates.eval 0 1) +
      fixedDualPhase c (ActualEisensteinCoordinates.eval 1 0) +
      fixedDualPhase c (ActualEisensteinCoordinates.eval 1 1) := by
  let h2 : (2 : O) ≠ 0 := by norm_num
  let : Finite (O ⧸ Ideal.span {(2 : O)}) := finite_quotient_span h2
  let : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
  let e := rationalCoordEquiv 2 (by norm_num)
  let P : O ⧸ Ideal.span {(2 : O)} → ℂ :=
    fun r => fixedDualPhase c (GaussianShiftedPartition.representative 2 r)
  have hpoint (p : ZMod 2 × ZMod 2) :
      P (e p) = fixedDualPhase c
        (ActualEisensteinCoordinates.eval (ZMod.cast p.1) (ZMod.cast p.2)) := by
    dsimp only [P]
    apply fixedDualPhase_eq_of_mod_two
    rw [GaussianShiftedPartition.representative_spec]
    exact rationalCoordEquiv_apply 2 (by norm_num) p.1 p.2
  have hsum : (∑ r : O ⧸ Ideal.span {(2 : O)}, P r) =
      ∑ p : ZMod 2 × ZMod 2,
        fixedDualPhase c
          (ActualEisensteinCoordinates.eval (ZMod.cast p.1) (ZMod.cast p.2)) := by
    calc
      (∑ r : O ⧸ Ideal.span {(2 : O)}, P r) =
          ∑ p : ZMod 2 × ZMod 2, P (e p) := (e.sum_comp P).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p hp
        exact hpoint p
  rw [show (∑ r : O ⧸ Ideal.span {(2 : O)},
      fixedDualPhase c (GaussianShiftedPartition.representative 2 r)) =
      ∑ r : O ⧸ Ideal.span {(2 : O)}, P r from rfl]
  rw [hsum, sum_zmod_two_square]
  have hcast1 : (ZMod.cast (1 : ZMod 2) : ℤ) = 1 := by decide
  simp only [ZMod.cast_zero, hcast1]
end OAI.ActualEisensteinCubic
