-- Prove2me | solution 1 for OAI.ActualEisensteinCoordinates.odd_residue_iff_not_two_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:36:35.127299+00:00
-- url     : https://prove2.me/submissions/325b0513-015f-4214-bceb-9d8bb90f1e55

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Theorems.Thm_OAI_ActualEisensteinCoordinates_eval_coords
import Theorems.Thm_OAI_ActualEisensteinCoordinates_residue_eval
import Theorems.Thm_OAI_ActualEisensteinCoordinates_residue_mul
section
namespace OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
namespace ShortDraftCusp
variable {R : Type*} [CommRing R]
end ShortDraftCusp
namespace ShortDraftConcretePhase
open ShortDraftTrace
end ShortDraftConcretePhase
namespace ShortDraftGauss
open Complex
open scoped ComplexConjugate
variable {F : Type*} [Field F] [Fintype F]
end ShortDraftGauss
namespace EisensteinRayPhase
end EisensteinRayPhase
namespace ShortDraftSextic
open scoped Classical
variable {R : Type*} [CommRing R]
end ShortDraftSextic
namespace ShortDraftGaussJacobi
open Finset
variable {F : Type*} [Field F] [Fintype F]
end ShortDraftGaussJacobi
namespace ShortDraftQuadraticGauss
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end ShortDraftQuadraticGauss
namespace ShortDraftQuotientPhase
variable {A B : Type*} [CommGroup A] [CommGroup B]
end ShortDraftQuotientPhase
namespace EisensteinEPrimaryPhase
end EisensteinEPrimaryPhase
namespace ShortDraftGaussianPhaseTable
end ShortDraftGaussianPhaseTable
namespace ActualEisensteinCoordinates
private theorem residue_two : residue (2 : O) = (2, 0) := by
  have h : eval 2 0 = (2 : O) := by simp [eval]
  rw [← h, residue_eval]
  norm_num
private theorem not_odd_mul_two (v : EisensteinEPrimaryPhase.Coord) :
    ¬ EisensteinEPrimaryPhase.odd
      (EisensteinEPrimaryPhase.mul (2, 0) v) := by
  decide +revert
private theorem not_odd_cast_zero (v : EisensteinEPrimaryPhase.Coord)
    (h : ¬ EisensteinEPrimaryPhase.odd v) :
    (ZMod.cast v.1 : ZMod 2) = 0 ∧
      (ZMod.cast v.2 : ZMod 2) = 0 := by
  decide +revert
end ActualEisensteinCoordinates
end
end OAI
end

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
open OAI.ActualEisensteinCoordinates
namespace OAI.ActualEisensteinCoordinates
theorem _root_.solution (x : O) :
    EisensteinEPrimaryPhase.odd (residue x) ↔ ¬ (2 : O) ∣ x := by
  constructor
  · intro hx hdiv
    obtain ⟨y, hy⟩ := hdiv
    rw [hy, residue_mul, residue_two] at hx
    exact not_odd_mul_two (residue y) hx
  · intro hdiv
    by_contra hodd
    obtain ⟨ha, hb⟩ := not_odd_cast_zero (residue x) hodd
    have ha' : ((coords x).1 : ZMod 2) = 0 := by
      simpa [residue, ZMod.cast_intCast (by decide : 2 ∣ 4)] using ha
    have hb' : ((coords x).2 : ZMod 2) = 0 := by
      simpa [residue, ZMod.cast_intCast (by decide : 2 ∣ 4)] using hb
    obtain ⟨a, ha2⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (coords x).1 2).mp ha'
    obtain ⟨b, hb2⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (coords x).2 2).mp hb'
    apply hdiv
    refine ⟨eval a b, ?_⟩
    rw [← eval_coords x]
    dsimp [eval]
    rw [ha2, hb2]
    push_cast
    ring
end OAI.ActualEisensteinCoordinates
