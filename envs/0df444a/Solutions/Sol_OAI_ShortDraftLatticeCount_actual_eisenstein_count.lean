-- Prove2me | solution 1 for OAI.ShortDraftLatticeCount.actual_eisenstein_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:22:09.624687+00:00
-- url     : https://prove2.me/submissions/84c3f64a-ba11-4b02-9000-5adf1def1a8e

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Theorems.Thm_OAI_ShortDraftLatticeCount_finite_lattice_count_linear
import Theorems.Thm_OAI_ActualEisensteinCoordinates_eval_coords


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
open OAI.ShortDraftLatticeCount
namespace OAI.ShortDraftLatticeCount
theorem _root_.solution
    (S : Finset ActualEisensteinCoordinates.O) (D : ℕ)
    (hS : ∀ x ∈ S, q (ActualEisensteinCoordinates.coords x) ≤ D) :
    S.card ≤ 64 * (D + 1) := by
  have hinj : Function.Injective ActualEisensteinCoordinates.coords := by
    intro x y hxy
    calc
      x = ActualEisensteinCoordinates.eval
          (ActualEisensteinCoordinates.coords x).1
          (ActualEisensteinCoordinates.coords x).2 :=
        (ActualEisensteinCoordinates.eval_coords x).symm
      _ = ActualEisensteinCoordinates.eval
          (ActualEisensteinCoordinates.coords y).1
          (ActualEisensteinCoordinates.coords y).2 := by rw [hxy]
      _ = y := ActualEisensteinCoordinates.eval_coords y
  have himage : (S.image ActualEisensteinCoordinates.coords).card = S.card :=
    Finset.card_image_of_injective S hinj
  have hbound : ∀ v ∈ S.image ActualEisensteinCoordinates.coords,
      q v ≤ D := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    exact hS x hx
  calc
    S.card = (S.image ActualEisensteinCoordinates.coords).card := himage.symm
    _ ≤ 64 * (D + 1) := finite_lattice_count_linear _ D hbound
end OAI.ShortDraftLatticeCount
