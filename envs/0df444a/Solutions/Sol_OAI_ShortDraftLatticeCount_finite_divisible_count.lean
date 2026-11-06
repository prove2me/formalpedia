-- Prove2me | solution 1 for OAI.ShortDraftLatticeCount.finite_divisible_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:23:53.909686+00:00
-- url     : https://prove2.me/submissions/580a317c-0fa8-455a-a697-6e84e2bb3b34

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Theorems.Thm_OAI_ShortDraftLatticeCount_finite_multiples_count
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
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
open OAI.ShortDraftLatticeCount
open ActualEisensteinCoordinates
namespace OAI.ShortDraftLatticeCount
theorem _root_.solution
    (p : O) (hp : p ≠ 0) (S : Finset O) (D : ℕ)
    (hdiv : ∀ n ∈ S, p ∣ n)
    (hnorm : ∀ n ∈ S, qNat n ≤ D) :
    S.card ≤ 64 * (D / qNat p + 1) := by
  classical
  let quotient : (x : {n : O // n ∈ S}) → O :=
    fun x => Classical.choose (hdiv x.1 x.2)
  have hrep : ∀ x : {n : O // n ∈ S}, x.1 = p * quotient x := by
    intro x
    exact Classical.choose_spec (hdiv x.1 x.2)
  have hinj : Function.Injective quotient := by
    intro x y hxy
    apply Subtype.ext
    calc
      x.1 = p * quotient x := hrep x
      _ = p * quotient y := by rw [hxy]
      _ = y.1 := (hrep y).symm
  let T : Finset O := S.attach.image quotient
  have hcard : T.card = S.card := by
    simpa [T] using Finset.card_image_of_injective S.attach hinj
  have hT : ∀ m ∈ T, qNat (p * m) ≤ D := by
    intro m hm
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hm
    rw [← hrep x]
    exact hnorm x.1 x.2
  calc
    S.card = T.card := hcard.symm
    _ ≤ 64 * (D / qNat p + 1) := finite_multiples_count p hp T D hT
end OAI.ShortDraftLatticeCount
