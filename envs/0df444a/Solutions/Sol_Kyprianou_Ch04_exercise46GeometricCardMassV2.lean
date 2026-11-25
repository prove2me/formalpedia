-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46GeometricCardMassV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T17:21:16.356578+00:00
-- url     : https://prove2.me/submissions/2082ac7f-ef14-46db-b33b-6774c10cb369

import Mathlib
open MeasureTheory Filter Set
open scoped ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega T : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (B : Omega → Set T) (p : Real) (hp : 0 < p) (hp1 : p < 1)
    (htail : ∀ k : Nat,
      (P {omega | ((k + 1 : Nat) : ENat) ≤ (B omega).encard}).toReal =
        (1 - p) ^ k)
    (hmeas : ∀ k : Nat, ∃ S : Set Omega, MeasurableSet S ∧
      S =ᵐ[P] {omega | ((k + 1 : Nat) : ENat) ≤ (B omega).encard})
    (hfinite : ∀ᵐ omega ∂P, (B omega).Finite) :
    ∀ k : Nat, (P {omega | (B omega).ncard = k + 1}).toReal =
      p * (1 - p) ^ k := by
  intro k
  let A : Set Omega := {omega | ((k + 1 : Nat) : ENat) ≤ (B omega).encard}
  let D : Set Omega := {omega | ((k + 1 + 1 : Nat) : ENat) ≤ (B omega).encard}
  have hsub : D ⊆ A := by
    intro omega ho
    change ((k + 1 + 1 : Nat) : ENat) ≤ (B omega).encard at ho
    change ((k + 1 : Nat) : ENat) ≤ (B omega).encard
    have hstep : ((k + 1 : Nat) : ENat) ≤ ((k + 1 + 1 : Nat) : ENat) := by
      exact_mod_cast Nat.le_succ (k + 1)
    exact hstep.trans ho
  have he : (A \ D) =ᵐ[P] {omega | (B omega).ncard = k + 1} := by
    filter_upwards [hfinite] with omega hf
    change ((((k + 1 : Nat) : ENat) ≤ (B omega).encard) ∧
      ¬ (((k + 1 + 1 : Nat) : ENat) ≤ (B omega).encard)) =
      ((B omega).ncard = k + 1)
    rw [← hf.cast_ncard_eq]
    simp only [ENat.coe_le_coe]
    exact propext (by omega)
  obtain ⟨S, hS, hSD⟩ := hmeas (k + 1)
  have hSD' : S =ᵐ[P] D := hSD
  have hd : Disjoint (A \ S) S := Set.disjoint_left.mpr fun _ ha hs => ha.2 hs
  have hu : (((A \ S) ∪ S : Set Omega)) =ᵐ[P] A := by
    filter_upwards [hSD'] with omega h
    change (omega ∈ A ∧ omega ∉ S ∨ omega ∈ S) = (omega ∈ A)
    change (omega ∈ S) = (omega ∈ D) at h
    rw [h]
    exact propext (by have hs : omega ∈ D → omega ∈ A := fun hD => hsub hD; tauto)
  have he' : (A \ S) =ᵐ[P] (A \ D) := by
    filter_upwards [hSD'] with omega h
    change (omega ∈ A ∧ omega ∉ S) = (omega ∈ A ∧ omega ∉ D)
    change (omega ∈ S) = (omega ∈ D) at h
    rw [h]
  have ha := measure_union (μ := P) hd hS
  have hU := measure_congr (μ := P) hu
  have hM := measure_congr (μ := P) (he'.trans he)
  have hD := measure_congr (μ := P) hSD'
  change P ((A \ S) ∪ S) = P A at hU
  change P (A \ S) = P {omega | (B omega).ncard = k + 1} at hM
  change P S = P D at hD
  have heq : P A = P {omega | (B omega).ncard = k + 1} + P D :=
    hU.symm.trans (ha.trans (congrArg₂ (· + ·) hM hD))
  have hr := congrArg ENNReal.toReal heq
  rw [ENNReal.toReal_add (measure_ne_top P _) (measure_ne_top P _)] at hr
  change (P A).toReal = _ + (P D).toReal at hr
  have hk : (P A).toReal = (1 - p) ^ k := htail k
  have hk1 : (P D).toReal = (1 - p) ^ (k + 1) := htail (k + 1)
  rw [hk, hk1, pow_succ] at hr
  linarith
