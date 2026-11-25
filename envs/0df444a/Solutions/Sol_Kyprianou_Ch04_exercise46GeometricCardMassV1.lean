-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46GeometricCardMassV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T14:44:27.943115+00:00
-- url     : https://prove2.me/submissions/34465bf5-aba8-492e-a5de-527fc1d77dcd

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
    (hmeas : ∀ k : Nat, MeasurableSet
      {omega | ((k + 1 : Nat) : ENat) ≤ (B omega).encard})
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
  have hd : Disjoint (A \ D) D := by
    refine Set.disjoint_left.mpr ?_
    intro omega ha hb
    exact ha.2 hb
  have hu : (A \ D) ∪ D = A := Set.diff_union_of_subset hsub
  have ha := measure_union (μ := P) hd (hmeas (k + 1))
  rw [hu] at ha
  have hmass := measure_congr (μ := P) he
  change P (A \ D) = P {omega | (B omega).ncard = k + 1} at hmass
  rw [hmass] at ha
  have hr := congrArg ENNReal.toReal ha
  rw [ENNReal.toReal_add (measure_ne_top P _) (measure_ne_top P _)] at hr
  change (P A).toReal = _ + (P D).toReal at hr
  have hk : (P A).toReal = (1 - p) ^ k := htail k
  have hk1 : (P D).toReal = (1 - p) ^ (k + 1) := htail (k + 1)
  rw [hk, hk1, pow_succ] at hr
  linarith
