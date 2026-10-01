-- Prove2me | solution 1 for JewellMRP.GainRate.gain_rate_improvement_identity
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:52:45.992354+00:00
-- url     : https://prove2.me/submissions/a6996048-b084-4c0b-9ef8-52ed4bdcba8f

import Definitions.Def_JewellMRP_GainRate_PolicyIteration
import Mathlib.Tactic

open JewellMRP.GainRate Matrix Finset

namespace CJewell

variable {N : ℕ} [NeZero N] {α : Type*}

theorem duration_pos (M : MRP N α) (z : Fin N → α) (π : Fin N → ℝ)
    (hπ : IsStationaryDist (M.policyMatrix z) π) : 0 < ∑ i, π i * M.ν i (z i) := by
  have hp : ∃ i, 0 < π i := by
    by_contra! h
    have hh := Finset.sum_nonpos (s := Finset.univ) (fun i _ => h i)
    rw [hπ.2.1] at hh
    linarith
  obtain ⟨i, hi⟩ := hp
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hπ.1 j) (M.ν_pos j (z j)).le)
    ⟨i, Finset.mem_univ _, mul_pos hi (M.ν_pos i (z i))⟩

theorem stationary_sum (M : MRP N α) (z : Fin N → α) (π v : Fin N → ℝ)
    (hπ : IsStationaryDist (M.policyMatrix z) π) :
    ∑ i, π i * (∑ j, M.p i (z i) j * v j) = ∑ i, π i * v i := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have h := congrFun hπ.2.2 j
  change ∑ i, π i * M.p i (z i) j = π j at h
  simpa only [mul_assoc, Finset.sum_mul] using congrArg (fun x : ℝ => x * v j) h

theorem value_gain (M : MRP N α) (z : Fin N → α) (g : ℝ) (v π : Fin N → ℝ)
    (hv : M.SolvesValueDetermination z g v) (hπ : IsStationaryDist (M.policyMatrix z) π) :
    M.gainRate z π = g := by
  have h := congrArg (fun f : Fin N → ℝ => ∑ i, π i * f i) (funext hv.2)
  simp_rw [mul_add, Finset.sum_add_distrib] at h
  rw [stationary_sum M z π v hπ] at h
  have hmul : (∑ i, π i * (g * M.ν i (z i))) = g * ∑ i, π i * M.ν i (z i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hmul] at h
  unfold MRP.gainRate
  apply (div_eq_iff (duration_pos M z π hπ).ne').mpr
  linarith

theorem test_eq_gain (M : MRP N α) (z : Fin N → α) (g : ℝ) (v : Fin N → ℝ)
    (hv : M.SolvesValueDetermination z g v) (i : Fin N) :
    M.testQuantity v i (z i) = g := by
  have h := hv.2 i
  unfold MRP.testQuantity
  have hn := (M.ν_pos i (z i)).ne'
  change M.ν i (z i) ≠ 0 at hn
  field_simp
  nlinarith

theorem time_sum (M : MRP N α) (z : Fin N → α) (π : Fin N → ℝ)
    (hπ : IsStationaryDist (M.policyMatrix z) π) :
    ∑ i, M.timeStationaryProb z π i = 1 := by
  unfold MRP.timeStationaryProb
  simp_rw [div_mul_eq_mul_div, mul_comm (M.ν _ _), ← Finset.sum_div]
  exact div_self (duration_pos M z π hπ).ne'

theorem average_test (M : MRP N α) (z : Fin N → α) (v π : Fin N → ℝ)
    (hπ : IsStationaryDist (M.policyMatrix z) π) :
    ∑ i, M.testQuantity v i (z i) * M.timeStationaryProb z π i = M.gainRate z π := by
  unfold MRP.testQuantity MRP.timeStationaryProb MRP.gainRate
  have heq (i : Fin N) :
      (1 / M.ν i (z i) * (M.ρ i (z i) + ∑ j, M.p i (z i) j * v j - v i)) *
        (M.ν i (z i) / (∑ k, π k * M.ν k (z k)) * π i) =
      (π i * (M.ρ i (z i) + ∑ j, M.p i (z i) j * v j - v i)) /
        (∑ k, π k * M.ν k (z k)) := by
    have hn : M.ν i (z i) ≠ 0 := (M.ν_pos i (z i)).ne'
    field_simp
  simp_rw [heq, ← Finset.sum_div]
  congr 1
  simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [stationary_sum M z π v hπ]
  ring

theorem improvement_identity (M : MRP N α) (zA zB : Fin N → α) (gA : ℝ)
    (vA πA πB : Fin N → ℝ) (hA : M.SolvesValueDetermination zA gA vA)
    (hπA : IsStationaryDist (M.policyMatrix zA) πA)
    (hπB : IsStationaryDist (M.policyMatrix zB) πB) :
    M.gainRate zB πB - M.gainRate zA πA =
      ∑ j, (M.testQuantity vA j (zB j) - M.testQuantity vA j (zA j)) *
        M.timeStationaryProb zB πB j := by
  simp_rw [test_eq_gain M zA gA vA hA, sub_mul, Finset.sum_sub_distrib]
  rw [average_test M zB vA πB hπB, ← Finset.mul_sum, time_sum M zB πB hπB,
    mul_one, value_gain M zA gA vA πA hA hπA]

theorem schweitzer_diff (M : MRP N α) (zA : Fin N → α) (gA : ℝ)
    (vA : Fin N → ℝ) (hA : M.SolvesValueDetermination zA gA vA)
    (j : Fin N) (a : α) :
    (M.schweitzerTestQuantity gA vA j a - M.schweitzerTestQuantity gA vA j (zA j)) /
      M.ν j a = M.testQuantity vA j a - M.testQuantity vA j (zA j) := by
  rw [test_eq_gain M zA gA vA hA]
  have h := hA.2 j
  unfold MRP.schweitzerTestQuantity MRP.testQuantity
  have hn : M.ν j a ≠ 0 := (M.ν_pos j a).ne'
  field_simp
  nlinarith

end CJewell

theorem solution {N : ℕ} [NeZero N] {α : Type*} (M : MRP N α)
    (hM : M.IsErgodic) (zA zB : Fin N → α) (gA : ℝ) (vA : Fin N → ℝ)
    (hA : M.SolvesValueDetermination zA gA vA) (πA πB : Fin N → ℝ)
    (hπA : IsStationaryDist (M.policyMatrix zA) πA)
    (hπB : IsStationaryDist (M.policyMatrix zB) πB) :
    M.gainRate zB πB - M.gainRate zA πA =
        ∑ j, ((M.schweitzerTestQuantity gA vA j (zB j) -
            M.schweitzerTestQuantity gA vA j (zA j)) / M.ν j (zB j)) *
          M.timeStationaryProb zB πB j ∧
      M.gainRate zB πB - M.gainRate zA πA =
        ∑ j, (M.testQuantity vA j (zB j) - M.testQuantity vA j (zA j)) *
          M.timeStationaryProb zB πB j := by
  have h := CJewell.improvement_identity M zA zB gA vA πA πB hA hπA hπB
  refine ⟨?_, h⟩
  simpa only [CJewell.schweitzer_diff M zA gA vA hA] using h
