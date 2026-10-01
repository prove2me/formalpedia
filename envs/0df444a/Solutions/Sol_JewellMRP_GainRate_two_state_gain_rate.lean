-- Prove2me | solution 1 for JewellMRP.GainRate.two_state_gain_rate
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:53:23.409769+00:00
-- url     : https://prove2.me/submissions/4be58b04-cf29-4645-bc10-b1f674ed1f6c

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


open JewellMRP.GainRate Matrix Finset

theorem solution {α : Type*} (M : MRP 2 α) (z : Fin 2 → α)
    (h12 : 0 < M.p 0 (z 0) 1) (h21 : 0 < M.p 1 (z 1) 0) :
    let p12 := M.p 0 (z 0) 1
    let p21 := M.p 1 (z 1) 0
    let ν1 := M.ν 0 (z 0)
    let ν2 := M.ν 1 (z 1)
    let ρ1 := M.ρ 0 (z 0)
    let ρ2 := M.ρ 1 (z 1)
    let g := (p21 * ρ1 + p12 * ρ2) / (ν1 * p21 + ν2 * p12)
    M.SolvesValueDetermination z g ![(ν2 * ρ1 - ν1 * ρ2) / (ν1 * p21 + ν2 * p12), 0] ∧
      ∀ π : Fin 2 → ℝ, IsStationaryDist (M.policyMatrix z) π → M.gainRate z π = g := by
  dsimp only
  have hn0 : 0 < M.ν 0 (z 0) := M.ν_pos 0 (z 0)
  have hn1 : 0 < M.ν 1 (z 1) := M.ν_pos 1 (z 1)
  have hd : 0 < M.ν 0 (z 0) * M.p 1 (z 1) 0 + M.ν 1 (z 1) * M.p 0 (z 0) 1 :=
    add_pos (mul_pos hn0 h21) (mul_pos hn1 h12)
  have hp := M.p_sum_one 0 (z 0)
  simp only [Fin.sum_univ_two] at hp
  have hp00 : M.p 0 (z 0) 0 = 1 - M.p 0 (z 0) 1 := by linarith
  have hvd : M.SolvesValueDetermination z
      ((M.p 1 (z 1) 0 * M.ρ 0 (z 0) + M.p 0 (z 0) 1 * M.ρ 1 (z 1)) /
        (M.ν 0 (z 0) * M.p 1 (z 1) 0 + M.ν 1 (z 1) * M.p 0 (z 0) 1))
      ![(M.ν 1 (z 1) * M.ρ 0 (z 0) - M.ν 0 (z 0) * M.ρ 1 (z 1)) /
        (M.ν 0 (z 0) * M.p 1 (z 1) 0 + M.ν 1 (z 1) * M.p 0 (z 0) 1), 0] := by
    constructor
    · simp [lastState]
    · intro i
      fin_cases i <;> simp [Fin.sum_univ_two, hp00] <;> field_simp [hd.ne'] <;> ring
  exact ⟨hvd, fun π hπ => CJewell.value_gain M z _ _ π hvd hπ⟩
