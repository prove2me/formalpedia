-- Prove2me | solution 1 for JewellMRP.GainRate.strict_improvement
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:56:37.237062+00:00
-- url     : https://prove2.me/submissions/b7251d35-1d03-4790-b90a-bb883340a4c3

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

namespace CJewell

variable {N : ℕ} [NeZero N] {α : Type*}

theorem stationary_positive (M : MRP N α) (hM : M.IsErgodic) (z : Fin N → α)
    (π : Fin N → ℝ) (hπ : IsStationaryDist (M.policyMatrix z) π) (j : Fin N) : 0 < π j := by
  obtain ⟨i, hi⟩ : ∃ i, 0 < π i := by
    by_contra! h
    have hh := Finset.sum_nonpos (s := Finset.univ) (fun i _ => h i)
    rw [hπ.2.1] at hh
    linarith
  have hn : ∀ i j, 0 ≤ M.policyMatrix z i j := fun i j => M.p_nonneg i (z i) j
  obtain ⟨n, hn0, hpos⟩ := (Matrix.isIrreducible_iff_exists_pow_pos hn).mp (hM z) i j
  have hpow (n : ℕ) : π ᵥ* (M.policyMatrix z)^n = π := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hπ.2.2]
  have hh := congrFun (hpow n) j
  change ∑ i, π i * ((M.policyMatrix z)^n) i j = π j at hh
  rw [← hh]
  exact Finset.sum_pos' (fun i _ => mul_nonneg (hπ.1 i) (Matrix.pow_apply_nonneg hn n i j))
    ⟨i, Finset.mem_univ _, mul_pos hi hpos⟩

theorem time_positive (M : MRP N α) (hM : M.IsErgodic) (z : Fin N → α)
    (π : Fin N → ℝ) (hπ : IsStationaryDist (M.policyMatrix z) π) (j : Fin N) :
    0 < M.timeStationaryProb z π j :=
  mul_pos (div_pos (M.ν_pos j (z j)) (duration_pos M z π hπ))
    (stationary_positive M hM z π hπ j)

theorem strict_improvement (M : MRP N α) (hM : M.IsErgodic) (z₁ z₂ : Fin N → α)
    (g₁ : ℝ) (v₁ : Fin N → ℝ) (h₁ : M.SolvesValueDetermination z₁ g₁ v₁)
    (hstep : M.IsImprovementStep z₁ v₁ z₂) (hne : z₂ ≠ z₁) (π₁ π₂ : Fin N → ℝ)
    (hπ₁ : IsStationaryDist (M.policyMatrix z₁) π₁)
    (hπ₂ : IsStationaryDist (M.policyMatrix z₂) π₂) :
    M.gainRate z₁ π₁ < M.gainRate z₂ π₂ := by
  have hnon (i : Fin N) : 0 ≤ M.testQuantity v₁ i (z₂ i) - M.testQuantity v₁ i (z₁ i) :=
    sub_nonneg.mpr ((hstep i).1 (z₁ i))
  obtain ⟨i, hi⟩ : ∃ i, z₂ i ≠ z₁ i := by
    by_contra! h
    exact hne (funext h)
  have hstrict : M.testQuantity v₁ i (z₁ i) < M.testQuantity v₁ i (z₂ i) := by
    apply lt_of_le_of_ne ((hstep i).1 (z₁ i))
    intro heq
    apply hi
    apply (hstep i).2
    intro a
    rw [heq]
    exact (hstep i).1 a
  have hs : 0 < ∑ j, (M.testQuantity v₁ j (z₂ j) - M.testQuantity v₁ j (z₁ j)) *
      M.timeStationaryProb z₂ π₂ j :=
    Finset.sum_pos' (fun j _ => mul_nonneg (hnon j) (time_positive M hM z₂ π₂ hπ₂ j).le)
      ⟨i, Finset.mem_univ _, mul_pos (sub_pos.mpr hstrict) (time_positive M hM z₂ π₂ hπ₂ i)⟩
  rw [← improvement_identity M z₁ z₂ g₁ v₁ π₁ π₂ h₁ hπ₁ hπ₂] at hs
  exact sub_pos.mp hs

end CJewell

theorem solution {N : ℕ} [NeZero N] {α : Type*} (M : MRP N α)
    (hM : M.IsErgodic) (z₁ z₂ : Fin N → α) (g₁ : ℝ) (v₁ : Fin N → ℝ)
    (h₁ : M.SolvesValueDetermination z₁ g₁ v₁) (hstep : M.IsImprovementStep z₁ v₁ z₂)
    (hne : z₂ ≠ z₁) (π₁ π₂ : Fin N → ℝ)
    (hπ₁ : IsStationaryDist (M.policyMatrix z₁) π₁)
    (hπ₂ : IsStationaryDist (M.policyMatrix z₂) π₂) :
    M.gainRate z₁ π₁ < M.gainRate z₂ π₂ := by
  exact CJewell.strict_improvement M hM z₁ z₂ g₁ v₁ h₁ hstep hne π₁ π₂ hπ₁ hπ₂
