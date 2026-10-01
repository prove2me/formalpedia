-- Prove2me | solution 1 for JewellMRP.GainRate.policy_iteration_optimal_gain_rate
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:00:49.834361+00:00
-- url     : https://prove2.me/submissions/db05737e-2715-449b-bab6-adbbdc00f573

import Definitions.Def_JewellMRP_GainRate_PolicyIteration
import Mathlib.Tactic

section

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
end

section

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
end

section

open JewellMRP.GainRate Matrix Finset

namespace CJewell

variable {N : ℕ} [NeZero N] {α : Type*}

theorem superharmonic_constant (P : Matrix (Fin N) (Fin N) ℝ)
    (hn : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1) (hP : P.IsIrreducible)
    (v : Fin N → ℝ) (hv : ∀ i, (P *ᵥ v) i ≤ v i) : ∀ i j, v i = v j := by
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image Finset.univ v Finset.univ_nonempty
  have hp1 (n : ℕ) : P^n *ᵥ (fun _ => (1:ℝ)) = fun _ => 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
      ext k
      simpa [Matrix.mulVec, dotProduct] using hrow k
  have hpow (n : ℕ) : ∀ j, (P^n *ᵥ v) j ≤ v j := by
    induction n with
    | zero => simp
    | succ n ih =>
      intro j
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      exact (Finset.sum_le_sum (s := Finset.univ) (fun k _ => mul_le_mul_of_nonneg_left (ih k) (hn j k))).trans (hv j)
  have heq (j : Fin N) : v i = v j := by
    obtain ⟨n, hn0, hnpos⟩ := (Matrix.isIrreducible_iff_exists_pow_pos hn).mp hP i j
    have hnon (k : Fin N) : 0 ≤ (P^n) i k * (v k-v i) :=
      mul_nonneg (Matrix.pow_apply_nonneg hn n i k) (sub_nonneg.mpr (hmin k (Finset.mem_univ _)))
    have hr : ∑ k, (P^n) i k = 1 := by
      simpa [Matrix.mulVec, dotProduct] using congrFun (hp1 n) i
    have hs : ∑ k, (P^n) i k * (v k-v i) ≤ 0 := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hr, one_mul]
      exact sub_nonpos.mpr (hpow n i)
    have hj := (Finset.single_le_sum (fun k _ => hnon k) (Finset.mem_univ j)).trans hs
    have hz := le_antisymm hj (hnon j)
    have := (mul_eq_zero.mp hz).resolve_left hnpos.ne'
    linarith
  exact fun k j => (heq k).symm.trans (heq j)

theorem gain_increment_nonneg (P : Matrix (Fin N) (Fin N) ℝ)
    (hn : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1)
    (v ν : Fin N → ℝ) (hν : ∀ i, 0 < ν i) (g : ℝ)
    (hge : ∀ i, (P *ᵥ v) i ≤ v i + g * ν i) : 0 ≤ g := by
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image Finset.univ v Finset.univ_nonempty
  have hminavg : v i ≤ (P *ᵥ v) i := by
    calc
      v i = ∑ j, P i j * v i := by rw [← Finset.sum_mul, hrow, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hmin j (Finset.mem_univ _)) (hn i j))
  have hm : 0 ≤ g * ν i := by linarith [hge i]
  exact (mul_nonneg_iff_of_pos_right (hν i)).mp hm

theorem positive_gain_increment (P : Matrix (Fin N) (Fin N) ℝ)
    (hn : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1) (hP : P.IsIrreducible)
    (v ν : Fin N → ℝ) (hν : ∀ i, 0 < ν i) (g : ℝ)
    (hge : ∀ i, (P *ᵥ v) i ≤ v i + g * ν i)
    (hlt : ∃ i, (P *ᵥ v) i < v i + g * ν i) : 0 < g := by
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image Finset.univ v Finset.univ_nonempty
  have hminavg : v i ≤ (P *ᵥ v) i := by
    calc
      v i = ∑ j, P i j * v i := by rw [← Finset.sum_mul, hrow, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hmin j (Finset.mem_univ _)) (hn i j))
  have hgn : 0 ≤ g := by
    have h := hge i
    have hm : 0 ≤ g * ν i := by linarith
    exact (mul_nonneg_iff_of_pos_right (hν i)).mp hm
  apply lt_of_le_of_ne hgn
  intro hg
  have hg0 : g = 0 := hg.symm
  have hc := superharmonic_constant P hn hrow hP v (fun i => by simpa [hg0] using hge i)
  obtain ⟨j, hj⟩ := hlt
  have heq : (P *ᵥ v) j = v j := by
    change ∑ k, P j k * v k = v j
    simp_rw [hc _ j]
    rw [← Finset.sum_mul, hrow, one_mul]
  simp [hg0, heq] at hj


theorem residual_difference (M : MRP N α) (zB : Fin N → α) (gA gB : ℝ)
    (vA vB : Fin N → ℝ) (hB : M.SolvesValueDetermination zB gB vB) (i : Fin N) :
    (vB-vA) i + (gB-gA)*M.ν i (zB i) =
      (M.policyMatrix zB *ᵥ (vB-vA)) i +
        M.ν i (zB i) * (M.testQuantity vA i (zB i)-gA) := by
  have ht : M.ν i (zB i) * M.testQuantity vA i (zB i) =
      M.ρ i (zB i) + ∑ j, M.p i (zB i) j * vA j - vA i := by
    unfold MRP.testQuantity
    have hn : M.ν i (zB i) ≠ 0 := (M.ν_pos i (zB i)).ne'
    field_simp [hn]
  have h := hB.2 i
  simp only [Matrix.mulVec, dotProduct, MRP.policyMatrix, Matrix.of_apply,
    Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [ht]
  linarith

theorem weak_value_compare (M : MRP N α) (zA zB : Fin N → α) (gA gB : ℝ)
    (vA vB : Fin N → ℝ) (hA : M.SolvesValueDetermination zA gA vA)
    (hB : M.SolvesValueDetermination zB gB vB)
    (hge : ∀ i, gA ≤ M.testQuantity vA i (zB i)) : gA ≤ gB := by
  apply sub_nonneg.mp
  apply gain_increment_nonneg (M.policyMatrix zB) (fun i j => M.p_nonneg i (zB i) j)
    (fun i => M.p_sum_one i (zB i)) (vB-vA) (fun i => M.ν i (zB i))
    (fun i => M.ν_pos i (zB i))
  intro i
  have he := residual_difference M zB gA gB vA vB hB i
  have hn : 0 ≤ M.ν i (zB i) * (M.testQuantity vA i (zB i) - gA) :=
    mul_nonneg (M.ν_pos i (zB i)).le (sub_nonneg.mpr (hge i))
  linarith

theorem value_gain_unique (M : MRP N α) (z : Fin N → α) (gA gB : ℝ)
    (vA vB : Fin N → ℝ) (hA : M.SolvesValueDetermination z gA vA)
    (hB : M.SolvesValueDetermination z gB vB) : gA = gB := by
  apply le_antisymm
  · exact weak_value_compare M z z gA gB vA vB hA hB
      (fun i => (test_eq_gain M z gA vA hA i).ge)
  · exact weak_value_compare M z z gB gA vB vA hB hA
      (fun i => (test_eq_gain M z gB vB hB i).ge)

theorem step_gain_strict (M : MRP N α) (hM : M.IsErgodic) (zA zB : Fin N → α)
    (gA gB : ℝ) (vA vB : Fin N → ℝ) (hA : M.SolvesValueDetermination zA gA vA)
    (hB : M.SolvesValueDetermination zB gB vB) (hstep : M.IsImprovementStep zA vA zB)
    (hne : zB ≠ zA) : gA < gB := by
  have hge (i : Fin N) : gA ≤ M.testQuantity vA i (zB i) := by
    rw [← test_eq_gain M zA gA vA hA i]
    exact (hstep i).1 (zA i)
  obtain ⟨i, hi⟩ : ∃ i, zB i ≠ zA i := by
    by_contra! h
    exact hne (funext h)
  have hlt : gA < M.testQuantity vA i (zB i) := by
    apply lt_of_le_of_ne (hge i)
    intro heq
    apply hi
    apply (hstep i).2
    intro a
    rw [test_eq_gain M zA gA vA hA, heq]
    exact (hstep i).1 a
  apply sub_pos.mp
  apply positive_gain_increment (M.policyMatrix zB) (fun i j => M.p_nonneg i (zB i) j)
    (fun i => M.p_sum_one i (zB i)) (hM zB) (vB-vA) (fun i => M.ν i (zB i))
    (fun i => M.ν_pos i (zB i))
  · intro j
    have he := residual_difference M zB gA gB vA vB hB j
    have hn : 0 ≤ M.ν j (zB j) * (M.testQuantity vA j (zB j) - gA) :=
      mul_nonneg (M.ν_pos j (zB j)).le (sub_nonneg.mpr (hge j))
    linarith
  · refine ⟨i, ?_⟩
    have he := residual_difference M zB gA gB vA vB hB i
    have hn : 0 < M.ν i (zB i) * (M.testQuantity vA i (zB i) - gA) :=
      mul_pos (M.ν_pos i (zB i)) (sub_pos.mpr hlt)
    linarith

end CJewell
end

section
open JewellMRP.GainRate Matrix Finset

theorem solution {N : ℕ} [NeZero N] {α : Type*} [Fintype α]
    [Nonempty α] (M : MRP N α) (hM : M.IsErgodic) (z : ℕ → Fin N → α) (g : ℕ → ℝ)
    (v : ℕ → Fin N → ℝ) (hrun : M.IsPolicyIterationRun z g v) :
    (∃ K, z (K + 1) = z K) ∧
      ∀ K, z (K + 1) = z K →
        (∀ π : Fin N → ℝ, IsStationaryDist (M.policyMatrix (z K)) π →
            g K = M.gainRate (z K) π) ∧
          ∀ (z' : Fin N → α) (π π' : Fin N → ℝ),
            IsStationaryDist (M.policyMatrix (z K)) π →
            IsStationaryDist (M.policyMatrix z') π' →
            M.gainRate z' π' ≤ M.gainRate (z K) π := by
  classical
  constructor
  · by_contra! hnever
    have hg : StrictMono g := strictMono_nat_of_lt_succ (fun k =>
      CJewell.step_gain_strict M hM (z k) (z (k+1)) (g k) (g (k+1)) (v k) (v (k+1))
        (hrun.value k) (hrun.value (k+1)) (hrun.improve k) (hnever k))
    apply not_injective_infinite_finite z
    intro i j hij
    apply hg.injective
    exact CJewell.value_gain_unique M (z i) (g i) (g j) (v i) (v j) (hrun.value i)
      (by simpa only [hij] using hrun.value j)
  · intro K hK
    constructor
    · intro π hπ
      exact (CJewell.value_gain M (z K) (g K) (v K) π (hrun.value K) hπ).symm
    · intro z' π π' hπ hπ'
      have hid := CJewell.improvement_identity M (z K) z' (g K) (v K) π π'
        (hrun.value K) hπ hπ'
      have hnon : (∑ j, (M.testQuantity (v K) j (z' j) - M.testQuantity (v K) j (z K j)) *
          M.timeStationaryProb z' π' j) ≤ 0 := by
        apply Finset.sum_nonpos
        intro j hj
        have ht := (hrun.improve K j).1 (z' j)
        rw [hK] at ht
        exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht)
          (CJewell.time_positive M hM z' π' hπ' j).le
      rw [← hid] at hnon
      exact sub_nonpos.mp hnon
end