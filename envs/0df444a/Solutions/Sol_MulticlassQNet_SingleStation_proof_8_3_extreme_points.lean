-- Prove2me | solution 1 for MulticlassQNet.SingleStation.proof_8_3_extreme_points
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T15:11:16.779833+00:00
-- url     : https://prove2.me/submissions/9ef85d52-603c-4773-9689-b32f75439252

import Mathlib
import Definitions.Def_MulticlassQNet_SingleStation_Polyhedra



namespace MulticlassQNet.SingleStation

open Finset AllocationIndices

theorem lowSet_succ' {n : ℕ} (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k < n) :
    lowSet π (k + 1) = insert (π ⟨k, hk⟩) (lowSet π k) := by
  ext i
  simp only [lowSet, mem_image, mem_filter, mem_univ, true_and, mem_insert]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
    · right; exact ⟨j, h, rfl⟩
    · left; congr 1; exact Fin.ext h
  · rintro (rfl | ⟨j, hj, rfl⟩)
    · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, rfl⟩
    · exact ⟨j, Nat.lt_succ_of_lt hj, rfl⟩

theorem not_mem_lowSet' {n : ℕ} (π : Equiv.Perm (Fin n)) (k : ℕ) (hk : k < n) :
    π ⟨k, hk⟩ ∉ lowSet π k := by
  simp only [lowSet, mem_image, mem_filter, mem_univ, true_and, not_exists, not_and]
  intro j hj h
  have := π.injective h
  rw [this] at hj
  exact lt_irrefl _ hj

theorem lowSet_zero' {n : ℕ} (π : Equiv.Perm (Fin n)) : lowSet π 0 = ∅ := by
  ext i; simp [lowSet]

theorem lowSet_n' {n : ℕ} (π : Equiv.Perm (Fin n)) : lowSet π n = univ := by
  ext i
  simp only [lowSet, mem_image, mem_filter, mem_univ, true_and, iff_true]
  exact ⟨π.symm i, (π.symm i).isLt, by simp⟩

theorem lowSet_symm_succ {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) :
    lowSet π ((π.symm i : ℕ) + 1) = insert i (lowSet π (π.symm i : ℕ)) := by
  rw [lowSet_succ' π _ (π.symm i).isLt]
  simp

theorem not_mem_lowSet_symm {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) :
    i ∉ lowSet π (π.symm i : ℕ) := by
  have := not_mem_lowSet' π _ (π.symm i).isLt
  simpa using this

/-- sums over lowSet as range sums -/
theorem sum_lowSet {n : ℕ} (π : Equiv.Perm (Fin n)) (z : Fin n → ℝ) :
    ∀ k, k ≤ n → ∑ i ∈ lowSet π k, z i =
      ∑ m ∈ range k, (if h : m < n then z (π ⟨m, h⟩) else 0) := by
  intro k
  induction k with
  | zero => intro _; simp [lowSet_zero']
  | succ k ih =>
    intro hk
    have hk' : k < n := hk
    rw [lowSet_succ' π k hk', sum_insert (not_mem_lowSet' π k hk'), sum_range_succ,
      ih hk'.le, dif_pos hk']
    ring

theorem chain_det {n : ℕ} (π : Equiv.Perm (Fin n)) (z1 z2 : Fin n → ℝ)
    (h : ∀ k, k ≤ n → ∑ i ∈ lowSet π k, z1 i = ∑ i ∈ lowSet π k, z2 i) : z1 = z2 := by
  funext i
  have h1 := h ((π.symm i : ℕ) + 1) (π.symm i).isLt
  have h2 := h (π.symm i : ℕ) (π.symm i).isLt.le
  rw [lowSet_symm_succ, sum_insert (not_mem_lowSet_symm π i),
    sum_insert (not_mem_lowSet_symm π i)] at h1
  linarith

theorem marg_real (cA cB rA rB g p : ℝ) (hcA : 0 ≤ cA) (hc : cA ≤ cB) (hr : rA ≤ rB)
    (hg : 0 ≤ g) (hp : 0 ≤ p) (hrA : 0 ≤ rA) (hpos : 0 < 1 - rB - p) :
    (g + cA) / (1 - (p + rA)) - cA / (1 - rA) ≤ (g + cB) / (1 - (p + rB)) - cB / (1 - rB) := by
  have e : ∀ c r : ℝ, 0 < 1 - r - p → (g + c) / (1 - (p + r)) - c / (1 - r) =
      g / (1 - r - p) + c * p / ((1 - r) * (1 - r - p)) := by
    intro c r hr
    have : 0 < 1 - r := by linarith
    have : 1 - (p + r) ≠ 0 := by linarith
    field_simp
    ring
  rw [e cA rA (by linarith), e cB rB hpos]
  have h1 : g / (1 - rA - p) ≤ g / (1 - rB - p) :=
    div_le_div_of_nonneg_left hg hpos (by linarith)
  have h2 : cA * p / ((1 - rA) * (1 - rA - p)) ≤ cB * p / ((1 - rB) * (1 - rB - p)) := by
    apply div_le_div₀ (by nlinarith) (by nlinarith) (by nlinarith)
    nlinarith
  linarith

theorem rho_lt_one {n : ℕ} (lam mu : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hmu : ∀ i, 0 < mu i) (hload : ∑ i, lam i / mu i < 1)
    (S : Finset (Fin n)) : ∑ i ∈ S, rho lam mu i < 1 :=
  lt_of_le_of_lt (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun i _ _ => (div_pos (hlam i) (hmu i)).le)) hload

theorem b_empty {n : ℕ} (lam mu : Fin n → ℝ) : b lam mu ∅ = 0 := by simp [b]

theorem b_marg {n : ℕ} (lam mu : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hmu : ∀ i, 0 < mu i) (hload : ∑ i, lam i / mu i < 1)
    (A B : Finset (Fin n)) (e : Fin n) (hAB : A ⊆ B) (he : e ∉ B) :
    b lam mu (insert e A) - b lam mu A ≤ b lam mu (insert e B) - b lam mu B := by
  have heA : e ∉ A := fun h => he (hAB h)
  have hρ : ∀ i, 0 ≤ rho lam mu i := fun i => (div_pos (hlam i) (hmu i)).le
  have hγ : ∀ i, 0 ≤ rho lam mu i / mu i := fun i => div_nonneg (hρ i) (hmu i).le
  unfold b
  rw [sum_insert heA, sum_insert heA, sum_insert he, sum_insert he]
  have hpos := rho_lt_one lam mu hlam hmu hload (insert e B)
  rw [sum_insert he] at hpos
  apply marg_real _ _ _ _ _ _ (sum_nonneg (fun i _ => hγ i))
    (sum_le_sum_of_subset_of_nonneg hAB (fun i _ _ => hγ i))
    (sum_le_sum_of_subset_of_nonneg hAB (fun i _ _ => hρ i)) (hγ e) (hρ e)
    (sum_nonneg (fun i _ => hρ i)) (by linarith)

theorem b_insert_ge {n : ℕ} (lam mu : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hmu : ∀ i, 0 < mu i) (hload : ∑ i, lam i / mu i < 1)
    (B : Finset (Fin n)) (e : Fin n) (he : e ∉ B) :
    b lam mu B ≤ b lam mu (insert e B) := by
  have h := b_marg lam mu hlam hmu hload ∅ B e (empty_subset _) he
  rw [b_empty] at h
  have : 0 ≤ b lam mu {e} := by
    unfold b
    have := rho_lt_one lam mu hlam hmu hload {e}
    apply div_nonneg
    · simp only [sum_singleton]; exact div_nonneg (div_pos (hlam e) (hmu e)).le (hmu e).le
    · linarith
  simp only [insert_empty] at h
  linarith

/-- the scaled vector `v(π)_i / μ_i` -/
noncomputable def yv {n : ℕ} (lam mu : Fin n → ℝ) (π : Equiv.Perm (Fin n)) (i : Fin n) : ℝ :=
  b lam mu (lowSet π ((π.symm i : ℕ) + 1)) - b lam mu (lowSet π (π.symm i : ℕ))

theorem v_eq {n : ℕ} (lam mu : Fin n → ℝ) (π : Equiv.Perm (Fin n)) (i : Fin n) :
    v lam mu π i = mu i * yv lam mu π i := rfl

theorem yv_sum {n : ℕ} (lam mu : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    ∀ k, k ≤ n → ∑ i ∈ lowSet π k, yv lam mu π i = b lam mu (lowSet π k) := by
  intro k
  induction k with
  | zero => intro _; simp [lowSet_zero', b_empty]
  | succ k ih =>
    intro hk
    have hk' : k < n := hk
    rw [lowSet_succ' π k hk', sum_insert (not_mem_lowSet' π k hk'), ih hk'.le]
    simp only [yv, Equiv.symm_apply_apply]
    rw [lowSet_succ' π k hk']
    ring

theorem yv_sub {n : ℕ} (lam mu : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hmu : ∀ i, 0 < mu i) (hload : ∑ i, lam i / mu i < 1)
    (π : Equiv.Perm (Fin n)) :
    ∀ k, k ≤ n → ∀ S, S ⊆ lowSet π k → b lam mu S ≤ ∑ i ∈ S, yv lam mu π i := by
  intro k
  induction k with
  | zero =>
    intro _ S hS
    rw [lowSet_zero', subset_empty] at hS
    subst hS; simp [b_empty]
  | succ k ih =>
    intro hk S hS
    have hk' : k < n := hk
    rw [lowSet_succ' π k hk'] at hS
    by_cases hm : π ⟨k, hk'⟩ ∈ S
    · have hS' : S.erase (π ⟨k, hk'⟩) ⊆ lowSet π k := subset_insert_iff.1 hS
      have hih := ih hk'.le _ hS'
      have hmarg := b_marg lam mu hlam hmu hload _ _ (π ⟨k, hk'⟩) hS' (not_mem_lowSet' π k hk')
      rw [insert_erase hm] at hmarg
      rw [← insert_erase hm, sum_insert (notMem_erase _ _), insert_erase hm]
      have hy : yv lam mu π (π ⟨k, hk'⟩) =
          b lam mu (insert (π ⟨k, hk'⟩) (lowSet π k)) - b lam mu (lowSet π k) := by
        simp only [yv, Equiv.symm_apply_apply]
        rw [lowSet_succ' π k hk']
      linarith
    · exact ih hk'.le S ((subset_insert_iff_of_notMem hm).1 hS)

theorem v_mem {n : ℕ} (lam mu : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hmu : ∀ i, 0 < mu i) (hload : ∑ i, lam i / mu i < 1)
    (π : Equiv.Perm (Fin n)) : v lam mu π ∈ P1 lam mu := by
  have hconv : ∀ S : Finset (Fin n), ∑ i ∈ S, 1 / mu i * v lam mu π i = ∑ i ∈ S, yv lam mu π i := by
    intro S; apply sum_congr rfl; intro i _
    rw [v_eq]; have := hmu i; field_simp
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [v_eq]
    apply mul_nonneg (hmu i).le
    simp only [yv]
    rw [lowSet_symm_succ]
    have := b_insert_ge lam mu hlam hmu hload _ i (not_mem_lowSet_symm π i)
    linarith
  · intro S _
    rw [hconv]
    exact yv_sub lam mu hlam hmu hload π n le_rfl S (by rw [lowSet_n']; exact subset_univ _)
  · rw [hconv]
    have := yv_sum lam mu π n le_rfl
    rw [lowSet_n'] at this
    exact this

theorem P1_convex {n : ℕ} (lam mu : Fin n → ℝ) : Convex ℝ (P1 lam mu) := by
  intro x hx y hy a c ha hc hac
  obtain ⟨hx0, hxS, hxU⟩ := hx
  obtain ⟨hy0, hyS, hyU⟩ := hy
  have hlin : ∀ S : Finset (Fin n), ∑ i ∈ S, 1 / mu i * (a • x + c • y) i =
      a * ∑ i ∈ S, 1 / mu i * x i + c * ∑ i ∈ S, 1 / mu i * y i := by
    intro S
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl; intros; ring
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx0 i; have := hy0 i; positivity
  · intro S hS
    rw [hlin]
    have h1 := hxS S hS; have h2 := hyS S hS
    simp only at h1 h2
    have e1 := mul_le_mul_of_nonneg_left h1 ha
    have e2 := mul_le_mul_of_nonneg_left h2 hc
    have : b lam mu S = (a + c) * b lam mu S := by rw [hac, one_mul]
    nlinarith
  · simp only at hxU hyU ⊢
    rw [hlin, hxU, hyU]
    rw [← add_mul, hac, one_mul]

theorem v_extreme {n : ℕ} (lam mu : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hmu : ∀ i, 0 < mu i) (hload : ∑ i, lam i / mu i < 1)
    (π : Equiv.Perm (Fin n)) : v lam mu π ∈ Set.extremePoints ℝ (P1 lam mu) := by
  rw [mem_extremePoints]
  refine ⟨v_mem lam mu hlam hmu hload π, ?_⟩
  have hconv : ∀ S : Finset (Fin n), ∑ i ∈ S, 1 / mu i * v lam mu π i = ∑ i ∈ S, yv lam mu π i := by
    intro S; apply sum_congr rfl; intro i _
    rw [v_eq]; have := hmu i; field_simp
  -- tight on the chain implies equal to v
  have key : ∀ x1 ∈ P1 lam mu, ∀ x2 ∈ P1 lam mu, ∀ a c : ℝ, 0 < a → 0 < c → a + c = 1 →
      a • x1 + c • x2 = v lam mu π → x1 = v lam mu π := by
    intro x1 hx1 x2 hx2 a c ha hc hac heq
    obtain ⟨_, hx1S, hx1U⟩ := hx1
    obtain ⟨_, hx2S, hx2U⟩ := hx2
    have hle : ∀ (z : Fin n → ℝ), z ∈ P1 lam mu → ∀ k, k ≤ n →
        b lam mu (lowSet π k) ≤ ∑ i ∈ lowSet π k, 1 / mu i * z i := by
      intro z hz k _
      obtain ⟨_, hzS, hzU⟩ := hz
      by_cases hu : lowSet π k = univ
      · rw [hu]; exact hzU.ge
      · exact hzS _ hu
    have htight : ∀ k, k ≤ n → ∑ i ∈ lowSet π k, 1 / mu i * x1 i = b lam mu (lowSet π k) := by
      intro k hk
      have h1 := hle x1 ⟨‹_›, hx1S, hx1U⟩ k hk
      have h2 := hle x2 ⟨‹_›, hx2S, hx2U⟩ k hk
      have h3 : ∑ i ∈ lowSet π k, 1 / mu i * v lam mu π i =
          a * ∑ i ∈ lowSet π k, 1 / mu i * x1 i + c * ∑ i ∈ lowSet π k, 1 / mu i * x2 i := by
        rw [← heq]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_sum, ← sum_add_distrib]
        apply sum_congr rfl; intros; ring
      rw [hconv, yv_sum lam mu π k hk] at h3
      have e1 : 0 ≤ a * (∑ i ∈ lowSet π k, 1 / mu i * x1 i - b lam mu (lowSet π k)) :=
        mul_nonneg ha.le (by linarith)
      have e2 : 0 ≤ c * (∑ i ∈ lowSet π k, 1 / mu i * x2 i - b lam mu (lowSet π k)) :=
        mul_nonneg hc.le (by linarith)
      have e3 : a * (∑ i ∈ lowSet π k, 1 / mu i * x1 i - b lam mu (lowSet π k)) = 0 := by
        have : b lam mu (lowSet π k) = (a + c) * b lam mu (lowSet π k) := by rw [hac, one_mul]
        nlinarith
      rcases mul_eq_zero.1 e3 with h | h
      · exact absurd h ha.ne'
      · linarith
    have hz := chain_det π (fun i => 1 / mu i * x1 i) (fun i => 1 / mu i * v lam mu π i)
      (fun k hk => by rw [htight k hk, hconv, yv_sum lam mu π k hk])
    funext i
    have := congrFun hz i
    try simp only at this
    have hm := hmu i
    field_simp at this
    linarith
  intro x1 hx1 x2 hx2 hseg
  obtain ⟨a, c, ha, hc, hac, heq⟩ := hseg
  refine ⟨key x1 hx1 x2 hx2 a c ha hc hac heq, ?_⟩
  exact key x2 hx2 x1 hx1 c a hc ha (by linarith) (by rw [add_comm]; exact heq)

theorem greedy_opt {n : ℕ} (lam mu : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hmu : ∀ i, 0 < mu i) (hload : ∑ i, lam i / mu i < 1)
    (c : Fin n → ℝ) :
    ∃ π : Equiv.Perm (Fin n), ∀ x ∈ P1 lam mu, ∑ i, c i * v lam mu π i ≤ ∑ i, c i * x i := by
  set π := Tuple.sort (fun i => -(c i * mu i)) with hπ
  have hmono : Monotone ((fun i => -(c i * mu i)) ∘ π) := Tuple.monotone_sort _
  refine ⟨π, ?_⟩
  intro x hx
  obtain ⟨hx0, hxS, hxU⟩ := hx
  let z : Fin n → ℝ := fun i => 1 / mu i * x i - yv lam mu π i
  have hdiff : ∑ i, c i * x i - ∑ i, c i * v lam mu π i = ∑ i, (c i * mu i) * z i := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl; intro i _
    simp only [z, v_eq]
    have := hmu i
    field_simp
  let F : ℕ → ℝ := fun m => if h : m < n then c (π ⟨m, h⟩) * mu (π ⟨m, h⟩) else 0
  let Z : ℕ → ℝ := fun m => if h : m < n then z (π ⟨m, h⟩) else 0
  have hre : ∑ i, (c i * mu i) * z i = ∑ m ∈ range n, F m • Z m := by
    rw [← Equiv.sum_comp π (fun i => (c i * mu i) * z i)]
    rw [← Fin.sum_univ_eq_sum_range (fun m => F m • Z m) n]
    apply sum_congr rfl; intro i _
    simp only [F, Z, i.isLt, dif_pos, Fin.eta, smul_eq_mul]
  have hG : ∀ k, k ≤ n → ∑ m ∈ range k, Z m = ∑ i ∈ lowSet π k, z i := by
    intro k hk; rw [sum_lowSet π z k hk]
  have hGn : ∑ m ∈ range n, Z m = 0 := by
    rw [hG n le_rfl, lowSet_n']
    simp only [z, sum_sub_distrib]
    have := yv_sum lam mu π n le_rfl
    rw [lowSet_n'] at this
    simp only at hxU
    rw [this, hxU, sub_self]
  have hGnn : ∀ k, k < n → 0 ≤ ∑ m ∈ range k, Z m := by
    intro k hk
    rw [hG k hk.le]
    simp only [z, sum_sub_distrib]
    have hne : lowSet π k ≠ univ := by
      intro h
      have := not_mem_lowSet' π k hk
      rw [h] at this; exact this (mem_univ _)
    have h1 := hxS _ hne
    simp only at h1
    rw [yv_sum lam mu π k hk.le]
    linarith
  have hparts := Finset.sum_range_by_parts F Z n
  have hrest : ∑ i ∈ range (n - 1), (F (i + 1) - F i) • ∑ m ∈ range (i + 1), Z m ≤ 0 := by
    apply sum_nonpos
    intro m hm
    rw [mem_range] at hm
    have hm1 : m + 1 < n := by omega
    have hm0 : m < n := by omega
    have hFle : F (m + 1) - F m ≤ 0 := by
      simp only [F, dif_pos hm1, dif_pos hm0]
      have := hmono (show (⟨m, hm0⟩ : Fin n) ≤ ⟨m + 1, hm1⟩ from by
        rw [Fin.mk_le_mk]; omega)
      simp only [Function.comp] at this
      linarith
    rw [smul_eq_mul]
    exact mul_nonpos_of_nonpos_of_nonneg hFle (hGnn _ hm1)
  have : 0 ≤ ∑ i, (c i * mu i) * z i := by
    rw [hre, hparts, hGn, smul_zero]
    linarith
  linarith

theorem hull_eq {n : ℕ} (lam mu : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hmu : ∀ i, 0 < mu i) (hload : ∑ i, lam i / mu i < 1) :
    P1 lam mu = convexHull ℝ (Set.range (v lam mu)) := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hn
    obtain ⟨f, u, hfx, hfb⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _)
      (((Set.finite_range (v lam mu)).isCompact_convexHull ℝ).isClosed) hn
    have hf : ∀ y : Fin n → ℝ, f y = ∑ i, (f fun j => if i = j then 1 else 0) * y i := by
      intro y
      have := LinearMap.pi_apply_eq_sum_univ (f : (Fin n → ℝ) →ₗ[ℝ] ℝ) y
      simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
      rw [this]; apply sum_congr rfl; intros; ring
    obtain ⟨π, hπ⟩ := greedy_opt lam mu hlam hmu hload (fun i => f fun j => if i = j then 1 else 0)
    have h1 := hfb (v lam mu π) (subset_convexHull ℝ _ ⟨π, rfl⟩)
    have h2 := hπ x hx
    rw [hf] at h1 hfx
    linarith
  · exact convexHull_min (Set.range_subset_iff.2 (v_mem lam mu hlam hmu hload)) (P1_convex lam mu)

theorem extreme_core {n : ℕ} (lam mu : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hmu : ∀ i, 0 < mu i) (hload : ∑ i, lam i / mu i < 1) :
    Set.extremePoints ℝ (P1 lam mu) = Set.range (v lam mu) ∧
      P1 lam mu = convexHull ℝ (Set.range (v lam mu)) := by
  have hh := hull_eq lam mu hlam hmu hload
  refine ⟨Set.Subset.antisymm ?_ (Set.range_subset_iff.2 (v_extreme lam mu hlam hmu hload)), hh⟩
  intro x hx
  rw [hh] at hx
  exact extremePoints_convexHull_subset hx

end MulticlassQNet.SingleStation

open MulticlassQNet.SingleStation


theorem solution {n : ℕ} (lam mu : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hmu : ∀ i, 0 < mu i) (hload : ∑ i, lam i / mu i < 1) :
    Set.extremePoints ℝ (P1 lam mu) = Set.range (v lam mu) ∧
      P1 lam mu = convexHull ℝ (Set.range (v lam mu)) := by
  exact extreme_core lam mu hlam hmu hload
