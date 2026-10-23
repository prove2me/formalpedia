-- Prove2me | solution 1 for KellyStochasticNetworks.ImpliedCosts.matrix_characterization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T21:27:32.004004+00:00
-- url     : https://prove2.me/submissions/c9f389f9-7c22-4c84-9b1b-73ab13508620

import Definitions.Def_KellyStochasticNetworks_ImpliedCosts_Model

namespace X7K
open Finset

lemma fact_ineqN (k i d : ℕ) (h : k ≤ i) :
    i.factorial * (k + d).factorial ≤ k.factorial * (i + d).factorial := by
  induction d with
  | zero => simp [mul_comm]
  | succ d ih =>
    rw [show k + (d+1) = (k+d) + 1 by ring, show i + (d+1) = (i+d) + 1 by ring,
      Nat.factorial_succ, Nat.factorial_succ]
    calc i.factorial * ((k + d + 1) * (k + d).factorial)
        = (k + d + 1) * (i.factorial * (k + d).factorial) := by ring
      _ ≤ (i + d + 1) * (k.factorial * (i + d).factorial) :=
          Nat.mul_le_mul (by omega) ih
      _ = _ := by ring

lemma fact_ineq (k i d : ℕ) (h : k ≤ i) :
    (i.factorial : ℝ) * ((k + d).factorial) ≤ (k.factorial) * ((i + d).factorial) := by
  exact_mod_cast fact_ineqN k i d h

/-- `t k = ρ^k/k!` -/
noncomputable def t (ρ : ℝ) (k : ℕ) : ℝ := ρ ^ k / (k.factorial : ℝ)

lemma t_succ (ρ : ℝ) (k : ℕ) : ρ * t ρ k = ((k:ℝ) + 1) * t ρ (k+1) := by
  unfold t; rw [Nat.factorial_succ]; push_cast
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp; ring

lemma t_pos {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) : 0 < t ρ k := by unfold t; positivity

/-- pairing inequality: for `k < i ≤ n`, `t (n+1) * t k ≤ t i * t (n+1+k-i)`. -/
lemma pair_le {ρ : ℝ} (hρ : 0 < ρ) {n k i : ℕ} (hki : k < i) (hin : i ≤ n) :
    t ρ (n+1) * t ρ k ≤ t ρ i * t ρ (n+1+k-i) := by
  unfold t
  have hp : ρ ^ (n+1) * ρ ^ k = ρ ^ i * ρ ^ (n+1+k-i) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  rw [div_mul_div_comm, div_mul_div_comm, hp]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  -- i! (n+1+k-i)! ≤ (n+1)! k!
  have := fact_ineq k i (n+1-i) hki.le
  rw [show k + (n+1-i) = n+1+k-i by omega, show i + (n+1-i) = n+1 by omega] at this
  rw [mul_comm ((n+1).factorial : ℝ)]; exact_mod_cast this

lemma inner_le {ρ : ℝ} (hρ : 0 < ρ) {n i : ℕ} (hi : i ≤ n + 1) :
    ∑ k ∈ range i, t ρ (n+1+k-i) ≤ ∑ j ∈ range (n+1), t ρ j := by
  have : ∑ k ∈ range i, t ρ (n+1+k-i) = ∑ j ∈ Ico (n+1-i) (n+1), t ρ j := by
    rw [Finset.sum_Ico_eq_sum_range, show n + 1 - (n+1-i) = i by omega]
    refine Finset.sum_congr rfl fun k hk => ?_
    congr 1; omega
  rw [this]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj; simp only [mem_Ico, mem_range] at hj ⊢; omega
  · intro j _ _; exact (t_pos hρ j).le

lemma key {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    t ρ (n+1) * ∑ k ∈ range (n+1), ((n:ℝ) - k) * t ρ k < (∑ k ∈ range (n+1), t ρ k) ^ 2 := by
  set S := ∑ k ∈ range (n+1), t ρ k
  have h1 : t ρ (n+1) * ∑ k ∈ range (n+1), ((n:ℝ) - k) * t ρ k
      = ∑ k ∈ range (n+1), ∑ i ∈ Ioc k n, t ρ (n+1) * t ρ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
    have : k ≤ n := by simp at hk; omega
    rw [Nat.cast_sub this]; ring
  have h2 : ∑ k ∈ range (n+1), ∑ i ∈ Ioc k n, t ρ (n+1) * t ρ k
      ≤ ∑ k ∈ range (n+1), ∑ i ∈ Ioc k n, t ρ i * t ρ (n+1+k-i) := by
    refine Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun i hi => ?_
    simp only [mem_Ioc] at hi
    exact pair_le hρ hi.1 hi.2
  have h3 : ∑ k ∈ range (n+1), ∑ i ∈ Ioc k n, t ρ i * t ρ (n+1+k-i)
      = ∑ i ∈ range (n+1), ∑ k ∈ range i, t ρ i * t ρ (n+1+k-i) := by
    apply Finset.sum_comm'
    intro k i; simp only [mem_range, mem_Ioc]; omega
  have h4 : ∑ i ∈ range (n+1), ∑ k ∈ range i, t ρ i * t ρ (n+1+k-i)
      < ∑ i ∈ range (n+1), t ρ i * S := by
    apply Finset.sum_lt_sum
    · intro i hi
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (inner_le hρ (by simp at hi; omega)) (t_pos hρ i).le
    · refine ⟨0, by simp, ?_⟩
      simp only [range_zero, sum_empty]
      have : 0 < S := Finset.sum_pos (fun j _ => t_pos hρ j) (by simp)
      exact mul_pos (t_pos hρ 0) this
  have h5 : ∑ i ∈ range (n+1), t ρ i * S = S ^ 2 := by rw [← Finset.sum_mul, sq]
  linarith

lemma rho_sum (ρ : ℝ) (n : ℕ) :
    ρ * ∑ k ∈ range (n+1), t ρ k
      = ((n:ℝ) * ∑ k ∈ range (n+1), t ρ k - ∑ k ∈ range (n+1), ((n:ℝ) - k) * t ρ k)
        + ((n:ℝ)+1) * t ρ (n+1) := by
  induction n with
  | zero => simp [t_succ ρ 0]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun k => ((((n+1:ℕ)):ℝ) - k) * t ρ k)]
    have e : ∑ k ∈ range (n+1), (((n+1:ℕ):ℝ) - k) * t ρ k
        = ∑ k ∈ range (n+1), ((n:ℝ) - k) * t ρ k + ∑ k ∈ range (n+1), t ρ k := by
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun k _ => ?_; push_cast; ring
    rw [e, mul_add, ih, t_succ ρ (n+1)]; push_cast; ring

lemma erlang_eq (ρ : ℝ) (n : ℕ) :
    KellyStochasticNetworks.erlang ρ n = t ρ n / ∑ k ∈ range (n+1), t ρ k := rfl

theorem erlang_delta {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) :
    0 ≤ ρ * (KellyStochasticNetworks.erlang ρ n - KellyStochasticNetworks.erlang ρ (n+1)) ∧
    ρ * (KellyStochasticNetworks.erlang ρ n - KellyStochasticNetworks.erlang ρ (n+1)) < 1 := by
  rw [erlang_eq, erlang_eq, Finset.sum_range_succ _ (n+1)]
  set S := ∑ k ∈ range (n+1), t ρ k
  set N := ∑ k ∈ range (n+1), ((n:ℝ) - k) * t ρ k
  have hS : 0 < S := Finset.sum_pos (fun j _ => t_pos hρ j) (by simp)
  have hu := t_pos hρ (n+1)
  have hN : 0 ≤ N := Finset.sum_nonneg fun k hk => by
    have : (k:ℝ) ≤ n := by exact_mod_cast (by simp at hk; omega : k ≤ n)
    exact mul_nonneg (by linarith) (t_pos hρ k).le
  have hk := key hρ n
  have hr := rho_sum ρ n
  have ht := t_succ ρ n
  have eq : ρ * (t ρ n / S - t ρ (n+1) / (S + t ρ (n+1)))
      = t ρ (n+1) * (N + S) / (S * (S + t ρ (n+1))) := by
    field_simp
    linear_combination (S + t ρ (n+1)) * ht - t ρ (n+1) * hr
  rw [eq]
  constructor
  · positivity
  · rw [div_lt_one (by positivity)]
    nlinarith

end X7K


namespace X7K
open Finset Matrix KellyStochasticNetworks.ImpliedCosts

variable {J R : ℕ} (A : Fin J → Fin R → ℕ) (lam : Fin R → ℝ) (g : Fin J → ℝ)

lemma K_apply (i j : Fin J) :
    (incidence A * diagonal lam * (incidence A).transpose) i j
      = ∑ r, (A i r : ℝ) * lam r * (A j r : ℝ) := by
  rw [Matrix.mul_apply]; simp [Matrix.mul_diagonal, incidence]

lemma P_apply (c : Fin J → ℝ) (j : Fin J) :
    vecMul c (1 + incidence A * diagonal lam * (incidence A).transpose * diagonal g) j
      = c j + g j * ∑ r, (A j r : ℝ) * lam r * ∑ i, c i * (A i r : ℝ) := by
  simp only [vecMul_add, vecMul_one, Pi.add_apply]
  congr 1
  rw [vecMul, dotProduct]
  simp_rw [Matrix.mul_diagonal, K_apply]
  simp_rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun i _ => by ring

lemma R_apply (w : Fin R → ℝ) (j : Fin J) :
    vecMul w (diagonal lam * (incidence A).transpose * diagonal g) j
      = g j * ∑ r, (A j r : ℝ) * lam r * w r := by
  rw [vecMul, dotProduct]
  simp_rw [Matrix.mul_diagonal, Matrix.diagonal_mul, transpose_apply, incidence, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => by ring

lemma P_inj (hlam : ∀ r, 0 ≤ lam r) (hg : ∀ j, 0 ≤ g j) (d : Fin J → ℝ)
    (hd : vecMul d (1 + incidence A * diagonal lam * (incidence A).transpose * diagonal g) = 0) :
    d = 0 := by
  set X : Fin J → ℝ := fun j => ∑ r, (A j r : ℝ) * lam r * ∑ i, d i * (A i r : ℝ)
  have hc : ∀ j, d j = - (g j * X j) := fun j => by
    have := congrFun hd j; rw [P_apply] at this; simp at this; linarith
  have h1 : ∑ j, d j * X j = ∑ r, lam r * (∑ i, d i * (A i r : ℝ)) ^ 2 := by
    obtain ⟨S, hS⟩ : ∃ S : Fin R → ℝ, S = fun r => ∑ i, d i * (A i r : ℝ) := ⟨_, rfl⟩
    have hX : ∀ j, X j = ∑ r, (A j r : ℝ) * lam r * S r := fun j => by simp [X, hS]
    have hS' : ∀ r, ∑ i, d i * (A i r : ℝ) = S r := fun r => by simp [hS]
    simp_rw [hX, hS', Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← hS', sq, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  have h2 : 0 ≤ ∑ r, lam r * (∑ i, d i * (A i r : ℝ)) ^ 2 :=
    Finset.sum_nonneg fun r _ => mul_nonneg (hlam r) (sq_nonneg _)
  have h3 : ∑ j, d j * X j = - ∑ j, g j * X j ^ 2 := by
    rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun j _ => by rw [hc j]; ring
  have h4 : ∑ j, g j * X j ^ 2 = 0 := by
    have : 0 ≤ ∑ j, g j * X j ^ 2 := Finset.sum_nonneg fun j _ => mul_nonneg (hg j) (sq_nonneg _)
    linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hg j) (sq_nonneg _))] at h4
  funext j
  have := h4 j (by simp)
  rw [hc j]
  rcases mul_eq_zero.1 this with h | h
  · simp [h]
  · simp [pow_eq_zero_iff two_ne_zero |>.1 h]

/-- the symmetric matrix is positive definite -/
lemma Q_posDef (hlam : ∀ r, 0 ≤ lam r) (h : Fin J → ℝ) :
    (1 + diagonal h * incidence A * diagonal lam * (incidence A).transpose * diagonal h).PosDef := by
  set K := diagonal h * incidence A * diagonal (fun r => Real.sqrt (lam r))
  have hK : diagonal h * incidence A * diagonal lam * (incidence A).transpose * diagonal h
      = K * Kᴴ := by
    simp only [K, conjTranspose_eq_transpose_of_trivial, transpose_mul, diagonal_transpose]
    have : diagonal (fun r => Real.sqrt (lam r)) * diagonal (fun r => Real.sqrt (lam r))
        = diagonal lam := by
      rw [diagonal_mul_diagonal]; congr 1; funext r; exact Real.mul_self_sqrt (hlam r)
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (diagonal fun r => √(lam r)) (diagonal fun r => √(lam r)), this]
  rw [hK]
  exact Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_self_mul_conjTranspose K)

end X7K


namespace X7K
open Finset Matrix KellyStochasticNetworks KellyStochasticNetworks.ImpliedCosts

lemma blocking_mem {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ) (C : Fin J → ℝ) (j : Fin J) :
    0 ≤ blocking A ν C j ∧ blocking A ν C j < 1 := by
  unfold blocking
  split_ifs with h
  · exact (Classical.choose_spec h).1 j
  · simp

lemma cost_j {J R : ℕ} (A : Fin J → Fin R → ℕ) (w lam : Fin R → ℝ) (δ : Fin J → ℝ)
    (c : Fin J → ℝ) (j : Fin J) (hq : 0 < linkLoad A lam j) (hδ : δ j < 1) :
    c j = δ j * (∑ r, (A j r : ℝ) * lam r * (surplus A w c r + c j)) / linkLoad A lam j ↔
      c j + gamma A lam δ j * ∑ r, (A j r : ℝ) * lam r * ∑ i, c i * (A i r : ℝ)
        = gamma A lam δ j * ∑ r, (A j r : ℝ) * lam r * w r := by
  set Y := ∑ r, (A j r : ℝ) * lam r * w r
  set Z := ∑ r, (A j r : ℝ) * lam r * ∑ i, c i * (A i r : ℝ)
  set q := linkLoad A lam j
  have hsum : ∑ r, (A j r : ℝ) * lam r * (surplus A w c r + c j) = Y - Z + c j * q := by
    have : ∀ r, (A j r : ℝ) * lam r * (surplus A w c r + c j)
        = (A j r : ℝ) * lam r * w r - (A j r : ℝ) * lam r * ∑ i, c i * (A i r : ℝ)
          + c j * ((A j r : ℝ) * lam r) := fun r => by simp only [surplus]; ring
    simp_rw [this]; rw [sum_add_distrib, sum_sub_distrib, ← mul_sum]; rfl
  have hγ : gamma A lam δ j * ((1 - δ j) * q) = δ j := by
    unfold gamma; exact div_mul_cancel₀ _ (mul_ne_zero (by linarith) hq.ne')
  rw [hsum, eq_div_iff hq.ne']
  constructor
  · intro h
    have h2 : (c j + gamma A lam δ j * Z - gamma A lam δ j * Y) * ((1 - δ j) * q) = 0 := by
      linear_combination h + (Z - Y) * hγ
    rcases mul_eq_zero.1 h2 with h3 | h3
    · linarith
    · exfalso; have : 0 < (1 - δ j) * q := mul_pos (by linarith) hq
      linarith
  · intro h
    linear_combination ((1 - δ j) * q) * h + (Y - Z) * hγ

lemma cost_iff {J R : ℕ} (A : Fin J → Fin R → ℕ) (w lam : Fin R → ℝ) (δ : Fin J → ℝ)
    (hq : ∀ j, 0 < linkLoad A lam j) (hδ : ∀ j, δ j < 1) (s : Fin R → ℝ) (c : Fin J → ℝ) :
    CostSystem A w lam δ s c ↔ s = surplus A w c ∧
      vecMul c (1 + incidence A * diagonal lam * (incidence A).transpose *
        diagonal (gamma A lam δ)) = vecMul w (diagonal lam * (incidence A).transpose *
          diagonal (gamma A lam δ)) := by
  unfold CostSystem
  refine and_congr_right fun hs => ?_
  subst hs
  rw [funext_iff]
  refine forall_congr' fun j => ?_
  rw [P_apply, R_apply]
  exact cost_j A w lam δ c j (hq j) (hδ j)

end X7K

open Finset Matrix KellyStochasticNetworks KellyStochasticNetworks.ImpliedCosts X7K in
theorem solution {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (w ν : Fin R → ℝ) (C : Fin J → ℕ)
    (hν : ∀ r, 0 < ν r) (hC : ∀ j, 1 ≤ C j)
    (hused : ∀ j, ∃ r, 0 < A j r) :
    let B := blocking A ν (fun j => (C j : ℝ))
    let lam := carried A ν B
    let δ := improvement A ν C B
    let G := Matrix.diagonal (gamma A lam δ)
    let M := incidence A
    let Λ := Matrix.diagonal lam
    let Q := symmetricCostMatrix A lam δ
    let cStar := explicitCosts A w lam δ
    (∀ j, 0 < linkLoad A lam j ∧ 0 ≤ δ j ∧ δ j < 1) ∧
    (∀ (s : Fin R → ℝ) (c : Fin J → ℝ),
      CostSystem A w lam δ s c ↔
        s = surplus A w c ∧
          Matrix.vecMul c (1 + M * Λ * M.transpose * G) =
            Matrix.vecMul w (Λ * M.transpose * G)) ∧
    Q.PosDef ∧ IsUnit Q ∧
    (∀ (s : Fin R → ℝ) (c : Fin J → ℝ),
      CostSystem A w lam δ s c ↔ s = surplus A w cStar ∧ c = cStar) := by
  intro B lam δ G M Λ Q cStar
  have hB : ∀ j, 0 ≤ B j ∧ B j < 1 := fun j => blocking_mem A ν _ j
  have hlam : ∀ r, 0 < lam r := fun r => by
    simp only [lam, carried, acceptance]
    exact mul_pos (hν r) (Finset.prod_pos fun j _ => pow_pos (by linarith [(hB j).2]) _)
  have hq : ∀ j, 0 < linkLoad A lam j := fun j => by
    obtain ⟨r, hr⟩ := hused j
    unfold linkLoad
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun r => (A j r : ℝ) * lam r)
      (fun r _ => mul_nonneg (by positivity) (hlam r).le) (Finset.mem_univ r))
    exact mul_pos (by exact_mod_cast hr) (hlam r)
  have hδ : ∀ j, 0 ≤ δ j ∧ δ j < 1 := fun j => by
    have hρ : 0 < reducedLoad A ν B j := by
      unfold reducedLoad
      exact mul_pos (inv_pos.2 (by linarith [(hB j).2])) (hq j)
    have := erlang_delta hρ (C j - 1)
    rw [Nat.sub_add_cancel (hC j)] at this
    exact this
  have hγ : ∀ j, 0 ≤ gamma A lam δ j := fun j => by
    unfold gamma
    exact div_nonneg (hδ j).1 (mul_nonneg (by linarith [(hδ j).2]) (hq j).le)
  have part2 := cost_iff A w lam δ hq (fun j => (hδ j).2)
  have hQ : Q.PosDef := Q_posDef A lam (fun r => (hlam r).le) _
  have hQu : IsUnit Q := hQ.isUnit
  -- existence
  set H := Matrix.diagonal (fun j => Real.sqrt (gamma A lam δ j)) with hH
  have hHH : H * H = G := by
    rw [hH, diagonal_mul_diagonal]; congr 1; funext j; exact Real.mul_self_sqrt (hγ j)
  have hQdef : Q = 1 + H * M * Λ * M.transpose * H := rfl
  have hHP : H * (1 + M * Λ * M.transpose * G) = Q * H := by
    rw [hQdef, ← hHH]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_assoc]
  have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQu
  have hex : vecMul cStar (1 + M * Λ * M.transpose * G) = vecMul w (Λ * M.transpose * G) := by
    have hc : cStar = vecMul w (Λ * M.transpose * H * Q⁻¹ * H) := rfl
    rw [hc, vecMul_vecMul]
    congr 1
    rw [Matrix.mul_assoc _ H, hHP, ← Matrix.mul_assoc, Matrix.mul_assoc _ Q⁻¹ Q,
      Matrix.nonsing_inv_mul Q hdet, Matrix.mul_one, Matrix.mul_assoc _ H H, hHH]
  refine ⟨fun j => ⟨hq j, hδ j⟩, part2, hQ, hQu, fun s c => ?_⟩
  rw [part2]
  constructor
  · rintro ⟨hs, hc⟩
    have : c - cStar = 0 := P_inj A lam _ (fun r => (hlam r).le) hγ _ (by
      rw [sub_vecMul, hc, hex, sub_self])
    have hc' : c = cStar := sub_eq_zero.1 this
    exact ⟨hc' ▸ hs, hc'⟩
  · rintro ⟨hs, rfl⟩
    exact ⟨hs, hex⟩

