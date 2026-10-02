-- Prove2me | solution 1 for NonmonotoneSubmod.QueryLB.unbalanced_count_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T06:41:08.597736+00:00
-- url     : https://prove2.me/submissions/082e3d83-fe29-431c-8eb3-5b71fe7591df

import Mathlib
import Definitions.Def_NonmonotoneSubmod_QueryLB_HardInstance

set_option autoImplicit false

namespace Pa5cc0e84
open NonmonotoneSubmod.QueryLB

lemma card_ins {n : ℕ} (C S : Finset (Fin n)) (x : Fin n) (hx : x ∉ S) :
    (((insert x S) ∩ C).card : ℝ) = ((S ∩ C).card : ℝ) + (if x ∈ C then 1 else 0) ∧
    (((insert x S) ∩ Cᶜ).card : ℝ) = ((S ∩ Cᶜ).card : ℝ) + (if x ∈ C then 0 else 1) := by
  by_cases hxC : x ∈ C
  · have hxnot : x ∉ Cᶜ := by simpa using hxC
    rw [Finset.insert_inter_of_mem hxC, Finset.insert_inter_of_notMem hxnot,
      Finset.card_insert_of_notMem (fun h => hx (Finset.mem_inter.mp h).1)]
    simp [hxC]
  · have hxc : x ∈ Cᶜ := by simpa using hxC
    rw [Finset.insert_inter_of_notMem hxC, Finset.insert_inter_of_mem hxc,
      Finset.card_insert_of_notMem (fun h => hx (Finset.mem_inter.mp h).1)]
    simp [hxC]


def pidx (n N : ℕ) (hn : n = N + N) (x : Fin n) : Fin N :=
  ⟨x.val / 2, by have := x.isLt; omega⟩

def evx (n N : ℕ) (hn : n = N + N) (p : Fin N) : Fin n :=
  ⟨2 * p.val, by have := p.isLt; omega⟩

def odx (n N : ℕ) (hn : n = N + N) (p : Fin N) : Fin n :=
  ⟨2 * p.val + 1, by have := p.isLt; omega⟩

lemma pidx_ev (n N : ℕ) (hn : n = N + N) (p : Fin N) : pidx n N hn (evx n N hn p) = p :=
  Fin.ext (by simp only [pidx, evx]; omega)

lemma pidx_od (n N : ℕ) (hn : n = N + N) (p : Fin N) : pidx n N hn (odx n N hn p) = p :=
  Fin.ext (by simp only [pidx, odx]; omega)

def Csig (n N : ℕ) (hn : n = N + N) (σ : Fin N → Bool) : Finset (Fin n) :=
  Finset.univ.image (fun p : Fin N => if σ p then evx n N hn p else odx n N hn p)

lemma Csig_card (n N : ℕ) (hn : n = N + N) (σ : Fin N → Bool) : (Csig n N hn σ).card = N := by
  unfold Csig
  rw [Finset.card_image_of_injective]
  · simp
  · have key : ∀ p : Fin N, pidx n N hn (if σ p then evx n N hn p else odx n N hn p) = p := by
      intro p; split_ifs
      · exact pidx_ev n N hn p
      · exact pidx_od n N hn p
    intro p p' h
    exact (key p).symm.trans ((congrArg (pidx n N hn) h).trans (key p'))

lemma mem_Csig (n N : ℕ) (hn : n = N + N) (σ : Fin N → Bool) (x : Fin n) :
    x ∈ Csig n N hn σ ↔ (σ (pidx n N hn x) = true ↔ x.val % 2 = 0) := by
  unfold Csig
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, rfl⟩
    by_cases hp : σ p = true
    · rw [if_pos hp, pidx_ev]
      simp only [evx]
      constructor
      · intro _; omega
      · intro _; exact hp
    · rw [if_neg hp, pidx_od]
      simp only [odx]
      constructor
      · intro h; exact absurd h hp
      · intro h; omega
  · intro h
    refine ⟨pidx n N hn x, ?_⟩
    by_cases hp : σ (pidx n N hn x) = true
    · simp only [hp, if_true]
      have := h.mp hp
      apply Fin.ext; simp only [evx, pidx]; omega
    · have hp0 : ¬ x.val % 2 = 0 := fun hh => hp (h.mpr hh)
      simp only [hp, Bool.false_eq_true, if_false]
      apply Fin.ext; simp only [odx, pidx]; omega

noncomputable def sgn (n N : ℕ) (hn : n = N + N) (σ : Fin N → Bool) (x : Fin n) : ℝ :=
  if x ∈ Csig n N hn σ then 1 else -1

def eps (b : Bool) : ℝ := if b then 1 else -1

def tau {n : ℕ} (x : Fin n) : ℝ := if x.val % 2 = 0 then 1 else -1

def cc (n N : ℕ) (hn : n = N + N) (Q : Finset (Fin n)) (p : Fin N) : ℝ :=
  (if evx n N hn p ∈ Q then 1 else 0) - (if odx n N hn p ∈ Q then 1 else 0)

lemma cc_abs (n N : ℕ) (hn : n = N + N) (Q : Finset (Fin n)) (p : Fin N) :
    |cc n N hn Q p| ≤ 1 := by
  unfold cc
  by_cases h1 : evx n N hn p ∈ Q <;> by_cases h2 : odx n N hn p ∈ Q <;> simp [h1, h2]

lemma diff_eq (n N : ℕ) (hn : n = N + N) (σ : Fin N → Bool) (Q : Finset (Fin n)) :
    ((Q ∩ Csig n N hn σ).card : ℝ) - ((Q ∩ (Csig n N hn σ)ᶜ).card : ℝ)
      = ∑ x ∈ Q, sgn n N hn σ x := by
  induction Q using Finset.induction_on with
  | empty => simp
  | insert x Q hx ih =>
    have h := card_ins (Csig n N hn σ) Q x hx
    rw [h.1, h.2, Finset.sum_insert hx, ← ih]
    unfold sgn
    by_cases hxC : x ∈ Csig n N hn σ <;> simp [hxC] <;> ring

lemma sgn_eq (n N : ℕ) (hn : n = N + N) (σ : Fin N → Bool) (x : Fin n) :
    sgn n N hn σ x = eps (σ (pidx n N hn x)) * tau x := by
  unfold sgn eps tau
  simp only [mem_Csig]
  cases hb : σ (pidx n N hn x) <;> by_cases hp : x.val % 2 = 0 <;> simp [hp]

lemma fiber_eq (n N : ℕ) (hn : n = N + N) (Q : Finset (Fin n)) (p : Fin N) :
    ∑ x ∈ Q.filter (fun x => pidx n N hn x = p), tau x = cc n N hn Q p := by
  have hne : evx n N hn p ≠ odx n N hn p := by
    intro h
    have := congrArg Fin.val h
    simp only [evx, odx] at this
    omega
  have hset : Q.filter (fun x => pidx n N hn x = p)
      = ({evx n N hn p, odx n N hn p} : Finset (Fin n)).filter (fun x => x ∈ Q) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hxQ, hx⟩
      refine ⟨?_, hxQ⟩
      have := congrArg Fin.val hx
      simp only [pidx] at this
      by_cases hpar : x.val % 2 = 0
      · left; apply Fin.ext; simp only [evx]; omega
      · right; apply Fin.ext; simp only [odx]; omega
    · rintro ⟨hx, hxQ⟩
      refine ⟨hxQ, ?_⟩
      rcases hx with rfl | rfl
      · exact pidx_ev n N hn p
      · exact pidx_od n N hn p
  rw [hset, Finset.sum_filter, Finset.sum_pair hne]
  unfold cc tau
  have e1 : (evx n N hn p).val % 2 = 0 := by simp only [evx]; omega
  have e2 : ¬ (odx n N hn p).val % 2 = 0 := by simp only [odx]; omega
  simp only [e1, e2, if_true, if_false]
  by_cases h1 : evx n N hn p ∈ Q <;> by_cases h2 : odx n N hn p ∈ Q <;> simp [h1, h2]

lemma D_eq (n N : ℕ) (hn : n = N + N) (σ : Fin N → Bool) (Q : Finset (Fin n)) :
    ((Q ∩ Csig n N hn σ).card : ℝ) - ((Q ∩ (Csig n N hn σ)ᶜ).card : ℝ)
      = ∑ p : Fin N, eps (σ p) * cc n N hn Q p := by
  rw [diff_eq]
  simp_rw [sgn_eq]
  rw [← Finset.sum_fiberwise Q (pidx n N hn)]
  apply Finset.sum_congr rfl
  intro p _
  have : ∀ x ∈ Q.filter (fun x => pidx n N hn x = p),
      eps (σ (pidx n N hn x)) * tau x = eps (σ p) * tau x := by
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, fiber_eq]

/-! ## Hoeffding-type count over sign vectors -/

lemma hoeff_sum (N : ℕ) (c : Fin N → ℝ) (hc : ∀ p, |c p| ≤ 1) (t : ℝ) :
    ∑ σ : Fin N → Bool, Real.exp (t * ∑ p, eps (σ p) * c p)
      ≤ 2 ^ N * Real.exp (N * t ^ 2 / 2) := by
  have h1 : ∀ σ : Fin N → Bool, Real.exp (t * ∑ p, eps (σ p) * c p)
      = ∏ p, Real.exp (t * (eps (σ p) * c p)) := by
    intro σ
    rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [h1]
  have key : ∑ σ : Fin N → Bool, ∏ p, Real.exp (t * (eps (σ p) * c p))
      = ∏ p, ∑ b : Bool, Real.exp (t * (eps b * c p)) := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [key]
  have h2 : ∀ p : Fin N, ∑ b : Bool, Real.exp (t * (eps b * c p)) ≤ 2 * Real.exp (t ^ 2 / 2) := by
    intro p
    rw [Fintype.sum_bool]
    simp only [eps, if_true, if_false, Bool.false_eq_true]
    have hcosh := Real.cosh_le_exp_half_sq (t * c p)
    rw [Real.cosh_eq] at hcosh
    have hc2 : (t * c p) ^ 2 ≤ t ^ 2 := by
      have : (c p) ^ 2 ≤ 1 := by
        have := hc p
        nlinarith [abs_nonneg (c p), sq_abs (c p)]
      nlinarith [sq_nonneg t]
    have hexp : Real.exp ((t * c p) ^ 2 / 2) ≤ Real.exp (t ^ 2 / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    have e1 : t * (1 * c p) = t * c p := by ring
    have e2 : t * (-1 * c p) = -(t * c p) := by ring
    rw [e1, e2]
    linarith
  calc ∏ p, ∑ b : Bool, Real.exp (t * (eps b * c p))
      ≤ ∏ _p : Fin N, (2 * Real.exp (t ^ 2 / 2)) :=
        Finset.prod_le_prod (fun p _ => Finset.sum_nonneg (fun b _ => (Real.exp_pos _).le))
          (fun p _ => h2 p)
    _ = 2 ^ N * Real.exp (N * t ^ 2 / 2) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring

lemma tail_sum (N : ℕ) (hN : 0 < N) (c : Fin N → ℝ) (hc : ∀ p, |c p| ≤ 1) (m : ℝ) (hm : 0 ≤ m) :
    ∑ σ : Fin N → Bool, (if m < ∑ p, eps (σ p) * c p then (1 : ℝ) else 0)
      ≤ 2 ^ N * Real.exp (-(m ^ 2) / (2 * N)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set t : ℝ := m / N with ht
  have ht0 : 0 ≤ t := div_nonneg hm hNr.le
  have step : ∀ σ : Fin N → Bool, (if m < ∑ p, eps (σ p) * c p then (1 : ℝ) else 0)
      ≤ Real.exp (-(t * m)) * Real.exp (t * ∑ p, eps (σ p) * c p) := by
    intro σ
    rw [← Real.exp_add]
    split_ifs with h
    · rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have : 0 ≤ t * (∑ p, eps (σ p) * c p - m) := mul_nonneg ht0 (by linarith)
      nlinarith
    · exact (Real.exp_pos _).le
  calc ∑ σ : Fin N → Bool, (if m < ∑ p, eps (σ p) * c p then (1 : ℝ) else 0)
      ≤ ∑ σ : Fin N → Bool, Real.exp (-(t * m)) * Real.exp (t * ∑ p, eps (σ p) * c p) :=
        Finset.sum_le_sum (fun σ _ => step σ)
    _ = Real.exp (-(t * m)) * ∑ σ : Fin N → Bool, Real.exp (t * ∑ p, eps (σ p) * c p) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (-(t * m)) * (2 ^ N * Real.exp (N * t ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left (hoeff_sum N c hc t) (Real.exp_pos _).le
    _ = 2 ^ N * Real.exp (-(m ^ 2) / (2 * N)) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        rw [ht]
        field_simp
        ring

lemma bad_sum (n N m : ℕ) (hn : n = N + N) (hN : 0 < N) (Q : Finset (Fin n)) :
    ∑ σ : Fin N → Bool, (if Balanced n m (Csig n N hn σ) Q then (0 : ℝ) else 1)
      ≤ 2 * (2 ^ N * Real.exp (-((m : ℝ) ^ 2) / (2 * N))) := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have t1 := tail_sum N hN (cc n N hn Q) (cc_abs n N hn Q) m hm0
  have t2 := tail_sum N hN (fun p => - cc n N hn Q p) (fun p => by rw [abs_neg]; exact cc_abs n N hn Q p) m hm0
  have pt : ∀ σ : Fin N → Bool, (if Balanced n m (Csig n N hn σ) Q then (0 : ℝ) else 1)
      ≤ (if (m : ℝ) < ∑ p, eps (σ p) * cc n N hn Q p then (1 : ℝ) else 0)
        + (if (m : ℝ) < ∑ p, eps (σ p) * (- cc n N hn Q p) then (1 : ℝ) else 0) := by
    intro σ
    have hD := D_eq n N hn σ Q
    have hneg : ∑ p, eps (σ p) * (- cc n N hn Q p) = -∑ p, eps (σ p) * cc n N hn Q p := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun p _ => by ring)
    rw [hneg]
    have hbal : Balanced n m (Csig n N hn σ) Q ↔ |∑ p, eps (σ p) * cc n N hn Q p| ≤ m := by
      unfold NonmonotoneSubmod.QueryLB.Balanced
      rw [hD]
    by_cases h1 : (m : ℝ) < ∑ p, eps (σ p) * cc n N hn Q p
    · have : ¬ Balanced n m (Csig n N hn σ) Q := by
        rw [hbal]; push_neg; exact lt_of_lt_of_le h1 (le_abs_self _)
      simp only [this, h1, if_true, if_false]
      split_ifs <;> norm_num
    · by_cases h2 : (m : ℝ) < -∑ p, eps (σ p) * cc n N hn Q p
      · simp only [h1, h2, if_true, if_false]
        split_ifs <;> norm_num
      · have : Balanced n m (Csig n N hn σ) Q := by
          rw [hbal, abs_le]; push_neg at h1 h2; constructor <;> linarith
        simp only [this, if_true]
        have e1 : (0:ℝ) ≤ (if (m : ℝ) < ∑ p, eps (σ p) * cc n N hn Q p then (1 : ℝ) else 0) := by
          split_ifs <;> norm_num
        have e2 : (0:ℝ) ≤ (if (m : ℝ) < -∑ p, eps (σ p) * cc n N hn Q p then (1 : ℝ) else 0) := by
          split_ifs <;> norm_num
        linarith
  calc ∑ σ : Fin N → Bool, (if Balanced n m (Csig n N hn σ) Q then (0 : ℝ) else 1)
      ≤ ∑ σ : Fin N → Bool, ((if (m : ℝ) < ∑ p, eps (σ p) * cc n N hn Q p then (1 : ℝ) else 0)
        + (if (m : ℝ) < ∑ p, eps (σ p) * (- cc n N hn Q p) then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum (fun σ _ => pt σ)
    _ = _ := Finset.sum_add_distrib
    _ ≤ 2 * (2 ^ N * Real.exp (-((m : ℝ) ^ 2) / (2 * N))) := by linarith

/-! ## averaging over permutations -/

noncomputable def bad (n m : ℕ) (Q C : Finset (Fin n)) : ℝ :=
  if NonmonotoneSubmod.QueryLB.Balanced n m C Q then 0 else 1

lemma bal_map (n m : ℕ) (π : Equiv.Perm (Fin n)) (C Q : Finset (Fin n)) :
    NonmonotoneSubmod.QueryLB.Balanced n m (C.map π.toEmbedding) Q ↔
      NonmonotoneSubmod.QueryLB.Balanced n m C (Q.map π.symm.toEmbedding) := by
  have h1 : Q ∩ C.map π.toEmbedding = (Q.map π.symm.toEmbedding ∩ C).map π.toEmbedding := by
    ext x; simp [Finset.mem_map_equiv]
  have h2 : Q ∩ (C.map π.toEmbedding)ᶜ = (Q.map π.symm.toEmbedding ∩ Cᶜ).map π.toEmbedding := by
    ext x; simp [Finset.mem_map_equiv]
  unfold NonmonotoneSubmod.QueryLB.Balanced
  rw [h1, h2, Finset.card_map, Finset.card_map]

lemma exists_perm (n : ℕ) (C C' : Finset (Fin n)) (h : C.card = C'.card) :
    ∃ τ : Equiv.Perm (Fin n), C.map τ.toEmbedding = C' := by
  have e1 : {x // x ∈ C} ≃ {x // x ∈ C'} :=
    Fintype.equivOfCardEq (by simp [h])
  have e2 : {x // ¬ x ∈ C} ≃ {x // ¬ x ∈ C'} :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl]
      simp [h])
  refine ⟨Equiv.subtypeCongr e1 e2, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    rw [Finset.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hv : (Equiv.subtypeCongr e1 e2) x = (e1 ⟨x, hx⟩ : Fin n) := by
      simp [Equiv.subtypeCongr, Equiv.sumCompl_symm_apply_of_pos hx]
    simp only [Equiv.coe_toEmbedding, hv]
    exact (e1 ⟨x, hx⟩).2
  · rw [Finset.card_map, h]

noncomputable def favg (n m : ℕ) (Q C : Finset (Fin n)) : ℝ :=
  ∑ π : Equiv.Perm (Fin n), bad n m Q (C.map π.toEmbedding)

lemma favg_const (n m : ℕ) (Q C C' : Finset (Fin n)) (h : C.card = C'.card) :
    favg n m Q C' = favg n m Q C := by
  obtain ⟨τ, hτ⟩ := exists_perm n C C' h
  unfold favg
  rw [← hτ]
  apply Fintype.sum_equiv (Equiv.mulRight τ)
  intro π
  simp only [Equiv.coe_mulRight, Finset.map_map]
  congr 2

lemma sum_favg (n m N : ℕ) (Q : Finset (Fin n)) :
    ∑ C ∈ Finset.univ.powersetCard N, favg n m Q C
      = ∑ _π : Equiv.Perm (Fin n), ∑ C ∈ Finset.univ.powersetCard N, bad n m Q C := by
  unfold favg
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro π _
  apply Finset.sum_nbij' (fun C => C.map π.toEmbedding) (fun C => C.map π.symm.toEmbedding)
  · intro C hC; simp only [Finset.mem_powersetCard] at hC ⊢; simp [hC.2]
  · intro C hC; simp only [Finset.mem_powersetCard] at hC ⊢; simp [hC.2]
  · intro C _; ext x; simp [Finset.mem_map_equiv]
  · intro C _; ext x; simp [Finset.mem_map_equiv]
  · intro C _; rfl

lemma favg_bound (n m N : ℕ) (hn : n = N + N) (hN : 0 < N) (Q : Finset (Fin n))
    (σ0 : Fin N → Bool) :
    favg n m Q (Csig n N hn σ0)
      ≤ (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * (2 * Real.exp (-((m : ℝ) ^ 2) / (2 * N))) := by
  have hc : ∀ σ : Fin N → Bool, favg n m Q (Csig n N hn σ) = favg n m Q (Csig n N hn σ0) :=
    fun σ => favg_const n m Q _ _ (by rw [Csig_card, Csig_card])
  have hsum : ∑ σ : Fin N → Bool, favg n m Q (Csig n N hn σ)
      = (2 : ℝ) ^ N * favg n m Q (Csig n N hn σ0) := by
    rw [Finset.sum_congr rfl (fun σ _ => hc σ), Finset.sum_const, Finset.card_univ]
    simp [Fintype.card_bool, nsmul_eq_mul]
  have hswap : ∑ σ : Fin N → Bool, favg n m Q (Csig n N hn σ)
      = ∑ π : Equiv.Perm (Fin n), ∑ σ : Fin N → Bool,
          (if NonmonotoneSubmod.QueryLB.Balanced n m (Csig n N hn σ) (Q.map π.symm.toEmbedding)
            then (0 : ℝ) else 1) := by
    unfold favg
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro π _
    apply Finset.sum_congr rfl; intro σ _
    unfold bad
    exact if_congr (bal_map n m π _ Q) rfl rfl
  have hle : ∑ π : Equiv.Perm (Fin n), ∑ σ : Fin N → Bool,
          (if NonmonotoneSubmod.QueryLB.Balanced n m (Csig n N hn σ) (Q.map π.symm.toEmbedding)
            then (0 : ℝ) else 1)
      ≤ ∑ _π : Equiv.Perm (Fin n), 2 * (2 ^ N * Real.exp (-((m : ℝ) ^ 2) / (2 * N))) :=
    Finset.sum_le_sum (fun π _ => bad_sum n N m hn hN _)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hle
  have h2 : (0 : ℝ) < 2 ^ N := by positivity
  have : (2 : ℝ) ^ N * favg n m Q (Csig n N hn σ0)
      ≤ (2 : ℝ) ^ N * ((Fintype.card (Equiv.Perm (Fin n)) : ℝ)
          * (2 * Real.exp (-((m : ℝ) ^ 2) / (2 * N)))) := by
    rw [← hsum, hswap]; linarith
  exact le_of_mul_le_mul_left this h2

lemma count_bound (n m N : ℕ) (hn : n = N + N) (hN : 0 < N) (Q : Finset (Fin n)) :
    ∑ C ∈ Finset.univ.powersetCard N, bad n m Q C
      ≤ 2 * Real.exp (-((m : ℝ) ^ 2) / (2 * N)) * (n.choose N : ℝ) := by
  set K : ℝ := (Fintype.card (Equiv.Perm (Fin n)) : ℝ) with hK
  have hKpos : 0 < K := by rw [hK]; exact_mod_cast Fintype.card_pos
  let σ0 : Fin N → Bool := fun _ => true
  have hconst : ∀ C ∈ Finset.univ.powersetCard N,
      favg n m Q C = favg n m Q (Csig n N hn σ0) := by
    intro C hC
    rw [Finset.mem_powersetCard] at hC
    exact favg_const n m Q _ _ (by rw [Csig_card, hC.2])
  have hP : (Finset.univ.powersetCard N : Finset (Finset (Fin n))).card = n.choose N := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have e1 := sum_favg n m N Q
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, hP, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, nsmul_eq_mul] at e1
  have hb := favg_bound n m N hn hN Q σ0
  have hch : (0 : ℝ) ≤ (n.choose N : ℝ) := Nat.cast_nonneg _
  have : K * ∑ C ∈ Finset.univ.powersetCard N, bad n m Q C
      ≤ K * (2 * Real.exp (-((m : ℝ) ^ 2) / (2 * N)) * (n.choose N : ℝ)) := by
    rw [← e1]
    calc (n.choose N : ℝ) * favg n m Q (Csig n N hn σ0)
        ≤ (n.choose N : ℝ) * (K * (2 * Real.exp (-((m : ℝ) ^ 2) / (2 * N)))) :=
          mul_le_mul_of_nonneg_left hb hch
      _ = _ := by ring
  exact le_of_mul_le_mul_left this hKpos

end Pa5cc0e84

open NonmonotoneSubmod.QueryLB in
theorem solution (n m : ℕ) (hn : Even n) (hm : 1 ≤ m) (hmn : 2 * m ≤ n)
    (Q : Finset (Fin n)) :
    (((Finset.univ.powersetCard (n / 2)).filter (fun C => ¬ Balanced n m C Q)).card : ℝ) ≤
      2 * Real.exp (-(((m : ℝ) / n) ^ 2 * n / 4)) * (n.choose (n / 2) : ℝ) := by
  obtain ⟨N, hN⟩ := hn
  have hn2 : n / 2 = N := by omega
  have hNpos : 0 < N := by omega
  rw [hn2]
  have hcount : (((Finset.univ.powersetCard N).filter (fun C => ¬ Balanced n m C Q)).card : ℝ)
      = ∑ C ∈ Finset.univ.powersetCard N, Pa5cc0e84.bad n m Q C := by
    rw [Finset.natCast_card_filter]
    apply Finset.sum_congr rfl
    intro C _
    unfold Pa5cc0e84.bad
    split_ifs <;> simp_all
  rw [hcount]
  refine le_trans (Pa5cc0e84.count_bound n m N hN hNpos Q) ?_
  have hch : (0 : ℝ) ≤ (n.choose N : ℝ) := Nat.cast_nonneg _
  apply mul_le_mul_of_nonneg_right _ hch
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hnr : (n : ℝ) = N + N := by exact_mod_cast hN
  rw [hnr]
  have hm0 : (0 : ℝ) ≤ (m : ℝ) ^ 2 := sq_nonneg _
  rw [div_pow, neg_div, neg_le_neg_iff]
  rw [div_mul_eq_mul_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hNr hNr]
