-- Prove2me | solution 1 for MultiPriceOnline.Hardness.lemma_4_counts
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T08:07:37.506255+00:00
-- url     : https://prove2.me/submissions/7a170ee7-abd6-4b6e-a87b-72ccc15ab394

import Mathlib
import Definitions.Def_MultiPriceOnline_Hardness_PriceSet
import Definitions.Def_MultiPriceOnline_Hardness_Model
import Definitions.Def_MultiPriceOnline_Hardness_Instance

open Finset MultiPriceOnline.Hardness

namespace L4C

variable {n : ℕ}

noncomputable def itm (k m : ℕ) (alg : OnlineAlg n) (A : Arrival n) (t : ℕ) : Option (Fin n) :=
  (sale m alg A (stockAt k m alg A t) t).map Prod.fst

lemma sale_some {m : ℕ} {alg : OnlineAlg n} {A : Arrival n} {stock : Fin n → ℕ} {t : ℕ}
    {y : Fin n} {j : ℕ} (h : sale m alg A stock t = some (y, j)) :
    t < A.T ∧ 0 < stock y ∧ 1 ≤ j ∧ j ≤ m ∧ row A t y j = 1 := by
  unfold sale at h
  revert h
  rcases alg t (history A t) with _ | ⟨i', j'⟩
  · simp
  · dsimp only
    split_ifs with hc
    · intro h; simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact hc
    · simp

lemma sale_congr {m : ℕ} (alg : OnlineAlg n) (A A' : Arrival n) (hT : A.T = A'.T)
    (stock : Fin n → ℕ) (t : ℕ) (hrow : ∀ s ≤ t, row A s = row A' s) :
    sale m alg A stock t = sale m alg A' stock t := by
  have hh : history A t = history A' t := funext fun s => hrow s (Nat.lt_succ_iff.1 s.2)
  unfold sale; rw [hh, hT, hrow t le_rfl]

lemma stock_congr (k m : ℕ) (alg : OnlineAlg n) (A A' : Arrival n) (hT : A.T = A'.T) (t₀ : ℕ)
    (hrow : ∀ s < t₀, row A s = row A' s) :
    ∀ t ≤ t₀, stockAt k m alg A t = stockAt k m alg A' t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    have h1 := ih (by omega)
    have h2 : sale m alg A (stockAt k m alg A t) t = sale m alg A' (stockAt k m alg A' t) t := by
      rw [h1]; exact sale_congr alg A A' hT _ t (fun s hs => hrow s (by omega))
    simp only [stockAt]
    rw [h2, h1]

lemma stock_count (k m : ℕ) (alg : OnlineAlg n) (A : Arrival n) (x : Fin n) :
    ∀ t, stockAt k m alg A t x + ((range t).filter (fun s => itm k m alg A s = some x)).card = k := by
  intro t
  induction t with
  | zero => simp [stockAt]
  | succ t ih =>
    rw [range_add_one, filter_insert]
    rcases h : sale m alg A (stockAt k m alg A t) t with _ | ⟨y, j⟩
    · have hI : itm k m alg A t = none := by simp [itm, h]
      have hs : stockAt k m alg A (t + 1) = stockAt k m alg A t := by
        simp only [stockAt]; rw [h]
      rw [hs, hI]; simpa using ih
    · have hI : itm k m alg A t = some y := by simp [itm, h]
      have hpos := (sale_some h).2.1
      have hs : stockAt k m alg A (t + 1) =
          Function.update (stockAt k m alg A t) y (stockAt k m alg A t y - 1) := by
        simp only [stockAt]; rw [h]
      rw [hs, hI]
      by_cases hxy : x = y
      · subst hxy
        simp only [if_true, Function.update_self]
        rw [card_insert_of_notMem (by simp)]
        omega
      · have : ¬ (some y = some x) := by simp [Ne.symm hxy]
        simp only [this, if_false, Function.update_of_ne hxy]
        exact ih

lemma row_hard (k m : ℕ) (B : ℕ → ℝ) (π : Equiv.Perm (Fin n)) (s : ℕ) :
    row (hardInstance n k m B π) s = fun x j =>
      if s < n * k ∧ s / k ≤ ((π.symm x : Fin n) : ℕ) ∧ 1 ≤ j ∧ j ≤ phaseOf n m B (s / k)
      then 1 else 0 := by
  funext x j
  unfold row
  by_cases hs : s < n * k
  · have hs' : s < (hardInstance n k m B π).T := hs
    rw [dif_pos hs']
    simp only [hardInstance]
    by_cases hc : s / k ≤ ((π.symm x : Fin n) : ℕ) ∧ 1 ≤ j ∧ j ≤ phaseOf n m B (s / k)
    · rw [if_pos hc, if_pos ⟨hs, hc⟩]
    · rw [if_neg hc, if_neg (fun h => hc h.2)]
  · have hs' : ¬ s < (hardInstance n k m B π).T := hs
    rw [dif_neg hs', if_neg (fun h => hs h.1)]

lemma swap_le_iff (g : ℕ) (i i' p : Fin n) (hi : g ≤ (i : ℕ)) (hi' : g ≤ (i' : ℕ)) (c : ℕ)
    (hc : c ≤ g) : c ≤ ((Equiv.swap i i' p : Fin n) : ℕ) ↔ c ≤ (p : ℕ) := by
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; omega
  · subst h2; omega
  · rfl

end L4C

open L4C

theorem solution {m : ℕ} {r : ℕ → ℝ} (hr : MultiPriceOnline.Balance.IsPriceSet m r)
    (B : ℕ → ℝ) (n k : ℕ) (hn : 1 ≤ n) (alg : OnlineAlg n) :
    ∃ q : ℕ → ℝ, (∀ t < n, 0 ≤ q t) ∧ (∑ t ∈ range n, q t) ≤ k ∧
      (∀ t < n, ((n : ℝ) - t) * q t ≤ k) ∧
      ((Nat.factorial n : ℝ))⁻¹ * ∑ π : Equiv.Perm (Fin n), revenue k m r alg (hardInstance n k m B π)
        ≤ ∑ t ∈ range n, r (phaseOf n m B t) * ((n : ℝ) - t) * q t := by
  -- prices
  have hrmono : ∀ d j : ℕ, 1 ≤ j → j + d ≤ m → r j ≤ r (j + d) := by
    intro d
    induction d with
    | zero => intro j _ _; simp
    | succ d ih =>
      intro j hj hjd
      have h1 := ih j hj (by omega)
      have h2 := hr.2 (j + d) (by omega) (by omega)
      rw [show j + (d + 1) = j + d + 1 by omega]; linarith
  have hrle : ∀ j j', 1 ≤ j → j ≤ j' → j' ≤ m → r j ≤ r j' := by
    intro j j' hj hjj' hj'
    have := hrmono (j' - j) j hj (by omega)
    rwa [show j + (j' - j) = j' by omega] at this
  have hrpos : ∀ j, 1 ≤ j → j ≤ m → 0 < r j := fun j hj hjm =>
    lt_of_lt_of_le hr.1 (hrle 1 j le_rfl hj hjm)
  have hph : ∀ g, 1 ≤ phaseOf n m B g ∧ (1 ≤ m → phaseOf n m B g ≤ m) := by
    intro g
    unfold phaseOf
    refine ⟨by omega, fun hm => ?_⟩
    have := Finset.card_filter_le (Icc 2 m) (fun j => ⌊(1 - B j) * (n : ℝ)⌋₊ ≤ g)
    simp at this
    omega
  -- notation
  set A : Equiv.Perm (Fin n) → Arrival n := fun π => hardInstance n k m B π with hA
  set Q : Equiv.Perm (Fin n) → ℕ → Fin n → ℝ := fun π g y =>
    ∑ t ∈ range (n * k), if t / k = g ∧ itm k m alg (A π) t = some y then (1 : ℝ) else 0 with hQ
  have hQnn : ∀ π g y, 0 ≤ Q π g y := by
    intro π g y; apply sum_nonneg; intros; split_ifs <;> norm_num
  have hT : ∀ π, (A π).T = n * k := fun π => rfl
  -- inventory bound
  have hQinv : ∀ π y, ∑ g ∈ range n, Q π g y ≤ k := by
    intro π y
    have h1 : ∑ g ∈ range n, Q π g y =
        ∑ t ∈ range (n * k), if itm k m alg (A π) t = some y then (1 : ℝ) else 0 := by
      simp only [hQ]
      rw [sum_comm]
      apply sum_congr rfl
      intro t ht
      have htn : t / k ∈ range n := by
        simp only [mem_range] at ht ⊢
        exact Nat.div_lt_of_lt_mul (by rwa [mul_comm] at ht)
      simp_rw [ite_and]
      rw [sum_ite_eq (range n) (t / k)]
      simp [htn]
    rw [h1, sum_boole]
    have := stock_count k m alg (A π) y (n * k)
    have h2 : (((range (n * k)).filter (fun s => itm k m alg (A π) s = some y)).card : ℝ) ≤ k := by
      exact_mod_cast (by omega : ((range (n * k)).filter (fun s => itm k m alg (A π) s = some y)).card ≤ k)
    simpa using h2
  -- group-size bound
  have hone : ∀ (o : Option (Fin n)), ∑ y : Fin n, (if o = some y then (1 : ℝ) else 0) ≤ 1 := by
    intro o
    rcases o with _ | z
    · simp
    · simp
  have hgrp_card : ∀ g, ∑ t ∈ range (n * k), (if t / k = g then (1 : ℝ) else 0) ≤ k := by
    intro g
    rw [sum_boole]
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0; simp
    · have hsub : (range (n * k)).filter (fun t => t / k = g) ⊆ Ico (g * k) (g * k + k) := by
        intro t ht
        simp only [mem_filter, mem_range] at ht
        simp only [mem_Ico]
        constructor
        · rw [← ht.2]; exact Nat.div_mul_le_self t k
        · have := Nat.lt_div_mul_add (a := t) hk0
          rw [ht.2] at this; exact this
      have := card_le_card hsub
      simp only [Nat.card_Ico, Nat.add_sub_cancel_left] at this
      exact_mod_cast this
  have hQgrp : ∀ π g, ∑ y : Fin n, Q π g y ≤ k := by
    intro π g
    simp only [hQ]
    rw [sum_comm]
    calc ∑ t ∈ range (n * k), ∑ y : Fin n,
          (if t / k = g ∧ itm k m alg (A π) t = some y then (1 : ℝ) else 0)
        ≤ ∑ t ∈ range (n * k), (if t / k = g then (1 : ℝ) else 0) := by
          apply sum_le_sum
          intro t _
          simp_rw [ite_and]
          split_ifs
          · exact hone _
          · simp
      _ ≤ k := hgrp_card g
  -- zero below the diagonal
  have hQzero : ∀ π g (i : Fin n), (i : ℕ) < g → Q π g (π i) = 0 := by
    intro π g i hig
    apply sum_eq_zero
    intro t ht
    rw [if_neg]
    rintro ⟨htg, hI⟩
    simp only [itm, Option.map_eq_some_iff] at hI
    obtain ⟨⟨y, j⟩, hs, hy⟩ := hI
    simp only at hy
    subst hy
    have := (sale_some hs).2.2.2.2
    rw [row_hard] at this
    simp only at this
    split_ifs at this with hc
    · simp at hc; omega
    · norm_num at this
  -- symmetry
  have hQsym : ∀ g (i i' : Fin n), g ≤ (i : ℕ) → g ≤ (i' : ℕ) →
      ∑ π : Equiv.Perm (Fin n), Q π g (π i) = ∑ π : Equiv.Perm (Fin n), Q π g (π i') := by
    intro g i i' hi hi'
    set σ := Equiv.swap i i' with hσ
    have hterm : ∀ π : Equiv.Perm (Fin n), Q π g (π i) = Q (π * σ) g ((π * σ) i') := by
      intro π
      have hval : (π * σ) i' = π i := by simp [hσ, Equiv.Perm.mul_apply]
      rw [hval]
      have hsymm : ∀ x, (π * σ).symm x = σ (π.symm x) := by
        intro x
        rw [Equiv.symm_apply_eq]
        simp [hσ, Equiv.Perm.mul_apply]
      have hrow : ∀ s, s / k ≤ g → row (A π) s = row (A (π * σ)) s := by
        intro s hs
        simp only [hA, row_hard]
        funext x j
        have := swap_le_iff g i i' (π.symm x) hi hi' (s / k) hs
        rw [hsymm x]
        by_cases hc : s / k ≤ ((π.symm x : Fin n) : ℕ)
        · have hc' := this.mpr hc
          by_cases hrest : s < n * k ∧ 1 ≤ j ∧ j ≤ phaseOf n m B (s / k)
          · rw [if_pos ⟨hrest.1, hc, hrest.2⟩, if_pos ⟨hrest.1, hc', hrest.2⟩]
          · rw [if_neg (fun h => hrest ⟨h.1, h.2.2⟩), if_neg (fun h => hrest ⟨h.1, h.2.2⟩)]
        · have hc' : ¬ s / k ≤ ((σ (π.symm x) : Fin n) : ℕ) := fun h => hc (this.mp h)
          rw [if_neg (fun h => hc h.2.1), if_neg (fun h => hc' h.2.1)]
      simp only [hQ]
      apply sum_congr rfl
      intro t ht
      by_cases htg : t / k = g
      · have hst : stockAt k m alg (A π) t = stockAt k m alg (A (π * σ)) t :=
          stock_congr k m alg (A π) (A (π * σ)) rfl t (fun s hs => hrow s (by rw [← htg]; exact Nat.div_le_div_right hs.le)) t le_rfl
        have hsl : sale m alg (A π) (stockAt k m alg (A π) t) t =
            sale m alg (A (π * σ)) (stockAt k m alg (A (π * σ)) t) t := by
          rw [hst]
          exact sale_congr alg (A π) (A (π * σ)) rfl _ t (fun s hs => hrow s (by rw [← htg]; exact Nat.div_le_div_right hs))
        have hI : itm k m alg (A π) t = itm k m alg (A (π * σ)) t := by simp only [itm, hsl]
        rw [hI]
      · simp [htg]
    calc ∑ π : Equiv.Perm (Fin n), Q π g (π i)
        = ∑ π : Equiv.Perm (Fin n), Q (π * σ) g ((π * σ) i') := sum_congr rfl (fun π _ => hterm π)
      _ = ∑ π : Equiv.Perm (Fin n), Q π g (π i') :=
          Equiv.sum_comp (Equiv.mulRight σ) (fun π => Q π g (π i'))
  -- revenue bound
  have hrev : ∀ π, revenue k m r alg (A π) ≤ ∑ g ∈ range n, r (phaseOf n m B g) * ∑ y : Fin n, Q π g y := by
    intro π
    have hval : ∀ t ∈ range (n * k),
        (match sale m alg (A π) (stockAt k m alg (A π) t) t with
          | some (_, j) => r j
          | none => 0 : ℝ) ≤
        r (phaseOf n m B (t / k)) * ∑ y : Fin n, (if itm k m alg (A π) t = some y then (1 : ℝ) else 0) := by
      intro t ht
      rcases h : sale m alg (A π) (stockAt k m alg (A π) t) t with _ | ⟨y, j⟩
      · simp [itm, h]
      · have hI : itm k m alg (A π) t = some y := by simp [itm, h]
        rw [hI]
        simp only [Option.some.injEq, sum_ite_eq, mem_univ, if_true, mul_one]
        obtain ⟨-, -, hj1, hjm, hrw⟩ := sale_some h
        rw [row_hard] at hrw
        simp only at hrw
        split_ifs at hrw with hc
        · exact hrle j _ hj1 hc.2.2.2 ((hph _).2 (by omega))
        · norm_num at hrw
    have hswap : ∑ g ∈ range n, r (phaseOf n m B g) * ∑ y : Fin n, Q π g y =
        ∑ t ∈ range (n * k), r (phaseOf n m B (t / k)) *
          ∑ y : Fin n, (if itm k m alg (A π) t = some y then (1 : ℝ) else 0) := by
      calc ∑ g ∈ range n, r (phaseOf n m B g) * ∑ y : Fin n, Q π g y
          = ∑ g ∈ range n, ∑ t ∈ range (n * k), ∑ y : Fin n, r (phaseOf n m B g) *
              (if t / k = g ∧ itm k m alg (A π) t = some y then (1 : ℝ) else 0) := by
            apply sum_congr rfl
            intro g _
            simp only [hQ]
            rw [mul_sum]
            simp_rw [mul_sum]
            rw [sum_comm]
        _ = ∑ t ∈ range (n * k), ∑ g ∈ range n, ∑ y : Fin n, r (phaseOf n m B g) *
              (if t / k = g ∧ itm k m alg (A π) t = some y then (1 : ℝ) else 0) := sum_comm
        _ = _ := by
            apply sum_congr rfl
            intro t ht
            have htn : t / k ∈ range n := by
              simp only [mem_range] at ht ⊢
              exact Nat.div_lt_of_lt_mul (by rwa [mul_comm] at ht)
            rw [sum_comm, mul_sum]
            apply sum_congr rfl
            intro y _
            simp_rw [ite_and]
            simp_rw [mul_ite, mul_zero]
            rw [sum_ite_eq (range n) (t / k)]
            simp [htn]
    rw [hswap]
    exact sum_le_sum hval
  -- assemble
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin n))).card = Nat.factorial n := by
    rw [card_univ, Fintype.card_perm, Fintype.card_fin]
  have hfact : (0 : ℝ) < Nat.factorial n := by exact_mod_cast Nat.factorial_pos n
  set last : Fin n := ⟨n - 1, by omega⟩ with hlast
  set q : ℕ → ℝ := fun g => ((Nat.factorial n : ℝ))⁻¹ * ∑ π : Equiv.Perm (Fin n), Q π g (π last) with hq
  have havg : ∀ g < n, ((Nat.factorial n : ℝ))⁻¹ * ∑ π : Equiv.Perm (Fin n), ∑ y : Fin n, Q π g y =
      ((n : ℝ) - g) * q g := by
    intro g hg
    have h1 : ∀ π : Equiv.Perm (Fin n), ∑ y : Fin n, Q π g y =
        ∑ i : Fin n, if g ≤ (i : ℕ) then Q π g (π i) else 0 := by
      intro π
      rw [← Equiv.sum_comp π (fun y => Q π g y)]
      apply sum_congr rfl
      intro i _
      split_ifs with h
      · rfl
      · exact hQzero π g i (by omega)
    simp_rw [h1]
    rw [sum_comm, mul_sum]
    have h2 : ∀ i : Fin n, ((Nat.factorial n : ℝ))⁻¹ *
        ∑ π : Equiv.Perm (Fin n), (if g ≤ (i : ℕ) then Q π g (π i) else 0) =
        if g ≤ (i : ℕ) then q g else 0 := by
      intro i
      split_ifs with h
      · simp only [hq]; congr 1
        exact hQsym g i last h (by simp [hlast]; omega)
      · simp
    simp_rw [h2]
    rw [Fin.sum_univ_eq_sum_range (fun i => if g ≤ i then q g else 0) n, sum_ite, sum_const_zero,
      add_zero, sum_const, nsmul_eq_mul]
    have hf : (range n).filter (fun i => g ≤ i) = Ico g n := by
      ext i; simp only [mem_filter, mem_range, mem_Ico]; omega
    rw [hf, Nat.card_Ico, Nat.cast_sub hg.le]
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · intro t _
    simp only [hq]
    exact mul_nonneg (by positivity) (sum_nonneg (fun π _ => hQnn _ _ _))
  · simp only [hq]
    rw [← mul_sum, sum_comm]
    calc ((Nat.factorial n : ℝ))⁻¹ * ∑ π : Equiv.Perm (Fin n), ∑ g ∈ range n, Q π g (π last)
        ≤ ((Nat.factorial n : ℝ))⁻¹ * ∑ _π : Equiv.Perm (Fin n), (k : ℝ) :=
          mul_le_mul_of_nonneg_left (sum_le_sum (fun π _ => hQinv π _)) (by positivity)
      _ = k := by
          rw [sum_const, hcard, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hfact.ne', one_mul]
  · intro t ht
    rw [← havg t ht]
    calc ((Nat.factorial n : ℝ))⁻¹ * ∑ π : Equiv.Perm (Fin n), ∑ y : Fin n, Q π t y
        ≤ ((Nat.factorial n : ℝ))⁻¹ * ∑ _π : Equiv.Perm (Fin n), (k : ℝ) :=
          mul_le_mul_of_nonneg_left (sum_le_sum (fun π _ => hQgrp π _)) (by positivity)
      _ = k := by
          rw [sum_const, hcard, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hfact.ne', one_mul]
  · calc ((Nat.factorial n : ℝ))⁻¹ * ∑ π : Equiv.Perm (Fin n), revenue k m r alg (hardInstance n k m B π)
        ≤ ((Nat.factorial n : ℝ))⁻¹ * ∑ π : Equiv.Perm (Fin n),
            ∑ g ∈ range n, r (phaseOf n m B g) * ∑ y : Fin n, Q π g y :=
          mul_le_mul_of_nonneg_left (sum_le_sum (fun π _ => hrev π)) (by positivity)
      _ = ∑ g ∈ range n, r (phaseOf n m B g) *
            (((Nat.factorial n : ℝ))⁻¹ * ∑ π : Equiv.Perm (Fin n), ∑ y : Fin n, Q π g y) := by
          rw [sum_comm, mul_sum]
          apply sum_congr rfl
          intro g _
          rw [← mul_sum]; ring
      _ = ∑ g ∈ range n, r (phaseOf n m B g) * ((n : ℝ) - g) * q g := by
          apply sum_congr rfl
          intro g hg
          rw [havg g (mem_range.1 hg)]; ring
