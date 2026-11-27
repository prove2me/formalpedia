-- Prove2me | solution 1 for HypercliqueAC0.FixedDepth.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:22:00.137499+00:00
-- url     : https://prove2.me/submissions/e78822a2-6274-42e9-a3b6-d2a4f755f364

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting

noncomputable section
namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

/-! ### Finite product-measure facts -/

lemma L46_weight_nonneg {X : Type*} [Fintype X] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : X → Bool) : 0 ≤ weight p x := by
  unfold weight OAI.Problem313.BiasedFourier.weight
  apply Finset.prod_nonneg
  intro i _
  cases x i
  · simp only [OAI.Problem313.BiasedFourier.scalarWeight_false]; linarith
  · simp only [OAI.Problem313.BiasedFourier.scalarWeight_true]; exact hp0

/-- The probability that all edges of `S` are present is `p ^ |S|`. -/
lemma L46_prob_all {X : Type*} [Fintype X] (p : ℝ) (S : Finset X) :
    ∑ x : X → Bool, weight p x * (if ∀ e ∈ S, x e = true then (1:ℝ) else 0) = p ^ S.card := by
  let g : X → Bool → ℝ := fun i b => if i ∈ S then (if b = true then p else 0)
      else OAI.Problem313.BiasedFourier.scalarWeight p b
  have h1 : ∀ x : X → Bool, weight p x * (if ∀ e ∈ S, x e = true then (1:ℝ) else 0)
      = ∏ i, g i (x i) := by
    intro x
    by_cases h : ∀ e ∈ S, x e = true
    · rw [if_pos h, mul_one]
      unfold weight OAI.Problem313.BiasedFourier.weight
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ S
      · simp [g, hi, h i hi]
      · simp [g, hi]
    · rw [if_neg h, mul_zero]
      push Not at h
      obtain ⟨i, hi, hxi⟩ := h
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [g, hi, hxi]
  rw [Finset.sum_congr rfl (fun x _ => h1 x), ← Fintype.prod_sum]
  have h2 : ∀ i, ∑ b : Bool, g i b = if i ∈ S then p else 1 := by
    intro i
    by_cases hi : i ∈ S
    · simp [g, hi]
    · simp [g, hi, OAI.Problem313.BiasedFourier.scalarWeight]
  rw [Finset.prod_congr rfl (fun i _ => h2 i), Fintype.prod_ite_mem, Finset.prod_const]

lemma L46_total {X : Type*} [Fintype X] (p : ℝ) :
    ∑ x : X → Bool, weight p x = 1 := by
  have h := L46_prob_all (X := X) p ∅
  simpa using h

/-! ### Combinatorics of edge sets -/

/-- Edges inside `B` but not inside `B'`. -/
def L46_sub {m r : ℕ} (B B' : Finset (Fin m)) : Finset (Edge m r) :=
  Finset.univ.filter (fun e : Edge m r => e.val ⊆ B ∧ ¬ e.val ⊆ B')

/-- Competing ℓ-sets. -/
def L46_I {m : ℕ} (ℓ : ℕ) (A : Finset (Fin m)) : Finset (Finset (Fin m)) :=
  Finset.univ.filter (fun Q : Finset (Fin m) => Q.card = ℓ ∧ Q ≠ A)

lemma L46_card_subsets {m r : ℕ} (B : Finset (Fin m)) :
    (Finset.univ.filter (fun e : Edge m r => e.val ⊆ B)).card = B.card.choose r := by
  rw [← Finset.card_powersetCard]
  apply Finset.card_bij (fun e _ => e.val)
  · intro e he
    rw [Finset.mem_filter] at he
    rw [Finset.mem_powersetCard]
    exact ⟨he.2, e.2⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro s hs
    rw [Finset.mem_powersetCard] at hs
    exact ⟨⟨s, hs.2⟩, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hs.1⟩, rfl⟩

lemma L46_card_sub {m r : ℕ} (B B' : Finset (Fin m)) (h : B' ⊆ B) :
    (L46_sub (r := r) B B').card = B.card.choose r - B'.card.choose r := by
  have hs : L46_sub (r := r) B B' = (Finset.univ.filter (fun e : Edge m r => e.val ⊆ B)) \
      (Finset.univ.filter (fun e : Edge m r => e.val ⊆ B')) := by
    ext e
    simp only [L46_sub, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
  rw [hs, Finset.card_sdiff_of_subset, L46_card_subsets, L46_card_subsets]
  intro e he
  rw [Finset.mem_filter] at he ⊢
  exact ⟨he.1, he.2.trans h⟩

/-- Union bound: if failure of `E` forces all edges of some `S i` or some `T k` to be present. -/
lemma L46_union {X ι κ : Type*} [Fintype X] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E : (X → Bool) → Prop) (I : Finset ι) (S : ι → Finset X) (J : Finset κ)
    (T : κ → Finset X)
    (h : ∀ x, ¬ E x → (∃ i ∈ I, ∀ e ∈ S i, x e = true) ∨ (∃ k ∈ J, ∀ e ∈ T k, x e = true)) :
    1 - (∑ i ∈ I, p ^ (S i).card) - (∑ k ∈ J, p ^ (T k).card) ≤ probability p E := by
  unfold probability expectation
  have hpt : ∀ x : X → Bool,
      1 - (∑ i ∈ I, (if ∀ e ∈ S i, x e = true then (1:ℝ) else 0))
        - (∑ k ∈ J, (if ∀ e ∈ T k, x e = true then (1:ℝ) else 0))
      ≤ (if E x then (1:ℝ) else 0) := by
    intro x
    have hn1 : 0 ≤ ∑ i ∈ I, (if ∀ e ∈ S i, x e = true then (1:ℝ) else 0) :=
      Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
    have hn2 : 0 ≤ ∑ k ∈ J, (if ∀ e ∈ T k, x e = true then (1:ℝ) else 0) :=
      Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
    by_cases hE : E x
    · rw [if_pos hE]; linarith
    · rw [if_neg hE]
      rcases h x hE with ⟨i, hi, hall⟩ | ⟨k, hk, hall⟩
      · have hs := Finset.single_le_sum
          (f := fun i => (if ∀ e ∈ S i, x e = true then (1:ℝ) else 0))
          (fun _ _ => by split_ifs <;> norm_num) hi
        simp only [if_pos hall] at hs
        linarith
      · have hs := Finset.single_le_sum
          (f := fun k => (if ∀ e ∈ T k, x e = true then (1:ℝ) else 0))
          (fun _ _ => by split_ifs <;> norm_num) hk
        simp only [if_pos hall] at hs
        linarith
  have e1 : ∑ x : X → Bool, ∑ i ∈ I, weight p x *
      (if ∀ e ∈ S i, x e = true then (1:ℝ) else 0) = ∑ i ∈ I, p ^ (S i).card := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => L46_prob_all p _)
  have e2 : ∑ x : X → Bool, ∑ k ∈ J, weight p x *
      (if ∀ e ∈ T k, x e = true then (1:ℝ) else 0) = ∑ k ∈ J, p ^ (T k).card := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun k _ => L46_prob_all p _)
  have key : ∑ x : X → Bool, weight p x *
      (1 - (∑ i ∈ I, (if ∀ e ∈ S i, x e = true then (1:ℝ) else 0))
        - (∑ k ∈ J, (if ∀ e ∈ T k, x e = true then (1:ℝ) else 0)))
      = 1 - (∑ i ∈ I, p ^ (S i).card) - (∑ k ∈ J, p ^ (T k).card) := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [L46_total, e1, e2]
  rw [← key]
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_mul_of_nonneg_left (hpt x) (L46_weight_nonneg hp0 hp1 x)

/-- Failure of the good event yields a competing ℓ-set or a vertex with all edges present. -/
lemma L46_bad {m r ℓ : ℕ} (A : Finset (Fin m)) (x : Edge m r → Bool)
    (hg : ¬ plantedGood ℓ A x) :
    (∃ Q ∈ L46_I ℓ A, ∀ e ∈ L46_sub (r := r) Q (Q ∩ A), x e = true) ∨
      (∃ u ∈ A, ∀ e ∈ L46_sub (r := r) A (A.erase u), x e = true) := by
  unfold plantedGood at hg
  rw [not_and_or] at hg
  rcases hg with h | h
  · push Not at h
    obtain ⟨Q, hQc, hQall, hQA⟩ := h
    refine Or.inl ⟨Q, ?_, ?_⟩
    · rw [L46_I, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hQc, hQA⟩
    · intro e he
      rw [L46_sub, Finset.mem_filter] at he
      have h1 := hQall e he.2.1
      simp only [plant, Bool.or_eq_true, decide_eq_true_eq] at h1
      rcases h1 with h1 | h1
      · exact h1
      · exact absurd (Finset.subset_inter he.2.1 h1) he.2.2
  · push Not at h
    obtain ⟨u, hu, hall⟩ := h
    refine Or.inr ⟨u, hu, ?_⟩
    intro e he
    rw [L46_sub, Finset.mem_filter] at he
    have hue : u ∈ e.val := by
      by_contra hne
      apply he.2.2
      intro y hy
      rw [Finset.mem_erase]
      exact ⟨fun hyu => hne (hyu ▸ hy), he.2.1 hy⟩
    have := hall e he.2.1 hue
    simpa using this

lemma L46_fiber_card {m ℓ : ℕ} (A : Finset (Fin m)) (hA : A.card = ℓ) (j : ℕ) :
    ((L46_I ℓ A).filter (fun Q => (Q \ A).card = j)).card ≤ m.choose j * ℓ.choose j := by
  have hT : ((Finset.univ : Finset (Fin m)).powersetCard j ×ˢ A.powersetCard j).card
      = m.choose j * ℓ.choose j := by
    rw [Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin, hA]
  rw [← hT]
  apply Finset.card_le_card_of_injOn (fun Q => (Q \ A, A \ Q))
  · intro Q hQ
    dsimp only
    rw [Finset.mem_coe, Finset.mem_filter, L46_I, Finset.mem_filter] at hQ
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard]
    refine ⟨⟨Finset.subset_univ _, hQ.2⟩, Finset.sdiff_subset, ?_⟩
    have h1 := Finset.card_sdiff_add_card_inter Q A
    have h2 := Finset.card_sdiff_add_card_inter A Q
    rw [Finset.inter_comm] at h2
    show (A \ Q).card = j
    omega
  · intro Q1 _ Q2 _ h
    simp only [Prod.mk.injEq] at h
    ext y
    have a1 := Finset.ext_iff.1 h.1 y
    have a2 := Finset.ext_iff.1 h.2 y
    simp only [Finset.mem_sdiff] at a1 a2
    by_cases hy : y ∈ A <;> tauto

/-! ### Numerical estimates -/

lemma L46_choose_ratio (a ℓ r : ℕ) (ha : a ≤ ℓ) (hr : 2 ≤ r) :
    a.choose r * ℓ.choose 2 ≤ a.choose 2 * ℓ.choose r := by
  have h1 := Nat.choose_mul (n := a) (k := r) (s := 2) hr
  have h2 := Nat.choose_mul (n := ℓ) (k := r) (s := 2) hr
  have h3 : (a - 2).choose (r - 2) ≤ (ℓ - 2).choose (r - 2) := Nat.choose_le_choose _ (by omega)
  have hpos : 0 < r.choose 2 := Nat.choose_pos hr
  apply Nat.le_of_mul_le_mul_right _ hpos
  calc a.choose r * ℓ.choose 2 * r.choose 2 = (a.choose r * r.choose 2) * ℓ.choose 2 := by ring
    _ = a.choose 2 * (a - 2).choose (r - 2) * ℓ.choose 2 := by rw [h1]
    _ ≤ a.choose 2 * (ℓ - 2).choose (r - 2) * ℓ.choose 2 := by gcongr
    _ = a.choose 2 * (ℓ.choose 2 * (ℓ - 2).choose (r - 2)) := by ring
    _ = a.choose 2 * (ℓ.choose r * r.choose 2) := by rw [h2]
    _ = a.choose 2 * ℓ.choose r * r.choose 2 := by ring

/-- `ℓ · (C(ℓ,r) - C(ℓ-j,r)) / C(ℓ,r) ≥ j (2 - (j-1)/(ℓ-1))`. -/
lemma L46_count_ge (ℓ r j : ℕ) (hr : 2 ≤ r) (hrℓ : r ≤ ℓ) (hjℓ : j ≤ ℓ) :
    (j : ℝ) * (2 - ((j:ℝ) - 1) / ((ℓ:ℝ) - 1)) ≤
      (ℓ : ℝ) * ((ℓ.choose r - (ℓ - j).choose r : ℕ) : ℝ) / (ℓ.choose r : ℝ) := by
  have hN : (0:ℝ) < ℓ.choose r := by exact_mod_cast Nat.choose_pos hrℓ
  have hle : (ℓ - j).choose r ≤ ℓ.choose r := Nat.choose_le_choose _ (Nat.sub_le _ _)
  have hrat := L46_choose_ratio (ℓ - j) ℓ r (Nat.sub_le _ _) hr
  have hratR : ((ℓ - j).choose r : ℝ) * (ℓ.choose 2 : ℝ)
      ≤ ((ℓ - j).choose 2 : ℝ) * (ℓ.choose r : ℝ) := by exact_mod_cast hrat
  rw [Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_sub hjℓ] at hratR
  rw [Nat.cast_sub hle]
  have hℓ1 : (1:ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  have hl1 : (0:ℝ) < ℓ - 1 := by linarith
  rw [le_div_iff₀ hN]
  rw [show (j:ℝ) * (2 - ((j:ℝ) - 1) / ((ℓ:ℝ) - 1)) = j * (2*ℓ - j - 1) / (ℓ - 1) by
    field_simp; ring]
  rw [div_mul_eq_mul_div, div_le_iff₀ hl1]
  nlinarith [hratR]

lemma L46_pow_bound {m ℓ r : ℕ} {p δ : ℝ} (hm : (1:ℝ) ≤ m) (hp0 : 0 < p)
    (hp : p ≤ (m : ℝ) ^ (-((1 + δ) * (ℓ : ℝ)) / (Nat.choose ℓ r : ℝ))) (hδ : 0 < δ)
    (hr : 2 ≤ r) (hrℓ : r ≤ ℓ) (j : ℕ) (hjℓ : j ≤ ℓ) :
    p ^ (ℓ.choose r - (ℓ - j).choose r) ≤
      (m : ℝ) ^ (-(1 + δ) * ((j : ℝ) * (2 - ((j:ℝ) - 1) / ((ℓ:ℝ) - 1)))) := by
  have hm0 : (0:ℝ) ≤ m := by linarith
  calc p ^ (ℓ.choose r - (ℓ - j).choose r)
      ≤ ((m : ℝ) ^ (-((1 + δ) * (ℓ : ℝ)) / (Nat.choose ℓ r : ℝ))) ^
          (ℓ.choose r - (ℓ - j).choose r) :=
        pow_le_pow_left₀ hp0.le hp _
    _ = (m:ℝ) ^ (-((1 + δ) * (ℓ : ℝ)) / (Nat.choose ℓ r : ℝ) *
          ((ℓ.choose r - (ℓ - j).choose r : ℕ) : ℝ)) :=
        (Real.rpow_mul_natCast hm0 _ _).symm
    _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hm
        have h := L46_count_ge ℓ r j hr hrℓ hjℓ
        have h2 := mul_le_mul_of_nonneg_left h (by linarith : (0:ℝ) ≤ 1 + δ)
        have e : -((1 + δ) * (ℓ : ℝ)) / (Nat.choose ℓ r : ℝ) *
            ((ℓ.choose r - (ℓ - j).choose r : ℕ) : ℝ)
            = -((1 + δ) * ((ℓ : ℝ) * ((ℓ.choose r - (ℓ - j).choose r : ℕ) : ℝ) /
              (ℓ.choose r : ℝ))) := by ring
        rw [e]
        linarith

lemma L46_choose_le_exp (n j : ℕ) (hj : 1 ≤ j) :
    (n.choose j : ℝ) ≤ (Real.exp 1 * n / j) ^ j := by
  have h1 := Nat.choose_le_pow_div (α := ℝ) j n
  have h2 := Real.pow_div_factorial_le_exp (j:ℝ) (Nat.cast_nonneg _) j
  have hjpos : (0:ℝ) < j := by exact_mod_cast hj
  have hf : (0:ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  rw [div_le_iff₀ hf] at h2
  calc (n.choose j : ℝ) ≤ n ^ j / j.factorial := h1
    _ ≤ (Real.exp 1 * n / j) ^ j := by
      rw [div_pow, mul_pow, Real.exp_one_pow, div_le_div_iff₀ hf (by positivity)]
      calc (n:ℝ) ^ j * (j:ℝ) ^ j ≤ n ^ j * (Real.exp j * j.factorial) := by gcongr
        _ = _ := by ring

lemma L46_term {m ℓ r : ℕ} {p δ : ℝ} (hm : (ℓ:ℝ) ≤ m) (hp0 : 0 < p)
    (hp : p ≤ (m : ℝ) ^ (-((1 + δ) * (ℓ : ℝ)) / (Nat.choose ℓ r : ℝ))) (hδ : 0 < δ)
    (hr : 2 ≤ r) (hrℓ : r ≤ ℓ) (j : ℕ) (hj1 : 1 ≤ j) (hjℓ : j ≤ ℓ) :
    (m.choose j : ℝ) * ℓ.choose j * p ^ (ℓ.choose r - (ℓ - j).choose r)
      ≤ (Real.exp 2 * (m:ℝ) ^ (-δ)) ^ j := by
  have hℓ2 : (2:ℝ) ≤ ℓ := by exact_mod_cast (le_trans hr hrℓ)
  have hm1 : (1:ℝ) ≤ m := by linarith
  have hmpos : (0:ℝ) < m := by linarith
  have hℓpos : (0:ℝ) < ℓ := by linarith
  have hjpos : (0:ℝ) < j := by exact_mod_cast hj1
  have hj1R : (1:ℝ) ≤ j := by exact_mod_cast hj1
  have hjℓR : (j:ℝ) ≤ ℓ := by exact_mod_cast hjℓ
  have hPE := L46_pow_bound hm1 hp0 hp hδ hr hrℓ j hjℓ
  set s : ℝ := ((j:ℝ) - 1) / ((ℓ:ℝ) - 1) with hs
  set M : ℝ := (m:ℝ) ^ (-(1 + δ) * (2 - s)) with hM
  have hME : (m:ℝ) ^ (-(1 + δ) * ((j : ℝ) * (2 - s))) = M ^ j := by
    rw [hM, ← Real.rpow_mul_natCast hmpos.le]; ring_nf
  have hs0 : 0 ≤ s := div_nonneg (by linarith) (by linarith)
  have hs1 : s ≤ 1 := by rw [hs, div_le_one (by linarith)]; linarith
  have hl1 : (ℓ:ℝ) - 1 ≠ 0 := by
    have : (0:ℝ) < (ℓ:ℝ) - 1 := by linarith
    exact this.ne'
  have hjs : (j:ℝ) = (1 - s) * 1 + s * ℓ := by
    rw [hs]; field_simp; ring
  have hcon : s * Real.log ℓ ≤ Real.log j := by
    have := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 - s) (w₂ := s) (p₁ := 1)
      (p₂ := ℓ) (by linarith) hs0 zero_le_one hℓpos.le (by ring)
    rw [Real.one_rpow, one_mul, ← hjs] at this
    have h' := Real.log_le_log (by positivity) this
    rwa [Real.log_rpow hℓpos] at h'
  have hlogj : 0 ≤ Real.log j := Real.log_nonneg hj1R
  have hlogℓm : Real.log ℓ ≤ Real.log m := Real.log_le_log hℓpos hm
  have hL0 : 0 ≤ Real.log m := Real.log_nonneg hm1
  have hbase0 : (ℓ:ℝ) * m * M ≤ j * j * (m:ℝ) ^ (-δ) := by
    have e1 : (ℓ:ℝ) * m * M
        = Real.exp (Real.log ℓ + Real.log m + Real.log m * (-(1 + δ) * (2 - s))) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hℓpos, Real.exp_log hmpos,
        ← Real.rpow_def_of_pos hmpos]
    have e2 : (j:ℝ) * j * (m:ℝ) ^ (-δ)
        = Real.exp (Real.log j + Real.log j + Real.log m * (-δ)) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hjpos, ← Real.rpow_def_of_pos hmpos]
    rw [e1, e2, Real.exp_le_exp]
    have P1 : 0 ≤ δ * (1 - s) * Real.log m :=
      mul_nonneg (mul_nonneg hδ.le (by linarith)) hL0
    have P2 : 0 ≤ (1 - s) * (Real.log m - Real.log ℓ) := mul_nonneg (by linarith) (by linarith)
    nlinarith [P1, P2, hcon, hlogj]
  have hbase : (Real.exp 1 * m / j) * (Real.exp 1 * ℓ / j) * M
      ≤ Real.exp 2 * (m:ℝ) ^ (-δ) := by
    calc (Real.exp 1 * m / j) * (Real.exp 1 * ℓ / j) * M
        = (Real.exp 1 * Real.exp 1) / (j * j) * ((ℓ:ℝ) * m * M) := by
          field_simp
      _ ≤ (Real.exp 1 * Real.exp 1) / (j * j) * (j * j * (m:ℝ) ^ (-δ)) :=
          mul_le_mul_of_nonneg_left hbase0 (by positivity)
      _ = (Real.exp 1 * Real.exp 1) * (m:ℝ) ^ (-δ) := by field_simp
      _ = Real.exp 2 * (m:ℝ) ^ (-δ) := by rw [← Real.exp_add]; norm_num
  calc (m.choose j : ℝ) * ℓ.choose j * p ^ (ℓ.choose r - (ℓ - j).choose r)
      ≤ (Real.exp 1 * m / j) ^ j * (Real.exp 1 * ℓ / j) ^ j * M ^ j := by
        rw [← hME]
        gcongr
        · exact L46_choose_le_exp m j hj1
        · exact L46_choose_le_exp ℓ j hj1
    _ = ((Real.exp 1 * m / j) * (Real.exp 1 * ℓ / j) * M) ^ j := by rw [mul_pow, mul_pow]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hbase j

end HypercliqueAC0.FixedDepth

open HypercliqueAC0.FixedDepth in
attribute [local instance] Classical.propDecidable Classical.decEq in
theorem solution :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℕ, 2 ≤ r → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (ℓ : ℕ) (p : ℝ) (A : Finset (Fin m)),
        r ≤ ℓ → ℓ ≤ m → 0 < p →
        p ≤ (m : ℝ) ^ (-((1 + δ) * (ℓ : ℝ)) / (Nat.choose ℓ r : ℝ)) →
        A.card = ℓ →
        probability p (plantedGood (r := r) ℓ A) ≥ 1 - K * (m : ℝ) ^ (-δ) := by
  refine ⟨2 * Real.exp 2 + 1, by positivity, ?_⟩
  intro r hr δ hδ hδ1
  refine ⟨⌈(2 * Real.exp 2) ^ δ⁻¹⌉₊, ?_⟩
  intro m hm₀ ℓ p A hrℓ hℓm hp0 hp hA
  have hℓm' : (ℓ:ℝ) ≤ m := by exact_mod_cast hℓm
  have hm2 : (2:ℝ) ≤ m := by exact_mod_cast (le_trans (le_trans hr hrℓ) hℓm)
  have hm1 : (1:ℝ) ≤ m := by linarith
  have hmpos : (0:ℝ) < m := by linarith
  have hp1 : p ≤ 1 := by
    refine hp.trans (Real.rpow_le_one_of_one_le_of_nonpos hm1 ?_)
    rw [neg_div]
    exact neg_nonpos.2 (by positivity)
  have hmδ : 2 * Real.exp 2 ≤ (m:ℝ) ^ δ := by
    have h1 : (2 * Real.exp 2) ^ δ⁻¹ ≤ (m:ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hm₀)
    have h2 := Real.rpow_le_rpow (by positivity) h1 hδ.le
    rwa [Real.rpow_inv_rpow (by positivity) hδ.ne'] at h2
  have hq0 : 0 ≤ Real.exp 2 * (m:ℝ) ^ (-δ) := by positivity
  have hq2 : Real.exp 2 * (m:ℝ) ^ (-δ) ≤ 1 / 2 := by
    rw [Real.rpow_neg hmpos.le, mul_inv_le_iff₀ (by positivity)]
    linarith
  have hred := L46_union hp0.le hp1 (plantedGood (r := r) ℓ A) (L46_I ℓ A)
    (fun Q => L46_sub (r := r) Q (Q ∩ A)) A (fun u => L46_sub (r := r) A (A.erase u))
    (fun x hx => L46_bad A x hx)
  have hU : (∑ u ∈ A, p ^ (L46_sub (r := r) A (A.erase u)).card) ≤ (m:ℝ) ^ (-δ) := by
    have hcard : ∀ u ∈ A, (L46_sub (r := r) A (A.erase u)).card
        = ℓ.choose r - (ℓ - 1).choose r := by
      intro u hu
      rw [L46_card_sub _ _ (Finset.erase_subset _ _), Finset.card_erase_of_mem hu, hA]
    rw [Finset.sum_congr rfl (fun u hu => by rw [hcard u hu]), Finset.sum_const, hA,
      nsmul_eq_mul]
    have hb := L46_pow_bound hm1 hp0 hp hδ hr hrℓ 1 (by omega)
    simp only [Nat.cast_one, sub_self, zero_div, sub_zero, one_mul] at hb
    calc (ℓ:ℝ) * p ^ (ℓ.choose r - (ℓ - 1).choose r) ≤ (m:ℝ) * (m:ℝ) ^ (-(1 + δ) * 2) :=
          mul_le_mul hℓm' hb (by positivity) hmpos.le
      _ = (m:ℝ) ^ (1 + (-(1 + δ) * 2)) := by rw [Real.rpow_add hmpos, Real.rpow_one]
      _ ≤ (m:ℝ) ^ (-δ) := Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
  have hQ : (∑ Q ∈ L46_I ℓ A, p ^ (L46_sub (r := r) Q (Q ∩ A)).card)
      ≤ 2 * (Real.exp 2 * (m:ℝ) ^ (-δ)) := by
    have hterm : ∀ Q ∈ L46_I ℓ A, p ^ (L46_sub (r := r) Q (Q ∩ A)).card
        = (fun j : ℕ => p ^ (ℓ.choose r - (ℓ - j).choose r)) (Q \ A).card := by
      intro Q hQ
      rw [L46_I, Finset.mem_filter] at hQ
      rw [L46_card_sub _ _ Finset.inter_subset_left, hQ.2.1]
      have := Finset.card_sdiff_add_card_inter Q A
      show p ^ (ℓ.choose r - (Q ∩ A).card.choose r) = p ^ (ℓ.choose r - (ℓ - (Q \ A).card).choose r)
      rw [show (Q ∩ A).card = ℓ - (Q \ A).card by omega]
    have hmaps : ∀ Q ∈ L46_I ℓ A, (Q \ A).card ∈ Finset.Icc 1 ℓ := by
      intro Q hQ
      rw [L46_I, Finset.mem_filter] at hQ
      rw [Finset.mem_Icc]
      constructor
      · rw [Nat.one_le_iff_ne_zero]
        intro h0
        rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at h0
        exact hQ.2.2 (Finset.eq_of_subset_of_card_le h0 (by rw [hQ.2.1, hA]))
      · calc (Q \ A).card ≤ Q.card := Finset.card_le_card Finset.sdiff_subset
          _ = ℓ := hQ.2.1
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_fiberwise_of_maps_to hmaps]
    calc ∑ j ∈ Finset.Icc 1 ℓ, ∑ Q ∈ (L46_I ℓ A).filter (fun Q => (Q \ A).card = j),
          (fun j : ℕ => p ^ (ℓ.choose r - (ℓ - j).choose r)) (Q \ A).card
        = ∑ j ∈ Finset.Icc 1 ℓ, (((L46_I ℓ A).filter (fun Q => (Q \ A).card = j)).card : ℝ)
            * p ^ (ℓ.choose r - (ℓ - j).choose r) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_congr rfl (fun Q hQ => by rw [(Finset.mem_filter.1 hQ).2]),
            Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.Icc 1 ℓ, (Real.exp 2 * (m:ℝ) ^ (-δ)) ^ j := by
          apply Finset.sum_le_sum
          intro j hj
          rw [Finset.mem_Icc] at hj
          have hfc : (((L46_I ℓ A).filter (fun Q => (Q \ A).card = j)).card : ℝ)
              ≤ (m.choose j : ℝ) * ℓ.choose j := by
            exact_mod_cast L46_fiber_card A hA j
          calc (((L46_I ℓ A).filter (fun Q => (Q \ A).card = j)).card : ℝ)
                * p ^ (ℓ.choose r - (ℓ - j).choose r)
              ≤ (m.choose j : ℝ) * ℓ.choose j * p ^ (ℓ.choose r - (ℓ - j).choose r) :=
                mul_le_mul_of_nonneg_right hfc (by positivity)
            _ ≤ _ := L46_term hℓm' hp0 hp hδ hr hrℓ j hj.1 hj.2
      _ ≤ 2 * (Real.exp 2 * (m:ℝ) ^ (-δ)) := by
          have hlt : Real.exp 2 * (m:ℝ) ^ (-δ) < 1 := by linarith
          have hIcc : Finset.Icc 1 ℓ = Finset.Ico 1 (ℓ + 1) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
          rw [hIcc]
          calc _ ≤ (Real.exp 2 * (m:ℝ) ^ (-δ)) ^ 1 / (1 - Real.exp 2 * (m:ℝ) ^ (-δ)) :=
                geom_sum_Ico_le_of_lt_one hq0 hlt
            _ ≤ 2 * (Real.exp 2 * (m:ℝ) ^ (-δ)) := by
                rw [pow_one, div_le_iff₀ (by linarith)]
                nlinarith
  rw [ge_iff_le]
  nlinarith [hred, hU, hQ]

