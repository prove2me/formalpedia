-- Prove2me | solution 1 for HypRecov.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T04:07:28.045297+00:00
-- url     : https://prove2.me/submissions/7eb234c5-4b7f-4385-9841-f84f8d325cf0

import Mathlib

set_option maxHeartbeats 4000000

/-- The positive-support bound, by induction on `N`. -/
private lemma main_pos : ∀ (N : ℕ) (d : ℕ) (μ : (Fin N → Bool) → ℝ), μ ≠ 0 →
    (∀ B : Finset (Fin N), B.card ≤ d →
      ∑ x, μ x * ∏ i ∈ B, (if x i then (1 : ℝ) else 0) = 0) →
    2 ^ d ≤ (Finset.univ.filter (fun x => 0 < μ x)).card := by
  intro N
  induction N with
  | zero =>
    intro d μ hμ hmom
    exfalso
    apply hμ
    funext x
    have h0 := hmom ∅ (by simp)
    rw [Finset.sum_eq_single x] at h0
    · simpa using h0
    · intro y _ hyx
      exact absurd (Subsingleton.elim y x) hyx
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  | succ n ih =>
    intro d μ hμ hmom
    -- splitting a sum over the `(n+1)`-cube into its two `n`-half-cubes
    have hsplit : ∀ F : (Fin (n + 1) → Bool) → ℝ,
        ∑ x, F x = ∑ y : Fin n → Bool, (F (Fin.cons true y) + F (Fin.cons false y)) := by
      intro F
      rw [Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).symm
        (fun x => F x) (fun p : Bool × (Fin n → Bool) => F (Fin.cons p.1 p.2))
        (fun p => by simp [Fin.consEquiv])]
      rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · -- level 0: the mean vanishes and `μ ≠ 0`
      subst hd0
      have hsum : ∑ x, μ x = 0 := by
        have h := hmom ∅ (by simp)
        simpa using h
      have hex : ∃ x, 0 < μ x := by
        by_contra hcon
        push_neg at hcon
        have hlt : ∃ x, μ x < 0 := by
          by_contra h2
          push_neg at h2
          exact hμ (funext fun x => le_antisymm (hcon x) (h2 x))
        obtain ⟨x0, hx0⟩ := hlt
        have hneg : ∑ x, μ x < 0 := by
          simpa using Finset.sum_lt_sum (fun i _ => hcon i) ⟨x0, Finset.mem_univ _, hx0⟩
        rw [hsum] at hneg
        exact lt_irrefl _ hneg
      obtain ⟨x0, hx0⟩ := hex
      have hpos : 0 < (Finset.univ.filter (fun x : Fin (n + 1) → Bool => 0 < μ x)).card :=
        Finset.card_pos.mpr ⟨x0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx0⟩⟩
      simpa using hpos
    · -- level `d ≥ 1`
      set μ₀ : (Fin n → Bool) → ℝ := fun y => μ (Fin.cons false y) with hμ₀
      set μ₁ : (Fin n → Bool) → ℝ := fun y => μ (Fin.cons true y) with hμ₁
      -- `μ₀ + μ₁` satisfies the moment conditions at level `d`
      have hmomA : ∀ B' : Finset (Fin n), B'.card ≤ d →
          ∑ y, (μ₀ y + μ₁ y) * ∏ i ∈ B', (if y i then (1 : ℝ) else 0) = 0 := by
        intro B' hB'
        have hB : ((B'.map (Fin.succEmb n)).card) ≤ d := by
          rw [Finset.card_map]; exact hB'
        have h := hmom (B'.map (Fin.succEmb n)) hB
        rw [hsplit] at h
        have hprod : ∀ (ε : Bool) (y : Fin n → Bool),
            ∏ i ∈ B'.map (Fin.succEmb n),
                (if (Fin.cons ε y : Fin (n + 1) → Bool) i then (1 : ℝ) else 0)
              = ∏ i ∈ B', (if y i then (1 : ℝ) else 0) := by
          intro ε y
          rw [Finset.prod_map]
          refine Finset.prod_congr rfl (fun i _ => ?_)
          simp [Fin.cons_succ]
        have hterm : ∀ y : Fin n → Bool,
            μ (Fin.cons true y) * ∏ i ∈ B'.map (Fin.succEmb n),
                (if (Fin.cons true y : Fin (n + 1) → Bool) i then (1 : ℝ) else 0)
          + μ (Fin.cons false y) * ∏ i ∈ B'.map (Fin.succEmb n),
                (if (Fin.cons false y : Fin (n + 1) → Bool) i then (1 : ℝ) else 0)
          = (μ₀ y + μ₁ y) * ∏ i ∈ B', (if y i then (1 : ℝ) else 0) := by
          intro y
          rw [hprod true y, hprod false y]
          simp only [hμ₀, hμ₁]
          ring
        rw [Finset.sum_congr rfl (fun y _ => hterm y)] at h
        exact h
      -- `μ₁` satisfies the moment conditions at level `d - 1`
      have hmomB : ∀ B' : Finset (Fin n), B'.card ≤ d - 1 →
          ∑ y, μ₁ y * ∏ i ∈ B', (if y i then (1 : ℝ) else 0) = 0 := by
        intro B' hB'
        have hmem : (0 : Fin (n + 1)) ∉ B'.map (Fin.succEmb n) := by
          rw [Finset.mem_map]
          rintro ⟨a, _, ha⟩
          exact Fin.succ_ne_zero a ha
        have hcard : (insert (0 : Fin (n + 1)) (B'.map (Fin.succEmb n))).card ≤ d := by
          rw [Finset.card_insert_of_notMem hmem, Finset.card_map]
          omega
        have h := hmom (insert (0 : Fin (n + 1)) (B'.map (Fin.succEmb n))) hcard
        rw [hsplit] at h
        have hprodT : ∀ y : Fin n → Bool,
            ∏ i ∈ insert (0 : Fin (n + 1)) (B'.map (Fin.succEmb n)),
                (if (Fin.cons true y : Fin (n + 1) → Bool) i then (1 : ℝ) else 0)
              = ∏ i ∈ B', (if y i then (1 : ℝ) else 0) := by
          intro y
          rw [Finset.prod_insert hmem]
          have h0 : (if (Fin.cons true y : Fin (n + 1) → Bool) 0 then (1 : ℝ) else 0) = 1 := by
            simp [Fin.cons_zero]
          rw [h0, one_mul, Finset.prod_map]
          refine Finset.prod_congr rfl (fun i _ => ?_)
          simp [Fin.cons_succ]
        have hprodF : ∀ y : Fin n → Bool,
            ∏ i ∈ insert (0 : Fin (n + 1)) (B'.map (Fin.succEmb n)),
                (if (Fin.cons false y : Fin (n + 1) → Bool) i then (1 : ℝ) else 0) = 0 := by
          intro y
          rw [Finset.prod_insert hmem]
          have h0 : (if (Fin.cons false y : Fin (n + 1) → Bool) 0 then (1 : ℝ) else 0) = 0 := by
            simp [Fin.cons_zero]
          rw [h0, zero_mul]
        have hterm : ∀ y : Fin n → Bool,
            μ (Fin.cons true y) * ∏ i ∈ insert (0 : Fin (n + 1)) (B'.map (Fin.succEmb n)),
                (if (Fin.cons true y : Fin (n + 1) → Bool) i then (1 : ℝ) else 0)
          + μ (Fin.cons false y) * ∏ i ∈ insert (0 : Fin (n + 1)) (B'.map (Fin.succEmb n)),
                (if (Fin.cons false y : Fin (n + 1) → Bool) i then (1 : ℝ) else 0)
          = μ₁ y * ∏ i ∈ B', (if y i then (1 : ℝ) else 0) := by
          intro y
          rw [hprodT y, hprodF y, mul_zero, add_zero, hμ₁]
        rw [Finset.sum_congr rfl (fun y _ => hterm y)] at h
        exact h
      -- cardinality of the positive set, split over the two halves
      have hcard : (Finset.univ.filter (fun x : Fin (n + 1) → Bool => 0 < μ x)).card
          = (Finset.univ.filter (fun y : Fin n → Bool => 0 < μ₀ y)).card
            + (Finset.univ.filter (fun y : Fin n → Bool => 0 < μ₁ y)).card := by
        rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
        rw [Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).symm
          (fun x : Fin (n + 1) → Bool => if 0 < μ x then (1 : ℕ) else 0)
          (fun p : Bool × (Fin n → Bool) => if 0 < μ (Fin.cons p.1 p.2) then (1 : ℕ) else 0)
          (fun p => by simp [Fin.consEquiv])]
        rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        simp only [hμ₀, hμ₁]
        ring
      by_cases hdeg : μ₀ + μ₁ = 0
      · -- degenerate case: `μ₁ = -μ₀`
        have hμ₁ne : μ₁ ≠ 0 := by
          intro h
          apply hμ
          funext x
          have hμ₀zero : μ₀ = 0 := by
            funext y
            have hh := congrFun hdeg y
            simp only [Pi.add_apply, Pi.zero_apply] at hh
            rw [h] at hh
            simp only [Pi.zero_apply, add_zero] at hh
            exact hh
          have hxeq : Fin.cons (x 0) (fun i => x i.succ) = x := Fin.cons_self_tail x
          rw [← hxeq]
          rcases hx0 : x 0 with _ | _
          · exact (congrFun hμ₀ _).symm.trans (by simp [hμ₀zero])
          · exact (congrFun hμ₁ _).symm.trans (by simp [h])
        have hcard' : (Finset.univ.filter (fun x : Fin (n + 1) → Bool => 0 < μ x)).card
            = (Finset.univ.filter (fun y : Fin n → Bool => μ₁ y < 0)).card
              + (Finset.univ.filter (fun y : Fin n → Bool => 0 < μ₁ y)).card := by
          have hfeq : (Finset.univ.filter (fun y : Fin n → Bool => 0 < μ₀ y))
              = (Finset.univ.filter (fun y : Fin n → Bool => μ₁ y < 0)) := by
            apply Finset.filter_congr
            intro y _
            have hy0 : μ₀ y = -μ₁ y := by
              have h := congrFun hdeg y
              simp only [Pi.add_apply, Pi.zero_apply] at h
              linarith
            rw [hy0]
            constructor <;> intro h <;> linarith
          rw [hcard, hfeq]
        have ih1 := ih (d - 1) μ₁ hμ₁ne hmomB
        have hmomNeg : ∀ B : Finset (Fin n), B.card ≤ d - 1 →
            ∑ y, (-μ₁ y) * ∏ i ∈ B, (if y i then (1 : ℝ) else 0) = 0 := by
          intro B hB
          have h := hmomB B hB
          have hneg : ∑ y, (-μ₁ y) * ∏ i ∈ B, (if y i then (1 : ℝ) else 0)
              = -∑ y, μ₁ y * ∏ i ∈ B, (if y i then (1 : ℝ) else 0) := by
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl (fun y _ => ?_)
            ring
          rw [hneg, h, neg_zero]
        have hne' : (fun y : Fin n → Bool => -μ₁ y) ≠ 0 := by
          intro h
          apply hμ₁ne
          funext y
          have := congrFun h y
          simp only [Pi.neg_apply, Pi.zero_apply, neg_eq_zero] at this
          exact this
        have ih2 := ih (d - 1) (fun y => -μ₁ y) hne' hmomNeg
        have ih2' : 2 ^ (d - 1) ≤ (Finset.univ.filter (fun y : Fin n → Bool => μ₁ y < 0)).card := by
          convert ih2 using 2
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.neg_apply]
          constructor <;> intro h <;> linarith
        have hpow : 2 ^ d = 2 ^ (d - 1) + 2 ^ (d - 1) := by
          rcases Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0) with ⟨e, rfl⟩
          rw [Nat.succ_sub_one, pow_succ]
          ring
        rw [hcard', hpow]
        linarith
      · -- non-degenerate case
        have ihA := ih d (μ₀ + μ₁) hdeg hmomA
        have hsubset : Finset.univ.filter (fun y : Fin n → Bool => 0 < (μ₀ + μ₁) y)
            ⊆ (Finset.univ.filter (fun y : Fin n → Bool => 0 < μ₀ y))
              ∪ (Finset.univ.filter (fun y : Fin n → Bool => 0 < μ₁ y)) := by
          intro y hy
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hy ⊢
          simp only [Pi.add_apply] at hy
          by_contra hcon
          push_neg at hcon
          linarith [hcon.1, hcon.2]
        have hle : (Finset.univ.filter (fun y : Fin n → Bool => 0 < (μ₀ + μ₁) y)).card
            ≤ (Finset.univ.filter (fun y : Fin n → Bool => 0 < μ₀ y)).card
              + (Finset.univ.filter (fun y : Fin n → Bool => 0 < μ₁ y)).card :=
          le_trans (Finset.card_le_card hsubset) (Finset.card_union_le _ _)
        rw [hcard]
        linarith

theorem solution (N d : ℕ) (μ : (Fin N → Bool) → ℝ) (hμ : μ ≠ 0)
    (hmom : ∀ B : Finset (Fin N), B.card ≤ d →
      ∑ x, μ x * ∏ i ∈ B, (if x i then (1 : ℝ) else 0) = 0) :
    2 ^ d ≤ (Finset.univ.filter (fun x => 0 < μ x)).card ∧
      2 ^ d ≤ (Finset.univ.filter (fun x => μ x < 0)).card := by
  constructor
  · exact main_pos N d μ hμ hmom
  · have hne' : (fun x : Fin N → Bool => -μ x) ≠ 0 := by
      intro h
      apply hμ
      funext x
      have := congrFun h x
      simp only [Pi.neg_apply, Pi.zero_apply, neg_eq_zero] at this
      exact this
    have hneg : 2 ^ d ≤ (Finset.univ.filter (fun x => 0 < -μ x)).card := by
      refine main_pos N d (fun x => -μ x) hne' ?_
      intro B hB
      have h := hmom B hB
      have hneg' : ∑ x, (-μ x) * ∏ i ∈ B, (if x i then (1 : ℝ) else 0)
          = -∑ x, μ x * ∏ i ∈ B, (if x i then (1 : ℝ) else 0) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        ring
      rw [hneg', h, neg_zero]
    convert hneg using 2
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.neg_apply]
    constructor <;> intro h <;> linarith
