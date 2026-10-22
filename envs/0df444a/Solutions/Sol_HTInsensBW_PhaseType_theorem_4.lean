-- Prove2me | solution 1 for HTInsensBW.PhaseType.theorem_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T21:36:45.994918+00:00
-- url     : https://prove2.me/submissions/4dced500-0d2d-4e06-bf19-06244a63d028
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HTInsensBW_PhaseType_InnerProduct
import Theorems.Thm_HTInsensBW_PhaseType_eq_5
import Theorems.Thm_HTInsensBW_PhaseType_prop_P1
import Theorems.Thm_HTInsensBW_PhaseType_lemma_7
import Theorems.Thm_HTInsensBW_PhaseType_lemma_9
import Theorems.Thm_HTInsensBW_PhaseType_theorem_3
import Theorems.Thm_HTInsensBW_PhaseType_eq_80
import Theorems.Thm_HTInsensBW_PhaseType_eq_86
import Theorems.Thm_HTInsensBW_PhaseType_expected_unused_bandwidth

namespace HTInsensBWSol

open Finset Matrix HTInsensBW.PhaseType

lemma pow_le_sum_choose (y : ℝ) (hy : 0 ≤ y) (k : ℕ) :
    y ^ (k+1) ≤ ((k+1).factorial : ℝ) * ∑ j ∈ range ⌈y⌉₊, ((j + k).choose k : ℝ) := by
  have h1 : y ^ (k+1) ≤ (⌈y⌉₊ : ℝ) ^ (k+1) := pow_le_pow_left₀ hy (Nat.le_ceil y) _
  rcases Nat.eq_zero_or_eq_succ_pred ⌈y⌉₊ with h0 | hK
  · rw [h0] at h1 ⊢
    simp only [Nat.cast_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      not_false_eq_true, zero_pow] at h1
    simpa using h1
  · set K' := ⌈y⌉₊.pred
    rw [hK] at h1 ⊢
    have hs : ∑ j ∈ range (K' + 1), ((j + k).choose k : ℝ) = ((K' + k + 1).choose (k+1) : ℝ) := by
      exact_mod_cast Nat.sum_range_add_choose K' k
    rw [hs]
    have h2 : ((K'+1) : ℕ) ^ (k+1) ≤ (K'+1).ascFactorial (k+1) := Nat.pow_succ_le_ascFactorial _ _
    rw [Nat.ascFactorial_eq_factorial_mul_choose] at h2
    have h3 : (((K'+1 : ℕ) : ℝ)) ^ (k+1) ≤ ((k+1).factorial : ℝ) * ((K' + (k + 1)).choose (k+1) : ℝ) := by
      exact_mod_cast h2
    have : K' + k + 1 = K' + (k+1) := by omega
    rw [this]
    exact h1.trans (by simpa using h3)

lemma moment_of_tail {S : Type*} (π : S → ℝ) (hπ0 : ∀ n, 0 ≤ π n) (hπ : HasSum π 1)
    (W : S → ℝ) (hW : ∀ n, 0 ≤ W n) (a b β : ℝ) (ha : 0 ≤ a) (hb : 0 < b)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (htail : ∀ j : ℕ, ∑' n, (if a + b * j < W n then π n else 0) ≤ β ^ (j+1)) (k : ℕ) :
    Summable (fun n => π n * W n ^ (k+1)) ∧
    ∑' n, π n * W n ^ (k+1) ≤
      2 ^ k * (a ^ (k+1) + b ^ (k+1) * (k+1).factorial / (1 - β) ^ (k+1)) := by
  set Y : S → ℝ := fun n => max 0 ((W n - a) / b) with hYdef
  have hY0 : ∀ n, 0 ≤ Y n := fun n => le_max_left _ _
  have hWY : ∀ n, W n ≤ a + b * Y n := by
    intro n
    have : (W n - a) / b ≤ Y n := le_max_right _ _
    have := (div_le_iff₀ hb).1 this
    linarith
  have hind : ∀ n (j : ℕ), j < ⌈Y n⌉₊ → a + b * j < W n := by
    intro n j hj
    have hj' : (j : ℝ) < Y n := Nat.lt_ceil.1 hj
    have hjpos : (0:ℝ) ≤ j := Nat.cast_nonneg j
    have hYeq : Y n = (W n - a) / b := by
      rcases le_total 0 ((W n - a) / b) with h | h
      · exact max_eq_right h
      · have : Y n = 0 := max_eq_left h
        linarith
    rw [hYeq, lt_div_iff₀ hb] at hj'
    linarith
  have hπs : Summable π := hπ.summable
  have hite_s : ∀ j : ℕ, Summable (fun n => if a + b * j < W n then π n else 0) := by
    intro j
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hπs
    · split_ifs <;> simp [hπ0 n]
    · split_ifs <;> simp [hπ0 n]
  have hgeo : Summable (fun j : ℕ => ((j + k).choose k : ℝ) * β ^ j) :=
    summable_choose_mul_geometric_of_norm_lt_one k (by rw [Real.norm_eq_abs, abs_of_nonneg hβ0]; exact hβ1)
  have hgeo_t : ∑' j : ℕ, ((j + k).choose k : ℝ) * β ^ j = 1 / (1 - β) ^ (k+1) :=
    tsum_choose_mul_geometric_of_norm_lt_one k (by rw [Real.norm_eq_abs, abs_of_nonneg hβ0]; exact hβ1)
  set c : ℝ := 2 ^ k * (a ^ (k+1) + b ^ (k+1) * (k+1).factorial / (1 - β) ^ (k+1)) with hc
  have hbound : ∀ s : Finset S, ∑ n ∈ s, π n * W n ^ (k+1) ≤ c := by
    intro s
    set M := s.sup (fun n => ⌈Y n⌉₊)
    have hpt : ∀ n ∈ s, π n * W n ^ (k+1) ≤
        2 ^ k * (a ^ (k+1) * π n + b ^ (k+1) * (k+1).factorial *
          ∑ j ∈ range M, ((j + k).choose k : ℝ) * (if a + b * j < W n then π n else 0)) := by
      intro n hn
      have e1 : W n ^ (k+1) ≤ (a + b * Y n) ^ (k+1) := pow_le_pow_left₀ (hW n) (hWY n) _
      have e2 : (a + b * Y n) ^ (k+1) ≤ 2 ^ k * (a ^ (k+1) + (b * Y n) ^ (k+1)) := by
        simpa using add_pow_le ha (mul_nonneg hb.le (hY0 n)) (k+1)
      have e3 : Y n ^ (k+1) ≤ ((k+1).factorial : ℝ) * ∑ j ∈ range ⌈Y n⌉₊, ((j + k).choose k : ℝ) :=
        pow_le_sum_choose _ (hY0 n) k
      have e4 : (∑ j ∈ range ⌈Y n⌉₊, ((j + k).choose k : ℝ)) * π n ≤
          ∑ j ∈ range M, ((j + k).choose k : ℝ) * (if a + b * j < W n then π n else 0) := by
        rw [Finset.sum_mul]
        have hsub : range ⌈Y n⌉₊ ⊆ range M := by
          apply Finset.range_subset_range.2
          exact Finset.le_sup (f := fun n => ⌈Y n⌉₊) hn
        calc ∑ j ∈ range ⌈Y n⌉₊, ((j + k).choose k : ℝ) * π n
            = ∑ j ∈ range ⌈Y n⌉₊, ((j + k).choose k : ℝ) * (if a + b * j < W n then π n else 0) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [if_pos (hind n j (Finset.mem_range.1 hj))]
          _ ≤ _ := by
              apply Finset.sum_le_sum_of_subset_of_nonneg hsub
              intro j _ _
              apply mul_nonneg (Nat.cast_nonneg _)
              split_ifs <;> simp [hπ0 n]
      have hp := hπ0 n
      calc π n * W n ^ (k+1) ≤ π n * (2 ^ k * (a ^ (k+1) + (b * Y n) ^ (k+1))) :=
            mul_le_mul_of_nonneg_left (e1.trans e2) hp
        _ = 2 ^ k * (a ^ (k+1) * π n + b ^ (k+1) * (Y n ^ (k+1) * π n)) := by ring
        _ ≤ 2 ^ k * (a ^ (k+1) * π n + b ^ (k+1) * (((k+1).factorial : ℝ) *
              ∑ j ∈ range M, ((j + k).choose k : ℝ) * (if a + b * j < W n then π n else 0))) := by
            have e5 : Y n ^ (k+1) * π n ≤ ((k+1).factorial : ℝ) *
                ∑ j ∈ range M, ((j + k).choose k : ℝ) * (if a + b * j < W n then π n else 0) := by
              calc Y n ^ (k+1) * π n ≤ (((k+1).factorial : ℝ) * ∑ j ∈ range ⌈Y n⌉₊, ((j + k).choose k : ℝ)) * π n :=
                    mul_le_mul_of_nonneg_right e3 hp
                _ = ((k+1).factorial : ℝ) * ((∑ j ∈ range ⌈Y n⌉₊, ((j + k).choose k : ℝ)) * π n) := by ring
                _ ≤ _ := mul_le_mul_of_nonneg_left e4 (by positivity)
            have hb' : 0 ≤ b ^ (k+1) := by positivity
            have h2k : (0:ℝ) ≤ 2 ^ k := by positivity
            exact mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left e5 hb') _) h2k
        _ = _ := by ring
    have hsum1 : ∑ n ∈ s, π n ≤ 1 := sum_le_hasSum s (fun n _ => hπ0 n) hπ
    have hsum2 : ∀ j : ℕ, ∑ n ∈ s, (if a + b * j < W n then π n else 0) ≤ β ^ (j+1) := by
      intro j
      refine le_trans ?_ (htail j)
      apply Summable.sum_le_tsum s _ (hite_s j)
      intro n _
      split_ifs <;> simp [hπ0 n]
    have hsum3 : ∑ j ∈ range M, ((j + k).choose k : ℝ) * β ^ (j+1) ≤ 1 / (1 - β) ^ (k+1) := by
      calc ∑ j ∈ range M, ((j + k).choose k : ℝ) * β ^ (j+1)
          = β * ∑ j ∈ range M, ((j + k).choose k : ℝ) * β ^ j := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
        _ ≤ 1 * ∑' j : ℕ, ((j + k).choose k : ℝ) * β ^ j := by
            apply mul_le_mul hβ1.le _ (Finset.sum_nonneg (fun j _ => by positivity)) zero_le_one
            apply Summable.sum_le_tsum _ (fun j _ => by positivity) hgeo
        _ = _ := by rw [hgeo_t, one_mul]
    calc ∑ n ∈ s, π n * W n ^ (k+1)
        ≤ ∑ n ∈ s, 2 ^ k * (a ^ (k+1) * π n + b ^ (k+1) * (k+1).factorial *
          ∑ j ∈ range M, ((j + k).choose k : ℝ) * (if a + b * j < W n then π n else 0)) :=
          Finset.sum_le_sum hpt
      _ = 2 ^ k * (a ^ (k+1) * ∑ n ∈ s, π n + b ^ (k+1) * (k+1).factorial *
          ∑ j ∈ range M, ((j + k).choose k : ℝ) *
            ∑ n ∈ s, (if a + b * j < W n then π n else 0)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            Finset.sum_comm]
          congr 3
          apply Finset.sum_congr rfl; intro j _; rw [Finset.mul_sum]
      _ ≤ 2 ^ k * (a ^ (k+1) * 1 + b ^ (k+1) * (k+1).factorial *
          ∑ j ∈ range M, ((j + k).choose k : ℝ) * β ^ (j+1)) := by
          gcongr with j hj
          exact hsum2 j
      _ ≤ 2 ^ k * (a ^ (k+1) * 1 + b ^ (k+1) * (k+1).factorial * (1 / (1 - β) ^ (k+1))) := by
          gcongr
      _ = c := by rw [hc]; ring
  have hnn : 0 ≤ fun n => π n * W n ^ (k+1) := fun n => mul_nonneg (hπ0 n) (pow_nonneg (hW n) _)
  exact ⟨summable_of_sum_le hnn hbound, Real.tsum_le_of_sum_le hnn hbound⟩

variable {L R : ℕ}

lemma mInner_projS (N : BWNetwork L R) (y v : Idx N → ℝ) :
    mInner N (projS N y) v = ∑ i : critical N, alphaS N y i * mInner N (bvec N i) v := by
  unfold mInner projS
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
  simp only [dotProduct, mulVec, Bs, Matrix.of_apply]

lemma x_nonneg (N : BWNetwork L R) (m : Fin R → ℕ) (x : Fin R → ℝ)
    (hx : IsWPFAllocation N m x) (r : Fin R) : 0 ≤ x r := by
  rcases Nat.eq_zero_or_pos (m r) with h | h
  · exact (hx.1 r h).ge
  · exact (hx.2.1 r h).le

lemma unused_bounds (N : BWNetwork L R) (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1)
    (x : (Fin R → ℕ) → Fin R → ℝ) (hx : ∀ m, IsWPFAllocation N m (x m)) (n : State N)
    (ℓ : Fin L) : 0 ≤ unused N x n ℓ ∧ unused N x n ℓ ≤ N.C ℓ := by
  unfold unused
  constructor
  · have := (hx (routeCount N n)).2.2.1 ℓ
    linarith
  · have : 0 ≤ ∑ r, N.H ℓ r * (routeCount N n r : ℝ) * x (routeCount N n) r := by
      apply Finset.sum_nonneg
      intro r _
      have hH : 0 ≤ N.H ℓ r := by rcases hH01 ℓ r with h | h <;> simp [h]
      exact mul_nonneg (mul_nonneg hH (Nat.cast_nonneg _)) (x_nonneg N _ _ (hx _) r)
    linarith

lemma wsum_eq (N : BWNetwork L R) (m : Fin R → ℕ) (x : Fin R → ℝ)
    (hx : IsWPFAllocation N m x) (p : Fin L → ℝ) (hp : IsKKTMultiplier N m x p) :
    ∑ r, N.κ r * (m r : ℝ) = ∑ ℓ, p ℓ * N.C ℓ := by
  have h1 : ∀ ℓ, p ℓ * N.C ℓ = p ℓ * ∑ r, N.H ℓ r * (m r : ℝ) * x r := by
    intro ℓ
    have := hp.2.1 ℓ
    linear_combination this
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rcases Nat.eq_zero_or_pos (m r) with h | h
  · simp [h]
  · have hxr := hp.2.2 r h
    have hxpos := hx.2.1 r h
    have hden : ∑ ℓ, N.H ℓ r * p ℓ ≠ 0 := by
      intro h0
      rw [h0, div_zero] at hxr
      linarith
    have : x r * ∑ ℓ, N.H ℓ r * p ℓ = N.κ r := by
      rw [hxr]; field_simp
    calc N.κ r * (m r : ℝ) = (m r : ℝ) * (x r * ∑ ℓ, N.H ℓ r * p ℓ) := by rw [this]; ring
      _ = _ := by rw [Finset.mul_sum, Finset.mul_sum]; apply Finset.sum_congr rfl; intro ℓ _; ring

lemma sum_split (N : BWNetwork L R) (f : Fin L → ℝ) :
    ∑ ℓ, f ℓ = ∑ i : critical N, f i + ∑ ℓ ∈ univ.filter (fun ℓ => ℓ ∉ critical N), f ℓ := by
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun ℓ => ℓ ∈ critical N)]
  congr 1
  rw [Finset.sum_coe_sort]
  congr 1
  ext ℓ; simp

lemma perpNorm_nonneg (N : BWNetwork L R) (y : Idx N → ℝ) : 0 ≤ perpNorm N y := by
  unfold perpNorm
  apply Real.sInf_nonneg
  rintro _ ⟨α, _, rfl⟩
  exact Real.sqrt_nonneg _

lemma wsum_nonneg (N : BWNetwork L R) (hκ : ∀ r, 0 < N.κ r) (n : State N) : 0 ≤ wsum N n := by
  unfold wsum
  exact Finset.sum_nonneg (fun r _ => mul_nonneg (hκ r).le (Nat.cast_nonneg _))

lemma slack_crit (N : BWNetwork L R) (ℓ : Fin L) (h : ℓ ∈ critical N) : slack N ℓ = 0 := by
  unfold slack
  unfold critical at h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
  linarith

lemma nx_zero (N : BWNetwork L R) (x : (Fin R → ℕ) → Fin R → ℝ) : nx N x 0 = 0 := by
  funext i; simp [nx]

lemma unused_zero (N : BWNetwork L R) (x : (Fin R → ℕ) → Fin R → ℝ) (ℓ : Fin L) :
    unused N x 0 ℓ = N.C ℓ := by
  simp [unused, routeCount]


lemma muMax_pos (N : BWNetwork L R) (hC : ∀ ℓ, 0 < N.C ℓ) (hLs : (critical N).Nonempty) :
    0 < muMax N := by
  obtain ⟨ℓ, hℓ⟩ := hLs
  have hR : Nonempty (Fin R) := by
    by_contra h
    rw [not_nonempty_iff] at h
    unfold critical at hℓ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hℓ
    linarith [hC ℓ]
  obtain ⟨r⟩ := hR
  have hB : Nonempty (Fin (N.D r).B) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : IsEmpty (Phase (N.D r)) := ⟨fun k => h.elim k.1⟩
    have := (N.D r).init_sum
    rw [Finset.univ_eq_empty, Finset.sum_empty] at this
    exact zero_ne_one this
  obtain ⟨b⟩ := hB
  unfold muMax
  calc 0 < (N.D r).rate b := (N.D r).rate_pos b
    _ ≤ ⨆ b, (N.D r).rate b := le_ciSup (Finite.bddAbove_range _) b
    _ ≤ ⨆ r, ⨆ b, (N.D r).rate b :=
        le_ciSup (f := fun r => ⨆ b, (N.D r).rate b) (Finite.bddAbove_range _) r

lemma W_moment {L R : ℕ} (N : BWNetwork L R)
    (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1) (hrank : N.H.rank = L)
    (hroute : ∀ r, ∃ ℓ, N.H ℓ r = 1) (hC : ∀ ℓ, 0 < N.C ℓ)
    (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r)
    (hload : ∀ ℓ, ∑ r, N.H ℓ r * routeLoad0 N r ≤ N.C ℓ) (hLs : (critical N).Nonempty)
    (x : (Fin R → ℕ) → Fin R → ℝ) (hx : ∀ m, IsWPFAllocation N m (x m)) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ π : State N → ℝ,
      IsStationary (rates N x ε) π →
      Summable (fun n => π n * wsum N n ^ (k+1)) ∧
        ∑' n, π n * wsum N n ^ (k+1) ≤ M / ε ^ (k+1) := by
  obtain ⟨A1, A3, A4, ν, ζ, η, hA1, hA3, hA4, hν, hζ, hη, h7⟩ :=
    lemma_7 N hH01 hrank hroute hC hκ hlam0 hload hLs x hx
  have hμ := muMax_pos N hC hLs
  set μ := muMax N with hμdef
  set c := η * A3 / μ with hcdef
  have hc : 0 < c := by positivity
  set a0 := μ * A1 * A4 / (η * A3) with ha0
  set b := 2 * ν * A4 with hbdef
  set F : ℝ := ((k+1).factorial : ℝ) with hF
  set Q := (ζ * ν + c) / c with hQ
  refine ⟨2 ^ k * (a0 ^ (k+1) + b ^ (k+1) * F * Q ^ (k+1)), by positivity, ?_⟩
  intro ε hε hε1 π hπ
  have htail := (h7 ε hε hε1).2.2.2 π hπ
  set β := ζ * ν / (ζ * ν + ε * η * A3 / μ) with hβdef
  have hεc : ε * η * A3 / μ = ε * c := by rw [hcdef]; ring
  have hβ' : β = ζ * ν / (ζ * ν + ε * c) := by rw [hβdef, hεc]
  have hzn : 0 < ζ * ν := by positivity
  have hβ0 : 0 ≤ β := by rw [hβ']; positivity
  have hβ1 : β < 1 := by
    rw [hβ', div_lt_one (by positivity)]
    have : 0 < ε * c := by positivity
    linarith
  have h1β : 1 - β = ε * c / (ζ * ν + ε * c) := by
    rw [hβ']; field_simp; ring
  obtain ⟨hs, hbd⟩ := moment_of_tail π hπ.1 hπ.2.1 (wsum N) (wsum_nonneg N hκ)
    (μ * A1 * A4 / (η * A3 * ε)) b β (by positivity) (by positivity) hβ0 hβ1 htail k
  refine ⟨hs, hbd.trans ?_⟩
  have ha : μ * A1 * A4 / (η * A3 * ε) = a0 / ε := by
    rw [ha0]; field_simp
  have hinv : 1 / (1 - β) ≤ Q / ε := by
    rw [h1β, one_div_div, hQ, div_div, show c * ε = ε * c by ring,
      div_le_div_iff_of_pos_right (by positivity)]
    have : ε * c ≤ c := by nlinarith
    linarith
  have hinvpow : (1 / (1 - β)) ^ (k+1) ≤ (Q / ε) ^ (k+1) :=
    pow_le_pow_left₀ (by rw [h1β]; positivity) hinv _
  rw [ha]
  have e1 : b ^ (k+1) * F / (1 - β) ^ (k+1) = b ^ (k+1) * F * (1 / (1 - β)) ^ (k+1) := by
    rw [_root_.one_div_pow]; ring
  rw [e1]
  have hb0 : 0 ≤ b ^ (k+1) * F := by positivity
  calc 2 ^ k * ((a0 / ε) ^ (k+1) + b ^ (k+1) * F * (1 / (1 - β)) ^ (k+1))
      ≤ 2 ^ k * ((a0 / ε) ^ (k+1) + b ^ (k+1) * F * (Q / ε) ^ (k+1)) := by
        gcongr
    _ = 2 ^ k * (a0 ^ (k+1) + b ^ (k+1) * F * Q ^ (k+1)) / ε ^ (k+1) := by
        simp only [div_pow]; field_simp

lemma G_eq (N : BWNetwork L R) (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r)
    (x : (Fin R → ℕ) → Fin R → ℝ) (y : Idx N → ℝ) :
    mInner N (projS N y) ((-Sfull N)ᵀ *ᵥ rho0 N) = ∑ i : critical N, alphaS N y i * N.C i := by
  rw [mInner_projS]
  apply Finset.sum_congr rfl
  intro i _
  have h := prop_P1 N hκ hlam0 x 0 i
  rw [nx_zero, sub_zero, unused_zero, slack_crit N i i.2, sub_zero] at h
  rw [h]

lemma H_eq (N : BWNetwork L R) (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r)
    (x : (Fin R → ℕ) → Fin R → ℝ) (n : State N) :
    mInner N (projS N (toReal N n)) ((-Sfull N)ᵀ *ᵥ (rho0 N - nx N x n)) =
      ∑ i : critical N, alphaS N (toReal N n) i * unused N x n i := by
  rw [mInner_projS]
  apply Finset.sum_congr rfl
  intro i _
  rw [prop_P1 N hκ hlam0 x n i, slack_crit N i i.2, sub_zero]

lemma pointwise_bounds (N : BWNetwork L R)
    (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1)
    (hroute : ∀ r, ∃ ℓ, N.H ℓ r = 1) (hC : ∀ ℓ, 0 < N.C ℓ)
    (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r)
    (x : (Fin R → ℕ) → Fin R → ℝ) (hx : ∀ m, IsWPFAllocation N m (x m))
    (B2 B3 : ℝ) (hB2 : 0 < B2)
    (h9 : ∀ (n : State N) (p : Fin L → ℝ),
      IsKKTMultiplier N (routeCount N n) (x (routeCount N n)) p →
      (∀ (ℓ : Fin L) (hℓ : ℓ ∈ critical N),
        |alphaS N (toReal N n) ⟨ℓ, hℓ⟩ - p ℓ| ≤
          B2 * Real.sqrt (perpNorm N (toReal N n)) * Real.sqrt (wsum N n)) ∧
      ∑ ℓ ∈ Finset.univ.filter (fun ℓ => ℓ ∉ critical N), p ℓ ≤
        B3 * perpNorm N (toReal N n))
    (n : State N) :
    |wsum N n - mInner N (projS N (toReal N n)) ((-Sfull N)ᵀ *ᵥ rho0 N)| ≤
      (∑ ℓ, N.C ℓ) * (B2 * Real.sqrt (perpNorm N (toReal N n)) * Real.sqrt (wsum N n) +
        B3 * perpNorm N (toReal N n)) ∧
    |mInner N (projS N (toReal N n)) ((-Sfull N)ᵀ *ᵥ (rho0 N - nx N x n))| ≤
      ∑ i : critical N, B2 * Real.sqrt (perpNorm N (toReal N n)) * Real.sqrt (wsum N n) *
        unused N x n i := by
  obtain ⟨p, hp⟩ := (eq_5 N hH01 hroute hC hκ (routeCount N n)).2 (x (routeCount N n)) (hx _)
  obtain ⟨hα, hnc⟩ := h9 n p hp
  set X := B2 * Real.sqrt (perpNorm N (toReal N n)) * Real.sqrt (wsum N n) with hX
  have hX0 : 0 ≤ X := by positivity
  have hCnn : ∀ ℓ, 0 ≤ N.C ℓ := fun ℓ => (hC ℓ).le
  have hCt : ∀ ℓ, N.C ℓ ≤ ∑ ℓ, N.C ℓ := fun ℓ =>
    Finset.single_le_sum (fun ℓ _ => hCnn ℓ) (Finset.mem_univ ℓ)
  have hCs : ∑ i : critical N, N.C i ≤ ∑ ℓ, N.C ℓ := by
    rw [Finset.sum_coe_sort]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun ℓ _ _ => hCnn ℓ)
  have hW : wsum N n = ∑ ℓ, p ℓ * N.C ℓ :=
    wsum_eq N (routeCount N n) (x (routeCount N n)) (hx _) p hp
  constructor
  · rw [G_eq N hκ hlam0 x, hW, sum_split N]
    have e : ∑ i : critical N, p i * N.C i +
        ∑ ℓ ∈ univ.filter (fun ℓ => ℓ ∉ critical N), p ℓ * N.C ℓ -
        ∑ i : critical N, alphaS N (toReal N n) i * N.C i =
        ∑ i : critical N, (p i - alphaS N (toReal N n) i) * N.C i +
        ∑ ℓ ∈ univ.filter (fun ℓ => ℓ ∉ critical N), p ℓ * N.C ℓ := by
      rw [add_sub_right_comm, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl; intro i _; ring
    rw [e]
    have h1 : |∑ i : critical N, (p i - alphaS N (toReal N n) i) * N.C i| ≤
        X * ∑ ℓ, N.C ℓ := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i : critical N, |(p i - alphaS N (toReal N n) i) * N.C i|
          ≤ ∑ i : critical N, X * N.C i := by
            apply Finset.sum_le_sum
            intro i _
            rw [abs_mul, abs_of_nonneg (hCnn i), abs_sub_comm]
            exact mul_le_mul_of_nonneg_right (hα i i.2) (hCnn i)
        _ = X * ∑ i : critical N, N.C i := by rw [Finset.mul_sum]
        _ ≤ X * ∑ ℓ, N.C ℓ := mul_le_mul_of_nonneg_left hCs hX0
    have h2 : |∑ ℓ ∈ univ.filter (fun ℓ => ℓ ∉ critical N), p ℓ * N.C ℓ| ≤
        (∑ ℓ, N.C ℓ) * (B3 * perpNorm N (toReal N n)) := by
      have hnn : 0 ≤ ∑ ℓ ∈ univ.filter (fun ℓ => ℓ ∉ critical N), p ℓ * N.C ℓ :=
        Finset.sum_nonneg (fun ℓ _ => mul_nonneg (hp.1 ℓ) (hCnn ℓ))
      rw [abs_of_nonneg hnn]
      calc ∑ ℓ ∈ univ.filter (fun ℓ => ℓ ∉ critical N), p ℓ * N.C ℓ
          ≤ ∑ ℓ ∈ univ.filter (fun ℓ => ℓ ∉ critical N), p ℓ * ∑ ℓ, N.C ℓ :=
            Finset.sum_le_sum (fun ℓ _ => mul_le_mul_of_nonneg_left (hCt ℓ) (hp.1 ℓ))
        _ = (∑ ℓ, N.C ℓ) * ∑ ℓ ∈ univ.filter (fun ℓ => ℓ ∉ critical N), p ℓ := by
            rw [← Finset.sum_mul, mul_comm]
        _ ≤ _ := mul_le_mul_of_nonneg_left hnc (Finset.sum_nonneg (fun ℓ _ => hCnn ℓ))
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ X * ∑ ℓ, N.C ℓ + (∑ ℓ, N.C ℓ) * (B3 * perpNorm N (toReal N n)) := add_le_add h1 h2
      _ = _ := by ring
  · rw [H_eq N hκ hlam0 x]
    have e : ∑ i : critical N, alphaS N (toReal N n) i * unused N x n i =
        ∑ i : critical N, (alphaS N (toReal N n) i - p i) * unused N x n i := by
      apply Finset.sum_congr rfl
      intro i _
      have hcs : p i * unused N x n i = 0 := hp.2.1 i
      linear_combination hcs
    rw [e]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro i _
    have hU := unused_bounds N hH01 x hx n i
    rw [abs_mul, abs_of_nonneg hU.1]
    exact mul_le_mul_of_nonneg_right (hα i i.2) hU.1

lemma amgm1 (P W s : ℝ) (hP : 0 ≤ P) (hW : 0 ≤ W) (hs : 0 < s) :
    Real.sqrt P * Real.sqrt W ≤ (P / s ^ 2 + s ^ 2 * W) / 2 := by
  have h := sq_nonneg (Real.sqrt P / s - s * Real.sqrt W)
  have e : (Real.sqrt P / s - s * Real.sqrt W) ^ 2 =
      Real.sqrt P ^ 2 / s ^ 2 + s ^ 2 * Real.sqrt W ^ 2 - 2 * (Real.sqrt P * Real.sqrt W) := by
    field_simp; ring
  rw [e, Real.sq_sqrt hP, Real.sq_sqrt hW] at h
  linarith

lemma amgm8 (P W s : ℝ) (hs : 0 < s) :
    P ^ 4 * W ^ 4 ≤ (P ^ 8 / s ^ 16 + s ^ 16 * W ^ 8) / 2 := by
  have h := sq_nonneg (P ^ 4 / s ^ 8 - s ^ 8 * W ^ 4)
  have e : (P ^ 4 / s ^ 8 - s ^ 8 * W ^ 4) ^ 2 =
      P ^ 8 / s ^ 16 + s ^ 16 * W ^ 8 - 2 * (P ^ 4 * W ^ 4) := by
    field_simp; ring
  rw [e] at h
  linarith

lemma trunc_bound (X U C s : ℝ) (hX : 0 ≤ X) (hU : 0 ≤ U) (hUC : U ≤ C) (hs : 0 < s) :
    X * U ≤ U / s ^ 7 + C * s ^ 49 * X ^ 8 := by
  set t := X * s ^ 7 with ht
  have ht0 : 0 ≤ t := by positivity
  have key : t * U ≤ U + C * t ^ 8 := by
    have hC0 : 0 ≤ C := hU.trans hUC
    rcases le_total t 1 with h | h
    · have : t * U ≤ U := by nlinarith
      have : 0 ≤ C * t ^ 8 := by positivity
      linarith
    · have h1 : t * U ≤ t * C := mul_le_mul_of_nonneg_left hUC ht0
      have h2 : t ≤ t ^ 8 := le_self_pow₀ h (by norm_num)
      have h3 : t * C ≤ t ^ 8 * C := mul_le_mul_of_nonneg_right h2 hC0
      nlinarith
  have hs7 : 0 < s ^ 7 := by positivity
  have : X * U = t * U / s ^ 7 := by rw [ht]; field_simp
  rw [this, div_le_iff₀ hs7]
  have e : (U / s ^ 7 + C * s ^ 49 * X ^ 8) * s ^ 7 = U + C * t ^ 8 := by
    rw [ht]; field_simp
  rw [e]; exact key

end HTInsensBWSol

open HTInsensBW.PhaseType HTInsensBWSol Finset Matrix

set_option maxHeartbeats 1000000 in
theorem solution {L R : ℕ} (N : BWNetwork L R)
    (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1) (hrank : N.H.rank = L)
    (hroute : ∀ r, ∃ ℓ, N.H ℓ r = 1) (hC : ∀ ℓ, 0 < N.C ℓ)
    (hκ : ∀ r, 0 < N.κ r) (hlam0 : ∀ r, 0 < N.lam0 r)
    (hload : ∀ ℓ, ∑ r, N.H ℓ r * routeLoad0 N r ≤ N.C ℓ) (hLs : (critical N).Nonempty)
    (x : (Fin R → ℕ) → Fin R → ℝ) (hx : ∀ m, IsWPFAllocation N m (x m)) :
    ∀ δ : ℝ, 0 < δ → ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ε < ε₁ →
      ∀ π : State N → ℝ, IsStationary (rates N x ε) π →
        Summable (fun n => π n * wsum N n) ∧
        (((critical N).card : ℝ) * kappaMin N - δ) / ε ≤ ∑' n, π n * wsum N n ∧
        ∑' n, π n * wsum N n ≤ (((critical N).card : ℝ) * kappaMax N + δ) / ε := by
  intro δ hδ
  obtain ⟨B2, B3, hB2, hB3, h9⟩ := lemma_9 N hH01 hrank hroute hC hκ hlam0 hload hLs x hx
  obtain ⟨C1, hC1, ε1a, hε1a, h31⟩ := theorem_3 N hH01 hrank hroute hC hκ hlam0 hload hLs x hx 1
  obtain ⟨C8, hC8, ε1b, hε1b, h38⟩ := theorem_3 N hH01 hrank hroute hC hκ hlam0 hload hLs x hx 8
  obtain ⟨M1, hM1, hW1⟩ := W_moment N hH01 hrank hroute hC hκ hlam0 hload hLs x hx 0
  obtain ⟨M8, hM8, hW8⟩ := W_moment N hH01 hrank hroute hC hκ hlam0 hload hLs x hx 7
  have hCnn : ∀ ℓ, 0 ≤ N.C ℓ := fun ℓ => (hC ℓ).le
  set Ct := ∑ ℓ, N.C ℓ with hCtdef
  set Cs := ∑ i : critical N, N.C i with hCsdef
  set Ls := ((critical N).card : ℝ) with hLsdef
  have hCt0 : 0 ≤ Ct := Finset.sum_nonneg (fun ℓ _ => hCnn ℓ)
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg (fun ℓ _ => hCnn ℓ)
  have hLs0 : 0 ≤ Ls := Nat.cast_nonneg _
  have hkmin : 0 ≤ kappaMin N := Real.iInf_nonneg (fun r => (hκ r).le)
  have hkmax : 0 ≤ kappaMax N := Real.iSup_nonneg (fun r => (hκ r).le)
  set K1 := Ct * (B2 * (C1 + M1) / 2 + B3 * C1) with hK1
  set K2 := B2 * Cs * (1 + (C8 + M8) / 2) with hK2
  have hK10 : 0 ≤ K1 := by positivity
  have hK20 : 0 ≤ K2 := by positivity
  set K := Ls * kappaMin N + K1 + K2 + 1 with hKdef
  have hK0 : 0 < K := by positivity
  refine ⟨min (min ε1a ε1b) (min 1 ((δ / K) ^ 8)), by positivity, ?_⟩
  intro ε hε hε1 hεε1 π hπ
  have hεa : ε < ε1a := lt_of_lt_of_le hεε1 ((min_le_left _ _).trans (min_le_left _ _))
  have hεb : ε < ε1b := lt_of_lt_of_le hεε1 ((min_le_left _ _).trans (min_le_right _ _))
  have hεK : ε < (δ / K) ^ 8 := lt_of_lt_of_le hεε1 ((min_le_right _ _).trans (min_le_right _ _))
  -- the scale `s = ε^{1/8}`
  set s := ε ^ ((1 : ℝ) / 8) with hsdef
  have hs0 : 0 < s := Real.rpow_pos_of_pos hε _
  have hs8 : s ^ 8 = ε := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]; norm_num
  have hs1 : s ≤ 1 := by
    by_contra h
    push_neg at h
    have : 1 ≤ s ^ 8 := one_le_pow₀ h.le
    linarith
  have hsK : s * K < δ := by
    by_contra h
    push_neg at h
    have h' : δ / K ≤ s := by rw [div_le_iff₀ hK0]; linarith
    have : (δ / K) ^ 8 ≤ s ^ 8 := pow_le_pow_left₀ (by positivity) h' 8
    linarith
  have hsqrt : Real.sqrt ε = s ^ 4 := by
    rw [← hs8, show s ^ 8 = (s ^ 4) ^ 2 by ring]; exact Real.sqrt_sq (by positivity)
  have hεs : ε ≤ s := by
    rw [← hs8]; exact pow_le_of_le_one hs0.le hs1 (by norm_num)
  have hs2 : s ^ 2 ≤ s := pow_le_of_le_one hs0.le hs1 (by norm_num)
  have hs4 : s ^ 4 ≤ s := pow_le_of_le_one hs0.le hs1 (by norm_num)
  -- notation
  set Pf : State N → ℝ := fun n => perpNorm N (toReal N n) with hPf
  set Wf : State N → ℝ := fun n => wsum N n with hWf
  set Gf : State N → ℝ := fun n =>
    mInner N (projS N (toReal N n)) ((-Sfull N)ᵀ *ᵥ rho0 N) with hGf
  set Hf : State N → ℝ := fun n =>
    mInner N (projS N (toReal N n)) ((-Sfull N)ᵀ *ᵥ (rho0 N - nx N x n)) with hHf
  have hP0 : ∀ n, 0 ≤ Pf n := fun n => perpNorm_nonneg N _
  have hW0 : ∀ n, 0 ≤ Wf n := fun n => wsum_nonneg N hκ n
  have hπ0 : ∀ n, 0 ≤ π n := hπ.1
  -- moment data
  obtain ⟨hP1s, hP1b⟩ := h31 ε hε hε1 hεa π hπ
  obtain ⟨hP8s, hP8b⟩ := h38 ε hε hε1 hεb π hπ
  obtain ⟨hW1s, hW1b⟩ := hW1 ε hε hε1 π hπ
  obtain ⟨hW8s, hW8b⟩ := hW8 ε hε hε1 π hπ
  simp only [pow_one, zero_add] at hP1s hP1b hW1s hW1b
  obtain ⟨hGs, hHs, hBs, h80⟩ := eq_80 N hH01 hrank hroute hC hκ hlam0 hload hLs x hx ε hε hε1 π hπ
  obtain ⟨-, h86l, h86u⟩ := eq_86 N hH01 hrank hroute hC hκ hlam0 hload hLs x hx ε hε hε1 π hπ
  have hU := fun i : critical N =>
    expected_unused_bandwidth N hH01 hrank hroute hC hκ hlam0 hload hLs x hx ε hε hε1 π hπ i i.2
  set eP := ∑' n, π n * Pf n with heP
  set eW := ∑' n, π n * Wf n with heW
  set eP8 := ∑' n, π n * Pf n ^ 8 with heP8
  set eW8 := ∑' n, π n * Wf n ^ 8 with heW8
  set eG := ∑' n, π n * Gf n with heG
  set eH := ∑' n, π n * Hf n with heH
  set eB := ∑' n, π n * B1 N x ε n with heB
  have hP : HasSum (fun n => π n * Pf n) eP := hP1s.hasSum
  have hW : HasSum (fun n => π n * Wf n) eW := hW1s.hasSum
  have hP8 : HasSum (fun n => π n * Pf n ^ 8) eP8 := hP8s.hasSum
  have hW8' : HasSum (fun n => π n * Wf n ^ 8) eW8 := hW8s.hasSum
  have hG : HasSum (fun n => π n * Gf n) eG := hGs.hasSum
  have hH : HasSum (fun n => π n * Hf n) eH := hHs.hasSum
  have heP0 : 0 ≤ eP := hP.nonneg (fun n => mul_nonneg (hπ0 n) (hP0 n))
  have heW0 : 0 ≤ eW := hW.nonneg (fun n => mul_nonneg (hπ0 n) (hW0 n))
  have heP80 : 0 ≤ eP8 := hP8.nonneg (fun n => mul_nonneg (hπ0 n) (pow_nonneg (hP0 n) _))
  have heW80 : 0 ≤ eW8 := hW8'.nonneg (fun n => mul_nonneg (hπ0 n) (pow_nonneg (hW0 n) _))
  -- scaled moment bounds
  have huP : s ^ 4 * eP ≤ C1 := by
    have := hP1b; rw [hsqrt] at this
    have e : C1 * (1 / s ^ 4) = C1 / s ^ 4 := by ring
    rw [e, le_div_iff₀ (by positivity)] at this; linarith
  have huW : s ^ 8 * eW ≤ M1 := by
    have := hW1b; rw [← hs8, le_div_iff₀ (by positivity)] at this; linarith
  have huP8 : s ^ 32 * eP8 ≤ C8 := by
    have := hP8b; rw [hsqrt] at this
    have e : C8 * (1 / s ^ 4) ^ 8 = C8 / s ^ 32 := by field_simp
    rw [e, le_div_iff₀ (by positivity)] at this; linarith
  have huW8 : s ^ 64 * eW8 ≤ M8 := by
    have h' : eW8 ≤ M8 / ε ^ 8 := hW8b
    have e : ε ^ 8 = s ^ 64 := by rw [← hs8]; ring
    rw [e, le_div_iff₀ (by positivity)] at h'; linarith
  -- pointwise bounds
  have hpt := fun n => pointwise_bounds N hH01 hroute hC hκ hlam0 x hx B2 B3 hB2 h9 n
  -- (i) the error between W and G
  set errG : State N → ℝ := fun n =>
    Ct * (B2 * ((Pf n / s ^ 2 + s ^ 2 * Wf n) / 2) + B3 * Pf n) with herrG
  have hErrG : HasSum (fun n => π n * errG n)
      (Ct * (B2 * ((eP / s ^ 2 + s ^ 2 * eW) / 2) + B3 * eP)) := by
    have := ((((hP.div_const (s ^ 2)).add (hW.mul_left (s ^ 2))).div_const 2).mul_left B2).add
      (hP.mul_left B3) |>.mul_left Ct
    have key : (fun n => π n * errG n) = fun n =>
        Ct * (B2 * ((π n * Pf n / s ^ 2 + s ^ 2 * (π n * Wf n)) / 2) + B3 * (π n * Pf n)) := by
      funext n; simp only [herrG]; ring
    rw [key]; exact this
  have hGerr : ∀ n, |Wf n - Gf n| ≤ errG n := by
    intro n
    refine (hpt n).1.trans ?_
    simp only [herrG]
    have := amgm1 (Pf n) (Wf n) s (hP0 n) (hW0 n) hs0
    have h2 : B2 * Real.sqrt (Pf n) * Real.sqrt (Wf n) ≤ B2 * ((Pf n / s ^ 2 + s ^ 2 * Wf n) / 2) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left this hB2.le
    exact mul_le_mul_of_nonneg_left (by linarith) hCt0
  have hGlo : eW - Ct * (B2 * ((eP / s ^ 2 + s ^ 2 * eW) / 2) + B3 * eP) ≤ eG := by
    refine hasSum_le (fun n => ?_) (hW.sub hErrG) hG
    have := (abs_le.1 (hGerr n)).2
    have := mul_le_mul_of_nonneg_left (show Wf n - errG n ≤ Gf n by linarith) (hπ0 n)
    linarith
  have hGhi : eG ≤ eW + Ct * (B2 * ((eP / s ^ 2 + s ^ 2 * eW) / 2) + B3 * eP) := by
    refine hasSum_le (fun n => ?_) hG (hW.add hErrG)
    have := (abs_le.1 (hGerr n)).1
    have := mul_le_mul_of_nonneg_left (show Gf n ≤ Wf n + errG n by linarith) (hπ0 n)
    linarith
  have hK1b : ε * (Ct * (B2 * ((eP / s ^ 2 + s ^ 2 * eW) / 2) + B3 * eP)) ≤ K1 * s := by
    have e : ε * (Ct * (B2 * ((eP / s ^ 2 + s ^ 2 * eW) / 2) + B3 * eP)) =
        Ct * (B2 * ((s ^ 2 * (s ^ 4 * eP) + s ^ 2 * (s ^ 8 * eW)) / 2) + B3 * (s ^ 4 * (s ^ 4 * eP))) := by
      rw [← hs8]; field_simp
    rw [e, hK1]
    have a1 : s ^ 2 * (s ^ 4 * eP) ≤ s * C1 := mul_le_mul hs2 huP (by positivity) hs0.le
    have a2 : s ^ 2 * (s ^ 8 * eW) ≤ s * M1 := mul_le_mul hs2 huW (by positivity) hs0.le
    have a3 : s ^ 4 * (s ^ 4 * eP) ≤ s * C1 := mul_le_mul hs4 huP (by positivity) hs0.le
    have : B2 * ((s ^ 2 * (s ^ 4 * eP) + s ^ 2 * (s ^ 8 * eW)) / 2) + B3 * (s ^ 4 * (s ^ 4 * eP))
        ≤ B2 * ((s * C1 + s * M1) / 2) + B3 * (s * C1) := by gcongr
    calc _ ≤ Ct * (B2 * ((s * C1 + s * M1) / 2) + B3 * (s * C1)) := mul_le_mul_of_nonneg_left this hCt0
      _ = _ := by ring
  -- (ii) the term E[⟨N^s, (-Sᵀ)(ρ^(0) - N x)⟩]
  set errH : State N → ℝ := fun n =>
    B2 * ((∑ i : critical N, unused N x n i) / s ^ 7 +
      Cs * s ^ 49 * ((Pf n ^ 8 / s ^ 16 + s ^ 16 * Wf n ^ 8) / 2)) with herrH
  have hUsum : HasSum (fun n => ∑ i : critical N, π n * unused N x n i) (∑ i : critical N, ε * N.C i) :=
    hasSum_sum (fun i _ => by
      obtain ⟨h1, h2⟩ := hU i
      rw [← h2]; exact h1.hasSum)
  have hErrH : HasSum (fun n => π n * errH n)
      (B2 * ((∑ i : critical N, ε * N.C i) / s ^ 7 +
        Cs * s ^ 49 * ((eP8 / s ^ 16 + s ^ 16 * eW8) / 2))) := by
    have := ((hUsum.div_const (s ^ 7)).add
      ((((hP8.div_const (s ^ 16)).add (hW8'.mul_left (s ^ 16))).div_const 2).mul_left (Cs * s ^ 49))).mul_left B2
    have key : (fun n => π n * errH n) = fun n =>
        B2 * ((∑ i : critical N, π n * unused N x n i) / s ^ 7 +
          Cs * s ^ 49 * ((π n * Pf n ^ 8 / s ^ 16 + s ^ 16 * (π n * Wf n ^ 8)) / 2)) := by
      funext n; simp only [herrH]; rw [← Finset.mul_sum]; ring
    rw [key]; exact this
  have hHerr : ∀ n, |Hf n| ≤ errH n := by
    intro n
    refine (hpt n).2.trans ?_
    simp only [herrH]
    set X := Real.sqrt (Pf n) * Real.sqrt (Wf n) with hX
    have hX0 : 0 ≤ X := by positivity
    have hX8 : X ^ 8 = Pf n ^ 4 * Wf n ^ 4 := by
      rw [hX, mul_pow, show (8:ℕ) = 2 * 4 by rfl, pow_mul, pow_mul, Real.sq_sqrt (hP0 n),
        Real.sq_sqrt (hW0 n)]
    have hX8' : X ^ 8 ≤ (Pf n ^ 8 / s ^ 16 + s ^ 16 * Wf n ^ 8) / 2 := by
      rw [hX8]; exact amgm8 _ _ s hs0
    calc ∑ i : critical N, B2 * Real.sqrt (Pf n) * Real.sqrt (Wf n) * unused N x n i
        ≤ ∑ i : critical N, B2 * (unused N x n i / s ^ 7 + N.C i * s ^ 49 * X ^ 8) := by
          apply Finset.sum_le_sum
          intro i _
          have hUb := unused_bounds N hH01 x hx n i
          have := trunc_bound X (unused N x n i) (N.C i) s hX0 hUb.1 hUb.2 hs0
          rw [hX] at this ⊢
          calc B2 * Real.sqrt (Pf n) * Real.sqrt (Wf n) * unused N x n i
              = B2 * (Real.sqrt (Pf n) * Real.sqrt (Wf n) * unused N x n i) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left this hB2.le
      _ = B2 * ((∑ i : critical N, unused N x n i) / s ^ 7 + Cs * s ^ 49 * X ^ 8) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_div, hCsdef, Finset.sum_mul,
            Finset.sum_mul]
      _ ≤ _ := by
          gcongr
  have hHlo : -(B2 * ((∑ i : critical N, ε * N.C i) / s ^ 7 +
        Cs * s ^ 49 * ((eP8 / s ^ 16 + s ^ 16 * eW8) / 2))) ≤ eH := by
    refine hasSum_le (fun n => ?_) hErrH.neg hH
    have := (abs_le.1 (hHerr n)).1
    have := mul_le_mul_of_nonneg_left (show -errH n ≤ Hf n by linarith) (hπ0 n)
    linarith
  have hHhi : eH ≤ B2 * ((∑ i : critical N, ε * N.C i) / s ^ 7 +
        Cs * s ^ 49 * ((eP8 / s ^ 16 + s ^ 16 * eW8) / 2)) := by
    refine hasSum_le (fun n => ?_) hH hErrH
    have := (abs_le.1 (hHerr n)).2
    exact mul_le_mul_of_nonneg_left this (hπ0 n)
  have hK2b : B2 * ((∑ i : critical N, ε * N.C i) / s ^ 7 +
        Cs * s ^ 49 * ((eP8 / s ^ 16 + s ^ 16 * eW8) / 2)) ≤ K2 * s := by
    rw [← Finset.mul_sum, ← hCsdef]
    have e : B2 * (ε * Cs / s ^ 7 + Cs * s ^ 49 * ((eP8 / s ^ 16 + s ^ 16 * eW8) / 2)) =
        B2 * Cs * (s + (s * (s ^ 32 * eP8) + s * (s ^ 64 * eW8)) / 2) := by
      rw [← hs8]; field_simp
    rw [e, hK2]
    have a1 : s * (s ^ 32 * eP8) ≤ s * C8 := mul_le_mul_of_nonneg_left huP8 hs0.le
    have a2 : s * (s ^ 64 * eW8) ≤ s * M8 := mul_le_mul_of_nonneg_left huW8 hs0.le
    have : s + (s * (s ^ 32 * eP8) + s * (s ^ 64 * eW8)) / 2 ≤ s + (s * C8 + s * M8) / 2 := by
      linarith
    calc _ ≤ B2 * Cs * (s + (s * C8 + s * M8) / 2) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  -- (iii) combine with (80) and (86)
  have h80' : ε * eG = eH + 1 / 2 * eB := h80
  refine ⟨hW1s, ?_, ?_⟩
  · rw [div_le_iff₀ hε]
    have hεW : ε * eG - ε * (Ct * (B2 * ((eP / s ^ 2 + s ^ 2 * eW) / 2) + B3 * eP)) ≤ ε * eW := by
      have := mul_le_mul_of_nonneg_left hGhi hε.le
      linarith
    have hεL : ε * (Ls * kappaMin N) ≤ s * (Ls * kappaMin N) :=
      mul_le_mul_of_nonneg_right hεs (by positivity)
    have hl : (1 - ε) * Ls * kappaMin N ≤ 1 / 2 * eB := h86l
    have hsum : s * (Ls * kappaMin N) + K1 * s + K2 * s ≤ s * K := by
      rw [hKdef]; linarith
    show Ls * kappaMin N - δ ≤ eW * ε
    linarith
  · rw [le_div_iff₀ hε]
    have hεW : ε * eW ≤ ε * eG + ε * (Ct * (B2 * ((eP / s ^ 2 + s ^ 2 * eW) / 2) + B3 * eP)) := by
      have := mul_le_mul_of_nonneg_left hGlo hε.le
      linarith
    have hu : 1 / 2 * eB ≤ (1 - ε) * Ls * kappaMax N := h86u
    have hu' : (1 - ε) * Ls * kappaMax N ≤ Ls * kappaMax N := by
      have : 0 ≤ ε * Ls * kappaMax N := by positivity
      linarith
    have hsum : K1 * s + K2 * s ≤ s * K := by
      have : 0 ≤ s * (Ls * kappaMin N) := by positivity
      rw [hKdef]; linarith
    show eW * ε ≤ Ls * kappaMax N + δ
    linarith
