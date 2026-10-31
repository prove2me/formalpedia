-- Prove2me | solution 1 for HubSpokePricing.Lagrangian.lemma_A_14
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T18:59:44.077995+00:00
-- url     : https://prove2.me/submissions/ae99220b-d43e-4dc5-8526-2c5f986797b6

import Mathlib
import Definitions.Def_HubSpokePricing_Lagrangian_Prob

namespace HubSpokeA14Aux

open HubSpokePricing.Lagrangian Finset

/-- inner-pair inequality from discrete log-concavity -/
lemma lc2 (p : ℕ → ℝ) (hp : IsLogConcave p) (a : ℕ) :
    ∀ t : ℕ, p a * p (a + t + 2) ≤ p (a + 1) * p (a + t + 1) := by
  obtain ⟨hp0, -, hcon, hlc⟩ := hp
  intro t
  induction t with
  | zero =>
    have := hlc (a + 1) (by omega)
    simp only [Nat.add_sub_cancel] at this
    have e1 : a + 1 + 1 = a + 0 + 2 := by omega
    have e2 : a + 0 + 1 = a + 1 := by omega
    rw [e1] at this; rw [e2]; nlinarith
  | succ t ih =>
    have e3 : a + (t + 1) + 2 = a + t + 3 := by omega
    have e4 : a + (t + 1) + 1 = a + t + 2 := by omega
    rw [e3, e4]
    rcases (hp0 a).lt_or_eq with ha | ha
    · rcases (hp0 (a + t + 3)).lt_or_eq with hb | hb
      · have h1 : 0 < p (a + t + 1) := hcon a (a + t + 3) _ (by omega) (by omega) ha hb
        have h2 : 0 < p (a + t + 2) := hcon a (a + t + 3) _ (by omega) (by omega) ha hb
        have hl := hlc (a + t + 2) (by omega)
        have e5 : a + t + 2 - 1 = a + t + 1 := by omega
        have e6 : a + t + 2 + 1 = a + t + 3 := by omega
        rw [e5, e6] at hl
        -- multiply ih and hl
        have hm : p a * p (a + t + 2) * (p (a + t + 1) * p (a + t + 3)) ≤
            p (a + 1) * p (a + t + 1) * p (a + t + 2) ^ 2 :=
          mul_le_mul ih hl (by positivity) (by nlinarith [hp0 (a + 1)])
        have hpos : 0 < p (a + t + 1) * p (a + t + 2) := mul_pos h1 h2
        have : (p a * p (a + t + 3)) * (p (a + t + 1) * p (a + t + 2)) ≤
            (p (a + 1) * p (a + t + 2)) * (p (a + t + 1) * p (a + t + 2)) := by
          nlinarith
        exact le_of_mul_le_mul_right this hpos
      · rw [← hb]; simp only [mul_zero]; exact mul_nonneg (hp0 _) (hp0 _)
    · rw [← ha]; simp only [zero_mul]; exact mul_nonneg (hp0 _) (hp0 _)

/-- submultiplicativity of a log-concave survival-like sequence -/
lemma submult (f : ℕ → ℝ) (h0 : ∀ k, 0 ≤ f k) (hanti : ∀ k, f (k + 1) ≤ f k) (hf0 : f 0 = 1)
    (hlc : ∀ k, f k * f (k + 2) ≤ f (k + 1) ^ 2) : ∀ j k, f (k + j) ≤ f k * f j := by
  -- ratio comparison
  have hanti' : ∀ a b, a ≤ b → f b ≤ f a := by
    intro a b hab
    induction b with
    | zero => have : a = 0 := by omega
              subst this; exact le_rfl
    | succ b ih =>
      rcases Nat.lt_or_ge a (b + 1) with h | h
      · exact (hanti b).trans (ih (by omega))
      · have : a = b + 1 := by omega
        subst this; exact le_rfl
  have Q : ∀ k j, 0 < f (j + k + 1) → f (j + k + 1) * f j ≤ f (j + k) * f (j + 1) := by
    intro k
    induction k with
    | zero => intro j _; simp only [add_zero]; nlinarith
    | succ k ih =>
      intro j hpos
      have hpos' : 0 < f (j + k + 1) := lt_of_lt_of_le hpos (by
        have := hanti (j + k + 1); simpa [Nat.add_assoc] using this)
      have hpos'' : 0 < f (j + k) := lt_of_lt_of_le hpos' (hanti _)
      have ih' := ih j hpos'
      have hl := hlc (j + k)
      have e : j + k + 2 = j + (k + 1) + 1 := by omega
      rw [e] at hl
      have e' : j + k + 1 = j + (k + 1) := by omega
      rw [e'] at ih' hl
      have hfj : 0 ≤ f j := h0 j
      have hm : f (j + (k + 1)) * f j * (f (j + k) * f (j + (k + 1) + 1)) ≤
          f (j + k) * f (j + 1) * f (j + (k + 1)) ^ 2 :=
        mul_le_mul ih' hl (by positivity) (by nlinarith [h0 (j + 1), h0 (j + k)])
      have hpos3 : 0 < f (j + k) * f (j + (k + 1)) := mul_pos hpos'' (e' ▸ hpos')
      have : (f (j + (k + 1) + 1) * f j) * (f (j + k) * f (j + (k + 1))) ≤
          (f (j + (k + 1)) * f (j + 1)) * (f (j + k) * f (j + (k + 1))) := by nlinarith
      exact le_of_mul_le_mul_right this hpos3
  intro j
  induction j with
  | zero => intro k; rw [hf0, mul_one, add_zero]
  | succ j ih =>
    intro k
    rcases (h0 (k + j + 1)).lt_or_eq with hpos | hz
    · have hq := Q k j (by rw [show j + k + 1 = k + j + 1 by omega]; exact hpos)
      have hfj : 0 < f j := lt_of_lt_of_le hpos (hanti' _ _ (by omega))
      have e : j + k = k + j := by omega
      rw [show j + k + 1 = k + (j + 1) by omega, e] at hq
      have := ih k
      have h2 : f (k + (j + 1)) * f j ≤ f k * f j * f (j + 1) :=
        hq.trans (mul_le_mul_of_nonneg_right this (h0 _))
      have : f (k + (j + 1)) * f j ≤ (f k * f (j + 1)) * f j := by linarith
      exact le_of_mul_le_mul_right this hfj
    · rw [show k + (j + 1) = k + j + 1 by omega, ← hz]
      exact mul_nonneg (h0 _) (h0 _)


/-- tail probabilities `S k = P[X ≥ k]` -/
noncomputable def S (p : ℕ → ℝ) (k : ℕ) : ℝ := ∑' j, p (j + k)

section
variable (p : ℕ → ℝ) (hp : IsLogConcave p)
include hp

lemma summ : Summable p := hp.2.1.summable

lemma S_nonneg (k : ℕ) : 0 ≤ S p k := tsum_nonneg fun j => hp.1 _

lemma S_zero : S p 0 = 1 := by
  simp only [S, add_zero]; exact hp.2.1.tsum_eq

lemma S_succ (k : ℕ) : S p k = p k + S p (k + 1) := by
  have hs : Summable (fun j => p (j + k)) := (summable_nat_add_iff k).2 (summ p hp)
  simp only [S]
  rw [hs.tsum_eq_zero_add]
  simp only [zero_add]
  congr 1
  apply tsum_congr; intro j; congr 1; omega

lemma S_tendsto : Filter.Tendsto (S p) Filter.atTop (nhds 0) :=
  tendsto_sum_nat_add p

lemma S_lc (k : ℕ) : S p k * S p (k + 2) ≤ S p (k + 1) ^ 2 := by
  have h1 := S_succ p hp k
  have h2 := S_succ p hp (k + 1)
  have key : p k * S p (k + 2) ≤ p (k + 1) * S p (k + 1) := by
    simp only [S]
    rw [← tsum_mul_left, ← tsum_mul_left]
    have hs2 : Summable (fun j => p (j + (k + 2))) := (summable_nat_add_iff _).2 (summ p hp)
    have hs1 : Summable (fun j => p (j + (k + 1))) := (summable_nat_add_iff _).2 (summ p hp)
    apply Summable.tsum_le_tsum _ (hs2.mul_left _) (hs1.mul_left _)
    intro j
    have := lc2 p hp k j
    rw [show j + (k + 2) = k + j + 2 by omega, show j + (k + 1) = k + j + 1 by omega]
    exact this
  rw [show k + 1 + 1 = k + 2 by omega] at h2
  rw [h1]
  have h3 : S p (k + 1) ^ 2 = S p (k + 1) * p (k + 1) + S p (k + 1) * S p (k + 2) := by
    rw [sq]; nth_rewrite 2 [h2]; ring
  rw [h3]
  linarith [mul_comm (p (k + 1)) (S p (k + 1))]

lemma S_anti (k : ℕ) : S p (k + 1) ≤ S p k := by
  have := S_succ p hp k; have := hp.1 k; linarith

lemma S_submult (j k : ℕ) : S p (k + j) ≤ S p k * S p j :=
  submult (S p) (S_nonneg p hp) (S_anti p hp) (S_zero p hp) (S_lc p hp) j k

/-- `A K = ∑_{k<K} S (k+1)`, `B K = ∑_{k ≤ K} k p k` -/
lemma AB (K : ℕ) : ∑ k ∈ range K, S p (k + 1) =
    ∑ k ∈ range (K + 1), (k : ℝ) * p k + K * S p (K + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun k => (k : ℝ) * p k) (K + 1),
      S_succ p hp (K + 1)]
    push_cast; ring

lemma S_le_one (k : ℕ) : S p k ≤ 1 := by
  induction k with
  | zero => rw [S_zero p hp]
  | succ k ih => exact (S_anti p hp k).trans ih

lemma A_bdd : ∃ M : ℝ, ∀ K, ∑ k ∈ range K, S p (k + 1) ≤ M := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((S_tendsto p hp).eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)))
  set K0 := max 1 N
  have hK0 : S p K0 < 1 / 2 := hN K0 (le_max_right _ _)
  refine ⟨2 * K0, fun K => ?_⟩
  have hnn : ∀ k, 0 ≤ S p (k + 1) := fun k => S_nonneg p hp _
  have hA0 : ∑ k ∈ range K0, S p (k + 1) ≤ K0 := by
    calc ∑ k ∈ range K0, S p (k + 1) ≤ ∑ k ∈ range K0, (1 : ℝ) :=
          sum_le_sum fun k _ => S_le_one p hp _
      _ = K0 := by simp
  have hsplit := sum_range_add (fun k => S p (k + 1)) K0 K
  have htail : ∑ k ∈ range K, S p (K0 + k + 1) ≤ (1 / 2) * ∑ k ∈ range K, S p (k + 1) := by
    rw [mul_sum]
    apply sum_le_sum
    intro k _
    have := S_submult p hp K0 (k + 1)
    rw [show k + 1 + K0 = K0 + k + 1 by omega] at this
    have := mul_le_mul_of_nonneg_left hK0.le (S_nonneg p hp (k + 1))
    nlinarith
  have hmono : ∑ k ∈ range K, S p (k + 1) ≤ ∑ k ∈ range (K0 + K), S p (k + 1) := by
    rw [add_comm K0 K, sum_range_add]
    have : 0 ≤ ∑ k ∈ range K0, S p (K + k + 1) := sum_nonneg fun k _ => S_nonneg p hp _
    linarith
  have : ∑ k ∈ range (K0 + K), S p (k + 1) ≤ K0 + (1 / 2) * ∑ k ∈ range (K0 + K), S p (k + 1) := by
    rw [hsplit]
    have := sum_nonneg (s := range K) fun k _ => hnn k
    nlinarith
  linarith

lemma mean_summable : Summable (fun k : ℕ => (k : ℝ) * p k) := by
  obtain ⟨M, hM⟩ := A_bdd p hp
  apply summable_of_sum_range_le (c := M)
  · intro k; exact mul_nonneg (Nat.cast_nonneg _) (hp.1 k)
  · intro n
    have h1 := AB p hp n
    have h2 : ∑ k ∈ range n, (k : ℝ) * p k ≤ ∑ k ∈ range (n + 1), (k : ℝ) * p k := by
      rw [sum_range_succ]; have := mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (hp.1 n); linarith
    have h3 : 0 ≤ (n : ℝ) * S p (n + 1) := mul_nonneg (Nat.cast_nonneg _) (S_nonneg p hp _)
    have := hM n
    linarith

lemma A_le_mean (J : ℕ) : ∑ k ∈ range J, S p (k + 1) ≤ pmfMean p := by
  have hms := mean_summable p hp
  rw [AB p hp J]
  have hsplit := hms.sum_add_tsum_nat_add (J + 1)
  rw [pmfMean, ← hsplit]
  have : (J : ℝ) * S p (J + 1) ≤ ∑' i, (((i + (J + 1) : ℕ) : ℝ) * p (i + (J + 1))) := by
    simp only [S]
    rw [← tsum_mul_left]
    apply Summable.tsum_le_tsum _ (((summable_nat_add_iff _).2 (summ p hp)).mul_left _)
      ((summable_nat_add_iff (J + 1)).2 hms)
    intro i
    apply mul_le_mul_of_nonneg_right _ (hp.1 _)
    push_cast; linarith [(Nat.cast_nonneg (α := ℝ) i)]
  linarith


noncomputable def A (K : ℕ) : ℝ := ∑ k ∈ range K, S p (k + 1)
noncomputable def G (z : ℝ) (K : ℕ) : ℝ := ∑ k ∈ range K, z ^ k * S p (k + 1)

omit hp in
lemma G_id (z : ℝ) (K : ℕ) :
    G p z K = A p K + (z - 1) * ∑ i ∈ range K, z ^ i * (A p K - A p (i + 1)) := by
  induction K with
  | zero => simp [G, A]
  | succ K ih =>
    have hA : A p (K + 1) = A p K + S p (K + 1) := by simp [A, sum_range_succ]
    have hG : G p z (K + 1) = G p z K + z ^ K * S p (K + 1) := by simp [G, sum_range_succ]
    rw [hG, ih, sum_range_succ, hA]
    have hsum : ∑ i ∈ range K, z ^ i * (A p K + S p (K + 1) - A p (i + 1)) =
        ∑ i ∈ range K, z ^ i * (A p K - A p (i + 1)) + S p (K + 1) * ∑ i ∈ range K, z ^ i := by
      rw [mul_sum, ← sum_add_distrib]
      apply sum_congr rfl; intro i _; ring
    rw [hsum]
    have hgeom := geom_sum_mul z K
    have : z ^ K * (A p K + S p (K + 1) - (A p K + S p (K + 1))) = 0 := by ring
    rw [this]
    linear_combination (-S p (K + 1)) * hgeom

lemma A_diff (i t : ℕ) : A p (i + 1 + t) - A p (i + 1) ≤ S p (i + 1) * pmfMean p := by
  have h := sum_range_add (fun k => S p (k + 1)) (i + 1) t
  simp only [A]
  rw [h, add_sub_cancel_left]
  calc ∑ j ∈ range t, S p (i + 1 + j + 1) ≤ ∑ j ∈ range t, S p (i + 1) * S p (j + 1) := by
        apply sum_le_sum; intro j _
        have := S_submult p hp (j + 1) (i + 1)
        rwa [show i + 1 + (j + 1) = i + 1 + j + 1 by omega] at this
    _ = S p (i + 1) * A p t := by rw [A, mul_sum]
    _ ≤ S p (i + 1) * pmfMean p := mul_le_mul_of_nonneg_left (A_le_mean p hp t) (S_nonneg p hp _)

lemma G_bound (z : ℝ) (hz1 : 1 ≤ z) (K : ℕ) :
    G p z K ≤ pmfMean p + (z - 1) * pmfMean p * G p z K := by
  conv_lhs => rw [G_id p z K]
  have h1 : A p K ≤ pmfMean p := A_le_mean p hp K
  have h2 : ∑ i ∈ range K, z ^ i * (A p K - A p (i + 1)) ≤
      pmfMean p * G p z K := by
    rw [G, mul_sum]
    apply sum_le_sum; intro i hi
    have hiK : i + 1 + (K - (i + 1)) = K := by have := mem_range.1 hi; omega
    have := A_diff p hp i (K - (i + 1))
    rw [hiK] at this
    have hz : 0 ≤ z ^ i := pow_nonneg (by linarith) i
    calc z ^ i * (A p K - A p (i + 1)) ≤ z ^ i * (S p (i + 1) * pmfMean p) :=
          mul_le_mul_of_nonneg_left this hz
      _ = pmfMean p * (z ^ i * S p (i + 1)) := by ring
  have hz1' : 0 ≤ z - 1 := by linarith
  have := mul_le_mul_of_nonneg_left h2 hz1'
  have e : (z - 1) * (pmfMean p * G p z K) = (z - 1) * pmfMean p * G p z K := by ring
  linarith

omit hp in
lemma E_id (z : ℝ) (K : ℕ) (hS : ∀ k, S p k = p k + S p (k + 1)) (h0 : S p 0 = 1) :
    ∑ k ∈ range (K + 1), p k * z ^ k + z ^ K * S p (K + 1) = 1 + (z - 1) * G p z K := by
  induction K with
  | zero => simp [G]; rw [← h0, hS 0]
  | succ K ih =>
    have hG : G p z (K + 1) = G p z K + z ^ K * S p (K + 1) := by simp [G, sum_range_succ]
    rw [sum_range_succ, hG]
    have := hS (K + 1)
    rw [pow_succ]
    linear_combination ih - z ^ K * z * this
end

end HubSpokeA14Aux

open HubSpokePricing.Lagrangian Finset HubSpokeA14Aux

theorem solution (p : ℕ → ℝ) (hp : IsLogConcave p) (z : ℝ) (hz1 : 1 ≤ z)
    (hz : pmfMean p * (z - 1) < 1) :
    Summable (fun k : ℕ => p k * z ^ k) ∧
      ∑' k : ℕ, p k * z ^ k ≤ 1 / (1 - pmfMean p * (z - 1)) := by
  have hpos : 0 < 1 - pmfMean p * (z - 1) := by linarith
  have hbound : ∀ K, ∑ k ∈ range (K + 1), p k * z ^ k ≤ 1 / (1 - pmfMean p * (z - 1)) := by
    intro K
    have hE := E_id p z K (S_succ p hp) (S_zero p hp)
    have hGb := G_bound p hp z hz1 K
    have hGle : G p z K * (1 - pmfMean p * (z - 1)) ≤ pmfMean p := by nlinarith
    have hzS : 0 ≤ z ^ K * S p (K + 1) :=
      mul_nonneg (pow_nonneg (by linarith) K) (S_nonneg p hp _)
    rw [le_div_iff₀ hpos]
    have hz1' : 0 ≤ z - 1 := by linarith
    have := mul_le_mul_of_nonneg_left hGle hz1'
    nlinarith
  have hnn : ∀ k, 0 ≤ p k * z ^ k := fun k => mul_nonneg (hp.1 k) (pow_nonneg (by linarith) k)
  have hb' : ∀ n, ∑ k ∈ range n, p k * z ^ k ≤ 1 / (1 - pmfMean p * (z - 1)) := by
    intro n
    refine le_trans ?_ (hbound n)
    rw [sum_range_succ]; linarith [hnn n]
  exact ⟨summable_of_sum_range_le hnn hb', Real.tsum_le_of_sum_range_le hnn hb'⟩
