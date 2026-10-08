-- Prove2me | solution 1 for MDPFinance.OptimalStopping.theorem_10_3_6
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T04:12:52.463276+00:00
-- url     : https://prove2.me/submissions/c2ac3499-1379-43a6-be3f-c0c17f4945ee

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Applications

open MeasureTheory
open MeasureTheory Set

namespace MDPFinance.OptimalStopping

noncomputable def Fv36 (α c : ℝ) : ℝ := (α * c + (max (1 - c) 0) ^ α) / (α - 1)

lemma shift36 (f : ℝ → ℝ) (B : ℝ) : ∫ z in Ioi 0, f (z + B) = ∫ t in Ioi B, f t := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  conv_rhs => rw [← integral_add_right_eq_self _ B]
  congr 1; funext x
  by_cases h : 0 < x
  · simp [indicator_apply, h, show B < x + B by linarith]
  · simp [indicator_apply, h, show ¬ B < x + B by linarith]

lemma rpowInt36 {p B : ℝ} (hp : p < -1) (hB : 0 < B) :
    ∫ t in Ioi B, t ^ p = B ^ (p + 1) / (-(p + 1)) := by
  rw [integral_Ioi_rpow_of_lt hp hB]; rw [div_neg, neg_div]

lemma key36 {α B c : ℝ} (hα : 1 < α) (hB : 0 < B) (hc : 0 ≤ c) :
    ∫ t in Ioi B, max (t - B) (t * c) * (α * B ^ α * t ^ (-(α + 1))) = B * Fv36 α c := by
  have hpow : ∀ t : ℝ, 0 < t → t * t ^ (-(α + 1)) = t ^ (-α) := by
    intro t ht
    rw [show -α = -(α + 1) + 1 by ring, Real.rpow_add ht, Real.rpow_one]; ring
  have i1 : IntegrableOn (fun t : ℝ => t ^ (-α)) (Ioi B) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hB
  have i2 : IntegrableOn (fun t : ℝ => t ^ (-(α + 1))) (Ioi B) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hB
  have hBa : B ^ α * B ^ (-α + 1) = B := by
    rw [← Real.rpow_add hB]; simp
  rcases le_or_gt 1 c with h1 | h1
  · have e : ∀ t ∈ Ioi B, max (t - B) (t * c) * (α * B ^ α * t ^ (-(α + 1)))
        = (c * α * B ^ α) * t ^ (-α) := by
      intro t ht
      have ht' : B < t := ht
      rw [max_eq_right (by nlinarith), ← hpow t (by linarith)]; ring
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
      rpowInt36 (by linarith) hB]
    have : max (1 - c) 0 = 0 := max_eq_right (by linarith)
    simp only [Fv36, this, Real.zero_rpow (by linarith : α ≠ 0)]
    have hα1 : α - 1 ≠ 0 := by linarith
    have : -(-α + 1) = α - 1 := by ring
    rw [this]
    field_simp
    linear_combination (c * α) * hBa
  · set T := B / (1 - c) with hT
    have hcp : 0 < 1 - c := by linarith
    have hTB : B ≤ T := by
      rw [hT, le_div_iff₀ hcp]; nlinarith
    have hT0 : 0 < T := by linarith
    have e : ∀ t ∈ Ioi B, max (t - B) (t * c) * (α * B ^ α * t ^ (-(α + 1)))
        = (c * α * B ^ α) * t ^ (-α) + (Ioi T).indicator
          (fun t => ((1 - c) * α * B ^ α) * t ^ (-α) - (B * α * B ^ α) * t ^ (-(α + 1))) t := by
      intro t ht
      have ht' : B < t := ht
      have htp : 0 < t := by linarith
      by_cases hTt : T < t
      · rw [indicator_of_mem (show t ∈ Ioi T from hTt)]
        have : t * c ≤ t - B := by
          have := (div_lt_iff₀ hcp).1 hTt; nlinarith
        rw [max_eq_left this, ← hpow t htp]; ring
      · rw [indicator_of_notMem (show t ∉ Ioi T from hTt)]
        have : t - B ≤ t * c := by
          have := (le_div_iff₀ hcp).1 (not_lt.1 hTt); nlinarith
        rw [max_eq_right this, ← hpow t htp]; ring
    have iT1 : IntegrableOn (fun t : ℝ => t ^ (-α)) (Ioi T) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) hT0
    have iT2 : IntegrableOn (fun t : ℝ => t ^ (-(α + 1))) (Ioi T) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) hT0
    have iind : IntegrableOn ((Ioi T).indicator
          (fun t => ((1 - c) * α * B ^ α) * t ^ (-α) - (B * α * B ^ α) * t ^ (-(α + 1))))
          (Ioi B) := by
      rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioi]
      rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ioi,
        inter_eq_left.2 (Ioi_subset_Ioi hTB)]
      exact (iT1.const_mul _).sub (iT2.const_mul _)
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_add (i1.const_mul _) iind,
      setIntegral_indicator measurableSet_Ioi,
      show Ioi B ∩ Ioi T = Ioi T from inter_eq_right.2 (Ioi_subset_Ioi hTB),
      integral_sub (iT1.const_mul _) (iT2.const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul, rpowInt36 (by linarith) hB, rpowInt36 (by linarith) hT0,
      rpowInt36 (by linarith) hT0]
    have hmax : max (1 - c) 0 = 1 - c := max_eq_left hcp.le
    simp only [Fv36, hmax]
    -- algebra
    have hTa : T ^ (-α + 1) = T * T ^ (-α) := by
      rw [Real.rpow_add hT0, Real.rpow_one]; ring
    have hTa2 : T ^ (-(α + 1) + 1) = T ^ (-α) := by ring_nf
    have hBT : B ^ α * T ^ (-α) = (1 - c) ^ α := by
      rw [Real.rpow_neg hT0.le, hT, Real.div_rpow hB.le hcp.le]
      have : 0 < B ^ α := Real.rpow_pos_of_pos hB α
      field_simp
    have hTc : (1 - c) * T = B := by rw [hT]; field_simp
    rw [hTa, hTa2]
    have e1 : -(-α + 1) = α - 1 := by ring
    have e2 : -(-(α + 1) + 1) = α := by ring
    rw [e1, e2]
    clear_value T
    have hα1 : α - 1 ≠ 0 := by linarith
    have hα0 : α ≠ 0 := by linarith
    have : c * α * B ^ α * (B ^ (-α + 1) / (α - 1)) +
      ((1 - c) * α * B ^ α * (T * T ^ (-α) / (α - 1)) - B * α * B ^ α * (T ^ (-α) / α)) =
      (c * α * (B ^ α * B ^ (-α + 1)) + α * ((1 - c) * T) * (B ^ α * T ^ (-α))) / (α - 1)
        - B * (B ^ α * T ^ (-α)) := by
      field_simp; ring
    rw [this, hBa, hBT, hTc]
    field_simp; ring

lemma step36 (M : BayesStopping) (m n : ℕ) (s c : ℝ) (hs : 0 ≤ s) (hc : 0 ≤ c)
    (hJ : ∀ z : ℝ, 0 < z → M.J m z (s + z) (n + 1) = max z ((M.b + s + z) * c)) :
    M.cfun (m + 1) s n = (M.b + s) * Fv36 ((n : ℝ) + M.a) c := by
  have hB : 0 < s + M.b := by linarith [M.b_pos]
  have hα : 1 < (n : ℝ) + M.a := by have := M.a_gt; have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  set B := s + M.b with hBdef
  set α := (n : ℝ) + M.a with hαdef
  have e : ∀ z ∈ Ioi (0:ℝ), M.J m z (s + z) (n + 1) * M.qZ s n z
      = (fun t => max (t - B) (t * c) * (α * B ^ α * t ^ (-(α + 1)))) (z + B) := by
    intro z hz
    have hz' : (0:ℝ) < z := hz
    rw [hJ z hz']
    simp only [BayesStopping.qZ]
    have h1 : z + B - B = z := by ring
    have h2 : (z + B) * c = (M.b + s + z) * c := by rw [hBdef]; ring
    have h3 : z + s + M.b = z + B := by rw [hBdef]; ring
    rw [h1, h2, h3, Real.rpow_neg (by linarith), div_eq_mul_inv]
  unfold BayesStopping.cfun
  simp only [Nat.add_sub_cancel]
  rw [setIntegral_congr_fun measurableSet_Ioi e, shift36 (fun t => max (t - B) (t * c) * (α * B ^ α * t ^ (-(α + 1)))) B,
    key36 hα hB hc, hBdef, add_comm s M.b]


lemma Fnn36 {α c : ℝ} (hα : 1 < α) (hc : 0 ≤ c) : 0 ≤ Fv36 α c := by
  unfold Fv36
  apply div_nonneg _ (by linarith)
  have := Real.rpow_nonneg (le_max_right (1 - c) 0) α
  nlinarith

lemma Fge36 {α c : ℝ} (hα : 1 < α) (hc : 0 ≤ c) : c ≤ Fv36 α c := by
  unfold Fv36
  rw [le_div_iff₀ (by linarith)]
  have := Real.rpow_nonneg (le_max_right (1 - c) 0) α
  nlinarith

lemma Fmono36 {α c c' : ℝ} (hα : 1 < α) (hc : 0 ≤ c) (hcc : c ≤ c') :
    Fv36 α c ≤ Fv36 α c' := by
  unfold Fv36
  apply div_le_div_of_nonneg_right _ (by linarith)
  set t := max (1 - c) 0 with ht
  set t' := max (1 - c') 0 with ht'
  have t'0 : 0 ≤ t' := le_max_right _ _
  have tt' : t' ≤ t := max_le_max (by linarith) le_rfl
  have t1 : t ≤ 1 := max_le (by linarith) (by norm_num)
  have hd : t - t' ≤ c' - c := by
    rw [ht, ht']
    rcases le_total c' 1 with h | h
    · rw [max_eq_left (by linarith : (0:ℝ) ≤ 1 - c'), max_eq_left (by linarith : (0:ℝ) ≤ 1 - c)]
      linarith
    · rw [max_eq_right (by linarith : 1 - c' ≤ 0)]
      rcases le_total c 1 with h2 | h2
      · rw [max_eq_left (by linarith : (0:ℝ) ≤ 1 - c)]; linarith
      · rw [max_eq_right (by linarith : 1 - c ≤ 0)]; linarith
  suffices hs : t ^ α - t' ^ α ≤ α * (t - t') by nlinarith
  rcases eq_or_lt_of_le (le_trans t'0 tt') with h0 | hpos
  · have : t' = 0 := le_antisymm (h0 ▸ tt') t'0
    rw [← h0, this]; simp
  · have hs1 : (-1:ℝ) ≤ t' / t - 1 := by
      have := div_nonneg t'0 hpos.le; linarith
    have bern := one_add_mul_self_le_rpow_one_add hs1 hα.le
    rw [show 1 + (t' / t - 1) = t' / t by ring, Real.div_rpow t'0 hpos.le] at bern
    have hu : t ^ α = t ^ (α - 1) * t := by
      rw [← Real.rpow_add_one hpos.ne']; ring_nf
    have hv1 : t ^ (α - 1) ≤ 1 := Real.rpow_le_one hpos.le t1 (by linarith)
    have hv0 : 0 ≤ t ^ (α - 1) := Real.rpow_nonneg hpos.le _
    have hua : 0 < t ^ α := Real.rpow_pos_of_pos hpos α
    rw [le_div_iff₀ hua] at bern
    have : t ^ α + α * (t' - t) * t ^ (α - 1) ≤ t' ^ α := by
      have e : (1 + α * (t' / t - 1)) * t ^ α = t ^ α + α * (t' - t) * t ^ (α - 1) := by
        rw [hu]; field_simp
      linarith
    have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ α) (by linarith : (0:ℝ) ≤ t - t'))
      (by linarith : (0:ℝ) ≤ 1 - t ^ (α - 1))
    nlinarith

lemma Fanti36 {α α' c : ℝ} (hα : 1 < α) (hαα : α ≤ α') (hc : 0 ≤ c) :
    Fv36 α' c ≤ Fv36 α c := by
  unfold Fv36
  have t0 : 0 ≤ max (1 - c) 0 := le_max_right _ _
  have t1 : max (1 - c) 0 ≤ 1 := max_le (by linarith) (by norm_num)
  have hp : max (1 - c) 0 ^ α' ≤ max (1 - c) 0 ^ α :=
    Real.rpow_le_rpow_of_exponent_ge' t0 t1 (by linarith) hαα
  have hp0 : 0 ≤ max (1 - c) 0 ^ α' := Real.rpow_nonneg t0 _
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

noncomputable def Cv36 (a : ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | n, (m + 1) => Fv36 ((n : ℝ) + a) (Cv36 a (n + 1) m)

lemma Cnn36 {a : ℝ} (ha : 1 < a) (n m : ℕ) : 0 ≤ Cv36 a n m := by
  induction m generalizing n with
  | zero => simp [Cv36]
  | succ m ih =>
    simp only [Cv36]
    exact Fnn36 (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith) (ih _)

lemma cfunC36 (M : BayesStopping) (m n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    M.cfun (m + 1) s n = (M.b + s) * Cv36 M.a n (m + 1) := by
  induction m generalizing n s with
  | zero =>
    rw [step36 M 0 n s 0 hs le_rfl (fun z hz => by simp [BayesStopping.J, le_of_lt hz])]
    simp [Cv36]
  | succ m ih =>
    rw [step36 M (m + 1) n s (Cv36 M.a (n + 1) (m + 1)) hs (Cnn36 M.a_gt _ _)]
    · rfl
    · intro z hz
      have : M.J (m + 1) z (s + z) (n + 1) = max z (M.cfun (m + 1) (s + z) (n + 1)) := rfl
      rw [this, ih (n + 1) (s + z) (by linarith), add_assoc]


lemma Cdiag36 {a : ℝ} (ha : 1 < a) (n m : ℕ) : Cv36 a (n + 1) m ≤ Cv36 a n (m + 1) := by
  simp only [Cv36]
  exact Fge36 (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith) (Cnn36 ha _ _)

lemma Cincm36 {a : ℝ} (ha : 1 < a) (m n : ℕ) : Cv36 a n m ≤ Cv36 a n (m + 1) := by
  induction m generalizing n with
  | zero => simpa [Cv36] using Cnn36 ha n 1
  | succ m ih =>
    simp only [Cv36] at *
    exact Fmono36 (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith) (Cnn36 ha _ _) (ih _)

lemma Cdecn36 {a : ℝ} (ha : 1 < a) (m n : ℕ) : Cv36 a (n + 1) m ≤ Cv36 a n m := by
  induction m generalizing n with
  | zero => simp [Cv36]
  | succ m ih =>
    simp only [Cv36]
    have h0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    calc Fv36 (((n + 1 : ℕ) : ℝ) + a) (Cv36 a (n + 1 + 1) m)
        ≤ Fv36 ((n : ℝ) + a) (Cv36 a (n + 1 + 1) m) :=
          Fanti36 (by linarith) (by push_cast; linarith) (Cnn36 ha _ _)
      _ ≤ Fv36 ((n : ℝ) + a) (Cv36 a (n + 1) m) :=
          Fmono36 (by linarith) (Cnn36 ha _ _) (ih _)

lemma chatC36 (M : BayesStopping) (N j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) :
    M.chat N j = Cv36 M.a (N - j) j := by
  induction j, hj using Nat.le_induction with
  | base =>
    simp only [BayesStopping.chat, Cv36, Fv36]
    rw [Nat.cast_sub (by omega)]
    simp
    ring
  | succ i hi ih =>
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have ih' := ih (by omega)
    simp only [BayesStopping.chat]
    rw [ih']
    rw [show N - (j + 1 + 1) = (N - (j + 2)) by omega]
    rw [show Cv36 M.a (N - (j + 2)) (j + 1 + 1) = Fv36 (((N - (j + 2) : ℕ) : ℝ) + M.a)
      (Cv36 M.a (N - (j + 2) + 1) (j + 1)) from rfl]
    rw [show N - (j + 2) + 1 = N - (j + 1) by omega, Fv36, Nat.cast_sub (by omega)]
    have e1 : (N : ℝ) - ((j : ℝ) + 1) + M.a - 1 = (N : ℝ) - ((j + 2 : ℕ) : ℝ) + M.a := by
      push_cast; ring
    have e2 : (N : ℝ) - ((j : ℝ) + 1) + M.a - 2 = (N : ℝ) - ((j + 2 : ℕ) : ℝ) + M.a - 1 := by
      push_cast; ring
    rw [e1, e2, Real.rpow_eq_pow]
    ring

theorem t36_core (M : BayesStopping) (N : ℕ) (hN : 1 ≤ N) :
    ((∀ (k : ℕ) (s : ℝ), k ≤ N - 1 → 0 ≤ s →
        M.cfun (N - k) s k = (M.b + s) * M.chat N (N - k)) ∧
      (M.chat N 1 = 1 / ((N : ℝ) + M.a - 2)) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ N - 1 →
        M.chat N (N - k + 1)
          = (1 / ((k : ℝ) + M.a - 2)) *
              (((k : ℝ) + M.a - 1) * M.chat N (N - k)
                + Real.rpow (max (1 - M.chat N (N - k)) 0) ((k : ℝ) + M.a - 1))) ∧
      (∀ j k : ℕ, 1 ≤ j → j ≤ k → k ≤ N → M.chat N j ≤ M.chat N k)) ∧
    ((∀ (k N₁ N₂ : ℕ), 1 ≤ k → k ≤ N₁ → N₁ ≤ N₂ → M.chat N₂ k ≤ M.chat N₁ k) ∧
      (∀ N₁ N₂ : ℕ, N₁ ≤ N₂ → M.nStar N₁ ≤ M.nStar N₂)) ∧
    (∀ (k : ℕ) (x s : ℝ), k + 1 ≤ M.nStar N → 0 ≤ x → x ≤ s →
      x < M.cfun (N - k) s k) ∧
    (M.J N 0 0 0 = M.b * M.chat N N) := by
  have ha := M.a_gt
  -- a1
  have a1 : ∀ (k : ℕ) (s : ℝ), k ≤ N - 1 → 0 ≤ s →
      M.cfun (N - k) s k = (M.b + s) * M.chat N (N - k) := by
    intro k s hk hs
    obtain ⟨m, hm⟩ : ∃ m, N - k = m + 1 := ⟨N - k - 1, by omega⟩
    rw [hm, cfunC36 M m k s hs, chatC36 M N (m + 1) (by omega) (by omega),
      show N - (m + 1) = k by omega]
  -- a4
  have a4 : ∀ j k : ℕ, 1 ≤ j → j ≤ k → k ≤ N → M.chat N j ≤ M.chat N k := by
    intro j k hj hjk hkN
    induction k, hjk using Nat.le_induction with
    | base => exact le_refl _
    | succ k hk ih =>
      refine le_trans (ih (by omega)) ?_
      rw [chatC36 M N k (by omega) (by omega), chatC36 M N (k + 1) (by omega) hkN,
        show N - k = (N - (k + 1)) + 1 by omega]
      exact Cdiag36 ha _ _
  -- b1
  have b1 : ∀ (k N₁ N₂ : ℕ), 1 ≤ k → k ≤ N₁ → N₁ ≤ N₂ → M.chat N₂ k ≤ M.chat N₁ k := by
    intro k N₁ N₂ hk h1 h2
    rw [chatC36 M N₂ k hk (by omega), chatC36 M N₁ k hk h1]
    exact (antitone_nat_of_succ_le (f := fun n => Cv36 M.a n k) (fun n => Cdecn36 ha k n)) (by omega)
  -- nStar set
  have nsub : ∀ N₁ N₂ : ℕ, N₁ ≤ N₂ →
      {k : ℕ | k ∈ Finset.Icc 1 N₁ ∧ 1 ≤ M.chat N₁ (N₁ - k + 1)} ⊆
      {k : ℕ | k ∈ Finset.Icc 1 N₂ ∧ 1 ≤ M.chat N₂ (N₂ - k + 1)} := by
    intro N₁ N₂ h k ⟨hk, hc⟩
    rw [Finset.mem_Icc] at hk
    refine ⟨Finset.mem_Icc.2 ⟨hk.1, by omega⟩, le_trans hc ?_⟩
    rw [chatC36 M N₁ _ (by omega) (by omega), chatC36 M N₂ _ (by omega) (by omega),
      show N₁ - (N₁ - k + 1) = k - 1 by omega, show N₂ - (N₂ - k + 1) = k - 1 by omega]
    exact (monotone_nat_of_le_succ (fun m => Cincm36 ha m (k - 1))) (by omega)
  have nbdd : ∀ N₁ : ℕ, BddAbove {k : ℕ | k ∈ Finset.Icc 1 N₁ ∧ 1 ≤ M.chat N₁ (N₁ - k + 1)} :=
    fun N₁ => ⟨N₁, fun k hk => (Finset.mem_Icc.1 hk.1).2⟩
  have b2 : ∀ N₁ N₂ : ℕ, N₁ ≤ N₂ → M.nStar N₁ ≤ M.nStar N₂ := by
    intro N₁ N₂ h
    unfold BayesStopping.nStar
    rcases Set.eq_empty_or_nonempty
      {k : ℕ | k ∈ Finset.Icc 1 N₁ ∧ 1 ≤ M.chat N₁ (N₁ - k + 1)} with he | hne
    · rw [he, csSup_empty]; exact bot_le
    · exact csSup_le_csSup (nbdd N₂) hne (nsub N₁ N₂ h)
  refine ⟨⟨a1, ?_, ?_, a4⟩, ⟨b1, b2⟩, ?_, ?_⟩
  · simp [BayesStopping.chat]
  · intro k hk1 hk2
    obtain ⟨j, hj⟩ : ∃ j, N - k = j + 1 := ⟨N - k - 1, by omega⟩
    rw [show N - k + 1 = j + 2 by omega, hj]
    have hk : (k : ℝ) = (N : ℝ) - ((j : ℝ) + 1) := by
      have : k + (j + 1) = N := by omega
      rw [← this]; push_cast; ring
    simp only [BayesStopping.chat]
    rw [hk]
  · intro k x s hk hx hxs
    have hne : {k : ℕ | k ∈ Finset.Icc 1 N ∧ 1 ≤ M.chat N (N - k + 1)}.Nonempty := by
      by_contra hcon
      rw [Set.not_nonempty_iff_eq_empty] at hcon
      unfold BayesStopping.nStar at hk
      rw [hcon, csSup_empty] at hk; simp at hk
    have hmem := Nat.sSup_mem hne (nbdd N)
    have hK : M.nStar N = sSup {k : ℕ | k ∈ Finset.Icc 1 N ∧ 1 ≤ M.chat N (N - k + 1)} := rfl
    rw [← hK] at hmem
    obtain ⟨hKI, hK1⟩ := hmem
    rw [Finset.mem_Icc] at hKI
    rw [a1 k s (by omega) (le_trans hx hxs)]
    have hc : 1 ≤ M.chat N (N - k) :=
      le_trans hK1 (a4 _ _ (by omega) (by omega) (by omega))
    have hb := M.b_pos
    nlinarith
  · obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    have h := a1 0 0 (by omega) le_rfl
    simp only [Nat.sub_zero, add_zero] at h
    have : M.J (m + 1) 0 0 0 = max 0 (M.cfun (m + 1) 0 0) := rfl
    rw [this, h, max_eq_right]
    rw [chatC36 M _ _ (by omega) le_rfl]
    exact mul_nonneg M.b_pos.le (Cnn36 ha _ _)

end MDPFinance.OptimalStopping

open MDPFinance.OptimalStopping


theorem solution (M : BayesStopping) (N : ℕ) (hN : 1 ≤ N) :
    ((∀ (k : ℕ) (s : ℝ), k ≤ N - 1 → 0 ≤ s →
        M.cfun (N - k) s k = (M.b + s) * M.chat N (N - k)) ∧
      (M.chat N 1 = 1 / ((N : ℝ) + M.a - 2)) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ N - 1 →
        M.chat N (N - k + 1)
          = (1 / ((k : ℝ) + M.a - 2)) *
              (((k : ℝ) + M.a - 1) * M.chat N (N - k)
                + Real.rpow (max (1 - M.chat N (N - k)) 0) ((k : ℝ) + M.a - 1))) ∧
      (∀ j k : ℕ, 1 ≤ j → j ≤ k → k ≤ N → M.chat N j ≤ M.chat N k)) ∧
    ((∀ (k N₁ N₂ : ℕ), 1 ≤ k → k ≤ N₁ → N₁ ≤ N₂ → M.chat N₂ k ≤ M.chat N₁ k) ∧
      (∀ N₁ N₂ : ℕ, N₁ ≤ N₂ → M.nStar N₁ ≤ M.nStar N₂)) ∧
    (∀ (k : ℕ) (x s : ℝ), k + 1 ≤ M.nStar N → 0 ≤ x → x ≤ s →
      x < M.cfun (N - k) s k) ∧
    (M.J N 0 0 0 = M.b * M.chat N N) := by
  exact t36_core M N hN
