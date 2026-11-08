-- Prove2me | solution 1 for KhachiyanRounding.BCD.theorem2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-08T01:51:53.454318+00:00
-- url     : https://prove2.me/submissions/169dd74d-40d6-4948-a4aa-864fdf17e9b7

import Mathlib
import Definitions.Def_KhachiyanRounding_BCD_Specification

set_option maxHeartbeats 1000000


/-! C3 (Khachiyan 1996 Thm 1 iteration count) for KhachiyanRounding.BCD (671ed666). -/

set_option autoImplicit false

namespace KH671C3

open scoped Matrix
open KhachiyanRound.BCD (momentMatrix w IsRelaxedOpt epsOf IsBCDRun F)


lemma log_one_add_ge {ε : ℝ} (hε : 0 < ε) : 2 * ε / (2 + ε) ≤ Real.log (1 + ε) := by
  have h := Real.hasSum_log_one_add_inv (inv_pos.mpr hε)
  rw [inv_inv] at h
  have h0 := le_hasSum h 0 (fun k _ => by positivity)
  have e : (1:ℝ) / (2 * ε⁻¹ + 1) = ε / (2 + ε) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    field_simp
  simp only [Nat.cast_zero, mul_zero, zero_add, pow_one, div_one, mul_one, e] at h0
  calc 2 * ε / (2 + ε) = 2 * (ε / (2 + ε)) := by ring
    _ ≤ _ := h0

lemma phi_ge {ε : ℝ} (hε : 0 < ε) :
    ε ^ 2 / ((2 + ε) * (1 + ε)) ≤ Real.log (1 + ε) - ε / (1 + ε) := by
  have h := log_one_add_ge hε
  have e : 2 * ε / (2 + ε) - ε / (1 + ε) = ε ^ 2 / ((2 + ε) * (1 + ε)) := by
    rw [div_sub_div _ _ (by positivity) (by positivity)]
    congr 1
    ring
  linarith

lemma phi_small {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ε ^ 2 / 6 ≤ Real.log (1 + ε) - ε / (1 + ε) := by
  have h := phi_ge hε
  have : ε ^ 2 / 6 ≤ ε ^ 2 / ((2 + ε) * (1 + ε)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
  linarith

lemma phi_big1 {ε : ℝ} (hε : 1 ≤ ε) : 1 / 6 ≤ Real.log (1 + ε) - ε / (1 + ε) := by
  have h := phi_ge (by linarith : (0:ℝ) < ε)
  have : 1 / 6 ≤ ε ^ 2 / ((2 + ε) * (1 + ε)) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  linarith

lemma phi_big2 {ε : ℝ} (hε : 1 ≤ ε) :
    Real.log (1 + ε) / 7 ≤ Real.log (1 + ε) - ε / (1 + ε) := by
  have h1 := phi_big1 hε
  have h2 : ε / (1 + ε) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  by_cases hL : Real.log (1 + ε) ≤ 7 / 6
  · linarith
  · linarith

/-- Telescoping a monotone potential over the steps that stay above a threshold. -/
lemma tele_mono (Φ : ℝ → ℝ) (σ : ℝ) (hΦ : ∀ x y, σ ≤ x → x ≤ y → Φ x ≤ Φ y) :
    ∀ (N : ℕ) (G : ℕ → ℝ), (∀ k < N, G (k + 1) ≤ G k) →
      ∑ k ∈ Finset.range N, (if σ ≤ G (k + 1) then Φ (G k) - Φ (G (k + 1)) else 0) ≤
        (if σ ≤ G 0 then Φ (G 0) - Φ σ else 0) := by
  intro N
  induction N with
  | zero =>
    intro G _
    simp only [Finset.range_zero, Finset.sum_empty]
    split_ifs with h
    · linarith [hΦ σ (G 0) le_rfl h]
    · exact le_rfl
  | succ n ih =>
    intro G hG
    rw [Finset.sum_range_succ']
    have h1 := ih (fun k => G (k + 1)) (fun k hk => hG (k + 1) (by omega))
    simp only [zero_add] at h1 ⊢
    have hG0 : G 1 ≤ G 0 := hG 0 (by omega)
    by_cases hs : σ ≤ G 1
    · have hs' : σ ≤ G 0 := le_trans hs hG0
      rw [if_pos hs, if_pos hs']
      rw [if_pos hs] at h1
      linarith
    · rw [if_neg hs]
      rw [if_neg hs] at h1
      split_ifs with h0
      · linarith [hΦ σ (G 0) le_rfl h0]
      · linarith

/-- Steps that end below a threshold: their capped decrements sum to at most `σ + c`. -/
lemma tail_min (σ c : ℝ) (hσ : 0 ≤ σ) (hc : 0 ≤ c) :
    ∀ (N : ℕ) (G : ℕ → ℝ), (∀ k < N, G (k + 1) ≤ G k) → G N = 0 →
      ∑ k ∈ Finset.range N, (if G (k + 1) < σ then min (G k - G (k + 1)) c else 0) ≤
        (if G 0 < σ then G 0 else σ + c) := by
  intro N
  induction N with
  | zero =>
    intro G _ hN
    simp only [Finset.range_zero, Finset.sum_empty]
    split_ifs with h
    · exact le_of_eq hN.symm
    · linarith
  | succ n ih =>
    intro G hG hN
    rw [Finset.sum_range_succ']
    have h1 := ih (fun k => G (k + 1)) (fun k hk => hG (k + 1) (by omega)) hN
    simp only [zero_add] at h1 ⊢
    have hG0 : G 1 ≤ G 0 := hG 0 (by omega)
    by_cases h0 : G 0 < σ
    · have hs : G 1 < σ := lt_of_le_of_lt hG0 h0
      rw [if_pos hs, if_pos h0]
      rw [if_pos hs] at h1
      have := min_le_left (G 0 - G 1) c
      linarith
    · rw [if_neg h0]
      by_cases hs : G 1 < σ
      · rw [if_pos hs]
        rw [if_pos hs] at h1
        have := min_le_right (G 0 - G 1) c
        linarith
      · rw [if_neg hs]
        rw [if_neg hs] at h1
        linarith

lemma card_mul_le_sum (N : ℕ) (s : Finset ℕ) (hs : ∀ k ∈ s, k ∈ Finset.range N)
    (Q : ℕ → Prop) [DecidablePred Q] (f : ℕ → ℝ) (a : ℝ)
    (hPQ : ∀ k ∈ s, Q k ∧ a ≤ f k) (hf : ∀ k < N, Q k → 0 ≤ f k) :
    (s.card : ℝ) * a ≤ ∑ k ∈ Finset.range N, (if Q k then f k else 0) := by
  calc (s.card : ℝ) * a = ∑ k ∈ s, a := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ s, (if Q k then f k else 0) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [if_pos (hPQ k hk).1]
        exact (hPQ k hk).2
    _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => hs k hk)
        intro k hk _
        split_ifs with h
        · exact hf k (Finset.mem_range.1 hk) h
        · exact le_rfl

/-- The abstract count (Khachiyan Thm 1, two phases): `G k = F(p_N) - F(p_k)`. -/
theorem count_abstract {d δ B : ℝ} (hd : 1 ≤ d) (hδ : 0 < δ) (hB : 1 ≤ Real.log B)
    {N : ℕ} {G ε : ℕ → ℝ} (hG : ∀ k < N, G (k + 1) ≤ G k) (hGN : G N = 0)
    (hεδ : ∀ k < N, δ < ε k)
    (hgap : ∀ k < N, G k ≤ d * Real.log (1 + ε k))
    (hstep : ∀ k < N, Real.log (1 + ε k) - ε k / (1 + ε k) ≤ G k - G (k + 1))
    (hG0 : G 0 ≤ d * Real.log B) :
    (N : ℝ) ≤ 7 * d * (Real.log 6 + Real.log d + Real.log (Real.log B)) + 12 * d / δ + 3 := by
  have hd0 : (0:ℝ) < d := by linarith
  set s := Finset.range N with hs_def
  set sA := s.filter (fun k => 1 ≤ ε k)
  set sB := s.filter (fun k => ¬ 1 ≤ ε k)
  set sA1 := sA.filter (fun k => 1 / 6 ≤ G (k + 1))
  set sA2 := sA.filter (fun k => ¬ 1 / 6 ≤ G (k + 1))
  set sB1 := sB.filter (fun k => d * δ ≤ G (k + 1))
  set sB2 := sB.filter (fun k => ¬ d * δ ≤ G (k + 1))
  have hc1 : sA.card + sB.card = N := by
    rw [← Finset.card_range N]; exact Finset.card_filter_add_card_filter_not _
  have hc2 : sA1.card + sA2.card = sA.card := Finset.card_filter_add_card_filter_not _
  have hc3 : sB1.card + sB2.card = sB.card := Finset.card_filter_add_card_filter_not _
  have mem : ∀ (P R : ℕ → Prop) [DecidablePred P] [DecidablePred R] (k : ℕ),
      k ∈ (s.filter P).filter R → k < N ∧ P k ∧ R k := by
    intro P R _ _ k hk
    simp only [hs_def, Finset.mem_filter, Finset.mem_range] at hk
    exact ⟨hk.1.1, hk.1.2, hk.2⟩
  have hΔ0 : ∀ k < N, 0 ≤ G k - G (k + 1) := fun k hk => by linarith [hG k hk]
  have hLε : ∀ k < N, Real.log (1 + ε k) ≤ ε k := fun k hk => by
    have := Real.log_le_sub_one_of_pos (by linarith [hεδ k hk] : (0:ℝ) < 1 + ε k)
    linarith
  -- phase A1: eps >= 1 and the next potential stays >= 1/6 (multiplicative decrease)
  have hA1 : (sA1.card : ℝ) ≤ 7 * d * (Real.log 6 + Real.log d + Real.log (Real.log B)) := by
    have h := card_mul_le_sum N sA1 (fun k hk => Finset.mem_range.2 (mem _ _ k hk).1)
      (fun k => 1 / 6 ≤ G (k + 1)) (fun k => 7 * d * Real.log (G k) - 7 * d * Real.log (G (k + 1)))
      1 ?_ ?_
    · have ht := tele_mono (fun x => 7 * d * Real.log x) (1 / 6)
        (fun x y hx hxy => mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hxy)
          (by positivity)) N G hG
      rw [mul_one] at h
      refine h.trans (ht.trans ?_)
      split_ifs with h6
      · have hG0pos : 0 < G 0 := by linarith
        have hlB : 0 < Real.log B := by linarith
        have h1 : Real.log (G 0) ≤ Real.log d + Real.log (Real.log B) := by
          rw [← Real.log_mul hd0.ne' hlB.ne']
          exact Real.log_le_log hG0pos hG0
        have h2 : Real.log (1 / 6 : ℝ) = - Real.log 6 := by rw [one_div, Real.log_inv]
        rw [h2]
        nlinarith
      · have := Real.log_nonneg (show (1:ℝ) ≤ 6 by norm_num)
        have := Real.log_nonneg hd
        have := Real.log_nonneg hB
        positivity
    · intro k hk
      obtain ⟨hkN, hε1, hG6⟩ := mem _ _ k hk
      refine ⟨hG6, ?_⟩
      have hph := phi_big2 hε1
      have hgk := hgap k hkN
      have hst := hstep k hkN
      have hpos1 : 0 < G (k + 1) := by linarith
      have hpos0 : 0 < G k := by linarith [hG k hkN]
      have hle : G (k + 1) / G k ≤ 1 - 1 / (7 * d) := by
        rw [div_le_iff₀ hpos0]
        have : G k / (7 * d) ≤ Real.log (1 + ε k) / 7 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        have e : (1 - 1 / (7 * d)) * G k = G k - G k / (7 * d) := by ring
        linarith
      have hl := Real.log_le_sub_one_of_pos (div_pos hpos1 hpos0)
      rw [Real.log_div hpos1.ne' hpos0.ne'] at hl
      have h7 : 1 / (7 * d) ≤ Real.log (G k) - Real.log (G (k + 1)) := by linarith
      calc (1:ℝ) = 7 * d * (1 / (7 * d)) := (mul_one_div_cancel (by positivity)).symm
        _ ≤ 7 * d * (Real.log (G k) - Real.log (G (k + 1))) :=
            mul_le_mul_of_nonneg_left h7 (by positivity)
        _ = _ := by ring
    · intro k hk hQ
      have := hG k hk
      have : Real.log (G (k + 1)) ≤ Real.log (G k) := Real.log_le_log (by linarith) this
      nlinarith
  -- phase A2: eps >= 1 and the next potential drops below 1/6: at most two such steps
  have hA2 : (sA2.card : ℝ) * (1 / 6) ≤ 1 / 3 := by
    have h := card_mul_le_sum N sA2 (fun k hk => Finset.mem_range.2 (mem _ _ k hk).1)
      (fun k => G (k + 1) < 1 / 6) (fun k => min (G k - G (k + 1)) (1 / 6)) (1 / 6) ?_ ?_
    · have ht := tail_min (1 / 6) (1 / 6) (by norm_num) (by norm_num) N G hG hGN
      refine h.trans (ht.trans ?_)
      split_ifs with h6
      · linarith
      · norm_num
    · intro k hk
      obtain ⟨hkN, hε1, hG6⟩ := mem _ _ k hk
      exact ⟨not_le.mp hG6, le_min (by linarith [phi_big1 hε1, hstep k hkN]) le_rfl⟩
    · intro k hk _
      exact le_min (hΔ0 k hk) (by norm_num)
  -- phase B1: delta < eps < 1, next potential >= d delta (reciprocal potential)
  have hB1 : (sB1.card : ℝ) ≤ 6 * d / δ := by
    have hσ : 0 < d * δ := by positivity
    have h := card_mul_le_sum N sB1 (fun k hk => Finset.mem_range.2 (mem _ _ k hk).1)
      (fun k => d * δ ≤ G (k + 1))
      (fun k => -(6 * d ^ 2 / G k) - -(6 * d ^ 2 / G (k + 1))) 1 ?_ ?_
    · have ht := tele_mono (fun x => -(6 * d ^ 2 / x)) (d * δ)
        (fun x y hx hxy => neg_le_neg (div_le_div_of_nonneg_left (by positivity)
          (by linarith) hxy)) N G hG
      rw [mul_one] at h
      refine h.trans (ht.trans ?_)
      have e : 6 * d ^ 2 / (d * δ) = 6 * d / δ := by
        rw [div_eq_div_iff hσ.ne' hδ.ne']; ring
      split_ifs with h6
      · have : 0 < 6 * d ^ 2 / G 0 := by
          have : 0 < G 0 := by linarith
          positivity
        linarith
      · positivity
    · intro k hk
      obtain ⟨hkN, hε1, hG6⟩ := mem _ _ k hk
      refine ⟨hG6, ?_⟩
      have hεk := hεδ k hkN
      have hε0 : 0 < ε k := by linarith
      have hph := phi_small hε0 (le_of_lt (not_le.mp hε1))
      have hst := hstep k hkN
      have hgk := hgap k hkN
      have hL := hLε k hkN
      have hg1 : 0 < G (k + 1) := by linarith
      have hle := hG k hkN
      have hg0 : 0 < G k := by linarith
      have h1 : G k ≤ d * ε k := by nlinarith
      have h2 : G k ^ 2 ≤ (d * ε k) ^ 2 := pow_le_pow_left₀ hg0.le h1 2
      have h3 : ε k ^ 2 ≤ 6 * (G k - G (k + 1)) := by linarith
      have key : G (k + 1) * G k ≤ d ^ 2 * (6 * (G k - G (k + 1))) := by
        have : G (k + 1) * G k ≤ G k ^ 2 := by nlinarith
        have : d ^ 2 * ε k ^ 2 ≤ d ^ 2 * (6 * (G k - G (k + 1))) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
        nlinarith
      have e : -(6 * d ^ 2 / G k) - -(6 * d ^ 2 / G (k + 1)) =
          6 * d ^ 2 * (G k - G (k + 1)) / (G (k + 1) * G k) := by
        field_simp
        ring
      rw [e, le_div_iff₀ (by positivity)]
      nlinarith
    · intro k hk hQ
      have hle := hG k hk
      have hg1 : 0 < G (k + 1) := by linarith [mul_pos hd0 hδ]
      have : 6 * d ^ 2 / G k ≤ 6 * d ^ 2 / G (k + 1) :=
        div_le_div_of_nonneg_left (by positivity) hg1 hle
      linarith
  -- phase B2: delta < eps < 1, next potential < d delta
  have hB2 : (sB2.card : ℝ) * (δ ^ 2 / 6) ≤ d * δ + δ ^ 2 / 6 := by
    have h := card_mul_le_sum N sB2 (fun k hk => Finset.mem_range.2 (mem _ _ k hk).1)
      (fun k => G (k + 1) < d * δ) (fun k => min (G k - G (k + 1)) (δ ^ 2 / 6)) (δ ^ 2 / 6) ?_ ?_
    · have ht := tail_min (d * δ) (δ ^ 2 / 6) (by positivity) (by positivity) N G hG hGN
      refine h.trans (ht.trans ?_)
      split_ifs with h6
      · have : 0 ≤ δ ^ 2 / 6 := by positivity
        linarith
      · exact le_rfl
    · intro k hk
      obtain ⟨hkN, hε1, hG6⟩ := mem _ _ k hk
      have hεk := hεδ k hkN
      have hε0 : 0 < ε k := by linarith
      have hph := phi_small hε0 (le_of_lt (not_le.mp hε1))
      have : δ ^ 2 ≤ ε k ^ 2 := by nlinarith
      exact ⟨not_le.mp hG6, le_min (by linarith [hstep k hkN]) le_rfl⟩
    · intro k hk _
      exact le_min (hΔ0 k hk) (by positivity)
  have hB2' : (sB2.card : ℝ) ≤ 6 * d / δ + 1 := by
    have hδ2 : 0 < δ ^ 2 / 6 := by positivity
    have e : (6 * d / δ + 1) * (δ ^ 2 / 6) = d * δ + δ ^ 2 / 6 := by
      field_simp
    exact le_of_mul_le_mul_right (by rw [e]; exact hB2) hδ2
  have hN : (N : ℝ) = sA1.card + sA2.card + sB1.card + sB2.card := by
    rw [← hc1, ← hc2, ← hc3]; push_cast; ring
  rw [hN]
  have : (sA2.card : ℝ) ≤ 2 := by linarith
  have e2 : 12 * d / δ = 6 * d / δ + 6 * d / δ := by ring
  linarith


theorem quad_vmv {d : ℕ} (s x : Fin d → ℝ) :
    x ⬝ᵥ (Matrix.vecMulVec s s *ᵥ x) = (s ⬝ᵥ x) ^ 2 := by
  have h : Matrix.vecMulVec s s *ᵥ x = (s ⬝ᵥ x) • s := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h, dotProduct_smul, smul_eq_mul, dotProduct_comm]; ring


theorem moment_quad {ι : Type} [Fintype ι] {d : ℕ} (v : ι → Fin d → ℝ) (p : ι → ℝ)
    (x : Fin d → ℝ) : x ⬝ᵥ (momentMatrix v p *ᵥ x) = ∑ i, p i * (v i ⬝ᵥ x) ^ 2 := by
  simp only [momentMatrix, Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum,
    dotProduct_smul, smul_eq_mul, quad_vmv]

theorem moment_posSemidef {ι : Type} [Fintype ι] {d : ℕ} (v : ι → Fin d → ℝ) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) : (momentMatrix v p).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x => ?_⟩
  · ext i j
    simp [momentMatrix, Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
      mul_comm]
  · rw [star_trivial, moment_quad]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (sq_nonneg _)


theorem phi_nonneg {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ Real.log (1 + ε) - ε / (1 + ε) := by
  rcases hε.lt_or_eq with h | h
  · exact le_trans (by positivity) (phi_ge h)
  · rw [← h]; simp

theorem moment_add {ι : Type} [Fintype ι] {d : ℕ} (v : ι → Fin d → ℝ) (p q : ι → ℝ) :
    momentMatrix v (p + q) = momentMatrix v p + momentMatrix v q := by
  simp only [momentMatrix, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem moment_smul {ι : Type} [Fintype ι] {d : ℕ} (v : ι → Fin d → ℝ) (c : ℝ) (p : ι → ℝ) :
    momentMatrix v (c • p) = c • momentMatrix v p := by
  simp only [momentMatrix, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem moment_single {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ} (v : ι → Fin d → ℝ)
    (r : ι) : momentMatrix v (Pi.single r 1) = Matrix.vecMulVec (v r) (v r) := by
  simp [momentMatrix, Pi.single_apply, ite_smul, Finset.sum_ite_eq']

theorem trace_vecMulVec {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ) (a : Fin d → ℝ) :
    (B * Matrix.vecMulVec a a).trace = a ⬝ᵥ (B *ᵥ a) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct,
    Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => by ring))

theorem trace_mul_moment {ι : Type} [Fintype ι] {d : ℕ} (v : ι → Fin d → ℝ)
    (B : Matrix (Fin d) (Fin d) ℝ) (q : ι → ℝ) :
    (B * momentMatrix v q).trace = ∑ j, q j * (v j ⬝ᵥ (B *ᵥ v j)) := by
  simp only [momentMatrix, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul,
    smul_eq_mul, trace_vecMulVec]

theorem sum_w {ι : Type} [Fintype ι] {d : ℕ} (v : ι → Fin d → ℝ) (p : ι → ℝ)
    (hA : (momentMatrix v p).PosDef) : ∑ j, p j * w v p j = d := by
  have h := trace_mul_moment v (momentMatrix v p)⁻¹ p
  rw [Matrix.nonsing_inv_mul _ (hA.det_pos.ne').isUnit, Matrix.trace_one, Fintype.card_fin] at h
  exact h.symm

theorem c3_sup_eq {ι : Type} [Fintype ι] {d : ℕ} (v : ι → Fin d → ℝ) (p : ι → ℝ) (r : ι)
    (hr : ∀ j, w v p j ≤ w v p r) : (⨆ j, w v p j) = w v p r := by
  haveI : Nonempty ι := ⟨r⟩
  exact le_antisymm (ciSup_le hr) (le_ciSup (Set.finite_range _).bddAbove r)

theorem det_rank_one {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (c : ℝ)
    (a : Fin d → ℝ) :
    (A + c • Matrix.vecMulVec a a).det = A.det * (1 + c * (a ⬝ᵥ (A⁻¹ *ᵥ a))) := by
  have e : c • Matrix.vecMulVec a a =
      Matrix.replicateCol Unit (c • a) * Matrix.replicateRow Unit a := by
    rw [← Matrix.vecMulVec_eq Unit]
    ext i j
    simp [Matrix.vecMulVec_apply, mul_assoc]
  rw [e, Matrix.det_add_replicateCol_mul_replicateRow (hA.det_pos.ne').isUnit,
    ← Matrix.replicateRow_vecMul,
    Matrix.det_unique (1 + Matrix.replicateRow Unit (a ᵥ* A⁻¹) * Matrix.replicateCol Unit (c • a)),
    Matrix.add_apply, Matrix.one_apply_eq,
    Matrix.replicateRow_mul_replicateCol_apply, dotProduct_smul, ← Matrix.dotProduct_mulVec,
    smul_eq_mul]

theorem bcd_step {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ} (v : ι → Fin d → ℝ)
    (p : ι → ℝ) (r : ι) (hp : p ∈ stdSimplex ℝ ι) (hA : (momentMatrix v p).PosDef)
    (hd : 2 ≤ d) (hr : ∀ j, w v p j ≤ w v p r) :
    let ε := epsOf v p
    let τ := ε / (w v p r - 1)
    let p' := (1 - τ) • p + τ • Pi.single r (1:ℝ)
    p' ∈ stdSimplex ℝ ι ∧ (momentMatrix v p').PosDef ∧ 0 ≤ ε ∧ w v p r = (1 + ε) * d ∧
      Real.log (1 + ε) - ε / (1 + ε) ≤ F v p' - F v p := by
  intro ε τ p'
  have hD : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d:ℝ) ≠ 0 := by positivity
  have hsum := sum_w v p hA
  have hWd : (d:ℝ) ≤ w v p r := by
    rw [← hsum]
    calc ∑ j, p j * w v p j ≤ ∑ j, p j * w v p r :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hr j) (hp.1 j))
      _ = w v p r := by rw [← Finset.sum_mul, hp.2, one_mul]
  have hε : ε = w v p r / d - 1 := by
    show epsOf v p = _
    simp only [epsOf]
    rw [c3_sup_eq v p r hr]
  have hε0 : 0 ≤ ε := by
    rw [hε, sub_nonneg, le_div_iff₀ (by linarith)]
    linarith
  have hWε : w v p r = (1 + ε) * d := by
    have hc : w v p r / d * d = w v p r := div_mul_cancel₀ _ hd0
    rw [hε]
    linear_combination -hc
  refine ⟨?_, ?_, hε0, hWε, ?_⟩ <;> rcases hε0.lt_or_eq with hεpos | hεz
  rotate_left
  · have hτ : τ = 0 := by simp only [τ, ← hεz, zero_div]
    have hpp : p' = p := by simp only [p', hτ, sub_zero, one_smul, zero_smul, add_zero]
    rw [hpp]; exact hp
  rotate_left
  · have hτ : τ = 0 := by simp only [τ, ← hεz, zero_div]
    have hpp : p' = p := by simp only [p', hτ, sub_zero, one_smul, zero_smul, add_zero]
    rw [hpp]; exact hA
  rotate_left
  · have hτ : τ = 0 := by simp only [τ, ← hεz, zero_div]
    have hpp : p' = p := by simp only [p', hτ, sub_zero, one_smul, zero_smul, add_zero]
    rw [hpp, ← hεz]; simp
  all_goals
    have hW1 : 1 < w v p r := by linarith
    have hτW : τ * (w v p r - 1) = ε := div_mul_cancel₀ _ (by linarith)
    have hτ0 : 0 < τ := div_pos hεpos (by linarith)
    have htW : (1 - τ) * (w v p r - 1) = (1 + ε) * (d - 1) := by
      linear_combination hWε - hτW
    have htpos : 0 < 1 - τ := by
      have : 0 < (1 + ε) * ((d:ℝ) - 1) := mul_pos (by linarith) (by linarith)
      by_contra hneg
      push_neg at hneg
      nlinarith
    have hAp' : momentMatrix v p' =
        (1 - τ) • momentMatrix v p + τ • Matrix.vecMulVec (v r) (v r) := by
      simp only [p', moment_add, moment_smul, moment_single]
  · exact convex_stdSimplex ℝ ι hp (single_mem_stdSimplex ℝ r) htpos.le hτ0.le (by ring)
  · rw [hAp']
    have hpsd := moment_posSemidef v (τ • Pi.single r (1:ℝ)) (fun i => by
      rw [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg hτ0.le (by rw [Pi.single_apply]; split_ifs <;> norm_num))
    rw [moment_smul, moment_single] at hpsd
    exact (hA.smul htpos).add_posSemidef hpsd
  · have hdet : (momentMatrix v p').det =
        (1 - τ) ^ (d - 1) * (1 + ε) * (momentMatrix v p).det := by
      have hc : (1 - τ) * (τ / (1 - τ)) = τ := by field_simp
      have e1 : momentMatrix v p' = (1 - τ) • (momentMatrix v p +
          (τ / (1 - τ)) • Matrix.vecMulVec (v r) (v r)) := by
        rw [hAp', smul_add, smul_smul, hc]
      rw [e1, Matrix.det_smul, det_rank_one _ hA, Fintype.card_fin]
      have e2 : (1 - τ) * (1 + τ / (1 - τ) * w v p r) = 1 + ε := by
        rw [mul_add, mul_one, ← mul_assoc, hc]
        linear_combination hτW
      have hdpow : (1 - τ) ^ d = (1 - τ) ^ (d - 1) * (1 - τ) := by
        rw [← pow_succ]; congr 1; omega
      rw [hdpow, ← e2]
      simp only [w]
      ring
    have hFd : F v p' - F v p = ((d:ℝ) - 1) * Real.log (1 - τ) + Real.log (1 + ε) := by
      simp only [F]
      rw [hdet, Real.log_mul (mul_pos (pow_pos htpos _) (by linarith)).ne' hA.det_pos.ne',
        Real.log_mul (pow_pos htpos _).ne' (by linarith), Real.log_pow,
        Nat.cast_sub (by omega : 1 ≤ d)]
      push_cast
      ring
    have hinv : (1 - τ)⁻¹ * (1 - τ) = 1 := inv_mul_cancel₀ htpos.ne'
    have hl := Real.one_sub_inv_le_log_of_pos htpos
    have key : ε / (1 + ε) = ((d:ℝ) - 1) * τ * (1 - τ)⁻¹ := by
      rw [div_eq_iff (by linarith)]
      linear_combination (-(τ * (w v p r - 1))) * hinv - hτW + (τ * (1 - τ)⁻¹) * htW
    have h1 : 1 - (1 - τ)⁻¹ = -τ * (1 - τ)⁻¹ := by linear_combination -hinv
    have hmul : ((d:ℝ) - 1) * (1 - (1 - τ)⁻¹) ≤ ((d:ℝ) - 1) * Real.log (1 - τ) :=
      mul_le_mul_of_nonneg_left hl (by linarith)
    rw [hFd]
    rw [h1] at hmul
    nlinarith

theorem w_le_inv {ι : Type} [Fintype ι] {d : ℕ} (v : ι → Fin d → ℝ) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hA : (momentMatrix v p).PosDef) (j : ι) : p j * w v p j ≤ 1 := by
  set A := momentMatrix v p with hAdef
  set x := A⁻¹ *ᵥ v j with hx
  have hw : w v p j = v j ⬝ᵥ x := rfl
  have hq : x ⬝ᵥ (A *ᵥ x) = v j ⬝ᵥ x := by
    rw [hx, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hA.det_pos.ne').isUnit,
      Matrix.one_mulVec]
    exact dotProduct_comm _ _
  have hm := moment_quad v p x
  have hge : p j * (v j ⬝ᵥ x) ^ 2 ≤ ∑ i, p i * (v i ⬝ᵥ x) ^ 2 :=
    Finset.single_le_sum (f := fun i => p i * (v i ⬝ᵥ x) ^ 2)
      (fun i _ => mul_nonneg (hp i) (sq_nonneg _)) (Finset.mem_univ j)
  have hy : p j * (v j ⬝ᵥ x) ^ 2 ≤ v j ⬝ᵥ x := by
    calc p j * (v j ⬝ᵥ x) ^ 2 ≤ ∑ i, p i * (v i ⬝ᵥ x) ^ 2 := hge
      _ = x ⬝ᵥ (A *ᵥ x) := hm.symm
      _ = v j ⬝ᵥ x := hq
  rw [hw]
  have hy0 : 0 ≤ v j ⬝ᵥ x := le_trans (mul_nonneg (hp j) (sq_nonneg _)) hy
  rcases hy0.lt_or_eq with hpos | hz
  · nlinarith
  · rw [← hz]; simp

theorem exists_factor {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (hP : P.PosSemidef) :
    ∃ R : Matrix (Fin d) (Fin d) ℝ, P = Rᴴ * R := by
  classical
  let U : Matrix (Fin d) (Fin d) ℝ := (hP.1.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
  let D : Matrix (Fin d) (Fin d) ℝ := Matrix.diagonal (fun i => Real.sqrt (hP.1.eigenvalues i))
  refine ⟨D * star U, ?_⟩
  have hs := hP.1.spectral_theorem
  have hDD : D * D = Matrix.diagonal (fun i => hP.1.eigenvalues i) := by
    simp only [D, Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    exact Real.mul_self_sqrt (hP.eigenvalues_nonneg i)
  have hDh : Dᴴ = D := by simp [D, Matrix.diagonal_conjTranspose]
  rw [Matrix.conjTranspose_mul, hDh, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc, Matrix.mul_assoc U D D, hDD]
  conv_lhs => rw [hs]
  simp [Unitary.conjStarAlgAut_apply, U, Function.comp_def, Matrix.star_eq_conjTranspose]

theorem log_det_le {d : ℕ} (hd : 0 < d) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hdet : 0 < S.det) (t : ℝ) (ht : S.trace ≤ t) : Real.log S.det ≤ d * Real.log (t / d) := by
  classical
  have hdet2 : S.det = ∏ i, hS.1.eigenvalues i := by
    simpa using hS.1.det_eq_prod_eigenvalues
  have htr2 : S.trace = ∑ i, hS.1.eigenvalues i := by
    simpa using hS.1.trace_eq_sum_eigenvalues
  set μ := hS.1.eigenvalues with hμdef
  have hμ0 : ∀ i, 0 ≤ μ i := hS.eigenvalues_nonneg
  have hμ : ∀ i, 0 < μ i := by
    intro i
    rcases (hμ0 i).lt_or_eq with h | h
    · exact h
    · exfalso
      have : S.det = 0 := by
        rw [hdet2]; exact Finset.prod_eq_zero (Finset.mem_univ i) h.symm
      linarith
  have hT : 0 < S.trace := by
    rw [htr2]; exact Finset.sum_pos (fun i _ => hμ i) ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  set s := t / d with hsdef
  have hs : 0 < s := div_pos (by linarith) hdR
  rw [hdet2, Real.log_prod (fun i _ => (hμ i).ne')]
  have key : ∀ i, Real.log (μ i) ≤ μ i / s - 1 + Real.log s := by
    intro i
    have := Real.log_le_sub_one_of_pos (div_pos (hμ i) hs)
    rw [Real.log_div (hμ i).ne' hs.ne'] at this
    linarith
  have hsum : ∑ i, (μ i / s - 1 + Real.log s) = (∑ i, μ i) / s - d + d * Real.log s := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hts : (∑ i, μ i) / s ≤ d := by
    rw [div_le_iff₀ hs, ← htr2, hsdef]
    rw [mul_div_cancel₀ _ hdR.ne']
    exact ht
  calc ∑ i, Real.log (μ i) ≤ ∑ i, (μ i / s - 1 + Real.log s) :=
        Finset.sum_le_sum (fun i _ => key i)
    _ = (∑ i, μ i) / s - d + d * Real.log s := hsum
    _ ≤ d * Real.log s := by linarith

theorem gap_bound {ι : Type} [Fintype ι] {d : ℕ} (hd : 0 < d) (v : ι → Fin d → ℝ)
    (p q : ι → ℝ) (hA : (momentMatrix v p).PosDef) (hq : q ∈ stdSimplex ℝ ι)
    (hB : (momentMatrix v q).PosDef) (W : ℝ) (hW : ∀ j, w v p j ≤ W) :
    F v q - F v p ≤ d * Real.log (W / d) := by
  set A := momentMatrix v p with hAdef
  set B := momentMatrix v q with hBdef
  obtain ⟨R, hR⟩ := exists_factor A⁻¹ hA.inv.posSemidef
  have hS : (R * B * Rᴴ).PosSemidef := hB.posSemidef.mul_mul_conjTranspose_same R
  have hdetA := hA.det_pos
  have hdetB := hB.det_pos
  have h1 : A⁻¹.det * A.det = 1 := by
    rw [← Matrix.det_mul, Matrix.nonsing_inv_mul _ (hdetA.ne').isUnit, Matrix.det_one]
  have hdetS : (R * B * Rᴴ).det = B.det / A.det := by
    have h2 : A⁻¹.det = Rᴴ.det * R.det := by rw [hR, Matrix.det_mul]
    have h3 : A⁻¹.det = A.det⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [Matrix.det_mul, Matrix.det_mul, div_eq_mul_inv, ← h3, h2]
    ring
  have htr : (R * B * Rᴴ).trace = ∑ j, q j * w v p j := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← hR, trace_mul_moment]
    rfl
  have htrW : ∑ j, q j * w v p j ≤ W := by
    calc ∑ j, q j * w v p j ≤ ∑ j, q j * W :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hW j) (hq.1 j))
      _ = W := by rw [← Finset.sum_mul, hq.2, one_mul]
  have hl := log_det_le hd _ hS (by rw [hdetS]; positivity) W ((le_of_eq htr).trans htrW)
  rw [hdetS, Real.log_div hdetB.ne' hdetA.ne'] at hl
  exact hl

theorem run_inv {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ} (hd : 2 ≤ d)
    (v : ι → Fin d → ℝ) (p : ℕ → ι → ℝ) (hM : 0 < Fintype.card ι)
    (hPD : (momentMatrix v (fun _ => 1 / (Fintype.card ι : ℝ))).PosDef) (hrun : IsBCDRun v p) :
    ∀ k, p k ∈ stdSimplex ℝ ι ∧ (momentMatrix v (p k)).PosDef := by
  obtain ⟨h0, hs⟩ := hrun
  have hM0 : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  intro k
  induction k with
  | zero =>
    rw [h0]
    refine ⟨⟨fun _ => by positivity, ?_⟩, hPD⟩
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  | succ k ih =>
    obtain ⟨r, hr, hpk⟩ := hs k
    obtain ⟨h1, h2, -⟩ := bcd_step v (p k) r ih.1 ih.2 hd hr
    rw [hpk]
    exact ⟨h1, h2⟩

/-- C3 (Khachiyan 1996, Theorem 1 iteration count), over a general finite index type. -/
theorem C3_gen : ∃ C0 : ℝ, 0 < C0 ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ)
    (v : ι → Fin d → ℝ) (p : ℕ → ι → ℝ) (δ : ℝ), 2 ≤ d → 3 ≤ Fintype.card ι → 0 < δ →
    (momentMatrix v (fun _ => 1 / (Fintype.card ι : ℝ))).PosDef → IsBCDRun v p →
    ∀ N : ℕ, (∀ k < N, ¬ IsRelaxedOpt v (p k) δ) →
      (N : ℝ) ≤ C0 * d * (1 / δ + Real.log d + Real.log (Real.log (Fintype.card ι)) + 1) := by
  refine ⟨50, by norm_num, ?_⟩
  intro ι _ _ d v p δ hd hM hδ hPD hrun N hN
  have hD : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0:ℝ) < d := by linarith
  have hMr : (3:ℝ) ≤ Fintype.card ι := by exact_mod_cast hM
  have inv := run_inv hd v p (by omega) hPD hrun
  obtain ⟨h0, hs⟩ := hrun
  choose r hr hpk using hs
  have st : ∀ k, 0 ≤ epsOf v (p k) ∧ w v (p k) (r k) = (1 + epsOf v (p k)) * d ∧
      Real.log (1 + epsOf v (p k)) - epsOf v (p k) / (1 + epsOf v (p k)) ≤
        F v (p (k + 1)) - F v (p k) := by
    intro k
    obtain ⟨_, _, h3, h4, h5⟩ := bcd_step v (p k) (r k) (inv k).1 (inv k).2 hd (hr k)
    rw [hpk k]
    exact ⟨h3, h4, h5⟩
  have hWd : ∀ k, w v (p k) (r k) / d = 1 + epsOf v (p k) := by
    intro k
    rw [(st k).2.1, mul_div_assoc, div_self hd0.ne', mul_one]
  have hB : 1 ≤ Real.log (Fintype.card ι) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hgap0 : ∀ k, F v (p N) - F v (p k) ≤ d * Real.log (1 + epsOf v (p k)) := by
    intro k
    have := gap_bound (by omega) v (p k) (p N) (inv k).2 (inv N).1 (inv N).2 _ (hr k)
    rwa [hWd k] at this
  have hG : ∀ k < N, F v (p N) - F v (p (k + 1)) ≤ F v (p N) - F v (p k) := by
    intro k _
    have := (st k).2.2
    have := phi_nonneg (st k).1
    linarith
  have hGN : F v (p N) - F v (p N) = 0 := sub_self _
  have hεδ : ∀ k < N, δ < epsOf v (p k) := by
    intro k hk
    have h := hN k hk
    simp only [IsRelaxedOpt, not_forall, not_le] at h
    obtain ⟨j, hj⟩ := h
    have h1 := hr k j
    have h2 := (st k).2.1
    nlinarith
  have hstep : ∀ k < N, Real.log (1 + epsOf v (p k)) - epsOf v (p k) / (1 + epsOf v (p k)) ≤
      (F v (p N) - F v (p k)) - (F v (p N) - F v (p (k + 1))) := by
    intro k _
    have := (st k).2.2
    linarith
  have hG0 : F v (p N) - F v (p 0) ≤ d * Real.log (Fintype.card ι) := by
    have hw0 := w_le_inv v (p 0) (fun i => (inv 0).1.1 i) (inv 0).2 (r 0)
    have hp0 : p 0 (r 0) = 1 / (Fintype.card ι : ℝ) := by rw [h0]
    rw [hp0] at hw0
    have hM0 : (0:ℝ) < Fintype.card ι := by linarith
    have hwM : w v (p 0) (r 0) ≤ Fintype.card ι := by
      rw [one_div, inv_mul_le_iff₀ hM0, mul_one] at hw0
      exact hw0
    have hε0 := (st 0).1
    have h2 := (st 0).2.1
    have h3 : 1 + epsOf v (p 0) ≤ Fintype.card ι := by nlinarith
    have h4 : Real.log (1 + epsOf v (p 0)) ≤ Real.log (Fintype.card ι) :=
      Real.log_le_log (by linarith) h3
    have := hgap0 0
    nlinarith
  have hcount := count_abstract (d := (d:ℝ)) (δ := δ) (B := (Fintype.card ι : ℝ)) (N := N)
    (G := fun k => F v (p N) - F v (p k)) (ε := fun k => epsOf v (p k))
    (by linarith) hδ hB hG hGN hεδ (fun k _ => hgap0 k) hstep hG0
  have hl6 : Real.log 6 ≤ 5 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 6)
    linarith
  have hld : 0 ≤ Real.log d := Real.log_nonneg (by linarith)
  have hll : 0 ≤ Real.log (Real.log (Fintype.card ι)) := Real.log_nonneg hB
  have hdδ : 0 ≤ (d:ℝ) / δ := by positivity
  have e1 : 50 * (d:ℝ) * (1 / δ + Real.log d + Real.log (Real.log (Fintype.card ι)) + 1) =
      50 * (d / δ) + 50 * (d * Real.log d) + 50 * (d * Real.log (Real.log (Fintype.card ι))) +
        50 * d := by ring
  have e2 : 7 * (d:ℝ) * (Real.log 6 + Real.log d + Real.log (Real.log (Fintype.card ι))) +
      12 * d / δ + 3 = 7 * (d * Real.log 6) + 7 * (d * Real.log d) +
        7 * (d * Real.log (Real.log (Fintype.card ι))) + 12 * (d / δ) + 3 := by ring
  have h6 : (d:ℝ) * Real.log 6 ≤ d * 5 := mul_le_mul_of_nonneg_left hl6 hd0.le
  have h7 : 0 ≤ (d:ℝ) * Real.log d := mul_nonneg hd0.le hld
  have h8 : 0 ≤ (d:ℝ) * Real.log (Real.log (Fintype.card ι)) := mul_nonneg hd0.le hll
  rw [e1]
  rw [e2] at hcount
  linarith

end KH671C3


/-! C5 lift_start for KhachiyanRounding.BCD (671ed666). -/

set_option autoImplicit false

namespace KH671

open KhachiyanRounding.BCD
open scoped Matrix
open KhachiyanRound.BCD (momentMatrix liftPts aggr blockMatrix)

theorem moment_lift {m n : ℕ} (a : Fin m → Fin n → ℝ) (q : Fin m ⊕ Fin m → ℝ) :
    momentMatrix (liftPts a) q = ∑ j, aggr q j •
      Matrix.vecMulVec (Fin.snoc (α := fun _ => ℝ) (a j) 1) (Fin.snoc (α := fun _ => ℝ) (a j) 1) := by
  simp only [momentMatrix, Fintype.sum_sum_type, liftPts, Sum.elim_inl, Sum.elim_inr,
    Matrix.neg_vecMulVec, Matrix.vecMulVec_neg, neg_neg, aggr, add_smul, Finset.sum_add_distrib]

theorem quad_vmv {d : ℕ} (s x : Fin d → ℝ) :
    x ⬝ᵥ (Matrix.vecMulVec s s *ᵥ x) = (s ⬝ᵥ x) ^ 2 := by
  have h : Matrix.vecMulVec s s *ᵥ x = (s ⬝ᵥ x) • s := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h, dotProduct_smul, smul_eq_mul, dotProduct_comm]; ring

theorem snoc_dot {n : ℕ} (u : Fin n → ℝ) (x : Fin (n + 1) → ℝ) :
    Fin.snoc (α := fun _ => ℝ) u 1 ⬝ᵥ x = u ⬝ᵥ (fun i => x (Fin.castSucc i)) + x (Fin.last n) := by
  simp [dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

theorem lift_moment_eq_block {m n : ℕ} (a : Fin m → Fin n → ℝ) (q : Fin m ⊕ Fin m → ℝ)
    (hq : ∑ j, aggr q j = 1) : momentMatrix (liftPts a) q = blockMatrix a (aggr q) := by
  rw [moment_lift]
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [blockMatrix, Matrix.sum_apply, Matrix.vecMulVec_apply, momentMatrix, hq,
      Fin.snoc_castSucc, Fin.snoc_last, mul_comm]

theorem lift_start_card {m n : ℕ} (a : Fin m → Fin n → ℝ)
    (ha : affineSpan ℝ (Set.range a) = ⊤) : n + 1 ≤ m := by
  rcases Nat.eq_zero_or_eq_succ_pred m with hm | hm
  · subst hm
    have : Set.range a = ∅ := Set.range_eq_empty a
    rw [this, AffineSubspace.span_empty] at ha
    exact absurd ha bot_ne_top
  · have hne : (Set.range a).Nonempty := ⟨a ⟨0, by omega⟩, Set.mem_range_self _⟩
    have hv := (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ (Fin n → ℝ) (Fin n → ℝ) hne).1 ha
    have hle := finrank_vectorSpan_range_le ℝ a (n := m - 1) (by simp; omega)
    rw [hv, finrank_top, Module.finrank_fin_fun] at hle
    omega

theorem lift_start_posDef {m n : ℕ} (a : Fin m → Fin n → ℝ)
    (ha : affineSpan ℝ (Set.range a) = ⊤) :
    (momentMatrix (liftPts a) (fun _ => 1 / ((2 * m : ℕ) : ℝ))).PosDef := by
  have hm := lift_start_card a ha
  set s : Fin m → Fin (n + 1) → ℝ := fun j => Fin.snoc (α := fun _ => ℝ) (a j) 1 with hs
  set c : ℝ := 1 / ((2 * m : ℕ) : ℝ) with hc
  have hc0 : 0 < c := by rw [hc]; exact one_div_pos.2 (by exact_mod_cast (by omega : 0 < 2 * m))
  rw [moment_lift]
  simp only [aggr]
  refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨?_, ?_⟩
  · ext i j
    simp [Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, mul_comm]
  · intro x hx
    simp only [star_trivial, Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum,
      dotProduct_smul, smul_eq_mul, quad_vmv]
    have hnn : ∀ j ∈ (Finset.univ : Finset (Fin m)),
        0 ≤ (c + c) * (Fin.snoc (α := fun _ => ℝ) (a j) 1 ⬝ᵥ x) ^ 2 :=
      fun j _ => mul_nonneg (by linarith) (sq_nonneg _)
    rcases (Finset.sum_nonneg hnn).lt_or_eq with h | h
    · exact h
    exfalso
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h.symm
    have hdot : ∀ j, Fin.snoc (α := fun _ => ℝ) (a j) 1 ⬝ᵥ x = 0 := fun j => by
      have := hz j (Finset.mem_univ _)
      have h2 : (0 : ℝ) < c + c := by linarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1
        ((mul_eq_zero.1 this).resolve_left h2.ne')
    set y : Fin n → ℝ := fun i => x (Fin.castSucc i) with hy
    have hdot' : ∀ j, a j ⬝ᵥ y + x (Fin.last n) = 0 := fun j => by
      rw [← snoc_dot]; exact hdot j
    let j0 : Fin m := ⟨0, by omega⟩
    let f : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun v => v ⬝ᵥ y
        map_add' := fun u v => add_dotProduct u v y
        map_smul' := fun r v => by simp [smul_dotProduct] }
    have hne : (Set.range a).Nonempty := ⟨a j0, Set.mem_range_self _⟩
    have hv := (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ (Fin n → ℝ) (Fin n → ℝ) hne).1 ha
    rw [vectorSpan_range_eq_span_range_vsub_right ℝ a j0] at hv
    have hker : Submodule.span ℝ (Set.range fun i => a i -ᵥ a j0) ≤ LinearMap.ker f := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, f, LinearMap.coe_mk, AddHom.coe_mk,
        vsub_eq_sub, sub_dotProduct]
      linarith [hdot' i, hdot' j0]
    rw [hv] at hker
    have hyy : y ⬝ᵥ y = 0 := by
      have : y ∈ LinearMap.ker f := hker Submodule.mem_top
      simpa [f] using this
    have hy0 : y = 0 := dotProduct_self_eq_zero.1 hyy
    have hl : x (Fin.last n) = 0 := by
      have := hdot' j0; rw [hy0, dotProduct_zero, zero_add] at this; exact this
    apply hx
    ext i
    refine Fin.lastCases hl (fun i' => ?_) i
    have := congrFun hy0 i'
    simpa [hy] using this

theorem C5_lift_start {n m : ℕ} (a : Fin m → Fin n → ℝ)
    (ha : affineSpan ℝ (Set.range a) = ⊤) :
    n + 1 ≤ m ∧
    (momentMatrix (liftPts a) (fun _ => 1 / ((2 * m : ℕ) : ℝ))).PosDef ∧
    ∀ q : Fin m ⊕ Fin m → ℝ, ∑ j, aggr q j = 1 →
      momentMatrix (liftPts a) q = blockMatrix a (aggr q) :=
  ⟨lift_start_card a ha, lift_start_posDef a ha, fun q hq => lift_moment_eq_block a q hq⟩


/-! ## C4 lifted rounding (Lemma 5 and (3.5)-(3.7)) -/

open KhachiyanRound.BCD (SF w IsRelaxedOpt lemma5Ellipsoid)

/-- The barycentre `∑ p_j a_j`. -/
noncomputable def bar {m n : ℕ} (a : Fin m → Fin n → ℝ) (p : Fin m → ℝ) : Fin n → ℝ :=
  ∑ j, p j • a j

theorem snoc_dot2 {n : ℕ} (u v : Fin n → ℝ) (α β : ℝ) :
    Fin.snoc (α := fun _ => ℝ) u α ⬝ᵥ Fin.snoc (α := fun _ => ℝ) v β = u ⬝ᵥ v + α * β := by
  simp [dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

theorem vmv_mulVec {d : ℕ} (s x : Fin d → ℝ) :
    Matrix.vecMulVec s s *ᵥ x = (s ⬝ᵥ x) • s := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem moment_quad {ι : Type} [Fintype ι] {d : ℕ} (v : ι → Fin d → ℝ) (p : ι → ℝ)
    (x : Fin d → ℝ) : x ⬝ᵥ (momentMatrix v p *ᵥ x) = ∑ i, p i * (v i ⬝ᵥ x) ^ 2 := by
  simp only [momentMatrix, Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum,
    dotProduct_smul, smul_eq_mul, quad_vmv]

theorem moment_posSemidef {ι : Type} [Fintype ι] {d : ℕ} (v : ι → Fin d → ℝ) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) : (momentMatrix v p).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x => ?_⟩
  · ext i j
    simp [momentMatrix, Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
      mul_comm]
  · rw [star_trivial, moment_quad]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (sq_nonneg _)

theorem posDef_symm {d : ℕ} {P : Matrix (Fin d) (Fin d) ℝ} (h : P.PosDef) : Pᵀ = P := by
  have := h.1
  rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this

theorem bil_symm {d : ℕ} {P : Matrix (Fin d) (Fin d) ℝ} (hP : Pᵀ = P) (u v : Fin d → ℝ) :
    u ⬝ᵥ (P *ᵥ v) = v ⬝ᵥ (P *ᵥ u) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hP, dotProduct_comm]

theorem qnn {d : ℕ} {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosDef) (x : Fin d → ℝ) :
    0 ≤ x ⬝ᵥ (P *ᵥ x) := by
  by_cases hx : x = 0
  · simp [hx]
  · have := (Matrix.posDef_iff_dotProduct_mulVec.1 hP).2 hx
    rw [star_trivial] at this
    exact this.le

theorem quad_convex {d : ℕ} {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosDef) (b : Fin d → ℝ)
    (r : ℝ) : Convex ℝ {x | (x - b) ⬝ᵥ (P *ᵥ (x - b)) ≤ r} := by
  intro x hx y hy θ φ hθ hφ hθφ
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have he : θ • x + φ • y - b = θ • (x - b) + φ • (y - b) := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (b i) * hθφ
  rw [he]
  have hs := bil_symm (posDef_symm hP) (x - b) (y - b)
  have hn := qnn hP ((x - b) - (y - b))
  obtain rfl : φ = 1 - θ := by linarith
  generalize x - b = u at hx hs hn ⊢
  generalize y - b = v at hy hs hn ⊢
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub, dotProduct_add,
    add_dotProduct, dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct,
    smul_eq_mul] at hn ⊢
  rw [← hs] at hn ⊢
  nlinarith [mul_nonneg (mul_nonneg hθ hφ) hn, mul_le_mul_of_nonneg_left hx hθ,
    mul_le_mul_of_nonneg_left hy hφ]

theorem quad_cs {d : ℕ} {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosDef) (u v : Fin d → ℝ) :
    (u ⬝ᵥ (P *ᵥ v)) ^ 2 ≤ (u ⬝ᵥ (P *ᵥ u)) * (v ⬝ᵥ (P *ᵥ v)) := by
  have hs := bil_symm (posDef_symm hP) u v
  have h := discrim_le_zero (K := ℝ) (a := v ⬝ᵥ (P *ᵥ v)) (b := 2 * (u ⬝ᵥ (P *ᵥ v)))
    (c := u ⬝ᵥ (P *ᵥ u)) (fun x => by
      have := qnn hP (u + x • v)
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
        dotProduct_smul, smul_dotProduct, smul_eq_mul] at this
      rw [← hs] at this
      linarith)
  unfold discrim at h
  nlinarith [h]

theorem block_mulVec {m n : ℕ} (a : Fin m → Fin n → ℝ) (p : Fin m → ℝ) (v : Fin n → ℝ)
    (c : ℝ) : blockMatrix a p *ᵥ Fin.snoc (α := fun _ => ℝ) v c =
      Fin.snoc (α := fun _ => ℝ) (momentMatrix a p *ᵥ v + c • bar a p) (bar a p ⬝ᵥ v + c) := by
  ext i
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, blockMatrix, bar,
      Finset.sum_apply, Finset.sum_mul, mul_comm]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, blockMatrix, bar,
      Finset.sum_apply, mul_comm]

theorem cov_eq {m n : ℕ} (a : Fin m → Fin n → ℝ) (p : Fin m → ℝ) :
    covariance a p = momentMatrix a p - Matrix.vecMulVec (bar a p) (bar a p) := rfl

theorem cov_mulVec {m n : ℕ} (a : Fin m → Fin n → ℝ) (p : Fin m → ℝ) (v : Fin n → ℝ) :
    covariance a p *ᵥ v = momentMatrix a p *ᵥ v - (bar a p ⬝ᵥ v) • bar a p := by
  rw [cov_eq, Matrix.sub_mulVec, vmv_mulVec]

theorem cov_herm {m n : ℕ} (a : Fin m → Fin n → ℝ) (p : Fin m → ℝ) :
    (covariance a p).IsHermitian := by
  ext i j
  simp [cov_eq, bar, momentMatrix, Matrix.sum_apply, Matrix.vecMulVec_apply, mul_comm]

theorem cov_posDef {m n : ℕ} (a : Fin m → Fin n → ℝ) (p : Fin m → ℝ)
    (hM : (blockMatrix a p).PosDef) : (covariance a p).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨cov_herm a p, fun x hx => ?_⟩
  have hz : Fin.snoc (α := fun _ => ℝ) x (-(bar a p ⬝ᵥ x)) ≠ 0 := by
    intro h; apply hx; ext i
    have := congrFun h (Fin.castSucc i)
    simpa [Fin.snoc_castSucc] using this
  have := (Matrix.posDef_iff_dotProduct_mulVec.1 hM).2 hz
  rw [star_trivial, block_mulVec, snoc_dot2] at this
  rw [star_trivial, cov_mulVec]
  simp only [dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul] at this ⊢
  rw [dotProduct_comm x (bar a p)] at this ⊢
  nlinarith [this]

theorem schur_quad {m n : ℕ} (a : Fin m → Fin n → ℝ) (p : Fin m → ℝ)
    (hM : (blockMatrix a p).PosDef) (hC : (covariance a p).PosDef) (x : Fin n → ℝ) :
    Fin.snoc (α := fun _ => ℝ) x 1 ⬝ᵥ ((blockMatrix a p)⁻¹ *ᵥ Fin.snoc (α := fun _ => ℝ) x 1) =
      1 + (x - bar a p) ⬝ᵥ ((covariance a p)⁻¹ *ᵥ (x - bar a p)) := by
  obtain ⟨u, hu⟩ : ∃ u, u = (covariance a p)⁻¹ *ᵥ (x - bar a p) := ⟨_, rfl⟩
  have hCu : covariance a p *ᵥ u = x - bar a p := by
    rw [hu, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hC.det_pos.ne'), Matrix.one_mulVec]
  have hA : momentMatrix a p *ᵥ u = covariance a p *ᵥ u + (bar a p ⬝ᵥ u) • bar a p := by
    rw [cov_mulVec]; abel
  have hMz : blockMatrix a p *ᵥ Fin.snoc (α := fun _ => ℝ) u (1 - bar a p ⬝ᵥ u) =
      Fin.snoc (α := fun _ => ℝ) x 1 := by
    rw [block_mulVec, hA, hCu]
    congr 1
    · ext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    · ring
  have hinv : (blockMatrix a p)⁻¹ *ᵥ Fin.snoc (α := fun _ => ℝ) x 1 =
      Fin.snoc (α := fun _ => ℝ) u (1 - bar a p ⬝ᵥ u) := by
    rw [← hMz, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hM.det_pos.ne'), Matrix.one_mulVec]
  rw [hinv, snoc_dot2, ← hu, sub_dotProduct]; ring

theorem cov_quad {m n : ℕ} (a : Fin m → Fin n → ℝ) (p : Fin m → ℝ) (hp1 : ∑ j, p j = 1)
    (g : Fin n → ℝ) :
    g ⬝ᵥ (covariance a p *ᵥ g) = ∑ j, p j * (g ⬝ᵥ (a j - bar a p)) ^ 2 := by
  have hgb : g ⬝ᵥ bar a p = ∑ j, p j * (g ⬝ᵥ a j) := by
    simp [bar, dotProduct_sum, dotProduct_smul]
  rw [cov_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul, moment_quad,
    dotProduct_comm (bar a p) g, hgb]
  simp only [dotProduct_sub, dotProduct_comm (a _) g, hgb]
  have : ∀ j, p j * (g ⬝ᵥ a j - ∑ i, p i * (g ⬝ᵥ a i)) ^ 2 =
      p j * (g ⬝ᵥ a j) ^ 2 - 2 * (∑ i, p i * (g ⬝ᵥ a i)) * (p j * (g ⬝ᵥ a j)) +
        (∑ i, p i * (g ⬝ᵥ a i)) ^ 2 * p j := fun j => by ring
  rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hp1]
  ring

theorem inner_round {m n : ℕ} (a : Fin m → Fin n → ℝ) (p : Fin m → ℝ)
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (hC : (covariance a p).PosDef) (t : ℝ) (ht : 0 < t)
    (hw : ∀ j, (a j - bar a p) ⬝ᵥ ((covariance a p)⁻¹ *ᵥ (a j - bar a p)) ≤ t)
    (u : Fin n → ℝ) (hu : t * (u ⬝ᵥ ((covariance a p)⁻¹ *ᵥ u)) ≤ 1) :
    bar a p + u ∈ convexHull ℝ (Set.range a) := by
  by_contra hnot
  obtain ⟨f, u0, hf1, hf2⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _)
    (((Set.finite_range a).isCompact_convexHull ℝ).isClosed) hnot
  set C := covariance a p with hCdef
  set b := bar a p with hbdef
  let g : Fin n → ℝ := fun i => f (fun j => if i = j then 1 else 0)
  have hfg : ∀ v, f v = g ⬝ᵥ v := by
    intro v
    conv_lhs => rw [pi_eq_sum_univ v]
    simp only [map_sum, map_smul, smul_eq_mul, dotProduct, g]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  set σ2 := g ⬝ᵥ (C *ᵥ g) with hσ2
  have hσ0 : 0 ≤ σ2 := qnn hC g
  have hCC : ∀ d, C *ᵥ (C⁻¹ *ᵥ d) = d := fun d => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hC.det_pos.ne'),
      Matrix.one_mulVec]
  have hcs : ∀ d, (g ⬝ᵥ d) ^ 2 ≤ σ2 * (d ⬝ᵥ (C⁻¹ *ᵥ d)) := fun d => by
    have := quad_cs hC g (C⁻¹ *ᵥ d)
    rwa [hCC, dotProduct_comm (C⁻¹ *ᵥ d) d] at this
  set y : Fin m → ℝ := fun j => g ⬝ᵥ (a j - b) with hy
  set κ := g ⬝ᵥ u with hκ
  have hyk : ∀ j, y j < κ := by
    intro j
    have h1 := hf1 (a j) (subset_convexHull ℝ _ (Set.mem_range_self j))
    rw [hfg] at h1
    rw [hfg, dotProduct_add] at hf2
    simp only [hy, hκ, dotProduct_sub]
    linarith
  have hgb : g ⬝ᵥ b = ∑ j, p j * (g ⬝ᵥ a j) := by
    simp [hbdef, bar, dotProduct_sum, dotProduct_smul]
  have hsum0 : ∑ j, p j * y j = 0 := by
    simp only [hy, dotProduct_sub, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1,
      one_mul, ← hgb, sub_self]
  have hsum2 : ∑ j, p j * y j ^ 2 = σ2 := by rw [hσ2, cov_quad a p hp1 g]
  have hy2 : ∀ j, y j ^ 2 ≤ σ2 * t := fun j =>
    (hcs (a j - b)).trans (mul_le_mul_of_nonneg_left (hw j) hσ0)
  have hk2 : t * κ ^ 2 ≤ σ2 := by
    have := hcs u
    nlinarith [mul_le_mul_of_nonneg_left hu hσ0, ht]
  -- κ > 0
  have hkpos : 0 < κ := by
    have hex : ∃ j, 0 < p j := by
      by_contra hno; push Not at hno
      have : ∑ j, p j ≤ 0 := Finset.sum_nonpos fun j _ => hno j
      linarith
    obtain ⟨j0, hj0⟩ := hex
    have hpos : 0 < ∑ j, p j * (κ - y j) :=
      Finset.sum_pos' (fun j _ => mul_nonneg (hp0 j) (sub_nonneg.2 (hyk j).le))
        ⟨j0, Finset.mem_univ _, mul_pos hj0 (sub_pos.2 (hyk j0))⟩
    have : ∑ j, p j * (κ - y j) = κ := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul, hsum0,
        sub_zero]
    linarith
  set σ := Real.sqrt σ2 with hσ
  set r := Real.sqrt t with hr
  have hσσ : σ ^ 2 = σ2 := Real.sq_sqrt hσ0
  have hrr : r ^ 2 = t := Real.sq_sqrt ht.le
  have hσnn : 0 ≤ σ := Real.sqrt_nonneg _
  have hrpos : 0 < r := Real.sqrt_pos.2 ht
  have hrk : r * κ ≤ σ := (abs_le_of_sq_le_sq' (by rw [mul_pow, hrr, hσσ]; exact hk2) hσnn).2
  have hylo : ∀ j, 0 ≤ y j + r * σ := fun j => by
    have := (abs_le_of_sq_le_sq' (a := y j) (b := r * σ) (by rw [mul_pow, hrr, hσσ, mul_comm]; exact hy2 j)
      (mul_nonneg hrpos.le hσnn)).1
    linarith
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin m)), 0 ≤ p j * ((κ - y j) * (y j + r * σ)) :=
    fun j _ => mul_nonneg (hp0 j) (mul_nonneg (sub_nonneg.2 (hyk j).le) (hylo j))
  have hS : ∑ j, p j * ((κ - y j) * (y j + r * σ)) = κ * r * σ - σ2 := by
    have : ∀ j, p j * ((κ - y j) * (y j + r * σ)) =
        κ * (p j * y j) + κ * r * σ * p j - p j * y j ^ 2 - r * σ * (p j * y j) :=
      fun j => by ring
    rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hsum0,
      hp1, hsum2]
    ring
  have hSle : κ * r * σ - σ2 ≤ 0 := by
    rw [← hσσ]; nlinarith [mul_le_mul_of_nonneg_right hrk hσnn]
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hterm).1
    (le_antisymm (hS ▸ hSle) (Finset.sum_nonneg hterm))
  have hlin : ∀ j, p j * (y j + r * σ) = 0 := fun j => by
    have h0 := hall j (Finset.mem_univ _)
    have hk : κ - y j ≠ 0 := (sub_pos.2 (hyk j)).ne'
    have : (κ - y j) * (p j * (y j + r * σ)) = 0 := by rw [← h0]; ring
    exact (mul_eq_zero.1 this).resolve_left hk
  have hrs : r * σ = 0 := by
    have : ∑ j, p j * (y j + r * σ) = 0 := Finset.sum_eq_zero fun j _ => hlin j
    simp only [mul_add, Finset.sum_add_distrib, hsum0, zero_add] at this
    rw [Finset.sum_congr rfl fun j _ => mul_comm (p j) (r * σ), ← Finset.mul_sum, hp1,
      mul_one] at this
    exact this
  have hσz : σ = 0 := (mul_eq_zero.1 hrs).resolve_left hrpos.ne'
  have : σ2 = 0 := by rw [← hσσ, hσz]; ring
  nlinarith [hk2, hkpos, ht]

theorem C4_lifted_rounding {n m : ℕ} (a : Fin m → Fin n → ℝ) (q : Fin m ⊕ Fin m → ℝ) (ε : ℝ)
    (hn : 1 ≤ n) (hε : 0 < ε) (hq : q ∈ SF (liftPts a))
    (hopt : IsRelaxedOpt (liftPts a) q ((n : ℝ) * ε / (n + 1 : ℕ))) :
    aggr q ∈ stdSimplex ℝ (Fin m) ∧ (blockMatrix a (aggr q)).PosDef ∧
    (covariance a (aggr q)).PosDef ∧
    (((1 + ε) * (n : ℝ)) • covariance a (aggr q)).PosDef ∧
    LinearOptimization.ellipsoid (∑ j, aggr q j • a j)
        (((1 + ε) * (n : ℝ)) • covariance a (aggr q)) = lemma5Ellipsoid a (aggr q) ε ∧
    Rounds a (∑ j, aggr q j • a j) (((1 + ε) * (n : ℝ)) • covariance a (aggr q))
      ((1 + ε) * (n : ℝ)) := by
  obtain ⟨⟨hq0, hq1⟩, hdet⟩ := hq
  have hbar : (∑ j, aggr q j • a j) = bar a (aggr q) := rfl
  rw [hbar]
  set p := aggr q with hpdef
  have hp0 : ∀ j, 0 ≤ p j := fun j => add_nonneg (hq0 _) (hq0 _)
  have hp1 : ∑ j, p j = 1 := by
    rw [← hq1, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => rfl
  have hMeq : momentMatrix (liftPts a) q = blockMatrix a p := lift_moment_eq_block a q hp1
  have hMpd : (blockMatrix a p).PosDef := by
    rw [← hMeq]
    exact (moment_posSemidef _ _ hq0).posDef_iff_det_ne_zero.2 hdet.ne'
  have hCpd := cov_posDef a p hMpd
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set t : ℝ := (1 + ε) * (n : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; nlinarith
  set C := covariance a p with hCdef
  set b := bar a p with hbdef
  have hw : ∀ j, (a j - b) ⬝ᵥ (C⁻¹ *ᵥ (a j - b)) ≤ t := by
    intro j
    have h1 := hopt (Sum.inl j)
    simp only [w] at h1
    rw [hMeq] at h1
    simp only [liftPts, Sum.elim_inl] at h1
    rw [schur_quad a p hMpd hCpd] at h1
    have : (1 + (n : ℝ) * ε / ((n + 1 : ℕ) : ℝ)) * ((n + 1 : ℕ) : ℝ) = 1 + t := by
      rw [ht]; push_cast; field_simp; ring
    linarith
  have hQinv : (t • C)⁻¹ = t⁻¹ • C⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hCpd.det_pos.ne'),
      inv_mul_cancel₀ ht0.ne', one_smul]
  have hmemE : ∀ x, x ∈ LinearOptimization.ellipsoid b (t • C) ↔
      (x - b) ⬝ᵥ (C⁻¹ *ᵥ (x - b)) ≤ t := by
    intro x
    simp only [LinearOptimization.ellipsoid, Set.mem_setOf_eq, hQinv, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul]
    rw [inv_mul_le_iff₀ ht0, mul_one]
  refine ⟨⟨hp0, hp1⟩, hMpd, hCpd, hCpd.smul ht0, ?_, ?_⟩
  · ext x
    rw [hmemE]
    simp only [lemma5Ellipsoid, KhachiyanRound.BCD.Eprime, Set.mem_setOf_eq]
    have hr0 : 0 < Real.sqrt (1 + t) := Real.sqrt_pos.2 (by linarith)
    have hr2 : Real.sqrt (1 + t) ^ 2 = 1 + t := Real.sq_sqrt (by linarith)
    have hS := schur_quad a p hMpd hCpd x
    rw [Set.mem_smul_set]
    constructor
    · intro h
      refine ⟨(Real.sqrt (1 + t))⁻¹ • Fin.snoc (α := fun _ => ℝ) x 1, ?_, ?_⟩
      · simp only [LinearOptimization.ellipsoid, Set.mem_setOf_eq, sub_zero,
          Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
        rw [hS, ← mul_assoc, ← mul_inv, ← sq, hr2, inv_mul_le_iff₀ (by linarith)]
        linarith
      · rw [smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
    · rintro ⟨z, hz, hzx⟩
      have hz' : z = (Real.sqrt (1 + t))⁻¹ • Fin.snoc (α := fun _ => ℝ) x 1 := by
        rw [← hzx, smul_smul, inv_mul_cancel₀ hr0.ne', one_smul]
      rw [hz'] at hz
      simp only [LinearOptimization.ellipsoid, Set.mem_setOf_eq, sub_zero,
        Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at hz
      rw [hS, ← mul_assoc, ← mul_inv, ← sq, hr2, inv_mul_le_iff₀ (by linarith)] at hz
      linarith
  unfold Rounds
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [hmemE] at hx
    have hh : AffineMap.homothety b t⁻¹ x = b + t⁻¹ • (x - b) := by
      rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, add_comm]
    rw [hh]
    refine inner_round a p hp0 hp1 hCpd t ht0 (fun j => hw j) _ ?_
    simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    have hD := qnn hCpd.inv (x - b)
    calc t * (t⁻¹ * (t⁻¹ * ((x - b) ⬝ᵥ (C⁻¹ *ᵥ (x - b))))) =
        t⁻¹ * ((x - b) ⬝ᵥ (C⁻¹ *ᵥ (x - b))) := by field_simp
      _ ≤ t⁻¹ * t := mul_le_mul_of_nonneg_left hx (inv_nonneg.2 ht0.le)
      _ = 1 := inv_mul_cancel₀ ht0.ne'
  · refine convexHull_min ?_ ?_
    · rintro _ ⟨j, rfl⟩
      exact (hmemE _).2 (hw j)
    · have : LinearOptimization.ellipsoid b (t • C) =
          {x | (x - b) ⬝ᵥ (C⁻¹ *ᵥ (x - b)) ≤ t} := Set.ext hmemE
      rw [this]
      exact quad_convex hCpd.inv b t

end KH671


/-! Runs/Sat library L0 for KhachiyanRounding.BCD (671ed666) + C1 invert_spec. -/

set_option autoImplicit false

namespace KH671

open KhachiyanRounding.BCD
open scoped Matrix
open KhachiyanRound.BCD (momentMatrix SF w IsRelaxedOpt epsOf IsBCDRun liftPts aggr
  blockMatrix lemma5Ellipsoid)

/-- `Sat P Q`: from every start counter `c`, `P` succeeds with one value `x`, adding one
cost `k` (independent of `c`), and `Q x k` holds. -/
def Sat {α : Type} (P : Calc α) (Q : α → ℕ → Prop) : Prop :=
  ∃ x k, Q x k ∧ ∀ c, P c = some (x, c + k)

def Runs {α : Type} (P : Calc α) (x : α) (K : ℕ) : Prop :=
  ∃ k ≤ K, ∀ c, P c = some (x, c + k)

theorem Sat.mono {α : Type} {P : Calc α} {Q Q' : α → ℕ → Prop} (h : Sat P Q)
    (hQ : ∀ x k, Q x k → Q' x k) : Sat P Q' := by
  obtain ⟨x, k, hq, hP⟩ := h
  exact ⟨x, k, hQ x k hq, hP⟩

theorem Sat.runs {α : Type} {P : Calc α} {x : α} {K : ℕ}
    (h : Sat P (fun y k => y = x ∧ k ≤ K)) : Runs P x K := by
  obtain ⟨y, k, ⟨rfl, hk⟩, hP⟩ := h
  exact ⟨k, hk, hP⟩

theorem Sat.ret {α : Type} {x : α} {Q : α → ℕ → Prop} (h : Q x 0) :
    Sat (pure x : Calc α) Q :=
  ⟨x, 0, h, fun _ => rfl⟩

theorem Sat.bnd {α β : Type} {P : Calc α} {f : α → Calc β} {Q : α → ℕ → Prop}
    {R : β → ℕ → Prop} (hP : Sat P Q)
    (hf : ∀ x k, Q x k → Sat (f x) (fun y k' => R y (k + k'))) : Sat (P >>= f) R := by
  obtain ⟨x, k, hq, hPc⟩ := hP
  obtain ⟨y, k', hr, hfc⟩ := hf x k hq
  refine ⟨y, k + k', hr, fun c => ?_⟩
  show StateT.bind P f c = _
  simp [StateT.bind, hPc, hfc, Nat.add_assoc]

theorem Sat.foldl_gen {β ι : Type} (f : β → ι → Calc β) (I : ℕ → β → ℕ → Prop) :
    ∀ (L : List ι) (s : ℕ) (b : β) (k0 : ℕ), I s b k0 →
    (∀ j (hj : j < L.length) b k, I (s + j) b k →
      Sat (f b L[j]) (fun b' k' => I (s + j + 1) b' (k + k'))) →
    Sat (L.foldlM f b) (fun b' k' => I (s + L.length) b' (k0 + k'))
  | [], s, b, k0, h0, _ => Sat.ret (by simpa using h0)
  | i :: L, s, b, k0, h0, hstep => by
    have hs : ∀ j, s + (j + 1) = s + 1 + j := fun j => by omega
    have h1 := hstep 0 (by simp) b k0 (by simpa using h0)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h1
    rw [List.foldlM_cons]
    refine Sat.bnd h1 (fun b1 k1 hb1 => ?_)
    have ih := Sat.foldl_gen f I L (s + 1) b1 (k0 + k1) hb1 (fun j hj b2 k h => by
      have h' := hstep (j + 1) (by simp only [List.length_cons]; omega) b2 k
        (by rw [hs]; exact h)
      rw [hs] at h'
      simpa only [List.getElem_cons_succ] using h')
    refine ih.mono (fun y k' hy => ?_)
    have e1 : s + (i :: L).length = s + 1 + L.length := by simp only [List.length_cons]; omega
    rw [e1, ← Nat.add_assoc]
    exact hy

theorem Sat.foldl_fin {β : Type} {n : ℕ} (f : β → Fin n → Calc β) (I : ℕ → β → ℕ → Prop)
    (b : β) (k0 : ℕ) (h0 : I 0 b k0)
    (hstep : ∀ i : Fin n, ∀ b k, I i b k → Sat (f b i) (fun b' k' => I (i + 1) b' (k + k'))) :
    Sat ((List.finRange n).foldlM f b) (fun b' k' => I n b' (k0 + k')) := by
  have h := Sat.foldl_gen f I (List.finRange n) 0 b k0 h0 (fun j hj b k hI => by
    rw [List.length_finRange] at hj
    have := hstep ⟨j, hj⟩ b k (by simpa using hI)
    simpa [List.getElem_finRange] using this)
  simpa using h

/-! Primitives with exact costs. -/

theorem sat_add (x y : ℝ) : Sat (add x y) (fun z k => z = x + y ∧ k = 1) :=
  ⟨_, 1, ⟨rfl, rfl⟩, fun _ => rfl⟩

theorem sat_sub (x y : ℝ) : Sat (sub x y) (fun z k => z = x - y ∧ k = 1) :=
  ⟨_, 1, ⟨rfl, rfl⟩, fun _ => rfl⟩

theorem sat_mul (x y : ℝ) : Sat (mul x y) (fun z k => z = x * y ∧ k = 1) :=
  ⟨_, 1, ⟨rfl, rfl⟩, fun _ => rfl⟩

theorem sat_le (x y : ℝ) : Sat (le x y) (fun z k => (z = true ↔ x ≤ y) ∧ k = 1) := by
  classical
  refine ⟨_, 1, ⟨?_, rfl⟩, fun c => rfl⟩
  simp

theorem sat_divide (x y : ℝ) (hy : y ≠ 0) : Sat (divide x y) (fun z k => z = x / y ∧ k = 2) :=
  ⟨_, 2, ⟨rfl, rfl⟩, fun _ => by simp [divide, hy]⟩

/-- Exact-cost bind. -/
theorem Sat.bndE {α β : Type} {P : Calc α} {f : α → Calc β} {x : α} {y : β} {c d : ℕ}
    (hP : Sat P (fun z k => z = x ∧ k = c)) (hf : Sat (f x) (fun z k => z = y ∧ k = d)) :
    Sat (P >>= f) (fun z k => z = y ∧ k = c + d) := by
  refine Sat.bnd hP (fun x' k ⟨hx, hk⟩ => ?_)
  subst hx hk
  exact hf.mono (fun z k' ⟨h1, h2⟩ => ⟨h1, by rw [h2]⟩)

theorem sat_vector {n : ℕ} (f : Fin n → Calc ℝ) (x : Fin n → ℝ) (c : ℕ)
    (hf : ∀ i, Sat (f i) (fun y k => y = x i ∧ k = c)) :
    Sat (vector f) (fun v k => v = x ∧ k = n * c) := by
  unfold vector
  have h := Sat.foldl_fin (fun v i => do
      let y ← f i
      pure (Function.update v i y))
    (fun j v k => (∀ i : Fin n, v i = if (i : ℕ) < j then x i else 0) ∧ k = j * c)
    (fun _ => 0) 0 ⟨fun i => by simp only [Nat.not_lt_zero, if_false]; try rfl, by simp⟩ (fun i v k ⟨h1, h2⟩ => by
      refine Sat.bnd (hf i) (fun y k1 ⟨hy, hk1⟩ => Sat.ret ⟨fun i' => ?_, ?_⟩)
      · subst hy
        by_cases h : i' = i
        · subst h; simp
        · rw [Function.update_of_ne h, h1]
          have : (i' : ℕ) ≠ i := fun e => h (Fin.ext e)
          split_ifs <;> first | rfl | omega
      · subst h2 hk1; ring)
  refine h.mono (fun v k ⟨h1, h2⟩ => ⟨funext fun i => by simpa [i.isLt] using h1 i, by
    simpa using h2⟩)

theorem sat_matrix {n : ℕ} (f : Fin n → Fin n → Calc ℝ) (X : Matrix (Fin n) (Fin n) ℝ)
    (c : Fin n → ℕ) (hf : ∀ i j, Sat (f i j) (fun y k => y = X i j ∧ k = c i)) :
    Sat (matrix f) (fun A k => A = X ∧ k = ∑ i, n * c i) := by
  unfold matrix
  have h := Sat.foldl_fin (fun A i => do
      let row ← vector (f i)
      pure (Function.update A i row))
    (fun j A k => (∀ i : Fin n, A i = if (i : ℕ) < j then X i else 0) ∧
      k = ∑ i : Fin n, if (i : ℕ) < j then n * c i else 0)
    (fun _ _ => 0) 0 ⟨fun i => by simp only [Nat.not_lt_zero, if_false]; try rfl, by simp⟩ (fun i A k ⟨h1, h2⟩ => by
      refine Sat.bnd (sat_vector (f i) (X i) (c i) (hf i))
        (fun y k1 ⟨hy, hk1⟩ => Sat.ret ⟨fun i' => ?_, ?_⟩)
      · subst hy
        by_cases h : i' = i
        · subst h; simp
        · rw [Function.update_of_ne h, h1]
          have : (i' : ℕ) ≠ i := fun e => h (Fin.ext e)
          split_ifs <;> first | rfl | omega
      · subst h2 hk1
        have e : ∀ i' : Fin n, (if (i' : ℕ) < (i : ℕ) + 1 then n * c i' else 0) =
            (if (i' : ℕ) < i then n * c i' else 0) + (if i' = i then n * c i' else 0) := by
          intro i'
          by_cases h : i' = i
          · subst h; simp
          · have : (i' : ℕ) ≠ i := fun e => h (Fin.ext e)
            simp only [h, if_false, Nat.add_zero]
            split_ifs <;> first | rfl | omega
        rw [Finset.sum_congr rfl (fun i' _ => e i'), Finset.sum_add_distrib,
          Finset.sum_ite_eq']
        simp)
  refine h.mono (fun A k ⟨h1, h2⟩ => ⟨funext fun i => by simpa [i.isLt] using h1 i, by
    rw [Nat.zero_add] at h2; rw [h2]; exact Finset.sum_congr rfl (fun i _ => if_pos i.isLt)⟩)

/-! C1: Gauss–Jordan inversion. -/

theorem C1_invert {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    Runs (invert A) A⁻¹ (4 * n ^ 3) := by
  apply Sat.runs
  unfold invert
  refine Sat.bnd (Sat.foldl_fin _
    (fun j (BH : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) k =>
      k = j * (4 * n ^ 2) ∧ BH.1 = BH.2 * A ∧
      (∀ i l : Fin n, (l : ℕ) < j → BH.1 i l = if i = l then 1 else 0) ∧
      (∀ i l : Fin n, j ≤ (i : ℕ) → j ≤ (l : ℕ) → BH.2 i l = if i = l then 1 else 0))
    _ 0 ⟨by simp, by ext i j; show A i j = ∑ l, (if i = l then (1:ℝ) else 0) * A l j; simp, fun _ _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ _ _ => rfl⟩ ?_) ?_
  · rintro kk ⟨B, H⟩ k ⟨hk, hB, hb, hc⟩
    dsimp only at hB hb hc ⊢
    subst hB
    -- the pivot is x^T A x for x = row kk of H
    have hpiv : 0 < (H * A) kk kk := by
      have hx : H kk ≠ 0 := by
        intro h0
        have := congrFun h0 kk
        rw [hc kk kk le_rfl le_rfl, if_pos rfl, Pi.zero_apply] at this
        exact one_ne_zero this
      have hq := hA.dotProduct_mulVec_pos hx
      have hv : Matrix.vecMul (H kk) A = fun j => (H * A) kk j := by
        ext j; simp [Matrix.vecMul, dotProduct, Matrix.mul_apply]
      rw [star_trivial, Matrix.dotProduct_mulVec, hv] at hq
      suffices e : (H * A) kk kk = ∑ l, (H * A) kk l * H kk l by rw [e]; exact hq
      rw [Finset.sum_eq_single kk]
      · rw [hc kk kk le_rfl le_rfl, if_pos rfl, mul_one]
      · intro l _ hl
        have hl' : (l : ℕ) ≠ kk := fun e => hl (Fin.ext e)
        rcases Nat.lt_or_gt_of_ne hl' with h | h
        · rw [hb kk l h, if_neg (Ne.symm hl), zero_mul]
        · rw [hc kk l le_rfl h.le, if_neg (Ne.symm hl), mul_zero]
      · simp
    have hpiv0 : (H * A) kk kk ≠ 0 := hpiv.ne'
    set B := H * A with hBdef
    refine Sat.bnd (sat_vector _ (fun j => B kk j / B kk kk) 2
      (fun j => sat_divide _ _ hpiv0)) (fun rowB k1 ⟨hrB, hk1⟩ => ?_)
    refine Sat.bnd (sat_vector _ (fun j => H kk j / B kk kk) 2
      (fun j => sat_divide _ _ hpiv0)) (fun rowH k2 ⟨hrH, hk2⟩ => ?_)
    subst hrB hrH
    refine Sat.bnd (sat_matrix _
      (fun i j => if i = kk then B kk j / B kk kk else B i j - B i kk * (B kk j / B kk kk))
      (fun i => if i = kk then 0 else 2) (fun i j => ?_)) (fun B' k3 ⟨hB', hk3⟩ => ?_)
    · by_cases h : i = kk
      · simp only [h, if_true]; exact Sat.ret ⟨rfl, rfl⟩
      · simp only [h, if_false]
        exact Sat.bndE (sat_mul _ _) (sat_sub _ _)
    refine Sat.bnd (sat_matrix _
      (fun i j => if i = kk then H kk j / B kk kk else H i j - B i kk * (H kk j / B kk kk))
      (fun i => if i = kk then 0 else 2) (fun i j => ?_)) (fun H' k4 ⟨hH', hk4⟩ => ?_)
    · by_cases h : i = kk
      · simp only [h, if_true]; exact Sat.ret ⟨rfl, rfl⟩
      · simp only [h, if_false]
        exact Sat.bndE (sat_mul _ _) (sat_sub _ _)
    subst hB' hH'
    refine Sat.ret ⟨?_, ?_, ?_, ?_⟩
    · -- cost
      have hS : (∑ i : Fin n, n * (if i = kk then 0 else 2)) + 2 * n = 2 * n * n := by
        have e2 : ∀ i : Fin n, n * (if i = kk then 0 else 2) + (if i = kk then n * 2 else 0)
            = n * 2 := by
          intro i; split_ifs <;> simp
        have := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => e2 i)
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq'] at this
        simp only [Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul] at this
        linarith
      subst hk hk1 hk2 hk3 hk4
      simp only [Nat.add_zero]
      nlinarith [hS]
    · -- B' = H' * A
      ext i j
      show (if i = kk then B kk j / B kk kk else B i j - B i kk * (B kk j / B kk kk)) =
        ∑ l, (if i = kk then H kk l / B kk kk else H i l - B i kk * (H kk l / B kk kk)) * A l j
      by_cases h : i = kk
      · simp only [h, if_true]
        have e : ∀ l, H kk l / B kk kk * A l j = H kk l * A l j / B kk kk := fun l => by ring
        rw [Finset.sum_congr rfl (fun l _ => e l), ← Finset.sum_div]
        rfl
      · simp only [h, if_false]
        have e : ∀ l, (H i l - B i kk * (H kk l / B kk kk)) * A l j =
            H i l * A l j - B i kk / B kk kk * (H kk l * A l j) := fun l => by ring
        rw [Finset.sum_congr rfl (fun l _ => e l), Finset.sum_sub_distrib, ← Finset.mul_sum]
        show B i j - B i kk * (B kk j / B kk kk) = B i j - B i kk / B kk kk * B kk j
        ring
    · -- columns < kk+1 of B' are unit
      intro i l hl
      have hcol : ∀ l : Fin n, (l : ℕ) < kk → B kk l = 0 := by
        intro l hl
        rw [hb kk l hl, if_neg]
        intro e; rw [e] at hl; exact lt_irrefl _ hl
      by_cases hlk : (l : ℕ) < kk
      · by_cases h : i = kk
        · simp only [h, if_true, hcol l hlk, zero_div]
          rw [if_neg]; intro e; rw [← e] at hlk; exact lt_irrefl _ hlk
        · simp only [h, if_false, hcol l hlk, zero_div, mul_zero, sub_zero]
          exact hb i l hlk
      · have hlk' : l = kk := Fin.ext (by omega)
        subst hlk'
        by_cases h : i = l
        · subst h; simp [hpiv0]
        · simp only [h, if_false, div_self hpiv0, mul_one, sub_self]
    · -- H' rows/cols >= kk+1 are unit
      intro i l hi hl
      have hik : i ≠ kk := fun e => by rw [e] at hi; omega
      have hlk : l ≠ kk := fun e => by rw [e] at hl; omega
      simp only [hik, if_false]
      rw [hc i l (by omega) (by omega), hc kk l le_rfl (by omega), if_neg (Ne.symm hlk),
        zero_div, mul_zero, sub_zero]
  · rintro ⟨B, H⟩ k ⟨hk, hB, hb, _⟩
    dsimp only at hB hb ⊢
    refine Sat.ret ⟨?_, ?_⟩
    · have h1 : H * A = 1 := by
        rw [← hB]; ext i l; rw [hb i l l.isLt, Matrix.one_apply]
      exact (Matrix.inv_eq_left_inv h1).symm
    · nlinarith [hk]

/-! General list folds (fill, sumList over any list). -/

theorem Sat.foldl_list {β ι : Type} (f : β → ι → Calc β) (I : List ι → β → ℕ → Prop)
    (L : List ι)
    (hstep : ∀ (l₁ l₂ : List ι) (i : ι) b k, L = l₁ ++ i :: l₂ → I l₁ b k →
      Sat (f b i) (fun b' k' => I (l₁ ++ [i]) b' (k + k'))) :
    ∀ (l₂ l₁ : List ι) (b : β) (k0 : ℕ), L = l₁ ++ l₂ → I l₁ b k0 →
      Sat (l₂.foldlM f b) (fun b' k' => I L b' (k0 + k'))
  | [], l₁, b, k0, hL, h0 => Sat.ret (by rw [hL, List.append_nil]; simpa using h0)
  | i :: l₂, l₁, b, k0, hL, h0 => by
    rw [List.foldlM_cons]
    refine Sat.bnd (hstep l₁ l₂ i b k0 hL h0) (fun b1 k1 hb1 => ?_)
    refine (Sat.foldl_list f I L hstep l₂ (l₁ ++ [i]) b1 (k0 + k1) (by rw [hL]; simp) hb1).mono
      (fun y k' hy => by rwa [Nat.add_assoc] at hy)

theorem sat_fill {ι : Type} [DecidableEq ι] (L : List ι) (hLc : ∀ i, i ∈ L)
    (f : ι → Calc ℝ) (x : ι → ℝ) (c : ι → ℕ)
    (hf : ∀ i, Sat (f i) (fun y k => y = x i ∧ k = c i)) :
    Sat (fill L f) (fun v k => v = x ∧ k = (L.map c).sum) := by
  unfold fill
  have h := Sat.foldl_list (fun v i => do
      let y ← f i
      pure (Function.update v i y))
    (fun pre v k => (∀ i, v i = if i ∈ pre then x i else 0) ∧ k = (pre.map c).sum) L
    (fun l₁ l₂ i v k _ ⟨h1, h2⟩ => by
      refine Sat.bnd (hf i) (fun y k1 ⟨hy, hk1⟩ => Sat.ret ⟨fun i' => ?_, ?_⟩)
      · subst hy
        by_cases h : i' = i
        · subst h; simp
        · rw [Function.update_of_ne h, h1]; simp [h]
      · subst h2 hk1; simp)
    L [] (fun _ => 0) 0 (by simp) ⟨fun i => by simp, by simp⟩
  exact h.mono (fun v k ⟨h1, h2⟩ => ⟨funext fun i => by simpa [hLc i] using h1 i, by
    simpa using h2⟩)

theorem sat_sumList {ι : Type} (L : List ι) (f : ι → Calc ℝ) (x : ι → ℝ) (c : ℕ)
    (hf : ∀ i, Sat (f i) (fun y k => y = x i ∧ k = c)) :
    Sat (sumList L f) (fun s k => s = (L.map x).sum ∧ k = L.length * (c + 1)) := by
  unfold sumList
  have h := Sat.foldl_list (fun s i => do
      let y ← f i
      add s y)
    (fun pre s k => s = (pre.map x).sum ∧ k = pre.length * (c + 1)) L
    (fun l₁ l₂ i s k _ ⟨h1, h2⟩ => Sat.bnd (hf i) (fun y k1 ⟨hy, hk1⟩ =>
      (sat_add s y).mono (fun z k2 ⟨hz, hk2⟩ => ⟨by rw [hz, h1, hy]; simp, by
        subst h2 hk1 hk2; simp; ring⟩)))
    L [] 0 0 (by simp) ⟨by simp, by simp⟩
  exact h.mono (fun s k ⟨h1, h2⟩ => ⟨h1, by simpa using h2⟩)

theorem list_sum_eq {ι : Type} [Fintype ι] (L : List ι) (hL : L.Nodup) (hLc : ∀ i, i ∈ L)
    (x : ι → ℝ) : (L.map x).sum = ∑ i, x i := by
  classical
  rw [← List.sum_toFinset x hL]
  congr 1
  exact Finset.eq_univ_iff_forall.mpr (fun i => List.mem_toFinset.mpr (hLc i))

theorem sat_dot {n : ℕ} (x y : Fin n → ℝ) :
    Sat (dot x y) (fun z k => z = x ⬝ᵥ y ∧ k = 2 * n) := by
  unfold dot
  refine (sat_sumList _ _ (fun i => x i * y i) 1 (fun i => sat_mul _ _)).mono
    (fun z k ⟨h1, h2⟩ => ⟨?_, by rw [h2, List.length_finRange]; ring⟩)
  rw [h1, list_sum_eq _ (List.nodup_finRange n) (List.mem_finRange)]
  rfl

theorem sat_matvec {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    Sat (matvec H x) (fun z k => z = H *ᵥ x ∧ k = n * (2 * n)) := by
  unfold matvec
  exact (sat_vector _ (fun i => H i ⬝ᵥ x) (2 * n) (fun i => sat_dot _ _)).mono
    (fun z k ⟨h1, h2⟩ => ⟨by rw [h1]; rfl, h2⟩)

/-! C2: the cached Sherman–Morrison update. -/

theorem coeff_facts (d W ε τ α β : ℝ) (hd : 2 ≤ d) (hW : d < W) (hε : ε = W / d - 1)
    (hτ : τ = ε / (W - 1)) (hα : α = 1 + ε / ((d - 1) * (1 + ε)))
    (hβ : β = ε / ((d - 1) * (1 + ε) * (1 + ε))) :
    0 < ε ∧ 0 < τ ∧ 0 < 1 - τ ∧ α * (1 - τ) = 1 ∧ α * τ - β * (1 - τ) - β * τ * W = 0 := by
  have hd0 : 0 < d := by linarith
  have hε0 : 0 < ε := by rw [hε, sub_pos, one_lt_div hd0]; exact hW
  have hWe : W = d * (1 + ε) := by rw [hε]; field_simp; ring
  subst hWe hτ hα hβ
  have hW1 : 0 < d * (1 + ε) - 1 := by nlinarith
  have hd1 : 0 < d - 1 := by linarith
  have h1e : 0 < 1 + ε := by linarith
  refine ⟨hε0, div_pos hε0 hW1, ?_, ?_, ?_⟩
  · rw [one_sub_div hW1.ne']; apply div_pos _ hW1; nlinarith
  · field_simp; ring
  · field_simp; ring

theorem sm_inv {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (x : Fin d → ℝ)
    (a b α β : ℝ) (hα : α * a = 1)
    (hβ : α * b - β * a - β * b * (x ⬝ᵥ (A⁻¹ *ᵥ x)) = 0) :
    (a • A + b • Matrix.vecMulVec x x)⁻¹ =
      α • A⁻¹ - β • Matrix.vecMulVec (A⁻¹ *ᵥ x) (A⁻¹ *ᵥ x) := by
  have hu : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hHA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hu
  have hAH : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hu
  have hT : A.transpose = A := by
    have := hA.1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have huA : (A⁻¹ *ᵥ x) ᵥ* A = x := by
    rw [← Matrix.mulVec_transpose, hT, Matrix.mulVec_mulVec, hAH, Matrix.one_mulVec]
  have hux : (A⁻¹ *ᵥ x) ⬝ᵥ x = x ⬝ᵥ (A⁻¹ *ᵥ x) := dotProduct_comm _ _
  apply Matrix.inv_eq_left_inv
  rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.mul_smul, hHA, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, huA,
    Matrix.vecMulVec_mul_vecMulVec, hux]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply, Matrix.one_apply, Pi.smul_apply]
  split_ifs
  · linear_combination hα + (A⁻¹ *ᵥ x) i * x j * hβ
  · linear_combination (A⁻¹ *ᵥ x) i * x j * hβ

theorem sup_w_eq {ι : Type} [Fintype ι] {d : ℕ} (v : ι → Fin d → ℝ) (p : ι → ℝ) (r : ι)
    (hmax : ∀ j, w v p j ≤ w v p r) : (⨆ j, w v p j) = w v p r := by
  haveI : Nonempty ι := ⟨r⟩
  exact le_antisymm (ciSup_le hmax) (le_ciSup (Set.finite_range _).bddAbove r)

theorem moment_step {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ} (v : ι → Fin d → ℝ)
    (p : ι → ℝ) (r : ι) (τ : ℝ) :
    momentMatrix v ((1 - τ) • p + τ • Pi.single r 1) =
      (1 - τ) • momentMatrix v p + τ • Matrix.vecMulVec (v r) (v r) := by
  simp only [momentMatrix, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul,
    Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum]
  congr 1
  rw [Finset.sum_eq_single r (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
  simp

theorem w_step {d : ℕ} (X H : Matrix (Fin d) (Fin d) ℝ) (u : Fin d → ℝ) (α β : ℝ)
    (hX : X = α • H - β • Matrix.vecMulVec u u) (y : Fin d → ℝ) :
    y ⬝ᵥ (X *ᵥ y) = α * (y ⬝ᵥ (H *ᵥ y)) - β * ((y ⬝ᵥ u) * (y ⬝ᵥ u)) := by
  subst hX
  simp [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul]
  exact Or.inl (Or.inl (dotProduct_comm u y))

theorem C2_update {ι : Type} [Fintype ι] [DecidableEq ι] (L : List ι)
    (hLc : ∀ i, i ∈ L) (d : ℕ) (v : ι → Fin d → ℝ) (s : Registers ι d) (r : ι)
    (hd : 2 ≤ d) (hA : (momentMatrix v s.weights).PosDef)
    (hH : s.inverse = (momentMatrix v s.weights)⁻¹)
    (hs : s.scores = fun j => w v s.weights j)
    (hmax : ∀ j, s.scores j ≤ s.scores r) (hthr : (d : ℝ) < s.scores r) :
    let τ := epsOf v s.weights / (w v s.weights r - 1)
    let p' := (1 - τ) • s.weights + τ • Pi.single r 1
    (momentMatrix v p').PosDef ∧
    Runs (update L v s r) ⟨p', (momentMatrix v p')⁻¹, fun j => w v p' j⟩
      (8 * L.length * d + 6 * d ^ 2 + 20) := by
  set p := s.weights with hpdef
  obtain ⟨W, hWdef⟩ : ∃ W, W = w v p r := ⟨_, rfl⟩
  have hmax' : ∀ j, w v p j ≤ W := fun j => by
    have := hmax j; rw [hs] at this; rw [hWdef]; exact this
  have hthr' : (d : ℝ) < W := by have := hthr; rw [hs] at this; rw [hWdef]; exact this
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < d).ne'
  have heps : epsOf v p = W / d - 1 := by
    rw [epsOf, sup_w_eq v p r (by rw [← hWdef]; exact hmax'), hWdef]
  intro τ p'
  have hτ : τ = (W / d - 1) / (W - 1) := by simp only [τ]; rw [heps, ← hWdef]
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = W / d - 1 := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = 1 + ε / (((d : ℝ) - 1) * (1 + ε)) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = ε / (((d : ℝ) - 1) * (1 + ε) * (1 + ε)) := ⟨_, rfl⟩
  obtain ⟨hε0, hτ0, hτ1, hαc, hβc⟩ := coeff_facts (d : ℝ) W ε τ α β hd2 hthr' hε
    (by rw [hτ, hε]) hα hβ
  obtain ⟨u, hu⟩ : ∃ u, u = (momentMatrix v p)⁻¹ *ᵥ v r := ⟨_, rfl⟩
  have hmm : momentMatrix v p' = (1 - τ) • momentMatrix v p + τ • Matrix.vecMulVec (v r) (v r) :=
    moment_step v p r τ
  have hPD : (momentMatrix v p').PosDef := by
    rw [hmm]
    refine (hA.smul hτ1).add_posSemidef
      ((?_ : (Matrix.vecMulVec (v r) (v r)).PosSemidef).smul hτ0.le)
    simpa using Matrix.posSemidef_vecMulVec_self_star (v r)
  have hWx : v r ⬝ᵥ ((momentMatrix v p)⁻¹ *ᵥ v r) = W := by rw [hWdef]; rfl
  have hinv : (momentMatrix v p')⁻¹ = α • (momentMatrix v p)⁻¹ - β • Matrix.vecMulVec u u := by
    rw [hmm, hu]; exact sm_inv _ hA (v r) (1 - τ) τ α β hαc (by rw [hWx]; exact hβc)
  have hw' : ∀ j, w v p' j = α * w v p j - β * ((v j ⬝ᵥ u) * (v j ⬝ᵥ u)) := fun j =>
    w_step _ _ u α β hinv (v j)
  have hW1 : W - 1 ≠ 0 := by linarith
  have hd1e : ((d : ℝ) - 1) * (1 + ε) ≠ 0 := mul_ne_zero (by linarith) (by linarith)
  refine ⟨hPD, Sat.runs ?_⟩
  unfold update
  refine Sat.bnd (sat_divide _ _ hd0) (fun z k1 ⟨hz, hk1⟩ => ?_)
  refine Sat.bnd (sat_sub _ _) (fun η k2 ⟨hη, hk2⟩ => ?_)
  refine Sat.bnd (sat_sub _ _) (fun wr1 k3 ⟨hwr1, hk3⟩ => ?_)
  have hη' : η = ε := by rw [hη, hz, hs, hε, hWdef]
  have hwr1' : wr1 = W - 1 := by rw [hwr1, hs, hWdef]
  refine Sat.bnd (sat_divide _ _ (by rw [hwr1']; exact hW1)) (fun τc k4 ⟨hτc, hk4⟩ => ?_)
  have hτc' : τc = τ := by rw [hτc, hη', hwr1', hτ, hε]
  refine Sat.bnd (sat_sub _ _) (fun scale k5 ⟨hscale, hk5⟩ => ?_)
  refine Sat.bnd (sat_fill L hLc _ (fun j => if j = r then scale * p j + τc else scale * p j)
    (fun j => if j = r then 2 else 1) (fun j => ?_)) (fun pv k6 ⟨hpv, hk6⟩ => ?_)
  · refine Sat.bnd (sat_mul _ _) (fun y k ⟨hy, hk⟩ => ?_)
    by_cases h : j = r
    · simp only [if_pos h]
      exact (sat_add _ _).mono (fun z' k' ⟨h1, h2⟩ => ⟨by rw [h1, hy], by rw [h2, hk]⟩)
    · simp only [if_neg h]
      exact Sat.ret ⟨hy, by rw [hk]⟩
  refine Sat.bnd (sat_matvec _ _) (fun uc k7 ⟨huc, hk7⟩ => ?_)
  refine Sat.bnd (sat_sub _ _) (fun dm1 k8 ⟨hdm1, hk8⟩ => ?_)
  refine Sat.bnd (sat_add _ _) (fun e1 k9 ⟨he1, hk9⟩ => ?_)
  refine Sat.bnd (sat_mul _ _) (fun den k10 ⟨hden, hk10⟩ => ?_)
  have hden' : den = ((d : ℝ) - 1) * (1 + ε) := by rw [hden, hdm1, he1, hη']
  refine Sat.bnd (sat_divide _ _ (by rw [hden']; exact hd1e)) (fun frac k11 ⟨hfrac, hk11⟩ => ?_)
  refine Sat.bnd (sat_add _ _) (fun αc k12 ⟨hαc', hk12⟩ => ?_)
  refine Sat.bnd (sat_mul _ _) (fun den2 k13 ⟨hden2, hk13⟩ => ?_)
  have hden2' : den2 = ((d : ℝ) - 1) * (1 + ε) * (1 + ε) := by rw [hden2, hden', he1, hη']
  refine Sat.bnd (sat_divide _ _ (by rw [hden2']; exact mul_ne_zero hd1e (by linarith)))
    (fun βc k14 ⟨hβc', hk14⟩ => ?_)
  have hαe : αc = α := by rw [hαc', hfrac, hη', hden', hα]
  have hβe : βc = β := by rw [hβc', hη', hden2', hβ]
  refine Sat.bnd (sat_matrix _
    (fun i k => αc * s.inverse i k - βc * (uc i * uc k)) (fun _ => 4)
    (fun i k => ?_)) (fun Hv k15 ⟨hHv, hk15⟩ => ?_)
  · exact (Sat.bndE (sat_mul _ _) (Sat.bndE (sat_mul _ _) (Sat.bndE (sat_mul _ _)
      (sat_sub _ _)))).mono (fun _ _ ⟨h1, h2⟩ => ⟨h1, by rw [h2]⟩)
  refine Sat.bnd (sat_fill L hLc _
    (fun j => αc * s.scores j - βc * ((v j ⬝ᵥ uc) * (v j ⬝ᵥ uc))) (fun _ => 2 * d + 4)
    (fun j => ?_)) (fun wv k16 ⟨hwv, hk16⟩ => ?_)
  · exact (Sat.bndE (sat_dot _ _) (Sat.bndE (sat_mul _ _) (Sat.bndE (sat_mul _ _)
      (Sat.bndE (sat_mul _ _) (sat_sub _ _))))).mono (fun _ _ ⟨h1, h2⟩ => ⟨h1, by rw [h2]⟩)
  refine Sat.ret ⟨?_, ?_⟩
  · subst hpv hHv hwv
    have huc' : uc = u := by rw [huc, hH, hu]
    rw [hαe, hβe, huc', hτc', hscale, hτc']
    show Registers.mk _ _ _ = Registers.mk _ _ _
    congr 1
    · funext j
      simp only [p', Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      split_ifs <;> ring
    · rw [hinv, hH]; ext i k
      simp [Matrix.vecMulVec_apply]
    · funext j; rw [hw' j, hs]
  · have hf1 : (L.map (fun j => if j = r then 2 else 1)).sum ≤ L.length * 2 := by
      have := List.sum_le_card_nsmul (L.map (fun j => if j = r then 2 else 1)) 2
        (fun x hx => by
          obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
          split_ifs <;> norm_num)
      simpa using this
    have hf2 : (L.map (fun _ => 2 * d + 4)).sum = L.length * (2 * d + 4) := by simp
    have hs15 : (∑ _i : Fin d, d * 4) = d * (d * 4) := by simp
    rw [hf2] at hk16
    rw [hs15] at hk15
    subst hk1 hk2 hk3 hk4 hk5 hk7 hk8 hk9 hk10 hk11 hk12 hk13 hk14 hk15 hk16
    subst hk6
    clear * - hf1 hd
    have : 2 * L.length ≤ L.length * d := Nat.mul_comm 2 _ ▸ Nat.mul_le_mul_left _ hd
    nlinarith [hf1, this]

end KH671

namespace KH671

open KhachiyanRounding.BCD
open scoped Matrix
open KhachiyanRound.BCD (momentMatrix SF w IsRelaxedOpt epsOf IsBCDRun liftPts aggr
  blockMatrix lemma5Ellipsoid)

/-! S6 glue: child statements as hypotheses. -/

def C1P : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), A.PosDef → Runs (invert A) A⁻¹ (4 * n ^ 3)

noncomputable def nxt {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ} (v : ι → Fin d → ℝ)
    (p : ι → ℝ) (r : ι) : ι → ℝ :=
  (1 - epsOf v p / (w v p r - 1)) • p + (epsOf v p / (w v p r - 1)) • Pi.single r 1

def C2P : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (L : List ι), (∀ i, i ∈ L) →
    ∀ (d : ℕ) (v : ι → Fin d → ℝ) (s : Registers ι d) (r : ι),
    2 ≤ d → (momentMatrix v s.weights).PosDef → s.inverse = (momentMatrix v s.weights)⁻¹ →
    s.scores = (fun j => w v s.weights j) → (∀ j, s.scores j ≤ s.scores r) →
    (d : ℝ) < s.scores r →
    Runs (update L v s r) ⟨nxt v s.weights r, (momentMatrix v (nxt v s.weights r))⁻¹,
      fun j => w v (nxt v s.weights r) j⟩ (8 * L.length * d + 6 * d ^ 2 + 20)

def C3P : Prop :=
  (∃ C0 : ℝ, 0 < C0 ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ)
    (v : ι → Fin d → ℝ) (p : ℕ → ι → ℝ) (δ : ℝ), 2 ≤ d → 3 ≤ Fintype.card ι → 0 < δ →
    (momentMatrix v (fun _ => 1 / (Fintype.card ι : ℝ))).PosDef → IsBCDRun v p →
    ∀ N : ℕ, (∀ k < N, ¬ IsRelaxedOpt v (p k) δ) →
      (N : ℝ) ≤ C0 * d * (1 / δ + Real.log d + Real.log (Real.log (Fintype.card ι)) + 1)) ∧
  (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ℕ), 2 ≤ d → ∀ (v : ι → Fin d → ℝ)
    (p : ℕ → ι → ℝ), 0 < Fintype.card ι →
    (momentMatrix v (fun _ => 1 / (Fintype.card ι : ℝ))).PosDef → IsBCDRun v p →
    ∀ k, p k ∈ stdSimplex ℝ ι ∧ (momentMatrix v (p k)).PosDef)

def C4P : Prop :=
  ∀ (n m : ℕ) (a : Fin m → Fin n → ℝ) (q : Fin m ⊕ Fin m → ℝ) (ε : ℝ),
    1 ≤ n → 0 < ε → q ∈ SF (liftPts a) →
    IsRelaxedOpt (liftPts a) q ((n : ℝ) * ε / (n + 1 : ℕ)) →
    aggr q ∈ stdSimplex ℝ (Fin m) ∧ (blockMatrix a (aggr q)).PosDef ∧
    (covariance a (aggr q)).PosDef ∧
    (((1 + ε) * (n : ℝ)) • covariance a (aggr q)).PosDef ∧
    LinearOptimization.ellipsoid (∑ j, aggr q j • a j)
        (((1 + ε) * (n : ℝ)) • covariance a (aggr q)) = lemma5Ellipsoid a (aggr q) ε ∧
    Rounds a (∑ j, aggr q j • a j) (((1 + ε) * (n : ℝ)) • covariance a (aggr q))
      ((1 + ε) * (n : ℝ))

def C5P : Prop :=
  ∀ (n m : ℕ) (a : Fin m → Fin n → ℝ), 1 ≤ n → affineSpan ℝ (Set.range a) = ⊤ →
    n + 1 ≤ m ∧
    (momentMatrix (liftPts a) (fun _ => 1 / ((2 * m : ℕ) : ℝ))).PosDef ∧
    ∀ q : Fin m ⊕ Fin m → ℝ, ∑ j, aggr q j = 1 →
      momentMatrix (liftPts a) q = blockMatrix a (aggr q)

/-! Generic program lemmas. -/

theorem runs_sat {α : Type} {P : Calc α} {x : α} {K : ℕ} (h : Runs P x K) :
    Sat P (fun z k => z = x ∧ k ≤ K) := by
  obtain ⟨k, hk, hP⟩ := h
  exact ⟨x, k, ⟨rfl, hk⟩, hP⟩

theorem card_eq {ι : Type} [Fintype ι] [DecidableEq ι] (L : List ι) (hL : L.Nodup)
    (hLc : ∀ i, i ∈ L) : L.length = Fintype.card ι := by
  rw [← List.toFinset_card_of_nodup hL, ← Finset.card_univ]
  congr 1
  exact Finset.eq_univ_iff_forall.2 (fun i => List.mem_toFinset.2 (hLc i))

theorem sat_maximum {ι : Type} (r0 : ι) (tail : List ι) (wf : ι → ℝ) :
    Sat (maximum (r0 :: tail) wf)
      (fun z k => (∀ j ∈ r0 :: tail, wf j ≤ wf z) ∧ k = tail.length) := by
  simp only [maximum]
  have key := Sat.foldl_list
    (fun best j => do
      let keep ← le (wf j) (wf best)
      pure (if keep then best else j))
    (fun l₁ b k => (∀ j ∈ r0 :: l₁, wf j ≤ wf b) ∧ k = l₁.length) tail ?_ tail [] r0 0
    (by simp) (by simp)
  · exact key.mono (fun z k ⟨h1, h2⟩ => ⟨h1, by simpa using h2⟩)
  · intro l₁ l₂ i b k _ ⟨hb, hk⟩
    refine Sat.bnd (sat_le (wf i) (wf b)) (fun z k1 ⟨hz, hk1⟩ => Sat.ret ⟨?_, ?_⟩)
    · intro j hj
      have hj' : j ∈ r0 :: l₁ ∨ j = i := by
        simp only [List.mem_cons, List.mem_append] at hj ⊢
        tauto
      cases z with
      | true =>
        have hib : wf i ≤ wf b := hz.1 rfl
        simp only [if_true]
        rcases hj' with h | h
        · exact hb j h
        · rw [h]; exact hib
      | false =>
        have hib : ¬ wf i ≤ wf b := fun h => by simpa using hz.2 h
        simp only [Bool.false_eq_true, if_false]
        rcases hj' with h | h
        · exact (hb j h).trans (le_of_lt (not_le.1 hib))
        · rw [h]
    · simp [hk, hk1]

noncomputable def selr {ι : Type} (r0 : ι) (tail : List ι) (wf : ι → ℝ) : ι :=
  Classical.choose (sat_maximum r0 tail wf)

theorem selr_spec {ι : Type} (r0 : ι) (tail : List ι) (wf : ι → ℝ) :
    Sat (maximum (r0 :: tail) wf) (fun z k => z = selr r0 tail wf ∧ k = tail.length) ∧
    ∀ j ∈ r0 :: tail, wf j ≤ wf (selr r0 tail wf) := by
  obtain ⟨k, ⟨h1, h2⟩, h3⟩ := Classical.choose_spec (sat_maximum r0 tail wf)
  exact ⟨⟨_, k, ⟨rfl, h2⟩, h3⟩, h1⟩

noncomputable def runP {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (v : ι → Fin d → ℝ) (r0 : ι) (tail : List ι) : ℕ → ι → ℝ
  | 0 => fun _ => 1 / (Fintype.card ι : ℝ)
  | k + 1 => nxt v (runP v r0 tail k) (selr r0 tail (w v (runP v r0 tail k)))

noncomputable def regs {ι : Type} [Fintype ι] {d : ℕ} (v : ι → Fin d → ℝ) (p : ι → ℝ) :
    Registers ι d :=
  ⟨p, (momentMatrix v p)⁻¹, fun j => w v p j⟩

theorem runP_isBCD {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ} (v : ι → Fin d → ℝ)
    (r0 : ι) (tail : List ι) (hLc : ∀ i, i ∈ r0 :: tail) : IsBCDRun v (runP v r0 tail) :=
  ⟨rfl, fun k => ⟨selr r0 tail (w v (runP v r0 tail k)),
    fun j => (selr_spec r0 tail _).2 j (hLc j), rfl⟩⟩

theorem sat_moment {ι : Type} [Fintype ι] {d : ℕ} (L : List ι) (hL : L.Nodup)
    (hLc : ∀ i, i ∈ L) (v : ι → Fin d → ℝ) (p : ι → ℝ) :
    Sat (moment L v p) (fun A k => A = momentMatrix v p ∧ k = d * (d * (L.length * 3))) := by
  unfold moment
  refine (sat_matrix _ (momentMatrix v p) (fun _ => L.length * 3) (fun i k => ?_)).mono
    (fun A k ⟨h1, h2⟩ => ⟨h1, by
      rw [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]⟩)
  refine (sat_sumList L _ (fun j => p j * v j i * v j k) 2
    (fun j => (Sat.bndE (sat_mul (p j) (v j i)) (sat_mul (p j * v j i) (v j k))).mono
      (fun z c h => ⟨h.1, by rw [h.2]⟩))).mono (fun z c ⟨h1, h2⟩ => ⟨?_, h2⟩)
  rw [h1, list_sum_eq L hL hLc]
  simp only [momentMatrix, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    smul_eq_mul, mul_assoc]

theorem sat_init {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ} (hC1 : C1P) (L : List ι)
    (hL : L.Nodup) (hLc : ∀ i, i ∈ L) (hne : 0 < L.length) (v : ι → Fin d → ℝ)
    (hPD : (momentMatrix v (fun _ => 1 / (L.length : ℝ))).PosDef) :
    Sat (initRegisters L v) (fun s k => s = regs v (fun _ => 1 / (L.length : ℝ)) ∧
      k ≤ 2 + d * (d * (L.length * 3)) + 4 * d ^ 3 + L.length * (d * (2 * d) + 2 * d)) := by
  have hlen : (L.length : ℝ) ≠ 0 := by exact_mod_cast hne.ne'
  unfold initRegisters
  refine Sat.bnd (sat_divide 1 _ hlen) (fun q k1 ⟨hq, hk1⟩ => ?_)
  subst hq
  refine Sat.bnd (sat_moment L hL hLc v _) (fun A k2 ⟨hA, hk2⟩ => ?_)
  subst hA
  refine Sat.bnd (runs_sat (hC1 d _ hPD)) (fun H k3 ⟨hH, hk3⟩ => ?_)
  subst hH
  refine Sat.bnd (sat_fill L hLc _ (fun j => v j ⬝ᵥ ((momentMatrix v
      (fun _ => 1 / (L.length : ℝ)))⁻¹ *ᵥ v j)) (fun _ => d * (2 * d) + 2 * d)
      (fun j => Sat.bndE (sat_matvec _ (v j)) (sat_dot _ _)))
    (fun z k4 ⟨hz, hk4⟩ => Sat.ret ⟨?_, ?_⟩)
  · subst hz; rfl
  · rw [hk4, List.map_const', List.sum_replicate, smul_eq_mul] ; omega

theorem sat_descend {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ} (hC2 : C2P) (hd : 2 ≤ d)
    (r0 : ι) (tail : List ι) (hLc : ∀ i, i ∈ r0 :: tail) (v : ι → Fin d → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hPD : ∀ k, (momentMatrix v (runP v r0 tail k)).PosDef) :
    ∀ f k, IsRelaxedOpt v (runP v r0 tail (k + f)) δ →
      (∀ j < k + f, ¬ IsRelaxedOpt v (runP v r0 tail j) δ) →
      Sat (descend (r0 :: tail) v ((1 + δ) * d) f (regs v (runP v r0 tail k)))
        (fun z c => z = regs v (runP v r0 tail (k + f)) ∧
          c ≤ (f + 1) * (tail.length + 1) +
            f * (8 * (tail.length + 1) * d + 6 * d ^ 2 + 20)) := by
  intro f
  induction f with
  | zero =>
    intro k hRO _
    rw [descend]
    refine Sat.bnd (selr_spec r0 tail _).1 (fun r k1 ⟨hr, hk1⟩ => ?_)
    subst hr
    refine Sat.bnd (sat_le _ _) (fun z k2 ⟨hz, hk2⟩ => ?_)
    have hz' : z = true := hz.2 (hRO _)
    subst hz'
    rw [if_pos rfl]
    exact Sat.ret ⟨by simp, by simp [hk1, hk2]⟩
  | succ f ih =>
    intro k hRO hnot
    rw [descend]
    refine Sat.bnd (selr_spec r0 tail _).1 (fun r k1 ⟨hr, hk1⟩ => ?_)
    subst hr
    have hmax : ∀ j, w v (runP v r0 tail k) j ≤
        w v (runP v r0 tail k) (selr r0 tail (regs v (runP v r0 tail k)).scores) :=
      fun j => (selr_spec r0 tail _).2 j (hLc j)
    have hk_not : ¬ IsRelaxedOpt v (runP v r0 tail k) δ := hnot k (by omega)
    have hgt : (1 + δ) * d <
        w v (runP v r0 tail k) (selr r0 tail (regs v (runP v r0 tail k)).scores) := by
      by_contra h
      exact hk_not (fun j => (hmax j).trans (not_lt.1 h))
    refine Sat.bnd (sat_le _ _) (fun z k2 ⟨hz, hk2⟩ => ?_)
    have hz' : z = false := by
      cases z
      · rfl
      · exact absurd (hz.1 rfl) (not_le.2 hgt)
    subst hz'
    rw [if_neg (by simp)]
    have hdpos : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hupd := runs_sat (hC2 ι (r0 :: tail) hLc d v (regs v (runP v r0 tail k))
      (selr r0 tail (regs v (runP v r0 tail k)).scores) hd (hPD k) rfl rfl hmax
      (by show (d : ℝ) < w v (runP v r0 tail k) _; nlinarith))
    refine Sat.bnd hupd (fun s' k3 ⟨hs', hk3⟩ => ?_)
    subst hs'
    have hih := ih (k + 1) (by rw [show k + 1 + f = k + (f + 1) by omega]; exact hRO)
      (fun j hj => hnot j (by omega))
    rw [show k + 1 + f = k + (f + 1) by omega] at hih
    refine hih.mono (fun z c ⟨h1, h2⟩ => ⟨h1, ?_⟩)
    simp only [List.length_cons] at hk3
    nlinarith

theorem sat_core {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ} (hC1 : C1P) (hC2 : C2P)
    (hd : 2 ≤ d) (r0 : ι) (tail : List ι) (hnd : (r0 :: tail).Nodup)
    (hLc : ∀ i, i ∈ r0 :: tail) (v : ι → Fin d → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hPD : ∀ k, (momentMatrix v (runP v r0 tail k)).PosDef) (N : ℕ)
    (hN : IsRelaxedOpt v (runP v r0 tail N) δ)
    (hmin : ∀ j < N, ¬ IsRelaxedOpt v (runP v r0 tail j) δ) :
    Sat (core (r0 :: tail) v δ N) (fun s c => s = regs v (runP v r0 tail N) ∧
      c ≤ 2 + d * (d * ((tail.length + 1) * 3)) + 4 * d ^ 3 +
        (tail.length + 1) * (d * (2 * d) + 2 * d) + 2 +
        ((N + 1) * (tail.length + 1) + N * (8 * (tail.length + 1) * d + 6 * d ^ 2 + 20))) := by
  have hcard : (((r0 :: tail).length : ℕ) : ℝ) = (Fintype.card ι : ℝ) := by
    rw [card_eq _ hnd hLc]
  have hinit := sat_init hC1 (r0 :: tail) hnd hLc (by simp) v (by rw [hcard]; exact hPD 0)
  rw [hcard] at hinit
  unfold core
  refine Sat.bnd hinit (fun s k1 ⟨hs, hk1⟩ => ?_)
  subst hs
  refine Sat.bnd (sat_add _ _) (fun e1 k2 ⟨he1, hk2⟩ => ?_)
  subst he1
  refine Sat.bnd (sat_mul _ _) (fun th k3 ⟨hth, hk3⟩ => ?_)
  subst hth
  have hdesc := sat_descend hC2 hd r0 tail hLc v δ hδ hPD N 0 (by simpa using hN)
    (by simpa using hmin)
  simp only [Nat.zero_add] at hdesc
  refine hdesc.mono (fun z c ⟨h1, h2⟩ => ⟨h1, ?_⟩)
  simp only [List.length_cons] at hk1
  omega

/-! Specific lemmas for the lifted program. -/

theorem liftOrder_nodup (m : ℕ) : (liftOrder m).Nodup := by
  unfold liftOrder
  refine List.Nodup.append ((List.nodup_finRange m).map Sum.inl_injective)
    ((List.nodup_finRange m).map Sum.inr_injective) ?_
  intro x h1 h2
  simp only [List.mem_map] at h1 h2
  obtain ⟨i, -, rfl⟩ := h1
  obtain ⟨j, -, h⟩ := h2
  cases h

theorem liftOrder_complete (m : ℕ) : ∀ x, x ∈ liftOrder m := by
  intro x; cases x <;> simp [liftOrder]

theorem liftOrder_length (m : ℕ) : (liftOrder m).length = m + m := by simp [liftOrder]

theorem sat_formLift {m n : ℕ} (a : Fin m → Fin n → ℝ) :
    Sat (formLift a) (fun z k => z = liftPts a ∧ k = m * (n + 1)) := by
  simp only [formLift]
  refine Sat.bnd (Sat.foldl_fin _
    (fun i (V : Fin m → Fin (n + 1) → ℝ) k =>
      (∀ j : Fin m, (j : ℕ) < i → V j = -Fin.snoc (α := fun _ => ℝ) (a j) 1) ∧ k = i * (n + 1))
    (fun _ _ => 0) 0 ⟨fun j hj => absurd hj (Nat.not_lt_zero _), (Nat.zero_mul _).symm⟩ ?_)
    (fun V k ⟨hV, hk⟩ => Sat.ret ⟨?_, by simpa using hk⟩)
  · intro i V k ⟨hV, hk⟩
    refine Sat.bnd (sat_vector _ (-Fin.snoc (α := fun _ => ℝ) (a i) 1) 1
      (fun t => (sat_sub _ _).mono (fun z c ⟨h1, h2⟩ => ⟨by rw [h1]; simp, h2⟩)))
      (fun row k1 ⟨hrow, hk1⟩ => Sat.ret ⟨?_, ?_⟩)
    · intro j hj
      by_cases hji : j = i
      · subst hji; simp [hrow]
      · rw [Function.update_of_ne hji]
        exact hV j (by have : (j : ℕ) ≠ i := fun h => hji (Fin.ext h); omega)
    · rw [hk, hk1]; ring
  · funext x
    cases x with
    | inl j => rfl
    | inr j => simp [liftPts, hV j j.isLt]

theorem cost_arith (n m N T k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 : ℕ) (hn : 1 ≤ n) (hmn : n + 1 ≤ m)
    (hT : T + 1 = m + m) (h1 : k1 = m * (n + 1)) (h2 : k2 = 1) (h3 : k3 = 2)
    (h4 : k4 ≤ 2 + (n + 1) * ((n + 1) * ((T + 1) * 3)) + 4 * (n + 1) ^ 3 +
        (T + 1) * ((n + 1) * (2 * (n + 1)) + 2 * (n + 1)) + 2 +
        ((N + 1) * (T + 1) + N * (8 * (T + 1) * (n + 1) + 6 * (n + 1) ^ 2 + 20)))
    (h5 : k5 = m * 1) (h6 : k6 = n * (m * (1 + 1))) (h7 : k7 = n * (n * (m * 3)))
    (h8 : k8 = 1) (h9 : k9 = 1) (h10 : k10 = n * (n * 3)) :
    k1 + (k2 + (k3 + (k4 + (k5 + (k6 + (k7 + (k8 + (k9 + (k10 + 0))))))))) ≤
      35 * (m + m) * (n + 1) * (N + 1) + 30 * (m + m) * (n + 1) ^ 2 := by
  rw [hT] at h4
  obtain ⟨a, rfl⟩ : ∃ a, n = a + 1 := ⟨n - 1, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, m = a + 2 + e := ⟨m - (a + 2), by omega⟩
  subst h1 h2 h3 h5 h6 h7 h8 h9 h10
  nlinarith [h4, Nat.zero_le (a * e * N), Nat.zero_le (a * e), Nat.zero_le (a * N),
    Nat.zero_le (e * N), Nat.zero_le (a ^ 2 * N), Nat.zero_le (a ^ 2 * e), Nat.zero_le (a ^ 3),
    Nat.zero_le (a ^ 2)]

theorem bk_pos (n m : ℕ) (ε : ℝ) (hn : 1 ≤ n) (hm : 2 ≤ m) (hε : 0 < ε) :
    1 / 2 ≤ ((n + 1 : ℕ) : ℝ) / ((n : ℝ) * ε) + Real.log (n + 1 : ℕ) +
      Real.log (Real.log (2 * m : ℕ)) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have h1 : 0 ≤ ((n + 1 : ℕ) : ℝ) / ((n : ℝ) * ε) := by positivity
  have hl2 := Real.log_two_gt_d9
  have h2 : Real.log 2 ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) (by push_cast; linarith)
  have h3 : 0 ≤ Real.log (Real.log ((2 * m : ℕ) : ℝ)) := by
    apply Real.log_nonneg
    have h4 : Real.log 4 ≤ Real.log ((2 * m : ℕ) : ℝ) :=
      Real.log_le_log (by norm_num) (by push_cast; linarith)
    have h5 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  linarith

theorem budget_real (n m N0 k : ℕ) (C0 ε : ℝ) (hC0 : 0 < C0) (hn : 1 ≤ n) (hm : 2 ≤ m)
    (hε : 0 < ε)
    (hk : k ≤ 35 * (m + m) * (n + 1) * (N0 + 1) + 30 * (m + m) * (n + 1) ^ 2)
    (hN : (N0 : ℝ) ≤ C0 * ((n + 1 : ℕ) : ℝ) * (1 / ((n : ℝ) * ε / ((n + 1 : ℕ) : ℝ)) +
      Real.log ((n + 1 : ℕ) : ℝ) + Real.log (Real.log ((2 * m : ℕ) : ℝ)) + 1)) :
    (k : ℝ) ≤ (105 * C0 + 130) * liftedBudget n m ε := by
  have hBk := bk_pos n m ε hn hm hε
  rw [one_div_div] at hN
  have hk' := (Nat.cast_le (α := ℝ)).2 hk
  unfold liftedBudget
  generalize ((n + 1 : ℕ) : ℝ) / ((n : ℝ) * ε) + Real.log ((n + 1 : ℕ) : ℝ) +
    Real.log (Real.log ((2 * m : ℕ) : ℝ)) = Bk at hN hBk ⊢
  push_cast at hN hk' ⊢
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) ≤ N0 := Nat.cast_nonneg _
  have e0 := mul_le_mul_of_nonneg_left (show Bk + 1 ≤ 3 * Bk by linarith)
    (by positivity : (0 : ℝ) ≤ C0 * (n + 1))
  have e1 : (N0 : ℝ) + 1 ≤ 3 * C0 * (n + 1) * Bk + 2 * Bk := by linarith
  have e2 := mul_le_mul_of_nonneg_left e1 (by positivity : (0 : ℝ) ≤ 35 * (m + m) * (n + 1))
  have e3 := mul_le_mul_of_nonneg_left (show (n : ℝ) + 1 ≤ (n + 1) ^ 2 by nlinarith)
    (by positivity : (0 : ℝ) ≤ 2 * m)
  have e3' := mul_le_mul_of_nonneg_right e3 (by linarith : (0 : ℝ) ≤ Bk)
  have e4 := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 2 * Bk by linarith)
    (by positivity : (0 : ℝ) ≤ 2 * m * (n + 1) ^ 2)
  nlinarith

theorem budget_K (n m : ℕ) (ε : ℝ) (hn : 1 ≤ n) (hm : 3 ≤ m) (hε : 0 < ε) :
    liftedBudget n m ε ≤ 160 * printedBudget n m ε := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn'
  have hlogm3 : Real.log 3 ≤ Real.log m := Real.log_le_log (by norm_num) hm'
  have he := Real.exp_one_lt_d9
  have hl3 : (1.09 : ℝ) ≤ Real.log 3 := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 / Real.exp 1 by positivity)
    rw [Real.log_div (by norm_num) (Real.exp_pos 1).ne', Real.log_exp, inv_div] at h
    linarith
  have hlm : (1.09 : ℝ) ≤ Real.log m := by linarith
  have hll : (0.08 : ℝ) ≤ Real.log (Real.log m) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < Real.log m by linarith)
    have : (Real.log m)⁻¹ ≤ 1 / 1.09 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hlm
    linarith
  have hA : Real.log ((n : ℝ) + 1) ≤ Real.log 2 + Real.log n := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hB : Real.log (Real.log (2 * (m : ℝ))) ≤ Real.log 2 + Real.log (Real.log m) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    have h2m : Real.log (2 * (m : ℝ)) = Real.log 2 + Real.log m :=
      Real.log_mul (by norm_num) (by positivity)
    exact Real.log_le_log (by rw [h2m]; linarith) (by rw [h2m]; linarith)
  have hB0 : 0 ≤ Real.log (Real.log (2 * (m : ℝ))) := by
    apply Real.log_nonneg
    have h2m : Real.log (2 * (m : ℝ)) = Real.log 2 + Real.log m :=
      Real.log_mul (by norm_num) (by positivity)
    rw [h2m]; linarith
  have hC : ((n : ℝ) + 1) / ((n : ℝ) * ε) ≤ 2 * (1 / ε) := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) hε]; nlinarith
  have hC0 : 0 ≤ ((n : ℝ) + 1) / ((n : ℝ) * ε) := by positivity
  have hA0 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hinv : 0 < 1 / ε := by positivity
  unfold liftedBudget printedBudget
  push_cast
  have hBkPb : ((n : ℝ) + 1) / ((n : ℝ) * ε) + Real.log ((n : ℝ) + 1) +
      Real.log (Real.log (2 * (m : ℝ))) ≤
      20 * (1 / ε + Real.log n + Real.log (Real.log m)) := by linarith
  have hBk0 : 0 ≤ ((n : ℝ) + 1) / ((n : ℝ) * ε) + Real.log ((n : ℝ) + 1) +
      Real.log (Real.log (2 * (m : ℝ))) := by linarith
  have h8 : 2 * (m : ℝ) * ((n : ℝ) + 1) ^ 2 ≤ 8 * m * n ^ 2 := by
    have : ((n : ℝ) + 1) ^ 2 ≤ 4 * n ^ 2 := by nlinarith
    nlinarith
  have H1 := mul_le_mul_of_nonneg_right h8 hBk0
  have H2 := mul_le_mul_of_nonneg_left hBkPb (by positivity : (0 : ℝ) ≤ 8 * m * n ^ 2)
  nlinarith

theorem exists_of_bounded {P : ℕ → Prop} {B : ℝ}
    (h : ∀ N : ℕ, (∀ k < N, ¬ P k) → (N : ℝ) ≤ B) : ∃ N, P N := by
  by_contra hne
  have h1 := h (⌈B⌉₊ + 1) (fun k _ => not_exists.1 hne k)
  have h2 := Nat.le_ceil B
  push_cast at h1
  linarith

theorem glue (hC1 : C1P) (hC2 : C2P) (hC3 : C3P) (hC4 : C4P) (hC5 : C5P) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (n m : ℕ) (a : Fin m → Fin n → ℝ), 1 ≤ n →
        affineSpan ℝ (Set.range a) = ⊤ → ∀ ε : ℝ, 0 < ε →
        ∃ (fuel : ℕ) (out : Output (Fin m ⊕ Fin m) (n + 1) n) (cost : ℕ),
          general a ε fuel 0 = some (out, cost) ∧
          EndpointCorrect (KhachiyanRound.BCD.liftPts a) out.endpoint
            ((n : ℝ) * ε / (n + 1 : ℕ)) ∧
          (let p := KhachiyanRound.BCD.aggr out.endpoint.weights
           p ∈ stdSimplex ℝ (Fin m) ∧
           (KhachiyanRound.BCD.blockMatrix a p).PosDef ∧
           (covariance a p).PosDef ∧
           out.center = ∑ j, p j • a j ∧
           out.shape = ((1 + ε) * (n : ℝ)) • covariance a p ∧
           out.shape.PosDef ∧
           LinearOptimization.ellipsoid out.center out.shape =
             KhachiyanRound.BCD.lemma5Ellipsoid a p ε) ∧
          Rounds a out.center out.shape ((1 + ε) * (n : ℝ)) ∧
          0 < liftedBudget n m ε ∧
          (cost : ℝ) ≤ C * liftedBudget n m ε ∧
          ((2 ≤ n ∨ 3 ≤ m) →
            liftedBudget n m ε ≤ K * printedBudget n m ε ∧
            (cost : ℝ) ≤ (C * K) * printedBudget n m ε) := by
  obtain ⟨⟨C0, hC0, hcount⟩, hinv⟩ := hC3
  refine ⟨105 * C0 + 130, 160, by positivity, by norm_num, ?_⟩
  intro n m a hn ha ε hε
  obtain ⟨hmn, hPD0, -⟩ := hC5 n m a hn ha
  have hm2 : 2 ≤ m := by omega
  have hnd := liftOrder_nodup m
  have hLc := liftOrder_complete m
  have hlen := liftOrder_length m
  obtain ⟨r0, tail, hL⟩ := List.exists_cons_of_ne_nil (show liftOrder m ≠ [] by
    intro h; rw [h] at hlen; simp at hlen; omega)
  rw [hL] at hnd hLc hlen
  have htl : tail.length + 1 = m + m := by simpa using hlen
  have hcardι : Fintype.card (Fin m ⊕ Fin m) = m + m := by simp
  have hcardR : (Fintype.card (Fin m ⊕ Fin m) : ℝ) = ((2 * m : ℕ) : ℝ) := by
    rw [hcardι]; push_cast; ring
  have hPDu : (momentMatrix (liftPts a)
      (fun _ => 1 / (Fintype.card (Fin m ⊕ Fin m) : ℝ))).PosDef := by
    rw [hcardR]; exact hPD0
  have hrun := runP_isBCD (liftPts a) r0 tail hLc
  have hd : 2 ≤ n + 1 := by omega
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
  have hδ : 0 < (n : ℝ) * ε / ((n + 1 : ℕ) : ℝ) := div_pos (mul_pos hnpos hε) (by positivity)
  have hinvk := hinv (Fin m ⊕ Fin m) (n + 1) hd (liftPts a) (runP (liftPts a) r0 tail)
    (by rw [hcardι]; omega) hPDu hrun
  have hcnt := hcount (Fin m ⊕ Fin m) (n + 1) (liftPts a) (runP (liftPts a) r0 tail) _ hd
    (by rw [hcardι]; omega) hδ hPDu hrun
  have hex := exists_of_bounded hcnt
  classical
  obtain ⟨N0, hN0, hmin⟩ : ∃ N0, IsRelaxedOpt (liftPts a) (runP (liftPts a) r0 tail N0)
      ((n : ℝ) * ε / ((n + 1 : ℕ) : ℝ)) ∧ ∀ j < N0, ¬ IsRelaxedOpt (liftPts a)
      (runP (liftPts a) r0 tail j) ((n : ℝ) * ε / ((n + 1 : ℕ) : ℝ)) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hN0B := hcnt N0 hmin
  rw [hcardR] at hN0B
  have hcore := sat_core hC1 hC2 hd r0 tail hnd hLc (liftPts a) _ hδ (fun k => (hinvk k).2)
    N0 hN0 hmin
  rw [← hL] at hcore
  obtain ⟨q, hq⟩ : ∃ q, q = runP (liftPts a) r0 tail N0 := ⟨_, rfl⟩
  rw [← hq] at hcore hN0
  obtain ⟨hqS, hqPD⟩ := hinvk N0
  rw [← hq] at hqS hqPD
  have hqSF : q ∈ SF (liftPts a) := ⟨hqS, hqPD.det_pos⟩
  have hgen : Sat (general a ε N0) (fun out k => out = ⟨regs (liftPts a) q,
      ∑ j, aggr q j • a j, ((1 + ε) * (n : ℝ)) • covariance a (aggr q)⟩ ∧
      k ≤ 35 * (m + m) * (n + 1) * (N0 + 1) + 30 * (m + m) * (n + 1) ^ 2) := by
    unfold general
    refine Sat.bnd (sat_formLift a) (fun V k1 ⟨hV, hk1⟩ => ?_)
    subst hV
    refine Sat.bnd (sat_mul _ _) (fun ne k2 ⟨hne, hk2⟩ => ?_)
    subst hne
    refine Sat.bnd (sat_divide _ _ (by positivity)) (fun δ' k3 ⟨hδ', hk3⟩ => ?_)
    subst hδ'
    refine Sat.bnd hcore (fun s k4 ⟨hs, hk4⟩ => ?_)
    subst hs
    refine Sat.bnd (sat_vector _ (aggr q) 1 (fun j => sat_add _ _))
      (fun p k5 ⟨hp, hk5⟩ => ?_)
    subst hp
    refine Sat.bnd (sat_vector _ (∑ j, aggr q j • a j) (m * (1 + 1))
      (fun i => (sat_sumList (List.finRange m) _ (fun j => aggr q j * a j i) 1
        (fun j => sat_mul _ _)).mono (fun z c ⟨h1, h2⟩ =>
          ⟨by rw [h1, list_sum_eq _ (List.nodup_finRange m) (List.mem_finRange)]
              simp [Finset.sum_apply],
           by rw [h2, List.length_finRange]⟩)))
      (fun b k6 ⟨hb, hk6⟩ => ?_)
    subst hb
    refine Sat.bnd (sat_moment (List.finRange m) (List.nodup_finRange m) List.mem_finRange
      a (aggr q)) (fun D k7 ⟨hD, hk7⟩ => ?_)
    subst hD
    refine Sat.bnd (sat_add _ _) (fun e1 k8 ⟨he1, hk8⟩ => ?_)
    subst he1
    refine Sat.bnd (sat_mul _ _) (fun t k9 ⟨ht, hk9⟩ => ?_)
    subst ht
    refine Sat.bnd (sat_matrix _ (((1 + ε) * (n : ℝ)) • covariance a (aggr q)) (fun _ => 3)
      (fun i j => ?_)) (fun Q k10 ⟨hQ, hk10⟩ => Sat.ret ⟨by rw [hQ], ?_⟩)
    · refine Sat.bnd (sat_mul _ _) (fun x c1 ⟨hx, hc1⟩ => ?_)
      refine Sat.bnd (sat_sub _ _) (fun y c2 ⟨hy, hc2⟩ => ?_)
      refine (sat_mul _ _).mono (fun z c3 ⟨hz, hc3⟩ => ⟨?_, by omega⟩)
      rw [hz, hy, hx]
      simp [covariance, Matrix.vecMulVec_apply, Finset.sum_apply]
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
        List.length_finRange] at hk10 hk7
      exact cost_arith n m N0 tail.length k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 hn hmn htl hk1 hk2
        hk3 hk4 hk5 hk6 hk7 hk8 hk9 hk10
  obtain ⟨out, k, ⟨hout, hk⟩, hrun0⟩ := hgen
  subst hout
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hC4 n m a q ε hn hε hqSF hN0
  have hbud := budget_real n m N0 k C0 ε hC0 hn hm2 hε hk hN0B
  have hBk := bk_pos n m ε hn hm2 hε
  have hlpos : 0 < liftedBudget n m ε := by
    unfold liftedBudget
    have hM : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * m)
    exact mul_pos (mul_pos hM (by positivity)) (by linarith)
  refine ⟨N0, ⟨regs (liftPts a) q, ∑ j, aggr q j • a j,
    ((1 + ε) * (n : ℝ)) • covariance a (aggr q)⟩, k, by rw [hrun0 0, Nat.zero_add],
    ⟨hqSF, hqPD, rfl, rfl, hN0⟩, ⟨h1, h2, h3, rfl, rfl, h4, h5⟩, h6, hlpos, hbud,
    fun hnm => ?_⟩
  have hm3 : 3 ≤ m := by omega
  have hK := budget_K n m ε hn hm3 hε
  refine ⟨hK, ?_⟩
  have hC : 0 < 105 * C0 + 130 := by positivity
  calc (k : ℝ) ≤ (105 * C0 + 130) * liftedBudget n m ε := hbud
    _ ≤ (105 * C0 + 130) * (160 * printedBudget n m ε) := mul_le_mul_of_nonneg_left hK hC.le
    _ = (105 * C0 + 130) * 160 * printedBudget n m ε := by ring

theorem c1_ok : C1P := fun _ A hA => C1_invert A hA

theorem c2_ok : C2P := fun _ _ _ L hLc d v s r hd hA hH hs hmax hthr =>
  (C2_update L hLc d v s r hd hA hH hs hmax hthr).2

theorem c3_ok : C3P :=
  ⟨KH671C3.C3_gen, fun _ _ _ _ hd v p hM hPD hrun => KH671C3.run_inv hd v p hM hPD hrun⟩

theorem c4_ok : C4P := fun _ _ a q ε hn hε hq hopt => C4_lifted_rounding a q ε hn hε hq hopt

theorem c5_ok : C5P := fun _ _ a _ ha => C5_lift_start a ha

end KH671

open KhachiyanRounding.BCD in
theorem solution :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (n m : ℕ) (a : Fin m → Fin n → ℝ), 1 ≤ n →
        affineSpan ℝ (Set.range a) = ⊤ → ∀ ε : ℝ, 0 < ε →
        ∃ (fuel : ℕ) (out : Output (Fin m ⊕ Fin m) (n + 1) n) (cost : ℕ),
          general a ε fuel 0 = some (out, cost) ∧
          EndpointCorrect (KhachiyanRound.BCD.liftPts a) out.endpoint
            ((n : ℝ) * ε / (n + 1 : ℕ)) ∧
          (let p := KhachiyanRound.BCD.aggr out.endpoint.weights
           p ∈ stdSimplex ℝ (Fin m) ∧
           (KhachiyanRound.BCD.blockMatrix a p).PosDef ∧
           (covariance a p).PosDef ∧
           out.center = ∑ j, p j • a j ∧
           out.shape = ((1 + ε) * (n : ℝ)) • covariance a p ∧
           out.shape.PosDef ∧
           LinearOptimization.ellipsoid out.center out.shape =
             KhachiyanRound.BCD.lemma5Ellipsoid a p ε) ∧
          Rounds a out.center out.shape ((1 + ε) * (n : ℝ)) ∧
          0 < liftedBudget n m ε ∧
          (cost : ℝ) ≤ C * liftedBudget n m ε ∧
          ((2 ≤ n ∨ 3 ≤ m) →
            liftedBudget n m ε ≤ K * printedBudget n m ε ∧
            (cost : ℝ) ≤ (C * K) * printedBudget n m ε) := by
  exact KH671.glue KH671.c1_ok KH671.c2_ok KH671.c3_ok KH671.c4_ok KH671.c5_ok
