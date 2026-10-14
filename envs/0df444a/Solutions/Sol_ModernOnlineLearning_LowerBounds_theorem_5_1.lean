-- Prove2me | solution 1 for ModernOnlineLearning.LowerBounds.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:04:04.33928+00:00
-- url     : https://prove2.me/submissions/a74c24b8-9628-46de-9bba-8e8afb63437b

import Mathlib
import Definitions.Def_ModernOnlineLearning_LowerBounds_Protocol

namespace RRAux_LB51
open Finset

/-- `c j = C(n, j-1)` for `j ≥ 1`, `c 0 = 0`. -/
noncomputable def cc (n j : ℕ) : ℝ := if j = 0 then 0 else (Nat.choose n (j - 1) : ℝ)

lemma ident (n j : ℕ) :
    (Nat.choose (n + 1) j : ℝ) * (2 * (j : ℝ) - (n + 1 : ℝ)) = (n + 1 : ℝ) * (cc n j - cc n (j + 1)) := by
  rcases j with _ | k
  · simp [cc]
  · simp only [cc, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    have h1 : ((n + 1 : ℕ) : ℝ) * (Nat.choose n k : ℝ)
        = (Nat.choose (n + 1) (k + 1) : ℝ) * ((k : ℝ) + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq n k
    by_cases hk : k ≤ n
    · have h2 : (Nat.choose n (k + 1) : ℝ) * ((n : ℝ) + 1)
          = (Nat.choose (n + 1) (k + 1) : ℝ) * ((n : ℝ) - k) := by
        have := Nat.choose_mul_succ_eq n (k + 1)
        have e : n + 1 - (k + 1) = n - k := by omega
        rw [e] at this
        have := congrArg (fun z : ℕ => (z : ℝ)) this
        push_cast [Nat.cast_sub hk] at this
        linarith
      push_cast at h1 ⊢
      nlinarith [h1, h2]
    · have e1 : Nat.choose (n + 1) (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have e2 : Nat.choose n k = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have e3 : Nat.choose n (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [e1, e2, e3]

lemma Qbound (n m : ℕ) (hm : m ≤ n) :
    2 * (n + 1 : ℝ) * (Nat.choose n m : ℝ) ≤
      ∑ j ∈ range (n + 2), (Nat.choose (n + 1) j : ℝ) * |2 * (j : ℝ) - (n + 1 : ℝ)| := by
  have hpt : ∀ j, (Nat.choose (n + 1) j : ℝ) * |2 * (j : ℝ) - (n + 1 : ℝ)|
      = (n + 1 : ℝ) * |cc n j - cc n (j + 1)| := by
    intro j
    have hc : (0 : ℝ) ≤ Nat.choose (n + 1) j := Nat.cast_nonneg _
    rw [← abs_of_nonneg hc, ← abs_mul, ident, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ n + 1)]
  simp_rw [hpt, ← Finset.mul_sum]
  have hsplit := Finset.sum_range_add_sum_Ico (fun j => |cc n j - cc n (j + 1)|)
    (show m + 1 ≤ n + 2 by omega)
  have hA : (Nat.choose n m : ℝ) ≤ ∑ j ∈ range (m + 1), |cc n j - cc n (j + 1)| := by
    refine le_trans ?_ (Finset.abs_sum_le_sum_abs _ _)
    rw [Finset.sum_range_sub']
    simp [cc]
  have hB : (Nat.choose n m : ℝ) ≤ ∑ j ∈ Ico (m + 1) (n + 2), |cc n j - cc n (j + 1)| := by
    refine le_trans ?_ (Finset.abs_sum_le_sum_abs _ _)
    rw [Finset.sum_Ico_eq_sub _ (show m + 1 ≤ n + 2 by omega), Finset.sum_range_sub',
      Finset.sum_range_sub']
    have : Nat.choose n (n + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [cc]
  rw [← hsplit]
  have hn : (0 : ℝ) ≤ n + 1 := by positivity
  nlinarith

lemma cb_bound (m : ℕ) (hm : 1 ≤ m) : 16 ^ m ≤ 4 * m * (Nat.centralBinom m) ^ 2 := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have h := Nat.succ_mul_centralBinom_succ m
    have key : (m + 1) * 16 ^ (m + 1) ≤ (m + 1) * (4 * (m + 1) * (Nat.centralBinom (m + 1)) ^ 2) := by
      calc (m + 1) * 16 ^ (m + 1) = 16 * (m + 1) * 16 ^ m := by ring
        _ ≤ 16 * (m + 1) * (4 * m * (Nat.centralBinom m) ^ 2) := Nat.mul_le_mul_left _ ih
        _ = 16 * (4 * m * (m + 1)) * (Nat.centralBinom m) ^ 2 := by ring
        _ ≤ 16 * (2 * m + 1) ^ 2 * (Nat.centralBinom m) ^ 2 := by
            apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_left; nlinarith
        _ = 4 * ((m + 1) * Nat.centralBinom (m + 1)) ^ 2 := by rw [h]; ring
        _ = (m + 1) * (4 * (m + 1) * (Nat.centralBinom (m + 1)) ^ 2) := by ring
    exact Nat.le_of_mul_le_mul_left key (Nat.succ_pos m)

lemma sqrt_helper (T : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (h : ((2:ℝ) ^ T) ^ 2 * 2 * T ≤ a ^ 2) : (2:ℝ) ^ T * Real.sqrt 2 * Real.sqrt T ≤ a := by
  have hb : (2:ℝ) ^ T * Real.sqrt 2 * Real.sqrt T = Real.sqrt (((2:ℝ) ^ T) ^ 2 * 2 * T) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [hb, ← Real.sqrt_sq ha]
  exact Real.sqrt_le_sqrt h

lemma Qbound' (n m : ℕ) (hm : m ≤ n) :
    2 * ((n + 1 : ℕ) : ℝ) * (Nat.choose n m : ℝ) ≤
      ∑ j ∈ range (n + 1 + 1), (Nat.choose (n + 1) j : ℝ) * |2 * (j : ℝ) - ((n + 1 : ℕ) : ℝ)| := by
  have := Qbound n m hm
  push_cast
  exact this

lemma Qfinal (T : ℕ) (hT : 1 ≤ T) :
    (2:ℝ) ^ T * Real.sqrt 2 * Real.sqrt T ≤
      2 * ∑ j ∈ range (T + 1), (Nat.choose T j : ℝ) * |2 * (j : ℝ) - (T : ℝ)| := by
  have hQ : ∀ m, m ≤ T - 1 → 2 * (T : ℝ) * (Nat.choose (T - 1) m : ℝ) ≤
      ∑ j ∈ range (T + 1), (Nat.choose T j : ℝ) * |2 * (j : ℝ) - (T : ℝ)| := by
    intro m hm
    have := Qbound' (T - 1) m hm
    rw [Nat.sub_add_cancel hT] at this
    exact this
  have ht : (0:ℝ) ≤ T := Nat.cast_nonneg _
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' T
  · obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
    have hT1 : T - 1 = 2 * l + 1 := by omega
    set X : ℝ := (Nat.choose (T - 1) l : ℝ) with hX
    have hQl := hQ l (by omega)
    have hcb : (Nat.centralBinom (l + 1) : ℝ) = 2 * X := by
      rw [hX, hT1, Nat.centralBinom_eq_two_mul_choose]
      have : 2 * (l + 1) = (2 * l + 1) + 1 := by ring
      rw [this, Nat.choose_succ_succ, ← Nat.choose_symm_half]
      push_cast; ring
    have hc' : (16:ℝ) ^ (l + 1) ≤ 4 * ((l : ℝ) + 1) * (Nat.centralBinom (l + 1) : ℝ) ^ 2 := by
      exact_mod_cast cb_bound (l + 1) (by omega)
    rw [hcb] at hc'
    have hTr : (T : ℝ) = 2 * ((l : ℝ) + 1) := by rw [hk]; push_cast; ring
    have e : ((2:ℝ) ^ T) ^ 2 = 16 ^ (l + 1) := by
      rw [← pow_mul, hk, show 2 * (l + 1) * 2 = 4 * (l + 1) by ring, pow_mul]; norm_num
    have hX0 : 0 ≤ X := Nat.cast_nonneg _
    have hP : ((2:ℝ) ^ T) ^ 2 ≤ 8 * (T : ℝ) * X ^ 2 := by rw [e, hTr]; nlinarith
    have hfin : ((2:ℝ) ^ T) ^ 2 * 2 * T ≤ (2 * (2 * (T : ℝ) * X)) ^ 2 := by
      have := mul_le_mul_of_nonneg_right hP (by positivity : (0:ℝ) ≤ 2 * T)
      nlinarith
    exact (sqrt_helper T _ (by positivity) hfin).trans (by linarith)
  · have hT1 : T - 1 = 2 * k := by omega
    set X : ℝ := (Nat.choose (T - 1) k : ℝ) with hX
    have hQk := hQ k (by omega)
    have hcb : (Nat.centralBinom k : ℝ) = X := by
      rw [hX, hT1, Nat.centralBinom_eq_two_mul_choose]
    have hc'' : (16:ℝ) ^ k ≤ 2 * (2 * (k : ℝ) + 1) * (Nat.centralBinom k : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0; simp [Nat.centralBinom]
      · have hc' : (16:ℝ) ^ k ≤ 4 * (k : ℝ) * (Nat.centralBinom k : ℝ) ^ 2 := by
          exact_mod_cast cb_bound k h0
        have : (0:ℝ) ≤ (Nat.centralBinom k : ℝ) ^ 2 := by positivity
        nlinarith
    rw [hcb] at hc''
    have hTr : (T : ℝ) = 2 * (k : ℝ) + 1 := by rw [hk]; push_cast; ring
    have e : ((2:ℝ) ^ T) ^ 2 = 4 * 16 ^ k := by
      rw [← pow_mul, hk, show (2 * k + 1) * 2 = 2 + 4 * k by ring, pow_add, pow_mul]; norm_num
    have hX0 : 0 ≤ X := Nat.cast_nonneg _
    have hP : ((2:ℝ) ^ T) ^ 2 ≤ 8 * (T : ℝ) * X ^ 2 := by rw [e, hTr]; nlinarith
    have hfin : ((2:ℝ) ^ T) ^ 2 * 2 * T ≤ (2 * (2 * (T : ℝ) * X)) ^ 2 := by
      have := mul_le_mul_of_nonneg_right hP (by positivity : (0:ℝ) ≤ 2 * T)
      nlinarith
    exact (sqrt_helper T _ (by positivity) hfin).trans (by linarith)

end RRAux_LB51

namespace RRAux_LB51
open Finset

def sg (s : Finset ℕ) (t : ℕ) : ℝ := if t ∈ s then 1 else -1

lemma diam_attained {d : ℕ} (V : Set (EuclideanSpace ℝ (Fin d))) (hne : V.Nonempty)
    (hc : IsClosed V) (hb : Bornology.IsBounded V) :
    ∃ v w, v ∈ V ∧ w ∈ V ∧ Metric.diam V = ‖v - w‖ := by
  have hK := Metric.isCompact_of_isClosed_isBounded hc hb
  obtain ⟨p, hp, hmax⟩ := (hK.prod hK).exists_isMaxOn (hne.prod hne)
    (continuous_dist.continuousOn (s := V ×ˢ V))
  refine ⟨p.1, p.2, hp.1, hp.2, ?_⟩
  rw [← dist_eq_norm]
  apply le_antisymm
  · apply Metric.diam_le_of_forall_dist_le dist_nonneg
    intro x hx y hy
    exact isMaxOn_iff.mp hmax (x, y) (Set.mk_mem_prod hx hy)
  · exact Metric.dist_le_diam_of_mem hb hp.1 hp.2

lemma mart {d : ℕ} (V : Set (EuclideanSpace ℝ (Fin d)))
    (A : ℕ → (ℕ → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    (hA : ModernOnlineLearning.LowerBounds.IsDeterministicOLOAlg V A)
    (z : EuclideanSpace ℝ (Fin d)) (L m : ℝ) (T t : ℕ) (ht : t ∈ Icc 1 T) :
    ∑ s ∈ (Icc 1 T).powerset,
      sg s t * (inner ℝ z (A t (fun r => (L * sg s r) • z)) - m) = 0 := by
  set f : Finset ℕ → ℝ := fun s => sg s t * (inner ℝ z (A t (fun r => (L * sg s r) • z)) - m)
    with hf
  have hflip : ∀ s : Finset ℕ, f (symmDiff s {t}) = - f s := by
    intro s
    have hmem : ∀ r, r ≠ t → (r ∈ symmDiff s {t} ↔ r ∈ s) := by
      intro r hr; simp [Finset.mem_symmDiff, hr]
    have hA' : A t (fun r => (L * sg (symmDiff s {t}) r) • z) = A t (fun r => (L * sg s r) • z) := by
      apply hA.2 t _ _ (Finset.mem_Icc.mp ht).1
      intro r _ hrt
      have : sg (symmDiff s {t}) r = sg s r := by
        unfold sg; rw [if_congr (hmem r (by omega)) rfl rfl]
      rw [this]
    have hsg : sg (symmDiff s {t}) t = - sg s t := by
      unfold sg
      by_cases h : t ∈ s <;> simp [Finset.mem_symmDiff, h]
    simp only [hf, hA', hsg]; ring
  have h : ∑ s ∈ (Icc 1 T).powerset, f s = ∑ s ∈ (Icc 1 T).powerset, - f s := by
    apply Finset.sum_nbij' (fun s => symmDiff s {t}) (fun s => symmDiff s {t})
    · intro s hs
      rw [Finset.mem_powerset] at hs ⊢
      intro r hr
      rcases Finset.mem_symmDiff.mp hr with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hs h1
      · rw [Finset.mem_singleton.mp h1]; exact ht
    · intro s hs
      rw [Finset.mem_powerset] at hs ⊢
      intro r hr
      rcases Finset.mem_symmDiff.mp hr with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hs h1
      · rw [Finset.mem_singleton.mp h1]; exact ht
    · intro s _; exact symmDiff_symmDiff_cancel_right _ _
    · intro s _; exact symmDiff_symmDiff_cancel_right _ _
    · intro s _; rw [hflip]; ring
  rw [Finset.sum_neg_distrib] at h
  show ∑ s ∈ (Icc 1 T).powerset, f s = 0
  linarith

lemma sumS (s : Finset ℕ) (T : ℕ) (hs : s ⊆ Icc 1 T) :
    ∑ t ∈ Icc 1 T, sg s t = 2 * (s.card : ℝ) - T := by
  have : ∀ t, sg s t = 2 * (if t ∈ s then (1:ℝ) else 0) - 1 := by
    intro t; unfold sg; split_ifs <;> ring
  simp_rw [this]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr hs]
  simp

lemma sumAbs (T : ℕ) :
    ∑ s ∈ (Icc 1 T).powerset, |∑ t ∈ Icc 1 T, sg s t| =
      ∑ j ∈ range (T + 1), (Nat.choose T j : ℝ) * |2 * (j : ℝ) - (T : ℝ)| := by
  have h1 : ∑ s ∈ (Icc 1 T).powerset, |∑ t ∈ Icc 1 T, sg s t|
      = ∑ s ∈ (Icc 1 T).powerset, (fun j : ℕ => |2 * (j : ℝ) - (T : ℝ)|) s.card := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [sumS s T (Finset.mem_powerset.mp hs)]
  rw [h1, Finset.sum_powerset_apply_card (fun j : ℕ => |2 * (j : ℝ) - (T : ℝ)|) (x := Icc 1 T)]
  simp [nsmul_eq_mul]

end RRAux_LB51

namespace RRAux_LB51
open Finset

lemma regret_split {d : ℕ}
    (A : ℕ → (ℕ → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    (z u : EuclideanSpace ℝ (Fin d)) (L m : ℝ) (s : Finset ℕ) (T : ℕ) :
    ModernOnlineLearning.LowerBounds.oloRegret A (fun r => (L * sg s r) • z) u T
      = L * ∑ t ∈ Icc 1 T, sg s t * (inner ℝ z (A t (fun r => (L * sg s r) • z)) - m)
        + L * (m - inner ℝ z u) * ∑ t ∈ Icc 1 T, sg s t := by
  unfold ModernOnlineLearning.LowerBounds.oloRegret
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  simp only [real_inner_smul_left]
  ring

lemma choose_u (L D m a b S : ℝ) (hL : 0 ≤ L) (ha : m - a = -(D / 2)) (hb : m - b = D / 2) :
    L * (m - (if S ≤ 0 then a else b)) * S = L * (D / 2) * |S| := by
  split_ifs with h
  · rw [ha, abs_of_nonpos h]; ring
  · rw [hb, abs_of_pos (not_le.mp h)]

end RRAux_LB51

open ModernOnlineLearning.LowerBounds in
theorem solution {d : ℕ} (V : Set (EuclideanSpace ℝ (Fin d)))
    (hVne : V.Nonempty) (hVclosed : IsClosed V)
    (hVbounded : Bornology.IsBounded V) (hVconvex : Convex ℝ V)
    (hD : 0 < Metric.diam V)
    (A : ℕ → (ℕ → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    (hA : IsDeterministicOLOAlg V A)
    (L : ℝ) (hL : 0 ≤ L) (T : ℕ) (hT : 1 ≤ T) :
    ∃ (g : ℕ → EuclideanSpace ℝ (Fin d)) (u : EuclideanSpace ℝ (Fin d)),
      u ∈ V ∧
      (∀ t ∈ Finset.Icc 1 T, ‖g t‖ ≤ L) ∧
      Real.sqrt 2 * L * Metric.diam V * Real.sqrt (T : ℝ) / 4 ≤
        oloRegret A g u T := by
  obtain ⟨v, w, hv, hw, hvw⟩ := RRAux_LB51.diam_attained V hVne hVclosed hVbounded
  rw [hvw] at hD ⊢
  set D := ‖v - w‖ with hDdef
  set z : EuclideanSpace ℝ (Fin d) := D⁻¹ • (v - w) with hzdef
  have hz : ‖z‖ = 1 := by
    rw [hzdef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hD, ← hDdef]
    exact inv_mul_cancel₀ hD.ne'
  have hφ : inner ℝ z v - inner ℝ z w = D := by
    rw [← inner_sub_right, hzdef, real_inner_smul_left, real_inner_self_eq_norm_sq, ← hDdef]
    field_simp
  set m : ℝ := (inner ℝ z v + inner ℝ z w) / 2 with hm
  have ha : m - inner ℝ z v = -(D / 2) := by rw [hm]; linarith
  have hb : m - inner ℝ z w = D / 2 := by rw [hm]; linarith
  set P := (Finset.Icc 1 T).powerset with hP
  let U : Finset ℕ → EuclideanSpace ℝ (Fin d) := fun s =>
    if (∑ t ∈ Finset.Icc 1 T, RRAux_LB51.sg s t) ≤ 0 then v else w
  have hR : ∀ s, oloRegret A (fun r => (L * RRAux_LB51.sg s r) • z) (U s) T
      = L * ∑ t ∈ Finset.Icc 1 T, RRAux_LB51.sg s t *
          (inner ℝ z (A t (fun r => (L * RRAux_LB51.sg s r) • z)) - m)
        + L * (D / 2) * |∑ t ∈ Finset.Icc 1 T, RRAux_LB51.sg s t| := by
    intro s
    rw [RRAux_LB51.regret_split A z (U s) L m s T]
    congr 1
    have : inner ℝ z (U s) = if (∑ t ∈ Finset.Icc 1 T, RRAux_LB51.sg s t) ≤ 0
        then inner ℝ z v else inner ℝ z w := by
      simp only [U]; split_ifs <;> rfl
    rw [this]
    exact RRAux_LB51.choose_u L D m _ _ _ hL ha hb
  have hmart : ∑ s ∈ P, L * ∑ t ∈ Finset.Icc 1 T, RRAux_LB51.sg s t *
      (inner ℝ z (A t (fun r => (L * RRAux_LB51.sg s r) • z)) - m) = 0 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    rw [Finset.sum_eq_zero (fun t ht => RRAux_LB51.mart V A hA z L m T t ht), mul_zero]
  have habs := RRAux_LB51.sumAbs T
  have hQ := RRAux_LB51.Qfinal T hT
  have hcard : (P.card : ℝ) = 2 ^ T := by
    rw [hP, Finset.card_powerset, Nat.card_Icc]; push_cast; simp
  have key : ∑ s ∈ P, Real.sqrt 2 * L * D * Real.sqrt (T : ℝ) / 4 ≤
      ∑ s ∈ P, oloRegret A (fun r => (L * RRAux_LB51.sg s r) • z) (U s) T := by
    simp_rw [hR]
    rw [Finset.sum_add_distrib, hmart, zero_add, ← Finset.mul_sum, habs, Finset.sum_const,
      nsmul_eq_mul, hcard]
    have hLD : 0 ≤ L * D := mul_nonneg hL hD.le
    have := mul_le_mul_of_nonneg_left hQ hLD
    nlinarith
  obtain ⟨s, _, hs⟩ := Finset.exists_le_of_sum_le
    (Finset.powerset_nonempty _) key
  refine ⟨fun r => (L * RRAux_LB51.sg s r) • z, U s, ?_, ?_, hs⟩
  · simp only [U]; split_ifs
    · exact hv
    · exact hw
  · intro t _
    rw [norm_smul, hz, mul_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg hL]
    have : |RRAux_LB51.sg s t| = 1 := by unfold RRAux_LB51.sg; split_ifs <;> simp
    rw [this, mul_one]

#print axioms solution
