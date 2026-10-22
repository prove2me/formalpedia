-- Prove2me | solution 1 for HTInsensBW.PhaseType.eq_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T21:48:41.447079+00:00
-- url     : https://prove2.me/submissions/cf5acd5e-0a6c-4468-98a4-5089f64f5450

import Mathlib
import Definitions.Def_HTInsensBW_PhaseType_Model

namespace HTInsensBWEq5

open HTInsensBW.PhaseType Finset

variable {L R : ℕ}

/-- The objective `Σ_r κ_r m_r log y_r`. -/
noncomputable def obj (N : BWNetwork L R) (m : Fin R → ℕ) (y : Fin R → ℝ) : ℝ :=
  ∑ r, N.κ r * (m r : ℝ) * Real.log (y r)

/-- The load of link `ℓ`, `Σ_r h_ℓr m_r y_r`. -/
def load (N : BWNetwork L R) (m : Fin R → ℕ) (y : Fin R → ℝ) (ℓ : Fin L) : ℝ :=
  ∑ r, N.H ℓ r * (m r : ℝ) * y r

lemma log_mid {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (Real.log a + Real.log b) / 2 ≤ Real.log ((a + b) / 2) ∧
      (a ≠ b → (Real.log a + Real.log b) / 2 < Real.log ((a + b) / 2)) := by
  have hab : 0 < a * b := mul_pos ha hb
  have hm : 0 < (a + b) / 2 := by positivity
  have e : Real.log a + Real.log b = Real.log (a * b) := (Real.log_mul ha.ne' hb.ne').symm
  have e2 : 2 * Real.log ((a + b) / 2) = Real.log (((a + b) / 2) ^ 2) := by
    rw [Real.log_pow]; push_cast; ring
  constructor
  · have : a * b ≤ ((a + b) / 2) ^ 2 := by nlinarith [sq_nonneg (a - b)]
    have := Real.log_le_log hab this
    linarith
  · intro hne
    have : a * b < ((a + b) / 2) ^ 2 := by
      have : 0 < (a - b) ^ 2 := by
        have : a - b ≠ 0 := sub_ne_zero.2 hne
        positivity
      nlinarith
    have := Real.log_lt_log hab this
    linarith

lemma term_nonneg (N : BWNetwork L R) (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1)
    (m : Fin R → ℕ) (y : Fin R → ℝ) (hy : ∀ r, 0 < m r → 0 < y r) (ℓ : Fin L) (r : Fin R) :
    0 ≤ N.H ℓ r * (m r : ℝ) * y r := by
  have hH : 0 ≤ N.H ℓ r := by rcases hH01 ℓ r with h | h <;> simp [h]
  rcases Nat.eq_zero_or_pos (m r) with h | h
  · simp [h]
  · exact mul_nonneg (mul_nonneg hH (Nat.cast_nonneg _)) (hy r h).le

/-- A strictly feasible point (Slater point). -/
lemma slater (N : BWNetwork L R) (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1)
    (hC : ∀ ℓ, 0 < N.C ℓ) (m : Fin R → ℕ) :
    ∃ y0 : Fin R → ℝ, (∀ r, 0 < m r → 0 < y0 r) ∧ (∀ r, m r = 0 → y0 r = 0) ∧
      ∀ ℓ, load N m y0 ℓ < N.C ℓ := by
  set M : ℝ := ∑ r, (m r : ℝ) with hM
  set Ci : ℝ := ∑ ℓ, 1 / N.C ℓ with hCi
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun r _ => Nat.cast_nonneg _)
  have hCi0 : 0 ≤ Ci := Finset.sum_nonneg (fun ℓ _ => (one_div_pos.2 (hC ℓ)).le)
  set θ : ℝ := 1 / ((1 + M) * (1 + Ci)) with hθ
  have hθ0 : 0 < θ := by positivity
  refine ⟨fun r => if 0 < m r then θ else 0, ?_, ?_, ?_⟩
  · intro r h; simp [h, hθ0]
  · intro r h; simp [h]
  · intro ℓ
    unfold load
    have h1 : ∑ r, N.H ℓ r * (m r : ℝ) * (if 0 < m r then θ else 0) ≤ M * θ := by
      rw [hM, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro r _
      have hH : N.H ℓ r ≤ 1 := by rcases hH01 ℓ r with h | h <;> simp [h]
      have hH0 : 0 ≤ N.H ℓ r := by rcases hH01 ℓ r with h | h <;> simp [h]
      split_ifs with h
      · have : N.H ℓ r * (m r : ℝ) ≤ 1 * (m r : ℝ) :=
          mul_le_mul_of_nonneg_right hH (Nat.cast_nonneg _)
        nlinarith
      · simp only [mul_zero]; positivity
    have h2 : M * θ < 1 / (1 + Ci) := by
      rw [hθ]
      rw [show M * (1 / ((1 + M) * (1 + Ci))) = (M / (1 + M)) * (1 / (1 + Ci)) by
        field_simp]
      have : M / (1 + M) < 1 := by rw [div_lt_one (by positivity)]; linarith
      have hp : 0 < 1 / (1 + Ci) := by positivity
      nlinarith
    have h3 : 1 / (1 + Ci) ≤ N.C ℓ := by
      have hle : 1 / N.C ℓ ≤ Ci :=
        Finset.single_le_sum (f := fun ℓ => 1 / N.C ℓ)
          (fun ℓ _ => (one_div_pos.2 (hC ℓ)).le) (Finset.mem_univ ℓ)
      rw [div_le_iff₀ (by positivity)]
      have hCl := hC ℓ
      have : N.C ℓ * (1 / N.C ℓ) = 1 := by field_simp
      nlinarith
    linarith

lemma upper (N : BWNetwork L R) (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1)
    (hroute : ∀ r, ∃ ℓ, N.H ℓ r = 1) (hC : ∀ ℓ, 0 < N.C ℓ) (m : Fin R → ℕ)
    (y : Fin R → ℝ) (hy : ∀ r, 0 < m r → 0 < y r) (hfeas : ∀ ℓ, load N m y ℓ ≤ N.C ℓ)
    (r : Fin R) (hr : 0 < m r) : y r ≤ ∑ ℓ, N.C ℓ := by
  obtain ⟨ℓ, hℓ⟩ := hroute r
  have h1 : N.H ℓ r * (m r : ℝ) * y r ≤ load N m y ℓ :=
    Finset.single_le_sum (f := fun r => N.H ℓ r * (m r : ℝ) * y r)
      (fun r _ => term_nonneg N hH01 m y hy ℓ r) (Finset.mem_univ r)
  have h2 : N.C ℓ ≤ ∑ ℓ, N.C ℓ :=
    Finset.single_le_sum (fun ℓ _ => (hC ℓ).le) (Finset.mem_univ ℓ)
  rw [hℓ, one_mul] at h1
  have hm1 : (1 : ℝ) ≤ m r := by exact_mod_cast hr
  have hyr := hy r hr
  have : y r ≤ (m r : ℝ) * y r := by nlinarith
  linarith [hfeas ℓ]

lemma obj_le_term (N : BWNetwork L R) (hκ : ∀ r, 0 < N.κ r) (m : Fin R → ℕ)
    (y : Fin R → ℝ) (hy : ∀ r, 0 < m r → 0 < y r) (B : ℝ)
    (hB : ∀ r, 0 < m r → y r ≤ B) (r : Fin R) :
    obj N m y ≤ N.κ r * (m r : ℝ) * Real.log (y r) +
      (∑ r, N.κ r * (m r : ℝ)) * |Real.log B| := by
  classical
  unfold obj
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
  have hbd : ∀ r', N.κ r' * (m r' : ℝ) * Real.log (y r') ≤ N.κ r' * (m r' : ℝ) * |Real.log B| := by
    intro r'
    rcases Nat.eq_zero_or_pos (m r') with h | h
    · simp [h]
    · have hyr := hy r' h
      have : Real.log (y r') ≤ |Real.log B| :=
        (Real.log_le_log hyr (hB r' h)).trans (le_abs_self _)
      exact mul_le_mul_of_nonneg_left this (mul_nonneg (hκ r').le (Nat.cast_nonneg _))
  have hs : ∑ x ∈ univ.erase r, N.κ x * (m x : ℝ) * Real.log (y x) ≤
      (∑ r, N.κ r * (m r : ℝ)) * |Real.log B| := by
    calc _ ≤ ∑ x ∈ univ.erase r, N.κ x * (m x : ℝ) * |Real.log B| := Finset.sum_le_sum (fun x _ => hbd x)
      _ ≤ ∑ x, N.κ x * (m x : ℝ) * |Real.log B| :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun x _ _ => by have := hκ x; positivity)
      _ = _ := by rw [Finset.sum_mul]
  linarith

lemma exists_wpf (N : BWNetwork L R) (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1)
    (hroute : ∀ r, ∃ ℓ, N.H ℓ r = 1) (hC : ∀ ℓ, 0 < N.C ℓ) (hκ : ∀ r, 0 < N.κ r)
    (m : Fin R → ℕ) : ∃ x, IsWPFAllocation N m x := by
  classical
  obtain ⟨y0, hy0p, hy0z, hy0f⟩ := slater N hH01 hC m
  set Cm : ℝ := ∑ ℓ, N.C ℓ with hCm
  set Λ : ℝ := ∑ r, N.κ r * (m r : ℝ) with hΛ
  set D : ℝ := |obj N m y0| + Λ * |Real.log Cm| with hD
  set η : Fin R → ℝ := fun r => Real.exp (-D / (N.κ r * (m r : ℝ))) with hη
  have hη0 : ∀ r, 0 < η r := fun r => Real.exp_pos _
  -- competitors with large objective lie in the box
  have hbox : ∀ y : Fin R → ℝ, (∀ r, 0 < m r → 0 < y r) → (∀ ℓ, load N m y ℓ ≤ N.C ℓ) →
      obj N m y0 ≤ obj N m y → ∀ r, 0 < m r → η r ≤ y r ∧ y r ≤ Cm := by
    intro y hy hf hobj r hr
    have hup := upper N hH01 hroute hC m y hy hf
    refine ⟨?_, hup r hr⟩
    have h1 := obj_le_term N hκ m y hy Cm hup r
    have hkm : 0 < N.κ r * (m r : ℝ) := mul_pos (hκ r) (by exact_mod_cast hr)
    have h2 : -D ≤ N.κ r * (m r : ℝ) * Real.log (y r) := by
      have := neg_abs_le (obj N m y0)
      rw [hD]; linarith
    have h3 : -D / (N.κ r * (m r : ℝ)) ≤ Real.log (y r) := by
      rw [div_le_iff₀ hkm]; linarith
    exact (Real.le_log_iff_exp_le (hy r hr)).1 h3
  set S : Set (Fin R → ℝ) := {y | (∀ r, 0 < m r → η r ≤ y r ∧ y r ≤ Cm) ∧
      (∀ r, m r = 0 → y r = 0) ∧ ∀ ℓ, load N m y ℓ ≤ N.C ℓ} with hS
  have hpos : ∀ y ∈ S, ∀ r, 0 < m r → 0 < y r := fun y hy r hr => (hη0 r).trans_le (hy.1 r hr).1
  have hy0S : y0 ∈ S := by
    refine ⟨hbox y0 hy0p (fun ℓ => (hy0f ℓ).le) le_rfl, hy0z, fun ℓ => (hy0f ℓ).le⟩
  have hCm0 : 0 ≤ Cm := Finset.sum_nonneg (fun ℓ _ => (hC ℓ).le)
  have hSsub : S ⊆ Set.univ.pi (fun _ => Set.Icc (0 : ℝ) Cm) := by
    intro y hy r _
    rcases Nat.eq_zero_or_pos (m r) with h | h
    · rw [hy.2.1 r h]; exact ⟨le_rfl, hCm0⟩
    · exact ⟨(hpos y hy r h).le, (hy.1 r h).2⟩
  have hSc : IsClosed S := by
    have e : S = (⋂ r, {y : Fin R → ℝ | 0 < m r → η r ≤ y r ∧ y r ≤ Cm}) ∩
        (⋂ r, {y : Fin R → ℝ | m r = 0 → y r = 0}) ∩
        ⋂ ℓ, {y : Fin R → ℝ | load N m y ℓ ≤ N.C ℓ} := by
      ext y; simp [hS, and_assoc]
    rw [e]
    refine ((isClosed_iInter fun r => ?_).inter (isClosed_iInter fun r => ?_)).inter
      (isClosed_iInter fun ℓ => ?_)
    · by_cases h : 0 < m r
      · simp only [h, true_implies, Set.ofPred_and]
        exact (isClosed_le continuous_const (continuous_apply r)).inter
          (isClosed_le (continuous_apply r) continuous_const)
      · simp only [h, false_implies, Set.ofPred_true]; exact isClosed_univ
    · by_cases h : m r = 0
      · simp only [h, true_implies]
        exact isClosed_eq (continuous_apply r) continuous_const
      · simp only [h, false_implies, Set.ofPred_true]; exact isClosed_univ
    · apply isClosed_le _ continuous_const
      unfold load
      exact continuous_finsetSum _ (fun r _ => continuous_const.mul (continuous_apply r))
  have hScomp : IsCompact S :=
    IsCompact.of_isClosed_subset (isCompact_univ_pi (fun _ => isCompact_Icc)) hSc hSsub
  have hcont : ContinuousOn (obj N m) S := by
    unfold obj
    apply continuousOn_finsetSum
    intro r _
    rcases Nat.eq_zero_or_pos (m r) with h | h
    · simp only [h, Nat.cast_zero, mul_zero, zero_mul]; exact continuousOn_const
    · apply ContinuousOn.mul continuousOn_const
      exact ContinuousOn.log (continuous_apply r).continuousOn
        (fun y hy => (hpos y hy r h).ne')
  obtain ⟨x, hxS, hxmax⟩ := hScomp.exists_isMaxOn ⟨y0, hy0S⟩ hcont
  refine ⟨x, hxS.2.1, hpos x hxS, hxS.2.2, ?_⟩
  intro y hy hf
  show obj N m y ≤ obj N m x
  by_cases hlt : obj N m y < obj N m y0
  · exact hlt.le.trans (hxmax hy0S)
  · push_neg at hlt
    set y' : Fin R → ℝ := fun r => if 0 < m r then y r else 0 with hy'
    have hobj' : obj N m y' = obj N m y := by
      unfold obj; apply Finset.sum_congr rfl; intro r _
      rcases Nat.eq_zero_or_pos (m r) with h | h
      · simp [h]
      · simp [hy', h]
    have hload' : ∀ ℓ, load N m y' ℓ = load N m y ℓ := by
      intro ℓ; unfold load; apply Finset.sum_congr rfl; intro r _
      rcases Nat.eq_zero_or_pos (m r) with h | h
      · simp [h]
      · simp [hy', h]
    have hy'p : ∀ r, 0 < m r → 0 < y' r := fun r h => by simp [hy', h, hy r h]
    have hf' : ∀ ℓ, load N m y' ℓ ≤ N.C ℓ := fun ℓ => by rw [hload']; exact hf ℓ
    have hy'S : y' ∈ S := by
      refine ⟨hbox y' hy'p hf' (by rw [hobj']; exact hlt), ?_, hf'⟩
      intro r h; simp [hy', h]
    rw [← hobj']
    exact hxmax hy'S

lemma unique_wpf (N : BWNetwork L R) (hκ : ∀ r, 0 < N.κ r) (m : Fin R → ℕ)
    (x x' : Fin R → ℝ) (hx : IsWPFAllocation N m x) (hx' : IsWPFAllocation N m x') : x = x' := by
  classical
  set z : Fin R → ℝ := fun r => (x r + x' r) / 2 with hz
  have hzp : ∀ r, 0 < m r → 0 < z r := fun r h => by
    have := hx.2.1 r h; have := hx'.2.1 r h; simp only [hz]; positivity
  have hzf : ∀ ℓ, ∑ r, N.H ℓ r * (m r : ℝ) * z r ≤ N.C ℓ := by
    intro ℓ
    have e : ∑ r, N.H ℓ r * (m r : ℝ) * z r =
        ((∑ r, N.H ℓ r * (m r : ℝ) * x r) + ∑ r, N.H ℓ r * (m r : ℝ) * x' r) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl; intro r _; simp only [hz]; ring
    rw [e]; linarith [hx.2.2.1 ℓ, hx'.2.2.1 ℓ]
  have h1 := hx.2.2.2 z hzp hzf
  have h2 := hx.2.2.2 x' hx'.2.1 hx'.2.2.1
  have h3 := hx'.2.2.2 x hx.2.1 hx.2.2.1
  funext r
  rcases Nat.eq_zero_or_pos (m r) with h | h
  · rw [hx.1 r h, hx'.1 r h]
  · by_contra hne
    -- strict inequality for the midpoint
    have hlt : (∑ r, N.κ r * (m r : ℝ) * Real.log (x r) + ∑ r, N.κ r * (m r : ℝ) * Real.log (x' r)) / 2
        < ∑ r, N.κ r * (m r : ℝ) * Real.log (z r) := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_lt_sum
      · intro r' _
        rcases Nat.eq_zero_or_pos (m r') with h' | h'
        · simp [h']
        · have := (log_mid (hx.2.1 r' h') (hx'.2.1 r' h')).1
          have hk : 0 ≤ N.κ r' * (m r' : ℝ) := mul_nonneg (hκ r').le (Nat.cast_nonneg _)
          simp only [hz]
          nlinarith
      · refine ⟨r, Finset.mem_univ r, ?_⟩
        have := (log_mid (hx.2.1 r h) (hx'.2.1 r h)).2 hne
        have hk : 0 < N.κ r * (m r : ℝ) := mul_pos (hκ r) (by exact_mod_cast h)
        simp only [hz]
        nlinarith
    linarith

/-- If `α + s β < c` for all `s ≥ 0` then `β ≤ 0`. -/
lemma ray_bound {α β c : ℝ} (h : ∀ s : ℝ, 0 ≤ s → α + s * β < c) : β ≤ 0 := by
  by_contra hb
  push_neg at hb
  set s := max 0 ((c - α) / β) + 1
  have hs : 0 ≤ s := by positivity
  have h1 := h s hs
  have h2 : (c - α) / β ≤ max 0 ((c - α) / β) := le_max_right _ _
  have h3 : (c - α) ≤ max 0 ((c - α) / β) * β := by
    rw [div_le_iff₀ hb] at h2; exact h2
  have : α + s * β = α + max 0 ((c - α) / β) * β + β := by ring
  linarith

lemma le_of_forall_pos (a c K : ℝ) (h : ∀ η : ℝ, 0 < η → a < c + η * K) : a ≤ c := by
  by_contra hac
  push_neg at hac
  set η := (a - c) / (|K| + 1)
  have hη : 0 < η := by positivity
  have h1 := h η hη
  have h2 : η * K ≤ η * |K| := mul_le_mul_of_nonneg_left (le_abs_self K) hη.le
  have h3 : η * |K| < a - c := by
    have : η * (|K| + 1) = a - c := by simp only [η]; field_simp
    nlinarith [abs_nonneg K]
  linarith

lemma one_dim (κ x c : ℝ) (hκ : 0 < κ) (hx : 0 < x)
    (h : ∀ s : ℝ, 0 < s → κ * (Real.log s - Real.log x) ≤ c * (s - x)) : x = κ / c := by
  have hc : 0 < c := by
    by_contra hc
    push_neg at hc
    have := h (x * Real.exp 1) (by positivity)
    rw [Real.log_mul hx.ne' (Real.exp_pos 1).ne', Real.log_exp] at this
    have hgt : x < x * Real.exp 1 := by
      have := Real.add_one_lt_exp (one_ne_zero)
      nlinarith
    have : c * (x * Real.exp 1 - x) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc (by linarith)
    linarith
  set t := c * x / κ with ht
  have ht0 : 0 < t := by positivity
  have h1 := h (κ / c) (by positivity)
  have e : Real.log (κ / c) - Real.log x = -Real.log t := by
    rw [ht, Real.log_div (by positivity) hκ.ne', Real.log_mul hc.ne' hx.ne',
      Real.log_div hκ.ne' hc.ne']
    ring
  rw [e] at h1
  have e2 : c * (κ / c - x) = κ * (1 - t) := by rw [ht]; field_simp
  rw [e2] at h1
  have h2 : t - 1 ≤ Real.log t := by nlinarith
  by_contra hne
  have ht1 : t ≠ 1 := by
    intro h1'
    apply hne
    rw [ht] at h1'
    field_simp at h1' ⊢
    linarith
  have := Real.log_lt_sub_one_of_pos ht0 ht1
  linarith

lemma kkt_of_wpf (N : BWNetwork L R) (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1)
    (hC : ∀ ℓ, 0 < N.C ℓ) (hκ : ∀ r, 0 < N.κ r) (m : Fin R → ℕ) (x : Fin R → ℝ)
    (hx : IsWPFAllocation N m x) : ∃ p, IsKKTMultiplier N m x p := by
  classical
  obtain ⟨y0, hy0p, -, hy0f⟩ := slater N hH01 hC m
  set g : (Fin R → ℝ) → Fin L → ℝ := fun y ℓ => load N m y ℓ - N.C ℓ with hg
  set Bset : Set ((Fin L → ℝ) × ℝ) := {z | (∀ ℓ, z.1 ℓ < 0) ∧ obj N m x < z.2} with hBset
  set Aset : Set ((Fin L → ℝ) × ℝ) := {z | ∃ y : Fin R → ℝ, (∀ r, 0 < m r → 0 < y r) ∧
      (∀ ℓ, g y ℓ ≤ z.1 ℓ) ∧ z.2 ≤ obj N m y} with hAset
  have hxopt : ∀ y : Fin R → ℝ, (∀ r, 0 < m r → 0 < y r) → (∀ ℓ, load N m y ℓ ≤ N.C ℓ) →
      obj N m y ≤ obj N m x := fun y hy hf => hx.2.2.2 y hy hf
  -- convexity and openness
  have hBconv : Convex ℝ Bset := by
    intro z1 hz1 z2 hz2 a b ha hb hab
    refine ⟨fun ℓ => ?_, ?_⟩
    · have h1 := hz1.1 ℓ; have h2 := hz2.1 ℓ
      simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases eq_or_lt_of_le ha with ha0 | ha0
      · rw [← ha0] at hab ⊢; simp only [zero_add] at hab; rw [hab]; linarith
      · nlinarith
    · have h1 := hz1.2; have h2 := hz2.2
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      have e : a * obj N m x + b * obj N m x = obj N m x := by rw [← add_mul, hab, one_mul]
      rcases eq_or_lt_of_le ha with ha0 | ha0
      · rw [← ha0] at hab ⊢; simp only [zero_add] at hab; rw [hab]; linarith
      · have := mul_lt_mul_of_pos_left h1 ha0
        have := mul_le_mul_of_nonneg_left h2.le hb
        linarith
  have hBopen : IsOpen Bset := by
    have e : Bset = (⋂ ℓ, {z : (Fin L → ℝ) × ℝ | z.1 ℓ < 0}) ∩ {z | obj N m x < z.2} := by
      ext z; simp [hBset]
    rw [e]
    refine IsOpen.inter (isOpen_iInter_of_finite fun ℓ => ?_) ?_
    · exact isOpen_lt ((continuous_apply ℓ).comp continuous_fst) continuous_const
    · exact isOpen_lt continuous_const continuous_snd
  have hAconv : Convex ℝ Aset := by
    intro z1 hz1 z2 hz2 a b ha hb hab
    obtain ⟨y1, hy1p, hy1g, hy1o⟩ := hz1
    obtain ⟨y2, hy2p, hy2g, hy2o⟩ := hz2
    refine ⟨a • y1 + b • y2, ?_, ?_, ?_⟩
    · intro r hr
      have := hy1p r hr; have := hy2p r hr
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases eq_or_lt_of_le ha with ha0 | ha0
      · rw [← ha0] at hab ⊢; simp only [zero_add] at hab; rw [hab]; linarith
      · nlinarith
    · intro ℓ
      have hl : load N m (a • y1 + b • y2) ℓ = a * load N m y1 ℓ + b * load N m y2 ℓ := by
        simp only [load, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro r _; ring
      have e : g (a • y1 + b • y2) ℓ = a * g y1 ℓ + b * g y2 ℓ := by
        simp only [hg]; rw [hl]; linear_combination (N.C ℓ) * hab
      rw [e]
      simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hy1g ℓ; have := hy2g ℓ
      nlinarith
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      have hc : a * obj N m y1 + b * obj N m y2 ≤ obj N m (a • y1 + b • y2) := by
        unfold obj
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro r _
        rcases Nat.eq_zero_or_pos (m r) with h | h
        · simp [h]
        · have hcv := (strictConcaveOn_log_Ioi.concaveOn).2 (Set.mem_Ioi.2 (hy1p r h))
            (Set.mem_Ioi.2 (hy2p r h)) ha hb hab
          simp only [smul_eq_mul] at hcv
          have hk : 0 ≤ N.κ r * (m r : ℝ) := mul_nonneg (hκ r).le (Nat.cast_nonneg _)
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          nlinarith
      nlinarith
  have hdisj : Disjoint Bset Aset := by
    rw [Set.disjoint_left]
    rintro z ⟨hz1, hz2⟩ ⟨y, hyp, hyg, hyo⟩
    have hf : ∀ ℓ, load N m y ℓ ≤ N.C ℓ := by
      intro ℓ; have := hyg ℓ; have := hz1 ℓ; simp only [hg] at *; linarith
    have := hxopt y hyp hf
    linarith
  obtain ⟨φ, c, hφB, hφA⟩ := geometric_hahn_banach_open hBconv hBopen hAconv hdisj
  set lam : Fin L → ℝ := fun ℓ => φ ((Pi.single ℓ (1 : ℝ) : Fin L → ℝ), (0 : ℝ)) with hlam
  set μ : ℝ := φ ((0 : Fin L → ℝ), (1 : ℝ)) with hμ
  have hrep : ∀ (u : Fin L → ℝ) (t : ℝ), φ (u, t) = ∑ ℓ, lam ℓ * u ℓ + μ * t := by
    intro u t
    have e : (u, t) = ∑ ℓ, u ℓ • ((Pi.single ℓ (1 : ℝ) : Fin L → ℝ), (0 : ℝ)) +
        t • ((0 : Fin L → ℝ), (1 : ℝ)) := by
      ext ℓ
      · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · simp [Prod.snd_sum]
    rw [e, map_add, map_sum, map_smul]
    simp only [map_smul, smul_eq_mul, hlam, hμ]
    rw [mul_comm t]
    congr 1
    apply Finset.sum_congr rfl; intro ℓ _; ring
  -- base point in B
  set b0 : (Fin L → ℝ) × ℝ := (fun _ => -1, obj N m x + 1) with hb0
  have hb0B : b0 ∈ Bset := ⟨fun ℓ => by simp [hb0], by simp [hb0]⟩
  -- sign conditions
  have hlam0 : ∀ ℓ, 0 ≤ lam ℓ := by
    intro ℓ
    have : -lam ℓ ≤ 0 := by
      apply ray_bound (α := φ b0) (c := c)
      intro s hs
      have hmem : b0 + s • ((-(Pi.single ℓ (1 : ℝ)) : Fin L → ℝ), (0 : ℝ)) ∈ Bset := by
        refine ⟨fun ℓ' => ?_, ?_⟩
        · simp only [hb0, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, Pi.neg_apply,
            smul_eq_mul]
          by_cases h : ℓ' = ℓ
          · subst h; simp; linarith
          · simp [Pi.single_apply, h]
        · simp [hb0]
      have := hφB _ hmem
      rw [map_add, map_smul] at this
      have e : φ ((-(Pi.single ℓ (1 : ℝ)) : Fin L → ℝ), (0 : ℝ)) = -lam ℓ := by
        rw [show ((-(Pi.single ℓ (1 : ℝ)) : Fin L → ℝ), (0 : ℝ)) =
          -((Pi.single ℓ (1 : ℝ) : Fin L → ℝ), (0 : ℝ)) by simp, map_neg]
      rw [e, smul_eq_mul] at this
      exact this
    linarith
  have hμ0 : μ ≤ 0 := by
    apply ray_bound (α := φ b0) (c := c)
    intro s hs
    have hmem : b0 + s • ((0 : Fin L → ℝ), (1 : ℝ)) ∈ Bset := by
      refine ⟨fun ℓ' => by simp [hb0], ?_⟩
      simp [hb0]; linarith
    have := hφB _ hmem
    rw [map_add, map_smul, smul_eq_mul] at this
    exact this
  have hμc : μ * obj N m x ≤ c := by
    apply le_of_forall_pos _ _ (∑ ℓ, lam ℓ - μ)
    intro η hη
    have hmem : ((fun _ => -η), obj N m x + η) ∈ Bset := ⟨fun ℓ => by simp; linarith, by simp; linarith⟩
    have := hφB _ hmem
    rw [hrep] at this
    have e : ∑ ℓ, lam ℓ * (-η) = -(η * ∑ ℓ, lam ℓ) := by rw [Finset.mul_sum, ← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro ℓ _; ring
    rw [e] at this
    nlinarith
  have hA : ∀ y : Fin R → ℝ, (∀ r, 0 < m r → 0 < y r) →
      μ * obj N m x ≤ ∑ ℓ, lam ℓ * g y ℓ + μ * obj N m y := by
    intro y hy
    have hmem : (g y, obj N m y) ∈ Aset := ⟨y, hy, fun ℓ => le_rfl, le_rfl⟩
    have := hφA _ hmem
    rw [hrep] at this
    linarith
  -- Slater: μ < 0
  have hμneg : μ < 0 := by
    rcases eq_or_lt_of_le hμ0 with h | h
    · exfalso
      have h1 := hA y0 hy0p
      rw [h, zero_mul, zero_mul, add_zero] at h1
      have hgn : ∀ ℓ, g y0 ℓ < 0 := fun ℓ => by simp only [hg]; linarith [hy0f ℓ]
      have hle : ∀ ℓ ∈ univ, lam ℓ * g y0 ℓ ≤ 0 :=
        fun ℓ _ => mul_nonpos_of_nonneg_of_nonpos (hlam0 ℓ) (hgn ℓ).le
      have hsum0 : ∑ ℓ, lam ℓ * g y0 ℓ = 0 := le_antisymm (Finset.sum_nonpos hle) h1
      have hall := (Finset.sum_eq_zero_iff_of_nonpos hle).1 hsum0
      have hlamz : ∀ ℓ, lam ℓ = 0 := by
        intro ℓ
        have := hall ℓ (Finset.mem_univ ℓ)
        rcases mul_eq_zero.1 this with h' | h'
        · exact h'
        · exact absurd h' (hgn ℓ).ne
      have hb := hφB b0 hb0B
      rw [show b0 = (b0.1, b0.2) from rfl, hrep] at hb
      simp only [hlamz, zero_mul, Finset.sum_const_zero, h, zero_add] at hb
      have ha := hφA (g y0, obj N m y0) ⟨y0, hy0p, fun ℓ => le_rfl, le_rfl⟩
      rw [hrep] at ha
      simp only [hlamz, zero_mul, Finset.sum_const_zero, h, zero_add] at ha
      linarith
    · exact h
  -- the multipliers
  set p : Fin L → ℝ := fun ℓ => lam ℓ / (-μ) with hp
  have hνpos : 0 < -μ := by linarith
  have hp0 : ∀ ℓ, 0 ≤ p ℓ := fun ℓ => div_nonneg (hlam0 ℓ) hνpos.le
  have hLag : ∀ y : Fin R → ℝ, (∀ r, 0 < m r → 0 < y r) →
      obj N m y - ∑ ℓ, p ℓ * g y ℓ ≤ obj N m x := by
    intro y hy
    have h1 := hA y hy
    have e : ∑ ℓ, p ℓ * g y ℓ = (∑ ℓ, lam ℓ * g y ℓ) / (-μ) := by
      rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro ℓ _; simp only [hp]; ring
    rw [e]
    have : obj N m y * (-μ) - ∑ ℓ, lam ℓ * g y ℓ ≤ obj N m x * (-μ) := by linarith
    have h2 : (obj N m y - (∑ ℓ, lam ℓ * g y ℓ) / (-μ)) * (-μ) ≤ obj N m x * (-μ) := by
      rw [sub_mul, div_mul_cancel₀ _ hνpos.ne']; exact this
    exact le_of_mul_le_mul_right h2 hνpos
  -- complementary slackness
  have hgx : ∀ ℓ, g x ℓ ≤ 0 := fun ℓ => by simp only [hg, load]; linarith [hx.2.2.1 ℓ]
  have hcs : ∀ ℓ, p ℓ * g x ℓ = 0 := by
    have h1 := hLag x hx.2.1
    have hle : ∀ ℓ ∈ univ, p ℓ * g x ℓ ≤ 0 :=
      fun ℓ _ => mul_nonpos_of_nonneg_of_nonpos (hp0 ℓ) (hgx ℓ)
    have hsum0 : ∑ ℓ, p ℓ * g x ℓ = 0 := le_antisymm (Finset.sum_nonpos hle) (by linarith)
    intro ℓ
    exact (Finset.sum_eq_zero_iff_of_nonpos hle).1 hsum0 ℓ (Finset.mem_univ ℓ)
  refine ⟨p, hp0, fun ℓ => ?_, fun r hr => ?_⟩
  · have := hcs ℓ
    simp only [hg, load] at this
    linear_combination -this
  · -- stationarity in coordinate r
    have hxr := hx.2.1 r hr
    apply one_dim (N.κ r) (x r) (∑ ℓ, N.H ℓ r * p ℓ) (hκ r) hxr
    intro s hs
    set y := Function.update x r s with hy
    have hyp : ∀ r', 0 < m r' → 0 < y r' := by
      intro r' h'
      by_cases hrr : r' = r
      · subst hrr; simp [hy, hs]
      · simp [hy, hrr, hx.2.1 r' h']
    have h1 := hLag y hyp
    have hxeq : obj N m x - ∑ ℓ, p ℓ * g x ℓ = obj N m x := by
      rw [Finset.sum_eq_zero (fun ℓ _ => hcs ℓ), sub_zero]
    have hdo : obj N m y - obj N m x = N.κ r * (m r : ℝ) * (Real.log s - Real.log (x r)) := by
      unfold obj
      rw [← Finset.sum_sub_distrib, Finset.sum_eq_single r]
      · simp [hy]; ring
      · intro r' _ hne; simp [hy, hne]
      · intro h; exact absurd (Finset.mem_univ r) h
    have hdg : ∑ ℓ, p ℓ * g y ℓ - ∑ ℓ, p ℓ * g x ℓ =
        (m r : ℝ) * (s - x r) * ∑ ℓ, N.H ℓ r * p ℓ := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ℓ _
      have : g y ℓ - g x ℓ = N.H ℓ r * (m r : ℝ) * (s - x r) := by
        simp only [hg, load]
        rw [sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib, Finset.sum_eq_single r]
        · simp [hy]; ring
        · intro r' _ hne; simp [hy, hne]
        · intro h; exact absurd (Finset.mem_univ r) h
      rw [← mul_sub, this]; ring
    have hmr : (0 : ℝ) < m r := by exact_mod_cast hr
    have key : (m r : ℝ) * (N.κ r * (Real.log s - Real.log (x r))) ≤
        (m r : ℝ) * ((∑ ℓ, N.H ℓ r * p ℓ) * (s - x r)) := by
      have : obj N m y - obj N m x - (∑ ℓ, p ℓ * g y ℓ - ∑ ℓ, p ℓ * g x ℓ) ≤ 0 := by linarith
      rw [hdo, hdg] at this
      nlinarith
    exact le_of_mul_le_mul_left key hmr

end HTInsensBWEq5

open HTInsensBW.PhaseType HTInsensBWEq5

theorem solution {L R : ℕ} (N : BWNetwork L R)
    (hH01 : ∀ ℓ r, N.H ℓ r = 0 ∨ N.H ℓ r = 1) (hroute : ∀ r, ∃ ℓ, N.H ℓ r = 1)
    (hC : ∀ ℓ, 0 < N.C ℓ) (hκ : ∀ r, 0 < N.κ r) :
    ∀ m : Fin R → ℕ, (∃! x, IsWPFAllocation N m x) ∧
      ∀ x, IsWPFAllocation N m x → ∃ p, IsKKTMultiplier N m x p := by
  intro m
  refine ⟨?_, fun x hx => kkt_of_wpf N hH01 hC hκ m x hx⟩
  obtain ⟨x, hx⟩ := exists_wpf N hH01 hroute hC hκ m
  exact ⟨x, hx, fun x' hx' => unique_wpf N hκ m x' x hx' hx⟩
