-- Prove2me | solution 1 for HardyFiveAxioms.dof_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T19:22:49.49336+00:00
-- url     : https://prove2.me/submissions/04de3de3-ddf2-444c-b4e6-7f7910155ae8

import Mathlib

noncomputable def D : ℕ → ℝ → ℝ → ℝ
  | 0, c, x => x ^ c
  | s+1, c, x => D s c (x+1) - D s c x

noncomputable def P : ℕ → ℝ → ℝ
  | 0, _ => 1
  | s+1, c => c * P s (c-1)

def DK (K : ℕ → ℕ) : ℕ → ℕ → ℤ
  | 0, n => K n
  | s+1, n => DK K s (n+1) - DK K s n

lemma D_deriv (s : ℕ) : ∀ c x, 0 < x → HasDerivAt (D s c) (c * D s (c-1) x) x := by
  induction s with
  | zero =>
    intro c x hx
    have : D 0 c = fun y => y ^ c := by funext y; simp [D]
    rw [this]; simpa [D] using Real.hasDerivAt_rpow_const (p := c) (Or.inl hx.ne')
  | succ s ih =>
    intro c x hx
    have h1 := (ih c (x+1) (by linarith)).comp_add_const x 1
    have h2 := ih c x hx
    have : D (s+1) c = fun y => D s c (y+1) - D s c y := by funext y; simp [D]
    rw [this]
    have e : c * D (s+1) (c-1) x = c * D s (c-1) (x+1) - c * D s (c-1) x := by
      simp only [D]; ring
    rw [e]; exact h1.sub h2

lemma D_mvt (s : ℕ) : ∀ (c x : ℝ), 0 < x → ∃ ξ, x ≤ ξ ∧ ξ ≤ x + s ∧ D s c x = P s c * ξ ^ (c - s) := by
  induction s with
  | zero => intro c x hx; exact ⟨x, le_rfl, by simp, by simp [D, P]⟩
  | succ s ih =>
    intro c x hx
    obtain ⟨η, hη1, hη2⟩ := exists_hasDerivAt_eq_slope (D s c) (fun y => c * D s (c-1) y)
      (lt_add_one x)
      (fun y hy => (D_deriv s c y (by linarith [hy.1])).continuousAt.continuousWithinAt)
      (fun y hy => D_deriv s c y (by linarith [hy.1]))
    obtain ⟨ξ, h1, h2, h3⟩ := ih (c-1) η (by linarith [hη1.1])
    refine ⟨ξ, by linarith [hη1.1], by push_cast; linarith [hη1.2], ?_⟩
    have e : D (s+1) c x = c * D s (c-1) η := by
      simp only [D]; rw [hη2]; simp
    rw [e, h3]; simp only [P]; push_cast
    rw [show c - 1 - (s:ℝ) = c - ((s:ℝ) + 1) by ring]; ring

lemma P_pos (s : ℕ) : ∀ c : ℝ, (s:ℝ) - 1 < c → 0 < P s c := by
  induction s with
  | zero => intro c _; simp [P]
  | succ s ih =>
    intro c hc; push_cast at hc
    simp only [P]
    exact mul_pos (by have : (0:ℝ) ≤ s := by positivity
                      linarith) (ih _ (by linarith))

lemma DK_eq (K : ℕ → ℕ) (c : ℝ) (hK : ∀ m, 1 ≤ m → (K m : ℝ) = (m:ℝ) ^ c) (s : ℕ) :
    ∀ n, 1 ≤ n → (DK K s n : ℝ) = D s c n := by
  induction s with
  | zero => intro n hn; simp [DK, D, hK n hn]
  | succ s ih =>
    intro n hn
    simp only [DK, D]; push_cast
    rw [ih n hn, ih (n+1) (by omega)]; push_cast; ring_nf

theorem solution (K : ℕ → ℕ)
    (hinc : ∀ N : ℕ, 1 ≤ N → K N + 1 ≤ K (N + 1))
    (hmul : ∀ NA NB : ℕ, 1 ≤ NA → 1 ≤ NB → K (NA * NB) = K NA * K NB) :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ N : ℕ, 1 ≤ N → K N = N ^ r := by
  have hK1 : K 1 = 1 := by
    have h := hmul 1 1 le_rfl le_rfl
    have h2 := hmul 2 1 (by norm_num) le_rfl
    have h3 := hinc 1 le_rfl
    simp only [mul_one, Nat.reduceAdd] at h h2 h3
    rcases Nat.eq_zero_or_pos (K 1) with h0 | h0
    · rw [h0] at h2 h3; simp at h2; omega
    · nlinarith
  have hmono : ∀ m n, 1 ≤ m → m < n → K m < K n := by
    intro m n hm hmn
    induction n, hmn using Nat.le_induction with
    | base => show K m < K (m+1); have := hinc m hm; omega
    | succ n hn ih => show K m < K (n+1); have := hinc n (by omega); omega
  have hpow : ∀ x k, 1 ≤ x → K (x ^ k) = K x ^ k := by
    intro x k hx
    induction k with
    | zero => simp [hK1]
    | succ k ih => rw [pow_succ, hmul _ _ (Nat.one_le_pow _ _ hx) hx, ih, pow_succ]
  have hge2 : ∀ n, 2 ≤ n → 2 ≤ K n := by
    intro n hn; have := hmono 1 n le_rfl (by omega); omega
  have hlog : ∀ m, 1 ≤ m → Real.log (K m) * Real.log 2 = Real.log m * Real.log (K 2) := by
    intro m hm
    rcases Nat.lt_or_ge m 2 with h | h
    · have : m = 1 := by omega
      subst this; simp [hK1]
    set A := Real.log m
    set B := Real.log 2
    set C := Real.log (K m)
    set E := Real.log (K 2)
    have hB : 0 < B := Real.log_pos (by norm_num)
    have hE : 0 < E := Real.log_pos (by have := hge2 2 le_rfl; exact_mod_cast (by omega : 1 < K 2))
    have key : ∀ a : ℕ, (a:ℝ) * (C*B - A*E) < B*E ∧ (a:ℝ) * (A*E - C*B) < B*E := by
      intro a
      set b := Nat.log 2 (m ^ a)
      have hma : m ^ a ≠ 0 := by positivity
      have l1 : 2 ^ b ≤ m ^ a := Nat.pow_log_le_self 2 hma
      have l2 : m ^ a < 2 ^ (b+1) := Nat.lt_pow_succ_log_self (by norm_num) _
      have k1 : K 2 ^ b ≤ K m ^ a := by
        rw [← hpow 2 b (by norm_num), ← hpow m a hm]
        rcases l1.lt_or_eq with h' | h'
        · exact (hmono _ _ (Nat.one_le_pow _ _ (by norm_num)) h').le
        · rw [h']
      have k2 : K m ^ a < K 2 ^ (b+1) := by
        rw [← hpow 2 _ (by norm_num), ← hpow m a hm]
        exact hmono _ _ (Nat.one_le_pow _ _ hm) l2
      have r1 : (b:ℝ) * B ≤ a * A := by
        have : ((2:ℕ):ℝ) ^ b ≤ ((m:ℕ):ℝ) ^ a := by exact_mod_cast l1
        have := Real.log_le_log (by positivity) this
        simpa [Real.log_pow] using this
      have r2 : (a:ℝ) * A < (b+1) * B := by
        have : ((m:ℕ):ℝ) ^ a < ((2:ℕ):ℝ) ^ (b+1) := by exact_mod_cast l2
        have := Real.log_lt_log (by have : (0:ℝ) < m := by exact_mod_cast hm
                                    positivity) this
        simpa [Real.log_pow] using this
      have hKm : (0:ℝ) < K m := by have := hge2 m h; exact_mod_cast (by omega : 0 < K m)
      have hK2 : (0:ℝ) < K 2 := by have := hge2 2 le_rfl; exact_mod_cast (by omega : 0 < K 2)
      have r3 : (b:ℝ) * E ≤ a * C := by
        have : ((K 2:ℕ):ℝ) ^ b ≤ ((K m:ℕ):ℝ) ^ a := by exact_mod_cast k1
        have := Real.log_le_log (by positivity) this
        simpa [Real.log_pow] using this
      have r4 : (a:ℝ) * C < (b+1) * E := by
        have : ((K m:ℕ):ℝ) ^ a < ((K 2:ℕ):ℝ) ^ (b+1) := by exact_mod_cast k2
        have := Real.log_lt_log (by positivity) this
        simpa [Real.log_pow] using this
      constructor
      · nlinarith [mul_lt_mul_of_pos_right r4 hB, mul_le_mul_of_nonneg_right r1 hE.le]
      · nlinarith [mul_lt_mul_of_pos_right r2 hE, mul_le_mul_of_nonneg_right r3 hB.le]
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨a, ha⟩ := exists_nat_gt (B*E / (A*E - C*B))
      have := (key a).2
      rw [div_lt_iff₀ (by linarith)] at ha; linarith
    · obtain ⟨a, ha⟩ := exists_nat_gt (B*E / (C*B - A*E))
      have := (key a).1
      rw [div_lt_iff₀ (by linarith)] at ha; linarith
  set c := Real.log (K 2) / Real.log 2 with hc
  have hB : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKc : ∀ m, 1 ≤ m → (K m : ℝ) = (m:ℝ) ^ c := by
    intro m hm
    have hKm : (0:ℝ) < K m := by
      rcases eq_or_lt_of_le hm with h | h
      · subst h; simp [hK1]
      · have := hmono 1 m le_rfl h; exact_mod_cast (by omega : 0 < K m)
    rw [Real.rpow_def_of_pos (by exact_mod_cast hm), hc, mul_div_assoc', ← hlog m hm,
      mul_div_assoc, div_self hB.ne', mul_one, Real.exp_log hKm]
  have hcpos : 0 < c := by
    have := hge2 2 le_rfl
    exact div_pos (Real.log_pos (by exact_mod_cast (by omega : 1 < K 2))) hB
  set r := ⌊c⌋₊
  by_cases hcr : c = r
  · refine ⟨r, ?_, ?_⟩
    · by_contra h0; have : r = 0 := by omega
      rw [this] at hcr; simp at hcr; linarith
    · intro N hN
      have := hKc N hN
      rw [hcr, Real.rpow_natCast] at this
      exact_mod_cast this
  exfalso
  have hr1 : (r:ℝ) < c := lt_of_le_of_ne (Nat.floor_le hcpos.le) (Ne.symm hcr)
  have hr2 : c < (r:ℝ) + 1 := Nat.lt_floor_add_one c
  have hP := P_pos (r+1) c (by push_cast; linarith)
  have hneg : 0 < ((r+1:ℕ):ℝ) - c := by push_cast; linarith
  have ht := (tendsto_rpow_neg_atTop hneg).comp tendsto_natCast_atTop_atTop
  have ev := (ht.eventually (gt_mem_nhds (inv_pos.mpr hP))).and (Filter.eventually_ge_atTop 1)
  obtain ⟨n, hn1, hn2⟩ := ev.exists
  simp only [Function.comp, neg_sub] at hn1
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn2
  obtain ⟨ξ, hξ1, _, hξ3⟩ := D_mvt (r+1) c n hnpos
  have hz := DK_eq K c hKc (r+1) n hn2
  have hξpow : ξ ^ (c - ((r+1:ℕ):ℝ)) ≤ (n:ℝ) ^ (c - ((r+1:ℕ):ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hnpos hξ1 (by linarith)
  have hpos : (0:ℝ) < DK K (r+1) n := by
    rw [hz, hξ3]; exact mul_pos hP (Real.rpow_pos_of_pos (by linarith) _)
  have hlt : (DK K (r+1) n : ℝ) < 1 := by
    rw [hz, hξ3]
    calc P (r+1) c * ξ ^ (c - ((r+1:ℕ):ℝ)) ≤ P (r+1) c * (n:ℝ) ^ (c - ((r+1:ℕ):ℝ)) :=
          mul_le_mul_of_nonneg_left hξpow hP.le
      _ < P (r+1) c * (P (r+1) c)⁻¹ := mul_lt_mul_of_pos_left hn1 hP
      _ = 1 := mul_inv_cancel₀ hP.ne'
  have a1 : 0 < DK K (r+1) n := by exact_mod_cast hpos
  have a2 : DK K (r+1) n < 1 := by exact_mod_cast hlt
  omega
