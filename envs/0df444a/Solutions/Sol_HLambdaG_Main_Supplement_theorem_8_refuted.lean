-- Prove2me | solution 1 for HLambdaG.Main.Supplement.theorem_8_refuted
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:26:30.30296+00:00
-- url     : https://prove2.me/submissions/4b69dc10-b8e8-40f3-ad44-b34f531cf895

import Mathlib
import Definitions.Def_HLambdaG_Main_Supplement_FCLTExamples

open scoped NNReal

open HLambdaG
open HLambdaG.Main
open HLambdaG.Main.Supplement

open Filter Topology MeasureTheory

/-- Refutation of Theorem 8 under its printed assumptions (33),(34), with λ = g = h = 1.
T_k = k, S_k = √k + 1, f_k = 2k on [k + √k, k + √k + 1], zero elsewhere.
Every f_k is nonnegative and integrable, and S_k/T_k → 0. The source's AVERAGES
(1), used literally in (27), give G_n → 0, T¹_n → 0, but H_n → -2√t uniformly on
compact time intervals. Thus the claimed relation (30), H = G - hT = 0, is false.
The deterministic continuous limit also witnesses failure of the claimed limit law. -/
theorem solution :
    (∀ k : ℕ, (∀ t : ℝ, 0 ≤ delayedRate k t) ∧
      Integrable (delayedRate k) ∧
      (∀ t : ℝ, t ∉ Set.Icc (k : ℝ) ((k : ℝ) + (Real.sqrt k + 1)) →
        delayedRate k t = 0) ∧
      (∀ t : ℝ≥0, delayedF k t = ∫ v in Set.Icc (0 : ℝ) t, delayedRate k v) ∧
      Tendsto (delayedF k) atTop (𝓝 (2 * k : ℝ))) ∧
    Tendsto (fun k : ℕ => (Real.sqrt k + 1) / (k : ℝ)) atTop (𝓝 0) ∧
    CompactConvergence (diffusion delayedG) (fun _ => 0) ∧
    CompactConvergence (diffusion integerT) (fun _ => 0) ∧
    CompactConvergence (diffusion delayedH) (fun t => -2 * Real.sqrt t) ∧
    (-2 * Real.sqrt (1 : ℝ) ≠ (0 : ℝ) - 1 * 0) := by
      have hinvsqrt : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp <| Real.tendsto_sqrt_atTop.comp <| tendsto_natCast_atTop_atTop
      have key : ∀ (f : ℕ → ℝ≥0 → ℝ) (g : ℝ≥0 → ℝ) (C : ℝ),
          (∀ n : ℕ, 1 ≤ n → ∀ t, |f n t - g t| ≤ C / Real.sqrt n) → CompactConvergence f g := by
        intro f g C hC a ε hε
        have h1 : Tendsto (fun n : ℕ => C * (Real.sqrt n)⁻¹) atTop (𝓝 0) := by
          simpa using hinvsqrt.const_mul C
        filter_upwards [h1.eventually (gt_mem_nhds hε), eventually_ge_atTop 1] with n hn hn1
        intro t _
        exact lt_of_le_of_lt (hC n hn1 t) (by simpa [div_eq_mul_inv] using hn)
      have hsum : ∀ m : ℕ, ∑ k ∈ Finset.Icc 1 m, (2 * k : ℝ) = m * (m + 1) := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          rw [Finset.sum_Icc_succ_top (by omega), ih]
          push_cast; ring
      -- diffusion identity
      have hdiff : ∀ (f : ℝ≥0 → ℝ) (n : ℕ) (t : ℝ≥0), 1 ≤ n →
          diffusion f n t = (f ((n : ℝ≥0) * t) - ((n : ℝ≥0) * t : ℝ≥0)) / Real.sqrt n := by
        intro f n t _
        simp [diffusion]
      have alg : ∀ (x d T : ℝ), 1 ≤ x → -2 ≤ d → d ≤ 2 → T ≤ (x^2-x+d)*((x^2-x+d)+1) →
            (x^2-x+d)*((x^2-x+d)+1) - 2*(x^2-x+d) ≤ T → |T - (x^2)^2 + 2*x*x^2| ≤ 10 * x^2 := by
        intro x d T hx hd1 hd2 hup hlow
        have hu : 0 ≤ x^2 - x := by nlinarith
        have h1 := mul_nonneg (by linarith : (0:ℝ) ≤ d + 2) hu
        have h2 := mul_nonneg (by linarith : (0:ℝ) ≤ 2 - d) hu
        have h3 := mul_nonneg (by linarith : (0:ℝ) ≤ d + 2) (by linarith : (0:ℝ) ≤ 2 - d)
        have h4 : 1 ≤ x^2 := by nlinarith
        rw [abs_le]; constructor <;> nlinarith
      have alg2 : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → |0 - (x^2)^2 + 2*x*x^2| ≤ 10 * x^2 := by
        intro x hx0 hx1
        have h1 : 0 ≤ x^2 := by positivity
        have h2 : x^2 ≤ x := by nlinarith
        rw [abs_le]; constructor <;> nlinarith
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro k
        set a : ℝ := (k : ℝ) + Real.sqrt k with ha
        have ha0 : 0 ≤ a := by positivity
        have hind : delayedRate k = Set.indicator (Set.Icc a (a + 1)) (fun _ => (2 * k : ℝ)) := by
          funext t
          simp [delayedRate, Set.indicator, Set.mem_Icc, ha]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro t
          unfold delayedRate
          split_ifs <;> positivity
        · rw [hind, integrable_indicator_iff measurableSet_Icc]
          exact continuous_const.integrableOn_Icc
        · intro t ht
          unfold delayedRate
          rw [if_neg]
          rintro ⟨h1, h2⟩
          apply ht
          constructor
          · nlinarith [Real.sqrt_nonneg (k : ℝ)]
          · linarith
        · intro t
          rw [hind, integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
            setIntegral_const, Set.Icc_inter_Icc, measureReal_def, Real.volume_Icc,
            ENNReal.toReal_ofReal', smul_eq_mul]
          unfold delayedF
          rw [max_eq_left ha0]
          have e : (t:ℝ) - k - Real.sqrt k = t - a := by rw [ha]; ring
          rw [e]
          rcases le_total (t : ℝ) a with h' | h'
          · have h1 : max 0 ((t:ℝ) - a) = 0 := max_eq_left (by linarith)
            have h2 : min (a+1) (t:ℝ) = t := min_eq_right (by linarith)
            have h3 : max ((t:ℝ) - a) 0 = 0 := max_eq_right (by linarith)
            rw [h1, h2, h3]; simp
          · rcases le_total (t : ℝ) (a + 1) with h | h
            · have h1 : max 0 ((t:ℝ) - a) = t - a := max_eq_right (by linarith)
              have h2 : min (a+1) (t:ℝ) = t := min_eq_right (by linarith)
              have h3 : max ((t:ℝ) - a) 0 = t - a := max_eq_left (by linarith)
              have h4 : min 1 ((t:ℝ) - a) = t - a := min_eq_right (by linarith)
              rw [h1, h2, h3, h4]; ring
            · have h1 : max 0 ((t:ℝ) - a) = t - a := max_eq_right (by linarith)
              have h2 : min (a+1) (t:ℝ) = a + 1 := min_eq_left (by linarith)
              have h3 : max (a + 1 - a) 0 = 1 := by rw [max_eq_left (by linarith)]; ring
              have h4 : min 1 ((t:ℝ) - a) = 1 := min_eq_left (by linarith)
              rw [h1, h2, h3, h4]; ring
        · apply tendsto_const_nhds.congr'
          filter_upwards [eventually_ge_atTop (⟨a + 1, by positivity⟩ : ℝ≥0)] with t ht
          have ht' : a + 1 ≤ (t : ℝ) := by exact_mod_cast ht
          unfold delayedF
          rw [max_eq_right (by linarith), min_eq_left (by linarith)]
          ring
      · have h2 : Tendsto (fun k : ℕ => (Real.sqrt k)⁻¹ + 1 / (k : ℝ)) atTop (𝓝 0) := by
          simpa using hinvsqrt.add tendsto_one_div_atTop_nhds_zero_nat
        apply h2.congr'
        filter_upwards [eventually_ge_atTop 1] with k hk
        rw [add_div, Real.sqrt_div_self', one_div, one_div]
      · apply key _ _ 1
        intro n hn t
        rw [hdiff _ _ _ hn]
        set s : ℝ≥0 := (n : ℝ≥0) * t
        have hG : |delayedG s - s| ≤ 1 := by
          have hm1 : ((⌊s⌋₊ : ℝ≥0) : ℝ) ≤ (s : ℝ) := by exact_mod_cast Nat.floor_le (by positivity)
          have hm2 : (s : ℝ) < ((⌊s⌋₊ : ℝ≥0) : ℝ) + 1 := by exact_mod_cast Nat.lt_floor_add_one s
          push_cast at hm1 hm2
          unfold delayedG
          rw [hsum]
          rcases eq_or_lt_of_le (NNReal.coe_nonneg s) with h0 | h0
          · rw [← h0]; simp
          · rw [abs_le]
            set m : ℝ := (⌊s⌋₊ : ℝ)
            have hm0 : 0 ≤ m := by positivity
            constructor
            · rw [le_sub_iff_add_le, le_div_iff₀ h0]; nlinarith
            · rw [sub_le_iff_le_add, div_le_iff₀ h0]; nlinarith
        have hn' : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
        simp only [sub_zero]
        rw [abs_div, abs_of_pos hn']
        gcongr
      · apply key _ _ 1
        intro n hn t
        rw [hdiff _ _ _ hn]
        set s : ℝ≥0 := (n : ℝ≥0) * t
        have hT : |integerT s - s| ≤ 1 := by
          have hm1 : ((⌊s⌋₊ : ℝ≥0) : ℝ) ≤ (s : ℝ) := by exact_mod_cast Nat.floor_le (by positivity)
          have hm2 : (s : ℝ) < ((⌊s⌋₊ : ℝ≥0) : ℝ) + 1 := by exact_mod_cast Nat.lt_floor_add_one s
          push_cast at hm1 hm2
          unfold integerT
          rw [abs_le]; constructor <;> linarith
        have hn' : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
        simp only [sub_zero]
        rw [abs_div, abs_of_pos hn']
        gcongr
      · have hH : ∀ s : ℝ≥0, |delayedH s - s + 2 * Real.sqrt s| ≤ 10 := by
          intro s
          classical
          have hm1 : ((⌊s⌋₊ : ℝ≥0) : ℝ) ≤ (s : ℝ) := by exact_mod_cast Nat.floor_le (by positivity)
          have hm2 : (s : ℝ) < ((⌊s⌋₊ : ℝ≥0) : ℝ) + 1 := by exact_mod_cast Nat.lt_floor_add_one s
          push_cast at hm1 hm2
          have hs0 : (0:ℝ) ≤ s := NNReal.coe_nonneg s
          let P : ℕ → Prop := fun k => (k:ℝ) + Real.sqrt k ≤ s
          set A := Nat.findGreatest P ⌊s⌋₊ with hA
          have hPA : (A:ℝ) + Real.sqrt A ≤ s :=
            Nat.findGreatest_spec (P := P) (Nat.zero_le _) (by simp [P, hs0])
          have hAle : A ≤ ⌊s⌋₊ := Nat.findGreatest_le _
          have hnot : ∀ k, A < k → k ≤ ⌊s⌋₊ → ¬ ((k:ℝ) + Real.sqrt k ≤ s) :=
            fun k h1 h2 => Nat.findGreatest_is_greatest h1 h2
          have hnext : (s:ℝ) < ((A:ℝ) + 1) + Real.sqrt ((A:ℝ) + 1) := by
            by_cases h : A + 1 ≤ ⌊s⌋₊
            · have := hnot (A+1) (by omega) h
              push_cast at this
              linarith
            · have h' : (⌊s⌋₊ : ℝ) ≤ A := by exact_mod_cast (by omega : ⌊s⌋₊ ≤ A)
              have := Real.sqrt_nonneg ((A:ℝ) + 1)
              linarith
          have hF_full : ∀ k : ℕ, (k:ℝ) + Real.sqrt k + 1 ≤ s → delayedF k s = 2 * k := by
            intro k hk; unfold delayedF
            rw [max_eq_right (by linarith), min_eq_left (by linarith)]; ring
          have hF_zero : ∀ k : ℕ, (s:ℝ) < k + Real.sqrt k → delayedF k s = 0 := by
            intro k hk; unfold delayedF
            rw [max_eq_left (by linarith)]; simp
          have hF_bd : ∀ k : ℕ, 0 ≤ delayedF k s ∧ delayedF k s ≤ 2 * k := by
            intro k; unfold delayedF
            have h0 : 0 ≤ min 1 (max 0 ((s:ℝ) - k - Real.sqrt k)) := le_min zero_le_one (le_max_left _ _)
            have h1 : min 1 (max 0 ((s:ℝ) - k - Real.sqrt k)) ≤ 1 := min_le_left _ _
            have hk : (0:ℝ) ≤ 2 * k := by positivity
            constructor
            · positivity
            · nlinarith
          set S := Finset.Icc 1 ⌊s⌋₊
          have hup : ∑ k ∈ S, delayedF k s ≤ (A:ℝ) * (A + 1) := by
            calc ∑ k ∈ S, delayedF k s ≤ ∑ k ∈ S, (if k ≤ A then (2 * k : ℝ) else 0) := by
                  apply Finset.sum_le_sum
                  intro k hk
                  split_ifs with h
                  · exact (hF_bd k).2
                  · have hk2 : k ≤ ⌊s⌋₊ := (Finset.mem_Icc.1 hk).2
                    rw [hF_zero k (lt_of_not_ge (hnot k (by omega) hk2))]
              _ = ∑ k ∈ S.filter (fun k => k ≤ A), (2 * k : ℝ) := by rw [Finset.sum_filter]
              _ = (A:ℝ) * (A + 1) := by
                  have : S.filter (fun k => k ≤ A) = Finset.Icc 1 A := by
                    ext k; simp only [S, Finset.mem_filter, Finset.mem_Icc]; omega
                  rw [this, hsum]
          have hlow : (A:ℝ) * (A + 1) - 2 * A ≤ ∑ k ∈ S, delayedF k s := by
            calc (A:ℝ) * (A + 1) - 2 * A ≤ ∑ k ∈ S, (if k ≤ A then (2 * k : ℝ) else 0)
                    - ∑ k ∈ S, (if k = A then (2 * k : ℝ) else 0) := by
                  have e1 : ∑ k ∈ S, (if k ≤ A then (2 * k : ℝ) else 0) = (A:ℝ) * (A + 1) := by
                    rw [← Finset.sum_filter]
                    have : S.filter (fun k => k ≤ A) = Finset.Icc 1 A := by
                      ext k; simp only [S, Finset.mem_filter, Finset.mem_Icc]; omega
                    rw [this, hsum]
                  have e2 : ∑ k ∈ S, (if k = A then (2 * k : ℝ) else 0) ≤ 2 * A := by
                    rw [Finset.sum_ite_eq']
                    split_ifs
                    · exact le_refl _
                    · positivity
                  linarith
              _ = ∑ k ∈ S, ((if k ≤ A then (2 * k : ℝ) else 0) - (if k = A then (2 * k : ℝ) else 0)) := by
                  rw [Finset.sum_sub_distrib]
              _ ≤ ∑ k ∈ S, delayedF k s := by
                  apply Finset.sum_le_sum
                  intro k hk
                  rcases lt_trichotomy k A with h | h | h
                  · rw [if_pos h.le, if_neg h.ne, hF_full k]
                    · simp
                    · have hk1 : (k:ℝ) + 1 ≤ A := by exact_mod_cast h
                      have : Real.sqrt k ≤ Real.sqrt A := Real.sqrt_le_sqrt (by linarith)
                      linarith
                  · rw [if_pos h.le, if_pos h]; simp [(hF_bd k).1]
                  · rw [if_neg (by omega), if_neg h.ne']; simp [(hF_bd k).1]
          set T := ∑ k ∈ S, delayedF k s
          have hHT : delayedH s = T / s := rfl
          set x := Real.sqrt (s:ℝ) with hx
          have hx0 : 0 ≤ x := Real.sqrt_nonneg _
          have hxx : x ^ 2 = s := Real.sq_sqrt hs0
          have hA0 : (0:ℝ) ≤ A := by positivity
          set r := Real.sqrt (A:ℝ) with hr
          have hr0 : 0 ≤ r := Real.sqrt_nonneg _
          have hrr : r ^ 2 = A := Real.sq_sqrt hA0
          set q := Real.sqrt ((A:ℝ) + 1) with hq
          have hq0 : 0 ≤ q := Real.sqrt_nonneg _
          have hqq : q ^ 2 = A + 1 := Real.sq_sqrt (by linarith)
          have hAs : (A:ℝ) ≤ s := by linarith
          have hqx : q ≤ x + 1 := by
            by_contra h; push Not at h
            nlinarith [mul_self_lt_mul_self (by linarith : 0 ≤ x + 1) h]
          have hAlo : x ^ 2 - x - 2 ≤ A := by linarith
          have hrx : x - 2 ≤ r := by
            by_contra h; push Not at h
            nlinarith [mul_self_lt_mul_self hr0 h]
          have hAhi : (A:ℝ) ≤ x ^ 2 - x + 2 := by linarith
          rcases eq_or_lt_of_le hs0 with h0 | h0
          · rw [hHT, ← h0, hx, ← h0]; simp
          have hkey : |T - (s:ℝ) ^ 2 + 2 * x * (s:ℝ)| ≤ 10 * (s:ℝ) := by
            rcases lt_or_ge (s:ℝ) 1 with hs1 | hs1
            · have hA00 : A = 0 := by
                have : (A:ℝ) < 1 := by linarith
                have : A < 1 := by exact_mod_cast this
                omega
              have hT0 : T = 0 := by
                rw [hA00] at hup hlow; push_cast at hup hlow; linarith
              have hx1 : x ≤ 1 := by
                have := Real.sqrt_le_sqrt hs1.le; rwa [Real.sqrt_one] at this
              rw [hT0, ← hxx]
              exact alg2 x hx0 hx1
            · have hx1 : 1 ≤ x := by
                have := Real.sqrt_le_sqrt hs1; rwa [Real.sqrt_one] at this
              have hA' : (x^2 - x + ((A:ℝ) - (x^2-x))) = A := by ring
              have := alg x ((A:ℝ) - (x^2 - x)) T hx1 (by linarith) (by linarith)
                (by rw [hA']; exact hup) (by rw [hA']; exact hlow)
              rw [← hxx]; exact this
          rw [hHT]
          have e : T / (s:ℝ) - (s:ℝ) + 2 * x = (T - (s:ℝ) ^ 2 + 2 * x * (s:ℝ)) / (s:ℝ) := by
            field_simp
          rw [e, abs_div, abs_of_pos h0, div_le_iff₀ h0]
          exact hkey
        apply key _ _ 10
        intro n hn t
        rw [hdiff _ _ _ hn]
        have hn' : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
        have hs : Real.sqrt (((n : ℝ≥0) * t : ℝ≥0) : ℝ) = Real.sqrt n * Real.sqrt t := by
          push_cast
          exact Real.sqrt_mul (by positivity) _
        have e : (delayedH ((n : ℝ≥0) * t) - (((n : ℝ≥0) * t : ℝ≥0) : ℝ)) / Real.sqrt n - -2 * Real.sqrt t
            = (delayedH ((n : ℝ≥0) * t) - (((n : ℝ≥0) * t : ℝ≥0) : ℝ)
                + 2 * Real.sqrt (((n : ℝ≥0) * t : ℝ≥0) : ℝ)) / Real.sqrt n := by
          rw [hs]; field_simp; ring
        rw [e, abs_div, abs_of_pos hn']
        gcongr
        exact hH _
      · simp
