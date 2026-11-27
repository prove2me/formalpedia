-- Prove2me | solution 1 for KellyLossNetworks.RevisedDual.Supplement.theorem_6_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:32:50.647779+00:00
-- url     : https://prove2.me/submissions/79d96516-02cb-4ed5-b30f-493ada60ed32

import Mathlib
import Definitions.Def_KellyLossNetworks_RevisedDual_Supplement_Exact

open KellyLossNetworks
open KellyLossNetworks.RevisedDual
open KellyLossNetworks.RevisedDual.Supplement

/-- **Theorem 6.1.** `(d/dν_r) W^π(ν; C) = (1 − L_r^π)(w_r − c_r^π)` (6.2), where
`c_r^π = W^π(ν; C) − W^π(ν; C − Ae_r)` (6.3).

Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
p. 368, Theorem 6.1, (6.2)–(6.3); `W^π` in §6.1, p. 368; `L_r^π` by (1.5), p. 322.

**Formalization Note.** `W^π(ν; C) = revenue A ν (capInt C) w` is the exact expectation of
`Σ_r w_r n_r` under the stationary distribution (1.2); `1 − L_r^π = acceptance`;
`c_r^π = impliedCost`. The derivative is the ordinary derivative of
`t ↦ W^π(ν with ν_r replaced by t; C)` at `t = ν_r`. Rates are positive and the revenues
`w_r` arbitrary reals. When `C − Ae_r` has a negative entry, `1 − L_r^π = 0` and the right side
is `0` whatever value `W^π(ν; C − Ae_r)` is given. -/
theorem solution {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (hν : ∀ r, 0 < ν r) (C : Fin J → ℕ) (w : Fin R → ℝ) (r : Fin R) :
    HasDerivAt (fun t : ℝ => revenue A (Function.update ν r t) (capInt C) w)
      (acceptance A ν (capInt C) r * (w r - impliedCost A ν (capInt C) w r)) (ν r) := by
        classical
        have hwpos : ∀ (v : Fin R → ℝ), (∀ s, 0 < v s) → ∀ n : Fin R → ℕ,
            0 < KellyStochasticNetworks.lossWeight v n := by
          intro v hv n
          exact Finset.prod_pos fun s _ => div_pos (pow_pos (hv s) _) (by positivity)
        have hsum : ∀ (v : Fin R → ℝ), (∀ s, 0 < v s) →
            Summable (KellyStochasticNetworks.lossWeight v) := by
          intro v hv
          have hseries : ∀ s, HasSum (fun n : ℕ => v s ^ n / (n.factorial : ℝ)) (Real.exp (v s)) := by
            intro s
            simpa only [← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (v s)
          have hfinite : ∀ t : Finset (Fin R → ℕ),
              ∑ n ∈ t, KellyStochasticNetworks.lossWeight v n ≤ Real.exp (∑ s, v s) := by
            intro t
            let b : Finset ℕ := t.biUnion (fun n => Finset.univ.image n)
            calc
              ∑ n ∈ t, KellyStochasticNetworks.lossWeight v n ≤
                  ∑ n ∈ Fintype.piFinset (fun _ : Fin R => b), KellyStochasticNetworks.lossWeight v n := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro n hn
                  simp only [Fintype.mem_piFinset]
                  intro s
                  exact Finset.mem_biUnion.mpr ⟨n, hn, Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩⟩
                · intro n _ _
                  exact (hwpos v hv n).le
              _ = ∏ s, ∑ k ∈ b, v s ^ k / (k.factorial : ℝ) := by
                exact Finset.sum_prod_piFinset b (fun s k => v s ^ k / (k.factorial : ℝ))
              _ ≤ ∏ s, Real.exp (v s) := by
                apply Finset.prod_le_prod
                · intro s _
                  exact Finset.sum_nonneg fun n _ => (div_pos (pow_pos (hv s) _) (by positivity)).le
                · intro s _
                  rw [← (hseries s).tsum_eq]
                  exact (hseries s).summable.sum_le_tsum b (fun n _ => (div_pos (pow_pos (hv s) _) (by positivity)).le)
              _ = Real.exp (∑ s, v s) := (Real.exp_sum _ _).symm
          exact summable_of_sum_le (fun n => (hwpos v hv n).le) hfinite
        have hscale : ∀ (q : ℝ) (n : Fin R → ℕ),
            KellyStochasticNetworks.lossWeight (fun s => q * ν s) n =
              q ^ (∑ s, n s) * KellyStochasticNetworks.lossWeight ν n := by
          intro q n
          unfold KellyStochasticNetworks.lossWeight
          simp_rw [mul_pow, mul_div_assoc]
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
        have hfac : ∀ (y : ℝ) (n : Fin R → ℕ),
            KellyStochasticNetworks.lossWeight (Function.update ν r y) n =
              y ^ (n r) * (KellyStochasticNetworks.lossWeight ν n / ν r ^ (n r)) := by
          intro y n
          unfold KellyStochasticNetworks.lossWeight
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r),
            ← Finset.mul_prod_erase Finset.univ (fun s => ν s ^ n s / (Nat.factorial (n s) : ℝ))
              (Finset.mem_univ r)]
          rw [Finset.prod_congr rfl (fun s hs => by
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)])]
          simp only [Function.update_self]
          have : ν r ^ n r ≠ 0 := pow_ne_zero _ (hν r).ne'
          field_simp
        have hshift : ∀ m : Fin R → ℕ,
            KellyStochasticNetworks.lossWeight ν (m + Pi.single r 1) * ((m r : ℝ) + 1) =
              KellyStochasticNetworks.lossWeight ν m * ν r := by
          intro m
          unfold KellyStochasticNetworks.lossWeight
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r),
            ← Finset.mul_prod_erase Finset.univ (fun s => ν s ^ m s / (Nat.factorial (m s) : ℝ))
              (Finset.mem_univ r)]
          rw [Finset.prod_congr rfl (fun s hs => by
            rw [Pi.add_apply, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hs), add_zero])]
          simp only [Pi.add_apply, Pi.single_eq_same, Nat.factorial_succ]
          push_cast
          have : ((m r).factorial : ℝ) ≠ 0 := by positivity
          field_simp
          ring
        have hpos_s : ∀ q : ℝ, 0 < q → ∀ s, 0 < q * ν s := fun q hq s => mul_pos hq (hν s)
        have hsumb : ∀ (b : (Fin R → ℕ) → ℝ) (K : ℝ), (∀ n, |b n| ≤ K * 2 ^ (∑ s, n s)) →
            Summable (fun n => b n * KellyStochasticNetworks.lossWeight ν n) := by
          intro b K hb
          refine Summable.of_norm_bounded ((hsum _ (hpos_s 2 two_pos)).mul_left K) (fun n => ?_)
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hwpos ν hν n), hscale, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right (hb n) (hwpos ν hν n).le
        have hderiv : ∀ (b : (Fin R → ℕ) → ℝ) (K : ℝ), 0 ≤ K → (∀ n, |b n| ≤ K * 2 ^ (∑ s, n s)) →
            HasDerivAt (fun y => ∑' n, b n * KellyStochasticNetworks.lossWeight (Function.update ν r y) n)
              (∑' m, b (m + Pi.single r 1) * KellyStochasticNetworks.lossWeight ν m) (ν r) := by
          intro b K hK hb
          have hfun : (fun y => ∑' n, b n * KellyStochasticNetworks.lossWeight (Function.update ν r y) n)
              = fun y => ∑' n, (b n * (KellyStochasticNetworks.lossWeight ν n / ν r ^ (n r))) * y ^ (n r) := by
            funext y
            congr 1
            funext n
            rw [hfac]
            ring
          rw [hfun]
          have hmem : ν r ∈ Set.Ioo (0 : ℝ) (2 * ν r) := ⟨hν r, by linarith [hν r]⟩
          have key := hasDerivAt_tsum_of_isPreconnected
            (u := fun n => (K / ν r) * KellyStochasticNetworks.lossWeight (fun s => 8 * ν s) n)
            (t := Set.Ioo (0 : ℝ) (2 * ν r))
            (g := fun n y => (b n * (KellyStochasticNetworks.lossWeight ν n / ν r ^ (n r))) * y ^ (n r))
            (g' := fun n y => (b n * (KellyStochasticNetworks.lossWeight ν n / ν r ^ (n r))) *
              ((n r : ℝ) * y ^ (n r - 1)))
            (y₀ := ν r) (y := ν r)
            ((hsum _ (hpos_s 8 (by norm_num))).mul_left _) isOpen_Ioo isPreconnected_Ioo
            (fun n y _ => (hasDerivAt_pow (n r) y).const_mul _)
            ?bound hmem ?s0 hmem
          case s0 =>
            refine (hsumb b K hb).congr (fun n => ?_)
            have : ν r ^ n r ≠ 0 := pow_ne_zero _ (hν r).ne'
            field_simp
          case bound =>
            intro n y hy
            have hφ := hwpos ν hν n
            have hk : n r ≤ ∑ s, n s := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
            rcases Nat.eq_zero_or_pos (n r) with h0 | hpos
            · simp only [h0, Nat.cast_zero, zero_mul, mul_zero, norm_zero]
              exact mul_nonneg (div_nonneg hK (hν r).le) (hwpos _ (hpos_s 8 (by norm_num)) n).le
            · obtain ⟨j, hj⟩ : ∃ j, n r = j + 1 := ⟨n r - 1, by omega⟩
              have hnat : 2 ^ (∑ s, n s) * ((j + 1) * 2 ^ j) ≤ 8 ^ (∑ s, n s) := by
                have h1 : j + 1 ≤ 2 ^ (∑ s, n s) :=
                  le_trans (Nat.lt_two_pow_self).le (Nat.pow_le_pow_right (by norm_num) (by omega))
                have h2 : 2 ^ j ≤ 2 ^ (∑ s, n s) := Nat.pow_le_pow_right (by norm_num) (by omega)
                calc 2 ^ (∑ s, n s) * ((j + 1) * 2 ^ j)
                    ≤ 2 ^ (∑ s, n s) * (2 ^ (∑ s, n s) * 2 ^ (∑ s, n s)) := by gcongr
                  _ = 8 ^ (∑ s, n s) := by rw [← mul_pow, ← mul_pow]; norm_num
              have hreal : (2 : ℝ) ^ (∑ s, n s) * (((j : ℝ) + 1) * 2 ^ j) ≤ 8 ^ (∑ s, n s) := by
                exact_mod_cast hnat
              rw [hj, hscale]
              simp only [Nat.add_sub_cancel]
              push_cast
              have hy0 : 0 ≤ y := hy.1.le
              have hy1 : y ≤ 2 * ν r := hy.2.le
              have hνr := hν r
              rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_nonneg (div_nonneg hφ.le (pow_nonneg hνr.le _)),
                abs_of_nonneg (mul_nonneg (by positivity) (pow_nonneg hy0 _))]
              calc |b n| * (KellyStochasticNetworks.lossWeight ν n / ν r ^ (j + 1)) * ((↑j + 1) * y ^ j)
                  ≤ (K * 2 ^ (∑ s, n s)) * (KellyStochasticNetworks.lossWeight ν n / ν r ^ (j + 1)) *
                      ((↑j + 1) * (2 * ν r) ^ j) := by
                    gcongr
                    exact hb n
                _ = K * KellyStochasticNetworks.lossWeight ν n / ν r *
                      (2 ^ (∑ s, n s) * (((j : ℝ) + 1) * 2 ^ j)) := by
                    rw [mul_pow, pow_succ]
                    field_simp
                _ ≤ K * KellyStochasticNetworks.lossWeight ν n / ν r * 8 ^ (∑ s, n s) := by
                    gcongr
                _ = K / ν r * (8 ^ (∑ s, n s) * KellyStochasticNetworks.lossWeight ν n) := by ring
          refine key.congr_deriv ?_
          rw [← (show Function.Injective (fun m : Fin R → ℕ => m + Pi.single r 1) from
            fun a c h => add_right_cancel h).tsum_eq (f := fun n => b n *
              (KellyStochasticNetworks.lossWeight ν n / ν r ^ (n r)) * ((n r : ℝ) * ν r ^ (n r - 1)))]
          · congr 1
            funext m
            have hsh := hshift m
            have hk : (m + Pi.single r 1 : Fin R → ℕ) r = m r + 1 := by simp
            simp only [hk]
            push_cast
            rw [pow_succ]
            have : ν r ^ m r ≠ 0 := pow_ne_zero _ (hν r).ne'
            have : ν r ≠ 0 := (hν r).ne'
            field_simp
            linear_combination (b (m + Pi.single r 1)) * hsh
          · intro n hn
            have hr : n r ≠ 0 := by
              intro h
              apply hn
              simp [h]
            refine ⟨n - Pi.single r 1, ?_⟩
            funext s
            by_cases hs : s = r
            · subst hs
              simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same]
              omega
            · simp [Pi.single_eq_of_ne hs]
        have hstates : ∀ c : Fin J → ℤ, (∀ j, 0 ≤ c j) →
            KellyStochasticNetworks.lossStates A (fun j => (c j).toNat) = stateSpace A c := by
          intro c hc
          ext n
          simp only [KellyStochasticNetworks.lossStates, stateSpace, Set.mem_ofPred_eq]
          refine forall_congr' (fun j => ?_)
          have := hc j
          omega
        have hempty : ∀ c : Fin J → ℤ, ¬ (∀ j, 0 ≤ c j) → ∀ n, n ∉ stateSpace A c := by
          intro c hc n hn
          apply hc
          intro j
          have := hn j
          have : (0 : ℤ) ≤ ((∑ r, A j r * n r : ℕ) : ℤ) := Int.natCast_nonneg _
          omega
        have hPF : ∀ (v : Fin R → ℝ) (c : Fin J → ℤ), partitionFn A v c =
            ∑' n, (stateSpace A c).indicator (KellyStochasticNetworks.lossWeight v) n := by
          intro v c
          unfold partitionFn
          split_ifs with h
          · unfold KellyStochasticNetworks.LossLimits.partition
            rw [tsum_subtype (KellyStochasticNetworks.lossStates A (fun j => (c j).toNat))
              (KellyStochasticNetworks.lossWeight v), hstates c h]
          · symm
            refine (tsum_congr (fun n => ?_)).trans tsum_zero
            exact Set.indicator_of_notMem (hempty c h n) _
        have hEx : ∀ (v : Fin R → ℝ), (∀ s, 0 < v s) → ∀ (c : Fin J → ℤ) (f : (Fin R → ℕ) → ℝ),
            expect A v c f = (∑' n, (stateSpace A c).indicator
              (fun n => f n * KellyStochasticNetworks.lossWeight v n) n) / partitionFn A v c := by
          intro v hv c f
          unfold expect
          split_ifs with h
          · unfold KellyStochasticNetworks.LossLimits.occupancyLaw
            rw [MeasureTheory.integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top)]
            have hP : 0 ≤ KellyStochasticNetworks.LossLimits.partition A v (fun j => (c j).toNat) :=
              tsum_nonneg (fun n => (hwpos v hv _).le)
            have e1 : ∀ n : KellyStochasticNetworks.lossStates A (fun j => (c j).toNat),
                (ENNReal.ofReal (KellyStochasticNetworks.lossWeight v (n : Fin R → ℕ) /
                  KellyStochasticNetworks.LossLimits.partition A v (fun j => (c j).toNat))).toReal •
                    f n = (f n * KellyStochasticNetworks.lossWeight v n) /
                  KellyStochasticNetworks.LossLimits.partition A v (fun j => (c j).toNat) := by
              intro n
              rw [ENNReal.toReal_ofReal (div_nonneg (hwpos v hv _).le hP), smul_eq_mul]
              ring
            rw [tsum_congr e1, tsum_div_const, partitionFn, if_pos h]
            congr 1
            rw [tsum_subtype (KellyStochasticNetworks.lossStates A (fun j => (c j).toNat))
              (fun n => f n * KellyStochasticNetworks.lossWeight v n), hstates c h]
          · rw [(tsum_congr (fun n => Set.indicator_of_notMem (hempty c h n) _)).trans tsum_zero,
              zero_div]
        set S := stateSpace A (capInt C) with hS
        set S' := stateSpace A (reduceCap A (capInt C) r) with hS'
        set g : (Fin R → ℕ) → ℝ := fun n => ∑ s, w s * (n s : ℝ) with hg
        have hσ : ∀ (n : Fin R → ℕ) (s : Fin R), (n s : ℝ) ≤ 2 ^ (∑ q, n q) := by
          intro n s
          exact_mod_cast le_trans (Nat.lt_two_pow_self).le
            (Nat.pow_le_pow_right (by norm_num) (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ s)))
        have hgabs : ∀ n, |g n| ≤ (∑ s, |w s|) * 2 ^ (∑ q, n q) := by
          intro n
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum (fun s _ => ?_)
          rw [abs_mul, Nat.abs_cast]
          exact mul_le_mul_of_nonneg_left (hσ n s) (abs_nonneg _)
        have hK : 0 ≤ ∑ s, |w s| := Finset.sum_nonneg (fun s _ => abs_nonneg _)
        have hind : ∀ (T : Set (Fin R → ℕ)) (f : (Fin R → ℕ) → ℝ) (K : ℝ),
            (∀ n, |f n| ≤ K * 2 ^ (∑ q, n q)) → 0 ≤ K → ∀ n, |T.indicator f n| ≤ K * 2 ^ (∑ q, n q) := by
          intro T f K hf hK0 n
          by_cases h : n ∈ T
          · rw [Set.indicator_of_mem h]; exact hf n
          · rw [Set.indicator_of_notMem h, abs_zero]; positivity
        have h1abs : ∀ n : Fin R → ℕ, |(fun _ => (1 : ℝ)) n| ≤ 1 * 2 ^ (∑ q, n q) := by
          intro n
          simp only [abs_one, one_mul]
          exact one_le_pow₀ (by norm_num)
        have hmemshift : ∀ m, (m + Pi.single r 1 ∈ S ↔ m ∈ S') := by
          intro m
          simp only [hS, hS', stateSpace, Set.mem_ofPred_eq, reduceCap, capInt]
          refine forall_congr' (fun j => ?_)
          have hsumeq : ∑ s, A j s * (m + Pi.single r 1 : Fin R → ℕ) s = ∑ s, A j s * m s + A j r := by
            simp [mul_add, Finset.sum_add_distrib, Pi.single_apply]
          rw [hsumeq]
          push_cast
          constructor <;> intro h <;> linarith
        have hgshift : ∀ m, g (m + Pi.single r 1) = g m + w r := by
          intro m
          simp [hg, mul_add, Finset.sum_add_distrib, Pi.single_apply]
        have hindshift : ∀ (f : (Fin R → ℕ) → ℝ) m, S.indicator f (m + Pi.single r 1) =
            S'.indicator (fun m => f (m + Pi.single r 1)) m := by
          intro f m
          by_cases h : m ∈ S'
          · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hmemshift m).2 h)]
          · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hmemshift m).1 h'))]
        have hG := hderiv (S.indicator (fun _ => (1 : ℝ))) 1 zero_le_one (hind S _ 1 h1abs zero_le_one)
        have hH := hderiv (S.indicator g) _ hK (hind S g _ hgabs hK)
        set G0 := ∑' n, S.indicator (fun _ => (1 : ℝ)) n * KellyStochasticNetworks.lossWeight ν n with hG0
        set H0 := ∑' n, S.indicator g n * KellyStochasticNetworks.lossWeight ν n with hH0
        set G1 := ∑' n, S'.indicator (fun _ => (1 : ℝ)) n * KellyStochasticNetworks.lossWeight ν n with hG1
        set H1 := ∑' n, S'.indicator g n * KellyStochasticNetworks.lossWeight ν n with hH1
        have hGd : (∑' m, S.indicator (fun _ => (1 : ℝ)) (m + Pi.single r 1) *
            KellyStochasticNetworks.lossWeight ν m) = G1 := by
          refine tsum_congr (fun m => ?_)
          rw [hindshift]
        have hHd : (∑' m, S.indicator g (m + Pi.single r 1) *
            KellyStochasticNetworks.lossWeight ν m) = H1 + w r * G1 := by
          rw [hH1, hG1, ← tsum_mul_left, ← Summable.tsum_add
            (hsumb _ _ (hind S' g _ hgabs hK))
            ((hsumb _ _ (hind S' _ 1 h1abs zero_le_one)).mul_left (w r))]
          refine tsum_congr (fun m => ?_)
          rw [hindshift]
          by_cases h : m ∈ S'
          · simp only [Set.indicator_of_mem h, hgshift]
            ring
          · simp only [Set.indicator_of_notMem h]
            ring
        rw [hGd] at hG
        rw [hHd] at hH
        have hS0 : (0 : Fin R → ℕ) ∈ S := by
          intro j
          simp [capInt]
        have hG0pos : 0 < G0 := by
          have hs := hsumb _ _ (hind S _ 1 h1abs zero_le_one)
          refine lt_of_lt_of_le ?_ (hs.le_tsum 0 (fun n _ => ?_))
          · rw [Set.indicator_of_mem hS0, one_mul]
            exact hwpos ν hν 0
          · exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (hwpos ν hν n).le
        have hcase : 0 < G1 ∨ (G1 = 0 ∧ H1 = 0) := by
          by_cases hc : ∀ j, 0 ≤ reduceCap A (capInt C) r j
          · left
            have hS10 : (0 : Fin R → ℕ) ∈ S' := by
              intro j
              simpa using hc j
            have hs := hsumb _ _ (hind S' _ 1 h1abs zero_le_one)
            refine lt_of_lt_of_le ?_ (hs.le_tsum 0 (fun n _ => ?_))
            · rw [Set.indicator_of_mem hS10, one_mul]
              exact hwpos ν hν 0
            · exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (hwpos ν hν n).le
          · right
            constructor
            · refine (tsum_congr (fun n => ?_)).trans tsum_zero
              rw [Set.indicator_of_notMem (hempty _ hc n), zero_mul]
            · refine (tsum_congr (fun n => ?_)).trans tsum_zero
              rw [Set.indicator_of_notMem (hempty _ hc n), zero_mul]
        have hacc : acceptance A ν (capInt C) r = G1 / G0 := by
          unfold acceptance
          rw [hPF, hPF, hG1, hG0]
          congr 1
          · refine tsum_congr (fun n => ?_)
            simp only [Set.indicator_apply]
            split_ifs <;> simp
          · refine tsum_congr (fun n => ?_)
            simp only [Set.indicator_apply]
            split_ifs <;> simp
        have hrev : ∀ (v : Fin R → ℝ), (∀ s, 0 < v s) → ∀ c : Fin J → ℤ,
            revenue A v c w = (∑' n, (stateSpace A c).indicator g n * KellyStochasticNetworks.lossWeight v n) /
              (∑' n, (stateSpace A c).indicator (fun _ => (1 : ℝ)) n * KellyStochasticNetworks.lossWeight v n) := by
          intro v hv c
          unfold revenue
          rw [hEx v hv, hPF]
          congr 1 <;> refine tsum_congr (fun n => ?_) <;>
            by_cases h : n ∈ stateSpace A c <;> simp [h, hg]
        have hic : impliedCost A ν (capInt C) w r = H0 / G0 - H1 / G1 := by
          unfold impliedCost
          rw [hrev ν hν, hrev ν hν]
        have hupd : ∀ t : ℝ, 0 < t → ∀ s, 0 < Function.update ν r t s := by
          intro t ht s
          by_cases h : s = r
          · subst h; simpa using ht
          · rw [Function.update_of_ne h]; exact hν s
        have hdiv := hH.div hG (by simpa only [Function.update_eq_self] using hG0pos.ne')
        simp only [Function.update_eq_self] at hdiv
        rw [← hG0, ← hH0] at hdiv
        refine (hdiv.congr_of_eventuallyEq ?_).congr_deriv ?_
        · filter_upwards [Ioi_mem_nhds (hν r)] with t ht
          exact hrev _ (hupd t ht) _
        · rw [hacc, hic]
          rcases hcase with h | ⟨h1, h2⟩
          · field_simp
            ring
          · simp [h1, h2]
