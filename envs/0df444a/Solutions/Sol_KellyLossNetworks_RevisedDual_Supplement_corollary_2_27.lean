-- Prove2me | solution 1 for KellyLossNetworks.RevisedDual.Supplement.corollary_2_27
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:31:04.676816+00:00
-- url     : https://prove2.me/submissions/250c3c0d-9060-4a36-a466-026fc4ec9979

import Mathlib
import Definitions.Def_KellyLossNetworks_RevisedDual_Supplement_Exact
import Definitions.Def_KellyStochasticNetworks_LossLimits_Optimization

open Filter Topology

open KellyLossNetworks
open KellyLossNetworks.RevisedDual
open KellyLossNetworks.RevisedDual.Supplement

/-- **Corollary 2.27.** Under the limiting regime (2.11),
`1 − L_r(N) = ∏_j (1 − B_j)^{A_jr} + o(1)`.

Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
p. 333, Corollary 2.27; the regime (2.11) is on p. 330.

**Formalization Note.** The `N`-th network has rates `νN N` and integer capacities `CN N`;
`1 − L_r(N)` is the exact acceptance probability `G(C(N) − Ae_r)/G(C(N))` of (1.5).
`B` is any solution of the conditions (2.7) for the limiting `ν` and `C` (the product
`∏_j (1 − B_j)^{A_jr} = x_r/ν_r` is the same for every solution, Theorem 2.8). "`+ o(1)`" is
convergence of `1 − L_r(N)` to the product. Positive rates `ν_r(N), ν_r > 0` are the standing
assumption of the model (the primal problem (2.1) contains `log ν_r`). -/
theorem solution {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (νN : ℕ → Fin R → ℝ) (CN : ℕ → Fin J → ℕ) (ν : Fin R → ℝ) (C : Fin J → ℝ)
    (hνN : ∀ N r, 0 < νN N r) (hν : ∀ r, 0 < ν r)
    (hrate : ∀ r, Tendsto (fun N : ℕ => νN N r / N) atTop (𝓝 (ν r)))
    (hcap : ∀ j, Tendsto (fun N : ℕ => (CN N j : ℝ) / N) atTop (𝓝 (C j)))
    (B : Fin J → ℝ) (hB : KellyStochasticNetworks.LossLimits.blockingConditions A ν C B)
    (r : Fin R) :
    Tendsto (fun N : ℕ => acceptance A (νN N) (capInt (CN N)) r) atTop
      (𝓝 (∏ j, (1 - B j) ^ A j r)) := by
        set_option maxHeartbeats 2000000 in
          classical
          let x := KellyStochasticNetworks.LossLimits.carried A ν B
          let y : Fin J → ℝ := fun j => -Real.log (1 - B j)
          have hBpos : ∀ j, 0 < 1 - B j := fun j => sub_pos.mpr (hB.1 j).2
          have hxpos : ∀ s, 0 < x s := by
            intro s
            exact mul_pos (hν s) (Finset.prod_pos fun j _ => pow_pos (hBpos j) _)
          have hy : ∀ j, 0 ≤ y j := by
            intro j
            exact neg_nonneg.mpr (Real.log_nonpos (hBpos j).le (by linarith [(hB.1 j).1]))
          have hxform : ∀ s, x s = ν s * Real.exp (-∑ j, y j * (A j s : ℝ)) := by
            intro s
            change ν s * ∏ j, (1 - B j) ^ A j s = _
            congr 1
            rw [← Finset.sum_neg_distrib, Real.exp_sum]
            apply Finset.prod_congr rfl
            intro j _
            dsimp [y]
            rw [neg_mul, neg_neg, mul_comm (Real.log (1 - B j)), Real.exp_nat_mul, Real.exp_log (hBpos j)]
          have hxfeas : ∀ j, ∑ s, (A j s : ℝ) * x s ≤ C j := hB.2.1
          have hcomp : ∀ j, y j * (C j - ∑ s, (A j s : ℝ) * x s) = 0 := by
            intro j
            by_cases hb : B j = 0
            · simp [y, hb]
            · rw [hB.2.2 j (lt_of_le_of_ne (hB.1 j).1 (Ne.symm hb)), sub_self, mul_zero]
          have hCnonneg : ∀ j, 0 ≤ C j := by
            intro j
            exact le_trans (Finset.sum_nonneg fun s _ => mul_nonneg (Nat.cast_nonneg _) (hxpos s).le) (hxfeas j)
          have hCpos : ∀ j, (∃ s, A j s ≠ 0) → 0 < C j := by
            rintro j ⟨s, hs⟩
            exact lt_of_lt_of_le (Finset.sum_pos' (fun t _ => mul_nonneg (Nat.cast_nonneg _) (hxpos t).le)
              ⟨s, Finset.mem_univ s, mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hs)) (hxpos s)⟩) (hxfeas j)
          have hdual : ∑ s, x s + ∑ j, y j * C j =
              KellyStochasticNetworks.LossLimits.entropyObjective ν x := by
            have hlog : ∀ s, Real.log (x s) = Real.log (ν s) - ∑ j, y j * (A j s : ℝ) := by
              intro s
              rw [hxform s, Real.log_mul (hν s).ne' (Real.exp_ne_zero _), Real.log_exp]
              ring
            unfold KellyStochasticNetworks.LossLimits.entropyObjective
            simp_rw [hlog]
            have hc : ∑ j, y j * C j = ∑ j, y j * ∑ s, (A j s : ℝ) * x s := by
              apply Finset.sum_congr rfl
              intro j _
              nlinarith [hcomp j]
            rw [hc]
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro s _
            simp_rw [← mul_assoc, mul_comm _ (x s)]
            rw [← Finset.mul_sum]
            ring
          have hwpos : ∀ (v : Fin R → ℝ), (∀ s, 0 < v s) → ∀ n : Fin R → ℕ,
              0 < KellyStochasticNetworks.lossWeight v n := by
            intro v hv n
            exact Finset.prod_pos fun s _ => div_pos (pow_pos (hv s) _) (by positivity)
          have hwbound : ∀ (v : Fin R → ℝ), (∀ s, 0 < v s) →
              Summable (KellyStochasticNetworks.lossWeight v) ∧
              (∑' n, KellyStochasticNetworks.lossWeight v n) ≤ Real.exp (∑ s, v s) := by
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
            have hs : Summable (KellyStochasticNetworks.lossWeight v) :=
              summable_of_sum_le (fun n => (hwpos v hv n).le) hfinite
            exact ⟨hs, hs.tsum_le_of_sum_le hfinite⟩
          have hpartitionpos : ∀ (v : Fin R → ℝ), (∀ s, 0 < v s) → ∀ D : Fin J → ℕ,
              0 < KellyStochasticNetworks.LossLimits.partition A v D := by
            intro v hv D
            let z : KellyStochasticNetworks.lossStates A D := ⟨0, by simp [KellyStochasticNetworks.lossStates]⟩
            exact lt_of_lt_of_le (hwpos v hv z) (((hwbound v hv).1.subtype _).le_tsum z (fun n _ => (hwpos v hv n).le))
          have hpartitionFn : ∀ (v : Fin R → ℝ) (D : Fin J → ℕ),
              partitionFn A v (capInt D) = KellyStochasticNetworks.LossLimits.partition A v D := by
            intro v D
            simp [partitionFn, capInt]
          let P (v : Fin R → ℝ) (c : Fin J → ℤ) : ℝ :=
            ∑' n : stateSpace A c, KellyStochasticNetworks.lossWeight v n
          have hP : ∀ v c, partitionFn A v c = P v c := by
            intro v c
            by_cases hc : ∀ j, 0 ≤ c j
            · rw [partitionFn, if_pos hc]
              apply tsum_congr_set_coe
              ext n
              change (∀ j, ∑ s, A j s * n s ≤ (c j).toNat) ↔
                (∀ j, ((∑ s, A j s * n s : ℕ) : ℤ) ≤ c j)
              constructor
              · intro h j
                have := Int.ofNat_le.mpr (h j)
                simpa only [Int.toNat_of_nonneg (hc j)] using this
              · intro h j
                exact Int.ofNat_le.mp (by simpa only [Int.toNat_of_nonneg (hc j)] using h j)
            · rw [partitionFn, if_neg hc]
              have he : stateSpace A c = ∅ := by
                apply Set.eq_empty_iff_forall_notMem.mpr
                intro n hn
                obtain ⟨j, hj⟩ := not_forall.mp hc
                exact hj (le_trans (Int.natCast_nonneg _) (hn j))
              dsimp [P]
              rw [he]
              simp
          have hPsum : ∀ (v : Fin R → ℝ), (∀ s, 0 < v s) → ∀ c,
              Summable (fun n : stateSpace A c => KellyStochasticNetworks.lossWeight v n) := by
            intro v hv c
            exact (hwbound v hv).1.subtype _
          have htilt : ∀ (v a : Fin R → ℝ) (n : Fin R → ℕ),
              KellyStochasticNetworks.lossWeight (fun s => v s * Real.exp (a s)) n =
                KellyStochasticNetworks.lossWeight v n * Real.exp (∑ s, (n s : ℝ) * a s) := by
            intro v a n
            unfold KellyStochasticNetworks.lossWeight
            rw [Real.exp_sum, ← Finset.prod_mul_distrib]
            apply Finset.prod_congr rfl
            intro s _
            rw [mul_pow, Real.exp_nat_mul]
            ring
          have htiltr : ∀ (v : Fin R → ℝ) (t : ℝ) (n : Fin R → ℕ),
              KellyStochasticNetworks.lossWeight (Function.update v r (v r * Real.exp t)) n =
                KellyStochasticNetworks.lossWeight v n * Real.exp (t * n r) := by
            intro v t n
            have he : Function.update v r (v r * Real.exp t) =
                fun s => v s * Real.exp (if s = r then t else 0) := by
              ext s
              by_cases hs : s = r <;> simp [hs]
            rw [he, htilt]
            congr 2
            simp [mul_comm]
          have hmomentSum : ∀ (v : Fin R → ℝ), (∀ s, 0 < v s) → ∀ c,
              Summable (fun n : stateSpace A c => (n.val r : ℝ) * KellyStochasticNetworks.lossWeight v n) := by
            intro v hv c
            have hv' : ∀ s, 0 < Function.update v r (v r * Real.exp 1) s := by
              intro s
              by_cases hs : s = r <;> simp [hs, hv s, hv r, Real.exp_pos]
            apply Summable.of_nonneg_of_le (fun n => mul_nonneg (Nat.cast_nonneg _) (hwpos v hv n).le)
              (g := fun n : stateSpace A c => (n.val r : ℝ) * KellyStochasticNetworks.lossWeight v n)
              (f := fun n : stateSpace A c => KellyStochasticNetworks.lossWeight (Function.update v r (v r * Real.exp 1)) n)
            · intro n
              rw [htiltr, one_mul, mul_comm (KellyStochasticNetworks.lossWeight v n)]
              apply mul_le_mul_of_nonneg_right _ (hwpos v hv n).le
              linarith [Real.add_one_le_exp (n.val r)]
            · exact hPsum _ hv' c
          let inc (n : Fin R → ℕ) : Fin R → ℕ := Function.update n r (n r + 1)
          let dec (n : Fin R → ℕ) : Fin R → ℕ := Function.update n r (n r - 1)
          have hincsum : ∀ n j, ∑ s, A j s * inc n s = (∑ s, A j s * n s) + A j r := by
            intro n j
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r),
              ← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
            dsimp [inc]
            simp only [Function.update_self]
            have he : ∑ s ∈ Finset.univ.erase r, A j s * Function.update n r (n r + 1) s =
                ∑ s ∈ Finset.univ.erase r, A j s * n s := by
              apply Finset.sum_congr rfl
              intro s hs
              rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
            rw [he]
            ring
          have hincweight : ∀ v n, (inc n r : ℝ) * KellyStochasticNetworks.lossWeight v (inc n) =
              v r * KellyStochasticNetworks.lossWeight v n := by
            intro v n
            unfold KellyStochasticNetworks.lossWeight
            rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ r),
              ← Finset.mul_prod_erase _ _ (Finset.mem_univ r)]
            have he : ∏ s ∈ Finset.univ.erase r, v s ^ inc n s / (↑(inc n s).factorial : ℝ) =
                ∏ s ∈ Finset.univ.erase r, v s ^ n s / (↑(n s).factorial : ℝ) := by
              apply Finset.prod_congr rfl
              intro s hs
              simp [inc, Function.update_of_ne (Finset.ne_of_mem_erase hs)]
            rw [he]
            simp only [inc, Function.update_self, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
            field_simp
          have hincmem : ∀ c n, n ∈ stateSpace A (reduceCap A c r) → inc n ∈ stateSpace A c := by
            intro c n hn j
            rw [hincsum, Nat.cast_add]
            have := hn j
            dsimp [reduceCap] at this
            omega
          have hdecinc : ∀ n, dec (inc n) = n := by
            intro n
            ext s
            by_cases hs : s = r <;> simp [inc, dec, hs]
          have hincdec : ∀ n, 0 < n r → inc (dec n) = n := by
            intro n hn
            ext s
            by_cases hs : s = r <;> simp [inc, dec, hs, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn.ne')]
          have hdecmem : ∀ c n, n ∈ stateSpace A c → 0 < n r →
              dec n ∈ stateSpace A (reduceCap A c r) := by
            intro c n hn hp j
            have he := hincsum (dec n) j
            rw [hincdec n hp] at he
            have hj := hn j
            change ((∑ s, A j s * dec n s : ℕ) : ℤ) ≤ c j - (A j r : ℤ)
            rw [he, Nat.cast_add] at hj
            omega
          have hmoment : ∀ (v : Fin R → ℝ), (∀ s, 0 < v s) → ∀ c,
              (∑' n : stateSpace A c, (n.val r : ℝ) * KellyStochasticNetworks.lossWeight v n) =
                v r * P v (reduceCap A c r) := by
            intro v hv c
            rw [← tsum_mul_left]
            let f : stateSpace A c → ℝ := fun n => (n.val r : ℝ) * KellyStochasticNetworks.lossWeight v n
            let g : stateSpace A (reduceCap A c r) → ℝ := fun n => v r * KellyStochasticNetworks.lossWeight v n
            change (∑' n, f n) = ∑' n, g n
            apply tsum_eq_tsum_of_ne_zero_bij (fun n => ⟨inc n.val.val, hincmem c _ n.val.property⟩)
            · intro n m h
              apply Subtype.ext
              apply Subtype.ext
              have he := congrArg (fun k : stateSpace A c => dec k.val) h
              simpa only [hdecinc] using he
            · intro n hn
              have hp : 0 < n.val r := by
                by_contra h
                have he : n.val r = 0 := Nat.eq_zero_of_not_pos h
                exact hn (by simp [f, he])
              let m : stateSpace A (reduceCap A c r) := ⟨dec n.val, hdecmem c _ n.property hp⟩
              have hm : g m ≠ 0 := (mul_pos (hv r) (hwpos v hv m)).ne'
              refine ⟨⟨m, hm⟩, ?_⟩
              apply Subtype.ext
              exact hincdec n.val hp
            · intro n
              exact hincweight v n.val.val
          have hPupper : ∀ (v : Fin R → ℝ), (∀ s, 0 < v s) → ∀ c,
              P v c ≤ Real.exp ((∑ s, v s * Real.exp (-∑ j, y j * (A j s : ℝ))) +
                ∑ j, y j * (c j : ℝ)) := by
            intro v hv c
            let v' : Fin R → ℝ := fun s => v s * Real.exp (-∑ j, y j * (A j s : ℝ))
            have hv' : ∀ s, 0 < v' s := fun s => mul_pos (hv s) (Real.exp_pos _)
            have ht : ∀ n : stateSpace A c, KellyStochasticNetworks.lossWeight v n ≤
                Real.exp (∑ j, y j * (c j : ℝ)) * KellyStochasticNetworks.lossWeight v' n := by
              intro n
              have he : KellyStochasticNetworks.lossWeight v' n = KellyStochasticNetworks.lossWeight v n *
                  Real.exp (-(∑ j, y j * ∑ s, (A j s : ℝ) * n.val s)) := by
                dsimp [v']
                rw [htilt]
                congr 2
                simp_rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro j _
                apply Finset.sum_congr rfl
                intro s _
                ring
              rw [he]
              have hn : ∑ j, y j * ∑ s, (A j s : ℝ) * n.val s ≤ ∑ j, y j * (c j : ℝ) := by
                apply Finset.sum_le_sum
                intro j _
                apply mul_le_mul_of_nonneg_left _ (hy j)
                exact_mod_cast n.property j
              have hmul := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (show 0 ≤
                  (∑ j, y j * (c j : ℝ)) - ∑ j, y j * ∑ s, (A j s : ℝ) * n.val s by linarith))
                  (hwpos v hv n).le
              rw [Real.exp_zero, mul_one, Real.exp_sub] at hmul
              rw [Real.exp_neg]
              simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
            calc
              P v c ≤ ∑' n : stateSpace A c, Real.exp (∑ j, y j * (c j : ℝ)) * KellyStochasticNetworks.lossWeight v' n :=
                (hPsum v hv c).tsum_le_tsum ht ((hPsum v' hv' c).mul_left _)
              _ = Real.exp (∑ j, y j * (c j : ℝ)) * P v' c := tsum_mul_left
              _ ≤ Real.exp (∑ j, y j * (c j : ℝ)) * Real.exp (∑ s, v' s) := by
                apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
                exact ((hwbound v' hv').1.tsum_subtype_le _ _ (fun n => (hwpos v' hv' n).le)).trans (hwbound v' hv').2
              _ = _ := by rw [← Real.exp_add]; congr 1; ring
          have hJensen : ∀ (v : Fin R → ℝ), (∀ s, 0 < v s) → ∀ (D : Fin J → ℕ) (t : ℝ),
              Real.log (P v (capInt D)) + t * (v r * acceptance A v (capInt D) r) ≤
                Real.log (P (Function.update v r (v r * Real.exp t)) (capInt D)) := by
            intro v hv D t
            let c := capInt D
            let m := v r * acceptance A v c r
            have hp : 0 < P v c := by rw [← hP, hpartitionFn]; exact hpartitionpos v hv D
            have hm : (∑' n : stateSpace A c, (n.val r : ℝ) * KellyStochasticNetworks.lossWeight v n) = m * P v c := by
              rw [hmoment v hv c]
              dsimp [m, acceptance]
              rw [hP, hP]
              field_simp
            have hv' : ∀ s, 0 < Function.update v r (v r * Real.exp t) s := by
              intro s
              by_cases hs : s = r <;> simp [hs, hv s, hv r, Real.exp_pos]
            have hlin : Summable (fun n : stateSpace A c =>
                (1 - t * m) * KellyStochasticNetworks.lossWeight v n +
                  t * ((n.val r : ℝ) * KellyStochasticNetworks.lossWeight v n)) :=
              ((hPsum v hv c).mul_left _).add ((hmomentSum v hv c).mul_left _)
            have ht : ∀ n : stateSpace A c,
                Real.exp (t * m) * ((1 - t * m) * KellyStochasticNetworks.lossWeight v n +
                  t * ((n.val r : ℝ) * KellyStochasticNetworks.lossWeight v n)) ≤
                KellyStochasticNetworks.lossWeight (Function.update v r (v r * Real.exp t)) n := by
              intro n
              rw [htiltr]
              have he : Real.exp (t * (n.val r : ℝ)) = Real.exp (t * m) * Real.exp (t * (n.val r - m)) := by
                rw [← Real.exp_add]
                congr 1
                ring
              rw [he]
              have hi := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (t * ((n.val r : ℝ) - m)))
                (mul_nonneg (hwpos v hv n).le (Real.exp_pos (t * m)).le)
              nlinarith
            have hi := (hlin.mul_left (Real.exp (t * m))).tsum_le_tsum ht (hPsum _ hv' c)
            have hs : (∑' n : stateSpace A c, Real.exp (t * m) *
                ((1 - t * m) * KellyStochasticNetworks.lossWeight v n +
                  t * ((n.val r : ℝ) * KellyStochasticNetworks.lossWeight v n))) =
                Real.exp (t * m) * P v c := by
              rw [tsum_mul_left, Summable.tsum_add ((hPsum v hv c).mul_left _)
                ((hmomentSum v hv c).mul_left _), tsum_mul_left, tsum_mul_left, hm]
              dsimp [P]
              ring
            rw [hs] at hi
            have hlog := Real.log_le_log (mul_pos (Real.exp_pos _) hp) hi
            rw [Real.log_mul (Real.exp_ne_zero _) hp.ne', Real.log_exp] at hlog
            simpa only [add_comm] using hlog
          have hNtop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
          have hlogN : Tendsto (fun N : ℕ => Real.log N / N) atTop (𝓝 0) := by
            convert (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hNtop using 1; simp [Function.comp_def]
          have hfac : ∀ (k : ℕ → ℕ) (z : ℝ), 0 < z →
              Tendsto (fun N => (k N : ℝ) / N) atTop (𝓝 z) →
              Tendsto (fun N => (Real.log ((k N).factorial : ℝ) - (k N : ℝ) * Real.log (k N) + k N) / N)
                atTop (𝓝 0) := by
            intro k z hz hk
            have hkreal : Tendsto (fun N => (k N : ℝ)) atTop atTop := by
              have he : ∀ᶠ N : ℕ in atTop, z / 2 ≤ (k N : ℝ) / N :=
                ((tendsto_order.mp hk).1 (z / 2) (by linarith)).mono (fun _ h => h.le)
              apply tendsto_atTop_mono' _ _ (Filter.Tendsto.const_mul_atTop (show 0 < z / 2 by linarith) hNtop)
              filter_upwards [he, eventually_ge_atTop 1] with N hN hNpos
              have hNp : (0 : ℝ) < N := by exact_mod_cast hNpos
              exact (le_div_iff₀ hNp).mp hN
            have hkNat : Tendsto k atTop atTop := tendsto_natCast_atTop_iff.mp hkreal
            have hst := (Real.continuousAt_log (by positivity : Real.sqrt Real.pi ≠ 0)).tendsto.comp
              (Stirling.tendsto_stirlingSeq_sqrt_pi.comp hkNat)
            have hsmall := hst.div_atTop hNtop
            have hlogk : Tendsto (fun N => Real.log (k N : ℝ) / N) atTop (𝓝 0) := by
              have hl : Tendsto (fun N => Real.log ((k N : ℝ) / N) / N) atTop (𝓝 0) :=
                ((Real.continuousAt_log hz.ne').tendsto.comp hk).div_atTop hNtop
              have hh : Tendsto (fun N => Real.log ((k N : ℝ) / N) / N + Real.log N / N) atTop (𝓝 0) :=
                by simpa only [add_zero] using hl.add hlogN
              apply hh.congr'
              filter_upwards [hNtop.eventually_ne_atTop 0, hkreal.eventually_ne_atTop 0] with N hN hkN
              rw [Real.log_div hkN hN]
              ring
            have hlog2k : Tendsto (fun N => Real.log (2 * (k N : ℝ)) / N) atTop (𝓝 0) := by
              have hc := hNtop.const_div_atTop (Real.log 2)
              have hh : Tendsto (fun N => Real.log 2 / N + Real.log (k N : ℝ) / N) atTop (𝓝 0) :=
                by simpa only [add_zero] using hc.add hlogk
              apply hh.congr'
              filter_upwards [hkreal.eventually_ne_atTop 0] with N hkN
              rw [Real.log_mul (by norm_num) hkN, add_div]
            have hh : Tendsto (fun N => Real.log (Stirling.stirlingSeq (k N)) / N +
                (1 / 2 : ℝ) * (Real.log (2 * (k N : ℝ)) / N)) atTop (𝓝 0) :=
              by simpa only [Function.comp_def, mul_zero, add_zero] using hsmall.add (hlog2k.const_mul (1 / 2 : ℝ))
            apply hh.congr'
            filter_upwards [hkreal.eventually_ne_atTop 0] with N hkN
            rw [Stirling.log_stirlingSeq_formula, Real.log_div hkN (Real.exp_ne_zero 1), Real.log_exp]
            ring
          have hfloor : ∀ z : ℝ, 0 < z → Tendsto (fun N : ℕ => (⌊(N : ℝ) * z⌋₊ : ℝ) / N) atTop (𝓝 z) := by
            intro z hz
            have hh := (tendsto_nat_floor_div_atTop.comp (Filter.Tendsto.atTop_mul_const hz hNtop)).mul_const z
            simp only [one_mul] at hh
            apply hh.congr'
            filter_upwards [hNtop.eventually_ne_atTop 0] with N hN
            dsimp [Function.comp_def]
            field_simp
          have hweightlimit : ∀ z : Fin R → ℝ, (∀ s, 0 < z s) →
              Tendsto (fun N : ℕ => Real.log (KellyStochasticNetworks.lossWeight (νN N)
                (fun s => ⌊(N : ℝ) * z s⌋₊)) / N) atTop
                (𝓝 (KellyStochasticNetworks.LossLimits.entropyObjective ν z)) := by
            intro z hz
            let k : ℕ → Fin R → ℕ := fun N s => ⌊(N : ℝ) * z s⌋₊
            have hk : ∀ s, Tendsto (fun N => (k N s : ℝ) / N) atTop (𝓝 (z s)) := fun s => hfloor (z s) (hz s)
            have ht : ∀ s, Tendsto (fun N : ℕ => ((k N s : ℝ) * Real.log (νN N s) -
                Real.log ((k N s).factorial : ℝ)) / N) atTop
                (𝓝 (z s * Real.log (ν s) - z s * Real.log (z s) + z s)) := by
              intro s
              have hlv := (Real.continuousAt_log (hν s).ne').tendsto.comp (hrate s)
              have hlk := (Real.continuousAt_log (hz s).ne').tendsto.comp (hk s)
              have hh := ((hk s).mul ((hlv.sub hlk).add_const 1)).sub (hfac (fun N => k N s) (z s) (hz s) (hk s))
              have he : z s * (Real.log (ν s) - Real.log (z s) + 1) - 0 =
                  z s * Real.log (ν s) - z s * Real.log (z s) + z s := by ring
              rw [he] at hh
              apply hh.congr'
              filter_upwards [hNtop.eventually_ne_atTop 0, (hk s).eventually_ne (hz s).ne'] with N hN hkN
              have hkNs : (k N s : ℝ) ≠ 0 := by intro he; simp [he] at hkN
              dsimp only [Function.comp_def]
              rw [Real.log_div (hνN N s).ne' hN, Real.log_div hkNs hN]
              ring
            have hh := tendsto_finsetSum Finset.univ (fun s _ => ht s)
            unfold KellyStochasticNetworks.LossLimits.entropyObjective
            convert hh using 1
            ext N
            rw [KellyStochasticNetworks.lossWeight, Real.log_prod (fun s _ =>
              (div_pos (pow_pos (hνN N s) _) (by positivity)).ne'), Finset.sum_div]
            apply Finset.sum_congr rfl
            intro s _
            rw [Real.log_div (pow_ne_zero _ (hνN N s).ne') (by positivity), Real.log_pow]
          have hfloorfeas : ∀ a : ℝ, 0 < a → a < 1 → ∀ᶠ N : ℕ in atTop,
              (fun s => ⌊(N : ℝ) * (a * x s)⌋₊) ∈ stateSpace A (capInt (CN N)) := by
            intro a ha ha1
            have hj : ∀ j, ∀ᶠ N : ℕ in atTop,
                (∑ s, A j s * ⌊(N : ℝ) * (a * x s)⌋₊ : ℕ) ≤ CN N j := by
              intro j
              by_cases he : ∃ s, A j s ≠ 0
              · have hlt : a * (∑ s, (A j s : ℝ) * x s) < C j := by
                  have hp := hCpos j he
                  nlinarith [hxfeas j, mul_nonneg (show 0 ≤ 1 - a by linarith)
                    (show 0 ≤ C j - ∑ s, (A j s : ℝ) * x s by linarith [hxfeas j])]
                have hc := (tendsto_order.mp (hcap j)).1 _ hlt
                filter_upwards [hc, eventually_ge_atTop 1] with N hN hNp
                have hNpos : (0 : ℝ) < N := by exact_mod_cast hNp
                have hsum : (∑ s, (A j s : ℝ) * (⌊(N : ℝ) * (a * x s)⌋₊ : ℝ)) ≤
                    (N : ℝ) * (a * ∑ s, (A j s : ℝ) * x s) := by
                  calc
                    _ ≤ ∑ s, (A j s : ℝ) * ((N : ℝ) * (a * x s)) := by
                      apply Finset.sum_le_sum
                      intro s _
                      exact mul_le_mul_of_nonneg_left (Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) (mul_pos ha (hxpos s)).le)) (Nat.cast_nonneg _)
                    _ = _ := by simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring
                have hi := (lt_div_iff₀ hNpos).mp hN
                have hsum' : ((∑ s, A j s * ⌊(N : ℝ) * (a * x s)⌋₊ : ℕ) : ℝ) ≤ (CN N j : ℝ) := by
                  push_cast
                  nlinarith
                exact_mod_cast hsum'
              · have hz : ∀ s, A j s = 0 := by simpa only [not_exists, not_not] using he
                exact Filter.Eventually.of_forall (fun N => by simp [hz])
            filter_upwards [Filter.eventually_all.mpr hj] with N hN
            intro j
            dsimp [capInt]
            exact_mod_cast hN j
          let U (v : Fin R → ℝ) (D : Fin J → ℕ) : ℝ :=
            (∑ s, v s * Real.exp (-∑ j, y j * (A j s : ℝ))) + ∑ j, y j * (D j : ℝ)
          let d : ℝ := KellyStochasticNetworks.LossLimits.entropyObjective ν x
          let u : ℕ → ℝ := fun N => Real.log (P (νN N) (capInt (CN N))) / N
          have hUlimit : Tendsto (fun N : ℕ => U (νN N) (CN N) / N) atTop (𝓝 d) := by
            have hs := tendsto_finsetSum Finset.univ (fun s _ => (hrate s).mul_const
              (Real.exp (-∑ j, y j * (A j s : ℝ))))
            have hc := tendsto_finsetSum Finset.univ (fun j _ => (hcap j).const_mul (y j))
            have hh := hs.add hc
            have he : (∑ s, ν s * Real.exp (-∑ j, y j * (A j s : ℝ))) + ∑ j, y j * C j = d := by
              simp_rw [← hxform]
              exact hdual
            rw [he] at hh
            convert hh using 1
            ext N
            dsimp [U]
            simp only [add_div, Finset.sum_div]
            congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
          have huUpper : ∀ N, u N ≤ U (νN N) (CN N) / N := by
            intro N
            apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
            have hp : 0 < P (νN N) (capInt (CN N)) := by
              rw [← hP, hpartitionFn]
              exact hpartitionpos _ (hνN N) _
            have hh := Real.log_le_log hp (hPupper _ (hνN N) (capInt (CN N)))
            rw [Real.log_exp] at hh
            exact hh
          have huLower : ∀ a : ℝ, 0 < a → a < 1 → ∀ᶠ N : ℕ in atTop,
              Real.log (KellyStochasticNetworks.lossWeight (νN N) (fun s => ⌊(N : ℝ) * (a * x s)⌋₊)) / N ≤ u N := by
            intro a ha ha1
            filter_upwards [hfloorfeas a ha ha1] with N hN
            apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
            apply Real.log_le_log (hwpos _ (hνN N) _)
            exact (hPsum _ (hνN N) _).le_tsum ⟨_, hN⟩ (fun n _ => (hwpos _ (hνN N) n).le)
          let a : ℕ → ℝ := fun k => 1 - 1 / ((k : ℝ) + 2)
          have ha0 : ∀ k, 0 < a k := by
            intro k
            dsimp [a]
            apply sub_pos.mpr
            apply (div_lt_one (by positivity : (0 : ℝ) < (k : ℝ) + 2)).mpr
            linarith [Nat.cast_nonneg (α := ℝ) k]
          have ha1 : ∀ k, a k < 1 := by
            intro k
            exact sub_lt_self _ (by positivity)
          have halim : Tendsto a atTop (𝓝 1) := by
            have ht : Tendsto (fun k : ℕ => (k : ℝ) + 2) atTop atTop := hNtop.atTop_add tendsto_const_nhds
            simpa only [sub_zero] using (ht.const_div_atTop (1 : ℝ)).const_sub 1
          have hentropy : Tendsto (fun k => KellyStochasticNetworks.LossLimits.entropyObjective ν
              (fun s => a k * x s)) atTop (𝓝 d) := by
            unfold KellyStochasticNetworks.LossLimits.entropyObjective
            have ht : ∀ s, Tendsto (fun k => a k * x s) atTop (𝓝 (x s)) := by
              intro s
              simpa only [one_mul] using halim.mul_const (x s)
            have hh := tendsto_finsetSum Finset.univ (fun s _ =>
              (((ht s).mul_const (Real.log (ν s))).sub
                ((ht s).mul ((Real.continuousAt_log (hxpos s).ne').tendsto.comp (ht s)))).add (ht s))
            exact hh
          have hulim : Tendsto u atTop (𝓝 d) := by
            apply tendsto_order.mpr
            constructor
            · intro b hb
              obtain ⟨k, hk⟩ := ((tendsto_order.mp hentropy).1 b hb).exists
              have ht := hweightlimit (fun s => a k * x s) (fun s => mul_pos (ha0 k) (hxpos s))
              filter_upwards [(tendsto_order.mp ht).1 b hk, huLower (a k) (ha0 k) (ha1 k)] with N hN hlow
              exact hN.trans_le hlow
            · intro b hb
              filter_upwards [(tendsto_order.mp hUlimit).2 b hb] with N hN
              exact (huUpper N).trans_lt hN
          let m : ℕ → ℝ := fun N => (νN N r * acceptance A (νN N) (capInt (CN N)) r) / N
          let V (t : ℝ) (N : ℕ) : ℝ :=
            U (Function.update (νN N) r (νN N r * Real.exp t)) (CN N) / N - u N
          have hVlim : ∀ t, Tendsto (V t) atTop (𝓝 (x r * (Real.exp t - 1))) := by
            intro t
            have he : ∀ N, U (Function.update (νN N) r (νN N r * Real.exp t)) (CN N) =
                U (νN N) (CN N) + νN N r * Real.exp (-∑ j, y j * (A j r : ℝ)) * (Real.exp t - 1) := by
              intro N
              dsimp [U]
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r),
                ← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
              simp only [Function.update_self]
              have hs : ∑ s ∈ Finset.univ.erase r,
                  Function.update (νN N) r (νN N r * Real.exp t) s * Real.exp (-∑ j, y j * (A j s : ℝ)) =
                  ∑ s ∈ Finset.univ.erase r, νN N s * Real.exp (-∑ j, y j * (A j s : ℝ)) := by
                apply Finset.sum_congr rfl
                intro s hs
                rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
              rw [hs]
              ring
            have hh := (hUlimit.add (((hrate r).mul_const (Real.exp (-∑ j, y j * (A j r : ℝ)))).mul_const
              (Real.exp t - 1))).sub hulim
            have ht : d + ν r * Real.exp (-∑ j, y j * (A j r : ℝ)) * (Real.exp t - 1) - d =
                x r * (Real.exp t - 1) := by rw [← hxform]; ring
            rw [ht] at hh
            convert hh using 1
            ext N
            dsimp [V]
            rw [he, add_div]
            ring
          have hVslope : ∀ t N, t * m N ≤ V t N := by
            intro t N
            have hv : ∀ s, 0 < Function.update (νN N) r (νN N r * Real.exp t) s := by
              intro s
              by_cases hs : s = r <;> simp [hs, hνN N s, hνN N r, Real.exp_pos]
            have hp : 0 < P (Function.update (νN N) r (νN N r * Real.exp t)) (capInt (CN N)) := by
              rw [← hP, hpartitionFn]
              exact hpartitionpos _ hv _
            have hu := Real.log_le_log hp (hPupper _ hv (capInt (CN N)))
            rw [Real.log_exp] at hu
            have hu' : Real.log (P (Function.update (νN N) r (νN N r * Real.exp t)) (capInt (CN N))) ≤
                U (Function.update (νN N) r (νN N r * Real.exp t)) (CN N) := by
              simpa only [U, capInt, Int.cast_natCast] using hu
            have hj := hJensen _ (hνN N) (CN N) t
            have hi : t * (νN N r * acceptance A (νN N) (capInt (CN N)) r) ≤
                U (Function.update (νN N) r (νN N r * Real.exp t)) (CN N) -
                  Real.log (P (νN N) (capInt (CN N))) := by linarith
            have hh := div_le_div_of_nonneg_right hi (Nat.cast_nonneg (α := ℝ) N)
            simpa only [m, V, u, sub_div, mul_div_assoc] using hh
          let q : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
          have hqpos : ∀ k, 0 < q k := by intro k; dsimp [q]; positivity
          have hqlim : Tendsto q atTop (𝓝 0) :=
            (hNtop.atTop_add tendsto_const_nhds).const_div_atTop 1
          have hslope : ∀ (f : ℕ → ℝ), Tendsto f atTop (𝓝 0) → (∀ k, f k ≠ 0) →
              Tendsto (fun k => x r * (Real.exp (f k) - 1) / f k) atTop (𝓝 (x r)) := by
            intro f hf hfne
            have hf' : Tendsto f atTop (𝓝[≠] (0 : ℝ)) := tendsto_nhdsWithin_iff.mpr
              ⟨hf, Filter.Eventually.of_forall (fun k => by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hfne k)⟩
            have hh := ((Real.hasDerivAt_exp 0).tendsto_slope_zero.comp hf').const_mul (x r)
            simpa only [Function.comp_def, zero_add, Real.exp_zero, mul_one, one_mul, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh
          have hmlim : Tendsto m atTop (𝓝 (x r)) := by
            apply tendsto_order.mpr
            constructor
            · intro b hb
              have hs := hslope (fun k => -q k) (by simpa only [neg_zero] using hqlim.neg)
                (fun k => neg_ne_zero.mpr (hqpos k).ne')
              obtain ⟨k, hk⟩ := ((tendsto_order.mp hs).1 b hb).exists
              have ht : -q k < 0 := neg_neg_of_pos (hqpos k)
              have hh := (hVlim (-q k)).div_const (-q k)
              filter_upwards [(tendsto_order.mp hh).1 b hk] with N hN
              have hmN : V (-q k) N / (-q k) ≤ m N := by
                apply (div_le_iff_of_neg ht).mpr
                simpa only [mul_comm] using hVslope (-q k) N
              exact hN.trans_le hmN
            · intro b hb
              have hs := hslope q hqlim (fun k => (hqpos k).ne')
              obtain ⟨k, hk⟩ := ((tendsto_order.mp hs).2 b hb).exists
              have hh := (hVlim (q k)).div_const (q k)
              filter_upwards [(tendsto_order.mp hh).2 b hk] with N hN
              have hmN : m N ≤ V (q k) N / q k := by
                apply (le_div_iff₀ (hqpos k)).mpr
                simpa only [mul_comm] using hVslope (q k) N
              exact hmN.trans_lt hN
          have hfinal := hmlim.div (hrate r) (hν r).ne'
          have hxratio : x r / ν r = ∏ j, (1 - B j) ^ A j r := by
            dsimp [x, KellyStochasticNetworks.LossLimits.carried]
            exact mul_div_cancel_left₀ _ (hν r).ne'
          rw [hxratio] at hfinal
          apply hfinal.congr'
          filter_upwards [hNtop.eventually_ne_atTop 0] with N hN
          dsimp [m]
          field_simp [(hνN N r).ne']
