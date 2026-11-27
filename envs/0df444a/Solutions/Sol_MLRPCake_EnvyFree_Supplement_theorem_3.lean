-- Prove2me | solution 1 for MLRPCake.EnvyFree.Supplement.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:09:49.588435+00:00
-- url     : https://prove2.me/submissions/234ebc05-9982-4641-b8f0-f3d3b07fe5bb

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model
import Definitions.Def_MLRPCake_EnvyFree_Supplement_Divisions
import Definitions.Def_MLRPCake_EnvyFree_Supplement_SocialDP

open MLRPCake
open MLRPCake.EnvyFree
open MLRPCake.EnvyFree.Supplement

/-- Theorem 3, p. 9: under MLRP and `λ`-Lipschitz queries, for every `η > 0` the §7 algorithm
(localize every switching point within `η/(nλ)`, then run the dynamic program on the sorted
estimates) returns an allocation whose social welfare is within `η` of the optimum over all
allocations, with work polynomial in `n`, `log λ` and `log(1/η)` (universal polynomial). -/
theorem solution : ∃ c : ℕ, ∀ (n : ℕ) (f : Fin n → ℝ → ℝ) (lam η : ℝ),
    1 ≤ n → IsInstance f → IsMLRP f → 1 ≤ lam → QueriesLipschitz f lam → 0 < η →
    IsAllocation (n := n) (swOutput f lam η) ∧
      (∀ (x : ℕ → ℝ) (σ : Equiv.Perm (Fin n)), IsAllocation (n := n) x →
        SW f x σ - η ≤ SW f (swOutput f lam η) (Equiv.refl (Fin n))) ∧
      (swCost f lam η : ℝ) ≤
        c * ((n : ℝ) + Real.logb 2 lam + max 0 (Real.logb 2 (1 / η)) + 1) ^ c := by
          set_option maxHeartbeats 4000000 in
          · refine ⟨16, ?_⟩
            intro n f lam η hn hI hM hlam hL hη
            have hlocI : ∀ (i j K s : ℕ), (locIter f i j K s).1 ≤ 2 ^ K ∧ (locIter f i j K s).2 ≤ 2 ^ K := by
              intro i j K s
              induction s with
              | zero => simp [locIter]
              | succ s ih =>
                simp only [locIter]
                split_ifs
                · exact ih
                · exact ⟨ih.1, by omega⟩
                · exact ⟨by omega, ih.2⟩
            have hSbd : ∀ y ∈ swGridSet f lam η, 0 ≤ y ∧ y ≤ 1 := by
              intro y hy
              simp only [swGridSet, Finset.mem_insert, Finset.mem_image] at hy
              rcases hy with rfl | rfl | ⟨p, -, rfl⟩
              · norm_num
              · norm_num
              · refine ⟨le_max_left _ _, max_le zero_le_one ?_⟩
                have h1 := (hlocI p.1 p.2 (locSteps (swGamma n lam η)) (locSteps (swGamma n lam η))).1
                have h2 : ((locIter f p.1 p.2 (locSteps (swGamma n lam η)) (locSteps (swGamma n lam η))).1 : ℝ)
                    ≤ 2 ^ locSteps (swGamma n lam η) := by exact_mod_cast h1
                rw [div_le_one (by positivity)]
                linarith
            have h0S : (0:ℝ) ∈ swGridSet f lam η := by simp [swGridSet]
            have h1S : (1:ℝ) ∈ swGridSet f lam η := by simp [swGridSet]
            have hLsort : (swGrid f lam η).Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
            have hmemL : ∀ y, y ∈ swGrid f lam η ↔ y ∈ swGridSet f lam η := fun y => Finset.mem_sort _
            have hLpos : 0 < (swGrid f lam η).length := List.length_pos_of_mem ((hmemL 0).2 h0S)
            have hgmono : ∀ s t, s ≤ t → t < (swGrid f lam η).length → swPoint f lam η s ≤ swPoint f lam η t := by
              intro s t hst ht
              unfold swPoint
              rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ ht]
              rcases hst.lt_or_eq with h | h
              · exact List.pairwise_iff_getElem.1 hLsort s t (by omega) ht h
              · subst h; exact le_rfl
            have hgbd : ∀ t, 0 ≤ swPoint f lam η t ∧ swPoint f lam η t ≤ 1 := by
              intro t
              unfold swPoint
              by_cases ht : t < (swGrid f lam η).length
              · rw [List.getD_eq_getElem _ _ ht]
                exact hSbd _ ((hmemL _).1 (List.getElem_mem ht))
              · rw [List.getD_eq_default _ _ (by omega)]; norm_num
            have hg0 : swPoint f lam η 0 = 0 := by
              obtain ⟨k, hk, hk0⟩ := List.getElem_of_mem ((hmemL 0).2 h0S)
              have := hgmono 0 k (Nat.zero_le _) hk
              have h' : swPoint f lam η k = 0 := by
                unfold swPoint; rw [List.getD_eq_getElem _ _ hk, hk0]
              linarith [(hgbd 0).1]
            have hgT : swPoint f lam η ((swGrid f lam η).length - 1) = 1 := by
              obtain ⟨k, hk, hk0⟩ := List.getElem_of_mem ((hmemL 1).2 h1S)
              have := hgmono k ((swGrid f lam η).length - 1) (by omega) (by omega)
              have h' : swPoint f lam η k = 1 := by
                unfold swPoint; rw [List.getD_eq_getElem _ _ hk, hk0]
              linarith [(hgbd ((swGrid f lam η).length - 1)).2]
            have hargle : ∀ (h : ℕ → ℝ) (t : ℕ), argmaxUpTo h t ≤ t := by
              intro h t
              induction t with
              | zero => simp [argmaxUpTo]
              | succ t ih => simp only [argmaxUpTo]; split_ifs <;> omega
            have hargmax : ∀ (h : ℕ → ℝ) (t s : ℕ), s ≤ t → h s ≤ h (argmaxUpTo h t) := by
              intro h t
              induction t with
              | zero => intro s hs; simp [argmaxUpTo]; rw [Nat.le_zero.1 hs]
              | succ t ih =>
                intro s hs
                simp only [argmaxUpTo]
                rcases Nat.lt_or_ge s (t+1) with h1 | h1
                · have := ih s (by omega)
                  split_ifs with h2
                  · linarith
                  · exact this
                · have : s = t + 1 := by omega
                  subst this
                  split_ifs with h2
                  · exact le_rfl
                  · exact not_lt.1 h2
            have hpredle : ∀ (comb : ℝ → ℝ → ℝ) (g : ℕ → ℝ) (k t : ℕ), dpPred f comb g k t ≤ t := by
              intro comb g k t
              rcases k with _ | _ | k
              · simp [dpPred]
              · simp [dpPred]
              · simp only [dpPred]; exact hargle _ _
            have hbackle : ∀ (comb : ℝ → ℝ → ℝ) (g : ℕ → ℝ) (T m : ℕ), dpBack f comb g T m ≤ T := by
              intro comb g T m
              induction m with
              | zero => simp [dpBack]
              | succ m ih => simp only [dpBack]; exact (hpredle _ _ _ _).trans ih
            have hbackn : dpBack f (· + ·) (swPoint f lam η) ((swGrid f lam η).length - 1) n = 0 := by
              have key : ∀ m T, n = m + 1 →
                  dpBack f (· + ·) (swPoint f lam η) T (m + 1) = 0 := by
                intro m T h
                simp only [dpBack]
                rw [show n - m = 1 by omega]
                simp [dpPred]
              have := key (n - 1) ((swGrid f lam η).length - 1) (by omega)
              rwa [Nat.sub_add_cancel hn] at this
            have hDP : ∀ s : ℕ → ℕ, s 0 = 0 → (∀ j < n, s j ≤ s (j+1)) → s n = (swGrid f lam η).length - 1 →
                ∑ j ∈ Finset.range n, eval f j (swPoint f lam η (s j)) (swPoint f lam η (s (j+1))) ≤
                  SW f (swOutput f lam η) (Equiv.refl (Fin n)) := by
              set g := swPoint f lam η with hgdef
              set T := (swGrid f lam η).length - 1 with hTdef
              have hgmono' : ∀ s t, s ≤ t → t ≤ T → g s ≤ g t := fun s t h1 h2 => hgmono s t h1 (by omega)
              show ∀ s : ℕ → ℕ, _ → _ → _ → _ ≤ SW f (dpCuts f (· + ·) g T) (Equiv.refl (Fin n))
              have hve : ∀ (k : ℕ) (a b : ℝ), a ≤ b → val f k a b = eval f k a b := by
                intro k a b hab
                unfold val eval
                rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Icc_eq_integral_Ioc]
              have A1 : ∀ k : ℕ, ∀ s : ℕ → ℕ, s 0 = 0 → (∀ j < k + 1, s j ≤ s (j+1)) →
                  ∑ j ∈ Finset.range (k+1), eval f j (g (s j)) (g (s (j+1))) ≤ dpVal f (· + ·) g (k+1) (s (k+1)) := by
                intro k
                induction k with
                | zero =>
                  intro s hs0 _
                  simp [dpVal, hs0]
                | succ k ih =>
                  intro s hs0 hs
                  rw [Finset.sum_range_succ]
                  have h1 := ih s hs0 (fun j hj => hs j (by omega))
                  have h2 := hargmax (dpCand f (· + ·) g (dpVal f (· + ·) g (k + 1)) (k + 1) (s (k+1+1))) (s (k+1+1)) (s (k+1)) (hs (k+1) (by omega))
                  simp only [dpVal]
                  simp only [dpCand] at h2 ⊢
                  linarith
              have A2 : ∀ k : ℕ, k + 1 ≤ n → dpVal f (· + ·) g (k+1) (dpBack f (· + ·) g T (n - (k+1))) =
                  ∑ i ∈ Finset.range (k+1), eval f i (g (dpBack f (· + ·) g T (n - i))) (g (dpBack f (· + ·) g T (n - (i+1)))) := by
                intro k
                induction k with
                | zero =>
                  intro hk
                  simp [dpVal, hbackn]
                | succ k ih =>
                  intro hk
                  rw [Finset.sum_range_succ, ← ih (by omega)]
                  have hb : dpBack f (· + ·) g T (n - (k+1)) = dpPred f (· + ·) g (k+2) (dpBack f (· + ·) g T (n - (k+1+1))) := by
                    rw [show n - (k+1) = (n - (k+1+1)) + 1 by omega, dpBack]
                    congr 1; omega
                  rw [hb]
                  simp only [dpVal, dpPred, dpCand]
              intro s hs0 hs hsn
              have e1 := A1 (n-1) s hs0 (fun j hj => hs j (by omega))
              rw [Nat.sub_add_cancel hn, hsn] at e1
              have e2 := A2 (n-1) (by omega)
              rw [Nat.sub_add_cancel hn, Nat.sub_self] at e2
              simp only [dpBack] at e2
              have e3 : SW f (dpCuts f (· + ·) g T) (Equiv.refl (Fin n)) =
                  ∑ i ∈ Finset.range n, eval f i (g (dpBack f (· + ·) g T (n - i))) (g (dpBack f (· + ·) g T (n - (i+1)))) := by
                unfold SW pieceVal dpCuts
                rw [← Fin.sum_univ_eq_sum_range (fun i => eval f i (g (dpBack f (· + ·) g T (n - i))) (g (dpBack f (· + ·) g T (n - (i+1))))) n]
                refine Finset.sum_congr rfl (fun i _ => ?_)
                simp only [Equiv.refl_apply]
                apply hve
                apply hgmono'
                · have : n - (i:ℕ) = (n - ((i:ℕ)+1)) + 1 := by omega
                  rw [this, dpBack]; exact hpredle _ _ _ _
                · exact hbackle _ _ _ _
              rw [e3, ← e2]
              exact e1
            have hAlloc : IsAllocation (n := n) (swOutput f lam η) := by
              refine ⟨?_, ?_, ?_⟩
              · simp only [swOutput, dpCuts, Nat.sub_zero]
                have key : ∀ m T, n = m + 1 →
                    dpBack f (· + ·) (swPoint f lam η) T (m + 1) = 0 := by
                  intro m T h
                  simp only [dpBack]
                  rw [show n - m = 1 by omega]
                  simp [dpPred]
                have := key (n - 1) ((swGrid f lam η).length - 1) (by omega)
                rw [Nat.sub_add_cancel hn] at this
                rw [this]; exact hg0
              · intro k hk
                simp only [swOutput, dpCuts]
                have : n - k = (n - (k+1)) + 1 := by omega
                rw [this, dpBack]
                apply hgmono _ _ (hpredle _ _ _ _)
                have := hbackle (· + ·) (swPoint f lam η) ((swGrid f lam η).length - 1) (n - (k+1))
                omega
              · simp only [swOutput, dpCuts, Nat.sub_self, dpBack]
                exact hgT
            refine ⟨hAlloc, ?_, ?_⟩
            · intro x σ hx
              have K : ∃ s : ℕ → ℕ, s 0 = 0 ∧ (∀ j < n, s j ≤ s (j+1)) ∧ s n = (swGrid f lam η).length - 1 ∧
                  SW f x σ - η ≤ ∑ j ∈ Finset.range n, eval f j (swPoint f lam η (s j)) (swPoint f lam η (s (j+1))) := by
                have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
                set Mx : ℝ → ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i => f i) with hMx
                have hfle : ∀ i t, f i t ≤ Mx t := by
                  intro i t
                  rw [hMx, Finset.sup'_apply]
                  exact Finset.le_sup' (fun j => f j t) (Finset.mem_univ i)
                have hMint : IntervalIntegrable Mx MeasureTheory.volume 0 1 := by
                  rw [hMx]
                  apply Finset.sup'_induction (p := fun h => IntervalIntegrable h MeasureTheory.volume 0 1)
                  · intro a ha b hb
                    rw [intervalIntegrable_iff] at ha hb ⊢
                    exact ha.sup hb
                  · intro i _
                    exact (hI i).2.2.1
                have hxmono : ∀ a b, a ≤ b → b ≤ n → x a ≤ x b := by
                  intro a b hab hb
                  induction b with
                  | zero => rw [Nat.le_zero.1 hab]
                  | succ b ih =>
                    rcases hab.lt_or_eq with h | h
                    · exact (ih (by omega) (by omega)).trans (hx.2.1 b (by omega))
                    · rw [h]
                have hxbd : ∀ k ≤ n, x k ∈ Set.Icc (0:ℝ) 1 := by
                  intro k hk
                  exact ⟨hx.1 ▸ hxmono 0 k (Nat.zero_le _) hk, hx.2.2 ▸ hxmono k n hk le_rfl⟩
                have hsub : ∀ k < n, Set.uIcc (x k) (x (k+1)) ⊆ Set.uIcc 0 1 := by
                  intro k hk
                  rw [Set.uIcc_of_le (hx.2.1 k hk), Set.uIcc_of_le zero_le_one]
                  exact Set.Icc_subset_Icc (hxbd k hk.le).1 (hxbd (k+1) hk).2
                have hdens : ∀ i : Fin n, dens f (i : ℕ) = f i := by
                  intro i; unfold dens; simp [i.isLt]
                have hUpper : SW f x σ ≤ ∫ t in (0:ℝ)..1, Mx t := by
                  have e1 : SW f x σ = ∑ k : Fin n, val f (σ.symm k) (x k) (x ((k:ℕ)+1)) := by
                    unfold SW pieceVal
                    exact (Equiv.sum_comp σ (fun k => val f (σ.symm k) (x k) (x ((k:ℕ)+1)))).symm.trans
                      (by simp) |>.symm
                  rw [e1]
                  have e2 : ∫ t in (0:ℝ)..1, Mx t = ∑ k ∈ Finset.range n, ∫ t in x k..x (k+1), Mx t := by
                    rw [intervalIntegral.sum_integral_adjacent_intervals (fun k hk => hMint.mono_set (hsub k hk)), hx.1, hx.2.2]
                  rw [e2, ← Fin.sum_univ_eq_sum_range (fun k => ∫ t in x k..x (k+1), Mx t) n]
                  refine Finset.sum_le_sum (fun k _ => ?_)
                  unfold val
                  rw [hdens]
                  exact intervalIntegral.integral_mono_on (hx.2.1 k k.isLt) (((hI _).2.2.1).mono_set (hsub k k.isLt))
                    (hMint.mono_set (hsub k k.isLt)) (fun t _ => hfle _ t)
                have hLower : ∃ s : ℕ → ℕ, s 0 = 0 ∧ (∀ j < n, s j ≤ s (j+1)) ∧ s n = (swGrid f lam η).length - 1 ∧
                    (∫ t in (0:ℝ)..1, Mx t) - η ≤
                      ∑ j ∈ Finset.range n, eval f j (swPoint f lam η (s j)) (swPoint f lam η (s (j+1))) := by
                  have hLip : ∀ k : Fin n, ∀ a b, a ∈ Set.Icc (0:ℝ) 1 → b ∈ Set.Icc (0:ℝ) 1 → a ≤ b →
                      ∫ t in a..b, f k t ≤ lam * (b - a) := by
                    intro k a b ha hb hab
                    have h := (hL k).1 a a a b ha ha ha hb
                    have h0 : eval f k a a = 0 := by
                      unfold eval; simp
                    have hv : eval f k a b = ∫ t in a..b, f k t := by
                      unfold eval
                      rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Icc_eq_integral_Ioc, hdens]
                    rw [h0, hv, sub_zero, sub_self, abs_zero, abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a),
                      max_eq_right (by linarith)] at h
                    exact (le_abs_self _).trans h
                  have hchain : ∀ d : ℕ, ∀ i j : Fin n, (j:ℕ) = i + d → ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ 1 →
                      f j x / f i x ≤ f j y / f i y := by
                    intro d
                    induction d with
                    | zero =>
                      intro i j hij x y hx hxy hy
                      have : i = j := Fin.ext (by omega)
                      subst this
                      have h1 := hM.1 i x ⟨hx, by linarith⟩
                      have h2 := hM.1 i y ⟨by linarith, hy⟩
                      rw [div_self h1.ne', div_self h2.ne']
                    | succ d ih =>
                      intro i j hij x y hx hxy hy
                      set m : Fin n := ⟨i + d, by omega⟩
                      have e1 := ih i m rfl x y hx hxy hy
                      have e2 := hM.2 m j (by simp [m]; omega) x y hx hxy hy
                      have px : ∀ k : Fin n, 0 < f k x := fun k => hM.1 k x ⟨hx, by linarith⟩
                      have py : ∀ k : Fin n, 0 < f k y := fun k => hM.1 k y ⟨by linarith, hy⟩
                      have r1 : f j x / f i x = (f j x / f m x) * (f m x / f i x) := by
                        field_simp [(px m).ne', (px i).ne']
                      have r2 : f j y / f i y = (f j y / f m y) * (f m y / f i y) := by
                        field_simp [(py m).ne', (py i).ne']
                      rw [r1, r2]
                      exact mul_le_mul e2 e1 (div_pos (px m) (px i)).le (div_pos (py j) (py m)).le
                  have hnR : (0:ℝ) < n := by exact_mod_cast hn
                  have hlamp : (0:ℝ) < lam := by linarith
                  have hγ : 0 < swGamma n lam η := by unfold swGamma; positivity
                  have hK : 2 / (2:ℝ) ^ locSteps (swGamma n lam η) ≤ swGamma n lam η := by
                    have h1 : Real.logb 2 (2 / swGamma n lam η) ≤ (locSteps (swGamma n lam η) : ℝ) := Nat.le_ceil _
                    have h2 : 2 / swGamma n lam η ≤ (2:ℝ) ^ (locSteps (swGamma n lam η) : ℝ) := by
                      calc 2 / swGamma n lam η = (2:ℝ) ^ (Real.logb 2 (2 / swGamma n lam η)) :=
                            (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
                        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
                    rw [Real.rpow_natCast] at h2
                    rw [div_le_iff₀ (by positivity)]
                    rw [div_le_iff₀ hγ] at h2
                    linarith
                  have hdint : ∀ j : ℕ, IntervalIntegrable (dens f j) MeasureTheory.volume 0 1 := by
                    intro j
                    unfold dens
                    split_ifs with h
                    · exact (hI ⟨j, h⟩).2.2.1
                    · exact intervalIntegrable_const
                  have hdon : ∀ j : ℕ, ∀ a b, 0 ≤ a → b ≤ 1 → MeasureTheory.IntegrableOn (dens f j) (Set.Icc a b) := by
                    intro j a b ha hb
                    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).1 (hdint j)).mono_set
                      (Set.Icc_subset_Icc ha hb)
                  have hdnn : ∀ j : ℕ, ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ dens f j t := by
                    intro j t ht; unfold dens; split_ifs with h
                    · exact (hI ⟨j,h⟩).1 t ht
                    · exact le_rfl
                  have hdpos : ∀ j < n, ∀ t ∈ Set.Icc (0:ℝ) 1, 0 < dens f j t := by
                    intro j hj t ht; unfold dens; rw [dif_pos hj]; exact hM.1 _ t ht
                  have hratio : ∀ i j : ℕ, i < j → j < n → ∀ x t : ℝ, 0 ≤ x → x ≤ t → t ≤ 1 →
                      dens f j x / dens f i x ≤ dens f j t / dens f i t := by
                    intro i j hij hj x t hx hxt ht
                    have := hchain (j - i) ⟨i, by omega⟩ ⟨j, hj⟩ (by simp; omega) x t hx hxt ht
                    unfold dens; rw [dif_pos hj, dif_pos (by omega : i < n)]; exact this
                  have hinv : ∀ (i j K s : ℕ), s ≤ K →
                      (locIter f i j K s).1 < (locIter f i j K s).2 ∧
                      (locIter f i j K s).2 ≤ (locIter f i j K s).1 + 2 ^ (K - s) ∧
                      ((locIter f i j K s).1 = 0 ∨ ¬ cellTest f i j K (locIter f i j K s).1) ∧
                      ((locIter f i j K s).2 = 2 ^ K ∨ cellTest f i j K (locIter f i j K s).2) := by
                    intro i j K s
                    induction s with
                    | zero => intro _; simp [locIter]
                    | succ s ih =>
                      intro hs
                      obtain ⟨h1, h2, h3, h4⟩ := ih (by omega)
                      have hp : 2 ^ (K - s) = 2 * 2 ^ (K - (s+1)) := by
                        rw [← pow_succ']; congr 1; omega
                      simp only [locIter]
                      split_ifs with c1 c2
                      · exact ⟨h1, by omega, h3, h4⟩
                      · exact ⟨by omega, by omega, h3, Or.inr c2⟩
                      · exact ⟨by omega, by omega, Or.inr c2, h4⟩
                  have hP1 : ∀ i j : ℕ, i < j → j < n → 0 < locLeft f i j (swGamma n lam η) →
                      ∀ t, 0 ≤ t → t ≤ locLeft f i j (swGamma n lam η) → dens f j t ≤ dens f i t := by
                    intro i j hij hj hq t ht0 htq
                    obtain ⟨h1, h2, h3, h4⟩ := hinv i j (locSteps (swGamma n lam η)) (locSteps (swGamma n lam η)) le_rfl
                    have hlo := (hlocI i j (locSteps (swGamma n lam η)) (locSteps (swGamma n lam η))).1
                    have hq' : locLeft f i j (swGamma n lam η) = max 0
                        ((((locIter f i j (locSteps (swGamma n lam η)) (locSteps (swGamma n lam η))).1 : ℝ) - 1) /
                          2 ^ locSteps (swGamma n lam η)) := rfl
                    set K := locSteps (swGamma n lam η)
                    set lo := (locIter f i j K K).1
                    have hD : (0:ℝ) < 2 ^ K := by positivity
                    have hpos : 0 < ((lo:ℝ) - 1) / 2 ^ K := by
                      rw [hq'] at hq
                      rcases lt_max_iff.1 hq with h | h
                      · exact absurd h (lt_irrefl 0)
                      · exact h
                    have hqe : locLeft f i j (swGamma n lam η) = ((lo:ℝ) - 1) / 2 ^ K := by
                      rw [hq']; exact max_eq_right hpos.le
                    have hlo1 : (1:ℝ) < lo := by
                      by_contra hc; push_neg at hc
                      exact absurd hpos (not_lt.2 (div_nonpos_of_nonpos_of_nonneg (by linarith) hD.le))
                    have hlo2 : 1 < lo := by exact_mod_cast hlo1
                    have hloK : (lo:ℝ) ≤ 2 ^ K := by exact_mod_cast hlo
                    by_contra hc
                    push_neg at hc
                    have hct : cellTest f i j K lo := by
                      unfold cellTest eval
                      apply MeasureTheory.setIntegral_mono_on (hdon i _ _ (by positivity) ?_) (hdon j _ _ (by positivity) ?_)
                        measurableSet_Icc
                      · intro x hx
                        have hx1 : x ≤ 1 := hx.2.trans (by rw [div_le_one hD]; exact hloK)
                        have htx : t ≤ x := htq.trans (hqe ▸ hx.1)
                        have hr := hratio i j hij hj t x ht0 htx hx1
                        have hi0 := hdpos i (by omega) t ⟨ht0, htx.trans hx1⟩
                        have hix := hdpos i (by omega) x ⟨ht0.trans htx, hx1⟩
                        have : 1 < dens f j t / dens f i t := (one_lt_div hi0).2 hc
                        exact ((one_lt_div hix).1 (this.trans_le hr)).le
                      · rw [div_le_one hD]; exact hloK
                      · rw [div_le_one hD]; exact hloK
                    rcases h3 with h | h
                    · omega
                    · exact h hct
                  have hP2 : ∀ i j : ℕ, i < j → j < n → locLeft f i j (swGamma n lam η) + swGamma n lam η < 1 →
                      ∀ t, t ≤ 1 → locLeft f i j (swGamma n lam η) + swGamma n lam η ≤ t → dens f i t ≤ dens f j t := by
                    intro i j hij hj hq t ht1 htq
                    obtain ⟨h1, h2, h3, h4⟩ := hinv i j (locSteps (swGamma n lam η)) (locSteps (swGamma n lam η)) le_rfl
                    have hhi := (hlocI i j (locSteps (swGamma n lam η)) (locSteps (swGamma n lam η))).2
                    have hq' : locLeft f i j (swGamma n lam η) = max 0
                        ((((locIter f i j (locSteps (swGamma n lam η)) (locSteps (swGamma n lam η))).1 : ℝ) - 1) /
                          2 ^ locSteps (swGamma n lam η)) := rfl
                    set K := locSteps (swGamma n lam η)
                    set lo := (locIter f i j K K).1
                    set hi := (locIter f i j K K).2
                    rw [Nat.sub_self, pow_zero] at h2
                    have hD : (0:ℝ) < 2 ^ K := by positivity
                    have hqge : ((lo:ℝ) - 1) / 2 ^ K ≤ locLeft f i j (swGamma n lam η) := hq' ▸ le_max_right _ _
                    have hq0 : 0 ≤ locLeft f i j (swGamma n lam η) := hq' ▸ le_max_left _ _
                    have hhiR : (hi:ℝ) ≤ lo + 1 := by exact_mod_cast h2
                    have hhi1 : (1:ℝ) ≤ hi := by exact_mod_cast (show 1 ≤ hi by omega)
                    have hhiK : (hi:ℝ) ≤ 2 ^ K := by exact_mod_cast hhi
                    have key : (hi:ℝ) / 2 ^ K ≤ locLeft f i j (swGamma n lam η) + swGamma n lam η := by
                      have e : (hi:ℝ) / 2 ^ K ≤ ((lo:ℝ) - 1) / 2 ^ K + 2 / 2 ^ K := by
                        rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hD.le
                      linarith
                    rcases h4 with h | hct
                    · exfalso
                      have : (hi:ℝ) = 2 ^ K := by rw [h]; push_cast; ring
                      have e : (1:ℝ) - 2 / 2 ^ K ≤ ((lo:ℝ) - 1) / 2 ^ K := by
                        rw [sub_div' (hc := hD.ne'), one_mul]
                        exact div_le_div_of_nonneg_right (by linarith) hD.le
                      linarith
                    · by_contra hc
                      push_neg at hc
                      have ht0 : 0 ≤ t := by linarith [hγ]
                      unfold cellTest eval at hct
                      have hB0 : (0:ℝ) ≤ ((hi:ℝ) - 1) / 2 ^ K := div_nonneg (by linarith) hD.le
                      have hB1 : (hi:ℝ) / 2 ^ K ≤ 1 := by rw [div_le_one hD]; exact hhiK
                      have hlt : 0 < ∫ x in Set.Icc (((hi:ℝ) - 1) / 2 ^ K) ((hi:ℝ) / 2 ^ K), (dens f i x - dens f j x) := by
                        have hpt : ∀ x ∈ Set.Icc (((hi:ℝ) - 1) / 2 ^ K) ((hi:ℝ) / 2 ^ K), dens f j x < dens f i x := by
                          intro x hx
                          have hxt : x ≤ t := hx.2.trans (key.trans htq)
                          have hr := hratio i j hij hj x t (hB0.trans hx.1) hxt ht1
                          have hit := hdpos i (by omega) t ⟨ht0, ht1⟩
                          have hix := hdpos i (by omega) x ⟨hB0.trans hx.1, hxt.trans ht1⟩
                          have : dens f j t / dens f i t < 1 := (div_lt_one hit).2 hc
                          exact (div_lt_one hix).1 (hr.trans_lt this)
                        rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae]
                        · have : Function.support (fun x => dens f i x - dens f j x) ∩
                              Set.Icc (((hi:ℝ) - 1) / 2 ^ K) ((hi:ℝ) / 2 ^ K) = Set.Icc (((hi:ℝ) - 1) / 2 ^ K) ((hi:ℝ) / 2 ^ K) := by
                            apply Set.inter_eq_right.2
                            intro x hx
                            simp only [Function.mem_support]
                            linarith [hpt x hx]
                          rw [this, Real.volume_Icc]
                          simp only [ENNReal.ofReal_pos]
                          rw [← sub_div]
                          apply div_pos (by linarith) hD
                        · refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall ?_)
                          intro x hx
                          simp only [Pi.zero_apply]
                          linarith [hpt x hx]
                        · exact (hdon i _ _ hB0 hB1).sub (hdon j _ _ hB0 hB1)
                      rw [MeasureTheory.integral_sub (hdon i _ _ hB0 hB1) (hdon j _ _ hB0 hB1)] at hlt
                      linarith
                  obtain ⟨N, hNdef⟩ : ∃ N : ℕ → ℝ → ℝ, N = fun k => (insert n (Finset.Ico k n)).sup' (Finset.insert_nonempty _ _) (fun j => dens f j) := ⟨_, rfl⟩
                  have hNapp : ∀ k t, N k t = (insert n (Finset.Ico k n)).sup' (Finset.insert_nonempty _ _) (fun j => dens f j t) := by
                    intro k t; rw [hNdef]; dsimp only; rw [Finset.sup'_apply]
                  have hNint : ∀ k, IntervalIntegrable (N k) MeasureTheory.volume 0 1 := by
                    intro k
                    rw [hNdef]
                    apply Finset.sup'_induction (p := fun h => IntervalIntegrable h MeasureTheory.volume 0 1)
                    · intro a ha b hb
                      rw [intervalIntegrable_iff] at ha hb ⊢
                      exact ha.sup hb
                    · intro i _; exact hdint i
                  have hNle : ∀ k j t, j ∈ insert n (Finset.Ico k n) → dens f j t ≤ N k t := by
                    intro k j t hj; rw [hNapp]; exact Finset.le_sup' (fun j => dens f j t) hj
                  have hNge : ∀ k t B, (∀ j ∈ insert n (Finset.Ico k n), dens f j t ≤ B) → N k t ≤ B := by
                    intro k t B h; rw [hNapp]; exact Finset.sup'_le _ _ h
                  have hdn : ∀ t, dens f n t = 0 := by intro t; unfold dens; simp
                  have hN0 : ∀ k t, 0 ≤ N k t := fun k t => (hdn t).symm.le.trans (hNle k n t (Finset.mem_insert_self _ _))
                  have hsubI : ∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → Set.uIcc a b ⊆ Set.uIcc 0 1 := by
                    intro a b h1 h2 h3 h4
                    apply Set.uIcc_subset_uIcc
                    · rw [Set.uIcc_of_le zero_le_one]; exact ⟨h1, h2⟩
                    · rw [Set.uIcc_of_le zero_le_one]; exact ⟨h3, h4⟩
                  have hNI : ∀ k (a b : ℝ), 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → IntervalIntegrable (N k) MeasureTheory.volume a b :=
                    fun k a b h1 h2 h3 h4 => (hNint k).mono_set (hsubI a b h1 h2 h3 h4)
                  have hDI : ∀ k (a b : ℝ), 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → IntervalIntegrable (dens f k) MeasureTheory.volume a b :=
                    fun k a b h1 h2 h3 h4 => (hdint k).mono_set (hsubI a b h1 h2 h3 h4)
                  have hgS : ∀ y ∈ swGridSet f lam η, ∃ b < (swGrid f lam η).length, swPoint f lam η b = y := by
                    intro y hy
                    obtain ⟨b, hb, hby⟩ := List.getElem_of_mem ((hmemL y).2 hy)
                    exact ⟨b, hb, by unfold swPoint; rw [List.getD_eq_getElem _ _ hb, hby]⟩
                  have hClaim : ∀ d : ℕ, d < n → ∀ a : ℕ, a < (swGrid f lam η).length →
                      ∃ s : ℕ → ℕ, s (n - 1 - d) = a ∧ (∀ j, n - 1 - d ≤ j → j < n → s j ≤ s (j+1)) ∧
                        s n = (swGrid f lam η).length - 1 ∧
                        (∫ t in (swPoint f lam η a)..1, N (n - 1 - d) t) - d * (lam * swGamma n lam η) ≤
                          ∑ j ∈ Finset.Ico (n - 1 - d) n,
                            ∫ t in (swPoint f lam η (s j))..(swPoint f lam η (s (j+1))), dens f j t := by
                    intro d
                    induction d with
                    | zero =>
                      intro _ a ha
                      refine ⟨fun j => if j = n - 1 then a else (swGrid f lam η).length - 1, by simp, ?_, ?_, ?_⟩
                      · intro j hj1 hj2
                        have : j = n - 1 := by omega
                        subst this
                        have hne : (n - 1 + 1 = n - 1) = False := eq_false (by omega)
                        simp only [hne, if_false, ↓reduceIte]
                        omega
                      · have hne : (n = n - 1) = False := eq_false (by omega)
                        simp only [hne, if_false]
                      · rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), show n - 1 - 0 + 1 = n by omega,
                          Finset.Ico_self, Finset.sum_empty, add_zero]
                        simp only [Nat.sub_zero, Nat.cast_zero, zero_mul, sub_zero]
                        have hne : (n = n - 1) = False := eq_false (by omega)
                        simp only [hne, if_false, ↓reduceIte]
                        rw [hgT]
                        have hga := hgbd a
                        apply intervalIntegral.integral_mono_on hga.2 (hNI _ _ _ hga.1 hga.2 zero_le_one le_rfl)
                          (hDI _ _ _ hga.1 hga.2 zero_le_one le_rfl)
                        intro t ht
                        apply hNge
                        intro j hj
                        rcases Finset.mem_insert.1 hj with h | h
                        · rw [h, hdn]; exact hdnn _ t ⟨hga.1.trans ht.1, ht.2⟩
                        · have : j = n - 1 := by rw [Finset.mem_Ico] at h; omega
                          rw [this]
                    | succ d ih =>
                      intro hd a ha
                      obtain ⟨k, hk⟩ : ∃ k, k = n - 1 - (d+1) := ⟨_, rfl⟩
                      have hk1 : n - 1 - d = k + 1 := by omega
                      rw [hk1] at ih
                      rw [← hk]
                      have hne : (Finset.Ico (k+1) n).Nonempty := ⟨k+1, Finset.mem_Ico.2 ⟨le_rfl, by omega⟩⟩
                      set Q := (Finset.Ico (k+1) n).inf' hne (fun j => locLeft f k j (swGamma n lam η)) with hQ
                      obtain ⟨j0, hj0mem, hj0⟩ := Finset.exists_mem_eq_inf' hne (fun j => locLeft f k j (swGamma n lam η))
                      rw [← hQ] at hj0
                      have hj0' := Finset.mem_Ico.1 hj0mem
                      have hQS : Q ∈ swGridSet f lam η := by
                        rw [hj0]
                        unfold swGridSet
                        apply Finset.mem_insert_of_mem; apply Finset.mem_insert_of_mem
                        apply Finset.mem_image.2
                        exact ⟨(k, j0), by unfold pairs; simp; omega, rfl⟩
                      obtain ⟨b, hb, hgb⟩ := hgS Q hQS
                      obtain ⟨a', ha', haa', hga'⟩ : ∃ a', a' < (swGrid f lam η).length ∧ a ≤ a' ∧
                          swPoint f lam η a' = max (swPoint f lam η a) Q := by
                        by_cases hc : Q ≤ swPoint f lam η a
                        · exact ⟨a, ha, le_rfl, (max_eq_left hc).symm⟩
                        · push_neg at hc
                          refine ⟨b, hb, ?_, by rw [max_eq_right hc.le, hgb]⟩
                          by_contra hc2; push_neg at hc2
                          have := hgmono b a hc2.le ha
                          linarith
                      obtain ⟨s', hs'k, hs'm, hs'n, hs'v⟩ := ih (by omega) a' ha'
                      refine ⟨fun j => if j = k then a else s' j, by simp, ?_, ?_, ?_⟩
                      · intro j hj1 hj2
                        rcases Nat.eq_or_lt_of_le hj1 with h | h
                        · subst h
                          have hne : (k + 1 = k) = False := eq_false (by omega)
                          simp only [hne, if_false, ↓reduceIte]
                          rw [hs'k]; exact haa'
                        · have hne : (j = k) = False := eq_false (by omega)
                          have hne2 : (j + 1 = k) = False := eq_false (by omega)
                          simp only [hne, hne2, if_false]
                          exact hs'm j (by omega) hj2
                      · have hne : (n = k) = False := eq_false (by omega)
                        simp only [hne, if_false]; exact hs'n
                      · rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]
                        have hrest : ∑ j ∈ Finset.Ico (k+1) n, ∫ t in (swPoint f lam η ((fun j => if j = k then a else s' j) j))..(swPoint f lam η ((fun j => if j = k then a else s' j) (j+1))), dens f j t
                            = ∑ j ∈ Finset.Ico (k+1) n, ∫ t in (swPoint f lam η (s' j))..(swPoint f lam η (s' (j+1))), dens f j t := by
                          refine Finset.sum_congr rfl (fun j hj => ?_)
                          rw [Finset.mem_Ico] at hj
                          have hne : (j = k) = False := eq_false (by omega)
                          have hne2 : (j + 1 = k) = False := eq_false (by omega)
                          simp only [hne, hne2, if_false]
                        rw [hrest]
                        have hne : (k + 1 = k) = False := eq_false (by omega)
                        simp only [hne, if_false, ↓reduceIte]
                        rw [hs'k, hga']
                        set y := swPoint f lam η a with hy
                        set R := max y Q with hR
                        have hy0 := (hgbd a).1
                        have hy1 := (hgbd a).2
                        have hR1 : R ≤ 1 := by rw [← hga']; exact (hgbd a').2
                        have hyR : y ≤ R := le_max_left _ _
                        have hQR : Q ≤ R := le_max_right _ _
                        have hR0 : 0 ≤ R := hy0.trans hyR
                        have hkn : k < n := by omega
                        have hdk : dens f k = f ⟨k, hkn⟩ := hdens ⟨k, hkn⟩
                        -- I1
                        have I1 := intervalIntegral.integral_add_adjacent_intervals (hNI k y R hy0 hy1 hR0 hR1) (hNI k R 1 hR0 hR1 zero_le_one le_rfl)
                        have I2 : ∫ t in y..R, N k t ≤ ∫ t in y..R, dens f k t := by
                          rcases eq_or_lt_of_le hyR with h | h
                          · rw [h, intervalIntegral.integral_same, intervalIntegral.integral_same]
                          · have hRQ : R = Q := by
                              rcases le_or_gt Q y with h2 | h2
                              · rw [hR, max_eq_left h2] at h; exact absurd h (lt_irrefl _)
                              · rw [hR, max_eq_right h2.le]
                            apply intervalIntegral.integral_mono_on hyR (hNI k y R hy0 hy1 hR0 hR1) (hDI k y R hy0 hy1 hR0 hR1)
                            intro t ht
                            apply hNge
                            intro j hj
                            rcases Finset.mem_insert.1 hj with hj | hj
                            · rw [hj, hdn]; exact hdnn _ t ⟨hy0.trans ht.1, ht.2.trans hR1⟩
                            · rw [Finset.mem_Ico] at hj
                              rcases Nat.eq_or_lt_of_le hj.1 with hj2 | hj2
                              · rw [hj2]
                              · have hqj : Q ≤ locLeft f k j (swGamma n lam η) :=
                                  Finset.inf'_le _ (Finset.mem_Ico.2 ⟨hj2, hj.2⟩)
                                exact hP1 k j hj2 hj.2 (by linarith) t (hy0.trans ht.1) (by linarith [ht.2])
                        set m := min 1 (R + swGamma n lam η) with hm
                        have hRm : R ≤ m := le_min hR1 (by linarith)
                        have hm1 : m ≤ 1 := min_le_left _ _
                        have hm0 : 0 ≤ m := hR0.trans hRm
                        have I3 := intervalIntegral.integral_add_adjacent_intervals (hNI k R m hR0 hR1 hm0 hm1) (hNI k m 1 hm0 hm1 zero_le_one le_rfl)
                        have I7 := intervalIntegral.integral_add_adjacent_intervals (hNI (k+1) R m hR0 hR1 hm0 hm1) (hNI (k+1) m 1 hm0 hm1 zero_le_one le_rfl)
                        have I4 : ∫ t in R..m, N k t ≤ (∫ t in R..m, N (k+1) t) + ∫ t in R..m, dens f k t := by
                          rw [← intervalIntegral.integral_add (hNI (k+1) R m hR0 hR1 hm0 hm1) (hDI k R m hR0 hR1 hm0 hm1)]
                          apply intervalIntegral.integral_mono_on hRm (hNI k R m hR0 hR1 hm0 hm1)
                            ((hNI (k+1) R m hR0 hR1 hm0 hm1).add (hDI k R m hR0 hR1 hm0 hm1))
                          intro t ht
                          have ht01 : t ∈ Set.Icc (0:ℝ) 1 := ⟨hR0.trans ht.1, ht.2.trans hm1⟩
                          apply hNge
                          intro j hj
                          rcases Finset.mem_insert.1 hj with hj | hj
                          · rw [hj, hdn]; linarith [hN0 (k+1) t, hdnn k t ht01]
                          · rw [Finset.mem_Ico] at hj
                            rcases Nat.eq_or_lt_of_le hj.1 with hj2 | hj2
                            · rw [← hj2]; linarith [hN0 (k+1) t]
                            · have := hNle (k+1) j t (Finset.mem_insert_of_mem (Finset.mem_Ico.2 ⟨hj2, hj.2⟩))
                              linarith [hdnn k t ht01]
                        have I5 : ∫ t in R..m, dens f k t ≤ lam * swGamma n lam η := by
                          rw [hdk]
                          have := hLip ⟨k, hkn⟩ R m ⟨hR0, hR1⟩ ⟨hm0, hm1⟩ hRm
                          have hmR : m - R ≤ swGamma n lam η := by
                            have := min_le_right 1 (R + swGamma n lam η); linarith only [this, hm]
                          exact this.trans (mul_le_mul_of_nonneg_left hmR hlamp.le)
                        have I6 : ∫ t in m..1, N k t ≤ ∫ t in m..1, N (k+1) t := by
                          rcases eq_or_lt_of_le hm1 with h | h
                          · rw [h, intervalIntegral.integral_same, intervalIntegral.integral_same]
                          · have hm' : m = R + swGamma n lam η := by
                              rcases le_or_gt 1 (R + swGamma n lam η) with h2 | h2
                              · rw [hm, min_eq_left h2] at h; exact absurd h (lt_irrefl _)
                              · rw [hm, min_eq_right h2.le]
                            apply intervalIntegral.integral_mono_on hm1 (hNI k m 1 hm0 hm1 zero_le_one le_rfl)
                              (hNI (k+1) m 1 hm0 hm1 zero_le_one le_rfl)
                            intro t ht
                            apply hNge
                            intro j hj
                            rcases Finset.mem_insert.1 hj with hj | hj
                            · rw [hj]; exact hNle (k+1) n t (Finset.mem_insert_self _ _)
                            · rw [Finset.mem_Ico] at hj
                              rcases Nat.eq_or_lt_of_le hj.1 with hj2 | hj2
                              · rw [← hj2]
                                have hq0 : locLeft f k j0 (swGamma n lam η) = Q := hj0.symm
                                have := hP2 k j0 (by omega) hj0'.2 (by rw [hq0]; linarith) t ht.2 (by rw [hq0]; linarith [ht.1])
                                exact this.trans (hNle (k+1) j0 t (Finset.mem_insert_of_mem hj0mem))
                              · exact hNle (k+1) j t (Finset.mem_insert_of_mem (Finset.mem_Ico.2 ⟨hj2, hj.2⟩))
                        have hc : ((d+1 : ℕ):ℝ) * (lam * swGamma n lam η) = d * (lam * swGamma n lam η) + lam * swGamma n lam η := by
                          rw [Nat.cast_succ, add_mul, one_mul]
                        rw [hga'] at hs'v
                        linarith only [I1, I2, I3, I4, I5, I6, I7, hs'v, hc]
                  have hC := hClaim (n-1) (by omega) 0 hLpos
                  rw [Nat.sub_self] at hC
                  obtain ⟨s, hs0, hsm, hsn, hval⟩ := hC
                  refine ⟨s, hs0, fun j hj => hsm j (Nat.zero_le _) hj, hsn, ?_⟩
                  have hMN : ∫ t in (0:ℝ)..1, Mx t ≤ ∫ t in (0:ℝ)..1, N 0 t := by
                    apply intervalIntegral.integral_mono_on zero_le_one hMint (hNint 0)
                    intro t ht
                    rw [hMx, Finset.sup'_apply]
                    apply Finset.sup'_le
                    intro i _
                    rw [← hdens i]
                    exact hNle 0 i t (Finset.mem_insert_of_mem (Finset.mem_Ico.2 ⟨Nat.zero_le _, i.isLt⟩))
                  rw [hg0] at hval
                  have hsT : ∀ m j, j + m = n → s j ≤ s n := by
                    intro m
                    induction m with
                    | zero => intro j h; rw [show j = n by omega]
                    | succ m ih => intro j h; exact (hsm j (Nat.zero_le _) (by omega)).trans (ih (j+1) (by omega))
                  have hsum : ∑ j ∈ Finset.Ico 0 n, ∫ t in (swPoint f lam η (s j))..(swPoint f lam η (s (j+1))), dens f j t
                      = ∑ j ∈ Finset.range n, eval f j (swPoint f lam η (s j)) (swPoint f lam η (s (j+1))) := by
                    rw [Finset.range_eq_Ico]
                    refine Finset.sum_congr rfl (fun j hj => ?_)
                    rw [Finset.mem_Ico] at hj
                    unfold eval
                    rw [intervalIntegral.integral_of_le ?_, MeasureTheory.integral_Icc_eq_integral_Ioc]
                    apply hgmono _ _ (hsm j (Nat.zero_le _) hj.2)
                    have := hsT (n - (j+1)) (j+1) (by omega)
                    omega
                  have hloss : ((n - 1 : ℕ) : ℝ) * (lam * swGamma n lam η) ≤ η := by
                    have e : lam * swGamma n lam η = η / n := by unfold swGamma; field_simp
                    rw [e]
                    have : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
                    calc ((n - 1 : ℕ) : ℝ) * (η / n) ≤ n * (η / n) := mul_le_mul_of_nonneg_right this (by positivity)
                      _ = η := by field_simp
                  linarith only [hMN, hval, hloss, hsum]
                obtain ⟨s, hs0, hs, hsn, hK⟩ := hLower
                exact ⟨s, hs0, hs, hsn, by linarith only [hK, hUpper]⟩
              obtain ⟨s, hs0, hs, hsn, hK⟩ := K
              exact hK.trans (hDP s hs0 hs hsn)
            ·
              set B := (n : ℝ) + Real.logb 2 lam + max 0 (Real.logb 2 (1 / η)) + 1 with hB
              have hN1 : (1:ℝ) ≤ n := by exact_mod_cast hn
              have hloglam : 0 ≤ Real.logb 2 lam := Real.logb_nonneg (by norm_num) hlam
              have hB2 : 2 ≤ B := by have := le_max_left 0 (Real.logb 2 (1 / η)); linarith
              have hNB : (n:ℝ) ≤ B := by have := le_max_left 0 (Real.logb 2 (1 / η)); linarith
              have hP : (pairs n).card ≤ n * n := by
                unfold pairs
                exact (Finset.card_filter_le _ _).trans (by simp)
              have hG : (swGrid f lam η).length ≤ n * n + 2 := by
                unfold swGrid
                rw [Finset.length_sort]
                unfold swGridSet
                refine (Finset.card_insert_le _ _).trans ?_
                have := Finset.card_insert_le (1:ℝ) ((pairs n).image (fun p => locLeft f p.1 p.2 (swGamma n lam η)))
                have := Finset.card_image_le (s := pairs n) (f := fun p => locLeft f p.1 p.2 (swGamma n lam η))
                omega
              have hD : ∀ G, dpQueries n G ≤ G + n * (G * (G + 1)) := by
                intro G
                unfold dpQueries
                have : (n - 1) * (G * (G + 1) / 2) ≤ n * (G * (G + 1)) :=
                  Nat.mul_le_mul (Nat.sub_le _ _) (Nat.div_le_self _ _)
                omega
              have hlogn : Real.logb 2 n ≤ 2 * n := by
                have h1 := Real.log_le_sub_one_of_pos (show (0:ℝ) < n by linarith)
                have h2 : (1/2 : ℝ) < Real.log 2 := by
                  have := Real.log_two_gt_d9; linarith
                rw [Real.logb, div_le_iff₀ (by linarith)]
                have h3 := mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ 2 * Real.log 2 by linarith) (Nat.cast_nonneg n : (0:ℝ) ≤ n)
                linarith only [h1, h3]
              have hQ : (locSteps (swGamma n lam η) : ℝ) ≤ 3 * B := by
                unfold locSteps swGamma
                have hx : Real.logb 2 (2 / (η / (n * lam))) ≤ 2 * B := by
                  have : 2 / (η / (n * lam)) = 2 * n * lam * (1 / η) := by field_simp
                  rw [this, Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) (by positivity),
                    Real.logb_mul (by positivity) (by positivity), Real.logb_self_eq_one (by norm_num)]
                  have := le_max_right 0 (Real.logb 2 (1 / η))
                  linarith
                rcases le_or_gt 0 (Real.logb 2 (2 / (η / (n * lam)))) with h | h
                · have := Nat.ceil_lt_add_one h; linarith
                · rw [Nat.ceil_eq_zero.2 h.le]; simp; linarith
              have hcost : swCost f lam η ≤ (pairs n).card * (2 * locSteps (swGamma n lam η)) +
                  ((swGrid f lam η).length + n * ((swGrid f lam η).length * ((swGrid f lam η).length + 1))) := by
                unfold swCost locQueries
                have := hD (swGrid f lam η).length
                omega
              have hcostR : (swCost f lam η : ℝ) ≤ ((pairs n).card : ℝ) * (2 * (locSteps (swGamma n lam η) : ℝ)) +
                  (((swGrid f lam η).length : ℝ) + n * (((swGrid f lam η).length : ℝ) * (((swGrid f lam η).length : ℝ) + 1))) := by
                exact_mod_cast hcost
              clear_value B
              have hPR : ((pairs n).card : ℝ) ≤ B ^ 2 := by
                have : ((pairs n).card : ℝ) ≤ (n:ℝ) * n := by exact_mod_cast hP
                have h2 : (n:ℝ) * n ≤ B ^ 2 := by rw [pow_two]; exact mul_le_mul hNB hNB (Nat.cast_nonneg _) (by linarith)
                linarith only [this, h2]
              have hGR : ((swGrid f lam η).length : ℝ) ≤ 2 * B ^ 2 := by
                have : ((swGrid f lam η).length : ℝ) ≤ (n:ℝ) * n + 2 := by exact_mod_cast hG
                have h2 : (n:ℝ) * n ≤ B ^ 2 := by rw [pow_two]; exact mul_le_mul hNB hNB (Nat.cast_nonneg _) (by linarith)
                have h4 : (2:ℝ) * 2 ≤ B ^ 2 := by rw [pow_two]; exact mul_le_mul hB2 hB2 (by norm_num) (by linarith)
                linarith only [this, h2, h4]
              have hGR0 : (0:ℝ) ≤ ((swGrid f lam η).length : ℝ) := by positivity
              have hQ0 : (0:ℝ) ≤ (locSteps (swGamma n lam η) : ℝ) := by positivity
              have hP0 : (0:ℝ) ≤ ((pairs n).card : ℝ) := by positivity
              have t1 : ((pairs n).card : ℝ) * (2 * (locSteps (swGamma n lam η) : ℝ)) ≤ 6 * B ^ 3 := by
                have := mul_le_mul hPR (show 2 * (locSteps (swGamma n lam η) : ℝ) ≤ 6 * B by linarith) (by positivity) (by positivity)
                have e : B ^ 2 * (6 * B) = 6 * B ^ 3 := by ring
                linarith only [this, e]
              have t3 : (n:ℝ) * (((swGrid f lam η).length : ℝ) * (((swGrid f lam η).length : ℝ) + 1)) ≤ 6 * B ^ 5 := by
                have a1 : ((swGrid f lam η).length : ℝ) + 1 ≤ 3 * B ^ 2 := by
                  have h4 : (2:ℝ) * 2 ≤ B ^ 2 := by rw [pow_two]; exact mul_le_mul hB2 hB2 (by norm_num) (by linarith)
                  linarith only [hGR, h4]
                have a2 := mul_le_mul hGR a1 (by positivity) (by positivity)
                have a3 := mul_le_mul hNB a2 (by positivity) (by positivity)
                have e : B * (2 * B ^ 2 * (3 * B ^ 2)) = 6 * B ^ 5 := by ring
                linarith only [a3, e]
              have hB1 : (1:ℝ) ≤ B := by linarith
              have p2 : B ^ 2 ≤ B ^ 16 := pow_le_pow_right₀ hB1 (by norm_num)
              have p3 : B ^ 3 ≤ B ^ 16 := pow_le_pow_right₀ hB1 (by norm_num)
              have p5 : B ^ 5 ≤ B ^ 16 := pow_le_pow_right₀ hB1 (by norm_num)
              have h16 : ((16:ℕ):ℝ) = 16 := by norm_num
              rw [h16]
              refine hcostR.trans ((add_le_add t1 (add_le_add hGR t3)).trans ?_)
              linarith only [p2, p3, p5, pow_nonneg (show (0:ℝ) ≤ B by linarith) 16]
