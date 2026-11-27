-- Prove2me | solution 1 for MarketInterference.FluidBias.Supplement.theorem_5_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:10:41.609698+00:00
-- url     : https://prove2.me/submissions/49ab4983-109b-4849-a665-a0e52952a7af

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_Supplement_RandomAllocation

open MarketInterference
open MarketInterference.FluidBias
open MarketInterference.FluidBias.Supplement

open MeasureTheory Filter

/-- Assumptions 1 and 2 alone do not imply existence of the displayed RCT variance limit. -/
theorem solution :
    (∃! x, IsOptimal varianceNetwork 1 (fun _ => 2) (fun _ => 1) x) ∧
    (∃! q, IsOptimalDual varianceNetwork 1 (fun _ => 2) (fun _ => 1) q) ∧
    (∀ n, IsProbabilityMeasure (varianceLaw (n + 1)) ∧
      HasExperimentLaw (varianceLaw (n + 1)) Prod.fst (fun _ => 2) (fun _ => 0)
        (fun _ => 1) (1/2) (n + 1 : ℕ)) ∧
    ∃ A : ∀ n : ℕ, BlindAllocation varianceNetwork (varianceLaw (n + 1)) Prod.fst (n + 1 : ℕ),
      (∀ n, ∀ᵐ ω ∂varianceLaw (n + 1), (A n).total ω =
        Finsupp.single variancePath (matchedCount (n + 1) ω.1 : ℝ)) ∧
      (∀ n, ∀ᵐ ω ∂varianceLaw (n + 1),
        (A n).control ω = Finsupp.single variancePath (alternatingControl (n + 1) ω : ℝ) ∧
        (A n).treatment ω = Finsupp.single variancePath
          ((matchedCount (n + 1) ω.1 : ℝ) - (alternatingControl (n + 1) ω : ℝ))) ∧
      (∀ n, MemLp (fun ω => Real.sqrt (n + 1 : ℕ) *
        rctEst varianceNetwork (varianceLaw (n + 1)) Prod.fst (1/2) (n + 1 : ℕ) (A n) ω)
        2 (varianceLaw (n + 1))) ∧
      (let V := fun n => rctScaledVariance varianceNetwork (varianceLaw (n + 1))
        Prod.fst (1/2) (n + 1 : ℕ) (A n)
       Tendsto (fun n => V (2 * n + 1)) atTop (nhds 2) ∧
       Tendsto (fun n => V (2 * n)) atTop atTop ∧
       ¬ ∃ v : ℝ, Tendsto V atTop (nhds v)) := by
         set_option maxHeartbeats 10000000 in
         open ProbabilityTheory Real in
         focus
           have hR : ∀ (C T S k m : ℝ), 0 ≤ C → 0 ≤ T → 0 ≤ S → 1 ≤ k → m = min (C + T) (min S (3 * k)) →
               ((T - C) * (2 * m - (C + T)) / (C + T))^2 ≤
                 900 * ((C - k)^4 + (T - k)^4 + (S - k)^4) / k^2 := by
             intro C T S k m hC hT hS hk hm
             have hk0 : 0 < k := lt_of_lt_of_le one_pos hk
             have hm0 : 0 ≤ m := by rw [hm]; exact le_min (add_nonneg hC hT) (le_min hS (by linarith only [hk0]))
             have hmD : m ≤ C + T := by rw [hm]; exact min_le_left _ _
             have h3 : (2 * m - (C + T))^2 ≤ (2 * S - (C + T))^2 + (C + T - 2 * k)^2 := by
               have he := sq_nonneg (C + T - 2 * k)
               rcases le_total (C + T) (min S (3 * k)) with h | h
               · rw [hm, min_eq_left h]
                 have h1 : C + T ≤ S := h.trans (min_le_left _ _)
                 have := pow_le_pow_left₀ (by linarith only [hC, hT] : 0 ≤ 2 * (C + T) - (C + T))
                   (by linarith only [h1] : 2 * (C + T) - (C + T) ≤ 2 * S - (C + T)) 2
                 exact this.trans (le_add_of_nonneg_right he)
               · rw [hm, min_eq_right h]
                 rcases le_total S (3 * k) with h' | h'
                 · rw [min_eq_left h']; exact le_add_of_nonneg_right he
                 · rw [min_eq_right h'] at h ⊢
                   rcases le_total (C + T) (6 * k) with h'' | h''
                   · have := pow_le_pow_left₀ (by linarith only [h''] : 0 ≤ 2 * (3 * k) - (C + T))
                       (by linarith only [h'] : 2 * (3 * k) - (C + T) ≤ 2 * S - (C + T)) 2
                     exact this.trans (le_add_of_nonneg_right he)
                   · have := pow_le_pow_left₀ (by linarith only [h''] : 0 ≤ (C + T) - 2 * (3 * k))
                       (by linarith only [hk0] : (C + T) - 2 * (3 * k) ≤ C + T - 2 * k) 2
                     have e : (2 * (3 * k) - (C + T))^2 = ((C + T) - 2 * (3 * k))^2 := by ring
                     rw [e]
                     exact this.trans (le_add_of_nonneg_left (sq_nonneg _))
             have h2 : ((T - C) * (2 * m - (C + T)) / (C + T))^2 ≤
                 (T - C)^2 * ((2 * m - (C + T))^2 + (C + T - 2 * k)^2) / k^2 := by
               have h2g : ∀ a W D e : ℝ, W^2 ≤ D^2 → (D ≤ k → k^2 ≤ e^2) →
                   (a * W / D)^2 ≤ a^2 * (W^2 + e^2) / k^2 := by
                 intro a W D e hWD hek
                 rw [mul_div_assoc, mul_pow, mul_div_assoc]
                 refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg a)
                 rw [div_pow]
                 rcases le_total k D with h | h
                 · exact (div_le_div_of_nonneg_left (sq_nonneg W) (pow_pos hk0 2)
                     (pow_le_pow_left₀ hk0.le h 2)).trans
                     (div_le_div_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg e)) (sq_nonneg k))
                 · calc W^2 / D^2 ≤ 1 := div_le_one_of_le₀ hWD (sq_nonneg D)
                     _ ≤ (W^2 + e^2) / k^2 := by
                       rw [one_le_div (pow_pos hk0 2)]
                       exact (hek h).trans (le_add_of_nonneg_left (sq_nonneg W))
               refine h2g _ _ _ _ (sq_le_sq' (by linarith only [hm0]) (by linarith only [hmD])) fun h => ?_
               have := pow_le_pow_left₀ hk0.le (by linarith only [h] : k ≤ 2 * k - (C + T)) 2
               have e : (2 * k - (C + T))^2 = (C + T - 2 * k)^2 := by ring
               rw [← e]; exact this
             refine h2.trans (div_le_div_of_nonneg_right ?_ (sq_nonneg k))
             have key : ∀ x y z w : ℝ, w^2 ≤ (2*z-x-y)^2 + (x+y)^2 →
                 (y-x)^2*(w^2+(x+y)^2) ≤ 900*(x^4+y^4+z^4) := by
               intro x y z w hw
               have hQ1 : (y - x)^2 ≤ 2 * (x^2+y^2+z^2) := by
                 linear_combination sq_nonneg (x+y) + 2 * sq_nonneg z
               have hQ2 : w^2 + (x+y)^2 ≤ 10 * (x^2+y^2+z^2) := by
                 linear_combination hw + 3 * sq_nonneg (x-y) + sq_nonneg (2*x+z) + sq_nonneg (2*y+z) + 4 * sq_nonneg z
               have hP := mul_le_mul hQ1 hQ2 (add_nonneg (sq_nonneg _) (sq_nonneg _))
                 (mul_nonneg zero_le_two (add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)))
               have e : ∀ t : ℝ, t^4 = (t^2)^2 := fun t => by ring
               rw [e, e, e]
               generalize x^2 = p at hP ⊢
               generalize y^2 = q at hP ⊢
               generalize z^2 = r at hP ⊢
               refine hP.trans ?_
               linear_combination 20 * sq_nonneg (p-q) + 20 * sq_nonneg (q-r) + 20 * sq_nonneg (p-r) + 840 * sq_nonneg p + 840 * sq_nonneg q + 840 * sq_nonneg r
             have := key (C-k) (T-k) (S-k) (2 * m - (C + T))
             rw [show T - k - (C - k) = T - C by ring, show C - k + (T - k) = C + T - 2 * k by ring,
               show 2 * (S - k) - (C - k) - (T - k) = 2 * S - (C + T) by ring] at this
             exact this h3
           have hLow : ∀ (C T S k m L U : ℝ), 0 ≤ C → 0 ≤ T → 0 ≤ S → 1 ≤ k → m = min (C + T) (min S (3 * k)) →
               L = max (m - T) 0 → U = min m C →
               |C - k| ≤ k / 10 → |T - k| ≤ k / 10 → |S - k| ≤ k / 10 →
               k^2 / 16 ≤ (U - m * C / (C + T)) * (m * C / (C + T) - L) := by
             intro C T S k m L U hC hT hS hk hm hL hU h1 h2 h3
             obtain ⟨h1a, h1b⟩ := abs_le.1 h1
             obtain ⟨h2a, h2b⟩ := abs_le.1 h2
             obtain ⟨h3a, h3b⟩ := abs_le.1 h3
             have hk0 : 0 < k := lt_of_lt_of_le one_pos hk
             have hD : 0 < C + T := by linear_combination h1a + h2a + 9/5 * hk0
             have hmS : m = S := by
               rw [hm, min_eq_left (by linear_combination h3b + 19/10 * hk0.le : S ≤ 3*k),
                 min_eq_right (by linear_combination h1a + h2a + h3b + 7/10 * hk0.le : S ≤ C + T)]
             subst hmS
             have hkk := mul_self_nonneg k
             have hDk := mul_nonneg hk0.le (by linear_combination h1b + h2b : 0 ≤ 11/5*k - (C + T))
             have hm9 : 0 ≤ m - 9/10*k := by linear_combination h3a
             have hC9 : 0 ≤ C - 9/10*k := by linear_combination h1a
             have hT9 : 0 ≤ T - 9/10*k := by linear_combination h2a
             have hDm : 0 ≤ C + T - m - 7/10*k := by linear_combination h1a + h2a + h3b
             have hDm' : 0 ≤ C + T - m := by linear_combination hDm + 7/10 * hk0.le
             have hML : k / 4 ≤ m * C / (C + T) - L := by
               rw [hL]
               rcases le_total (m - T) 0 with h | h
               · rw [max_eq_right h, sub_zero, le_div_iff₀ hD]
                 linear_combination mul_nonneg hm9 hC + 9/10 * mul_nonneg hk0.le hC9 + 1/4 * hDk + 13/50 * hkk
               · rw [max_eq_left h, le_sub_iff_add_le, le_div_iff₀ hD]
                 linear_combination mul_nonneg hT9 hDm' + 9/10 * mul_nonneg hk0.le hDm + 1/4 * hDk + 2/25 * hkk
             have hUM : k / 4 ≤ U - m * C / (C + T) := by
               rw [hU]
               rcases le_total m C with h | h
               · rw [min_eq_left h, le_sub_comm, div_le_iff₀ hD]
                 linear_combination mul_nonneg hm9 hT + 9/10 * mul_nonneg hk0.le hT9 + 1/4 * hDk + 13/50 * hkk
               · rw [min_eq_right h, le_sub_comm, div_le_iff₀ hD]
                 linear_combination mul_nonneg hC9 hDm' + 9/10 * mul_nonneg hk0.le hDm + 1/4 * hDk + 2/25 * hkk
             have hk4 : 0 ≤ k / 4 := div_nonneg hk0.le zero_le_four
             calc k^2/16 = (k/4)*(k/4) := by ring
               _ ≤ _ := mul_le_mul hUM hML hk4 (hk4.trans hUM)
           have h1 : ∃! x, IsOptimal varianceNetwork 1 (fun _ => 2) (fun _ => 1) x := by
             have hsum : ∀ (p : Fin 1 → Prop) [DecidablePred p], (∀ e, p e) → ∀ y : Fin 1 → ℝ,
                 ∑ e with p e, y e = y 0 := by
               intro p _ hp y; rw [Finset.filter_true_of_mem (fun e _ => hp e), Fin.sum_univ_one]
             have hobj : ∀ y : Fin 1 → ℝ, obj varianceNetwork y = y 0 := by
               intro y; rw [obj, Fin.sum_univ_one]; exact one_mul _
             have hF1 : Feasible varianceNetwork 1 (fun _ => 2) (fun _ => 1) (fun _ => 1) :=
               ⟨fun e => (by norm_num : (0:ℝ) ≤ 1 ∧ (1:ℝ) ≤ 1 * 3),
                fun i => (hsum _ (fun e => congrArg Sum.inl (Subsingleton.elim _ _)) _).trans_le
                  (by norm_num : (1:ℝ) ≤ 2),
                fun j => (hsum _ (fun e => congrArg Sum.inl (Subsingleton.elim _ _)) _).trans_le le_rfl,
                fun u => u.elim⟩
             refine ⟨fun _ => 1, ⟨hF1, fun y hy => ?_⟩, fun y hy => ?_⟩
             · have h := (hsum (fun e => varianceNetwork.tail e = Sum.inl 0) (fun e => rfl) y).symm.trans_le
                 (hy.2.2.1 0)
               rw [hobj, hobj]; exact h
             · have h1 := (hsum (fun e => varianceNetwork.tail e = Sum.inl 0) (fun e => rfl) y).symm.trans_le
                 (hy.1.2.2.1 0)
               have h2 := hy.2 _ hF1
               rw [hobj, hobj] at h2
               funext e; rw [Subsingleton.elim e 0]; exact le_antisymm h1 h2
           have h2 : ∃! q, IsOptimalDual varianceNetwork 1 (fun _ => 2) (fun _ => 1) q := by
             let q0 : DualVar 1 1 Empty (Fin 1) := ⟨fun _ => 0, fun _ => 1, fun u => u.elim, fun _ => 0⟩
             have key : ∀ q : DualVar 1 1 Empty (Fin 1), DualFeasible varianceNetwork q →
                 1 ≤ q.a 0 + q.b 0 + q.ξ 0 ∧ 0 ≤ q.a 0 ∧ 0 ≤ q.b 0 ∧ 0 ≤ q.ξ 0 := by
               intro q hq
               have h : (1:ℝ) ≤ q.b 0 + q.a 0 + q.ξ 0 := hq.1 0
               exact ⟨by linarith only [h], hq.2.1 0, hq.2.2.1 0, hq.2.2.2 0⟩
             have hobj : ∀ q : DualVar 1 1 Empty (Fin 1), dualObj varianceNetwork 1 (fun _ => 2) (fun _ => 1) q
                 = 2 * q.a 0 + q.b 0 + 3 * q.ξ 0 := by
               intro q; simp only [dualObj, Fin.sum_univ_one]
               show q.a 0 * 2 + q.b 0 * 1 + q.ξ 0 * 3 * 1 = _
               ring
             have hf0 : DualFeasible varianceNetwork q0 :=
               ⟨fun e => (by norm_num : (1:ℝ) ≤ 1 + 0 + 0), fun i => le_rfl, fun j => zero_le_one, fun e => le_rfl⟩
             refine ⟨q0, ⟨hf0, fun q' hq' => ?_⟩, fun q hq => ?_⟩
             · have := key q' hq'; rw [hobj, hobj]
               show 2 * (0:ℝ) + 1 + 3 * 0 ≤ _
               linarith only [this.1, this.2.1, this.2.2.2]
             · have k := key q hq.1
               have k2 : 2 * q.a 0 + q.b 0 + 3 * q.ξ 0 ≤ 2 * 0 + 1 + 3 * 0 := by
                 have := hq.2 q0 hf0; rwa [hobj, hobj] at this
               obtain ⟨a, b, m, ξ⟩ := q
               simp only at k k2
               have ha : a = fun _ => 0 := by
                 funext i; rw [Subsingleton.elim i 0]; linarith only [k.1, k.2.1, k.2.2.2, k2]
               have hb : b = fun _ => 1 := by
                 funext i; rw [Subsingleton.elim i 0]; linarith only [k.1, k.2.1, k.2.2.2, k2]
               have hξ : ξ = fun _ => 0 := by
                 funext i; rw [Subsingleton.elim i 0]; linarith only [k.1, k.2.1, k.2.2.2, k2]
               have hm : m = fun u => u.elim := funext fun u => u.elim
               subst ha hb hξ hm; rfl
           have h3 : ∀ n, IsProbabilityMeasure (varianceLaw (n + 1)) ∧
               HasExperimentLaw (varianceLaw (n + 1)) Prod.fst (fun _ => 2) (fun _ => 0)
                 (fun _ => 1) (1/2) (n + 1 : ℕ) := by
             intro n
             haveI : IsProbabilityMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) :=
               ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]⟩
             refine ⟨by unfold varianceLaw MarketInterference.FiniteSample.experimentLaw MarketInterference.FiniteSample.poisLaw; infer_instance, measurable_fst, ?_⟩
             rw [varianceLaw, Measure.map_fst_prod, measure_univ, one_smul]
           have hPV : pathValue variancePath = 1 := by simp [pathValue, variancePath, varianceNetwork]
           have hRev : ∀ v, pathRevenue varianceNetwork (Finsupp.single variancePath v) = v := by
             intro v
             by_cases hv : v = 0
             · subst hv; simp [pathRevenue]
             · simp [pathRevenue, Finsupp.support_single_ne_zero _ hv, hPV]
           have hmeanb : ∀ k z, (lowerControl k z : ℝ) ≤ meanControl k z ∧
               meanControl k z ≤ upperControl k z ∧ 0 ≤ meanControl k z := by
             intro k z
             unfold meanControl lowerControl upperControl
             have hmD : matchedCount k z ≤ z.1.1 0 + z.1.2 0 := min_le_left _ _
             generalize matchedCount k z = m at hmD ⊢
             generalize z.1.1 0 = C at hmD ⊢
             generalize z.1.2 0 = T at hmD ⊢
             have hmR : (m:ℝ) ≤ C + T := by exact_mod_cast hmD
             have hC : (0:ℝ) ≤ C := Nat.cast_nonneg _
             have hT : (0:ℝ) ≤ T := Nat.cast_nonneg _
             have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg _
             have hnn : 0 ≤ (m:ℝ) * C / (C + T) := div_nonneg (mul_nonneg hm0 hC) (add_nonneg hC hT)
             rcases eq_or_lt_of_le (add_nonneg hC hT) with h0 | hD
             · have hm' : (m:ℝ) = 0 := le_antisymm (hmR.trans_eq h0.symm) hm0
               have hm'' : m = 0 := by exact_mod_cast hm'
               rw [← h0, div_zero, hm'', Nat.zero_sub, Nat.cast_zero]
               exact ⟨le_rfl, Nat.cast_nonneg _, le_rfl⟩
             refine ⟨?_, ?_, hnn⟩
             · rcases le_total m T with h | h
               · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]; exact hnn
               · rw [Nat.cast_sub h, le_div_iff₀ hD]
                 linarith only [mul_nonneg hT (sub_nonneg.2 hmR)]
             · rw [div_le_iff₀ hD, Nat.cast_min]
               rcases le_total (m:ℝ) C with h | h
               · rw [min_eq_left h]; exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hT) hm0
               · rw [min_eq_right h]; exact (mul_le_mul_of_nonneg_right hmR hC).trans_eq (mul_comm _ _)
           have hab : ∀ k z u, 0 ≤ u → lowerControl k z ≤ alternatingControl k (z,u) ∧
               alternatingControl k (z,u) ≤ upperControl k z := by
             intro k z u hu
             obtain ⟨hl, hu', h0⟩ := hmeanb k z
             have hlu : lowerControl k z ≤ upperControl k z := Nat.cast_le.1 (hl.trans hu')
             unfold alternatingControl
             split_ifs
             · unfold roundedControl
               split_ifs with hc
               · constructor
                 · exact (Nat.le_floor hl).trans (Nat.le_succ _)
                 · by_contra hcon
                   have h1 : (upperControl k z : ℝ) ≤ Nat.floor (meanControl k z) :=
                     Nat.cast_le.2 (Nat.lt_succ_iff.mp (lt_of_not_ge hcon))
                   have h2 := Nat.floor_le h0
                   linarith only [h1, h2, hu', hc, hu]
               · exact ⟨Nat.le_floor hl, Nat.floor_le_of_le hu'⟩
             · unfold extremeControl
               split_ifs
               · exact ⟨hlu, le_rfl⟩
               · exact ⟨le_rfl, hlu⟩
           have hDem : ∀ v i, pathDemand varianceNetwork (Finsupp.single variancePath v) i = v := by
             intro v i
             fin_cases i
             by_cases hv : v = 0
             · subst hv; simp [pathDemand]
             · rw [pathDemand, Finsupp.support_single_ne_zero _ hv, Finset.filter_singleton]
               simp [variancePath]
           have hite : ∀ c : ℝ, 0 ≤ c → c ≤ 1 → ∀ A B : ℝ,
               ∫ u in Set.Icc (0:ℝ) 1, (if u < c then A else B) = A * c + B * (1 - c) := by
             intro c hc0 hc1 A B
             have hfun : (fun u : ℝ => if u < c then A else B) = fun u => (Set.Iio c).indicator (fun _ => A - B) u + B := by
               funext u; by_cases h : u < c <;> simp [Set.indicator, h]
             rw [hfun, integral_add, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
             · rw [setIntegral_const, setIntegral_const]
               have : Set.Iio c ∩ Set.Icc 0 1 = Set.Ico 0 c := by
                 ext u; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc, Set.mem_Ico]; constructor
                 · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1⟩
                 · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
               rw [this, Real.volume_real_Ico_of_le hc0, Real.volume_real_Icc_of_le zero_le_one, smul_eq_mul, smul_eq_mul]; ring
             · refine (integrable_const _).indicator measurableSet_Iio
             · exact integrable_const _
           have hint : ∀ k z, ∫ u in Set.Icc (0:ℝ) 1, (alternatingControl k (z,u) : ℝ) = meanControl k z := by
             intro k z
             obtain ⟨hl, hu, h0⟩ := hmeanb k z
             unfold alternatingControl
             split_ifs
             · unfold roundedControl
               simp only [Nat.cast_ite]
               have hf1 := Nat.floor_le h0
               have hf2 := Nat.lt_floor_add_one (meanControl k z)
               rw [hite _ (sub_nonneg.2 hf1) (by linarith only [hf2]), Nat.cast_succ]
               ring
             · unfold extremeControl
               simp only [Nat.cast_ite]
               rcases eq_or_lt_of_le (hl.trans hu) with heq | hlt
               · have : meanControl k z = lowerControl k z := le_antisymm (hu.trans_eq heq.symm) hl
                 rw [← heq, sub_self, div_zero, hite 0 le_rfl zero_le_one, this, heq]
                 ring
               · have hpos : (0:ℝ) < upperControl k z - lowerControl k z := sub_pos.2 hlt
                 rw [hite _ (div_nonneg (sub_nonneg.2 hl) hpos.le) ((div_le_one hpos).mpr (sub_le_sub_right hu _))]
                 have e := mul_div_cancel₀ (meanControl k z - lowerControl k z) hpos.ne'
                 linear_combination e
           have hIcc : ∀ k, ∀ᵐ ω ∂varianceLaw k, ω.2 ∈ Set.Icc (0:ℝ) 1 := by
             intro k
             exact Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)
           have hmeasA : ∀ k, Measurable (fun ω : Counts 1 1 × ℝ => (alternatingControl k ω : ℝ)) := by
             intro k
             refine measurable_from_prod_countable_right (fun z => ?_)
             unfold alternatingControl roundedControl extremeControl
             dsimp only
             split_ifs <;> simp only [Nat.cast_ite] <;>
               exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const
           have hmeasM : ∀ k, Measurable (fun ω : Counts 1 1 × ℝ => (matchedCount k ω.1 : ℝ)) :=
             fun k => (measurable_of_countable (fun z : Counts 1 1 => (matchedCount k z : ℝ))).comp measurable_fst
           have hsingle : ∀ f : Counts 1 1 × ℝ → ℝ, Measurable f → ∀ p,
               Measurable (fun ω => Finsupp.single variancePath (f ω) p) := by
             intro f hf p
             by_cases h : variancePath = p
             · subst h; simpa using hf
             · simp [Finsupp.single_apply, h]
           have hfeas : ∀ (τ : ℝ) d s x, Feasible varianceNetwork τ d s x ↔
               (0 ≤ x 0 ∧ x 0 ≤ τ * 3) ∧ x 0 ≤ d 0 ∧ x 0 ≤ s 0 := by
             intro τ d s x
             have hs : ∀ (p : Fin 1 → Prop) [DecidablePred p], (∀ e, p e) → ∑ e with p e, x e = x 0 := by
               intro p _ hp; rw [Finset.filter_true_of_mem (fun e _ => hp e), Fin.sum_univ_one]
             unfold Feasible
             rw [Fin.forall_fin_one, Fin.forall_fin_one, Fin.forall_fin_one,
               hs (fun e => varianceNetwork.head e = Sum.inl 0) (fun e => rfl),
               hs (fun e => varianceNetwork.tail e = Sum.inl 0) (fun e => rfl)]
             exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1⟩, fun h => ⟨h.1, h.2.1, h.2.2, fun u => u.elim⟩⟩
           -- bounds a.e.
           have hbnd : ∀ k, ∀ᵐ ω ∂varianceLaw k, (alternatingControl k ω : ℝ) ≤ matchedCount k ω.1 ∧
               (alternatingControl k ω : ℝ) ≤ ω.1.1.1 0 ∧
               (matchedCount k ω.1 : ℝ) - alternatingControl k ω ≤ ω.1.1.2 0 := by
             intro k
             filter_upwards [hIcc k] with ω hω
             obtain ⟨h1, h2⟩ := hab k ω.1 ω.2 hω.1
             have h3 : upperControl k ω.1 ≤ matchedCount k ω.1 := min_le_left _ _
             have h4 : upperControl k ω.1 ≤ ω.1.1.1 0 := min_le_right _ _
             have h5 : matchedCount k ω.1 ≤ lowerControl k ω.1 + ω.1.1.2 0 := by
               unfold lowerControl; omega
             refine ⟨Nat.cast_le.2 (h2.trans h3), Nat.cast_le.2 (h2.trans h4), ?_⟩
             have : (matchedCount k ω.1 : ℝ) ≤ alternatingControl k ω + ω.1.1.2 0 := by
               rw [← Nat.cast_add]; exact Nat.cast_le.2 (h5.trans (Nat.add_le_add_right h1 _))
             linarith only [this]
           have hmle : ∀ k z, (matchedCount k z : ℝ) ≤ 3 * k := by
             intro k z
             have : matchedCount k z ≤ 3 * k := (min_le_right _ _).trans (min_le_right _ _)
             exact_mod_cast this
           have hA : ∀ n, ∃ A : BlindAllocation varianceNetwork (varianceLaw (n + 1)) Prod.fst (n + 1 : ℕ),
               (∀ ω, A.total ω = Finsupp.single variancePath (matchedCount (n + 1) ω.1 : ℝ)) ∧
               (∀ ω, A.control ω = Finsupp.single variancePath (alternatingControl (n + 1) ω : ℝ) ∧
                 A.treatment ω = Finsupp.single variancePath
                   ((matchedCount (n + 1) ω.1 : ℝ) - (alternatingControl (n + 1) ω : ℝ))) := by
             intro n
             haveI hP : IsProbabilityMeasure (varianceLaw (n+1)) := (h3 n).1
             refine ⟨
               { total := fun ω => Finsupp.single variancePath (matchedCount (n + 1) ω.1 : ℝ)
                 control := fun ω => Finsupp.single variancePath (alternatingControl (n + 1) ω : ℝ)
                 treatment := fun ω => Finsupp.single variancePath
                     ((matchedCount (n + 1) ω.1 : ℝ) - (alternatingControl (n + 1) ω : ℝ))
                 total_measurable := hsingle _ (hmeasM _)
                 control_measurable := hsingle _ (hmeasA _)
                 treatment_measurable := hsingle _ ((hmeasM _).sub (hmeasA _))
                 optimal := by
                   refine Eventually.of_forall (fun ω => ⟨fun _ => (matchedCount (n + 1) ω.1 : ℝ), ⟨?_, ?_⟩, ?_⟩)
                   · rw [hfeas]
                     have := hmle (n+1) ω.1
                     exact ⟨⟨Nat.cast_nonneg _, this.trans_eq (mul_comm _ _)⟩, Nat.cast_le.2 (min_le_left _ _),
                       Nat.cast_le.2 ((min_le_right _ _).trans (min_le_left _ _))⟩
                   · intro y hy
                     rw [hfeas] at hy
                     simp only [obj, varianceNetwork, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, one_mul]
                     unfold matchedCount
                     push_cast
                     push_cast at hy
                     refine le_min hy.2.1 (le_min hy.2.2 ?_)
                     linarith [hy.1.2]
                   · refine ⟨fun p => ?_, fun e => ?_⟩
                     · by_cases h : variancePath = p
                       · subst h; rw [Finsupp.single_eq_same]; exact Nat.cast_nonneg _
                       · rw [Finsupp.single_eq_of_ne' h]
                     · fin_cases e
                       by_cases hv : (matchedCount (n + 1) ω.1 : ℝ) = 0
                       · rw [hv]; simp
                       · rw [Finsupp.support_single_ne_zero _ hv]; simp [variancePath]
                 split := Eventually.of_forall (fun ω => by rw [← Finsupp.single_add]; congr 1; ring)
                 nonneg := by
                   filter_upwards [hbnd (n+1)] with ω hω
                   refine ⟨fun p => ?_, fun p => ?_⟩
                   · by_cases h : variancePath = p
                     · subst h; rw [Finsupp.single_eq_same]; exact Nat.cast_nonneg _
                     · rw [Finsupp.single_eq_of_ne' h]
                   · by_cases h : variancePath = p
                     · subst h; rw [Finsupp.single_eq_same]; exact sub_nonneg.2 hω.1
                     · rw [Finsupp.single_eq_of_ne' h]
                 control_count := by
                   filter_upwards [hbnd (n+1)] with ω hω
                   intro i; fin_cases i; rw [hDem]; exact hω.2.1
                 treatment_count := by
                   filter_upwards [hbnd (n+1)] with ω hω
                   intro i; fin_cases i; rw [hDem]; exact hω.2.2
                 blind := by
                   intro p
                   by_cases h : variancePath = p
                   · subst h
                     simp only [Finsupp.single_eq_same]
                     have hm : MeasurableSpace.comap (Prod.fst : Counts 1 1 × ℝ → Counts 1 1)
                         (inferInstance : MeasurableSpace (Counts 1 1)) ≤ (inferInstance : MeasurableSpace (Counts 1 1 × ℝ)) :=
                       measurable_fst.comap_le
                     have hfi : Integrable (fun ω : Counts 1 1 × ℝ => (alternatingControl (n + 1) ω : ℝ)) (varianceLaw (n+1)) := by
                       refine Integrable.of_bound (hmeasA _).aestronglyMeasurable (3 * (n+1:ℕ)) ?_
                       filter_upwards [hbnd (n+1)] with ω hω
                       rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
                       exact hω.1.trans (hmle _ _)
                     let g : Counts 1 1 → ℝ := fun z => (z.1.1 0 : ℝ) / ((z.1.1 0 : ℝ) + (z.1.2 0 : ℝ)) * matchedCount (n+1) z
                     have hgb : ∀ z, ‖g z‖ ≤ 3 * (n+1:ℕ) := by
                       intro z
                       have hC : (0:ℝ) ≤ z.1.1 0 := Nat.cast_nonneg _
                       have hT : (0:ℝ) ≤ z.1.2 0 := Nat.cast_nonneg _
                       have h1 : (z.1.1 0 : ℝ) / ((z.1.1 0 : ℝ) + (z.1.2 0 : ℝ)) ≤ 1 :=
                         div_le_one_of_le₀ (le_add_of_nonneg_right hT) (add_nonneg hC hT)
                       have hM : (0:ℝ) ≤ matchedCount (n+1) z := Nat.cast_nonneg _
                       rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ g z from mul_nonneg (div_nonneg hC (add_nonneg hC hT)) hM)]
                       exact (mul_le_of_le_one_left hM h1).trans (hmle _ _)
                     have hgi : Integrable (fun ω : Counts 1 1 × ℝ => g ω.1) (varianceLaw (n+1)) :=
                       Integrable.of_bound ((measurable_of_countable g).comp measurable_fst).aestronglyMeasurable
                         _ (Eventually.of_forall fun ω => hgb ω.1)
                     refine (ae_eq_condExp_of_forall_setIntegral_eq hm hfi (fun s _ _ => hgi.integrableOn) ?_ ?_).symm
                     · rintro s ⟨B, hB, rfl⟩ _
                       rw [← Set.prod_univ]
                       have hres : (varianceLaw (n+1)).restrict (B ×ˢ Set.univ) =
                           ((MarketInterference.FiniteSample.experimentLaw (fun _ => 2) (fun _ => 0)
                             (fun _ => 1) (1/2) ((n+1 : ℕ) : ℝ)).restrict B).prod (volume.restrict (Set.Icc (0:ℝ) 1)) := by
                         rw [varianceLaw, ← Measure.prod_restrict, Measure.restrict_univ]
                       have hfi' := hfi.restrict (s := B ×ˢ Set.univ)
                       have hgi' := hgi.restrict (s := B ×ˢ Set.univ)
                       rw [hres] at hfi' hgi' ⊢
                       rw [integral_prod _ hfi', integral_prod _ hgi']
                       congr 1
                       funext z
                       haveI : IsProbabilityMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) :=
                         ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]⟩
                       rw [hint]
                       simp only [g, meanControl, integral_const, probReal_univ, smul_eq_mul, one_mul]
                       ring
                     · exact ((measurable_of_countable g).comp (comap_measurable Prod.fst)).aestronglyMeasurable
                   · have h0 : (fun ω : Counts 1 1 × ℝ => (Finsupp.single variancePath (alternatingControl (n + 1) ω : ℝ)) p) = fun _ => 0 := by
                       funext ω; exact Finsupp.single_eq_of_ne' h
                     rw [h0, ← Pi.zero_def, condExp_zero]
                     refine Eventually.of_forall (fun ω => ?_)
                     simp [Finsupp.single_apply, h] }
           , fun ω => rfl, fun ω => ⟨rfl, rfl⟩⟩
           choose A hAt hAc using hA
           have hest : ∀ n ω, Real.sqrt (n + 1 : ℕ) *
               rctEst varianceNetwork (varianceLaw (n + 1)) Prod.fst (1/2) (n + 1 : ℕ) (A n) ω =
               Real.sqrt (n + 1 : ℕ) * ((1 / ((n + 1 : ℕ) : ℝ)) *
                 (2 * (matchedCount (n + 1) ω.1 : ℝ) - 4 * (alternatingControl (n + 1) ω : ℝ))) := by
             intro n ω
             simp only [rctEst, (hAc n ω).1, (hAc n ω).2, hRev]
             ring
           have hfm : ∀ (r : NNReal) (k : ℕ), HasSum (fun n : ℕ => exp (-r) * (r:ℝ) ^ n / (n.factorial) *
               (∏ i ∈ Finset.range k, ((n:ℝ) - i))) ((r:ℝ) ^ k) := by
             intro r k
             rw [← hasSum_nat_add_iff' k]
             have hz : ∑ i ∈ Finset.range k, exp (-r) * (r:ℝ) ^ i / (i.factorial) *
                 (∏ j ∈ Finset.range k, ((i:ℝ) - j)) = 0 := by
               refine Finset.sum_eq_zero (fun i hi => ?_)
               rw [Finset.prod_eq_zero hi (sub_self _), mul_zero]
             rw [hz, sub_zero]
             have h1 := (ProbabilityTheory.hasSum_one_poissonMeasure r).mul_left ((r:ℝ)^k)
             rw [mul_one] at h1
             have hp : ∀ n k : ℕ, (∏ i ∈ Finset.range k, (((n + k : ℕ):ℝ) - i)) * (n.factorial : ℝ) = ((n + k).factorial : ℝ) := by
               intro n k
               induction k with
               | zero => rw [Finset.prod_range_zero, one_mul]; rfl
               | succ k ih =>
                 rw [Finset.prod_range_succ']
                 have : ∏ x ∈ Finset.range k, (((n + (k+1) : ℕ):ℝ) - ((x + 1 : ℕ) : ℝ)) = ∏ x ∈ Finset.range k, (((n + k : ℕ):ℝ) - x) := by
                   refine Finset.prod_congr rfl (fun x _ => ?_); push_cast; ring
                 rw [this, show n + (k+1) = (n + k) + 1 by ring, Nat.factorial_succ]
                 push_cast
                 rw [← ih]; push_cast; ring
             have : (fun n : ℕ => exp (-r) * (r:ℝ) ^ (n + k) / ((n + k).factorial) *
               (∏ i ∈ Finset.range k, (((n + k : ℕ):ℝ) - i))) = fun i => (r:ℝ) ^ k * (exp (-r) * (r:ℝ) ^ i / (i.factorial)) := by
               funext n
               rw [← hp n k]
               have : (n.factorial : ℝ) ≠ 0 := by positivity
               by_cases h0 : (∏ i ∈ Finset.range k, (((n + k : ℕ):ℝ) - i)) = 0
               · exfalso
                 have := hp n k; rw [h0, zero_mul] at this; exact (Nat.factorial_ne_zero _) (by exact_mod_cast this.symm)
               · rw [div_mul_eq_mul_div, mul_comm (∏ i ∈ Finset.range k, (((n + k : ℕ):ℝ) - i)) (n.factorial : ℝ),
                   mul_div_mul_right _ _ h0, pow_add]; ring
             rw [← this] at h1
             simpa only [Nat.cast_add] using h1
           have hw : ∀ (r : NNReal) (n : ℕ), 0 ≤ exp (-r) * (r:ℝ) ^ n / (n.factorial) := fun r n => by positivity
           have hs4 : ∀ r : NNReal, HasSum (fun n : ℕ => exp (-r) * (r:ℝ) ^ n / (n.factorial) * ((n:ℝ) - r)^4)
               (3 * (r:ℝ)^2 + r) := by
             intro r
             have h := ((((hfm r 4).add ((hfm r 3).mul_left (6 - 4 * (r:ℝ)))).add
               ((hfm r 2).mul_left (7 - 12 * (r:ℝ) + 6 * (r:ℝ)^2))).add
               ((hfm r 1).mul_left (1 - 4 * (r:ℝ) + 6 * (r:ℝ)^2 - 4 * (r:ℝ)^3))).add
               ((hfm r 0).mul_left ((r:ℝ)^4))
             convert h using 1
             · funext n; simp only [Finset.prod_range_succ, Finset.prod_range_zero]; ring
             · ring
           have hs2 : ∀ r : NNReal, HasSum (fun n : ℕ => exp (-r) * (r:ℝ) ^ n / (n.factorial) * ((n:ℝ) - r)^2)
               (r:ℝ) := by
             intro r
             have h := (((hfm r 2).add ((hfm r 1).mul_left (1 - 2 * (r:ℝ)))).add
               ((hfm r 0).mul_left ((r:ℝ)^2)))
             convert h using 1
             · funext n; simp only [Finset.prod_range_succ, Finset.prod_range_zero]; ring
             · ring
           have hs1 : ∀ r : NNReal, HasSum (fun n : ℕ => exp (-r) * (r:ℝ) ^ n / (n.factorial) * ((n:ℝ) - r))
               0 := by
             intro r
             have h := ((hfm r 1).add ((hfm r 0).mul_left (- (r:ℝ))))
             convert h using 1
             · funext n; simp only [Finset.prod_range_succ, Finset.prod_range_zero]; ring
             · ring
           have hI : ∀ (r : NNReal) (f : ℕ → ℝ) (v : ℝ), (∀ n, 0 ≤ f n) →
               HasSum (fun n : ℕ => exp (-r) * (r:ℝ) ^ n / (n.factorial) * f n) v →
               Integrable f (poissonMeasure r) ∧ ∫ x, f x ∂(poissonMeasure r) = v := by
             intro r f v hf h
             refine ⟨integrable_poissonMeasure_iff.mpr ?_, ?_⟩
             · convert h.summable using 2 with n; rw [Real.norm_eq_abs, abs_of_nonneg (hf n)]
             · rw [integral_poissonMeasure]; simpa [smul_eq_mul] using h.tsum_eq
           haveI : IsProbabilityMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) :=
               ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]⟩
           have hpi : ∀ (r : NNReal), (Measure.pi (fun _ : Fin 1 => poissonMeasure r)).map (fun x => x 0) = poissonMeasure r := by
             intro r
             rw [show (fun x : Fin 1 → ℕ => x 0) = Function.eval 0 from rfl, Measure.pi_map_eval]
             simp
           have hlaw : ∀ k : ℕ,
               (varianceLaw k).map (fun ω => ω.1.1.1 0) = poissonMeasure (Real.toNNReal ((1 - 1/2) * 2 * k)) ∧
               (varianceLaw k).map (fun ω => ω.1.1.2 0) = poissonMeasure (Real.toNNReal (1/2 * (2 + 0) * k)) ∧
               (varianceLaw k).map (fun ω => ω.1.2 0) = poissonMeasure (Real.toNNReal (1 * k)) := by
             intro k
             unfold varianceLaw MarketInterference.FiniteSample.experimentLaw MarketInterference.FiniteSample.poisLaw
             have hm0 : Measurable (fun x : Fin 1 → ℕ => x 0) := measurable_pi_apply 0
             refine ⟨?_, ?_, ?_⟩
             · rw [show (fun ω : Counts 1 1 × ℝ => ω.1.1.1 0) = (fun x : Fin 1 → ℕ => x 0) ∘ Prod.fst ∘ Prod.fst ∘ Prod.fst from rfl,
                 ← Measure.map_map hm0 (measurable_fst.comp (measurable_fst.comp measurable_fst)),
                 ← Measure.map_map measurable_fst (measurable_fst.comp measurable_fst),
                 ← Measure.map_map measurable_fst measurable_fst]
               simp only [Measure.map_fst_prod, measure_univ, one_smul]
               exact hpi _
             · rw [show (fun ω : Counts 1 1 × ℝ => ω.1.1.2 0) = (fun x : Fin 1 → ℕ => x 0) ∘ Prod.snd ∘ Prod.fst ∘ Prod.fst from rfl,
                 ← Measure.map_map hm0 (measurable_snd.comp (measurable_fst.comp measurable_fst)),
                 ← Measure.map_map measurable_snd (measurable_fst.comp measurable_fst),
                 ← Measure.map_map measurable_fst measurable_fst]
               simp only [Measure.map_fst_prod, Measure.map_snd_prod, measure_univ, one_smul]
               exact hpi _
             · rw [show (fun ω : Counts 1 1 × ℝ => ω.1.2 0) = (fun x : Fin 1 → ℕ => x 0) ∘ Prod.snd ∘ Prod.fst from rfl,
                 ← Measure.map_map hm0 (measurable_snd.comp measurable_fst),
                 ← Measure.map_map measurable_snd measurable_fst]
               simp only [Measure.map_fst_prod, Measure.map_snd_prod, measure_univ, one_smul]
               exact hpi _
           have hprob : ∀ k, IsProbabilityMeasure (varianceLaw k) := by
             intro k; unfold varianceLaw MarketInterference.FiniteSample.experimentLaw MarketInterference.FiniteSample.poisLaw; infer_instance
           have hcoord : ∀ (k : ℕ) (pr : Counts 1 1 × ℝ → ℕ), Measurable pr →
               (varianceLaw k).map pr = poissonMeasure (Real.toNNReal (k:ℝ)) →
               (Integrable (fun ω => ((pr ω : ℝ) - k)^4) (varianceLaw k) ∧ ∫ ω, ((pr ω : ℝ) - k)^4 ∂(varianceLaw k) = 3 * (k:ℝ)^2 + k) ∧
               (Integrable (fun ω => ((pr ω : ℝ) - k)^2) (varianceLaw k) ∧ ∫ ω, ((pr ω : ℝ) - k)^2 ∂(varianceLaw k) = k) ∧
               (Integrable (fun ω => ((pr ω : ℝ))) (varianceLaw k) ∧ ∫ ω, ((pr ω : ℝ)) ∂(varianceLaw k) = k) := by
             intro k pr hpr hmap
             have hr : ((Real.toNNReal (k:ℝ) : NNReal) : ℝ) = k := Real.coe_toNNReal _ (by positivity)
             have key : ∀ (f : ℕ → ℝ) (v : ℝ), (∀ n, 0 ≤ f n) →
                 HasSum (fun n : ℕ => exp (-(Real.toNNReal (k:ℝ) : ℝ)) * ((Real.toNNReal (k:ℝ) : NNReal):ℝ) ^ n / (n.factorial) * f n) v →
                 Integrable (fun ω => f (pr ω)) (varianceLaw k) ∧ ∫ ω, f (pr ω) ∂(varianceLaw k) = v := by
               intro f v hf h
               obtain ⟨hi, he⟩ := hI _ f v hf h
               rw [← hmap] at hi he
               refine ⟨(integrable_map_measure (measurable_of_countable f).aestronglyMeasurable hpr.aemeasurable).mp hi, ?_⟩
               rw [← he, integral_map hpr.aemeasurable (measurable_of_countable f).aestronglyMeasurable]
             have h4 := hs4 (Real.toNNReal (k:ℝ)); rw [hr] at h4
             have h2 := hs2 (Real.toNNReal (k:ℝ)); rw [hr] at h2
             have h1 := hfm (Real.toNNReal (k:ℝ)) 1; rw [hr] at h1
             simp only [Finset.prod_range_one, CharP.cast_eq_zero, sub_zero, pow_one] at h1
             simp only [hr] at key
             exact ⟨key (fun n => ((n:ℝ) - k)^4) _ (fun n => by positivity) h4,
               key (fun n => ((n:ℝ) - k)^2) _ (fun n => sq_nonneg _) h2,
               key (fun n => (n:ℝ)) _ (fun n => Nat.cast_nonneg n) h1⟩
           have hindep : ∀ k : ℕ, IndepFun (fun ω : Counts 1 1 × ℝ => ω.1.1.1 0) (fun ω => ω.1.1.2 0) (varianceLaw k) := by
             intro k
             haveI := hprob k
             have hm0 : Measurable (fun x : Fin 1 → ℕ => x 0) := measurable_pi_apply 0
             rw [indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop), (hlaw k).1, (hlaw k).2.1]
             unfold varianceLaw MarketInterference.FiniteSample.experimentLaw MarketInterference.FiniteSample.poisLaw
             rw [show (fun ω : Counts 1 1 × ℝ => (ω.1.1.1 0, ω.1.1.2 0)) = (Prod.map (fun x : Fin 1 → ℕ => x 0) (fun x : Fin 1 → ℕ => x 0)) ∘ Prod.fst ∘ Prod.fst from rfl,
                 ← Measure.map_map (hm0.prodMap hm0) (measurable_fst.comp measurable_fst),
                 ← Measure.map_map measurable_fst measurable_fst]
             simp only [Measure.map_fst_prod, measure_univ, one_smul]
             rw [← Measure.map_prod_map _ _ hm0 hm0, hpi, hpi]
           refine ⟨h1, h2, h3, A, fun n => Eventually.of_forall (hAt n),
             fun n => Eventually.of_forall (hAc n), ?_, ?_⟩
           · intro n
             haveI hP : IsProbabilityMeasure (varianceLaw (n+1)) := (h3 n).1
             simp only [hest]
             refine MemLp.of_bound ((((((hmeasM _).const_mul 2).sub ((hmeasA _).const_mul 4)).const_mul _).const_mul _).aestronglyMeasurable)
               (Real.sqrt (n + 1 : ℕ) * ((1 / ((n + 1 : ℕ) : ℝ)) * (2 * (3 * (n+1:ℕ)) + 4 * (3 * (n+1:ℕ))))) ?_
             filter_upwards [hbnd (n+1)] with ω hω
             have h1 := hmle (n+1) ω.1
             have h0 : (0:ℝ) ≤ alternatingControl (n+1) ω := Nat.cast_nonneg _
             have h0' : (0:ℝ) ≤ matchedCount (n+1) ω.1 := Nat.cast_nonneg _
             have hK : (0:ℝ) ≤ 1 / ((n + 1 : ℕ) : ℝ) := one_div_nonneg.2 (Nat.cast_nonneg _)
             rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_mul, abs_of_nonneg hK]
             refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hK) (Real.sqrt_nonneg _)
             rw [abs_le]; constructor <;> linarith only [h1, h0, h0', hω.1]
           · intro V
             have hVe : ∀ n, V n = variance (fun ω => Real.sqrt ((n+1:ℕ):ℝ) * ((1 / ((n + 1 : ℕ) : ℝ)) *
                 (2 * (matchedCount (n + 1) ω.1 : ℝ) - 4 * (alternatingControl (n + 1) ω : ℝ)))) (varianceLaw (n+1)) := by
               intro n
               show variance _ _ = _
               exact congrArg (fun g => variance g (varianceLaw (n+1))) (funext (hest n))
             have hvar : ∀ (μ : Measure (Counts 1 1 × ℝ)) [IsProbabilityMeasure μ] (Y Z : Counts 1 1 × ℝ → ℝ),
                 MemLp Y 2 μ → MemLp Z 2 μ → ∀ δ : ℝ, 0 < δ →
                 variance (Y + Z) μ ≤ (1 + δ) * variance Y μ + (1 + 1/δ) * variance Z μ := by
               intro μ _ Y Z hY hZ δ hδ
               rw [variance_add hY hZ, variance_eq_integral hY.aemeasurable, variance_eq_integral hZ.aemeasurable]
               have ha := (hY.sub (memLp_const (μ[Y])))
               have hb := (hZ.sub (memLp_const (μ[Z])))
               have hab : Integrable (fun ω => (Y ω - μ[Y]) * (Z ω - μ[Z])) μ := ha.integrable_mul hb
               have ha2 : Integrable (fun ω => (Y ω - μ[Y])^2) μ := (memLp_two_iff_integrable_sq ha.aestronglyMeasurable).mp ha
               have hb2 : Integrable (fun ω => (Z ω - μ[Z])^2) μ := (memLp_two_iff_integrable_sq hb.aestronglyMeasurable).mp hb
               have hc : 2 * covariance Y Z μ ≤ δ * ∫ ω, (Y ω - μ[Y])^2 ∂μ + (1/δ) * ∫ ω, (Z ω - μ[Z])^2 ∂μ := by
                 calc 2 * covariance Y Z μ = ∫ ω, 2 * ((Y ω - μ[Y]) * (Z ω - μ[Z])) ∂μ := by
                       rw [covariance, integral_const_mul]
                   _ ≤ ∫ ω, (δ * (Y ω - μ[Y])^2 + 1/δ * (Z ω - μ[Z])^2) ∂μ := by
                       refine integral_mono (hab.const_mul _) ((ha2.const_mul _).add (hb2.const_mul _)) (fun ω => ?_)
                       have h1 := mul_nonneg (one_div_nonneg.mpr hδ.le) (sq_nonneg (δ * (Y ω - μ[Y]) - (Z ω - μ[Z])))
                       have hδ' : δ * (1 / δ) = 1 := mul_one_div_cancel hδ.ne'
                       linear_combination h1 + (δ * (Y ω - μ[Y])^2 - 2 * (Y ω - μ[Y]) * (Z ω - μ[Z])) * hδ'
                   _ = _ := by rw [integral_add (ha2.const_mul _) (hb2.const_mul _), integral_const_mul, integral_const_mul]
               linear_combination hc
             have hCo : ∀ k : ℕ,
                 ((Integrable (fun ω : Counts 1 1 × ℝ => ((ω.1.1.1 0 : ℝ) - k)^4) (varianceLaw k) ∧ ∫ ω, ((ω.1.1.1 0 : ℝ) - k)^4 ∂(varianceLaw k) = 3 * (k:ℝ)^2 + k) ∧
                 (Integrable (fun ω : Counts 1 1 × ℝ => ((ω.1.1.1 0 : ℝ) - k)^2) (varianceLaw k) ∧ ∫ ω, ((ω.1.1.1 0 : ℝ) - k)^2 ∂(varianceLaw k) = k) ∧
                 (Integrable (fun ω : Counts 1 1 × ℝ => ((ω.1.1.1 0 : ℝ))) (varianceLaw k) ∧ ∫ ω, ((ω.1.1.1 0 : ℝ)) ∂(varianceLaw k) = k)) ∧
                 ((Integrable (fun ω : Counts 1 1 × ℝ => ((ω.1.1.2 0 : ℝ) - k)^4) (varianceLaw k) ∧ ∫ ω, ((ω.1.1.2 0 : ℝ) - k)^4 ∂(varianceLaw k) = 3 * (k:ℝ)^2 + k) ∧
                 (Integrable (fun ω : Counts 1 1 × ℝ => ((ω.1.1.2 0 : ℝ) - k)^2) (varianceLaw k) ∧ ∫ ω, ((ω.1.1.2 0 : ℝ) - k)^2 ∂(varianceLaw k) = k) ∧
                 (Integrable (fun ω : Counts 1 1 × ℝ => ((ω.1.1.2 0 : ℝ))) (varianceLaw k) ∧ ∫ ω, ((ω.1.1.2 0 : ℝ)) ∂(varianceLaw k) = k)) ∧
                 ((Integrable (fun ω : Counts 1 1 × ℝ => ((ω.1.2 0 : ℝ) - k)^4) (varianceLaw k) ∧ ∫ ω, ((ω.1.2 0 : ℝ) - k)^4 ∂(varianceLaw k) = 3 * (k:ℝ)^2 + k) ∧
                 (Integrable (fun ω : Counts 1 1 × ℝ => ((ω.1.2 0 : ℝ) - k)^2) (varianceLaw k) ∧ ∫ ω, ((ω.1.2 0 : ℝ) - k)^2 ∂(varianceLaw k) = k) ∧
                 (Integrable (fun ω : Counts 1 1 × ℝ => ((ω.1.2 0 : ℝ))) (varianceLaw k) ∧ ∫ ω, ((ω.1.2 0 : ℝ)) ∂(varianceLaw k) = k)) := by
               intro k
               refine ⟨hcoord k (fun ω => ω.1.1.1 0) ((measurable_pi_apply 0).comp (measurable_fst.comp (measurable_fst.comp measurable_fst))) ?_,
                 hcoord k (fun ω => ω.1.1.2 0) ((measurable_pi_apply 0).comp (measurable_snd.comp (measurable_fst.comp measurable_fst))) ?_,
                 hcoord k (fun ω => ω.1.2 0) ((measurable_pi_apply 0).comp (measurable_snd.comp measurable_fst)) ?_⟩
               · rw [(hlaw k).1]; congr 2; ring
               · rw [(hlaw k).2.1]; congr 2; ring
               · rw [(hlaw k).2.2]; congr 2; ring
             have hcast : ∀ k z, (matchedCount k z : ℝ) = min ((z.1.1 0 : ℝ) + z.1.2 0) (min (z.2 0 : ℝ) (3 * k)) ∧
                 (lowerControl k z : ℝ) = max ((matchedCount k z : ℝ) - z.1.2 0) 0 ∧
                 (upperControl k z : ℝ) = min (matchedCount k z : ℝ) (z.1.1 0) := by
               intro k z
               refine ⟨by rw [matchedCount, Nat.cast_min, Nat.cast_min, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat],
                 ?_, by rw [upperControl, Nat.cast_min]⟩
               unfold lowerControl
               rcases le_total (matchedCount k z) (z.1.2 0) with h | h
               · rw [Nat.sub_eq_zero_of_le h, max_eq_right (sub_nonpos.mpr (Nat.cast_le.mpr h)), Nat.cast_zero]
               · rw [Nat.cast_sub h, max_eq_left (sub_nonneg.mpr (Nat.cast_le.mpr h))]
             have halg : ∀ (U L m M s K c : ℝ), L ≤ m → m ≤ U → 0 < K → s^2 = K →
                 16 / K * ((U - m) * (m - L)) ≤ (s * ((1 / K) * (2 * M - 4 * U)) - c)^2 * ((m - L) / (U - L)) +
                   (s * ((1 / K) * (2 * M - 4 * L)) - c)^2 * (1 - (m - L) / (U - L)) := by
               intro U L m M s K c hl hu hK hs
               rcases eq_or_lt_of_le (hl.trans hu) with h | h
               · have h1 : m = L := le_antisymm (h ▸ hu) hl
                 rw [h1, ← h, sub_self, mul_zero, mul_zero, zero_div, mul_zero, sub_zero, mul_one, zero_add]
                 exact sq_nonneg _
               · have hp : (m - L) / (U - L) * (U - L) = m - L := div_mul_cancel₀ _ (sub_pos.mpr h).ne'
                 have hK1 : K * (1 / K)^2 = 1 / K := by rw [sq, ← mul_assoc, mul_one_div_cancel hK.ne', one_mul]
                 generalize (m - L) / (U - L) = p at hp ⊢
                 generalize ha : s * ((1 / K) * (2 * M - 4 * U)) - c = a
                 generalize hb : s * ((1 / K) * (2 * M - 4 * L)) - c = b
                 have hab : (a - b)^2 = 16 / K * (U - L)^2 := by
                   have : (a - b)^2 = s^2 * (1/K)^2 * (16 * (U - L)^2) := by rw [← ha, ← hb]; ring
                   rw [this, hs, hK1]; ring
                 have e1 : a^2 * p + b^2 * (1 - p) = (p * a + (1 - p) * b)^2 + p * (1 - p) * (a - b)^2 := by ring
                 have e2 : p * (1 - p) * (16 / K * (U - L)^2) = 16 / K * ((p * (U - L)) * ((U - L) - p * (U - L))) := by ring
                 have e3 : (U - L) - (m - L) = U - m := by ring
                 rw [e1, hab, e2, hp, e3, mul_comm (m - L)]
                 exact le_add_of_nonneg_left (sq_nonneg _)
             have hLbR : ∀ (C T S K g : ℝ), 0 < K → 0 ≤ g →
                 ((|C - K| ≤ K/10 ∧ |T - K| ≤ K/10 ∧ |S - K| ≤ K/10) → K^2/16 ≤ g) →
                 K - 100 / K * ((C - K)^2 + (T - K)^2 + (S - K)^2) ≤ 16 / K * g := by
               intro C T S K g hKp hg hgood
               have hGz : 0 ≤ 16 / K * g := mul_nonneg (div_nonneg (by norm_num) hKp.le) hg
               have p1 := sq_nonneg (C - K)
               have p2 := sq_nonneg (T - K)
               have p3 := sq_nonneg (S - K)
               have hQ : 0 ≤ 100 / K * ((C - K)^2 + (T - K)^2 + (S - K)^2) :=
                 mul_nonneg (div_nonneg (by norm_num) hKp.le) (add_nonneg (add_nonneg p1 p2) p3)
               by_cases hg' : |C - K| ≤ K/10 ∧ |T - K| ≤ K/10 ∧ |S - K| ≤ K/10
               · have h := hgood hg'
                 have h' : K ≤ 16 / K * g := by
                   calc K = 16 / K * (K^2/16) := by rw [div_mul_div_comm, eq_div_iff (mul_pos hKp (by norm_num)).ne']; ring
                     _ ≤ _ := mul_le_mul_of_nonneg_left h (div_nonneg (by norm_num) hKp.le)
                 linarith only [h', hQ]
               · have key : ∀ x : ℝ, ¬ |x - K| ≤ K/10 → K^2 < 100 * (x - K)^2 := by
                   intro x hx
                   have h1 := pow_lt_pow_left₀ (lt_of_not_ge hx) (div_nonneg hKp.le (by norm_num) : (0:ℝ) ≤ K/10) two_ne_zero
                   rw [sq_abs] at h1
                   have e : (K/10)^2 = K^2/100 := by ring
                   linarith only [e, h1]
                 have hsq : K^2 < 100 * ((C - K)^2 + (T - K)^2 + (S - K)^2) := by
                   rw [not_and_or, not_and_or] at hg'
                   rcases hg' with h | h | h <;> have := key _ h <;> linarith only [this, p1, p2, p3]
                 have hbig : K < 100 / K * ((C - K)^2 + (T - K)^2 + (S - K)^2) := by
                   rw [div_mul_eq_mul_div, lt_div_iff₀ hKp]
                   have e : K * K = K^2 := by ring
                   linarith only [e, hsq]
                 linarith only [hbig, hGz]
             have hZBR : ∀ (C T S K M A mn s : ℝ), 0 ≤ C → 0 ≤ T → 0 ≤ S → 1 ≤ K → M = min (C + T) (min S (3 * K)) →
                 |A - mn| ≤ 1 → mn = M * C / (C + T) → s^2 = K → 0 < s →
                 (s * ((1 / K) * (2 * M - 4 * A)) - (1 / s) * (T - C))^2 ≤
                   1 / K * (1800 / K^2 * ((C - K)^4 + (T - K)^4 + (S - K)^4) + 32) := by
               intro C T S K M A mn s hC0 hT0 hS0 hK hm hε hmn hs hsp
               have hKp : 0 < K := lt_of_lt_of_le one_pos hK
               have hMle : M ≤ C + T := by rw [hm]; exact min_le_left _ _
               have hM0 : 0 ≤ M := by rw [hm]; exact le_min (add_nonneg hC0 hT0) (le_min hS0 (by linarith only [hK]))
               have hRid : 2 * M - 4 * mn - (T - C) = (T - C) * (2 * M - (C + T)) / (C + T) := by
                 rw [hmn]
                 rcases eq_or_lt_of_le (add_nonneg hC0 hT0) with h | h
                 · have hC : C = 0 := by linarith only [h, hC0, hT0]
                   have hT : T = 0 := by linarith only [h, hC0, hT0]
                   have hM : M = 0 := by linarith only [h, hMle, hM0]
                   rw [hC, hT, hM]; simp only [mul_zero, zero_mul, add_zero, zero_div, sub_self, div_zero]
                 · rw [eq_div_iff h.ne', sub_mul, sub_mul, mul_assoc 4, div_mul_cancel₀ _ h.ne']; ring
               have hRb := hR C T S K M hC0 hT0 hS0 hK hm
               generalize (T - C) * (2 * M - (C + T)) / (C + T) = R at hRid hRb
               have hsk : s * (1 / K) = 1 / s := by
                 rw [eq_div_iff hsp.ne', mul_comm, ← mul_assoc, ← sq, hs, mul_one_div_cancel hKp.ne']
               have hZe : (s * ((1 / K) * (2 * M - 4 * A)) - (1 / s) * (T - C))^2 = 1 / K * (R - 4 * (A - mn))^2 := by
                 rw [← mul_assoc, hsk, ← mul_sub, mul_pow, div_pow, one_pow, hs, ← hRid]
                 ring
               rw [hZe]
               refine mul_le_mul_of_nonneg_left ?_ (div_nonneg zero_le_one hKp.le)
               generalize A - mn = ε at hε
               have hε2 : ε^2 ≤ 1 := by rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) hε
               have h1 : (R - 4 * ε)^2 ≤ 2 * R^2 + 32 := by linear_combination 32 * hε2 + sq_nonneg (R + 4 * ε)
               linear_combination h1 + 2 * hRb
             have hite' : ∀ (p : ℝ), 0 ≤ p → p ≤ 1 → ∀ (a b : ℕ) (g : ℕ → ℝ),
                 ∫ u in Set.Icc (0:ℝ) 1, g (if u < p then a else b) = g a * p + g b * (1 - p) := by
               intro p h0 h1 a b g
               rw [← hite p h0 h1 (g a) (g b)]
               congr 1; funext u; split_ifs <;> rfl
             have hoddK : ∀ k : ℕ, 1 ≤ k → k % 2 = 0 → |variance (fun ω => Real.sqrt (k:ℝ) * ((1 / (k:ℝ)) *
                 (2 * (matchedCount k ω.1 : ℝ) - 4 * (alternatingControl k ω : ℝ)))) (varianceLaw k) - 2| ≤ 100000 / Real.sqrt k := by
               intro k hk1 hk2
               haveI := hprob k
               obtain ⟨⟨hC4i, hC4⟩, ⟨hC2i, hC2⟩, ⟨hC1i, hC1⟩⟩ := (hCo k).1
               obtain ⟨⟨hT4i, hT4⟩, ⟨hT2i, hT2⟩, ⟨hT1i, hT1⟩⟩ := (hCo k).2.1
               obtain ⟨⟨hS4i, hS4⟩, -, -⟩ := (hCo k).2.2
               have hK : (1:ℝ) ≤ k := by exact_mod_cast hk1
               have hKp : (0:ℝ) < k := lt_of_lt_of_le one_pos hK
               have hs : Real.sqrt (k:ℝ) ^ 2 = k := Real.sq_sqrt hKp.le
               have hs1 : 1 ≤ Real.sqrt (k:ℝ) := Real.one_le_sqrt.mpr hK
               have hsp : 0 < Real.sqrt (k:ℝ) := lt_of_lt_of_le one_pos hs1
               have hfm : Measurable (fun ω : Counts 1 1 × ℝ => Real.sqrt (k:ℝ) * ((1 / (k:ℝ)) *
                   (2 * (matchedCount k ω.1 : ℝ) - 4 * (alternatingControl k ω : ℝ)))) :=
                 ((((hmeasM k).const_mul 2).sub ((hmeasA k).const_mul 4)).const_mul _).const_mul _
               have hCm : Measurable (fun ω : Counts 1 1 × ℝ => (ω.1.1.1 0 : ℝ)) :=
                 (measurable_of_countable (fun z : Counts 1 1 => (z.1.1 0 : ℝ))).comp measurable_fst
               have hTm : Measurable (fun ω : Counts 1 1 × ℝ => (ω.1.1.2 0 : ℝ)) :=
                 (measurable_of_countable (fun z : Counts 1 1 => (z.1.2 0 : ℝ))).comp measurable_fst
               have hCL : MemLp (fun ω : Counts 1 1 × ℝ => (ω.1.1.1 0 : ℝ)) 2 (varianceLaw k) := by
                 have h := ((memLp_two_iff_integrable_sq ((hCm.sub_const (k:ℝ)).aestronglyMeasurable)).mpr hC2i).add
                   (memLp_const (k:ℝ))
                 convert h using 1
                 funext ω; exact (sub_add_cancel _ _).symm
               have hTL : MemLp (fun ω : Counts 1 1 × ℝ => (ω.1.1.2 0 : ℝ)) 2 (varianceLaw k) := by
                 have h := ((memLp_two_iff_integrable_sq ((hTm.sub_const (k:ℝ)).aestronglyMeasurable)).mpr hT2i).add
                   (memLp_const (k:ℝ))
                 convert h using 1
                 funext ω; exact (sub_add_cancel _ _).symm
               have hVC : variance (fun ω : Counts 1 1 × ℝ => (ω.1.1.1 0 : ℝ)) (varianceLaw k) = k := by
                 rw [variance_eq_integral hCm.aemeasurable]
                 rw [hC1]; exact hC2
               have hVT : variance (fun ω : Counts 1 1 × ℝ => (ω.1.1.2 0 : ℝ)) (varianceLaw k) = k := by
                 rw [variance_eq_integral hTm.aemeasurable]
                 rw [hT1]; exact hT2
               have hcov : covariance (fun ω : Counts 1 1 × ℝ => (ω.1.1.2 0 : ℝ)) (fun ω : Counts 1 1 × ℝ => (ω.1.1.1 0 : ℝ))
                   (varianceLaw k) = 0 :=
                 ((hindep k).symm.comp (measurable_of_countable (Nat.cast : ℕ → ℝ))
                   (measurable_of_countable (Nat.cast : ℕ → ℝ))).covariance_eq_zero hTL hCL
               have hYL : MemLp (fun ω : Counts 1 1 × ℝ => (1 / Real.sqrt k) * ((ω.1.1.2 0 : ℝ) - (ω.1.1.1 0 : ℝ))) 2 (varianceLaw k) :=
                 (hTL.sub hCL).const_mul _
               have hVY : variance (fun ω : Counts 1 1 × ℝ => (1 / Real.sqrt k) * ((ω.1.1.2 0 : ℝ) - (ω.1.1.1 0 : ℝ))) (varianceLaw k) = 2 := by
                 rw [variance_const_mul, variance_fun_sub hTL hCL, hVT, hVC, hcov, div_pow, hs, one_pow, mul_zero,
                   sub_zero, div_mul_eq_mul_div, one_mul, div_eq_iff hKp.ne']
                 ring
               have hfL : MemLp (fun ω : Counts 1 1 × ℝ => Real.sqrt (k:ℝ) * ((1 / (k:ℝ)) *
                   (2 * (matchedCount k ω.1 : ℝ) - 4 * (alternatingControl k ω : ℝ)))) 2 (varianceLaw k) := by
                 refine MemLp.of_bound hfm.aestronglyMeasurable (12 * Real.sqrt k) ?_
                 filter_upwards [hbnd k] with ω hω
                 have hm := hmle k ω.1
                 have hA0 : (0:ℝ) ≤ alternatingControl k ω := Nat.cast_nonneg _
                 have hW : |(1 / (k:ℝ)) * (2 * (matchedCount k ω.1 : ℝ) - 4 * (alternatingControl k ω : ℝ))| ≤ 12 := by
                   rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / k), one_div, inv_mul_le_iff₀ hKp, abs_le]
                   obtain ⟨hb1, -, -⟩ := hω
                   constructor <;> linarith only [hb1, hm, hA0]
                 rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_comm]
                 exact mul_le_mul_of_nonneg_right hW (Real.sqrt_nonneg _)
               have hZL := hfL.sub hYL
               have hZ2 := (memLp_two_iff_integrable_sq hZL.aestronglyMeasurable).mp hZL
               have h4 : Integrable (fun ω : Counts 1 1 × ℝ => (((ω.1.1.1 0 : ℕ) : ℝ) - k)^4 + (((ω.1.1.2 0 : ℕ) : ℝ) - k)^4) (varianceLaw k) :=
                 hC4i.add hT4i
               have h4' : Integrable (fun ω : Counts 1 1 × ℝ => (((ω.1.1.1 0 : ℕ) : ℝ) - k)^4 + (((ω.1.1.2 0 : ℕ) : ℝ) - k)^4
                 + (((ω.1.2 0 : ℕ) : ℝ) - k)^4) (varianceLaw k) := h4.add hS4i
               have h4'' : Integrable (fun ω : Counts 1 1 × ℝ => 1800 / (k:ℝ)^2 * ((((ω.1.1.1 0 : ℕ) : ℝ) - k)^4 + (((ω.1.1.2 0 : ℕ) : ℝ) - k)^4
                 + (((ω.1.2 0 : ℕ) : ℝ) - k)^4) + 32) (varianceLaw k) := (h4'.const_mul _).add (integrable_const _)
               have hBdi : Integrable (fun ω : Counts 1 1 × ℝ => 1 / (k:ℝ) * (1800 / (k:ℝ)^2 * ((((ω.1.1.1 0 : ℕ) : ℝ) - k)^4 + (((ω.1.1.2 0 : ℕ) : ℝ) - k)^4
                 + (((ω.1.2 0 : ℕ) : ℝ) - k)^4) + 32)) (varianceLaw k) := h4''.const_mul _
               have hEZ : ∫ ω, 1 / (k:ℝ) * (1800 / (k:ℝ)^2 * ((((ω.1.1.1 0 : ℕ) : ℝ) - k)^4 + (((ω.1.1.2 0 : ℕ) : ℝ) - k)^4
                   + (((ω.1.2 0 : ℕ) : ℝ) - k)^4) + 32) ∂(varianceLaw k) ≤ 21632 / (k:ℝ) := by
                 rw [integral_const_mul, integral_add (h4'.const_mul _) (integrable_const _), integral_const_mul,
                   integral_add h4 hS4i, integral_add hC4i hT4i, hC4, hT4, hS4, integral_const, probReal_univ, one_smul]
                 have h1 : 1800 / (k:ℝ)^2 * (3 * (k:ℝ)^2 + k + (3 * (k:ℝ)^2 + k) + (3 * (k:ℝ)^2 + k)) ≤ 21600 := by
                   rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
                   linear_combination 5400 * le_self_pow₀ hK two_ne_zero
                 rw [one_div_mul_eq_div]
                 exact div_le_div_of_nonneg_right (by linarith only [h1]) hKp.le
               set F := (fun ω : Counts 1 1 × ℝ => Real.sqrt (k:ℝ) * ((1 / (k:ℝ)) *
                   (2 * (matchedCount k ω.1 : ℝ) - 4 * (alternatingControl k ω : ℝ)))) with hF
               set Yf := (fun ω : Counts 1 1 × ℝ => (1 / Real.sqrt k) * ((ω.1.1.2 0 : ℝ) - (ω.1.1.1 0 : ℝ))) with hYf
               have hZB : ∀ ω : Counts 1 1 × ℝ, ((F - Yf)^2) ω ≤
                   1 / (k:ℝ) * (1800 / (k:ℝ)^2 * ((((ω.1.1.1 0 : ℕ) : ℝ) - k)^4 + (((ω.1.1.2 0 : ℕ) : ℝ) - k)^4
                   + (((ω.1.2 0 : ℕ) : ℝ) - k)^4) + 32) := by
                 intro ω
                 have hAr : alternatingControl k ω = roundedControl k ω.1 ω.2 := by
                   unfold alternatingControl; rw [if_pos hk2]
                 obtain ⟨hm, -, -⟩ := hcast k ω.1
                 obtain ⟨-, -, h0⟩ := hmeanb k ω.1
                 have hε : |(alternatingControl k ω : ℝ) - meanControl k ω.1| ≤ 1 := by
                   rw [hAr]; unfold roundedControl
                   have hf1 := Nat.floor_le h0
                   have hf2 := Nat.lt_floor_add_one (meanControl k ω.1)
                   rw [abs_le]
                   split_ifs <;> push_cast <;> constructor <;> linarith only [hf1, hf2]
                 exact hZBR (ω.1.1.1 0) (ω.1.1.2 0) (ω.1.2 0) k (matchedCount k ω.1) (alternatingControl k ω)
                   (meanControl k ω.1) (Real.sqrt k) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
                   hK hm hε rfl hs hsp
               have hVZ : variance (F - Yf) (varianceLaw k) ≤ 21632 / (k:ℝ) :=
                 (variance_le_expectation_sq hZL.aestronglyMeasurable).trans ((integral_mono hZ2 hBdi hZB).trans hEZ)
               have up := hvar _ _ _ hYL hZL (1 / Real.sqrt k) (by positivity)
               have lo := hvar _ _ _ (hYL.add hZL) hZL.neg (1 / Real.sqrt k) (by positivity)
               have e1 : Yf + (F - Yf) = F := by abel
               rw [e1] at up lo
               have e2 : F + -(F - Yf) = Yf := by abel
               rw [e2, variance_neg, hVY, one_div_one_div] at lo
               rw [hVY, one_div_one_div] at up
               have hz0 := variance_nonneg (F - Yf) (varianceLaw k)
               clear_value F Yf
               generalize variance F (varianceLaw k) = v at up lo ⊢
               generalize variance (F - Yf) (varianceLaw k) = z at up lo hVZ hz0
               generalize hsd : Real.sqrt (k:ℝ) = s at *
               have hw : 1 / s * s = 1 := one_div_mul_cancel hsp.ne'
               have hw0 : 0 < 1 / s := by positivity
               have hw1 : 1 / s ≤ 1 := (div_le_one hsp).mpr hs1
               have hzs : z * s^2 ≤ 21632 := by rw [hs]; rwa [le_div_iff₀ hKp] at hVZ
               have H1 : z * s^2 * (1/s) ≤ 21632 * (1/s) := mul_le_mul_of_nonneg_right hzs hw0.le
               have H2 : 0 ≤ (s - 1) * z := mul_nonneg (sub_nonneg.mpr hs1) hz0
               have hz1 : (1 + s) * z ≤ 2 * 21632 * (1 / s) := by linear_combination 2 * H1 + H2 + (-2 * z * s) * hw
               have hv1 : v ≤ 2 + 2 * (1/s) + 2 * 21632 * (1/s) := by linear_combination up + hz1
               have H3 := mul_le_mul_of_nonneg_left hv1 hw0.le
               have H4 : 0 ≤ 1 / s * (1 - 1 / s) := mul_nonneg hw0.le (sub_nonneg.mpr hw1)
               have hv2 : v * (1/s) ≤ (4 + 2 * 21632) * (1/s) := by linear_combination H3 + 43266 * H4
               rw [abs_le, div_eq_mul_one_div 100000 s]
               exact ⟨by linear_combination lo + hz1 + hv2 + 13468 * hw0.le, by linear_combination hv1 + 56734 * hw0.le⟩
             have hevenK : ∀ k : ℕ, 1 ≤ k → k % 2 = 1 → (k:ℝ) - 300 ≤ variance (fun ω => Real.sqrt (k:ℝ) * ((1 / (k:ℝ)) *
                 (2 * (matchedCount k ω.1 : ℝ) - 4 * (alternatingControl k ω : ℝ)))) (varianceLaw k) := by
               intro k hk1 hk2
               haveI := hprob k
               have hmc : ∀ f : Counts 1 1 → ℝ, Measurable f := fun f => measurable_of_countable f
               obtain ⟨-, ⟨hC2i, hC2⟩, -⟩ := (hCo k).1
               obtain ⟨-, ⟨hT2i, hT2⟩, -⟩ := (hCo k).2.1
               obtain ⟨-, ⟨hS2i, hS2⟩, -⟩ := (hCo k).2.2
               have hK : (1:ℝ) ≤ k := by exact_mod_cast hk1
               have hKp : (0:ℝ) < k := lt_of_lt_of_le one_pos hK
               have hs : Real.sqrt (k:ℝ) ^ 2 = k := Real.sq_sqrt hKp.le
               have hs1 : 1 ≤ Real.sqrt (k:ℝ) := Real.one_le_sqrt.mpr hK
               have hfm : Measurable (fun ω : Counts 1 1 × ℝ => Real.sqrt (k:ℝ) * ((1 / (k:ℝ)) *
                   (2 * (matchedCount k ω.1 : ℝ) - 4 * (alternatingControl k ω : ℝ)))) :=
                 ((((hmeasM k).const_mul 2).sub ((hmeasA k).const_mul 4)).const_mul _).const_mul _
               rw [variance_eq_integral hfm.aemeasurable]
               set c := ∫ ω, Real.sqrt (k:ℝ) * ((1 / (k:ℝ)) *
                   (2 * (matchedCount k ω.1 : ℝ) - 4 * (alternatingControl k ω : ℝ))) ∂(varianceLaw k) with hc
               have hbd : ∀ᵐ ω ∂(varianceLaw k), ‖(Real.sqrt (k:ℝ) * ((1 / (k:ℝ)) *
                   (2 * (matchedCount k ω.1 : ℝ) - 4 * (alternatingControl k ω : ℝ))) - c)^2‖ ≤ (12 * Real.sqrt k + |c|)^2 := by
                 filter_upwards [hbnd k] with ω hω
                 have hm := hmle k ω.1
                 have hA0 : (0:ℝ) ≤ alternatingControl k ω := Nat.cast_nonneg _
                 have hW : |(1 / (k:ℝ)) * (2 * (matchedCount k ω.1 : ℝ) - 4 * (alternatingControl k ω : ℝ))| ≤ 12 := by
                   rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / k), one_div, inv_mul_le_iff₀ hKp, abs_le]
                   obtain ⟨hb1, -, -⟩ := hω
                   constructor <;> linarith only [hb1, hm, hA0]
                 rw [Real.norm_eq_abs, abs_pow]
                 refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
                 refine (abs_sub _ _).trans ?_
                 rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
                 have := mul_le_mul_of_nonneg_left hW (Real.sqrt_nonneg (k:ℝ))
                 linarith only [this]
               have hInt := Integrable.of_bound ((hfm.sub_const c).pow_const 2).aestronglyMeasurable _ hbd
               set P := MarketInterference.FiniteSample.experimentLaw (fun _ => (2:ℝ)) (fun _ => 0) (fun _ => 1) (1/2) (k:ℝ) with hP
               haveI : IsProbabilityMeasure P := by
                 rw [hP]; unfold MarketInterference.FiniteSample.experimentLaw MarketInterference.FiniteSample.poisLaw; infer_instance
               have hμ : varianceLaw k = P.prod (volume.restrict (Set.Icc (0:ℝ) 1)) := rfl
               have hmap : (varianceLaw k).map Prod.fst = P := by
                 rw [hμ, Measure.map_fst_prod, measure_univ, one_smul]
               let G : Counts 1 1 → ℝ := fun z => (16 / (k:ℝ)) * (((upperControl k z : ℝ) - meanControl k z) *
                 (meanControl k z - (lowerControl k z : ℝ)))
               let Lb : Counts 1 1 → ℝ := fun z => (k:ℝ) - (100 / (k:ℝ)) * (((z.1.1 0 : ℝ) - k)^2 + ((z.1.2 0 : ℝ) - k)^2
                 + ((z.2 0 : ℝ) - k)^2)
               have hLbμ : Integrable (fun ω : Counts 1 1 × ℝ => Lb ω.1) (varianceLaw k) :=
                 (integrable_const _).sub (((hC2i.add hT2i).add hS2i).const_mul _)
               have hLbP : Integrable Lb P := by
                 rw [← hmap]
                 exact (integrable_map_measure (hmc _).aestronglyMeasurable
                   measurable_fst.aemeasurable).mpr hLbμ
               have hLbI : ∫ z, Lb z ∂P = (k:ℝ) - 300 := by
                 rw [← hmap, integral_map measurable_fst.aemeasurable (hmc _).aestronglyMeasurable]
                 show ∫ ω, ((k:ℝ) - (100 / (k:ℝ)) * ((((ω.1.1.1 0 : ℕ) : ℝ) - k)^2 + (((ω.1.1.2 0 : ℕ) : ℝ) - k)^2
                   + (((ω.1.2 0 : ℕ) : ℝ) - k)^2)) ∂(varianceLaw k) = _
                 have h12 : Integrable (fun ω : Counts 1 1 × ℝ => (((ω.1.1.1 0 : ℕ) : ℝ) - k)^2 + (((ω.1.1.2 0 : ℕ) : ℝ) - k)^2) (varianceLaw k) := hC2i.add hT2i
                 have hsum : Integrable (fun ω : Counts 1 1 × ℝ => (((ω.1.1.1 0 : ℕ) : ℝ) - k)^2 + (((ω.1.1.2 0 : ℕ) : ℝ) - k)^2
                   + (((ω.1.2 0 : ℕ) : ℝ) - k)^2) (varianceLaw k) := h12.add hS2i
                 have e1 : ∫ ω, ((((ω.1.1.1 0 : ℕ) : ℝ) - k)^2 + (((ω.1.1.2 0 : ℕ) : ℝ) - k)^2
                     + (((ω.1.2 0 : ℕ) : ℝ) - k)^2) ∂(varianceLaw k) = 3 * k := by
                   rw [integral_add h12 hS2i, integral_add hC2i hT2i, hC2, hT2, hS2]; ring
                 rw [integral_sub (integrable_const _) (hsum.const_mul _), integral_const_mul, e1, integral_const]
                 rw [probReal_univ, one_smul]
                 have : (100:ℝ) / k * (3 * k) = 300 := by rw [div_mul_eq_mul_div, div_eq_iff hKp.ne']; ring
                 linarith only [this]
               have hG0 : ∀ z, 0 ≤ ((upperControl k z : ℝ) - meanControl k z) * (meanControl k z - (lowerControl k z : ℝ)) := by
                 intro z
                 obtain ⟨hl, hu, -⟩ := hmeanb k z
                 exact mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hl)
               have hGi : Integrable G P := by
                 refine Integrable.of_bound (hmc _).aestronglyMeasurable ((16 / (k:ℝ)) * (9 * (k:ℝ)^2))
                   (Eventually.of_forall fun z => ?_)
                 obtain ⟨hl, hu, h0⟩ := hmeanb k z
                 have h3 : (upperControl k z : ℝ) ≤ 3 * k := by
                   have : upperControl k z ≤ matchedCount k z := min_le_left _ _
                   exact (Nat.cast_le.mpr this).trans (hmle k z)
                 have hL0 : (0:ℝ) ≤ lowerControl k z := Nat.cast_nonneg _
                 rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (div_nonneg (by norm_num) hKp.le) (hG0 z))]
                 refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (by norm_num) hKp.le)
                 calc _ ≤ (3 * (k:ℝ)) * (3 * k) := mul_le_mul (by linarith only [h3, h0]) (by linarith only [hu, h3, hL0]) (by linarith only [hl]) (by linarith only [hK])
                   _ = 9 * (k:ℝ)^2 := by ring
               have hLb : ∀ z, Lb z ≤ G z := by
                 intro z
                 obtain ⟨hm, hL, hU⟩ := hcast k z
                 exact hLbR _ _ _ _ _ hKp (hG0 z) (fun hg => hLow _ _ _ _ _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _)
                   (Nat.cast_nonneg _) hK hm hL hU hg.1 hg.2.1 hg.2.2)
               have hG : ∀ z, G z ≤ ∫ u in Set.Icc (0:ℝ) 1, (Real.sqrt (k:ℝ) * ((1 / (k:ℝ)) *
                   (2 * (matchedCount k z : ℝ) - 4 * (alternatingControl k (z, u) : ℝ))) - c)^2 := by
                 intro z
                 obtain ⟨hl, hu, h0⟩ := hmeanb k z
                 have hp0 : 0 ≤ (meanControl k z - (lowerControl k z : ℝ)) / ((upperControl k z : ℝ) - (lowerControl k z : ℝ)) :=
                   div_nonneg (by linarith only [hl]) (by linarith only [hl, hu])
                 have hp1 : (meanControl k z - (lowerControl k z : ℝ)) / ((upperControl k z : ℝ) - (lowerControl k z : ℝ)) ≤ 1 :=
                   div_le_one_of_le₀ (by linarith only [hu]) (by linarith only [hl, hu])
                 have e : ∀ u, alternatingControl k (z, u) = extremeControl k z u := fun u => by
                   unfold alternatingControl; rw [if_neg (by omega)]
                 let g : ℕ → ℝ := fun n => (Real.sqrt (k:ℝ) * ((1 / (k:ℝ)) * (2 * (matchedCount k z : ℝ) - 4 * (n : ℝ))) - c)^2
                 have hfun : (fun u : ℝ => (Real.sqrt (k:ℝ) * ((1 / (k:ℝ)) * (2 * (matchedCount k z : ℝ) -
                     4 * (alternatingControl k (z, u) : ℝ))) - c)^2) = fun u => g (extremeControl k z u) :=
                   funext fun u => by rw [e]
                 rw [hfun]
                 exact le_of_le_of_eq (halg _ _ _ _ _ _ c hl hu hKp hs)
                   (hite' _ hp0 hp1 (upperControl k z) (lowerControl k z) g).symm
               have hInt' : Integrable (fun ω : Counts 1 1 × ℝ => (Real.sqrt (k:ℝ) * ((1 / (k:ℝ)) *
                   (2 * (matchedCount k ω.1 : ℝ) - 4 * (alternatingControl k ω : ℝ))) - c)^2)
                   (P.prod (volume.restrict (Set.Icc (0:ℝ) 1))) := hInt
               have e := integral_prod _ hInt'
               show (k:ℝ) - 300 ≤ ∫ ω, (Real.sqrt (k:ℝ) * ((1 / (k:ℝ)) *
                   (2 * (matchedCount k ω.1 : ℝ) - 4 * (alternatingControl k ω : ℝ))) - c)^2 ∂(P.prod (volume.restrict (Set.Icc (0:ℝ) 1)))
               rw [e, ← hLbI]
               exact (integral_mono hLbP hGi hLb).trans (integral_mono hGi hInt'.integral_prod_left hG)
             have hodd : Tendsto (fun n => V (2 * n + 1)) atTop (nhds 2) := by
               rw [tendsto_iff_norm_sub_tendsto_zero]
               refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) ((tendsto_const_nhds (x := (100000:ℝ))).div_atTop
                 (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp
                   (tendsto_atTop_mono (fun n => (by omega : n ≤ 2 * n + 1 + 1)) tendsto_id))))
               rw [hVe, Real.norm_eq_abs]
               exact hoddK (2 * n + 1 + 1) (by omega) (by omega)
             have heven : Tendsto (fun n => V (2 * n)) atTop atTop := by
               rw [tendsto_atTop]
               intro b
               filter_upwards [eventually_ge_atTop ⌈b + 300⌉₊] with n hn
               have h1 := hevenK (2 * n + 1) (by omega) (by omega)
               have h2 : b + 300 ≤ (n:ℝ) := Nat.ceil_le.mp hn
               show b ≤ V (2 * n)
               rw [hVe]
               push_cast at h1 ⊢
               linarith only [h1, h2, (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
             refine ⟨hodd, heven, ?_⟩
             rintro ⟨v, hv⟩
             have h1 := hv.comp (tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))
             exact not_tendsto_nhds_of_tendsto_atTop heven v h1
