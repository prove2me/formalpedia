-- Prove2me | solution 1 for HLambdaG.Main.Supplement.theorem_4_corrected
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:25:05.212018+00:00
-- url     : https://prove2.me/submissions/e539db10-e80e-4490-9bf9-8f199f37c7f9

import Mathlib
import Definitions.Def_HLambdaG_Main_Supplement_Discrete

open scoped NNReal

open HLambdaG
open HLambdaG.Main
open HLambdaG.Main.Supplement

open Filter Topology

/-- Theorem 4, p. 641, with the inequalities of (a)(i), (a)(ii), (b)(i), (b)(ii) corrected
(the printed parts interchange the roles of (17) and (18), as Theorem 1(a)/(b) do), and (17)
taken with lower index `n + 1` (Theorem 2). Setting of §1.1, `F(s, t) = Σ_{k ≤ [s]} F_k(t)`. -/
theorem solution (D : DiscreteSetting) (lam : ℝ) (hlam : 0 < lam) :
    -- (a): `n⁻¹T_n → λ⁻¹` and `G(n) → g`
    (∀ g : ℝ, Tendsto (fun n : ℕ => (D.T n : ℝ) / (n : ℝ)) atTop (𝓝 lam⁻¹) →
      Tendsto (fun n : ℕ => G D.input (n : ℝ≥0)) atTop (𝓝 g) →
        (D.Cond17 → limsupE (H D.input) ≤ ((lam * g : ℝ) : EReal)) ∧
        ((∃ S, D.Cond18 S) → ((lam * g : ℝ) : EReal) ≤ liminfE (H D.input)) ∧
        (D.Cond17 → (∃ S, D.Cond18 S) → Tendsto (H D.input) atTop (𝓝 (lam * g)))) ∧
    -- (b): `t⁻¹N(t) → λ` and `H(t) → h`
    (∀ h : ℝ, Tendsto (fun t : ℝ≥0 => (D.N t : ℝ) / (t : ℝ)) atTop (𝓝 lam) →
      Tendsto (H D.input) atTop (𝓝 h) →
        (D.Cond17 → ((lam⁻¹ * h : ℝ) : EReal) ≤
          Filter.liminf (fun n : ℕ => ((G D.input (n : ℝ≥0) : ℝ) : EReal)) atTop) ∧
        ((∃ S, D.Cond18 S) →
          Filter.limsup (fun n : ℕ => ((G D.input (n : ℝ≥0) : ℝ) : EReal)) atTop ≤
            ((lam⁻¹ * h : ℝ) : EReal)) ∧
        (D.Cond17 → (∃ S, D.Cond18 S) →
          Tendsto (fun n : ℕ => G D.input (n : ℝ≥0)) atTop (𝓝 (lam⁻¹ * h)))) := by
            have hIcc : ∀ (t : ℝ≥0) (n : ℕ), ∑ k ∈ Finset.Icc 1 n, D.F k t
                = ∑ k ∈ Finset.range (n+1), D.F k t := by
              intro t n
              induction n with
              | zero => simp [D.F_zero]
              | succ m ih =>
                rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ _ (m+1)]
            obtain ⟨B, hBdef⟩ : ∃ B : ℝ≥0 → ℝ, ∀ t, B t = ∑' k, D.F k t := ⟨_, fun _ => rfl⟩
            obtain ⟨R, hRdef⟩ : ∃ R : ℕ → ℝ≥0 → ℝ, ∀ m t, R m t = ∑' j, D.F (m + 1 + j) t :=
              ⟨_, fun _ _ => rfl⟩
            obtain ⟨A, hAdef⟩ : ∃ A : ℕ → ℝ, ∀ n, A n = ∑ k ∈ Finset.Icc 1 n, D.Finf k :=
              ⟨_, fun _ => rfl⟩
            have hsplit : ∀ (m : ℕ) (t : ℝ≥0), B t = ∑ k ∈ Finset.Icc 1 m, D.F k t + R m t := by
              intro m t
              rw [hBdef, hRdef, hIcc, ← (D.F_summable t).sum_add_tsum_nat_add (m+1)]
              congr 1
              refine tsum_congr (fun j => ?_)
              rw [add_comm]
            have hRsum : ∀ (m : ℕ) (t : ℝ≥0), Summable (fun j => D.F (m + 1 + j) t) := by
              intro m t
              have := (summable_nat_add_iff (m+1)).mpr (D.F_summable t)
              refine this.congr (fun j => ?_)
              simp only [add_comm]
            have hR0 : ∀ m t, 0 ≤ R m t := fun m t => by
              rw [hRdef]; exact tsum_nonneg (fun j => D.F_nonneg _ _)
            have hRmono : ∀ m (t t' : ℝ≥0), t ≤ t' → R m t ≤ R m t' := by
              intro m t t' h
              rw [hRdef, hRdef]
              exact (hRsum m t).tsum_le_tsum (fun j => D.F_mono _ h) (hRsum m t')
            have hH : ∀ t, H D.input t = ((t : ℝ))⁻¹ * B t := by
              intro t
              show ((t : ℝ))⁻¹ * FInfT D.input t = _
              congr 1
              rw [hBdef]
              show (⨆ s : ℝ≥0, ∑ k ∈ Finset.Icc 1 ⌊s⌋₊, D.F k t) = _
              apply le_antisymm
              · exact ciSup_le (fun s => (D.F_summable t).sum_le_tsum _ (fun k _ => D.F_nonneg k t))
              · refine Real.tsum_le_of_sum_range_le (fun k => D.F_nonneg k t) (fun n => ?_)
                have hb : BddAbove (Set.range (fun s : ℝ≥0 => ∑ k ∈ Finset.Icc 1 ⌊s⌋₊, D.F k t)) :=
                  D.input.bdd_s t
                calc ∑ k ∈ Finset.range n, D.F k t ≤ ∑ k ∈ Finset.range (n+1), D.F k t :=
                      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (Nat.le_succ n))
                        (fun k _ _ => D.F_nonneg k t)
                  _ = ∑ k ∈ Finset.Icc 1 ⌊((n:ℝ≥0))⌋₊, D.F k t := by rw [Nat.floor_natCast, hIcc]
                  _ ≤ _ := le_ciSup hb (n : ℝ≥0)
            have hFle : ∀ k t, D.F k t ≤ D.Finf k := fun k t => le_ciSup (D.F_bdd k) t
            have hG : ∀ n : ℕ, G D.input (n : ℝ≥0) = ((n : ℝ))⁻¹ * A n := by
              intro n
              show (((n:ℝ≥0) : ℝ))⁻¹ * FsInf D.input (n : ℝ≥0) = _
              rw [NNReal.coe_natCast]
              congr 1
              show (⨆ t : ℝ≥0, ∑ k ∈ Finset.Icc 1 ⌊(n:ℝ≥0)⌋₊, D.F k t) = _
              rw [Nat.floor_natCast, hAdef]
              have h1 : Tendsto (fun t : ℝ≥0 => ∑ k ∈ Finset.Icc 1 n, D.F k t) atTop
                  (𝓝 (∑ k ∈ Finset.Icc 1 n, D.Finf k)) :=
                tendsto_finsetSum _ (fun k _ => tendsto_atTop_ciSup (D.F_mono k) (D.F_bdd k))
              have h2 : Tendsto (fun t : ℝ≥0 => ∑ k ∈ Finset.Icc 1 n, D.F k t) atTop
                  (𝓝 (⨆ t : ℝ≥0, ∑ k ∈ Finset.Icc 1 n, D.F k t)) := by
                have hm := D.input.mono_t (n : ℝ≥0)
                have hb := D.input.bdd_t (n : ℝ≥0)
                simp only [DiscreteSetting.input, Nat.floor_natCast] at hm hb
                exact tendsto_atTop_ciSup hm hb
              exact tendsto_nhds_unique h2 h1
            have hsumA : ∀ m t, ∑ k ∈ Finset.Icc 1 m, D.F k t ≤ A m := fun m t => by
              rw [hAdef]; exact Finset.sum_le_sum (fun k _ => hFle k t)
            have hsumB : ∀ m t, ∑ k ∈ Finset.Icc 1 m, D.F k t ≤ B t := fun m t => by
              rw [hsplit m t]; linarith [hR0 m t]
            have hcount : ∀ V : ℕ → ℝ≥0, Monotone V → Tendsto V atTop atTop → V 0 = 0 → ∀ t : ℝ≥0,
                V (sSup {k | V k ≤ t}) ≤ t ∧ t < V (sSup {k | V k ≤ t} + 1) ∧
                  ∀ n, V n ≤ t → n ≤ sSup {k | V k ≤ t} := by
              intro V hVm hVt hV0 t
              obtain ⟨K, hK⟩ := eventually_atTop.1 (hVt.eventually_gt_atTop t)
              have hbdd : BddAbove {k | V k ≤ t} := by
                refine ⟨K, fun k hk => ?_⟩
                by_contra hc
                push_neg at hc
                have := hK k hc.le
                simp only [Set.mem_setOf_eq] at hk
                exact absurd hk (not_le.2 this)
              have hne : ({k | V k ≤ t} : Set ℕ).Nonempty := ⟨0, by simp [hV0]⟩
              have hmem : V (sSup {k | V k ≤ t}) ≤ t := Nat.sSup_mem hne hbdd
              have hle : ∀ n, V n ≤ t → n ≤ sSup {k | V k ≤ t} := fun n hn => le_csSup hbdd hn
              refine ⟨hmem, ?_, hle⟩
              by_contra hc
              push_neg at hc
              have := hle _ hc
              omega
            have hcountT : ∀ V : ℕ → ℝ≥0, Monotone V → Tendsto V atTop atTop → V 0 = 0 →
                Tendsto (fun t : ℝ≥0 => sSup {k | V k ≤ t}) atTop atTop := by
              intro V hVm hVt hV0
              refine tendsto_atTop.2 (fun n => ?_)
              filter_upwards [eventually_ge_atTop (V n)] with t ht
              exact (hcount V hVm hVt hV0 t).2.2 n ht
            have hTr : Tendsto (fun n => (D.T n : ℝ)) atTop atTop := NNReal.tendsto_coe_atTop.2 D.T_tendsto
            have hTpos : ∀ᶠ n in atTop, (0 : ℝ) < D.T n := hTr.eventually_gt_atTop 0
            have hUlim : ∀ S : ℕ → ℝ≥0, Tendsto (fun n : ℕ => (S n : ℝ) / (D.T n : ℝ)) atTop (𝓝 0) →
                Tendsto (fun n : ℕ => (U S n : ℝ) / (D.T n : ℝ)) atTop (𝓝 0) := by
              intro S hS
              have hpos := hTpos
              rw [tendsto_order]
              refine ⟨fun a ha => Eventually.of_forall (fun n => lt_of_lt_of_le ha (by positivity)), ?_⟩
              intro b hb
              have hε : (0 : ℝ) < b / 2 := by linarith
              have h1 : ∀ᶠ n in atTop, (S n : ℝ) / D.T n < b / 2 := (tendsto_order.1 hS).2 _ hε
              obtain ⟨N, hN⟩ := eventually_atTop.1 (h1.and hpos)
              have hSk : ∀ k, N ≤ k → (S k : ℝ) ≤ b / 2 * D.T k := by
                intro k hk
                obtain ⟨h1, h2⟩ := hN k hk
                rw [div_lt_iff₀ h2] at h1
                linarith
              have hU : ∀ n, N ≤ n → (U S n : ℝ) ≤ U S N + b / 2 * D.T n := by
                intro n hn
                have hB : U S n ≤ U S N + (b/2).toNNReal * D.T n := by
                  apply Finset.sup_le
                  intro k hk
                  rcases le_or_gt k N with hkN | hkN
                  · have : S k ≤ U S N :=
                      Finset.le_sup (f := S) (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hk).1, hkN⟩)
                    exact le_trans this le_self_add
                  · rw [← NNReal.coe_le_coe]
                    push_cast
                    rw [Real.coe_toNNReal _ hε.le]
                    have := hSk k hkN.le
                    have hTk : (D.T k : ℝ) ≤ D.T n := NNReal.coe_le_coe.2 (D.T_mono (Finset.mem_Icc.1 hk).2)
                    have : (0:ℝ) ≤ U S N := (U S N).2
                    nlinarith
                have := NNReal.coe_le_coe.2 hB
                push_cast at this
                rwa [Real.coe_toNNReal _ hε.le] at this
              have h2 : Tendsto (fun n => (U S N : ℝ) / D.T n) atTop (𝓝 0) :=
                tendsto_const_nhds.div_atTop hTr
              have h3 : ∀ᶠ n in atTop, (U S N : ℝ) / D.T n < b / 2 := (tendsto_order.1 h2).2 _ hε
              filter_upwards [h3, hpos, eventually_ge_atTop N] with n h3 hp hn
              have := hU n hn
              rw [div_lt_iff₀ hp] at h3 ⊢
              nlinarith
            have hVlim : ∀ S : ℕ → ℝ≥0, D.Cond18 S →
                Tendsto (fun n : ℕ => (D.T n : ℝ) / (n : ℝ)) atTop (𝓝 lam⁻¹) →
                Tendsto (fun n : ℕ => ((D.T n + U S n : ℝ≥0) : ℝ) / (n : ℝ)) atTop (𝓝 lam⁻¹) := by
              intro S h18 hT
              have h := hT.add ((hUlim S h18.1).mul hT)
              rw [zero_mul, add_zero] at h
              refine h.congr' ?_
              filter_upwards [hTpos] with n hn
              push_cast
              field_simp
            have hV0 : ∀ S : ℕ → ℝ≥0, D.T 0 + U S 0 = 0 := by
              intro S; simp [U, D.T_zero]
            have hVmono : ∀ S : ℕ → ℝ≥0, Monotone (fun n => D.T n + U S n) :=
              fun S => D.T_mono.add (U_mono S)
            have hVtend : ∀ S : ℕ → ℝ≥0, Tendsto (fun n => D.T n + U S n) atTop atTop :=
              fun S => tendsto_atTop_mono (fun n => le_add_of_nonneg_right (by positivity)) D.T_tendsto
            have hlowV : ∀ (S : ℕ → ℝ≥0) (m : ℕ) (t : ℝ≥0), D.T m + U S m ≤ t →
                A m - ∑ k ∈ Finset.Icc 1 m, (D.Finf k - D.F k (D.T k + S k)) ≤
                  ∑ k ∈ Finset.Icc 1 m, D.F k t := by
              intro S m t ht
              rw [hAdef, ← Finset.sum_sub_distrib]
              refine Finset.sum_le_sum (fun k hk => ?_)
              have hk' := Finset.mem_Icc.1 hk
              have : D.T k + S k ≤ t :=
                le_trans (add_le_add (D.T_mono hk'.2) (Finset.le_sup (f := S) hk)) ht
              have := D.F_mono k this
              linarith
            have hlowV0 : ∀ (S : ℕ → ℝ≥0) (m : ℕ),
                0 ≤ A m - ∑ k ∈ Finset.Icc 1 m, (D.Finf k - D.F k (D.T k + S k)) := by
              intro S m
              rw [hAdef, ← Finset.sum_sub_distrib]
              refine Finset.sum_nonneg (fun k _ => ?_)
              linarith [D.F_nonneg k (D.T k + S k)]
            have hNt : Tendsto D.N atTop atTop := hcountT D.T D.T_mono D.T_tendsto D.T_zero
            have hNfacts : ∀ t, D.T (D.N t) ≤ t ∧ t < D.T (D.N t + 1) ∧ ∀ n, D.T n ≤ t → n ≤ D.N t :=
              hcount D.T D.T_mono D.T_tendsto D.T_zero
            have hB0 : ∀ t, 0 ≤ B t := fun t => by rw [hBdef]; exact tsum_nonneg (fun k => D.F_nonneg k t)
            refine ⟨fun g hT hGg => ?_, fun h hN hHh => ?_⟩
            · have hAn : Tendsto (fun n : ℕ => ((n:ℝ))⁻¹ * A n) atTop (𝓝 g) := hGg.congr hG
              have hA1 : Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹ * A (n+1)) atTop (𝓝 g) := by
                have := hAn.comp (tendsto_add_atTop_nat 1)
                refine this.congr (fun n => ?_)
                simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
              have hTn1 : Tendsto (fun n : ℕ => ((D.T n : ℝ) / ((n:ℝ)+1))⁻¹) atTop (𝓝 lam) := by
                have h1 := hT.mul (tendsto_natCast_div_add_atTop (1:ℝ))
                rw [mul_one] at h1
                have h2 := h1.inv₀ (inv_ne_zero hlam.ne')
                rw [inv_inv] at h2
                refine h2.congr' ?_
                filter_upwards [eventually_gt_atTop 0] with n hn
                have : (n:ℝ) ≠ 0 := by positivity
                congr 1
                field_simp
              have hup : D.Cond17 → ∃ u : ℝ≥0 → ℝ, Tendsto u atTop (𝓝 (lam * g)) ∧
                  ∀ᶠ t in atTop, H D.input t ≤ u t := by
                intro h17
                unfold DiscreteSetting.Cond17 at h17
                have hR1 : Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹ * R (n+1) (D.T (n+1))) atTop (𝓝 0) := by
                  have := h17.comp (tendsto_add_atTop_nat 1)
                  refine this.congr (fun n => ?_)
                  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, hRdef]
                refine ⟨fun t => ((D.T (D.N t) : ℝ) / ((D.N t : ℝ)+1))⁻¹ *
                  (((D.N t:ℝ)+1)⁻¹ * A (D.N t+1) + ((D.N t:ℝ)+1)⁻¹ * R (D.N t+1) (D.T (D.N t+1))),
                  ?_, ?_⟩
                · have := (hTn1.mul (hA1.add hR1)).comp hNt
                  rw [add_zero] at this
                  exact this
                · filter_upwards [hNt.eventually hTpos] with t ht
                  obtain ⟨h1, h2, -⟩ := hNfacts t
                  generalize D.N t = n at ht h1 h2 ⊢
                  have hb : B t ≤ A (n+1) + R (n+1) (D.T (n+1)) := by
                    rw [hsplit (n+1) t]
                    exact add_le_add (hsumA _ _) (hRmono _ _ _ h2.le)
                  have ht' : (D.T n : ℝ) ≤ t := h1
                  rw [hH]
                  have e : ((D.T n:ℝ)/((n:ℝ)+1))⁻¹ * (((n:ℝ)+1)⁻¹ * A (n+1) +
                      ((n:ℝ)+1)⁻¹ * R (n+1) (D.T (n+1))) =
                      (D.T n : ℝ)⁻¹ * (A (n+1) + R (n+1) (D.T (n+1))) := by
                    have : (n:ℝ) + 1 ≠ 0 := by positivity
                    field_simp
                  rw [e]
                  calc ((t:ℝ))⁻¹ * B t ≤ (D.T n:ℝ)⁻¹ * B t :=
                        mul_le_mul_of_nonneg_right (inv_anti₀ ht ht') (hB0 t)
                    _ ≤ _ := mul_le_mul_of_nonneg_left hb (inv_nonneg.2 ht.le)
              have hlow : (∃ S, D.Cond18 S) → ∃ v : ℝ≥0 → ℝ, Tendsto v atTop (𝓝 (lam * g)) ∧
                  ∀ᶠ t in atTop, v t ≤ H D.input t := by
                rintro ⟨S, h18⟩
                have hMt := hcountT (fun n => D.T n + U S n) (hVmono S) (hVtend S) (hV0 S)
                have hMf := hcount (fun n => D.T n + U S n) (hVmono S) (hVtend S) (hV0 S)
                have hV1 : Tendsto (fun m : ℕ => (((D.T (m+1) + U S (m+1) : ℝ≥0) : ℝ) / ((m:ℝ)+1))⁻¹)
                    atTop (𝓝 lam) := by
                  have := ((hVlim S h18 hT).comp (tendsto_add_atTop_nat 1)).inv₀ (inv_ne_zero hlam.ne')
                  rw [inv_inv] at this
                  refine this.congr (fun m => ?_)
                  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
                have hE := h18.2
                have hlim := (hV1.mul (tendsto_natCast_div_add_atTop (1:ℝ))).mul (hAn.sub hE)
                rw [mul_one, sub_zero] at hlim
                refine ⟨fun t => _, hlim.comp hMt, ?_⟩
                filter_upwards [hMt.eventually (eventually_gt_atTop 0), eventually_gt_atTop 0] with t hm ht
                obtain ⟨h1, h2, -⟩ := hMf t
                simp only [Function.comp_apply]
                generalize sSup {k | D.T k + U S k ≤ t} = m at hm h1 h2 ⊢
                have ht0 : (0:ℝ) < t := ht
                have hV : (t:ℝ) ≤ ((D.T (m+1) + U S (m+1) : ℝ≥0) : ℝ) := h2.le
                have hVp : (0:ℝ) < ((D.T (m+1) + U S (m+1) : ℝ≥0) : ℝ) := lt_of_lt_of_le ht0 hV
                have e : (((D.T (m+1) + U S (m+1) : ℝ≥0) : ℝ) / ((m:ℝ)+1))⁻¹ * ((m:ℝ) / ((m:ℝ) + 1)) *
                    ((m:ℝ)⁻¹ * A m - (m:ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 m, (D.Finf k - D.F k (D.T k + S k))) =
                    (((D.T (m+1) + U S (m+1) : ℝ≥0) : ℝ))⁻¹ *
                      (A m - ∑ k ∈ Finset.Icc 1 m, (D.Finf k - D.F k (D.T k + S k))) := by
                  have : (m:ℝ) ≠ 0 := by positivity
                  have : (m:ℝ) + 1 ≠ 0 := by positivity
                  field_simp
                rw [e, hH]
                calc _ ≤ ((t:ℝ))⁻¹ * (A m - ∑ k ∈ Finset.Icc 1 m, (D.Finf k - D.F k (D.T k + S k))) :=
                      mul_le_mul_of_nonneg_right (inv_anti₀ ht0 hV) (hlowV0 S m)
                  _ ≤ ((t:ℝ))⁻¹ * ∑ k ∈ Finset.Icc 1 m, D.F k t :=
                      mul_le_mul_of_nonneg_left (hlowV S m t h1) (inv_nonneg.2 ht0.le)
                  _ ≤ _ := mul_le_mul_of_nonneg_left (hsumB m t) (inv_nonneg.2 ht0.le)
              refine ⟨fun h17 => ?_, fun hS => ?_, fun h17 hS => ?_⟩
              · obtain ⟨u, hu, hle⟩ := hup h17
                unfold limsupE
                calc limsup (fun t => ((H D.input t : ℝ) : EReal)) atTop
                    ≤ limsup (fun t => ((u t : ℝ) : EReal)) atTop :=
                      limsup_le_limsup (hle.mono fun t ht => EReal.coe_le_coe_iff.2 ht)
                  _ = _ := ((continuous_coe_real_ereal.tendsto _).comp hu).limsup_eq
              · obtain ⟨v, hv, hle⟩ := hlow hS
                unfold liminfE
                calc ((lam * g : ℝ) : EReal) = liminf (fun t => ((v t : ℝ) : EReal)) atTop :=
                      (((continuous_coe_real_ereal.tendsto _).comp hv).liminf_eq).symm
                  _ ≤ _ := liminf_le_liminf (hle.mono fun t ht => EReal.coe_le_coe_iff.2 ht)
              · obtain ⟨u, hu, hle⟩ := hup h17
                obtain ⟨v, hv, hle'⟩ := hlow hS
                exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hv hu hle' hle
            · have hTn : Tendsto (fun n : ℕ => (D.T n : ℝ) / (n : ℝ)) atTop (𝓝 lam⁻¹) := by
                have hsub : Tendsto (fun n => D.T n - 1) atTop atTop :=
                  tendsto_atTop.2 fun b => (tendsto_atTop.1 D.T_tendsto (b+1)).mono
                    fun n hn => le_tsub_of_add_le_right hn
                have hup1 : Tendsto (fun n : ℕ => (D.N (D.T n) : ℝ) / (D.T n : ℝ)) atTop (𝓝 lam) :=
                  hN.comp D.T_tendsto
                have hlo1 : Tendsto (fun n : ℕ => (D.N (D.T n - 1) : ℝ) / ((D.T n - 1 : ℝ≥0) : ℝ) *
                    (((D.T n - 1 : ℝ≥0) : ℝ) / (D.T n : ℝ))) atTop (𝓝 lam) := by
                  have h1 : Tendsto (fun n : ℕ => (D.N (D.T n - 1) : ℝ) / ((D.T n - 1 : ℝ≥0) : ℝ))
                      atTop (𝓝 lam) := hN.comp hsub
                  have h2 : Tendsto (fun n : ℕ => ((D.T n - 1 : ℝ≥0) : ℝ) / (D.T n : ℝ)) atTop (𝓝 1) := by
                    have := (tendsto_const_nhds (x := (1:ℝ))).sub (tendsto_inv_atTop_zero.comp hTr)
                    rw [sub_zero] at this
                    refine this.congr' ?_
                    filter_upwards [hTr.eventually_ge_atTop 1] with n hn
                    simp only [Function.comp_apply]
                    rw [NNReal.coe_sub (by exact_mod_cast hn : (1:ℝ≥0) ≤ D.T n)]
                    have : (D.T n : ℝ) ≠ 0 := by positivity
                    push_cast
                    field_simp
                  have := h1.mul h2
                  rwa [mul_one] at this
                have hinv : Tendsto (fun n : ℕ => (n : ℝ) / (D.T n : ℝ)) atTop (𝓝 lam) := by
                  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo1 hup1 ?_ ?_
                  · filter_upwards [hTr.eventually_gt_atTop 1] with n hn
                    have hT1 : (1:ℝ≥0) ≤ D.T n := by exact_mod_cast hn.le
                    have hpos : (0:ℝ) < ((D.T n - 1 : ℝ≥0) : ℝ) := by
                      rw [NNReal.coe_sub hT1]; push_cast; linarith
                    have hlt : D.N (D.T n - 1) < n := by
                      obtain ⟨h1, -, -⟩ := hNfacts (D.T n - 1)
                      by_contra hc
                      push_neg at hc
                      have h3 := D.T_mono hc
                      have h4 : D.T n - 1 < D.T n :=
                        tsub_lt_self (by exact_mod_cast (by linarith : (0:ℝ) < D.T n)) one_pos
                      exact absurd (le_trans h3 h1) (not_le.2 h4)
                    rw [div_mul_div_cancel₀ hpos.ne']
                    exact div_le_div_of_nonneg_right (by exact_mod_cast hlt.le) (by positivity)
                  · filter_upwards [hTpos] with n hn
                    exact div_le_div_of_nonneg_right
                      (by exact_mod_cast (hNfacts (D.T n)).2.2 n le_rfl) hn.le
                have := hinv.inv₀ hlam.ne'
                refine this.congr (fun n => ?_)
                rw [inv_div]
              have hlowG : D.Cond17 → ∃ w : ℕ → ℝ, Tendsto w atTop (𝓝 (lam⁻¹ * h)) ∧
                  ∀ᶠ n in atTop, w n ≤ G D.input (n : ℝ≥0) := by
                intro h17
                unfold DiscreteSetting.Cond17 at h17
                refine ⟨fun n => (D.T n : ℝ) / n * H D.input (D.T n) - (n:ℝ)⁻¹ * R n (D.T n), ?_, ?_⟩
                · have h17' : Tendsto (fun n : ℕ => (n:ℝ)⁻¹ * R n (D.T n)) atTop (𝓝 0) :=
                    h17.congr (fun n => by rw [hRdef])
                  have := (hTn.mul (hHh.comp D.T_tendsto)).sub h17'
                  rw [sub_zero] at this
                  exact this
                · filter_upwards [hTpos, eventually_gt_atTop 0] with n hn hn0
                  rw [hG, hH, hsplit n (D.T n)]
                  have hs := hsumA n (D.T n)
                  have : (n:ℝ) ≠ 0 := by positivity
                  have e : (D.T n : ℝ) / n * ((D.T n : ℝ)⁻¹ * (∑ k ∈ Finset.Icc 1 n, D.F k (D.T n) +
                      R n (D.T n))) - (n:ℝ)⁻¹ * R n (D.T n) =
                      (n:ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 n, D.F k (D.T n) := by
                    field_simp
                    ring
                  rw [e]
                  exact mul_le_mul_of_nonneg_left hs (by positivity)
              have hupG : (∃ S, D.Cond18 S) → ∃ z : ℕ → ℝ, Tendsto z atTop (𝓝 (lam⁻¹ * h)) ∧
                  ∀ᶠ n : ℕ in atTop, G D.input (n : ℝ≥0) ≤ z n := by
                rintro ⟨S, h18⟩
                refine ⟨fun n => ((D.T n + U S n : ℝ≥0) : ℝ) / n * H D.input (D.T n + U S n) +
                  (n:ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 n, (D.Finf k - D.F k (D.T k + S k)), ?_, ?_⟩
                · have := ((hVlim S h18 hTn).mul (hHh.comp (hVtend S))).add h18.2
                  rw [add_zero] at this
                  exact this
                · filter_upwards [hTpos, eventually_gt_atTop 0] with n hn hn0
                  rw [hG, hH]
                  have hV : (0:ℝ) < ((D.T n + U S n : ℝ≥0) : ℝ) := by
                    push_cast; linarith [(U S n).2]
                  have h1 := hlowV S n (D.T n + U S n) le_rfl
                  have h2 := hsumB n (D.T n + U S n)
                  have : (n:ℝ) ≠ 0 := by positivity
                  have e : ((D.T n + U S n : ℝ≥0) : ℝ) / n * (((D.T n + U S n : ℝ≥0) : ℝ)⁻¹ *
                      B (D.T n + U S n)) + (n:ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 n, (D.Finf k - D.F k (D.T k + S k))
                      = (n:ℝ)⁻¹ * (B (D.T n + U S n) +
                        ∑ k ∈ Finset.Icc 1 n, (D.Finf k - D.F k (D.T k + S k))) := by
                    field_simp
                  rw [e]
                  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
              refine ⟨fun h17 => ?_, fun hS => ?_, fun h17 hS => ?_⟩
              · obtain ⟨w, hw, hle⟩ := hlowG h17
                calc ((lam⁻¹ * h : ℝ) : EReal) = liminf (fun n : ℕ => ((w n : ℝ) : EReal)) atTop :=
                      (((continuous_coe_real_ereal.tendsto _).comp hw).liminf_eq).symm
                  _ ≤ _ := liminf_le_liminf (hle.mono fun t ht => EReal.coe_le_coe_iff.2 ht)
              · obtain ⟨z, hz, hle⟩ := hupG hS
                calc limsup (fun n : ℕ => ((G D.input (n : ℝ≥0) : ℝ) : EReal)) atTop
                    ≤ limsup (fun n : ℕ => ((z n : ℝ) : EReal)) atTop :=
                      limsup_le_limsup (hle.mono fun t ht => EReal.coe_le_coe_iff.2 ht)
                  _ = _ := ((continuous_coe_real_ereal.tendsto _).comp hz).limsup_eq
              · obtain ⟨w, hw, hle⟩ := hlowG h17
                obtain ⟨z, hz, hle'⟩ := hupG hS
                exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hw hz hle hle'
