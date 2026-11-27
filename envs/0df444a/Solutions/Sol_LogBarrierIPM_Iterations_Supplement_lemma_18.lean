-- Prove2me | solution 1 for LogBarrierIPM.Iterations.Supplement.lemma_18
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:04:41.139971+00:00
-- url     : https://prove2.me/submissions/a836c1ce-53d8-4594-bdb5-79da6a69beeb

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_Supplement_Specialization

open Filter Matrix

open LogBarrierIPM
open LogBarrierIPM.Iterations
open LogBarrierIPM.Iterations.Supplement

open LogBarrierIPM.Curvature

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux)
    (b : Fin m → Puiseux) (c : Fin n → Puiseux)
    (hstrict : StrictlyFeasibleK A b c)
    (zstar : PuiseuxSlackPoint n m) (hopt : OptimalPairK A b c zstar) :
    ∃ t0 : ℝ, SpecializationThreshold A b c zstar t0 := by
      classical
      -- valuation structure
      have VAL : ∀ f : Puiseux, ((∀ α, f.coeff α = 0) ∧ f.val = ⊥) ∨
          ∃ m, f.coeff m ≠ 0 ∧ (∀ α, f.coeff α ≠ 0 → α ≤ m) ∧ f.val = (m : WithBot ℝ) := by
        intro f
        by_cases hne : (Function.support f.coeff).Nonempty
        · right
          obtain ⟨α0, h0⟩ := hne
          have hfin := f.support_finite_above α0
          have hS : hfin.toFinset.Nonempty := ⟨α0, by simp [hfin.mem_toFinset]; exact h0⟩
          obtain ⟨m, hm, hmax⟩ := hfin.toFinset.exists_max_image id hS
          rw [hfin.mem_toFinset] at hm
          have hub : ∀ α, f.coeff α ≠ 0 → α ≤ m := by
            intro α hα
            by_cases h : α0 ≤ α
            · exact hmax α ((hfin.mem_toFinset).2 ⟨h, hα⟩)
            · linarith [hm.1]
          refine ⟨m, hm.2, hub, ?_⟩
          unfold Puiseux.val
          rw [if_pos ⟨α0, h0⟩]
          congr 1
          exact IsGreatest.csSup_eq ⟨hm.2, fun α hα => hub α hα⟩
        · left
          have hz : ∀ α, f.coeff α = 0 := by
            intro α; by_contra h; exact hne ⟨α, h⟩
          refine ⟨hz, ?_⟩
          unfold Puiseux.val
          rw [if_neg hne]
      have Z : ∀ f : Puiseux, (∀ α, f.coeff α = 0) → ∀ t, f.eval t = 0 := by
        intro f hf t
        unfold Puiseux.eval
        simp [hf]
      have MON : ∀ c r : ℝ, ∃ p : Puiseux, (∀ α, p.coeff α = if α = r then c else 0) ∧
          ∀ t, p.eval t = c * t ^ r := by
        intro c r
        refine ⟨⟨fun α => if α = r then c else 0, ?_, ?_⟩, fun α => rfl, ?_⟩
        · intro c'
          apply (Set.finite_singleton r).subset
          intro α hα
          simp only [Set.mem_ofPred_eq] at hα
          by_contra h
          exact hα.2 (if_neg h)
        · refine ⟨1, one_pos, fun t _ => ?_⟩
          apply summable_of_ne_finset_zero (s := {r})
          intro α hα
          simp at hα
          simp [hα]
        · intro t
          unfold Puiseux.eval
          simp only
          rw [tsum_eq_single r]
          · simp
          · intro α hα; simp [hα]
      have MONval : ∀ (p : Puiseux) (c r : ℝ), (∀ α, p.coeff α = if α = r then c else 0) → c ≠ 0 →
          p.val = (r : WithBot ℝ) := by
        intro p c r hp hc
        rcases VAL p with ⟨hz, _⟩ | ⟨m, hm, hub, hv⟩
        · have := hz r; rw [hp, if_pos rfl] at this; exact absurd this hc
        · rw [hv]
          have : m = r := by
            by_contra h; exact hm (by rw [hp, if_neg h])
          rw [this]
      -- dominated convergence for tails
      have DC : ∀ (w : ℝ → ℝ) (a ρ : ℝ), 0 < ρ → (∀ t, ρ < t → Summable fun α => |w α| * t ^ α) →
          (∀ α, w α ≠ 0 → α < a) →
          Tendsto (fun t : ℝ => ∑' α, |w α| * t ^ (α - a)) atTop (nhds 0) := by
        intro w a ρ hρ hs hlt
        have ht0 : 0 < ρ + 1 := by linarith
        have hsum : Summable fun α => |w α| * (ρ + 1) ^ (α - a) := by
          have := (hs (ρ + 1) (by linarith)).mul_right (((ρ + 1) ^ a)⁻¹)
          refine this.congr (fun α => ?_)
          rw [Real.rpow_sub ht0]; ring
        have h0 : (0 : ℝ) = ∑' α : ℝ, (0 : ℝ) := by simp
        rw [h0]
        apply tendsto_tsum_of_dominated_convergence hsum
        · intro α
          by_cases hw : w α = 0
          · simp [hw]
          · have hlt' : 0 < a - α := by linarith [hlt α hw]
            have := (tendsto_rpow_neg_atTop hlt').const_mul (|w α|)
            simp only [mul_zero, neg_sub] at this
            exact this
        · filter_upwards [eventually_ge_atTop (ρ + 1)] with t ht α
          rw [Real.norm_eq_abs, abs_mul, abs_abs]
          by_cases hw : w α = 0
          · simp [hw]
          · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            rw [abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]
            exact Real.rpow_le_rpow_of_nonpos ht0 ht (by linarith [hlt α hw])
      have SUMM : ∀ (w : ℝ → ℝ) (t : ℝ), 0 < t → Summable (fun α => |w α| * t ^ α) →
          Summable (fun α => w α * t ^ α) := by
        intro w t ht hs
        refine Summable.of_norm (hs.congr fun α => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht _)]
      have LEAD : ∀ (f : Puiseux) (m : ℝ), f.coeff m ≠ 0 → (∀ α, f.coeff α ≠ 0 → α ≤ m) →
          ∀ ε > 0, ∀ᶠ t in atTop, |f.eval t - f.coeff m * t ^ m| ≤ ε * t ^ m := by
        intro f m hm hub ε hε
        obtain ⟨ρ, hρ, hs⟩ := f.abs_summable
        set w : ℝ → ℝ := fun α => if α = m then 0 else f.coeff α with hw
        have hws : ∀ t, ρ < t → Summable fun α => |w α| * t ^ α := by
          intro t ht
          refine (hs t ht).of_nonneg_of_le (fun α => mul_nonneg (abs_nonneg _)
            (Real.rpow_nonneg (by linarith) _)) (fun α => ?_)
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
          simp only [hw]; split_ifs <;> simp
        have hlt : ∀ α, w α ≠ 0 → α < m := by
          intro α hα
          simp only [hw] at hα
          split_ifs at hα with h
          · exact absurd rfl hα
          · exact lt_of_le_of_ne (hub α hα) h
        have hT := DC w m ρ hρ hws hlt
        filter_upwards [hT.eventually (gt_mem_nhds hε), eventually_gt_atTop ρ] with t h1 ht
        have htp : 0 < t := by linarith
        have hfs := SUMM f.coeff t htp (hs t ht)
        have e1 : f.eval t = f.coeff m * t ^ m + ∑' α, w α * t ^ α := by
          unfold Puiseux.eval
          rw [hfs.tsum_eq_add_tsum_ite m]
          congr 1
          apply tsum_congr; intro α; simp only [hw]; split_ifs <;> simp
        rw [e1, add_sub_cancel_left]
        have e2 : ∑' α, |w α| * t ^ α = t ^ m * ∑' α, |w α| * t ^ (α - m) := by
          rw [← tsum_mul_left]
          apply tsum_congr; intro α
          rw [Real.rpow_sub htp]
          have : 0 < t ^ m := Real.rpow_pos_of_pos htp _
          field_simp
        calc |∑' α, w α * t ^ α| ≤ ∑' α, ‖w α * t ^ α‖ := by
              rw [← Real.norm_eq_abs]
              apply norm_tsum_le_tsum_norm
              refine (hws t ht).congr fun α => ?_
              rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos htp _)]
          _ = ∑' α, |w α| * t ^ α := by
              apply tsum_congr; intro α
              rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos htp _)]
          _ = t ^ m * ∑' α, |w α| * t ^ (α - m) := e2
          _ ≤ t ^ m * ε := by
              apply mul_le_mul_of_nonneg_left (le_of_lt h1) (Real.rpow_nonneg htp.le _)
          _ = ε * t ^ m := by ring
      have POS : ∀ (f : Puiseux) (m : ℝ), KNonneg f → f.coeff m ≠ 0 →
          (∀ α, f.coeff α ≠ 0 → α ≤ m) → 0 < f.coeff m := by
        intro f m hf hm hub
        by_contra hneg
        have hc : f.coeff m < 0 := lt_of_le_of_ne (not_lt.1 hneg) hm
        obtain ⟨t, h1, h2, h3⟩ := ((LEAD f m hm hub (-(f.coeff m) / 2) (by linarith)).and
          (hf.and (eventually_gt_atTop 0))).exists
        have hp : 0 < t ^ m := Real.rpow_pos_of_pos h3 _
        have := (abs_le.1 h1).2
        linarith [mul_neg_of_neg_of_pos hc hp]
      have TH : ∀ (f : Puiseux) (m : ℝ), KNonneg f → f.coeff m ≠ 0 →
          (∀ α, f.coeff α ≠ 0 → α ≤ m) →
          ∀ᶠ t in atTop, f.coeff m / 2 * t ^ m ≤ f.eval t ∧ f.eval t ≤ 2 * f.coeff m * t ^ m := by
        intro f m hf hm hub
        have hc := POS f m hf hm hub
        filter_upwards [LEAD f m hm hub (f.coeff m / 2) (by linarith), eventually_gt_atTop 0]
          with t h1 h3
        have hp : 0 < t ^ m := Real.rpow_pos_of_pos h3 _
        have := abs_le.1 h1
        have hcp := mul_pos hc hp
        constructor <;> linarith [this.1, this.2]
      have P1 : ∀ f g : Puiseux, KNonneg f → KNonneg g → KLe f g → f.val ≤ g.val := by
        intro f g hf hg hfg
        rcases VAL f with ⟨hz, hv⟩ | ⟨m, hm, hub, hv⟩
        · rw [hv]; exact bot_le
        have hc := POS f m hf hm hub
        rcases VAL g with ⟨hz', hv'⟩ | ⟨m', hm', hub', hv'⟩
        · exfalso
          obtain ⟨t, h1, h2, h3⟩ := ((TH f m hf hm hub).and (hfg.and (eventually_gt_atTop 0))).exists
          have hp : 0 < t ^ m := Real.rpow_pos_of_pos h3 _
          rw [Z g hz' t] at h2
          linarith [h1.1, mul_pos hc hp]
        rw [hv, hv', WithBot.coe_le_coe]
        by_contra hlt
        push Not at hlt
        have hc' := POS g m' hg hm' hub'
        have hT : Tendsto (fun t : ℝ => t ^ (-(m - m'))) atTop (nhds 0) :=
          tendsto_rpow_neg_atTop (by linarith)
        have hev := hT.eventually (gt_mem_nhds (show (0:ℝ) < f.coeff m / (4 * g.coeff m') by positivity))
        obtain ⟨t, h1, h2, h3, h4, h5⟩ := ((TH f m hf hm hub).and ((TH g m' hg hm' hub').and
          (hfg.and (hev.and (eventually_gt_atTop 0))))).exists
        have hp : 0 < t ^ m' := Real.rpow_pos_of_pos h5 _
        have hpm : 0 < t ^ m := Real.rpow_pos_of_pos h5 _
        have e : t ^ m' = t ^ (-(m - m')) * t ^ m := by
          rw [← Real.rpow_add h5]; ring_nf
        have hc4 : 0 < 4 * g.coeff m' := by linarith
        have h4' : t ^ (-(m - m')) * (4 * g.coeff m') < f.coeff m := by
          rwa [lt_div_iff₀ hc4] at h4
        have : 2 * g.coeff m' * t ^ m' < f.coeff m / 2 * t ^ m := by
          have := mul_lt_mul_of_pos_right h4' hpm
          rw [e]; linarith
        linarith [h1.1, h2.2]
      have VZ : ∀ f : Puiseux, f.val = ⊥ → ∀ t, f.eval t = 0 := by
        intro f hf
        rcases VAL f with ⟨hz, _⟩ | ⟨m, _, _, hv⟩
        · exact Z f hz
        · rw [hv] at hf; exact absurd hf (WithBot.coe_ne_bot)
      have WB : ∀ x : WithBot ℝ, x = ⊥ ∨ ∃ M : ℝ, x = ↑M := by
        intro x; induction x using WithBot.recBotCoe <;> simp
      have MONP : ∀ c r : ℝ, 0 < c → ∃ p : Puiseux, KNonneg p ∧ p.val = (r : WithBot ℝ) ∧
          ∀ t, p.eval t = c * t ^ r := by
        intro c r hc
        obtain ⟨p, hp, he⟩ := MON c r
        refine ⟨p, ?_, MONval p c r hp hc.ne', he⟩
        filter_upwards [eventually_ge_atTop 0] with t ht
        rw [he]; exact mul_nonneg hc.le (Real.rpow_nonneg ht _)
      obtain ⟨z0, hz0c, hz0v⟩ : ∃ z : Puiseux, (∀ a, z.coeff a = 0) ∧ z.val = ⊥ := by
        obtain ⟨p, hp, _⟩ := MON 0 0
        have hz : ∀ a, p.coeff a = 0 := fun a => by rw [hp]; split_ifs <;> rfl
        refine ⟨p, hz, ?_⟩
        rcases VAL p with ⟨_, hv⟩ | ⟨m, hm, _, _⟩
        · exact hv
        · exact absurd (hz m) hm
      have VB : ∀ h : Puiseux, (∀ᶠ t in atTop, h.eval t = 0) → h.val = ⊥ := by
        intro h hh
        have := P1 h z0 (by filter_upwards [hh] with t ht; rw [ht])
          (Filter.Eventually.of_forall fun t => by rw [Z z0 hz0c t])
          (by filter_upwards [hh] with t ht; rw [ht, Z z0 hz0c t])
        rw [hz0v] at this
        exact le_bot_iff.1 this
      have UB : ∀ f : Puiseux, KNonneg f → ∀ M : ℝ, f.val ≤ (M : WithBot ℝ) →
          ∃ C > 0, ∀ᶠ t in atTop, f.eval t ≤ C * t ^ M := by
        intro f hf M hM
        rcases VAL f with ⟨hz, _⟩ | ⟨m, hm, hub, hv⟩
        · refine ⟨1, one_pos, ?_⟩
          filter_upwards [eventually_gt_atTop 0] with t ht
          rw [Z f hz t]; exact mul_nonneg zero_le_one (Real.rpow_nonneg ht.le _)
        · rw [hv, WithBot.coe_le_coe] at hM
          have hc := POS f m hf hm hub
          refine ⟨2 * f.coeff m, by linarith, ?_⟩
          filter_upwards [TH f m hf hm hub, eventually_ge_atTop 1] with t h1 ht
          have := Real.rpow_le_rpow_of_exponent_le ht hM
          linarith [h1.2, mul_le_mul_of_nonneg_left this (by linarith : (0:ℝ) ≤ 2 * f.coeff m)]
      have LB : ∀ f : Puiseux, KNonneg f → ∀ m : ℝ, f.val = (m : WithBot ℝ) →
          ∃ c > 0, ∀ᶠ t in atTop, c / 2 * t ^ m ≤ f.eval t ∧ f.eval t ≤ 2 * c * t ^ m := by
        intro f hf m hM
        rcases VAL f with ⟨_, hv⟩ | ⟨m', hm, hub, hv⟩
        · rw [hv] at hM; exact absurd hM.symm WithBot.coe_ne_bot
        · rw [hv, WithBot.coe_inj] at hM
          subst hM
          exact ⟨f.coeff m', POS f m' hf hm hub, TH f m' hf hm hub⟩
      have ADDU : ∀ f g : Puiseux, KNonneg f → KNonneg g →
          ∀ h : Puiseux, (∀ᶠ t in atTop, h.eval t = f.eval t + g.eval t) →
            KNonneg h ∧ h.val = max f.val g.val := by
        intro f g hf hg h hh
        have hn : KNonneg h := by
          filter_upwards [hh, hf, hg] with t h1 h2 h3; rw [h1]; linarith
        refine ⟨hn, le_antisymm ?_ ?_⟩
        · rcases WB (max f.val g.val) with hb | ⟨M, hM⟩
          · rw [hb]
            have h1 := VZ f (max_eq_bot.1 hb).1
            have h2 := VZ g (max_eq_bot.1 hb).2
            rw [VB h (by filter_upwards [hh] with t ht; rw [ht, h1, h2]; simp)]
          · rw [hM]
            obtain ⟨C1, hC1, hu1⟩ := UB f hf M (hM ▸ le_max_left _ _)
            obtain ⟨C2, hC2, hu2⟩ := UB g hg M (hM ▸ le_max_right _ _)
            obtain ⟨p, hpn, hpv, hpe⟩ := MONP (C1 + C2) M (by linarith)
            rw [← hpv]
            apply P1 h p hn hpn
            filter_upwards [hh, hu1, hu2] with t h1 h2 h3
            rw [h1, hpe]; linarith
        · apply max_le
          · apply P1 f h hf hn
            filter_upwards [hh, hg] with t h1 h2; rw [h1]; linarith
          · apply P1 g h hg hn
            filter_upwards [hh, hf] with t h1 h2; rw [h1]; linarith
      have MULU : ∀ f g : Puiseux, KNonneg f → KNonneg g →
          ∀ h : Puiseux, (∀ᶠ t in atTop, h.eval t = f.eval t * g.eval t) →
            KNonneg h ∧ h.val = f.val + g.val := by
        intro f g hf hg h hh
        have hn : KNonneg h := by
          filter_upwards [hh, hf, hg] with t h1 h2 h3; rw [h1]; exact mul_nonneg h2 h3
        refine ⟨hn, ?_⟩
        rcases WB f.val with hb | ⟨m, hm⟩
        · rw [hb, WithBot.bot_add]
          exact VB h (by filter_upwards [hh] with t ht; rw [ht, VZ f hb]; simp)
        rcases WB g.val with hb | ⟨m', hm'⟩
        · rw [hb, WithBot.add_bot]
          exact VB h (by filter_upwards [hh] with t ht; rw [ht, VZ g hb]; simp)
        obtain ⟨c, hc, h1⟩ := LB f hf m hm
        obtain ⟨c', hc', h2⟩ := LB g hg m' hm'
        rw [hm, hm', ← WithBot.coe_add]
        apply le_antisymm
        · obtain ⟨p, hpn, hpv, hpe⟩ := MONP (2 * c * (2 * c')) (m + m') (by positivity)
          rw [← hpv]
          apply P1 h p hn hpn
          filter_upwards [hh, h1, h2, eventually_gt_atTop 0] with t e h3 h4 ht
          rw [e, hpe, Real.rpow_add ht]
          have := Real.rpow_pos_of_pos ht m
          have := Real.rpow_pos_of_pos ht m'
          calc f.eval t * g.eval t ≤ (2 * c * t ^ m) * (2 * c' * t ^ m') :=
                mul_le_mul h3.2 h4.2 (le_trans (by positivity) h4.1) (by positivity)
            _ = _ := by ring
        · obtain ⟨p, hpn, hpv, hpe⟩ := MONP (c / 2 * (c' / 2)) (m + m') (by positivity)
          rw [← hpv]
          apply P1 p h hpn hn
          filter_upwards [hh, h1, h2, eventually_gt_atTop 0] with t e h3 h4 ht
          rw [e, hpe, Real.rpow_add ht]
          have := Real.rpow_pos_of_pos ht m
          have := Real.rpow_pos_of_pos ht m'
          calc c / 2 * (c' / 2) * (t ^ m * t ^ m') = (c / 2 * t ^ m) * (c' / 2 * t ^ m') := by ring
            _ ≤ f.eval t * g.eval t :=
                mul_le_mul h3.1 h4.1 (by positivity) (le_trans (by positivity) h3.1)
      have ADDE : ∀ f g : Puiseux, ∃ h : Puiseux, ∀ᶠ t in atTop, h.eval t = f.eval t + g.eval t := by
        intro f g
        obtain ⟨ρf, hρf, hsf⟩ := f.abs_summable
        obtain ⟨ρg, hρg, hsg⟩ := g.abs_summable
        have hs : ∀ t, max ρf ρg < t → Summable fun α => |f.coeff α + g.coeff α| * t ^ α := by
          intro t ht
          have ht1 : ρf < t := lt_of_le_of_lt (le_max_left _ _) ht
          have ht2 : ρg < t := lt_of_le_of_lt (le_max_right _ _) ht
          refine ((hsf t ht1).add (hsg t ht2)).of_nonneg_of_le (fun α => mul_nonneg (abs_nonneg _)
            (Real.rpow_nonneg (by linarith) _)) (fun α => ?_)
          rw [← add_mul]
          exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (Real.rpow_nonneg (by linarith) _)
        let h : Puiseux := ⟨fun α => f.coeff α + g.coeff α, fun c => by
            apply ((f.support_finite_above c).union (g.support_finite_above c)).subset
            intro α hα
            simp only [Set.mem_ofPred_eq] at hα
            by_cases h1 : f.coeff α = 0
            · right; refine ⟨hα.1, ?_⟩; intro h2; apply hα.2; rw [h1, h2]; simp
            · left; exact ⟨hα.1, h1⟩,
          ⟨max ρf ρg, lt_max_of_lt_left hρf, hs⟩⟩
        refine ⟨h, ?_⟩
        filter_upwards [eventually_gt_atTop (max ρf ρg)] with t ht
        have ht1 : ρf < t := lt_of_le_of_lt (le_max_left _ _) ht
        have ht2 : ρg < t := lt_of_le_of_lt (le_max_right _ _) ht
        have htp : 0 < t := by linarith
        unfold Puiseux.eval
        rw [← (SUMM f.coeff t htp (hsf t ht1)).tsum_add (SUMM g.coeff t htp (hsg t ht2))]
        apply tsum_congr; intro α; simp only [h]; ring
      have BDD : ∀ f : Puiseux, ∃ A, ∀ α, f.coeff α ≠ 0 → α ≤ A := by
        intro f
        rcases VAL f with ⟨hz, _⟩ | ⟨m, _, hub, _⟩
        · exact ⟨0, fun α hα => absurd (hz α) hα⟩
        · exact ⟨m, hub⟩
      have PUSH : ∀ {ι : Type} (F e : ι → ℝ), (∀ c, {i | c ≤ e i ∧ F i ≠ 0}.Finite) →
          (∃ ρ > 0, ∀ t, ρ < t → Summable fun i => |F i| * t ^ e i) →
          ∃ h : Puiseux, (∀ γ, h.coeff γ ≠ 0 → ∃ i, e i = γ ∧ F i ≠ 0) ∧
            ∀ t, 0 < t → Summable (fun i => |F i| * t ^ e i) →
              Summable (fun γ => |h.coeff γ| * t ^ γ) ∧
              ∑' γ, |h.coeff γ| * t ^ γ ≤ ∑' i, |F i| * t ^ e i ∧
              h.eval t = ∑' i, F i * t ^ e i := by
        intro ι F e hfin hsρ
        obtain ⟨ρ, hρ, hs⟩ := hsρ
        set cf : ℝ → ℝ := fun γ => ∑' i : ↑(e ⁻¹' {γ}), F i with hcf
        have key : ∀ t, 0 < t → Summable (fun i => |F i| * t ^ e i) →
            Summable (fun γ => |cf γ| * t ^ γ) ∧
            ∑' γ, |cf γ| * t ^ γ ≤ ∑' i, |F i| * t ^ e i ∧
            ∑' γ, cf γ * t ^ γ = ∑' i, F i * t ^ e i := by
          intro t ht hsum
          have hK : Summable fun i => F i * t ^ e i := by
            refine Summable.of_norm (hsum.congr fun i => ?_)
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht _)]
          have hGf := hsum.hasSum.tsum_fiberwise e
          have hKf := hK.hasSum.tsum_fiberwise e
          have hfib : ∀ γ, ∑' i : ↑(e ⁻¹' {γ}), F i * t ^ e i = cf γ * t ^ γ := by
            intro γ
            simp only [hcf]
            rw [← tsum_mul_right]
            apply tsum_congr; intro i
            have := i.2
            simp only [Set.mem_preimage, Set.mem_singleton_iff] at this
            rw [this]
          have hle : ∀ γ, |cf γ| * t ^ γ ≤ ∑' i : ↑(e ⁻¹' {γ}), |F i| * t ^ e i := by
            intro γ
            have e0 : |cf γ| * t ^ γ = ‖cf γ * t ^ γ‖ := by
              rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht _)]
            rw [e0, ← hfib γ]
            refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
            · refine (hsum.subtype _).congr fun i => ?_
              rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht _)]; rfl
            · apply tsum_congr; intro i
              rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht _)]
          have hsm : Summable (fun γ => |cf γ| * t ^ γ) :=
            hGf.summable.of_nonneg_of_le (fun γ => mul_nonneg (abs_nonneg _)
              (Real.rpow_nonneg ht.le _)) hle
          refine ⟨hsm, ?_, ?_⟩
          · rw [← hGf.tsum_eq]
            exact hsm.tsum_le_tsum hle hGf.summable
          · rw [← hKf.tsum_eq]
            apply tsum_congr; intro γ; rw [hfib γ]
        let h : Puiseux := ⟨cf, fun c => by
            apply ((hfin c).image e).subset
            intro γ hγ
            simp only [Set.mem_ofPred_eq] at hγ
            by_contra hcon
            apply hγ.2
            simp only [hcf]
            have : ∀ i : ↑(e ⁻¹' {γ}), F i = 0 := by
              intro i
              by_contra hF
              have := i.2
              simp only [Set.mem_preimage, Set.mem_singleton_iff] at this
              exact hcon ⟨i, ⟨by rw [this]; exact hγ.1, hF⟩, this⟩
            simp [this],
          ⟨ρ, hρ, fun t ht => (key t (by linarith) (hs t ht)).1⟩⟩
        refine ⟨h, ?_, fun t ht hsum => ?_⟩
        · intro γ hγ
          by_contra hcon
          push Not at hcon
          apply hγ
          show cf γ = 0
          simp only [hcf]
          have : ∀ i : ↑(e ⁻¹' {γ}), F i = 0 := by
            intro i
            have := i.2
            simp only [Set.mem_preimage, Set.mem_singleton_iff] at this
            exact hcon i this
          simp [this]
        · obtain ⟨k1, k2, k3⟩ := key t ht hsum
          exact ⟨k1, k2, k3⟩
      have MUL : ∀ f g : Puiseux, ∃ h : Puiseux,
          (∀ γ, h.coeff γ ≠ 0 → ∃ α β, α + β = γ ∧ f.coeff α ≠ 0 ∧ g.coeff β ≠ 0) ∧
          ∀ t, 0 < t → Summable (fun α => |f.coeff α| * t ^ α) →
            Summable (fun β => |g.coeff β| * t ^ β) →
            Summable (fun γ => |h.coeff γ| * t ^ γ) ∧
            ∑' γ, |h.coeff γ| * t ^ γ ≤
              (∑' α, |f.coeff α| * t ^ α) * (∑' β, |g.coeff β| * t ^ β) ∧
            h.eval t = f.eval t * g.eval t := by
        intro f g
        obtain ⟨A, hA⟩ := BDD f
        obtain ⟨B, hB⟩ := BDD g
        obtain ⟨ρf, hρf, hsf⟩ := f.abs_summable
        obtain ⟨ρg, hρg, hsg⟩ := g.abs_summable
        have hprod : ∀ t, 0 < t → Summable (fun α => |f.coeff α| * t ^ α) →
            Summable (fun β => |g.coeff β| * t ^ β) →
            Summable (fun p : ℝ × ℝ => |f.coeff p.1 * g.coeff p.2| * t ^ (p.1 + p.2)) := by
          intro t ht s1 s2
          have := Summable.mul_of_nonneg (f := fun α => |f.coeff α| * t ^ α)
            (g := fun β => |g.coeff β| * t ^ β) s1 s2
            (fun α => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg ht.le _))
            (fun α => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg ht.le _))
          refine this.congr (fun p => ?_)
          rw [abs_mul, Real.rpow_add ht]; ring
        obtain ⟨h, hsupp, hkey⟩ := PUSH (ι := ℝ × ℝ) (fun p => f.coeff p.1 * g.coeff p.2)
          (fun p => p.1 + p.2) (fun c => by
            apply (((f.support_finite_above (c - B))).prod (g.support_finite_above (c - A))).subset
            intro p hp
            simp only [Set.mem_ofPred_eq] at hp
            obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hp.2
            have k1 := hA _ h1
            have k2 := hB _ h2
            have k3 := hp.1
            exact ⟨⟨by linarith only [k1, k2, k3], h1⟩, ⟨by linarith only [k1, k2, k3], h2⟩⟩)
          ⟨max ρf ρg, lt_max_of_lt_left hρf, fun t ht =>
            hprod t (lt_of_le_of_lt (le_max_of_le_left hρf.le) ht)
              (hsf t (lt_of_le_of_lt (le_max_left _ _) ht))
              (hsg t (lt_of_le_of_lt (le_max_right _ _) ht))⟩
        refine ⟨h, fun γ hγ => ?_, fun t ht s1 s2 => ?_⟩
        · obtain ⟨p, hp1, hp2⟩ := hsupp γ hγ
          exact ⟨p.1, p.2, hp1, (mul_ne_zero_iff.1 hp2).1, (mul_ne_zero_iff.1 hp2).2⟩
        · have hps := Summable.mul_of_nonneg (f := fun α => |f.coeff α| * t ^ α)
            (g := fun β => |g.coeff β| * t ^ β) s1 s2
            (fun α => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg ht.le _))
            (fun α => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg ht.le _))
          obtain ⟨k1, k2, k3⟩ := hkey t ht (hprod t ht s1 s2)
          refine ⟨k1, ?_, ?_⟩
          · rw [s1.tsum_mul_tsum s2 hps]
            refine k2.trans (le_of_eq ?_)
            apply tsum_congr; intro p
            rw [abs_mul, Real.rpow_add ht]; ring
          · rw [k3]
            have n1 : Summable fun α => ‖f.coeff α * t ^ α‖ := s1.congr fun α => by
              rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht _)]
            have n2 : Summable fun α => ‖g.coeff α * t ^ α‖ := s2.congr fun α => by
              rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht _)]
            unfold Puiseux.eval
            rw [tsum_mul_tsum_of_summable_norm n1 n2]
            apply tsum_congr; intro p
            rw [Real.rpow_add ht]; ring
      have INV : ∀ f : Puiseux, KPositive f → ∃ h : Puiseux, ∀ᶠ t in atTop, f.eval t * h.eval t = 1 := by
        intro f hf
        have hfn : KNonneg f := hf.mono (fun t ht => ht.le)
        rcases VAL f with ⟨hz, _⟩ | ⟨m, hm, hub, _⟩
        · exfalso
          obtain ⟨t, h1⟩ := hf.exists
          rw [Z f hz t] at h1; exact lt_irrefl _ h1
        have hc : 0 < f.coeff m := POS f m hfn hm hub
        clear P1 TH LEAD VZ WB MONP VB UB LB ADDU MULU ADDE BDD MONval POS
        set c := f.coeff m with hcdef
        obtain ⟨ρf, hρf, hsf⟩ := f.abs_summable
        have hvs : ∀ t, ρf < t → Summable fun β => |if β = m then 0 else -(f.coeff β / c)| *
            t ^ (β - m) := by
          intro t ht
          have htp : 0 < t := by linarith
          refine ((hsf t ht).mul_right (1 / (c * t ^ m))).of_nonneg_of_le
            (fun β => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg htp.le _)) (fun β => ?_)
          have := Real.rpow_pos_of_pos htp m
          split_ifs with hb
          · simp only [abs_zero, zero_mul]
            exact mul_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg htp.le _)) (by positivity)
          · rw [abs_neg, abs_div, abs_of_pos hc, Real.rpow_sub htp]
            apply le_of_eq; ring
        obtain ⟨v, hvsupp, hvkey⟩ := PUSH (ι := ℝ) (fun β => if β = m then 0 else -(f.coeff β / c))
          (fun β => β - m) (fun c' => by
            apply (f.support_finite_above (c' + m)).subset
            intro β hβ
            simp only [Set.mem_ofPred_eq] at hβ
            split_ifs at hβ with hb
            · exact absurd rfl hβ.2
            · refine ⟨by linarith only [hβ.1], fun h0 => hβ.2 (by rw [h0]; simp)⟩)
          ⟨ρf, hρf, hvs⟩
        have hvneg : ∀ γ, v.coeff γ ≠ 0 → γ < 0 := by
          intro γ hγ
          obtain ⟨β, hβ, hF⟩ := hvsupp γ hγ
          split_ifs at hF with hb
          · exact absurd rfl hF
          · have : f.coeff β ≠ 0 := fun h0 => hF (by rw [h0]; simp)
            have := lt_of_le_of_ne (hub β this) hb
            linarith only [this, hβ]
        obtain ⟨δ, hδ, hδv⟩ : ∃ δ > 0, ∀ γ, v.coeff γ ≠ 0 → γ ≤ -δ := by
          have S := v.support_finite_above (-1)
          by_cases hne : S.toFinset.Nonempty
          · obtain ⟨x0, hx0, hmax⟩ := S.toFinset.exists_max_image id hne
            rw [S.mem_toFinset] at hx0
            have hx0n := hvneg x0 hx0.2
            refine ⟨min 1 (-x0), lt_min one_pos (by linarith only [hx0n]), fun γ hγ => ?_⟩
            by_cases h1 : -1 ≤ γ
            · have := hmax γ (S.mem_toFinset.2 ⟨h1, hγ⟩)
              have := min_le_right 1 (-x0)
              simp only [id] at *
              linarith
            · have := min_le_left 1 (-x0)
              linarith
          · refine ⟨1, one_pos, fun γ hγ => ?_⟩
            by_contra h1
            exact hne ⟨γ, S.mem_toFinset.2 ⟨by linarith, hγ⟩⟩
        obtain ⟨ρv, hρv, hsv⟩ := v.abs_summable
        have hV := DC v.coeff 0 ρv hρv hsv (fun γ h => hvneg γ h)
        obtain ⟨T, hT⟩ := eventually_atTop.1 (hV.eventually (gt_mem_nhds (one_half_pos (α := ℝ))))
        have hT' : ∀ t ≥ T, ∑' γ, |v.coeff γ| * t ^ γ < 1 / 2 := by
          intro t ht; have := hT t ht; simpa only [sub_zero] using this
        obtain ⟨one, hone, hone_e⟩ := MON 1 0
        choose mul hmul using MUL
        let pw : ℕ → Puiseux := fun n => (fun p => mul p v)^[n] one
        have pw_succ : ∀ n, pw (n + 1) = mul (pw n) v := fun n =>
          Function.iterate_succ_apply' (fun p => mul p v) n one
        have pw0 : pw 0 = one := rfl
        have hsupp_pw : ∀ n : ℕ, ∀ γ, (pw n).coeff γ ≠ 0 → γ ≤ -(n * δ) := by
          intro n
          induction n with
          | zero =>
            intro γ h
            rw [pw0, hone] at h
            split_ifs at h with hg
            · simp [hg]
            · exact absurd rfl h
          | succ n ih =>
            intro γ h
            rw [pw_succ] at h
            obtain ⟨α, β, hab, h1, h2⟩ := (hmul (pw n) v).1 γ h
            have := ih α h1
            have := hδv β h2
            push_cast
            linarith
        have hpw : ∀ t, 0 < t → Summable (fun γ => |v.coeff γ| * t ^ γ) → ∀ n : ℕ,
            Summable (fun γ => |(pw n).coeff γ| * t ^ γ) ∧
            ∑' γ, |(pw n).coeff γ| * t ^ γ ≤ (∑' γ, |v.coeff γ| * t ^ γ) ^ n ∧
            (pw n).eval t = (v.eval t) ^ n := by
          intro t ht hsvt n
          induction n with
          | zero =>
            rw [pw0]
            have e1 : ∀ γ, |one.coeff γ| * t ^ γ = if γ = 0 then 1 else 0 := by
              intro γ; rw [hone]; split_ifs with hg
              · rw [hg]; simp
              · simp
            refine ⟨?_, ?_, ?_⟩
            · refine (summable_of_ne_finset_zero (s := {0}) (fun γ hγ => ?_) :
                Summable fun γ : ℝ => if γ = 0 then (1:ℝ) else 0).congr (fun γ => (e1 γ).symm)
              rw [if_neg (by simpa using hγ)]
            · rw [tsum_congr e1, tsum_ite_eq]; simp
            · rw [hone_e]; simp
          | succ n ih =>
            obtain ⟨a1, a2, a3⟩ := (hmul (pw n) v).2 t ht ih.1 hsvt
            rw [pw_succ]
            refine ⟨a1, a2.trans ?_, by rw [a3, ih.2.2, pow_succ]⟩
            rw [pow_succ]
            exact mul_le_mul_of_nonneg_right ih.2.1
              (tsum_nonneg fun γ => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg ht.le _))
        have hfinh : ∀ c', {p : ℕ × ℝ | c' ≤ p.2 - m ∧ (pw p.1).coeff p.2 / c ≠ 0}.Finite := by
          intro c'
          apply (Set.Finite.biUnion (Finset.range (⌈-(c' + m) / δ⌉₊ + 1)).finite_toSet
            (fun n _ => ((pw n).support_finite_above (c' + m)).image (fun γ => (n, γ)))).subset
          rintro ⟨n, γ⟩ ⟨h1, h2⟩
          have h3 : (pw n).coeff γ ≠ 0 := (div_ne_zero_iff.1 h2).1
          have h4 := hsupp_pw n γ h3
          simp only at h1
          have h5 : (n:ℝ) ≤ -(c' + m) / δ := by
            rw [le_div_iff₀ hδ]; linarith
          have h6 : n ≤ ⌈-(c' + m) / δ⌉₊ := by exact_mod_cast h5.trans (Nat.le_ceil _)
          exact Set.mem_iUnion₂.2 ⟨n, Finset.mem_coe.2 (Finset.mem_range.2 (Nat.lt_succ_of_le h6)),
            γ, ⟨by linarith, h3⟩, rfl⟩
        set ρ := max (max T ρv) (max ρf 1) with hρ
        have tfacts : ∀ t, ρ < t → 0 < t ∧ T ≤ t ∧ ρv < t ∧ ρf < t := by
          intro t ht
          have a1 := le_max_left (max T ρv) (max ρf 1)
          have a2 := le_max_right (max T ρv) (max ρf 1)
          have a3 := le_max_left T ρv
          have a4 := le_max_right T ρv
          have a5 := le_max_left ρf 1
          have a6 := le_max_right ρf 1
          refine ⟨by linarith, by linarith, by linarith, by linarith⟩
        have hK : ∀ t, ρ < t →
            Summable (fun p : ℕ × ℝ => |(pw p.1).coeff p.2 / c| * t ^ (p.2 - m)) := by
          intro t ht
          obtain ⟨htp, hTt, hvt, _⟩ := tfacts t ht
          have hsvt := hsv t hvt
          have hVlt := hT' t hTt
          have hV0 : 0 ≤ ∑' γ, |v.coeff γ| * t ^ γ :=
            tsum_nonneg fun γ => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg htp.le _)
          have hterm : ∀ (n : ℕ) (γ : ℝ), |(pw n).coeff γ / c| * t ^ (γ - m) =
              |(pw n).coeff γ| * t ^ γ * (1 / (c * t ^ m)) := by
            intro n γ; rw [abs_div, abs_of_pos hc, Real.rpow_sub htp]; ring
          have hK0 : 0 ≤ 1 / (c * t ^ m) := by
            have := Real.rpow_pos_of_pos htp m; positivity
          refine (summable_prod_of_nonneg (fun p => mul_nonneg (abs_nonneg _)
            (Real.rpow_nonneg htp.le _))).2 ⟨fun n => ?_, ?_⟩
          · simp only [hterm]; exact (hpw t htp hsvt n).1.mul_right _
          · simp only [hterm]
            refine ((summable_geometric_of_lt_one hV0 (by linarith)).mul_right
              (1 / (c * t ^ m))).of_nonneg_of_le (fun n => tsum_nonneg fun γ =>
                mul_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg htp.le _)) hK0) (fun n => ?_)
            rw [tsum_mul_right]
            exact mul_le_mul_of_nonneg_right (hpw t htp hsvt n).2.1 hK0
        obtain ⟨h, -, hkey⟩ := PUSH (ι := ℕ × ℝ) (fun p => (pw p.1).coeff p.2 / c) (fun p => p.2 - m)
          hfinh ⟨ρ, by linarith [(tfacts (ρ + 1) (by linarith)).1, le_max_right ρf 1,
            le_max_right (max T ρv) (max ρf 1)], hK⟩
        refine ⟨h, ?_⟩
        filter_upwards [eventually_gt_atTop ρ] with t ht
        obtain ⟨htp, hTt, hvt, hft⟩ := tfacts t ht
        have hsvt := hsv t hvt
        have hVlt := hT' t hTt
        have hvabs : |v.eval t| < 1 := by
          have : |v.eval t| ≤ ∑' γ, |v.coeff γ| * t ^ γ := by
            unfold Puiseux.eval; rw [← Real.norm_eq_abs]
            refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
            · exact hsvt.congr fun γ => by
                rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos htp _)]
            · apply tsum_congr; intro γ
              rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos htp _)]
          linarith
        have hheval : h.eval t = (1 - v.eval t)⁻¹ * (1 / (c * t ^ m)) := by
          rw [(hkey t htp (hK t ht)).2.2]
          have hsig : Summable (fun p : ℕ × ℝ => (pw p.1).coeff p.2 / c * t ^ (p.2 - m)) :=
            Summable.of_norm ((hK t ht).congr fun p => by
              rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos htp _)])
          rw [hsig.tsum_prod]
          have hin : ∀ n : ℕ, ∑' γ, (pw n).coeff γ / c * t ^ (γ - m) =
              (v.eval t) ^ n * (1 / (c * t ^ m)) := by
            intro n
            rw [← (hpw t htp hsvt n).2.2]
            unfold Puiseux.eval
            rw [← tsum_mul_right]
            apply tsum_congr; intro γ
            rw [Real.rpow_sub htp]; ring
          simp only [hin]
          rw [tsum_mul_right, tsum_geometric_of_abs_lt_one hvabs]
        have hfeval : f.eval t = c * t ^ m * (1 - v.eval t) := by
          have hfs := SUMM f.coeff t htp (hsf t hft)
          have hve := (hvkey t htp (hvs t hft)).2.2
          have htm : t ^ m ≠ 0 := (Real.rpow_pos_of_pos htp m).ne'
          have e2 : c * t ^ m * v.eval t = -(∑' β, if β = m then 0 else f.coeff β * t ^ β) := by
            rw [hve, ← tsum_mul_left, ← tsum_neg]
            apply tsum_congr; intro β
            split_ifs with hb
            · simp
            · rw [Real.rpow_sub htp]; field_simp
          rw [mul_sub, mul_one, e2, sub_neg_eq_add]
          unfold Puiseux.eval
          exact hfs.tsum_eq_add_tsum_ite m
        rw [hfeval, hheval]
        have h1 : 1 - v.eval t ≠ 0 := by linarith [abs_lt.1 hvabs]
        have h2 : c * t ^ m ≠ 0 := by
          have := Real.rpow_pos_of_pos htp m; positivity
        field_simp
      obtain ⟨GE, hGE⟩ : ∃ GE : (ℝ → ℝ) → Prop,
          ∀ f, GE f ↔ ∃ p : Puiseux, ∀ᶠ t in atTop, p.eval t = f t := ⟨_, fun _ => Iff.rfl⟩
      have GEp : ∀ p : Puiseux, GE (fun t => p.eval t) := by
        intro p; exact (hGE _).2 ⟨p, Eventually.of_forall fun _ => rfl⟩
      have GEcongr : ∀ f g : ℝ → ℝ, GE f → (∀ᶠ t in atTop, f t = g t) → GE g := by
        intro f g hf hfg
        obtain ⟨p, hp⟩ := (hGE f).1 hf
        exact (hGE g).2 ⟨p, by filter_upwards [hp, hfg] with t h1 h2; rw [h1, h2]⟩
      have GEc : ∀ r : ℝ, GE (fun _ => r) := by
        intro r
        obtain ⟨p, -, hp⟩ := MON r 0
        exact (hGE _).2 ⟨p, Eventually.of_forall fun t => by rw [hp]; simp⟩
      have GEadd : ∀ f g : ℝ → ℝ, GE f → GE g → GE (fun t => f t + g t) := by
        intro f g hf hg
        obtain ⟨p, hp⟩ := (hGE f).1 hf
        obtain ⟨q, hq⟩ := (hGE g).1 hg
        obtain ⟨h, hh⟩ := ADDE p q
        exact (hGE _).2 ⟨h, by filter_upwards [hp, hq, hh] with t h1 h2 h3; rw [h3, h1, h2]⟩
      have GEmulP : ∀ p q : Puiseux, ∃ h : Puiseux, ∀ᶠ t in atTop, h.eval t = p.eval t * q.eval t := by
        intro f g
        obtain ⟨h, _, hk⟩ := MUL f g
        obtain ⟨ρf, hρf, hsf⟩ := f.abs_summable
        obtain ⟨ρg, hρg, hsg⟩ := g.abs_summable
        refine ⟨h, ?_⟩
        filter_upwards [eventually_gt_atTop (max ρf ρg)] with t ht
        have ht1 : ρf < t := lt_of_le_of_lt (le_max_left _ _) ht
        have ht2 : ρg < t := lt_of_le_of_lt (le_max_right _ _) ht
        exact (hk t (by linarith) (hsf t ht1) (hsg t ht2)).2.2
      have GEmul : ∀ f g : ℝ → ℝ, GE f → GE g → GE (fun t => f t * g t) := by
        intro f g hf hg
        obtain ⟨p, hp⟩ := (hGE f).1 hf
        obtain ⟨q, hq⟩ := (hGE g).1 hg
        obtain ⟨h, hh⟩ := GEmulP p q
        exact (hGE _).2 ⟨h, by filter_upwards [hp, hq, hh] with t h1 h2 h3; rw [h3, h1, h2]⟩
      have GEtri : ∀ f : ℝ → ℝ, GE f → (∀ᶠ t in atTop, f t = 0) ∨ (∀ᶠ t in atTop, 0 < f t) ∨
          (∀ᶠ t in atTop, f t < 0) := by
        intro f hf
        obtain ⟨p, hp⟩ := (hGE f).1 hf
        rcases VAL p with ⟨h0, -⟩ | ⟨m, hm, hub, -⟩
        · left
          filter_upwards [hp] with t ht
          rw [← ht, Z p h0 t]
        · have hε : 0 < |p.coeff m| / 2 := by have := abs_pos.2 hm; linarith
          have hL := LEAD p m hm hub _ hε
          rcases lt_or_gt_of_ne hm with hneg | hpos
          · right; right
            filter_upwards [hp, hL, eventually_gt_atTop 0] with t h1 h2 h3
            have htm : 0 < t ^ m := Real.rpow_pos_of_pos h3 _
            rw [abs_of_neg hneg] at h2
            have := (abs_le.1 h2).2
            rw [← h1]; linarith [mul_neg_of_neg_of_pos hneg htm]
          · right; left
            filter_upwards [hp, hL, eventually_gt_atTop 0] with t h1 h2 h3
            have htm : 0 < t ^ m := Real.rpow_pos_of_pos h3 _
            rw [abs_of_pos hpos] at h2
            have := (abs_le.1 h2).1
            rw [← h1]; linarith [mul_pos hpos htm]
      have GEinv : ∀ f : ℝ → ℝ, GE f → GE (fun t => (f t)⁻¹) := by
        intro f hf
        obtain ⟨p, hp⟩ := (hGE f).1 hf
        rcases GEtri f hf with h0 | hpos | hneg
        · exact GEcongr _ _ (GEc 0) (by filter_upwards [h0] with t ht; rw [ht]; simp)
        · have hK : KPositive p := by
            filter_upwards [hp, hpos] with t h1 h2; rw [h1]; exact h2
          obtain ⟨h, hh⟩ := INV p hK
          refine (hGE _).2 ⟨h, ?_⟩
          filter_upwards [hp, hh, hpos] with t h1 h2 h3
          rw [h1] at h2
          exact (eq_inv_of_mul_eq_one_right h2)
        · obtain ⟨o, -, ho⟩ := MON (-1) 0
          obtain ⟨q, hq⟩ := GEmulP o p
          have hK : KPositive q := by
            filter_upwards [hp, hq, hneg] with t h1 h2 h3
            rw [h2, ho, h1]; simp; linarith
          obtain ⟨h, hh⟩ := INV q hK
          obtain ⟨h', hh'⟩ := GEmulP o h
          refine (hGE _).2 ⟨h', ?_⟩
          filter_upwards [hp, hq, hh, hh', hneg] with t h1 h2 h3 h4 h5
          rw [h2, ho, h1] at h3
          rw [h4, ho]
          simp only [Real.rpow_zero, mul_one] at h3 ⊢
          have : f t * h.eval t = -1 := by linarith
          have hne : f t ≠ 0 := h5.ne
          field_simp
          linarith
      have GEsum : ∀ {ι : Type} (s : Finset ι) (F : ι → ℝ → ℝ), (∀ i ∈ s, GE (F i)) →
          GE (fun t => ∑ i ∈ s, F i t) := by
        intro ι s F hF
        classical
        induction s using Finset.induction_on with
        | empty => simpa using GEc 0
        | insert a s ha ih =>
          have h1 := hF a (Finset.mem_insert_self a s)
          have h2 := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
          refine GEcongr _ _ (GEadd _ _ h1 h2) (Eventually.of_forall fun t => ?_)
          simp [Finset.sum_insert ha]
      have GEprod : ∀ {ι : Type} (s : Finset ι) (F : ι → ℝ → ℝ), (∀ i ∈ s, GE (F i)) →
          GE (fun t => ∏ i ∈ s, F i t) := by
        intro ι s F hF
        classical
        induction s using Finset.induction_on with
        | empty => simpa using GEc 1
        | insert a s ha ih =>
          have h1 := hF a (Finset.mem_insert_self a s)
          have h2 := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
          refine GEcongr _ _ (GEmul _ _ h1 h2) (Eventually.of_forall fun t => ?_)
          simp [Finset.prod_insert ha]
      have GEdet : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (M : ℝ → Matrix ι ι ℝ),
          (∀ i j, GE (fun t => M t i j)) → GE (fun t => (M t).det) := by
        intro ι _ _ M hM
        refine GEcongr _ _ (GEsum Finset.univ (fun σ : Equiv.Perm ι => fun t =>
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, M t (σ i) i) (fun σ _ => ?_))
          (Eventually.of_forall fun t => ?_)
        · exact GEmul _ _ (GEc _) (GEprod _ _ (fun i _ => hM _ _))
        · simp only [Matrix.det_apply']
      have GEmatmul : ∀ {ι κ μ : Type} [Fintype κ] (P : ℝ → Matrix ι κ ℝ) (Q : ℝ → Matrix κ μ ℝ),
          (∀ i j, GE (fun t => P t i j)) → (∀ i j, GE (fun t => Q t i j)) →
          ∀ i j, GE (fun t => (P t * Q t) i j) := by
        intro ι κ μ _ P Q hP hQ i j
        refine GEcongr _ _ (GEsum Finset.univ (fun k => fun t => P t i k * Q t k j)
          (fun k _ => GEmul _ _ (hP _ _) (hQ _ _))) (Eventually.of_forall fun t => ?_)
        simp [Matrix.mul_apply]
      have GEmulVec : ∀ {ι κ : Type} [Fintype ι] (P : ℝ → Matrix κ ι ℝ) (v : ℝ → ι → ℝ),
          (∀ i j, GE (fun t => P t i j)) → (∀ i, GE (fun t => v t i)) →
          ∀ k, GE (fun t => (P t *ᵥ v t) k) := by
        intro ι κ _ P v hP hv k
        refine GEcongr _ _ (GEsum Finset.univ (fun j => fun t => P t k j * v t j)
          (fun j _ => GEmul _ _ (hP _ _) (hv _))) (Eventually.of_forall fun t => ?_)
        simp [Matrix.mulVec, dotProduct]
      have GEmatinv : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (M : ℝ → Matrix ι ι ℝ),
          (∀ i j, GE (fun t => M t i j)) → ∀ i j, GE (fun t => (M t)⁻¹ i j) := by
        intro ι _ _ M hM i j
        have hadj : GE (fun t => (M t).adjugate i j) := by
          refine GEcongr _ _ (GEdet (fun t => (M t).updateRow j (Pi.single i 1)) ?_)
            (Eventually.of_forall fun t => ?_)
          · intro a b
            by_cases hab : a = j
            · subst hab
              refine GEcongr _ _ (GEc ((Pi.single i (1:ℝ) : ι → ℝ) b))
                (Eventually.of_forall fun t => ?_)
              simp
            · refine GEcongr _ _ (hM a b) (Eventually.of_forall fun t => ?_)
              simp [Matrix.updateRow_ne hab]
          · simp [Matrix.adjugate_apply]
        refine GEcongr _ _ (GEmul _ _ (GEinv _ (GEdet M hM)) hadj)
          (Eventually.of_forall fun t => ?_)
        simp [Matrix.inv_def, Ring.inverse_eq_inv']
      have GEfreq0 : ∀ f : ℝ → ℝ, GE f → (∃ᶠ t in atTop, f t = 0) → ∀ᶠ t in atTop, f t = 0 := by
        intro f hf hfr
        rcases GEtri f hf with h | h | h
        · exact h
        · exact absurd (hfr.and_eventually h).exists (by rintro ⟨t, h1, h2⟩; linarith)
        · exact absurd (hfr.and_eventually h).exists (by rintro ⟨t, h1, h2⟩; linarith)
      have GEfreqnn : ∀ f : ℝ → ℝ, GE f → (∃ᶠ t in atTop, 0 ≤ f t) → ∀ᶠ t in atTop, 0 ≤ f t := by
        intro f hf hfr
        rcases GEtri f hf with h | h | h
        · exact h.mono fun t ht => ht.symm.le
        · exact h.mono fun t ht => ht.le
        · exact absurd (hfr.and_eventually h).exists (by rintro ⟨t, h1, h2⟩; linarith)
      have HBL : ∀ (k l : ℕ) (A : Matrix (Fin k) (Fin l) ℝ) (b : Fin k → ℝ) (c : Fin l → ℝ) (p : ℝ),
          (∃ x0 : Fin l → ℝ, (∀ j, 0 < x0 j) ∧ ∀ i, (A *ᵥ x0) i < b i) →
          (∀ x : Fin l → ℝ, (∀ j, 0 ≤ x j) → (∀ i, (A *ᵥ x) i ≤ b i) → p ≤ c ⬝ᵥ x) →
          ∃ y : Fin k → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ j, 0 ≤ (c + Aᵀ *ᵥ y) j) ∧ p ≤ -(b ⬝ᵥ y) := by
        intro k l A b c p ⟨x0, hx0p, hx0A⟩ hp
        let O : Set ((Fin k → ℝ) × (Fin l → ℝ) × ℝ) := ⋃ x : Fin l → ℝ,
          ({z | ∀ i, (A *ᵥ x) i - b i < z.1 i} ∩ {z | ∀ j, -x j < z.2.1 j} ∩ {z | c ⬝ᵥ x < z.2.2})
        have hmem : ∀ z, z ∈ O ↔ ∃ x : Fin l → ℝ, (∀ i, (A *ᵥ x) i - b i < z.1 i) ∧
            (∀ j, -x j < z.2.1 j) ∧ c ⬝ᵥ x < z.2.2 := by
          intro z; simp only [O, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, and_assoc]
        have hOopen : IsOpen O := by
          refine isOpen_iUnion fun x => ?_
          refine IsOpen.inter (IsOpen.inter ?_ ?_) ?_
          · simp only [Set.setOf_forall]
            exact isOpen_iInter_of_finite fun i =>
              isOpen_lt continuous_const ((continuous_apply i).comp continuous_fst)
          · simp only [Set.setOf_forall]
            exact isOpen_iInter_of_finite fun j =>
              isOpen_lt continuous_const ((continuous_apply j).comp (continuous_fst.comp continuous_snd))
          · exact isOpen_lt continuous_const (continuous_snd.comp continuous_snd)
        have hOconv : Convex ℝ O := by
          refine convex_iff_forall_pos.2 ?_
          intro z1 hz1 z2 hz2 a1 a2 ha1 ha2 hab
          obtain ⟨x1, h11, h12, h13⟩ := (hmem z1).1 hz1
          obtain ⟨x2, h21, h22, h23⟩ := (hmem z2).1 hz2
          refine (hmem _).2 ⟨a1 • x1 + a2 • x2, fun i => ?_, fun j => ?_, ?_⟩
          · have e : (A *ᵥ (a1 • x1 + a2 • x2)) i - b i =
                a1 * ((A *ᵥ x1) i - b i) + a2 * ((A *ᵥ x2) i - b i) := by
              rw [mulVec_add, mulVec_smul, mulVec_smul]; simp only [Pi.add_apply, Pi.smul_apply,
                smul_eq_mul]
              have : b i = a1 * b i + a2 * b i := by rw [← add_mul, hab, one_mul]
              linarith
            rw [e]; simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            have := mul_lt_mul_of_pos_left (h11 i) ha1
            have := mul_lt_mul_of_pos_left (h21 i) ha2
            linarith
          · simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, Pi.add_apply,
              Pi.smul_apply, smul_eq_mul]
            have := mul_lt_mul_of_pos_left (h12 j) ha1
            have := mul_lt_mul_of_pos_left (h22 j) ha2
            linarith
          · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, dotProduct_add, dotProduct_smul]
            have := mul_lt_mul_of_pos_left h13 ha1
            have := mul_lt_mul_of_pos_left h23 ha2
            linarith
        have hnot : ((0 : Fin k → ℝ), (0 : Fin l → ℝ), p) ∉ O := by
          intro h
          obtain ⟨x, h1, h2, h3⟩ := (hmem _).1 h
          have := hp x (fun j => by have := h2 j; simp at this; linarith)
            (fun i => by have := h1 i; simp at this; linarith)
          simp at h3; linarith
        obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hOconv hOopen hnot
        set α : Fin k → ℝ := fun i => f ((Pi.single i 1 : Fin k → ℝ), (0 : Fin l → ℝ), (0 : ℝ)) with hα
        set β : Fin l → ℝ := fun j => f ((0 : Fin k → ℝ), (Pi.single j 1 : Fin l → ℝ), (0 : ℝ)) with hβ
        set γ : ℝ := f ((0 : Fin k → ℝ), (0 : Fin l → ℝ), (1 : ℝ)) with hγ
        have hform : ∀ u v r, f (u, v, r) = u ⬝ᵥ α + v ⬝ᵥ β + r * γ := by
          intro u v r
          have e : (u, v, r) = ∑ i, u i • ((Pi.single i 1 : Fin k → ℝ), (0 : Fin l → ℝ), (0:ℝ)) +
              ∑ j, v j • ((0 : Fin k → ℝ), (Pi.single j 1 : Fin l → ℝ), (0:ℝ)) +
              r • ((0 : Fin k → ℝ), (0 : Fin l → ℝ), (1:ℝ)) := by
            ext i
            · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
            · simp [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
            · simp [Prod.snd_sum]
          rw [e, map_add, map_add, map_sum, map_sum, map_smul]
          simp only [map_smul, smul_eq_mul, dotProduct, hα, hβ, hγ]
        have hO : ∀ x : Fin l → ℝ, ∀ u v r, (∀ i, (A *ᵥ x) i - b i < u i) → (∀ j, -x j < v j) →
            c ⬝ᵥ x < r → u ⬝ᵥ α + v ⬝ᵥ β + r * γ < p * γ := by
          intro x u v r h1 h2 h3
          have := hf (u, v, r) ((hmem _).2 ⟨x, h1, h2, h3⟩)
          rw [hform, hform] at this; simpa using this
        have LIN : ∀ C a q : ℝ, (∀ T : ℝ, 0 ≤ T → C + T * a < q) → a ≤ 0 := by
          intro C a q h; by_contra ha
          have ha' : 0 < a := not_le.1 ha
          have := h ((|q - C| + 1) / a) (div_nonneg (add_nonneg (abs_nonneg _) zero_le_one) ha'.le)
          rw [div_mul_cancel₀ _ ha'.ne'] at this
          linarith [le_abs_self (q - C)]
        have LIM : ∀ L K q : ℝ, (∀ ε : ℝ, 0 < ε → L + ε * K < q) → L ≤ q := by
          intro L K q h; by_contra hL
          have hLq : 0 < L - q := sub_pos.2 (not_le.1 hL)
          have hK1 : 0 < |K| + 1 := add_pos_of_nonneg_of_pos (abs_nonneg K) one_pos
          have hε : 0 < (L - q) / (|K| + 1) := div_pos hLq hK1
          have h0 := h _ hε
          have he : (L - q) / (|K| + 1) * (|K| + 1) = L - q := div_mul_cancel₀ _ hK1.ne'
          have h1 : (L - q) / (|K| + 1) * (-|K|) ≤ (L - q) / (|K| + 1) * K :=
            mul_le_mul_of_nonneg_left (neg_abs_le K) hε.le
          rw [mul_add, mul_one] at he
          rw [mul_neg] at h1
          linarith
        have hαn : ∀ i, α i ≤ 0 := by
          intro i
          refine LIN ((fun i' => -b i' + 1) ⬝ᵥ α + (fun _ => (1:ℝ)) ⬝ᵥ β + 1 * γ) (α i) (p * γ)
            (fun T hT => ?_)
          have hmemu : ∀ i', (A *ᵥ (0 : Fin l → ℝ)) i' - b i' <
              ((fun i' => -b i' + 1) + T • (Pi.single i 1 : Fin k → ℝ)) i' := by
            intro i'
            have : 0 ≤ (T • (Pi.single i 1 : Fin k → ℝ)) i' := by
              simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]; split_ifs <;> linarith
            simp only [Pi.add_apply, mulVec_zero, Pi.zero_apply]; linarith
          have := hO 0 _ (fun _ => 1) 1 hmemu (fun j => by simp) (by simp)
          rw [add_dotProduct, smul_dotProduct, single_dotProduct] at this
          simp only [smul_eq_mul, one_mul] at this ⊢; linarith
        have hβn : ∀ j, β j ≤ 0 := by
          intro j
          refine LIN ((fun i' => -b i' + 1) ⬝ᵥ α + (fun _ => (1:ℝ)) ⬝ᵥ β + 1 * γ) (β j) (p * γ)
            (fun T hT => ?_)
          have hmemv : ∀ j', -(0 : Fin l → ℝ) j' <
              ((fun _ : Fin l => (1:ℝ)) + T • (Pi.single j 1 : Fin l → ℝ)) j' := by
            intro j'
            have : 0 ≤ (T • (Pi.single j 1 : Fin l → ℝ)) j' := by
              simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]; split_ifs <;> linarith
            simp only [Pi.add_apply, Pi.zero_apply]; linarith
          have := hO 0 (fun i' => -b i' + 1) _ 1 (fun i' => by simp) hmemv (by simp)
          rw [add_dotProduct, smul_dotProduct, single_dotProduct] at this
          simp only [smul_eq_mul, one_mul] at this ⊢; linarith
        have hγn : γ ≤ 0 := by
          refine LIN ((fun i' => -b i' + 1) ⬝ᵥ α + (fun _ => (1:ℝ)) ⬝ᵥ β + 1 * γ) γ (p * γ)
            (fun T hT => ?_)
          have := hO 0 (fun i' => -b i' + 1) (fun _ => 1) (1 + T) (fun i' => by simp)
            (fun j => by simp) (by simp; linarith)
          linarith
        have KEY : ∀ x : Fin l → ℝ, (A *ᵥ x - b) ⬝ᵥ α - x ⬝ᵥ β + (c ⬝ᵥ x) * γ ≤ p * γ := by
          intro x
          refine LIM _ (∑ i, α i + ∑ j, β j + γ) _ (fun ε hε => ?_)
          have := hO x (fun i => (A *ᵥ x) i - b i + ε) (fun j => -x j + ε) (c ⬝ᵥ x + ε)
            (fun i => by linarith) (fun j => by linarith) (by linarith)
          have e1 : (fun i => (A *ᵥ x) i - b i + ε) ⬝ᵥ α = (A *ᵥ x - b) ⬝ᵥ α + ε * ∑ i, α i := by
            simp only [dotProduct, Pi.sub_apply, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
          have e2 : (fun j => -x j + ε) ⬝ᵥ β = -(x ⬝ᵥ β) + ε * ∑ j, β j := by
            simp only [dotProduct, add_mul, Finset.sum_add_distrib, Finset.mul_sum, neg_mul,
              Finset.sum_neg_distrib]
          rw [e1, e2] at this; linarith
        have hγneg : γ < 0 := by
          refine lt_of_le_of_ne hγn fun hγ0 => ?_
          have h := KEY x0
          rw [hγ0, mul_zero, mul_zero, add_zero] at h
          have hS1 : ∀ i ∈ Finset.univ, 0 ≤ (A *ᵥ x0 - b) i * α i := fun i _ =>
            mul_nonneg_of_nonpos_of_nonpos (by simp only [Pi.sub_apply]; linarith [hx0A i]) (hαn i)
          have hS2 : ∀ j ∈ Finset.univ, x0 j * β j ≤ 0 := fun j _ =>
            mul_nonpos_of_nonneg_of_nonpos (hx0p j).le (hβn j)
          have s1 := Finset.sum_nonneg hS1
          have s2 := Finset.sum_nonpos hS2
          simp only [dotProduct] at h
          have z1 : ∑ i, (A *ᵥ x0 - b) i * α i = 0 := by linarith
          have z2 : ∑ j, x0 j * β j = 0 := by linarith
          have hα0 : ∀ i, α i = 0 := by
            intro i
            have := (Finset.sum_eq_zero_iff_of_nonneg hS1).1 z1 i (Finset.mem_univ _)
            rcases mul_eq_zero.1 this with h' | h'
            · simp only [Pi.sub_apply] at h'; linarith [hx0A i]
            · exact h'
          have hβ0 : ∀ j, β j = 0 := by
            intro j
            have := (Finset.sum_eq_zero_iff_of_nonpos hS2).1 z2 j (Finset.mem_univ _)
            rcases mul_eq_zero.1 this with h' | h'
            · linarith [hx0p j]
            · exact h'
          have := hO 0 (fun i' => -b i' + 1) (fun _ => 1) 1 (fun i' => by simp)
            (fun j => by simp) (by simp)
          have ea : α = 0 := funext hα0
          have eb : β = 0 := funext hβ0
          rw [ea, eb, hγ0] at this; simp at this
        obtain ⟨y, hy⟩ : ∃ y : Fin k → ℝ, y = γ⁻¹ • α := ⟨_, rfl⟩
        obtain ⟨σ, hσ⟩ : ∃ σ : Fin l → ℝ, σ = γ⁻¹ • β := ⟨_, rfl⟩
        have hya : α = γ • y := by rw [hy, smul_smul, mul_inv_cancel₀ hγneg.ne, one_smul]
        have hsb : β = γ • σ := by rw [hσ, smul_smul, mul_inv_cancel₀ hγneg.ne, one_smul]
        have hyn : ∀ i, 0 ≤ y i := fun i => by
          simp only [hy, Pi.smul_apply, smul_eq_mul]
          exact mul_nonneg_of_nonpos_of_nonpos (inv_nonpos.2 hγn) (hαn i)
        have hσn : ∀ j, 0 ≤ σ j := fun j => by
          simp only [hσ, Pi.smul_apply, smul_eq_mul]
          exact mul_nonneg_of_nonpos_of_nonpos (inv_nonpos.2 hγn) (hβn j)
        have KEY2 : ∀ x : Fin l → ℝ, p ≤ x ⬝ᵥ (c + Aᵀ *ᵥ y - σ) - b ⬝ᵥ y := by
          intro x
          have h := KEY x
          rw [hya, hsb, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h
          have eA : (A *ᵥ x - b) ⬝ᵥ y = x ⬝ᵥ (Aᵀ *ᵥ y) - b ⬝ᵥ y := by
            rw [sub_dotProduct, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose,
              dotProduct_comm]
          have e2 : x ⬝ᵥ (c + Aᵀ *ᵥ y - σ) = x ⬝ᵥ c + x ⬝ᵥ (Aᵀ *ᵥ y) - x ⬝ᵥ σ := by
            rw [dotProduct_sub, dotProduct_add]
          rw [e2, dotProduct_comm x c]
          rw [eA] at h
          by_contra hcon
          have := mul_lt_mul_of_neg_right (not_le.1 hcon) hγneg
          linarith
        refine ⟨y, hyn, fun j => ?_, by simpa using KEY2 0⟩
        have hq : (c + Aᵀ *ᵥ y - σ) j = 0 := by
          by_contra hne
          have := KEY2 (((p + b ⬝ᵥ y - 1) / ((c + Aᵀ *ᵥ y - σ) j)) • Pi.single j 1)
          rw [smul_dotProduct, single_dotProduct, smul_eq_mul, one_mul,
            div_mul_cancel₀ _ hne] at this
          linarith
        have := hσn j
        simp only [Pi.sub_apply] at hq
        linarith
      have SD : ∀ (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ),
          (strictlyFeasible A b c).Nonempty →
          ∃ z : PDPoint n m, z ∈ primalDualFeasible A b c ∧ c ⬝ᵥ z.1 + b ⬝ᵥ z.2.2.2 ≤ 0 := by
        intro A b c ⟨z0, hPe, hDe, hx0, hw0, hs0, hy0⟩
        have WD : ∀ x : Fin n → ℝ, ∀ y : Fin m → ℝ, (∀ j, 0 ≤ x j) → (∀ i, (A *ᵥ x) i ≤ b i) →
            (∀ i, 0 ≤ y i) → (∀ j, 0 ≤ (c + Aᵀ *ᵥ y) j) → 0 ≤ c ⬝ᵥ x + b ⬝ᵥ y := by
          intro x y hx hAx hy hcy
          have h1 : (A *ᵥ x) ⬝ᵥ y ≤ b ⬝ᵥ y :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hAx i) (hy i)
          have h2 : 0 ≤ x ⬝ᵥ (c + Aᵀ *ᵥ y) := Finset.sum_nonneg fun j _ => mul_nonneg (hx j) (hcy j)
          have e : x ⬝ᵥ (c + Aᵀ *ᵥ y) = c ⬝ᵥ x + (A *ᵥ x) ⬝ᵥ y := by
            rw [dotProduct_add, dotProduct_comm x c, mulVec_transpose, dotProduct_comm x,
              ← dotProduct_mulVec, dotProduct_comm y]
          linarith
        set P : Set ℝ := {v | ∃ x : Fin n → ℝ, (∀ j, 0 ≤ x j) ∧ (∀ i, (A *ᵥ x) i ≤ b i) ∧
          v = c ⬝ᵥ x} with hP
        set D : Set ℝ := {v | ∃ y : Fin m → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ j, 0 ≤ (c + Aᵀ *ᵥ y) j) ∧
          v = b ⬝ᵥ y} with hD
        have hAx0 : ∀ i, (A *ᵥ z0.1) i < b i := by
          intro i; have := congrFun hPe i; simp only [Pi.add_apply] at this; linarith [hw0 i]
        have hcy0 : ∀ j, 0 < (c + Aᵀ *ᵥ z0.2.2.2) j := by
          intro j; have := congrFun hDe j; simp only [Pi.sub_apply] at this
          simp only [Pi.add_apply]; linarith [hs0 j]
        have hPne : P.Nonempty := ⟨_, z0.1, fun j => (hx0 j).le, fun i => (hAx0 i).le, rfl⟩
        have hDne : D.Nonempty := ⟨_, z0.2.2.2, fun i => (hy0 i).le, fun j => (hcy0 j).le, rfl⟩
        have hPb : BddBelow P := ⟨-(b ⬝ᵥ z0.2.2.2), by
          rintro v ⟨x, hx, hAx, rfl⟩
          linarith [WD x z0.2.2.2 hx hAx (fun i => (hy0 i).le) (fun j => (hcy0 j).le)]⟩
        have hDb : BddBelow D := ⟨-(c ⬝ᵥ z0.1), by
          rintro v ⟨y, hy, hcy, rfl⟩
          linarith [WD z0.1 y (fun j => (hx0 j).le) (fun i => (hAx0 i).le) hy hcy]⟩
        obtain ⟨y, hy, hcy, hpy⟩ := HBL m n A b c (sInf P) ⟨z0.1, hx0, hAx0⟩
          (fun x hx hAx => csInf_le hPb ⟨x, hx, hAx, rfl⟩)
        obtain ⟨x, hx, hbx, hdx⟩ := HBL n m (-Aᵀ) c b (sInf D) ⟨z0.2.2.2, hy0, fun j => by
            have := hcy0 j; simp only [Pi.add_apply] at this
            rw [neg_mulVec]; simp only [Pi.neg_apply]; linarith⟩
          (fun y hy hAy => csInf_le hDb ⟨y, hy, fun j => by
            have := hAy j; rw [neg_mulVec] at this; simp only [Pi.neg_apply] at this
            simp only [Pi.add_apply]; linarith, rfl⟩)
        have hbx' : ∀ i, 0 ≤ b i - (A *ᵥ x) i := by
          intro i; have := hbx i
          rw [transpose_neg, transpose_transpose, neg_mulVec] at this
          simpa [sub_eq_add_neg] using this
        have hpd : 0 ≤ sInf P + sInf D := by
          have : -sInf D ≤ sInf P := by
            refine le_csInf hPne ?_
            rintro v ⟨x', hx', hAx', rfl⟩
            have : -(c ⬝ᵥ x') ≤ sInf D := by
              refine le_csInf hDne ?_
              rintro w ⟨y', hy', hcy', rfl⟩
              linarith [WD x' y' hx' hAx' hy' hcy']
            linarith
          linarith
        refine ⟨(x, b - A *ᵥ x, c + Aᵀ *ᵥ y, y), ⟨?_, ?_, hx, fun i => ?_, hcy, hy⟩, ?_⟩
        · simp
        · simp
        · simpa using hbx' i
        · simp only; linarith
      have BFS : ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] (M : Matrix κ ι ℝ)
          (r : κ → ℝ) (v : ι → ℝ), M *ᵥ v = r → (∀ j, 0 ≤ v j) →
          ∃ S : Finset ι, M *ᵥ ((Matrix.diagonal (fun j => if j ∈ S then (1:ℝ) else 0) * Mᵀ * M *
              Matrix.diagonal (fun j => if j ∈ S then (1:ℝ) else 0) +
              (1 - Matrix.diagonal (fun j => if j ∈ S then (1:ℝ) else 0)))⁻¹ *ᵥ
              (Matrix.diagonal (fun j => if j ∈ S then (1:ℝ) else 0) *ᵥ (Mᵀ *ᵥ r))) = r ∧
            ∀ j, 0 ≤ ((Matrix.diagonal (fun j => if j ∈ S then (1:ℝ) else 0) * Mᵀ * M *
              Matrix.diagonal (fun j => if j ∈ S then (1:ℝ) else 0) +
              (1 - Matrix.diagonal (fun j => if j ∈ S then (1:ℝ) else 0)))⁻¹ *ᵥ
              (Matrix.diagonal (fun j => if j ∈ S then (1:ℝ) else 0) *ᵥ (Mᵀ *ᵥ r))) j := by
        intro ι κ _ _ _ M r v hv hnn
        classical
        have hex : ∃ k, ∃ u : ι → ℝ, M *ᵥ u = r ∧ (∀ j, 0 ≤ u j) ∧
            (Finset.univ.filter (fun j => u j ≠ 0)).card = k := ⟨_, v, hv, hnn, rfl⟩
        obtain ⟨u, hu, hunn, hcard⟩ := Nat.find_spec hex
        have hmin : ∀ u' : ι → ℝ, M *ᵥ u' = r → (∀ j, 0 ≤ u' j) →
            ¬ (Finset.univ.filter (fun j => u' j ≠ 0)).card < Nat.find hex := by
          intro u' h1 h2 h3
          exact Nat.find_min hex h3 ⟨u', h1, h2, rfl⟩
        set S := Finset.univ.filter (fun j => u j ≠ 0) with hS
        refine ⟨S, ?_⟩
        set D : Matrix ι ι ℝ := Matrix.diagonal (fun j => if j ∈ S then (1:ℝ) else 0) with hD
        have key : ∀ x : ι → ℝ, (∀ j, j ∉ S → x j = 0) → M *ᵥ x = 0 → (∃ j, 0 < x j) → False := by
          intro x hxS hMx ⟨j0, hj0⟩
          set P := Finset.univ.filter (fun j => 0 < x j) with hP
          have hPn : P.Nonempty := ⟨j0, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj0⟩⟩
          obtain ⟨jm, hjm, hjmin⟩ := P.exists_min_image (fun j => u j / x j) hPn
          have hxjm : 0 < x jm := (Finset.mem_filter.1 hjm).2
          set θ := u jm / x jm with hθdef
          have hθ : 0 ≤ θ := div_nonneg (hunn jm) hxjm.le
          apply hmin (u - θ • x)
          · rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hMx, hu, smul_zero, sub_zero]
          · intro j
            simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
            by_cases hj : 0 < x j
            · have := hjmin j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)
              rw [le_div_iff₀ hj] at this
              linarith
            · push_neg at hj
              linarith [hunn j, mul_nonpos_of_nonneg_of_nonpos hθ hj]
          · have hsub : Finset.univ.filter (fun j => (u - θ • x) j ≠ 0) ⊆ S.erase jm := by
              intro j hj
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
              rw [Finset.mem_erase]
              constructor
              · rintro rfl
                apply hj
                simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, θ]
                rw [div_mul_cancel₀ _ hxjm.ne', sub_self]
              · by_contra hjS
                apply hj
                have h1 := hxS j hjS
                have h2 : u j = 0 := by
                  by_contra h2; exact hjS (Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩)
                simp [h1, h2]
            have hjmS : jm ∈ S := by
              by_contra h
              have := hxS jm h; linarith
            calc _ ≤ (S.erase jm).card := Finset.card_le_card hsub
              _ < S.card := Finset.card_erase_lt_of_mem hjmS
              _ = Nat.find hex := hcard
        have hind : ∀ x : ι → ℝ, (∀ j, j ∉ S → x j = 0) → M *ᵥ x = 0 → x = 0 := by
          intro x hxS hMx
          by_contra hx0
          obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
            by_contra h; push_neg at h; exact hx0 (funext h)
          rcases lt_or_gt_of_ne hj with hlt | hgt
          · apply key (-x)
            · intro i hi; simp [hxS i hi]
            · rw [Matrix.mulVec_neg, hMx, neg_zero]
            · exact ⟨j, by simp; linarith⟩
          · exact key x hxS hMx ⟨j, hgt⟩
        have hDv : ∀ (y : ι → ℝ) j, (D *ᵥ y) j = if j ∈ S then y j else 0 := by
          intro y j; simp [D, Matrix.mulVec_diagonal]
        have hHv : ∀ y : ι → ℝ, (D * Mᵀ * M * D + (1 - D)) *ᵥ y =
            D *ᵥ (Mᵀ *ᵥ (M *ᵥ (D *ᵥ y))) + (y - D *ᵥ y) := by
          intro y
          rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
          simp only [← Matrix.mulVec_mulVec]
        have hHdet : (D * Mᵀ * M * D + (1 - D)).det ≠ 0 := by
          intro hdet
          obtain ⟨x, hx0, hHx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
          apply hx0
          rw [hHv] at hHx
          have hxS : ∀ j, j ∉ S → x j = 0 := by
            intro j hj
            have := congrFun hHx j
            simp only [Pi.add_apply, Pi.sub_apply, hDv, if_neg hj, Pi.zero_apply] at this
            linarith
          have hDx : D *ᵥ x = x := by
            funext j; rw [hDv]; split_ifs with h
            · rfl
            · exact (hxS j h).symm
          rw [hDx, sub_self, add_zero] at hHx
          apply hind x hxS
          have h1 : x ⬝ᵥ (D *ᵥ (Mᵀ *ᵥ (M *ᵥ x))) = 0 := by rw [hHx, dotProduct_zero]
          have h2 : x ⬝ᵥ (D *ᵥ (Mᵀ *ᵥ (M *ᵥ x))) = (M *ᵥ x) ⬝ᵥ (M *ᵥ x) := by
            have : x ⬝ᵥ (D *ᵥ (Mᵀ *ᵥ (M *ᵥ x))) = x ⬝ᵥ (Mᵀ *ᵥ (M *ᵥ x)) := by
              unfold dotProduct
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [hDv]; split_ifs with h
              · rfl
              · rw [hxS j h]; simp
            rw [this, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
          rw [h2] at h1
          exact dotProduct_self_eq_zero.mp h1
        have hDu : D *ᵥ u = u := by
          funext j; rw [hDv]; split_ifs with h
          · rfl
          · simp [S] at h; exact h.symm
        have hHu : (D * Mᵀ * M * D + (1 - D)) *ᵥ u = D *ᵥ (Mᵀ *ᵥ r) := by
          rw [hHv, hDu, hu, sub_self, add_zero]
        have hval : (D * Mᵀ * M * D + (1 - D))⁻¹ *ᵥ (D *ᵥ (Mᵀ *ᵥ r)) = u := by
          rw [← hHu, Matrix.mulVec_mulVec,
            Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hHdet), Matrix.one_mulVec]
        rw [hval]
        exact ⟨hu, hunn⟩
      have hconv : ∀ f : Puiseux, ∀ᶠ t in atTop, ConvergesAt f t := by
        intro f
        obtain ⟨ρ, -, hρ⟩ := f.abs_summable
        filter_upwards [eventually_gt_atTop ρ] with t ht
        exact hρ t ht
      have hA : ∀ᶠ t in atTop, ∀ i j, ConvergesAt (A i j) t := by
        rw [eventually_all]; intro i; rw [eventually_all]; intro j; exact hconv _
      have hb : ∀ᶠ t in atTop, ∀ i, ConvergesAt (b i) t := by
        rw [eventually_all]; intro i; exact hconv _
      have hc : ∀ᶠ t in atTop, ∀ i, ConvergesAt (c i) t := by
        rw [eventually_all]; intro i; exact hconv _
      have hz1 : ∀ᶠ t in atTop, ∀ i, ConvergesAt (zstar.1 i) t := by
        rw [eventually_all]; intro i; exact hconv _
      have hz2 : ∀ᶠ t in atTop, ∀ i, ConvergesAt (zstar.2.1 i) t := by
        rw [eventually_all]; intro i; exact hconv _
      have hz3 : ∀ᶠ t in atTop, ∀ i, ConvergesAt (zstar.2.2.1 i) t := by
        rw [eventually_all]; intro i; exact hconv _
      have hz4 : ∀ᶠ t in atTop, ∀ i, ConvergesAt (zstar.2.2.2 i) t := by
        rw [eventually_all]; intro i; exact hconv _
      have hsf : ∀ᶠ t in atTop,
          (strictlyFeasible (evalMatrix A t) (evalFun b t) (evalFun c t)).Nonempty := by
        obtain ⟨z, hz⟩ := hstrict
        filter_upwards [hz] with t ht
        exact ⟨_, ht⟩
      have WD : ∀ (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
          (x : Fin n → ℝ) (w : Fin m → ℝ) (s : Fin n → ℝ) (y : Fin m → ℝ),
          A *ᵥ x + w = b → s - Aᵀ *ᵥ y = c → (∀ j, 0 ≤ x j) → (∀ i, 0 ≤ w i) →
          (∀ j, 0 ≤ s j) → (∀ i, 0 ≤ y i) → 0 ≤ c ⬝ᵥ x + b ⬝ᵥ y := by
        intro A b c x w s y h1 h2 hx hw hs hy
        rw [← h1, ← h2, sub_dotProduct, mulVec_transpose, ← dotProduct_mulVec, add_dotProduct,
          dotProduct_comm (A *ᵥ x) y]
        have e1 : 0 ≤ s ⬝ᵥ x := Finset.sum_nonneg fun j _ => mul_nonneg (hs j) (hx j)
        have e2 : 0 ≤ w ⬝ᵥ y := Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (hy j)
        linarith
      have GEneg : ∀ f : ℝ → ℝ, GE f → GE (fun t => -f t) := by
        intro f hf
        exact GEcongr _ _ (GEmul _ _ (GEc (-1)) hf) (Eventually.of_forall fun t => by ring)
      have GEsub : ∀ f g : ℝ → ℝ, GE f → GE g → GE (fun t => f t - g t) := by
        intro f g hf hg
        exact GEcongr _ _ (GEadd _ _ hf (GEneg _ hg)) (Eventually.of_forall fun t => by ring)
      -- the combined primal-dual system with zero gap
      obtain ⟨Mt, hMt⟩ : ∃ Mt : ℝ → Matrix (Option (Fin m ⊕ Fin n))
          ((Fin n ⊕ Fin m) ⊕ (Fin n ⊕ Fin m)) ℝ, ∀ t k v, Mt t k v =
          match k with
          | none => Sum.elim (Sum.elim (fun j => (c j).eval t) (fun _ => 0))
              (Sum.elim (fun _ => 0) (fun i => (b i).eval t)) v
          | some (Sum.inl i) => Sum.elim (Sum.elim (fun j => (A i j).eval t)
              (fun i' => if i = i' then 1 else 0)) (fun _ => 0) v
          | some (Sum.inr j) => Sum.elim (fun _ => 0) (Sum.elim
              (fun j' => if j = j' then 1 else 0) (fun i => -(A i j).eval t)) v :=
        ⟨fun t k v => _, fun _ _ _ => rfl⟩
      obtain ⟨rt, hrt⟩ : ∃ rt : ℝ → Option (Fin m ⊕ Fin n) → ℝ, ∀ t k, rt t k =
          match k with
          | none => 0
          | some (Sum.inl i) => (b i).eval t
          | some (Sum.inr j) => (c j).eval t := ⟨fun t k => _, fun _ _ => rfl⟩
      have hrow : ∀ t (v : (Fin n ⊕ Fin m) ⊕ (Fin n ⊕ Fin m) → ℝ),
          Mt t *ᵥ v = rt t ↔
            (evalMatrix A t *ᵥ (fun j => v (Sum.inl (Sum.inl j))) + (fun i => v (Sum.inl (Sum.inr i)))
              = evalFun b t ∧
            (fun j => v (Sum.inr (Sum.inl j))) - (evalMatrix A t)ᵀ *ᵥ (fun i => v (Sum.inr (Sum.inr i)))
              = evalFun c t ∧
            evalFun c t ⬝ᵥ (fun j => v (Sum.inl (Sum.inl j))) +
              evalFun b t ⬝ᵥ (fun i => v (Sum.inr (Sum.inr i))) = 0) := by
        intro t v
        have r1 : ∀ i, (Mt t *ᵥ v) (some (Sum.inl i)) =
            (evalMatrix A t *ᵥ (fun j => v (Sum.inl (Sum.inl j))) +
              (fun i => v (Sum.inl (Sum.inr i)))) i := by
          intro i
          simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, hMt, Sum.elim_inl, Sum.elim_inr,
            Pi.add_apply, evalMatrix, ite_mul, one_mul, zero_mul,
            Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const_zero, add_zero]
        have r2 : ∀ j, (Mt t *ᵥ v) (some (Sum.inr j)) =
            ((fun j => v (Sum.inr (Sum.inl j))) -
              (evalMatrix A t)ᵀ *ᵥ (fun i => v (Sum.inr (Sum.inr i)))) j := by
          intro j
          simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, hMt, Sum.elim_inl, Sum.elim_inr,
            Pi.sub_apply, evalMatrix, Matrix.transpose_apply, ite_mul, one_mul,
            zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const_zero, zero_add,
            neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
        have r3 : (Mt t *ᵥ v) none = evalFun c t ⬝ᵥ (fun j => v (Sum.inl (Sum.inl j))) +
              evalFun b t ⬝ᵥ (fun i => v (Sum.inr (Sum.inr i))) := by
          simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, hMt, Sum.elim_inl, Sum.elim_inr,
            evalFun, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
        constructor
        · intro h
          refine ⟨funext fun i => ?_, funext fun j => ?_, ?_⟩
          · rw [← r1, h, hrt]; rfl
          · rw [← r2, h, hrt]; rfl
          · rw [← r3, h, hrt]
        · rintro ⟨h1, h2, h3⟩
          funext k
          rcases k with _ | (i | j)
          · rw [r3, h3, hrt]
          · rw [r1, h1, hrt]; rfl
          · rw [r2, h2, hrt]; rfl
      have hMGE : ∀ k v, GE (fun t => Mt t k v) := by
        intro k v
        rcases k with _ | (i | j) <;> rcases v with (j' | i') | (j' | i') <;>
          simp only [hMt, Sum.elim_inl, Sum.elim_inr]
        all_goals first
          | exact GEc _
          | exact GEp _
          | exact GEneg _ (GEp _)
      have hrGE : ∀ k, GE (fun t => rt t k) := by
        intro k
        rcases k with _ | (i | j) <;> simp only [hrt]
        all_goals first
          | exact GEc _
          | exact GEp _
      -- candidate basic solutions
      classical
      let D : Finset ((Fin n ⊕ Fin m) ⊕ (Fin n ⊕ Fin m)) →
          Matrix ((Fin n ⊕ Fin m) ⊕ (Fin n ⊕ Fin m)) ((Fin n ⊕ Fin m) ⊕ (Fin n ⊕ Fin m)) ℝ :=
        fun S => Matrix.diagonal (fun j => if j ∈ S then (1:ℝ) else 0)
      let cand : Finset ((Fin n ⊕ Fin m) ⊕ (Fin n ⊕ Fin m)) → ℝ →
          (Fin n ⊕ Fin m) ⊕ (Fin n ⊕ Fin m) → ℝ := fun S t =>
        (D S * (Mt t)ᵀ * Mt t * D S + (1 - D S))⁻¹ *ᵥ (D S *ᵥ ((Mt t)ᵀ *ᵥ rt t))
      have hcandGE : ∀ S j, GE (fun t => cand S t j) := by
        intro S j
        have hD : ∀ i j, GE (fun _ : ℝ => D S i j) := fun i j => GEc _
        have hT : ∀ i j, GE (fun t => (Mt t)ᵀ i j) := fun i j => hMGE j i
        have hH : ∀ i j, GE (fun t => (D S * (Mt t)ᵀ * Mt t * D S + (1 - D S) : Matrix
            ((Fin n ⊕ Fin m) ⊕ (Fin n ⊕ Fin m)) ((Fin n ⊕ Fin m) ⊕ (Fin n ⊕ Fin m)) ℝ) i j) := by
          intro i j
          have h1 := GEmatmul (fun t => D S * (Mt t)ᵀ * Mt t) (fun _ => D S)
            (GEmatmul (fun t => D S * (Mt t)ᵀ) (fun t => Mt t)
              (GEmatmul (fun _ => D S) (fun t => (Mt t)ᵀ) hD hT) hMGE) hD i j
          have h2 : GE (fun _ : ℝ => (1 - D S) i j) := GEc _
          exact GEcongr _ _ (GEadd _ _ h1 h2) (Eventually.of_forall fun t => by simp)
        have hv : ∀ i, GE (fun t => (D S *ᵥ ((Mt t)ᵀ *ᵥ rt t)) i) :=
          GEmulVec (fun _ => D S) (fun t => (Mt t)ᵀ *ᵥ rt t) hD
            (GEmulVec (fun t => (Mt t)ᵀ) (fun t => rt t) hT hrGE)
        exact GEmulVec _ _ (GEmatinv _ hH) hv j
      have hev1 : ∀ᶠ t in atTop, ∃ S, Mt t *ᵥ cand S t = rt t ∧ ∀ j, 0 ≤ cand S t j := by
        filter_upwards [hsf] with t ht
        obtain ⟨z, ⟨e1, e2, h1, h2, h3, h4⟩, hg⟩ := SD _ _ _ ht
        have hg0 := WD _ _ _ _ _ _ _ e1 e2 h1 h2 h3 h4
        let v : (Fin n ⊕ Fin m) ⊕ (Fin n ⊕ Fin m) → ℝ :=
          Sum.elim (Sum.elim z.1 z.2.1) (Sum.elim z.2.2.1 z.2.2.2)
        have hv : Mt t *ᵥ v = rt t := (hrow t v).2 ⟨e1, e2, le_antisymm hg hg0⟩
        have hvn : ∀ j, 0 ≤ v j := by
          rintro ((j | i) | (j | i))
          exacts [h1 j, h2 i, h3 j, h4 i]
        exact BFS (Mt t) (rt t) v hv hvn
      clear_value cand D
      obtain ⟨S, hS⟩ : ∃ S, ∃ᶠ t in atTop, Mt t *ᵥ cand S t = rt t ∧ ∀ j, 0 ≤ cand S t j := by
        by_contra hne
        simp only [not_exists, Filter.not_frequently] at hne
        have := (eventually_all.2 hne).and hev1
        obtain ⟨t, h1, S, h2⟩ := this.exists
        exact h1 S h2
      have hev2 : ∀ᶠ t in atTop, Mt t *ᵥ cand S t = rt t ∧ ∀ j, 0 ≤ cand S t j := by
        have hrows : ∀ k, ∀ᶠ t in atTop, (Mt t *ᵥ cand S t) k - rt t k = 0 := by
          intro k
          refine GEfreq0 (fun t => (Mt t *ᵥ cand S t) k - rt t k)
            (GEsub (fun t => (Mt t *ᵥ cand S t) k) (fun t => rt t k)
              (GEmulVec (fun t => Mt t) (fun t => cand S t) hMGE (hcandGE S) k) (hrGE k)) ?_
          exact hS.mono fun t ht => sub_eq_zero.2 (congrFun ht.1 k)
        have hnn : ∀ j, ∀ᶠ t in atTop, 0 ≤ cand S t j := fun j =>
          GEfreqnn _ (hcandGE S j) (hS.mono fun t ht => ht.2 j)
        filter_upwards [eventually_all.2 hrows, eventually_all.2 hnn] with t h1 h2
        exact ⟨funext fun k => sub_eq_zero.1 (h1 k), h2⟩
      have hpex : ∀ j, ∃ q : Puiseux, ∀ᶠ t in atTop, q.eval t = cand S t j :=
        fun j => (hGE (fun t => cand S t j)).1 (hcandGE S j)
      choose p hp using hpex
      have hp' : ∀ᶠ t in atTop, ∀ j, (p j).eval t = cand S t j := eventually_all.2 hp
      have hfeas : ∀ᶠ t in atTop,
          evalMatrix A t *ᵥ evalFun (fun j => p (Sum.inl (Sum.inl j))) t +
            evalFun (fun i => p (Sum.inl (Sum.inr i))) t = evalFun b t ∧
          evalFun (fun j => p (Sum.inr (Sum.inl j))) t -
            (evalMatrix A t)ᵀ *ᵥ evalFun (fun i => p (Sum.inr (Sum.inr i))) t = evalFun c t ∧
          evalFun c t ⬝ᵥ evalFun (fun j => p (Sum.inl (Sum.inl j))) t +
            evalFun b t ⬝ᵥ evalFun (fun i => p (Sum.inr (Sum.inr i))) t = 0 ∧
          ∀ j, 0 ≤ (p j).eval t := by
        filter_upwards [hev2, hp'] with t h1 h2
        have e : ∀ j, (p j).eval t = cand S t j := h2
        have := (hrow t (cand S t)).1 h1.1
        have q1 : evalFun (fun j => p (Sum.inl (Sum.inl j))) t = fun j => cand S t (Sum.inl (Sum.inl j)) :=
          funext fun j => e _
        have q2 : evalFun (fun j => p (Sum.inl (Sum.inr j))) t = fun j => cand S t (Sum.inl (Sum.inr j)) :=
          funext fun j => e _
        have q3 : evalFun (fun j => p (Sum.inr (Sum.inl j))) t = fun j => cand S t (Sum.inr (Sum.inl j)) :=
          funext fun j => e _
        have q4 : evalFun (fun j => p (Sum.inr (Sum.inr j))) t = fun j => cand S t (Sum.inr (Sum.inr j)) :=
          funext fun j => e _
        rw [q1, q2, q3, q4]
        exact ⟨this.1, this.2.1, this.2.2, fun j => (e j).symm ▸ h1.2 j⟩
      have hP : ((fun j => p (Sum.inl (Sum.inl j))), (fun i => p (Sum.inl (Sum.inr i)))) ∈
          kPrimal A b := by
        filter_upwards [hfeas] with t h
        exact ⟨h.1, fun j => h.2.2.2 _, fun i => h.2.2.2 _⟩
      have hD : ((fun j => p (Sum.inr (Sum.inl j))), (fun i => p (Sum.inr (Sum.inr i)))) ∈
          kDual A c := by
        filter_upwards [hfeas] with t h
        exact ⟨h.2.1, fun j => h.2.2.2 _, fun i => h.2.2.2 _⟩
      have hgap : ∀ᶠ t in atTop,
          evalFun c t ⬝ᵥ evalFun zstar.1 t = -(evalFun b t ⬝ᵥ evalFun zstar.2.2.2 t) := by
        obtain ⟨⟨hzP, hzD⟩, hoP, hoD⟩ := hopt
        filter_upwards [hoP _ hP, hoD _ hD, hfeas, hzP, hzD] with t h1 h2 h3 h4 h5
        have := WD _ _ _ _ _ _ _ h4.1 h5.1 h4.2.1 h4.2.2 h5.2.1 h5.2.2
        linarith [h3.2.2.1]
      have hopr : ∀ᶠ t in atTop, OptimalPairReal (evalMatrix A t) (evalFun b t) (evalFun c t)
          (evalPoint zstar t) := by
        obtain ⟨⟨hP, hD⟩, -, -⟩ := hopt
        filter_upwards [hP, hD, hgap] with t hPt hDt hgt
        obtain ⟨hPe, hPx, hPw⟩ := hPt
        obtain ⟨hDe, hDs, hDy⟩ := hDt
        refine ⟨⟨hPe, hDe, hPx, hPw, hDs, hDy⟩, ?_, ?_, hgt⟩
        · intro x w hxw hx hw
          show evalFun c t ⬝ᵥ evalFun zstar.1 t ≤ evalFun c t ⬝ᵥ x
          rw [hgt, ← hDe, sub_dotProduct, mulVec_transpose, ← dotProduct_mulVec, ← hxw,
            add_dotProduct, dotProduct_comm (evalMatrix A t *ᵥ x)]
          have h1 : 0 ≤ evalFun zstar.2.2.1 t ⬝ᵥ x :=
            Finset.sum_nonneg fun j _ => mul_nonneg (hDs j) (hx j)
          have h2 : 0 ≤ w ⬝ᵥ evalFun zstar.2.2.2 t :=
            Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (hDy j)
          linarith
        · intro s y hsy hs hy
          show evalFun b t ⬝ᵥ evalFun zstar.2.2.2 t ≤ evalFun b t ⬝ᵥ y
          have hb' : evalFun b t ⬝ᵥ evalFun zstar.2.2.2 t = - (evalFun c t ⬝ᵥ evalFun zstar.1 t) := by
            linarith
          rw [hb', ← hsy, sub_dotProduct, mulVec_transpose, ← dotProduct_mulVec, ← hPe,
            add_dotProduct]
          have h1 : 0 ≤ s ⬝ᵥ evalFun zstar.1 t :=
            Finset.sum_nonneg fun j _ => mul_nonneg (hs j) (hPx j)
          have h2 : 0 ≤ evalFun zstar.2.1 t ⬝ᵥ y :=
            Finset.sum_nonneg fun j _ => mul_nonneg (hPw j) (hy j)
          rw [dotProduct_comm (evalMatrix A t *ᵥ evalFun zstar.1 t) y]
          linarith
      have hall := hA.and (hb.and (hc.and (hsf.and (hopr.and (hz1.and (hz2.and (hz3.and hz4)))))))
      obtain ⟨a, ha⟩ := eventually_atTop.1 hall
      refine ⟨max a 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun t ht => ?_⟩
      exact ha t (le_trans (le_max_left _ _) ht.le)
