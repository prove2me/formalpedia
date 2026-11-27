-- Prove2me | solution 1 for LogBarrierIPM.Iterations.Supplement.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:03:59.110026+00:00
-- url     : https://prove2.me/submissions/02de2232-e4a2-4919-8f0b-22d1c58b893b

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_Supplement_PuiseuxGeometry

open Filter Matrix

open LogBarrierIPM
open LogBarrierIPM.Iterations
open LogBarrierIPM.Iterations.Supplement

open LogBarrierIPM.Curvature

theorem solution :
    (∀ f g : Puiseux, KNonneg f → KNonneg g → KLe f g → f.val ≤ g.val) ∧
    (∀ a : WithBot ℝ, ∃ f : Puiseux, KNonneg f ∧ f.val = a) ∧
    (∃ z : Puiseux, (∀ a, z.coeff a = 0) ∧ z.val = ⊥) ∧
    (∃ o : Puiseux, (∀ᶠ t in atTop, o.eval t = 1) ∧ o.val = 0) ∧
    (∀ f g : Puiseux, KNonneg f → KNonneg g →
      (∃ h : Puiseux, ∀ᶠ t in atTop, h.eval t = f.eval t + g.eval t) ∧
      ∀ h : Puiseux, (∀ᶠ t in atTop, h.eval t = f.eval t + g.eval t) →
        KNonneg h ∧ h.val = max f.val g.val) ∧
    (∀ f g : Puiseux, KNonneg f → KNonneg g →
      (∃ h : Puiseux, ∀ᶠ t in atTop, h.eval t = f.eval t * g.eval t) ∧
      ∀ h : Puiseux, (∀ᶠ t in atTop, h.eval t = f.eval t * g.eval t) →
        KNonneg h ∧ h.val = f.val + g.val) ∧
    (∀ f : Puiseux, KPositive f →
      (∃ h : Puiseux, ∀ᶠ t in atTop, f.eval t * h.eval t = 1) ∧
      ∀ h : Puiseux, (∀ᶠ t in atTop, f.eval t * h.eval t = 1) →
        KPositive h ∧ f.val + h.val = 0) := by
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
            nlinarith
          have TH : ∀ (f : Puiseux) (m : ℝ), KNonneg f → f.coeff m ≠ 0 →
              (∀ α, f.coeff α ≠ 0 → α ≤ m) →
              ∀ᶠ t in atTop, f.coeff m / 2 * t ^ m ≤ f.eval t ∧ f.eval t ≤ 2 * f.coeff m * t ^ m := by
            intro f m hf hm hub
            have hc := POS f m hf hm hub
            filter_upwards [LEAD f m hm hub (f.coeff m / 2) (by linarith), eventually_gt_atTop 0]
              with t h1 h3
            have hp : 0 < t ^ m := Real.rpow_pos_of_pos h3 _
            have := abs_le.1 h1
            constructor <;> nlinarith
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
              nlinarith [h1.1]
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
              rw [e]; nlinarith
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
              nlinarith [h1.2]
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
                    mul_le_mul h3.2 h4.2 (by nlinarith [h4.1]) (by positivity)
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
                    mul_le_mul h3.1 h4.1 (by positivity) (by nlinarith [h3.1])
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
          refine ⟨P1, ?_, ⟨z0, hz0c, hz0v⟩, ?_, ?_, ?_, ?_⟩
          · intro a
            rcases WB a with rfl | ⟨r, rfl⟩
            · exact ⟨z0, Eventually.of_forall (fun t => by rw [Z z0 hz0c t]), hz0v⟩
            · obtain ⟨p, hpn, hpv, _⟩ := MONP 1 r one_pos
              exact ⟨p, hpn, hpv⟩
          · obtain ⟨p, _, hpv, hpe⟩ := MONP 1 0 one_pos
            exact ⟨p, Eventually.of_forall (fun t => by rw [hpe]; simp), by rw [hpv]; rfl⟩
          · intro f g hf hg
            exact ⟨ADDE f g, ADDU f g hf hg⟩
          · intro f g hf hg
            refine ⟨?_, MULU f g hf hg⟩
            obtain ⟨h, _, hk⟩ := MUL f g
            obtain ⟨ρf, hρf, hsf⟩ := f.abs_summable
            obtain ⟨ρg, hρg, hsg⟩ := g.abs_summable
            refine ⟨h, ?_⟩
            filter_upwards [eventually_gt_atTop (max ρf ρg)] with t ht
            have ht1 : ρf < t := lt_of_le_of_lt (le_max_left _ _) ht
            have ht2 : ρg < t := lt_of_le_of_lt (le_max_right _ _) ht
            exact (hk t (by linarith) (hsf t ht1) (hsg t ht2)).2.2
          · intro f hf
            refine ⟨INV f hf, fun h hh => ?_⟩
            have hfn : KNonneg f := hf.mono (fun t ht => ht.le)
            have hp : KPositive h := by
              filter_upwards [hh, hf] with t h1 h2
              exact pos_of_mul_pos_right (by rw [h1]; exact one_pos) h2.le
            refine ⟨hp, ?_⟩
            obtain ⟨o, _, hov, hoe⟩ := MONP 1 0 one_pos
            have := (MULU f h hfn (hp.mono (fun t ht => ht.le)) o (by
              filter_upwards [hh] with t ht; rw [ht, hoe]; simp)).2
            rw [hov] at this
            rw [← this]; rfl
