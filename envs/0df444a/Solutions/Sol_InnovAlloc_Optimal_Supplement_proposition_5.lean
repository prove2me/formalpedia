-- Prove2me | solution 1 for InnovAlloc.Optimal.Supplement.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:29:02.060551+00:00
-- url     : https://prove2.me/submissions/8a64bc81-cd59-4ae5-b83a-952dd55050c6

import Mathlib
import Definitions.Def_InnovAlloc_Optimal_Supplement_Comparison

open InnovAlloc
open InnovAlloc.Optimal
open InnovAlloc.Optimal.Supplement

/-- Proposition 5 (p. 19): weak quasiconcavity on the full share interval, unique
attainment, and comparative statics, retaining both endpoints of α ∈ [0,1]. -/
theorem solution :
    (∀ α B : ℝ, 0 ≤ α → α ≤ 1 → 2 < B →
      QuasiconcaveOn ℝ (Set.Ioo (0 : ℝ) 1) (fun γ => profitDuo α γ B) ∧
      (∃! γ, IsDuoShare α B γ) ∧
      IsDuoShare α B (gammaD α B) ∧
      2 < gammaD α B * B ∧
      duoValue α B = duoZProfit α B (gammaD α B * B) ∧
      (∀ z ∈ Set.Ioo (2 : ℝ) B, duoZProfit α B z ≤ duoValue α B)) ∧
    (∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      StrictAntiOn (fun B => gammaD α B) (Set.Ioi (2 : ℝ))) ∧
    (∀ B : ℝ, 2 < B →
      StrictMonoOn (fun α => gammaD α B) (Set.Icc (0 : ℝ) 1)) := by
        have hP0 : ∀ α B γ, γ*B ≤ 2 → profitDuo α γ B = 0 := by
          intro α B γ h; unfold profitDuo; rw [if_pos h]
        have hrep2 : ∀ α B v : ℝ, 0 ≤ α → α ≤ 1 → 0 < B → 0 < v → v < 2 →
            2 < 8/(B*(v*(2*α+(1-α)*v))) * B ∧
            profitDuo α (8/(B*(v*(2*α+(1-α)*v)))) B = (2*α+(1-α)*v - 8/B/v)*(2-v)/2 := by
          intro α B v h0 h1 hB hv0 hv2
          have hw : 0 < 2*α+(1-α)*v := by nlinarith
          have hn : v*(2*α+(1-α)*v) < 4 := by nlinarith
          have hnp : 0 < v*(2*α+(1-α)*v) := by positivity
          have hγB : 8/(B*(v*(2*α+(1-α)*v))) * B = 8/(v*(2*α+(1-α)*v)) := by
            field_simp
          have h2 : 2 < 8/(B*(v*(2*α+(1-α)*v))) * B := by
            rw [hγB, lt_div_iff₀ hnp]; linarith
          refine ⟨h2, ?_⟩
          unfold profitDuo
          rw [if_neg (by linarith)]
          have hsq : (α + (1-α)*v)^2 = α^2 + (1-α)*(v*(2*α+(1-α)*v)) := by ring
          have hval : 0 ≤ α + (1-α)*v := by nlinarith
          generalize hwd : 2*α+(1-α)*v = w at *
          generalize hnd : v*w = n at *
          have harg : (8/(B*n) * α^2 * B - 8*α + 8) / (8/(B*n) * B) = (α + (1-α)*v)^2 := by
            rw [hsq, show 8/(B*n) * α^2 * B = 8/(B*n) * B * α^2 by ring, hγB]
            field_simp; ring
          rw [harg, Real.sqrt_sq hval, ← hnd]
          have hw0 : w ≠ 0 := hw.ne'
          have hv0' : v ≠ 0 := hv0.ne'
          field_simp
          rw [← hwd]; ring
        have hinv : ∀ α B η : ℝ, 0 ≤ α → α ≤ 1 → 0 < B → 0 < η → 2 < η*B →
            ∃ v, 0 < v ∧ v < 2 ∧ η = 8/(B*(v*(2*α+(1-α)*v))) := by
          intro α B η h0 h1 hB hη h2
          have hηB : 0 < η*B := by positivity
          set t := 1/(η*B) with ht
          have ht0 : 0 < t := by positivity
          have ht2 : t < 1/2 := by rw [ht, div_lt_div_iff₀ hηB (by norm_num)]; linarith
          set S := Real.sqrt (α^2 + 8*(1-α)*t) with hS
          have hS0 : 0 ≤ S := Real.sqrt_nonneg _
          have hS2 : S^2 = α^2 + 8*(1-α)*t :=
            Real.sq_sqrt (by linarith [sq_nonneg α, mul_nonneg (sub_nonneg.2 h1) ht0.le])
          have hSa : 0 < S + α := by
            by_contra hc; push Not at hc
            nlinarith [mul_nonneg hS0 h0]
          refine ⟨8*t/(S+α), by positivity, ?_, ?_⟩
          · rw [div_lt_iff₀ hSa]
            by_contra hc; push Not at hc
            nlinarith [mul_self_le_mul_self hS0 (show S ≤ 4*t - α by linarith)]
          · have hβ : (1-α)*(8*t/(S+α)) = S - α := by
              rw [mul_div_assoc', div_eq_iff hSa.ne']; linear_combination -hS2
            rw [hβ, show 2*α + (S-α) = S + α by ring]
            have : 8*t/(S+α)*(S+α) = 8*t := by field_simp
            rw [this, ht]; field_simp
        have hchar : ∀ α B v : ℝ, 0 ≤ α → α ≤ 1 → 2 < B → 0 < v → v < 2 →
            v^2*(2*α-1+(1-α)*v) = 8/B →
            IsDuoShare α B (8/(B*(v*(2*α+(1-α)*v)))) ∧
            ∀ γ, IsDuoShare α B γ → γ = 8/(B*(v*(2*α+(1-α)*v))) := by
          intro α B v h0 h1 hB hv0 hv2 hm
          have hB0 : 0 < B := by linarith
          have hw : 0 < 2*α+(1-α)*v := by
            have := mul_nonneg h0 (sub_nonneg.2 hv2.le); linarith
          have hq : 0 < (1-α)*v + α := by
            have := mul_nonneg (sub_nonneg.2 h1) hv0.le
            rcases eq_or_lt_of_le h0 with h | h
            · rw [← h]; linarith
            · linarith
          have hnp : 0 < v*(2*α+(1-α)*v) := by positivity
          obtain ⟨hγ2, hγP⟩ := hrep2 α B v h0 h1 hB0 hv0 hv2
          have hγ0 : 0 < 8/(B*(v*(2*α+(1-α)*v))) := by positivity
          have hγ1 : 8/(B*(v*(2*α+(1-α)*v))) < 1 := by
            rw [div_lt_one (by positivity)]
            have h8 : 8 = B * (v^2*(2*α-1+(1-α)*v)) := by rw [hm]; field_simp
            rw [h8]
            apply mul_lt_mul_of_pos_left _ hB0
            have e : v*(2*α+(1-α)*v) - v^2*(2*α-1+(1-α)*v) = v*((2-v)*((1-α)*v+α)) := by ring
            have : 0 < v*((2-v)*((1-α)*v+α)) := mul_pos hv0 (mul_pos (by linarith) hq)
            linarith
          -- the core comparison: for any u in (0,2), profit at u ≤ profit at v, with equality iff u = v
          have hcmp : ∀ u, 0 < u → u < 2 →
              (2*α+(1-α)*u - 8/B/u)*(2-u)/2 + (u-v)^2*((1-α) + 2*(8/B)/(u*v^2))/2
                = (2*α+(1-α)*v - 8/B/v)*(2-v)/2 := by
            intro u hu0 hu2
            rw [← hm]
            field_simp
            ring
          have hpos : ∀ u, 0 < u → 0 ≤ (u-v)^2*((1-α) + 2*(8/B)/(u*v^2)) := by
            intro u hu0
            apply mul_nonneg (sq_nonneg _)
            have : 0 ≤ 2*(8/B)/(u*v^2) := by positivity
            linarith
          have hP : 0 < profitDuo α (8/(B*(v*(2*α+(1-α)*v)))) B := by
            rw [hγP]
            have : 0 < 2*α+(1-α)*v - 8/B/v := by
              rw [← hm]
              have : v^2*(2*α-1+(1-α)*v)/v = v*(2*α-1+(1-α)*v) := by field_simp
              rw [this]
              have := mul_pos (sub_pos.2 hv2) hq
              linarith
            have : 0 < 2 - v := by linarith
            positivity
          have hopt : IsDuoShare α B (8/(B*(v*(2*α+(1-α)*v)))) := by
            refine ⟨⟨hγ0, hγ1⟩, ?_⟩
            intro η hη
            by_cases hηB : η*B ≤ 2
            · rw [hP0 α B η hηB]; exact hP.le
            push Not at hηB
            obtain ⟨u, hu0, hu2, rfl⟩ := hinv α B η h0 h1 hB0 hη.1 hηB
            rw [(hrep2 α B u h0 h1 hB0 hu0 hu2).2, hγP, ← hcmp u hu0 hu2]
            have := hpos u hu0
            linarith
          refine ⟨hopt, ?_⟩
          intro γ hγ
          have hle := hγ.2 _ ⟨hγ0, hγ1⟩
          have hγB : 2 < γ*B := by
            by_contra hc; push Not at hc
            rw [hP0 α B γ hc] at hle; linarith
          obtain ⟨u, hu0, hu2, rfl⟩ := hinv α B γ h0 h1 hB0 hγ.1.1 hγB
          have hle2 := hopt.2 _ hγ.1
          rw [(hrep2 α B u h0 h1 hB0 hu0 hu2).2, hγP, ← hcmp u hu0 hu2] at hle hle2
          have hz : (u-v)^2*((1-α) + 2*(8/B)/(u*v^2)) = 0 := le_antisymm (by linarith) (hpos u hu0)
          have h3 : 0 < (1-α) + 2*(8/B)/(u*v^2) := by
            have : 0 < 2*(8/B)/(u*v^2) := by positivity
            linarith
          rcases mul_eq_zero.1 hz with h | h
          · have : u = v := by linarith [pow_eq_zero_iff (n := 2) two_ne_zero |>.1 h]
            rw [this]
          · linarith
        have hexv : ∀ α B : ℝ, 0 ≤ α → α ≤ 1 → 2 < B →
            ∃ v, 0 < v ∧ v < 2 ∧ v^2*(2*α-1+(1-α)*v) = 8/B := by
          intro α B h0 h1 hB
          have hc : ContinuousOn (fun v : ℝ => v^2*(2*α-1+(1-α)*v)) (Set.Icc 0 2) := by fun_prop
          have hmem : 8/B ∈ Set.Ioo ((fun v : ℝ => v^2*(2*α-1+(1-α)*v)) 0)
              ((fun v : ℝ => v^2*(2*α-1+(1-α)*v)) 2) := by
            simp only
            constructor
            · norm_num; positivity
            · rw [div_lt_iff₀ (by linarith)]; nlinarith
          obtain ⟨v, hv, hv'⟩ := intermediate_value_Ioo (by norm_num) hc hmem
          exact ⟨v, hv.1, hv.2, hv'⟩
        have hgD : ∀ α B v : ℝ, 0 ≤ α → α ≤ 1 → 2 < B → 0 < v → v < 2 →
            v^2*(2*α-1+(1-α)*v) = 8/B → gammaD α B = 8/(B*(v*(2*α+(1-α)*v))) := by
          intro α B v h0 h1 hB hv0 hv2 hm
          have hc := hchar α B v h0 h1 hB hv0 hv2 hm
          have hex : ∃ γ, IsDuoShare α B γ := ⟨_, hc.1⟩
          unfold gammaD
          rw [dif_pos hex]
          exact hc.2 _ (Classical.choose_spec hex)
        have hz : ∀ α B γ : ℝ, 0 ≤ α → α ≤ 1 → 0 < B → 0 < γ → 2 < γ*B →
            profitDuo α γ B = duoZProfit α B (γ*B) := by
          intro α B γ h0 h1 hB hγ h2
          unfold profitDuo duoZProfit
          rw [if_neg (by linarith)]
          have hzp : 0 < γ*B := by positivity
          have harg : (γ * α ^ 2 * B - 8 * α + 8) = 8 - 8*α + α^2*(γ*B) := by ring
          rw [harg, Real.sqrt_div' _ hzp.le]
          have hs : Real.sqrt (γ*B) ^ 2 = γ*B := Real.sq_sqrt hzp.le
          have hs0 : 0 < Real.sqrt (γ*B) := Real.sqrt_pos.2 hzp
          generalize Real.sqrt (8 - 8*α + α^2*(γ*B)) = R
          generalize hX : Real.sqrt (γ*B) = X at *
          have hγ0 : γ ≠ 0 := hγ.ne'
          have hB0 : B ≠ 0 := hB.ne'
          have hX0 : X ≠ 0 := hs0.ne'
          rw [← hs]
          field_simp
          linear_combination (4 - α*X^2 - X*R) * hs.symm
        have hE : ∀ α B : ℝ, 0 < B → ∀ u u' : ℝ, 0 < u → 0 < u' →
            (2*α+(1-α)*u - 8/B/u)*(2-u)/2 - (2*α+(1-α)*u' - 8/B/u')*(2-u')/2
              = (u-u')*(2*(1-α) - 2*α - (1-α)*(u+u') + 2*(8/B)/(u*u'))/2 := by
          intro α B hB0 u u' hu hu'
          have : B ≠ 0 := hB0.ne'
          have : u ≠ 0 := hu.ne'
          have : u' ≠ 0 := hu'.ne'
          field_simp; ring
        have hord : ∀ α B v : ℝ, 0 ≤ α → α ≤ 1 → 2 < B → 0 < v → v < 2 → v^2*(2*α-1+(1-α)*v) = 8/B →
            ∀ u1 u2 : ℝ, 0 < u1 → 0 < u2 →
            8/(B*(u1*(2*α+(1-α)*u1))) ≤ 8/(B*(u2*(2*α+(1-α)*u2))) → u2 ≤ u1 := by
          intro α B v h0 h1 hB hv0 hv2 hm
          have hB0 : 0 < B := by linarith
          have ha0 : 0 < 8/B := by positivity
          intro u1 u2 hu1 hu2 hle
          by_contra hc; push Not at hc
          have hn : u1*(2*α+(1-α)*u1) < u2*(2*α+(1-α)*u2) := by
            have e : u2*(2*α+(1-α)*u2) - u1*(2*α+(1-α)*u1) = (u2-u1)*(2*α+(1-α)*(u1+u2)) := by ring
            have : 0 < 2*α+(1-α)*(u1+u2) := by
              have : 0 ≤ (1-α)*(u1+u2) := mul_nonneg (by linarith) (by linarith)
              rcases eq_or_lt_of_le h0 with h | h
              · rw [← h]; linarith
              · linarith
            linarith [mul_pos (sub_pos.2 hc) this]
          have hn1 : 0 < u1*(2*α+(1-α)*u1) := mul_pos hu1 (by
            have : 0 ≤ (1-α)*u1 := mul_nonneg (by linarith) hu1.le
            rcases eq_or_lt_of_le h0 with h | h
            · rw [← h]; linarith
            · linarith)
          have := div_lt_div_of_pos_left (by norm_num : (0:ℝ) < 8) (mul_pos hB0 hn1)
            (mul_lt_mul_of_pos_left hn hB0)
          linarith
        have hinc : ∀ α B v : ℝ, 0 ≤ α → α ≤ 1 → 2 < B → 0 < v → v < 2 → v^2*(2*α-1+(1-α)*v) = 8/B →
            ∀ u u' : ℝ, v ≤ u → u ≤ u' →
            (2*α+(1-α)*u' - 8/B/u')*(2-u')/2 ≤ (2*α+(1-α)*u - 8/B/u)*(2-u)/2 := by
          intro α B v h0 h1 hB hv0 hv2 hm
          have hB0 : 0 < B := by linarith
          have ha0 : 0 < 8/B := by positivity
          have hE := hE α B hB0
          have hE0 : 2*(1-α) - 2*α - (1-α)*(v+v) + 2*(8/B)/(v*v) = 0 := by
            rw [← hm]
            have : v^2*(2*α-1+(1-α)*v)/(v*v) = 2*α-1+(1-α)*v := by
              rw [div_eq_iff (by positivity)]; ring
            rw [mul_div_assoc, this]; ring
          intro u u' hu hu'
          have hu0 : 0 < u := by linarith
          have hu0' : 0 < u' := by linarith
          have hvv : v*v ≤ u*u' := mul_le_mul hu (by linarith) hv0.le hu0.le
          have h1' : 2*(8/B)/(u*u') ≤ 2*(8/B)/(v*v) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hvv
          have hEn : 2*(1-α) - 2*α - (1-α)*(u+u') + 2*(8/B)/(u*u') ≤ 0 := by
            linarith [mul_nonneg (sub_nonneg.2 h1) (show 0 ≤ u + u' - (v+v) by linarith)]
          have := hE u u' hu0 hu0'
          linarith [mul_nonneg (sub_nonneg.2 hu') (neg_nonneg.2 hEn)]
        have hdec : ∀ α B v : ℝ, 0 ≤ α → α ≤ 1 → 2 < B → 0 < v → v < 2 → v^2*(2*α-1+(1-α)*v) = 8/B →
            ∀ u u' : ℝ, 0 < u → u ≤ u' → u' ≤ v →
            (2*α+(1-α)*u - 8/B/u)*(2-u)/2 ≤ (2*α+(1-α)*u' - 8/B/u')*(2-u')/2 := by
          intro α B v h0 h1 hB hv0 hv2 hm
          have hB0 : 0 < B := by linarith
          have ha0 : 0 < 8/B := by positivity
          have hE := hE α B hB0
          have hE0 : 2*(1-α) - 2*α - (1-α)*(v+v) + 2*(8/B)/(v*v) = 0 := by
            rw [← hm]
            have : v^2*(2*α-1+(1-α)*v)/(v*v) = 2*α-1+(1-α)*v := by
              rw [div_eq_iff (by positivity)]; ring
            rw [mul_div_assoc, this]; ring
          intro u u' hu0 hu hu'
          have hu0' : 0 < u' := by linarith
          have hvv : u*u' ≤ v*v := mul_le_mul (by linarith) hu' hu0'.le hv0.le
          have h1' : 2*(8/B)/(v*v) ≤ 2*(8/B)/(u*u') :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hvv
          have hEn : 0 ≤ 2*(1-α) - 2*α - (1-α)*(u+u') + 2*(8/B)/(u*u') := by
            linarith [mul_nonneg (sub_nonneg.2 h1) (show 0 ≤ (v+v) - (u + u') by linarith)]
          have := hE u u' hu0 hu0'
          linarith [mul_nonneg (sub_nonneg.2 hu) hEn]
        have hnn : ∀ α B v : ℝ, 0 ≤ α → α ≤ 1 → 2 < B → 0 < v → v < 2 → v^2*(2*α-1+(1-α)*v) = 8/B →
            ∀ γ, γ < 1 → 0 ≤ profitDuo α γ B := by
          intro α B v h0 h1 hB hv0 hv2 hm
          have hB0 : 0 < B := by linarith
          have ha0 : 0 < 8/B := by positivity
          intro γ hγ1
          by_cases hγB : γ*B ≤ 2
          · rw [hP0 α B γ hγB]
          push Not at hγB
          have hγ0 : 0 < γ := by
            by_contra hc; push Not at hc; nlinarith
          obtain ⟨u, hu0, hu2, rfl⟩ := hinv α B γ h0 h1 hB0 hγ0 hγB
          rw [(hrep2 α B u h0 h1 hB0 hu0 hu2).2]
          have hw : 0 < 2*α+(1-α)*u := by nlinarith
          have hn : 0 < u*(2*α+(1-α)*u) := mul_pos hu0 hw
          have h8 : 8/B < u*(2*α+(1-α)*u) := by
            rw [div_lt_one (mul_pos hB0 hn)] at hγ1
            rw [div_lt_iff₀ hB0]; linarith
          have : 8/B/u < 2*α+(1-α)*u := by
            rw [div_lt_iff₀ hu0]; linarith
          have : 0 < 2 - u := by linarith
          have : 0 ≤ 2*α+(1-α)*u - 8/B/u := by linarith
          positivity
        have hq3 : ∀ α B v : ℝ, 0 ≤ α → α ≤ 1 → 2 < B → 0 < v → v < 2 → v^2*(2*α-1+(1-α)*v) = 8/B →
            ∀ x c y : ℝ, 0 < x → x ≤ c → c ≤ y → y < 1 →
            min (profitDuo α x B) (profitDuo α y B) ≤ profitDuo α c B := by
          intro α B v h0 h1 hB hv0 hv2 hm
          have hB0 : 0 < B := by linarith
          have ha0 : 0 < 8/B := by positivity
          have hord := hord α B v h0 h1 hB hv0 hv2 hm
          have hinc := hinc α B v h0 h1 hB hv0 hv2 hm
          have hdec := hdec α B v h0 h1 hB hv0 hv2 hm
          have hnn := hnn α B v h0 h1 hB hv0 hv2 hm
          obtain ⟨hγs2, hγsP⟩ := hrep2 α B v h0 h1 hB0 hv0 hv2
          intro x c y hx hxc hcy hy
          by_cases hcγ : c ≤ 8/(B*(v*(2*α+(1-α)*v)))
          · refine le_trans (min_le_left _ _) ?_
            by_cases hxB : x*B ≤ 2
            · rw [hP0 α B x hxB]; exact hnn c (by linarith)
            push Not at hxB
            have hcB : 2 < c*B := lt_of_lt_of_le hxB (mul_le_mul_of_nonneg_right hxc hB0.le)
            obtain ⟨ux, hux0, hux2, rfl⟩ := hinv α B x h0 h1 hB0 hx hxB
            obtain ⟨uc, huc0, huc2, rfl⟩ := hinv α B c h0 h1 hB0 (by linarith) hcB
            rw [(hrep2 α B ux h0 h1 hB0 hux0 hux2).2, (hrep2 α B uc h0 h1 hB0 huc0 huc2).2]
            exact hinc uc ux (hord uc v huc0 hv0 hcγ) (hord ux uc hux0 huc0 hxc)
          · push Not at hcγ
            refine le_trans (min_le_right _ _) ?_
            have hcB : 2 < c*B := lt_trans hγs2 (mul_lt_mul_of_pos_right hcγ hB0)
            have hyB : 2 < y*B := lt_of_lt_of_le hcB (mul_le_mul_of_nonneg_right hcy hB0.le)
            have hc0 : 0 < c := by linarith
            obtain ⟨uy, huy0, huy2, rfl⟩ := hinv α B y h0 h1 hB0 (by linarith) hyB
            obtain ⟨uc, huc0, huc2, rfl⟩ := hinv α B c h0 h1 hB0 hc0 hcB
            rw [(hrep2 α B uy h0 h1 hB0 huy0 huy2).2, (hrep2 α B uc h0 h1 hB0 huc0 huc2).2]
            exact hdec uy uc huy0 (hord uc uy huc0 huy0 hcy) (hord v uc hv0 huc0 hcγ.le)
        have hQC : ∀ α B : ℝ, 0 ≤ α → α ≤ 1 → 2 < B →
            QuasiconcaveOn ℝ (Set.Ioo (0 : ℝ) 1) (fun γ => profitDuo α γ B) := by
          intro α B h0 h1 hB
          have hB0 : 0 < B := by linarith
          obtain ⟨v, hv0, hv2, hm⟩ := hexv α B h0 h1 hB
          have ha0 : 0 < 8/B := by positivity
          have hq3 := hq3 α B v h0 h1 hB hv0 hv2 hm
          rw [quasiconcaveOn_iff_min_le]
          refine ⟨convex_Ioo 0 1, ?_⟩
          intro x hx y hy a b ha hb hab
          simp only [smul_eq_mul]
          obtain rfl : a = 1 - b := by linarith
          rcases le_total x y with hxy | hxy
          · have e1 := mul_nonneg hb (sub_nonneg.2 hxy)
            have e2 := mul_nonneg ha (sub_nonneg.2 hxy)
            exact hq3 x _ y hx.1 (by linarith) (by linarith) hy.2
          · rw [min_comm]
            have e1 := mul_nonneg hb (sub_nonneg.2 hxy)
            have e2 := mul_nonneg ha (sub_nonneg.2 hxy)
            exact hq3 y _ x hy.1 (by linarith) (by linarith) hx.2
        refine ⟨?_, ?_, ?_⟩
        · intro α B h0 h1 hB
          have hB0 : 0 < B := by linarith
          obtain ⟨v, hv0, hv2, hm⟩ := hexv α B h0 h1 hB
          have hc := hchar α B v h0 h1 hB hv0 hv2 hm
          have hg := hgD α B v h0 h1 hB hv0 hv2 hm
          have hsh : IsDuoShare α B (gammaD α B) := by rw [hg]; exact hc.1
          have h2 : 2 < gammaD α B * B := by rw [hg]; exact (hrep2 α B v h0 h1 hB0 hv0 hv2).1
          have hdv : duoValue α B = profitDuo α (gammaD α B) B := by
            unfold duoValue; rw [if_neg (by linarith)]
          refine ⟨hQC α B h0 h1 hB, ⟨_, hc.1, hc.2⟩, hsh, h2, ?_, ?_⟩
          · rw [hdv]; exact hz α B _ h0 h1 hB0 hsh.1.1 h2
          · intro z hzI
            have hzB : z / B * B = z := by field_simp
            have hγ0 : 0 < z / B := div_pos (by linarith [hzI.1]) hB0
            have hγ1 : z / B < 1 := by rw [div_lt_one hB0]; exact hzI.2
            rw [← hzB, ← hz α B (z/B) h0 h1 hB0 hγ0 (by rw [hzB]; exact hzI.1), hdv]
            exact hsh.2 _ ⟨hγ0, hγ1⟩
        · intro α h0 h1 B1 hB1 B2 hB2 h12
          simp only [Set.mem_Ioi] at hB1 hB2
          simp only
          obtain ⟨v1, hv10, hv12, hm1⟩ := hexv α B1 h0 h1 hB1
          obtain ⟨v2, hv20, hv22, hm2⟩ := hexv α B2 h0 h1 hB2
          rw [hgD α B1 v1 h0 h1 hB1 hv10 hv12 hm1, hgD α B2 v2 h0 h1 hB2 hv20 hv22 hm2]
          have hB10 : 0 < B1 := by linarith
          have hB20 : 0 < B2 := by linarith
          have ha : 8/B2 < 8/B1 := div_lt_div_of_pos_left (by norm_num) hB10 h12
          have hk1 : 0 < 2*α-1+(1-α)*v1 := by
            have : 0 < v1^2*(2*α-1+(1-α)*v1) := by rw [hm1]; positivity
            exact pos_of_mul_pos_right this (by positivity)
          have hk2 : 0 < 2*α-1+(1-α)*v2 := by
            have : 0 < v2^2*(2*α-1+(1-α)*v2) := by rw [hm2]; positivity
            exact pos_of_mul_pos_right this (by positivity)
          have hv : v2 < v1 := by
            by_contra hc; push Not at hc
            have e1 : 2*α-1+(1-α)*v1 ≤ 2*α-1+(1-α)*v2 := by
              have := mul_le_mul_of_nonneg_left hc (sub_nonneg.2 h1); linarith
            have e2 : v1^2 ≤ v2^2 := pow_le_pow_left₀ hv10.le hc 2
            have : v1^2*(2*α-1+(1-α)*v1) ≤ v2^2*(2*α-1+(1-α)*v2) :=
              mul_le_mul e2 e1 hk1.le (by positivity)
            linarith
          have g1 : 8/(B1*(v1*(2*α+(1-α)*v1))) = v1*(2*α-1+(1-α)*v1)/(2*α+(1-α)*v1) := by
            have hw : 0 < 2*α+(1-α)*v1 := by
              have := mul_nonneg h0 (sub_nonneg.2 hv12.le); linarith
            rw [← div_div, ← hm1, pow_two, mul_assoc, mul_div_mul_left _ _ hv10.ne']
          have g2 : 8/(B2*(v2*(2*α+(1-α)*v2))) = v2*(2*α-1+(1-α)*v2)/(2*α+(1-α)*v2) := by
            have hw : 0 < 2*α+(1-α)*v2 := by
              have := mul_nonneg h0 (sub_nonneg.2 hv22.le); linarith
            rw [← div_div, ← hm2, pow_two, mul_assoc, mul_div_mul_left _ _ hv20.ne']
          rw [g1, g2]
          have hw1 : 0 < 2*α+(1-α)*v1 := by
            have := mul_nonneg h0 (sub_nonneg.2 hv12.le); linarith
          have hw2 : 0 < 2*α+(1-α)*v2 := by
            have := mul_nonneg h0 (sub_nonneg.2 hv22.le); linarith
          rw [div_lt_div_iff₀ hw2 hw1]
          have e : v1*(2*α-1+(1-α)*v1)*(2*α+(1-α)*v2) - v2*(2*α-1+(1-α)*v2)*(2*α+(1-α)*v1)
              = (v1-v2)*(2*α*(2*α-1+(1-α)*v1) + 2*α*(1-α)*v2 + (1-α)^2*v1*v2) := by ring
          have hpos : 0 < 2*α*(2*α-1+(1-α)*v1) + 2*α*(1-α)*v2 + (1-α)^2*v1*v2 := by
            have h1a : 0 ≤ 1 - α := by linarith
            have t2 : 0 ≤ 2*α*(1-α)*v2 := by positivity
            have t3 : 0 ≤ (1-α)^2*v1*v2 := by positivity
            rcases eq_or_lt_of_le h0 with h | h
            · rw [← h]; have := mul_pos hv10 hv20; norm_num; linarith
            · have t1 := mul_pos (mul_pos (two_pos (α := ℝ)) h) hk1
              linarith
          have := mul_pos (sub_pos.2 hv) hpos
          linarith
        · intro B hB α1 hα1 α2 hα2 h12
          simp only [Set.mem_Icc] at hα1 hα2
          simp only
          obtain ⟨v1, hv10, hv12, hm1⟩ := hexv α1 B hα1.1 hα1.2 hB
          obtain ⟨v2, hv20, hv22, hm2⟩ := hexv α2 B hα2.1 hα2.2 hB
          rw [hgD α1 B v1 hα1.1 hα1.2 hB hv10 hv12 hm1, hgD α2 B v2 hα2.1 hα2.2 hB hv20 hv22 hm2]
          have hB0 : 0 < B := by linarith
          obtain ⟨a, ha⟩ : ∃ a, a = 8/B := ⟨_, rfl⟩
          have ha0 : 0 < a := by rw [ha]; positivity
          rw [← ha] at hm1 hm2
          have hk1' : 2*α1-1+(1-α1)*v1 = v1 - 1 + α1*(2-v1) := by ring
          have hk2' : 2*α2-1+(1-α2)*v2 = v2 - 1 + α2*(2-v2) := by ring
          rw [hk1'] at hm1
          rw [hk2'] at hm2
          have hk1 : 0 < v1 - 1 + α1*(2-v1) := by
            have : 0 < v1^2*(v1 - 1 + α1*(2-v1)) := by rw [hm1]; positivity
            exact pos_of_mul_pos_right this (by positivity)
          have hk2 : 0 < v2 - 1 + α2*(2-v2) := by
            have : 0 < v2^2*(v2 - 1 + α2*(2-v2)) := by rw [hm2]; positivity
            exact pos_of_mul_pos_right this (by positivity)
          have hk1l : v1 - 1 + α1*(2-v1) < 1 := by
            have := mul_lt_mul_of_pos_right (lt_of_lt_of_le h12 hα2.2) (sub_pos.2 hv12); linarith
          have hk2l : v2 - 1 + α2*(2-v2) ≤ 1 := by
            have := mul_le_mul_of_nonneg_right hα2.2 (sub_pos.2 hv22).le; linarith
          have hv : v2 < v1 := by
            by_contra hc; push Not at hc
            have e1 : v1 - 1 + α1*(2-v1) < v2 - 1 + α2*(2-v2) := by
              have := mul_nonneg (sub_nonneg.2 hc) (sub_nonneg.2 hα1.2)
              have := mul_pos (sub_pos.2 h12) (sub_pos.2 hv22)
              linarith
            have e2 : v1^2 ≤ v2^2 := pow_le_pow_left₀ hv10.le hc 2
            have : v1^2*(v1 - 1 + α1*(2-v1)) < v2^2*(v2 - 1 + α2*(2-v2)) := by
              calc v1^2*(v1 - 1 + α1*(2-v1)) ≤ v2^2*(v1 - 1 + α1*(2-v1)) :=
                    mul_le_mul_of_nonneg_right e2 hk1.le
                _ < v2^2*(v2 - 1 + α2*(2-v2)) := mul_lt_mul_of_pos_left e1 (by positivity)
            linarith
          have hprod : a < v1*v2 := by
            have hsq : a^2 < (v1*v2)^2 := by
              have e : a^2 = (v1*v2)^2 * ((v1 - 1 + α1*(2-v1))*(v2 - 1 + α2*(2-v2))) := by
                calc a^2 = a*a := by ring
                  _ = v1^2*(v1 - 1 + α1*(2-v1)) * (v2^2*(v2 - 1 + α2*(2-v2))) := by rw [hm1, hm2]
                  _ = _ := by ring
              rw [e]
              have hP : (v1 - 1 + α1*(2-v1))*(v2 - 1 + α2*(2-v2)) < 1 := by
                have := mul_lt_mul_of_pos_right hk1l hk2; linarith
              have hX : 0 < (v1*v2)^2 := by positivity
              calc (v1*v2)^2 * ((v1 - 1 + α1*(2-v1))*(v2 - 1 + α2*(2-v2))) < (v1*v2)^2 * 1 :=
                    mul_lt_mul_of_pos_left hP hX
                _ = (v1*v2)^2 := mul_one _
            exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
          have hn1 : v1*(2*α1+(1-α1)*v1) = v1 + a/v1 := by
            have : a/v1 = v1*(v1 - 1 + α1*(2-v1)) := by rw [div_eq_iff hv10.ne', ← hm1]; ring
            rw [this]; ring
          have hn2 : v2*(2*α2+(1-α2)*v2) = v2 + a/v2 := by
            have : a/v2 = v2*(v2 - 1 + α2*(2-v2)) := by rw [div_eq_iff hv20.ne', ← hm2]; ring
            rw [this]; ring
          rw [hn1, hn2]
          have hlt : v2 + a/v2 < v1 + a/v1 := by
            have e : v1 + a/v1 - (v2 + a/v2) = (v1-v2)*(v1*v2-a)/(v1*v2) := by
              have : v1 ≠ 0 := hv10.ne'
              have : v2 ≠ 0 := hv20.ne'
              field_simp; ring
            have : 0 < (v1-v2)*(v1*v2-a)/(v1*v2) := by
              apply div_pos (mul_pos (by linarith) (by linarith)) (by positivity)
            linarith
          have hp2 : 0 < v2 + a/v2 := by have := div_pos ha0 hv20; linarith
          exact div_lt_div_of_pos_left (by norm_num) (mul_pos hB0 hp2) (mul_lt_mul_of_pos_left hlt hB0)
