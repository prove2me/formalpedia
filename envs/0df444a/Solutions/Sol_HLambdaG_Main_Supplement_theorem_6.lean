-- Prove2me | solution 1 for HLambdaG.Main.Supplement.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:25:58.040103+00:00
-- url     : https://prove2.me/submissions/e21bc86a-9cd4-4dc3-a375-c9ae226bea00

import Mathlib
import Definitions.Def_HLambdaG_Main_Supplement_Continuous

open scoped NNReal

open HLambdaG
open HLambdaG.Main
open HLambdaG.Main.Supplement

open Filter Topology MeasureTheory

/-- Theorem 6, p. 642: in the continuous `L = λW` setting ((13) with (25)), if
`s⁻¹T₁(s) → λ⁻¹` and `s⁻¹w(s) → 0`, then `G(s) → W` for some finite `W` iff `H(t) → L` for
some finite `L`, in which case `L = λW`. -/
theorem solution (τ₁ : TimeChange) (w : ℝ≥0 → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (hw_nonneg : ∀ u, 0 ≤ w u)
    (hw_rcont : ∀ u, ContinuousWithinAt w (Set.Ici u) u)
    (hw_int : ∀ s : ℝ, IntegrableOn (fun u : ℝ => w u.toNNReal) (Set.Icc 0 s))
    (hT₁ : Tendsto (fun s : ℝ≥0 => (τ₁.T s : ℝ) / (s : ℝ)) atTop (𝓝 lam⁻¹))
    (hw : Tendsto (fun s : ℝ≥0 => w s / (s : ℝ)) atTop (𝓝 0)) :
    ((∃ W : ℝ, Tendsto (contG w) atTop (𝓝 W)) ↔
      (∃ L : ℝ, Tendsto (contH τ₁ w) atTop (𝓝 L))) ∧
      ∀ W L : ℝ, Tendsto (contG w) atTop (𝓝 W) →
        Tendsto (contH τ₁ w) atTop (𝓝 L) → L = lam * W := by
          have hT'meas : Measurable (fun u : ℝ => (τ₁.T u.toNNReal : ℝ)) := by
            apply Monotone.measurable
            intro x y hxy
            exact_mod_cast τ₁.mono (Real.toNNReal_le_toNNReal hxy)
          have hF_nn : ∀ t : ℝ≥0, ∀ u : ℝ, 0 ≤ contF τ₁ w u.toNNReal t := fun t u =>
            le_min (hw_nonneg _) (le_max_left _ _)
          have hF_le : ∀ t : ℝ≥0, ∀ u : ℝ, contF τ₁ w u.toNNReal t ≤ w u.toNNReal := fun t u =>
            min_le_left _ _
          have hF_int : ∀ t : ℝ≥0, ∀ S : ℝ,
              IntegrableOn (fun u : ℝ => contF τ₁ w u.toNNReal t) (Set.Icc 0 S) := by
            intro t S
            refine Integrable.mono' (hw_int S) ?_ ?_
            · have h1 : AEMeasurable (fun u : ℝ => w u.toNNReal) (volume.restrict (Set.Icc 0 S)) :=
                (hw_int S).aestronglyMeasurable.aemeasurable
              have h2 : Measurable (fun u : ℝ => max 0 ((t:ℝ) - (τ₁.T u.toNNReal : ℝ))) :=
                measurable_const.max (measurable_const.sub hT'meas)
              exact (h1.min h2.aemeasurable).aestronglyMeasurable
            · exact Filter.Eventually.of_forall (fun u => by
                rw [Real.norm_eq_abs, abs_of_nonneg (hF_nn t u)]; exact hF_le t u)
          have hwII : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
              IntervalIntegrable (fun u : ℝ => w u.toNNReal) volume x y := by
            have h0 : ∀ y : ℝ, 0 ≤ y → IntervalIntegrable (fun u : ℝ => w u.toNNReal) volume 0 y :=
              fun y hy => (intervalIntegrable_iff_integrableOn_Icc_of_le hy).2 (hw_int y)
            intro x y hx hy
            exact (h0 x hx).symm.trans (h0 y hy)
          have hFII : ∀ t : ℝ≥0, ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
              IntervalIntegrable (fun u : ℝ => contF τ₁ w u.toNNReal t) volume x y := by
            intro t
            have h0 : ∀ y : ℝ, 0 ≤ y →
                IntervalIntegrable (fun u : ℝ => contF τ₁ w u.toNNReal t) volume 0 y :=
              fun y hy => (intervalIntegrable_iff_integrableOn_Icc_of_le hy).2 (hF_int t y)
            intro x y hx hy
            exact (h0 x hx).symm.trans (h0 y hy)
          -- I and A
          obtain ⟨I, hIdef⟩ : ∃ I : ℝ → ℝ, ∀ s, I s = ∫ u in (0:ℝ)..s, w u.toNNReal := ⟨_, fun _ => rfl⟩
          obtain ⟨A, hAdef⟩ : ∃ A : ℝ≥0 → ℝ, ∀ t,
              A t = ∫ u in Set.Ici (0:ℝ), contF τ₁ w u.toNNReal t := ⟨_, fun _ => rfl⟩
          have hG : ∀ s : ℝ≥0, contG w s = (s:ℝ)⁻¹ * I s := by
            intro s
            rw [hIdef, intervalIntegral.integral_of_le (NNReal.coe_nonneg s), contG, integral_Icc_eq_integral_Ioc]
          have hH : ∀ t : ℝ≥0, contH τ₁ w t = (t:ℝ)⁻¹ * A t := by
            intro t; rw [hAdef]; rfl
          -- key sandwich
          have hKS : ∀ a b : ℝ, 0 < a → a < lam → lam < b → ∃ C : ℝ,
              ∀ᶠ t : ℝ≥0 in atTop, I (a * t) - C ≤ A t ∧ A t ≤ I (b * t) := by
            intro a b ha hal hlb
            have hb : (0:ℝ) < b := hlam.trans hlb
            have hsum : Tendsto (fun s : ℝ≥0 => ((τ₁.T s : ℝ) + w s) / (s:ℝ)) atTop (𝓝 lam⁻¹) := by
              have := hT₁.add hw
              simp only [add_zero] at this
              refine this.congr (fun s => ?_)
              rw [add_div]
            have h1 : lam⁻¹ < a⁻¹ := inv_strictAnti₀ ha hal
            have h2 : b⁻¹ < lam⁻¹ := inv_strictAnti₀ hlam hlb
            have ev1 : ∀ᶠ s : ℝ≥0 in atTop, ((τ₁.T s : ℝ) + w s) / (s:ℝ) < a⁻¹ :=
              hsum.eventually (gt_mem_nhds h1)
            have ev2 : ∀ᶠ s : ℝ≥0 in atTop, b⁻¹ < (τ₁.T s : ℝ) / (s:ℝ) :=
              hT₁.eventually (lt_mem_nhds h2)
            have ev3 : ∀ᶠ s : ℝ≥0 in atTop, (0:ℝ≥0) < s := eventually_gt_atTop 0
            obtain ⟨u0, hu0⟩ := eventually_atTop.1 (ev1.and ev3)
            obtain ⟨u1, hu1⟩ := eventually_atTop.1 (ev2.and ev3)
            have hlow : ∀ u : ℝ, (u0:ℝ) ≤ u → (τ₁.T u.toNNReal : ℝ) + w u.toNNReal ≤ a⁻¹ * u := by
              intro u hu
              have hu' : u0 ≤ u.toNNReal := by
                rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (u0.2.trans hu)]; exact hu
              obtain ⟨h, hpos⟩ := hu0 _ hu'
              have hpos' : (0:ℝ) < (u.toNNReal : ℝ) := by exact_mod_cast hpos
              rw [div_lt_iff₀ hpos', Real.coe_toNNReal _ (u0.2.trans hu)] at h
              linarith
            have hup : ∀ u : ℝ, (u1:ℝ) ≤ u → b⁻¹ * u < (τ₁.T u.toNNReal : ℝ) := by
              intro u hu
              have hu' : u1 ≤ u.toNNReal := by
                rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (u1.2.trans hu)]; exact hu
              obtain ⟨h, hpos⟩ := hu1 _ hu'
              have hpos' : (0:ℝ) < (u.toNNReal : ℝ) := by exact_mod_cast hpos
              rw [lt_div_iff₀ hpos', Real.coe_toNNReal _ (u1.2.trans hu)] at h
              linarith
            refine ⟨I u0, ?_⟩
            filter_upwards [eventually_ge_atTop (Real.toNNReal (u0 / a)),
              eventually_ge_atTop (Real.toNNReal (u1 / b))] with t ht0 ht1
            have ht0' : (u0:ℝ) / a ≤ t := by
              have := (Real.toNNReal_le_iff_le_coe).1 ht0; exact this
            have ht1' : (u1:ℝ) / b ≤ t := (Real.toNNReal_le_iff_le_coe).1 ht1
            have hat : (u0:ℝ) ≤ a * t := by rwa [div_le_iff₀' ha] at ht0'
            have hbt : (u1:ℝ) ≤ b * t := by rwa [div_le_iff₀' hb] at ht1'
            have ht : (0:ℝ) ≤ t := t.2
            have hab : a * (t:ℝ) ≤ b * t := mul_le_mul_of_nonneg_right (by linarith) ht
            have hat0 : 0 ≤ a * (t:ℝ) := mul_nonneg ha.le ht
            have hbt0 : 0 ≤ b * (t:ℝ) := mul_nonneg hb.le ht
            have hAeq : A t = ∫ u in (0:ℝ)..(b * t), contF τ₁ w u.toNNReal t := by
              rw [hAdef, intervalIntegral.integral_of_le hbt0, ← integral_Icc_eq_integral_Ioc]
              apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ici
              · exact Set.Icc_subset_Ici_self
              · intro u hu
                have hu2 : b * (t:ℝ) < u := by
                  simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_Icc, not_and, not_le] at hu
                  exact hu.2 hu.1
                have h3 := hup u (by linarith)
                have h4 : (t:ℝ) < τ₁.T u.toNNReal := by
                  calc (t:ℝ) = b⁻¹ * (b * t) := by field_simp
                    _ < b⁻¹ * u := mul_lt_mul_of_pos_left hu2 (inv_pos.2 hb)
                    _ < _ := h3
                show min (w u.toNNReal) (max 0 ((t:ℝ) - τ₁.T u.toNNReal)) = 0
                rw [max_eq_left (by linarith), min_eq_right (hw_nonneg _)]
            constructor
            · rw [hAeq]
              have e1 := intervalIntegral.integral_add_adjacent_intervals
                (hFII t 0 u0 le_rfl u0.2) (hFII t u0 (a*t) u0.2 hat0)
              have e2 := intervalIntegral.integral_add_adjacent_intervals
                (hFII t 0 (a*t) le_rfl hat0) (hFII t (a*t) (b*t) hat0 hbt0)
              have e3 := intervalIntegral.integral_add_adjacent_intervals
                (hwII 0 u0 le_rfl u0.2) (hwII u0 (a*t) u0.2 hat0)
              have e4 : ∫ u in (u0:ℝ)..(a*t), contF τ₁ w u.toNNReal t =
                  ∫ u in (u0:ℝ)..(a*t), w u.toNNReal := by
                apply intervalIntegral.integral_congr
                intro u hu
                rw [Set.uIcc_of_le hat] at hu
                have h5 := hlow u hu.1
                have h6 : a⁻¹ * u ≤ t := by
                  calc a⁻¹ * u ≤ a⁻¹ * (a * t) := mul_le_mul_of_nonneg_left hu.2 (inv_nonneg.2 ha.le)
                    _ = t := by field_simp
                show min (w u.toNNReal) (max 0 ((t:ℝ) - τ₁.T u.toNNReal)) = w u.toNNReal
                exact min_eq_left (le_max_of_le_right (by linarith))
              have n1 : 0 ≤ ∫ u in (0:ℝ)..u0, contF τ₁ w u.toNNReal t :=
                intervalIntegral.integral_nonneg u0.2 (fun u _ => hF_nn t u)
              have n2 : 0 ≤ ∫ u in (a * t)..(b*t), contF τ₁ w u.toNNReal t :=
                intervalIntegral.integral_nonneg hab (fun u _ => hF_nn t u)
              rw [hIdef, hIdef]
              linarith
            · rw [hAeq, hIdef]
              exact intervalIntegral.integral_mono_on hbt0 (hFII t 0 _ le_rfl hbt0)
                (hwII 0 _ le_rfl hbt0) (fun u _ => hF_le t u)
          have hcoeTop : Tendsto (fun t : ℝ≥0 => (t:ℝ)) atTop atTop := NNReal.tendsto_coe_atTop.2 tendsto_id
          have hGr : ∀ W, Tendsto (contG w) atTop (𝓝 W) →
              Tendsto (fun s : ℝ => s⁻¹ * I s) atTop (𝓝 W) := by
            intro W hW
            refine (hW.comp tendsto_real_toNNReal_atTop).congr' ?_
            filter_upwards [eventually_ge_atTop 0] with s hs
            simp only [Function.comp, hG, Real.coe_toNNReal _ hs]
          have D1 : ∀ W, Tendsto (contG w) atTop (𝓝 W) →
              Tendsto (contH τ₁ w) atTop (𝓝 (lam * W)) := by
            intro W hW
            have hGW := hGr W hW
            have c1 : Tendsto (fun a : ℝ => a * W) (𝓝 lam) (𝓝 (lam * W)) :=
              ((continuous_id.mul continuous_const).tendsto lam)
            rw [tendsto_order]
            constructor
            · intro x hx
              have ev : ∀ᶠ a in 𝓝[<] lam, (x < a * W ∧ 0 < a) ∧ a < lam :=
                (((c1.eventually (lt_mem_nhds hx)).and (lt_mem_nhds hlam)).filter_mono
                  nhdsWithin_le_nhds).and self_mem_nhdsWithin
              obtain ⟨a, ⟨hxa, ha0⟩, hal⟩ := ev.exists
              obtain ⟨C, hC⟩ := hKS a (lam + 1) ha0 hal (by linarith)
              have c2 : Tendsto (fun t : ℝ≥0 => a * ((a * t)⁻¹ * I (a * t)) - C * (t:ℝ)⁻¹) atTop
                  (𝓝 (a * W - C * 0)) :=
                ((hGW.comp (hcoeTop.const_mul_atTop ha0)).const_mul a).sub
                  ((tendsto_inv_atTop_zero.comp hcoeTop).const_mul C)
              filter_upwards [c2.eventually (lt_mem_nhds (by simpa using hxa)), hC,
                eventually_gt_atTop 0] with t h1 h2 h3
              have ht : (0:ℝ) < t := h3
              rw [hH]
              have e : a * ((a * t)⁻¹ * I (a * t)) - C * (t:ℝ)⁻¹ = (t:ℝ)⁻¹ * (I (a*t) - C) := by
                field_simp
              rw [e] at h1
              exact lt_of_lt_of_le h1 (mul_le_mul_of_nonneg_left h2.1 (inv_nonneg.2 ht.le))
            · intro x hx
              have ev : ∀ᶠ b in 𝓝[>] lam, b * W < x ∧ lam < b :=
                ((c1.eventually (gt_mem_nhds hx)).filter_mono
                  nhdsWithin_le_nhds).and self_mem_nhdsWithin
              obtain ⟨b, hbx, hlb⟩ := ev.exists
              have hb : 0 < b := hlam.trans hlb
              obtain ⟨C, hC⟩ := hKS (lam / 2) b (by positivity) (by linarith) hlb
              have c2 : Tendsto (fun t : ℝ≥0 => b * ((b * t)⁻¹ * I (b * t))) atTop (𝓝 (b * W)) :=
                ((hGW.comp (hcoeTop.const_mul_atTop hb)).const_mul b)
              filter_upwards [c2.eventually (gt_mem_nhds hbx), hC,
                eventually_gt_atTop 0] with t h1 h2 h3
              have ht : (0:ℝ) < t := h3
              rw [hH]
              have e : b * ((b * t)⁻¹ * I (b * t)) = (t:ℝ)⁻¹ * I (b*t) := by
                field_simp
              rw [e] at h1
              exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h2.2 (inv_nonneg.2 ht.le)) h1
          have hsc : ∀ c : ℝ, 0 < c → Tendsto (fun s : ℝ≥0 => (((s:ℝ) / c).toNNReal)) atTop atTop :=
            fun c hc => tendsto_real_toNNReal_atTop.comp (hcoeTop.atTop_div_const hc)
          have D2 : ∀ L, Tendsto (contH τ₁ w) atTop (𝓝 L) →
              Tendsto (contG w) atTop (𝓝 (L / lam)) := by
            intro L hL
            have c1 : Tendsto (fun b : ℝ => L / b) (𝓝 lam) (𝓝 (L / lam)) :=
              (continuousAt_const.div continuousAt_id hlam.ne').tendsto
            rw [tendsto_order]
            constructor
            · intro x hx
              have ev : ∀ᶠ b in 𝓝[>] lam, x < L / b ∧ lam < b :=
                ((c1.eventually (lt_mem_nhds hx)).filter_mono
                  nhdsWithin_le_nhds).and self_mem_nhdsWithin
              obtain ⟨b, hxb, hlb⟩ := ev.exists
              have hb : 0 < b := hlam.trans hlb
              obtain ⟨C, hC⟩ := hKS (lam / 2) b (by positivity) (by linarith) hlb
              have c2 : Tendsto (fun s : ℝ≥0 => b⁻¹ * contH τ₁ w (((s:ℝ) / b).toNNReal)) atTop
                  (𝓝 (b⁻¹ * L)) := (hL.comp (hsc b hb)).const_mul _
              filter_upwards [c2.eventually (lt_mem_nhds (by rwa [inv_mul_eq_div])),
                (hsc b hb).eventually hC, eventually_gt_atTop 0] with s h1 h2 h3
              have hs : (0:ℝ) < s := h3
              have e : ((((s:ℝ) / b).toNNReal : ℝ≥0) : ℝ) = s / b := Real.coe_toNNReal _ (by positivity)
              have e2 : b * ((s:ℝ) / b) = s := by field_simp
              rw [e, e2] at h2
              rw [hH, e] at h1
              rw [hG]
              have e3 : b⁻¹ * (((s:ℝ) / b)⁻¹ * A (((s:ℝ) / b).toNNReal)) =
                  (s:ℝ)⁻¹ * A (((s:ℝ) / b).toNNReal) := by
                field_simp
              rw [e3] at h1
              exact lt_of_lt_of_le h1 (mul_le_mul_of_nonneg_left h2.2 (inv_nonneg.2 hs.le))
            · intro x hx
              have ev : ∀ᶠ a in 𝓝[<] lam, (L / a < x ∧ 0 < a) ∧ a < lam :=
                (((c1.eventually (gt_mem_nhds hx)).and (lt_mem_nhds hlam)).filter_mono
                  nhdsWithin_le_nhds).and self_mem_nhdsWithin
              obtain ⟨a, ⟨hax, ha0⟩, hal⟩ := ev.exists
              obtain ⟨C, hC⟩ := hKS a (lam + 1) ha0 hal (by linarith)
              have c2 : Tendsto (fun s : ℝ≥0 => a⁻¹ * contH τ₁ w (((s:ℝ) / a).toNNReal) + C * (s:ℝ)⁻¹)
                  atTop (𝓝 (a⁻¹ * L + C * 0)) :=
                ((hL.comp (hsc a ha0)).const_mul _).add
                  ((tendsto_inv_atTop_zero.comp hcoeTop).const_mul C)
              filter_upwards [c2.eventually (gt_mem_nhds (by rwa [mul_zero, add_zero, inv_mul_eq_div])),
                (hsc a ha0).eventually hC, eventually_gt_atTop 0] with s h1 h2 h3
              have hs : (0:ℝ) < s := h3
              have e : ((((s:ℝ) / a).toNNReal : ℝ≥0) : ℝ) = s / a := Real.coe_toNNReal _ (by positivity)
              have e2 : a * ((s:ℝ) / a) = s := by field_simp
              rw [e, e2] at h2
              rw [hH, e] at h1
              rw [hG]
              have e3 : a⁻¹ * (((s:ℝ) / a)⁻¹ * A (((s:ℝ) / a).toNNReal)) + C * (s:ℝ)⁻¹ =
                  (s:ℝ)⁻¹ * (A (((s:ℝ) / a).toNNReal) + C) := by
                field_simp
              rw [e3] at h1
              refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left (by linarith [h2.1]) (inv_nonneg.2 hs.le)) h1
          refine ⟨⟨fun ⟨W, hW⟩ => ⟨_, D1 W hW⟩, fun ⟨L, hL⟩ => ⟨_, D2 L hL⟩⟩,
            fun W L hW hL => tendsto_nhds_unique hL (D1 W hW)⟩
