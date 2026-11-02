-- Prove2me | solution 1 for NaiveLearn.OverMatch.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T12:49:48.326271+00:00
-- url     : https://prove2.me/submissions/d92ef8e1-4611-4cfb-996c-a73a0abc26f3

import Mathlib
import Definitions.Def_NaiveLearn_OverMatch_Model
import Theorems.Thm_NaiveLearn_OverMatch_lemma_6

open MeasureTheory ProbabilityTheory Filter Topology
open NaiveLearn.OverMatch

lemma NL_actOf_cases (σ : ℝ → ℝ) (u : unitInterval) (y : ℝ) :
    actOf σ u y = 0 ∨ actOf σ u y = 1 := by
  unfold actOf; split_ifs <;> simp

lemma NL_belief_succ {m : ℕ} (σ : ℝ → ℝ) (ε : ℝ) (W : Matrix (Fin m) (Fin m) ℝ)
    (x1 : Fin m → ℝ) (U : Coins m) (t : ℕ) (i : Fin m) :
    beliefAct σ ε W x1 U (t + 1) i =
      (1 - ε) * beliefAct σ ε W x1 U t i + ε * ∑ j, W i j * action σ ε W x1 U t j := by
  simp [beliefAct, action, Matrix.mulVec, dotProduct]

/-- If the beliefs converge to `1`, every agent eventually plays `1`. -/
lemma NL_eventually_one {m : ℕ} (σ : ℝ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (W : Matrix (Fin m) (Fin m) ℝ) (hW : IsWeightMatrix W)
    (x1 : Fin m → ℝ) (U : Coins m)
    (h : Tendsto (beliefAct σ ε W x1 U) atTop (𝓝 1)) :
    ∃ t0 : ℕ, ∀ t ≥ t0, ∀ i, action σ ε W x1 U t i = 1 := by
  have hev : ∀ᶠ t in atTop, ∀ i, action σ ε W x1 U t i = 1 := by
    rw [eventually_all]
    intro i
    have hi : Tendsto (fun t => beliefAct σ ε W x1 U t i) atTop (𝓝 1) :=
      (continuous_apply i).continuousAt.tendsto.comp h
    have hi1 : Tendsto (fun t => beliefAct σ ε W x1 U (t + 1) i) atTop (𝓝 1) :=
      hi.comp (tendsto_add_atTop_nat 1)
    have hd : Tendsto (fun t => beliefAct σ ε W x1 U (t + 1) i -
        (1 - ε) * beliefAct σ ε W x1 U t i) atTop (𝓝 (1 - (1 - ε) * 1)) :=
      hi1.sub (hi.const_mul _)
    have hWii : 0 < W i i := hW.2.2 i
    have hlt : ε * (1 - W i i) < 1 - (1 - ε) * 1 := by nlinarith
    filter_upwards [hd.eventually (lt_mem_nhds hlt)] with t ht
    rcases NL_actOf_cases σ (U t i) (beliefAct σ ε W x1 U t i) with h0 | h1
    · exfalso
      have h0' : action σ ε W x1 U t i = 0 := h0
      have hS : ∑ j, W i j * action σ ε W x1 U t j ≤ 1 - W i i := by
        have : ∀ j, W i j * action σ ε W x1 U t j ≤ W i j * (1 - if j = i then 1 else 0) := by
          intro j
          have hWij : 0 ≤ W i j := Matrix.nonneg_of_mem_rowStochastic hW.1
          by_cases hji : j = i
          · subst hji; simp [h0']
          · simp only [hji, if_false, sub_zero, mul_one]
            rcases NL_actOf_cases σ (U t j) (beliefAct σ ε W x1 U t j) with a | a <;>
              simp only [action, a] <;> nlinarith
        calc ∑ j, W i j * action σ ε W x1 U t j
            ≤ ∑ j, W i j * (1 - if j = i then 1 else 0) := Finset.sum_le_sum fun j _ => this j
          _ = 1 - W i i := by
            simp [mul_sub, Finset.sum_sub_distrib, Matrix.sum_row_of_mem_rowStochastic hW.1]
      rw [NL_belief_succ] at ht
      nlinarith
    · exact h1
  obtain ⟨t0, ht0⟩ := eventually_atTop.1 hev
  exact ⟨t0, ht0⟩

/-- If the beliefs converge to `0`, every agent eventually plays `0`. -/
lemma NL_eventually_zero {m : ℕ} (σ : ℝ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (W : Matrix (Fin m) (Fin m) ℝ) (hW : IsWeightMatrix W)
    (x1 : Fin m → ℝ) (U : Coins m)
    (h : Tendsto (beliefAct σ ε W x1 U) atTop (𝓝 0)) :
    ∃ t0 : ℕ, ∀ t ≥ t0, ∀ i, action σ ε W x1 U t i = 0 := by
  have hev : ∀ᶠ t in atTop, ∀ i, action σ ε W x1 U t i = 0 := by
    rw [eventually_all]
    intro i
    have hi : Tendsto (fun t => beliefAct σ ε W x1 U t i) atTop (𝓝 0) :=
      (continuous_apply i).continuousAt.tendsto.comp h
    have hi1 : Tendsto (fun t => beliefAct σ ε W x1 U (t + 1) i) atTop (𝓝 0) :=
      hi.comp (tendsto_add_atTop_nat 1)
    have hd : Tendsto (fun t => beliefAct σ ε W x1 U (t + 1) i -
        (1 - ε) * beliefAct σ ε W x1 U t i) atTop (𝓝 (0 - (1 - ε) * 0)) :=
      hi1.sub (hi.const_mul _)
    have hWii : 0 < W i i := hW.2.2 i
    have hlt : 0 - (1 - ε) * 0 < ε * W i i := by nlinarith
    filter_upwards [hd.eventually (gt_mem_nhds hlt)] with t ht
    rcases NL_actOf_cases σ (U t i) (beliefAct σ ε W x1 U t i) with h0 | h1
    · exact h0
    · exfalso
      have h1' : action σ ε W x1 U t i = 1 := h1
      have hS : W i i ≤ ∑ j, W i j * action σ ε W x1 U t j := by
        have : ∀ j, (if j = i then W i i else 0) ≤ W i j * action σ ε W x1 U t j := by
          intro j
          have hWij : 0 ≤ W i j := Matrix.nonneg_of_mem_rowStochastic hW.1
          by_cases hji : j = i
          · subst hji; simp [h1']
          · simp only [hji, if_false]
            rcases NL_actOf_cases σ (U t j) (beliefAct σ ε W x1 U t j) with a | a <;>
              simp only [action, a] <;> nlinarith
        calc W i i = ∑ j, (if j = i then W i i else 0) := by simp
          _ ≤ _ := Finset.sum_le_sum fun j _ => this j
      rw [NL_belief_succ] at ht
      nlinarith
  obtain ⟨t0, ht0⟩ := eventually_atTop.1 hev
  exact ⟨t0, ht0⟩

/-- The posterior is measurable and lies in `[0, 1]` almost surely in both states. -/
lemma NL_post_bound' (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    {S : Type*} [MeasurableSpace S] (F0 F1 : Measure S)
    [IsProbabilityMeasure F0] [IsProbabilityMeasure F1] :
    Measurable (posterior p F0 F1) ∧ (∀ᵐ s ∂F1, posterior p F0 F1 s ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ᵐ s ∂F0, posterior p F0 F1 s ∈ Set.Icc (0 : ℝ) 1) := by
  set a : ENNReal := ENNReal.ofReal p with ha
  set b : ENNReal := ENNReal.ofReal (1 - p) with hb
  set ν : Measure S := a • F1 + b • F0 with hν
  have hxdef : ∀ s, posterior p F0 F1 s = ((a • F1).rnDeriv ν s).toReal := fun s => rfl
  have hat : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have ha0 : a ≠ 0 := by simp [ha, hp0]
  have hb0 : b ≠ 0 := by simp [hb, hp1]
  have : IsFiniteMeasure (a • F1) := by
    constructor; rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]; exact hat.lt_top
  have : IsFiniteMeasure (b • F0) := by
    constructor; rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    exact ENNReal.ofReal_lt_top
  have : IsFiniteMeasure ν := by rw [hν]; infer_instance
  have hle : a • F1 ≤ ν := Measure.le_add_right le_rfl
  have hle1 : ∀ᵐ s ∂ν, (a • F1).rnDeriv ν s ≤ 1 := Measure.rnDeriv_le_one_of_le hle
  have hxb : ∀ᵐ s ∂ν, posterior p F0 F1 s ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [hle1] with s hs
    rw [hxdef]
    exact ⟨ENNReal.toReal_nonneg, by simpa using ENNReal.toReal_mono ENNReal.one_ne_top hs⟩
  have hF1 : F1 ≪ ν := (Measure.absolutelyContinuous_smul ha0).trans
    (Measure.AbsolutelyContinuous.add_right Measure.AbsolutelyContinuous.rfl _)
  have hF0 : F0 ≪ ν := (Measure.absolutelyContinuous_smul hb0).trans
    (Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl))
  exact ⟨(Measure.measurable_rnDeriv _ _).ennreal_toReal, hF1.ae_le hxb, hF0.ae_le hxb⟩

theorem solution (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    {S : Type*} [MeasurableSpace S] (F0 F1 : Measure S)
    [IsProbabilityMeasure F0] [IsProbabilityMeasure F1]
    (σ : ℝ → ℝ → ℝ) (hσ : IsExtremizationFamily p σ)
    {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (μ : Fin m → ℝ)
    (hW : IsWeightMatrix W) (hμ : IsCentrality W μ) :
    ∀ r : ℝ, 0 < r → ∃ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ ε ∈ Set.Ioc (0 : ℝ) 1,
      NaiveLearning (1 - lGF p F0 F1 μ + r) (σ δ) ε p W F0 F1 := by
  intro r hr
  obtain ⟨hxm, hx1, hx0⟩ := NL_post_bound' p hp0 hp1 F0 F1
  set x := posterior p F0 F1 with hxdef
  set P1 : Measure (Fin m → S) := Measure.pi fun _ : Fin m => F1
  set P0 : Measure (Fin m → S) := Measure.pi fun _ : Fin m => F0
  set Y : (Fin m → S) → ℝ := fun s => ∑ i, μ i * x (s i) with hY
  have hYm : Measurable Y := by
    refine Finset.measurable_sum _ fun i _ => ?_
    exact measurable_const.mul (hxm.comp (measurable_pi_apply i))
  set B1 : ℝ → Set (Fin m → S) := fun η => {s | p + η < Y s}
  set B0 : ℝ → Set (Fin m → S) := fun η => {s | Y s < p - η}
  set G : Set (Fin m → S) := {s | ∀ i, x (s i) ∈ Set.Icc (0 : ℝ) 1}
  have hGm : MeasurableSet G := by
    have : G = ⋂ i, (fun s : Fin m → S => s i) ⁻¹' (x ⁻¹' Set.Icc 0 1) := by
      ext s; simp [G]
    rw [this]
    exact MeasurableSet.iInter fun i =>
      (measurable_pi_apply i) (hxm measurableSet_Icc)
  have hG1 : P1 Gᶜ = 0 := by
    have : ∀ᵐ s ∂P1, s ∈ G := by
      simp only [G, Set.mem_setOf_eq]
      rw [ae_all_iff]
      intro i
      exact (measurePreserving_eval (fun _ : Fin m => F1) i).quasiMeasurePreserving.ae hx1
    exact this
  have hG0 : P0 Gᶜ = 0 := by
    have : ∀ᵐ s ∂P0, s ∈ G := by
      simp only [G, Set.mem_setOf_eq]
      rw [ae_all_iff]
      intro i
      exact (measurePreserving_eval (fun _ : Fin m => F0) i).quasiMeasurePreserving.ae hx0
    exact this
  -- choose η
  set q : ℝ → ℝ := fun η => (1 - η) * (p * (P1 (B1 η)).toReal + (1 - p) * (P0 (B0 η)).toReal)
  have hq : ∃ η : ℝ, 0 < η ∧ η < 1 ∧ lGF p F0 F1 μ - r ≤ q η := by
    set e : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 2)
    have he0 : ∀ j, 0 < e j := fun j => by positivity
    have he1 : ∀ j, e j < 1 := fun j => by
      simp only [e]; rw [div_lt_one (by positivity)]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have hemono : Antitone e := fun i j hij => by
      simp only [e]
      apply one_div_le_one_div_of_le (by positivity)
      have : (i : ℝ) ≤ j := Nat.cast_le.2 hij
      linarith
    have he : Tendsto e atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
      refine this.congr fun j => ?_
      simp only [e, Function.comp_apply]; push_cast; ring
    have hU1 : (⋃ j, B1 (e j)) = {s | p < Y s} := by
      ext s; simp only [B1, Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · rintro ⟨j, hj⟩; linarith [he0 j]
      · intro hs
        have : ∀ᶠ j in atTop, e j < Y s - p := he.eventually (gt_mem_nhds (by linarith))
        obtain ⟨j, hj⟩ := this.exists
        exact ⟨j, by linarith⟩
    have hU0 : (⋃ j, B0 (e j)) = {s | Y s < p} := by
      ext s; simp only [B0, Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · rintro ⟨j, hj⟩; linarith [he0 j]
      · intro hs
        have : ∀ᶠ j in atTop, e j < p - Y s := he.eventually (gt_mem_nhds (by linarith))
        obtain ⟨j, hj⟩ := this.exists
        exact ⟨j, by linarith⟩
    have hm1 : Monotone fun j => B1 (e j) := fun i j hij s hs => by
      simp only [B1, Set.mem_setOf_eq] at hs ⊢; linarith [hemono hij]
    have hm0 : Monotone fun j => B0 (e j) := fun i j hij s hs => by
      simp only [B0, Set.mem_setOf_eq] at hs ⊢; linarith [hemono hij]
    have t1 := tendsto_measure_iUnion_atTop (μ := P1) hm1
    have t0 := tendsto_measure_iUnion_atTop (μ := P0) hm0
    rw [hU1] at t1
    rw [hU0] at t0
    have t1' := (ENNReal.tendsto_toReal (measure_ne_top P1 _)).comp t1
    have t0' := (ENNReal.tendsto_toReal (measure_ne_top P0 _)).comp t0
    have tq : Tendsto (fun j => q (e j)) atTop (𝓝 ((1 - 0) * (p * (P1 {s | p < Y s}).toReal +
        (1 - p) * (P0 {s | Y s < p}).toReal))) :=
      ((tendsto_const_nhds.sub he).mul ((t1'.const_mul p).add (t0'.const_mul (1 - p))))
    have hl : lGF p F0 F1 μ = (1 - 0) * (p * (P1 {s | p < Y s}).toReal +
        (1 - p) * (P0 {s | Y s < p}).toReal) := by
      simp [lGF, P1, P0, Y, x]
    rw [← hl] at tq
    obtain ⟨j, hj⟩ := (tq.eventually (lt_mem_nhds (show lGF p F0 F1 μ - r < lGF p F0 F1 μ by
      linarith))).exists
    exact ⟨e j, he0 j, he1 j, hj.le⟩
  obtain ⟨η, hη0, hη1, hqη⟩ := hq
  obtain ⟨δ, hδ, ε0, hε0, H⟩ := lemma_6 p hp0 hp1 σ hσ W μ hW hμ η hη0
  set ε := min (ε0 / 2) 1 with hεdef
  have hεpos : 0 < ε := lt_min (by linarith) one_pos
  have hεlt : ε < ε0 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεle : ε ≤ 1 := min_le_right _ _
  refine ⟨δ, hδ, ε, ⟨hεpos, hεle⟩, ?_⟩
  -- the probability bound
  set a : ENNReal := ENNReal.ofReal p
  set b : ENNReal := ENNReal.ofReal (1 - p)
  set D1 : Measure (Bool × (Fin m → S)) := (Measure.dirac true).prod P1
  set D0 : Measure (Bool × (Fin m → S)) := (Measure.dirac false).prod P0
  set mix := a • D1 + b • D0 with hmix
  set L := LearnEvent (σ δ) ε p W F0 F1
  have hfull : fullLaw m p F0 F1 = mix.prod (coinLaw m) := rfl
  have : IsProbabilityMeasure (coinLaw m) := by unfold coinLaw; infer_instance
  set C1 : Set (Fin m → S) := G ∩ B1 η
  set C0 : Set (Fin m → S) := G ∩ B0 η
  have hC1m : MeasurableSet C1 := hGm.inter (measurableSet_lt measurable_const hYm)
  have hC0m : MeasurableSet C0 := hGm.inter (measurableSet_lt hYm measurable_const)
  set T : Set (Bool × (Fin m → S)) := ({true} ×ˢ C1) ∪ ({false} ×ˢ C0)
  have hTm : MeasurableSet T :=
    ((measurableSet_singleton _).prod hC1m).union ((measurableSet_singleton _).prod hC0m)
  have hpt : ∀ ξ, T.indicator (fun _ => ENNReal.ofReal (1 - η)) ξ ≤
      coinLaw m (Prod.mk ξ ⁻¹' L) := by
    rintro ⟨ω, s⟩
    by_cases hT : (ω, s) ∈ T
    · rw [Set.indicator_of_mem hT]
      rcases hT with ⟨hω, hs⟩ | ⟨hω, hs⟩
      · simp only [Set.mem_singleton_iff] at hω
        subst hω
        have hb := (H ε ⟨hεpos, hεlt⟩ (fun j => x (s j)) hs.1).1 hs.2
        refine hb.trans (measure_mono ?_)
        intro U hU
        simp only [Set.mem_setOf_eq] at hU
        obtain ⟨t0, ht0⟩ := NL_eventually_one (σ δ) ε hεpos W hW _ U hU
        exact ⟨t0, fun t ht i => by simpa using ht0 t ht i⟩
      · simp only [Set.mem_singleton_iff] at hω
        subst hω
        have hb := (H ε ⟨hεpos, hεlt⟩ (fun j => x (s j)) hs.1).2 hs.2
        refine hb.trans (measure_mono ?_)
        intro U hU
        simp only [Set.mem_setOf_eq] at hU
        obtain ⟨t0, ht0⟩ := NL_eventually_zero (σ δ) ε hεpos W hW _ U hU
        exact ⟨t0, fun t ht i => by simpa using ht0 t ht i⟩
    · rw [Set.indicator_of_notMem hT]; exact bot_le
  have hstep1 : ENNReal.ofReal (1 - η) * mix T ≤ fullLaw m p F0 F1 L := by
    rw [hfull, ← measure_toMeasurable L, Measure.prod_apply (measurableSet_toMeasurable _ _),
      ← lintegral_indicator_const hTm]
    refine lintegral_mono fun ξ => (hpt ξ).trans (measure_mono ?_)
    exact Set.preimage_mono (subset_toMeasurable _ _)
  have hstep2 : a * P1 (B1 η) + b * P0 (B0 η) ≤ mix T := by
    have e1 : P1 (B1 η) ≤ D1 T := by
      calc P1 (B1 η) ≤ P1 C1 := by
            calc P1 (B1 η) ≤ P1 (C1 ∪ Gᶜ) := measure_mono (fun s hs => by
                    by_cases hg : s ∈ G
                    · exact Or.inl ⟨hg, hs⟩
                    · exact Or.inr hg)
              _ ≤ P1 C1 + P1 Gᶜ := measure_union_le _ _
              _ = P1 C1 := by rw [hG1, add_zero]
        _ = D1 ({true} ×ˢ C1) := by
            rw [Measure.prod_prod]; simp
        _ ≤ D1 T := measure_mono Set.subset_union_left
    have e0 : P0 (B0 η) ≤ D0 T := by
      calc P0 (B0 η) ≤ P0 C0 := by
            calc P0 (B0 η) ≤ P0 (C0 ∪ Gᶜ) := measure_mono (fun s hs => by
                    by_cases hg : s ∈ G
                    · exact Or.inl ⟨hg, hs⟩
                    · exact Or.inr hg)
              _ ≤ P0 C0 + P0 Gᶜ := measure_union_le _ _
              _ = P0 C0 := by rw [hG0, add_zero]
        _ = D0 ({false} ×ˢ C0) := by
            rw [Measure.prod_prod]; simp
        _ ≤ D0 T := measure_mono Set.subset_union_right
    rw [hmix, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
      smul_eq_mul]
    gcongr
  have hfin : fullLaw m p F0 F1 L ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (Set.subset_univ L))
    rw [hfull, ← Set.univ_prod_univ, Measure.prod_prod, measure_univ (μ := coinLaw m), mul_one, hmix,
      Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
    simp [D1, D0, P1, P0, a, b]
  have hbound : ENNReal.ofReal (1 - η) * (a * P1 (B1 η) + b * P0 (B0 η)) ≤
      fullLaw m p F0 F1 L :=
    le_trans (by gcongr) hstep1
  have hreal := ENNReal.toReal_mono hfin hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_ne_top _ _)) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
    ENNReal.toReal_ofReal hp0.le, ENNReal.toReal_ofReal (by linarith)] at hreal
  unfold NaiveLearning
  have : q η ≤ (fullLaw m p F0 F1 L).toReal := hreal
  linarith
