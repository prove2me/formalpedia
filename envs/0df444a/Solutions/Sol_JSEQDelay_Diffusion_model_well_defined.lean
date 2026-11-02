-- Prove2me | solution 1 for JSEQDelay.Diffusion.model_well_defined
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T11:29:59.966398+00:00
-- url     : https://prove2.me/submissions/5e57a691-5341-4b37-b933-b947126258a0

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_RankBasedSDI_LoadBalancing_Reflection
import Definitions.Def_JSEQDelay_Diffusion_Model
import Definitions.Def_JSEQDelay_Diffusion_Skorokhod

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open BellWilliams2001.ThresholdPolicy RankBasedSDI.LoadBalancing

namespace JSEQA2Aux

lemma cadlag_bdd (x : ℝ → ℝ) (hx : IsCadlag x) (t : ℝ) :
    ∃ M : ℝ, ∀ s ∈ Set.Icc 0 t, |x s| ≤ M := by
  have hc : IsCompact (Set.Icc (0:ℝ) t) := isCompact_Icc
  refine hc.induction_on (p := fun S => ∃ M : ℝ, ∀ s ∈ S, |x s| ≤ M) ⟨0, by simp⟩ ?_ ?_ ?_
  · intro S T hST ⟨M, hM⟩
    exact ⟨M, fun s hs => hM s (hST hs)⟩
  · intro S T ⟨M, hM⟩ ⟨N, hN⟩
    refine ⟨max M N, fun s hs => ?_⟩
    rcases hs with hs | hs
    · exact (hM s hs).trans (le_max_left _ _)
    · exact (hN s hs).trans (le_max_right _ _)
  · intro s hs
    have hr : ∀ᶠ y in 𝓝[≥] s, |x y - x s| < 1 := by
      have := hx.1 s hs.1
      have h2 := this.tendsto.eventually (Metric.ball_mem_nhds (x s) one_pos)
      filter_upwards [h2] with y hy
      simpa [Real.dist_eq] using hy
    rcases eq_or_lt_of_le hs.1 with h0 | hpos
    · subst h0
      refine ⟨{y | |x y - x 0| < 1}, ?_, |x 0| + 1, ?_⟩
      · exact nhdsWithin_mono _ (fun y hy => hy.1) hr
      · intro y hy
        have := abs_sub_abs_le_abs_sub (x y) (x 0)
        simp only [Set.mem_setOf_eq] at hy
        linarith
    · obtain ⟨l, hl⟩ := hx.2 s hpos
      have hlft : ∀ᶠ y in 𝓝[<] s, |x y - l| < 1 := by
        have h2 := hl.eventually (Metric.ball_mem_nhds l one_pos)
        filter_upwards [h2] with y hy
        simpa [Real.dist_eq] using hy
      refine ⟨{y | |x y - x s| < 1} ∪ {y | |x y - l| < 1}, ?_, max (|x s|) (|l|) + 1, ?_⟩
      · apply mem_nhdsWithin_of_mem_nhds
        rw [← nhdsLT_sup_nhdsGE]
        exact ⟨Filter.mem_of_superset hlft (fun y hy => Or.inr hy),
          Filter.mem_of_superset hr (fun y hy => Or.inl hy)⟩
      · intro y hy
        rcases hy with hy | hy
        · have := abs_sub_abs_le_abs_sub (x y) (x s)
          simp only [Set.mem_setOf_eq] at hy
          have := le_max_left (|x s|) (|l|)
          linarith
        · have := abs_sub_abs_le_abs_sub (x y) l
          simp only [Set.mem_setOf_eq] at hy
          have := le_max_right (|x s|) (|l|)
          linarith

variable (x : ℝ → ℝ) (hx : IsCadlag x)
include hx

lemma reg_bdd (t : ℝ) : BddAbove ((fun s => max (-x s) 0) '' Set.Icc 0 t) := by
  obtain ⟨M, hM⟩ := cadlag_bdd x hx t
  refine ⟨max M 0, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  have := hM s hs
  have := neg_abs_le (x s)
  exact max_le_max (by linarith) le_rfl

lemma le_reg {t r : ℝ} (hr : r ∈ Set.Icc 0 t) : max (-x r) 0 ≤ skorokhodReg x t :=
  le_csSup (reg_bdd x hx t) (Set.mem_image_of_mem _ hr)

omit hx in
lemma reg_le {t c : ℝ} (ht : 0 ≤ t) (h : ∀ r ∈ Set.Icc 0 t, max (-x r) 0 ≤ c) :
    skorokhodReg x t ≤ c := by
  apply csSup_le ((Set.nonempty_Icc.2 ht).image _)
  rintro _ ⟨s, hs, rfl⟩
  exact h s hs

lemma reg_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ skorokhodReg x t :=
  (le_max_right _ _).trans (le_reg x hx ⟨le_rfl, ht⟩)

lemma neg_le_reg {t r : ℝ} (hr : r ∈ Set.Icc 0 t) : -x r ≤ skorokhodReg x t :=
  (le_max_left _ _).trans (le_reg x hx hr)

lemma reg_zero (hx0 : 0 ≤ x 0) : skorokhodReg x 0 = 0 := by
  apply le_antisymm
  · apply reg_le x le_rfl
    intro r hr
    have : r = 0 := le_antisymm hr.2 hr.1
    subst this
    simp [hx0]
  · exact reg_nonneg x hx le_rfl

lemma reg_mono : MonotoneOn (skorokhodReg x) (Set.Ici 0) := by
  intro a ha b hb hab
  apply reg_le x (show (0:ℝ) ≤ a from ha)
  intro r hr
  exact le_reg x hx ⟨hr.1, hr.2.trans hab⟩


/-- If `-x ≤ R t + c` on `[t, s]` then `R s ≤ R t + c`. -/
lemma reg_le_of_near {t s c : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) (hc : 0 ≤ c)
    (h : ∀ r ∈ Set.Icc t s, -x r ≤ skorokhodReg x t + c) :
    skorokhodReg x s ≤ skorokhodReg x t + c := by
  apply reg_le x (ht.trans hts)
  intro r hr
  rcases le_or_gt r t with hrt | hrt
  · exact (le_reg x hx ⟨hr.1, hrt⟩).trans (by linarith)
  · have h1 := h r ⟨hrt.le, hr.2⟩
    have h2 := reg_nonneg x hx ht
    exact max_le h1 (by linarith)

lemma eventually_near {t η : ℝ} (ht : 0 ≤ t) (hη : 0 < η) :
    ∃ δ > 0, ∀ r ∈ Set.Ico t (t + δ), |x r - x t| < η := by
  have hc := hx.1 t ht
  have h2 : ∀ᶠ y in 𝓝[≥] t, |x y - x t| < η := by
    have := hc.tendsto.eventually (Metric.ball_mem_nhds (x t) hη)
    filter_upwards [this] with y hy
    simpa [Real.dist_eq] using hy
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 h2
  refine ⟨u - t, by simpa using hu, fun r hr => hsub ?_⟩
  simpa using hr

lemma reg_rightcont {t : ℝ} (ht : 0 ≤ t) :
    ContinuousWithinAt (skorokhodReg x) (Set.Ici t) t := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hnear⟩ := eventually_near x hx ht (half_pos hε)
  refine ⟨δ, hδ, fun {s} hs hd => ?_⟩
  have hts : t ≤ s := hs
  rw [Real.dist_eq, abs_lt] at hd
  have hup := reg_le_of_near x hx ht hts (half_pos hε).le (fun r hr => by
    have h1 := hnear r ⟨hr.1, by linarith [hr.2]⟩
    have h2 := neg_le_reg x hx (t := t) (r := t) ⟨ht, le_rfl⟩
    have := (abs_lt.1 h1).1
    linarith)
  have hlo := reg_mono x hx (show (0:ℝ) ≤ t from ht) (show (0:ℝ) ≤ s from ht.trans hts) hts
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

lemma reg_leftlim {t : ℝ} (ht : 0 < t) : ∃ l : ℝ, Tendsto (skorokhodReg x) (𝓝[<] t) (𝓝 l) := by
  set Rm : ℝ → ℝ := fun s => skorokhodReg x (max s 0)
  have hm : Monotone Rm := by
    intro a b hab
    exact reg_mono x hx (show (0:ℝ) ≤ max a 0 from le_max_right _ _)
      (show (0:ℝ) ≤ max b 0 from le_max_right _ _) (max_le_max hab le_rfl)
  refine ⟨_, (hm.tendsto_nhdsLT t).congr' ?_⟩
  have : Set.Ioo 0 t ∈ 𝓝[<] t := Ioo_mem_nhdsLT ht
  filter_upwards [this] with s hs
  simp [Rm, max_eq_left hs.1.le]

lemma reg_cadlag : IsCadlag (skorokhodReg x) :=
  ⟨fun t ht => reg_rightcont x hx ht, fun t ht => reg_leftlim x hx ht⟩

lemma gamma1_cadlag : IsCadlag (JSEQDelay.Diffusion.Gamma1 x) := by
  refine ⟨fun t ht => (hx.1 t ht).add (reg_rightcont x hx ht), fun t ht => ?_⟩
  obtain ⟨l1, h1⟩ := hx.2 t ht
  obtain ⟨l2, h2⟩ := reg_leftlim x hx ht
  exact ⟨l1 + l2, h1.add h2⟩

lemma gamma1_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ JSEQDelay.Diffusion.Gamma1 x t := by
  have := neg_le_reg x hx (t := t) (r := t) ⟨ht, le_rfl⟩
  simp only [JSEQDelay.Diffusion.Gamma1]
  linarith


/-- The extension by `0` to negative times of a function that is nonneg, monotone and
right-continuous on `[0, ∞)` and vanishes at `0` is a Stieltjes function. -/
noncomputable def extStieltjes (y : ℝ → ℝ) (hy0 : y 0 = 0) (hpos : ∀ t, 0 ≤ t → 0 ≤ y t)
    (hmono : MonotoneOn y (Set.Ici 0))
    (hrc : ∀ t, 0 ≤ t → ContinuousWithinAt y (Set.Ici t) t) : StieltjesFunction ℝ where
  toFun := fun t => if 0 ≤ t then y t else 0
  mono' := by
    intro a b hab
    by_cases ha : 0 ≤ a
    · simp only [ha, (ha.trans hab), if_true]
      exact hmono ha (ha.trans hab) hab
    · simp only [ha, if_false]
      split_ifs with hb
      · exact hpos b hb
      · exact le_rfl
  right_continuous' := by
    intro t
    by_cases ht : 0 ≤ t
    · apply (hrc t ht).congr
      · intro s hs
        have : 0 ≤ s := ht.trans hs
        simp [this]
      · simp [ht]
    · push Not at ht
      apply ContinuousWithinAt.mono _ (Set.subset_univ _)
      rw [continuousWithinAt_univ]
      have : (fun t : ℝ => if 0 ≤ t then y t else 0) =ᶠ[𝓝 t] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds ht] with s hs
        simp [not_le.2 (show s < 0 from hs)]
      exact (continuousAt_const.congr this.symm)


section compl
variable (hx0 : 0 ≤ x 0)
include hx0

noncomputable def regG : StieltjesFunction ℝ :=
  extStieltjes (skorokhodReg x) (reg_zero x hx hx0) (fun _ ht => reg_nonneg x hx ht)
    (reg_mono x hx) (fun _ ht => reg_rightcont x hx ht)

lemma regG_apply (t : ℝ) : regG x hx hx0 t = if 0 ≤ t then skorokhodReg x t else 0 := rfl

lemma regG_nonneg (t : ℝ) : 0 ≤ regG x hx hx0 t := by
  rw [regG_apply]; split_ifs with h
  · exact reg_nonneg x hx h
  · exact le_rfl

lemma regG_noJump {t : ℝ} (ht : 0 ≤ t) (hpos : 0 < JSEQDelay.Diffusion.Gamma1 x t) :
    Function.leftLim (regG x hx hx0) t = regG x hx hx0 t := by
  have hm : Monotone (regG x hx hx0) := (regG x hx hx0).mono
  apply le_antisymm (hm.leftLim_le le_rfl)
  have hℓ0 : 0 ≤ Function.leftLim (regG x hx hx0) t :=
    (regG_nonneg x hx hx0 (t - 1)).trans (hm.le_leftLim (by linarith))
  rw [regG_apply, if_pos ht]
  rcases eq_or_lt_of_le ht with h0 | htpos
  · subst h0; rw [reg_zero x hx hx0]; exact hℓ0
  set ℓ := Function.leftLim (regG x hx hx0) t
  have hbefore : ∀ r ∈ Set.Icc 0 t, r < t → max (-x r) 0 ≤ ℓ := by
    intro r hr hrt
    have h1 := le_reg x hx (t := r) (r := r) ⟨hr.1, le_rfl⟩
    have h2 := hm.le_leftLim hrt
    rw [regG_apply, if_pos hr.1] at h2
    exact h1.trans h2
  have hxt : -x t ≤ ℓ := by
    by_contra hcon
    push Not at hcon
    have : skorokhodReg x t ≤ -x t := by
      apply reg_le x ht
      intro r hr
      rcases lt_or_eq_of_le hr.2 with hrt | hrt
      · exact (hbefore r hr hrt).trans hcon.le
      · subst hrt; exact max_le le_rfl (by linarith)
    simp only [JSEQDelay.Diffusion.Gamma1] at hpos
    linarith
  apply reg_le x ht
  intro r hr
  rcases lt_or_eq_of_le hr.2 with hrt | hrt
  · exact hbefore r hr hrt
  · subst hrt; exact max_le hxt hℓ0

lemma reg_flat {t : ℝ} (ht : 0 ≤ t) (hpos : 0 < JSEQDelay.Diffusion.Gamma1 x t) :
    ∃ q : ℚ, t < q ∧ skorokhodReg x q = skorokhodReg x t := by
  obtain ⟨δ, hδ, hnear⟩ := eventually_near x hx ht hpos
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t < t + δ by linarith)
  refine ⟨q, hq1, le_antisymm ?_ (reg_mono x hx ht (ht.trans hq1.le) hq1.le)⟩
  have := reg_le_of_near x hx (c := 0) ht hq1.le le_rfl (fun r hr => by
    have h1 := (abs_lt.1 (hnear r ⟨hr.1, lt_of_le_of_lt hr.2 hq2⟩)).1
    simp only [JSEQDelay.Diffusion.Gamma1] at h1
    linarith)
  simpa using this

lemma regG_null :
    (regG x hx hx0).measure {t | 0 ≤ t ∧ 0 < JSEQDelay.Diffusion.Gamma1 x t} = 0 := by
  set G := regG x hx hx0
  set U := {t | 0 ≤ t ∧ 0 < JSEQDelay.Diffusion.Gamma1 x t}
  set N : Set ℝ := ⋃ (p : ℚ) (q : ℚ) (_ : G p = G q), Set.Ioc (p : ℝ) q
  have hN : G.measure N = 0 := by
    refine measure_iUnion_null fun p => measure_iUnion_null fun q => measure_iUnion_null fun h => ?_
    rw [StieltjesFunction.measure_Ioc, h, sub_self, ENNReal.ofReal_zero]
  have hflat : ∀ t ∈ U, ∃ q : ℚ, t < q ∧ skorokhodReg x q = skorokhodReg x t :=
    fun t ht => reg_flat x hx hx0 ht.1 ht.2
  choose! f hf using hflat
  have hinj : Set.InjOn f (U \ N) := by
    have key : ∀ t ∈ U \ N, ∀ t' ∈ U \ N, t < t' → f t ≠ f t' := by
      intro t ht t' ht' htt' hfe
      obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn htt'
      have hft := hf t ht.1
      have hft' := hf t' ht'.1
      have ht0 : 0 ≤ t := ht.1.1
      have hq0 : (0:ℝ) ≤ (f t' : ℝ) := ht0.trans (htt'.trans hft'.1).le
      have hp0 : (0:ℝ) ≤ (p : ℝ) := ht0.trans hp1.le
      have hRp1 : skorokhodReg x t ≤ skorokhodReg x p := reg_mono x hx ht0 hp0 hp1.le
      have hRp2 : skorokhodReg x p ≤ skorokhodReg x (f t') :=
        reg_mono x hx hp0 hq0 (hp2.trans hft'.1).le
      have hRq : skorokhodReg x (f t') = skorokhodReg x t := by rw [← hfe]; exact hft.2
      have hGeq : G p = G (f t') := by
        simp only [G, regG_apply, if_pos hp0, if_pos hq0]
        linarith
      apply ht'.2
      simp only [N, Set.mem_iUnion]
      exact ⟨p, f t', hGeq, hp2, hft'.1.le⟩
    intro t ht t' ht' hfe
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key t ht t' ht' h hfe
    · exact key t' ht' t ht h hfe.symm
  have hcount : (U \ N).Countable :=
    Set.MapsTo.countable_of_injOn (Set.mapsTo_univ _ _) hinj Set.countable_univ
  have hE : G.measure (U \ N) = 0 := by
    have : U \ N = ⋃ t ∈ U \ N, ({t} : Set ℝ) := (Set.biUnion_of_singleton _).symm
    rw [this, measure_biUnion_null_iff hcount]
    intro t ht
    rw [StieltjesFunction.measure_singleton, regG_noJump x hx hx0 ht.1.1 ht.1.2, sub_self,
      ENNReal.ofReal_zero]
  apply measure_mono_null (show U ⊆ (U \ N) ∪ N by intro t ht; by_cases h : t ∈ N <;> simp [h, ht])
  exact measure_union_null hE hN

lemma reg_compl : StieltjesComplementary (JSEQDelay.Diffusion.Gamma1 x) (skorokhodReg x) := by
  refine ⟨regG x hx hx0, regG_apply x hx hx0, ?_⟩
  have : ∀ᵐ t ∂((regG x hx hx0).measure.restrict (Set.Ici 0)),
      ENNReal.ofReal (JSEQDelay.Diffusion.Gamma1 x t) = 0 := by
    rw [ae_restrict_iff' measurableSet_Ici]
    apply measure_mono_null _ (regG_null x hx hx0)
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_Ici, ENNReal.ofReal_eq_zero,
      _root_.not_imp, not_le] at ht
    exact ht
  rw [lintegral_congr_ae this, lintegral_zero]

end compl


omit hx in
/-- A positive lower bound for the integrand on a set of positive measure contradicts
complementarity. -/
lemma compl_contra (z : ℝ → ℝ) (G : StieltjesFunction ℝ)
    (hint : ∫⁻ t in Set.Ici 0, ENNReal.ofReal (z t) ∂G.measure = 0)
    (I : Set ℝ) (hI : MeasurableSet I) (hI0 : I ⊆ Set.Ici 0) {ε : ℝ} (hε : 0 < ε)
    (hz : ∀ s ∈ I, ε ≤ z s) (hμ : G.measure I ≠ 0) : False := by
  have h1 : ∫⁻ t in I, ENNReal.ofReal ε ∂G.measure ≤ ∫⁻ t in I, ENNReal.ofReal (z t) ∂G.measure :=
    setLIntegral_mono' hI (fun s hs => ENNReal.ofReal_le_ofReal (hz s hs))
  have h2 := lintegral_mono_set (μ := G.measure) (f := fun t => ENNReal.ofReal (z t)) hI0
  rw [setLIntegral_const] at h1
  have : ENNReal.ofReal ε * G.measure I = 0 := le_antisymm (by
    calc _ ≤ _ := h1
      _ ≤ _ := h2
      _ = 0 := hint) bot_le
  rcases mul_eq_zero.1 this with h | h
  · exact (ENNReal.ofReal_pos.2 hε).ne' h
  · exact hμ h

lemma skorokhod_unique (z y : ℝ → ℝ) (h : JSEQDelay.Diffusion.SkorokhodSolves x z y)
    {t : ℝ} (ht : 0 ≤ t) : y t = skorokhodReg x t := by
  obtain ⟨_, _, _, hy0, hypos, hzxy, hymono, G, hG, hint⟩ := h
  -- lower bound
  have hlow : skorokhodReg x t ≤ y t := by
    apply reg_le x ht
    intro r hr
    have := hzxy r hr.1
    have := hymono hr.1 (hr.1.trans hr.2) hr.2
    have := ‹∀ t, 0 ≤ t → 0 ≤ z t› r hr.1
    exact max_le (by linarith) (hypos t ht)
  refine le_antisymm ?_ hlow
  by_contra hcon
  push Not at hcon
  set c := skorokhodReg x t
  have hc0 : 0 ≤ c := reg_nonneg x hx ht
  set d := y t - c
  have hd : 0 < d := by simp only [d]; linarith
  have hzlow : ∀ s ∈ Set.Icc 0 t, y s - c ≤ z s := by
    intro s hs
    have := hzxy s hs.1
    have := neg_le_reg x hx hs
    linarith
  set S := {s | s ∈ Set.Icc 0 t ∧ y s ≤ c + d / 2}
  have hS0 : (0:ℝ) ∈ S := ⟨⟨le_rfl, ht⟩, by rw [hy0]; linarith⟩
  have hSb : BddAbove S := ⟨t, fun s hs => hs.1.2⟩
  set a := sSup S
  have ha0 : 0 ≤ a := le_csSup hSb hS0
  have hat : a ≤ t := csSup_le ⟨0, hS0⟩ (fun s hs => hs.1.2)
  have hafter : ∀ s, a < s → s ≤ t → c + d / 2 < y s := by
    intro s has hst
    by_contra hh
    push Not at hh
    have : s ≤ a := le_csSup hSb ⟨⟨ha0.trans has.le, hst⟩, hh⟩
    linarith
  have hGa : ∀ s, 0 ≤ s → G s = y s := fun s hs => by rw [hG, if_pos hs]
  by_cases hya : y a ≤ c + d / 2
  · -- the interval `(a, t]`
    apply compl_contra z G hint (Set.Ioc a t) measurableSet_Ioc
      (fun s hs => ha0.trans hs.1.le) (half_pos hd)
    · intro s hs
      have := hafter s hs.1 hs.2
      have := hzlow s ⟨ha0.trans hs.1.le, hs.2⟩
      linarith
    · rw [StieltjesFunction.measure_Ioc, hGa t ht, hGa a ha0]
      apply (ENNReal.ofReal_pos.2 _).ne'
      linarith
  · -- the interval `[a, t]`
    push Not at hya
    have hapos : 0 < a := by
      rcases eq_or_lt_of_le ha0 with h | h
      · rw [← h, hy0] at hya; linarith
      · exact h
    have hleft : Function.leftLim G a ≤ c + d / 2 := by
      have hm : Monotone G := G.mono
      apply le_of_tendsto (hm.tendsto_leftLim a)
      filter_upwards [self_mem_nhdsWithin] with s (hs : s < a)
      by_cases hs0 : 0 ≤ s
      · obtain ⟨s', hs'S, hss'⟩ := exists_lt_of_lt_csSup ⟨0, hS0⟩ hs
        rw [hGa s hs0]
        exact (hymono hs0 (hs0.trans hss'.le) hss'.le).trans hs'S.2
      · rw [hG, if_neg hs0]; linarith
    apply compl_contra z G hint (Set.Icc a t) measurableSet_Icc
      (fun s hs => ha0.trans hs.1) (half_pos hd)
    · intro s hs
      have := hymono ha0 (ha0.trans hs.1) hs.1
      have := hzlow s ⟨ha0.trans hs.1, hs.2⟩
      linarith
    · rw [StieltjesFunction.measure_Icc, hGa t ht]
      apply (ENNReal.ofReal_pos.2 _).ne'
      linarith

end JSEQA2Aux


namespace JSEQR21Aux

section renewal
variable {X : ℕ → ℝ} (hX0 : X 0 = 0) (hXs : StrictMono X) (hXt : Tendsto X atTop atTop)

include hXs in
lemma rc_eq {m : ℕ} {x : ℝ} (h1 : X m ≤ x) (h2 : x < X (m + 1)) : renewalCount X x = m := by
  apply le_antisymm
  · refine iSup₂_le fun n hn => ?_
    have : n < m + 1 := by
      by_contra hc
      push Not at hc
      have := hXs.monotone hc
      linarith
    exact_mod_cast Nat.lt_succ_iff.1 this
  · exact le_iSup₂ (f := fun n (_ : X n ≤ x) => (n : ℕ∞)) m h1

include hX0 hXs in
lemma rc_neg {x : ℝ} (hx : x < 0) : renewalCount X x = 0 := by
  apply le_antisymm _ bot_le
  refine iSup₂_le fun n hn => ?_
  have := hXs.monotone (Nat.zero_le n)
  linarith

include hX0 hXt in
lemma exists_m {x : ℝ} (hx : 0 ≤ x) : ∃ m, X m ≤ x ∧ x < X (m + 1) := by
  classical
  have hex : ∃ n, x < X n := (hXt.eventually_gt_atTop x).exists
  have hne : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0, hX0] at this
    linarith
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    push Not at this
    exact this
  · rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hne)]
    exact Nat.find_spec hex

include hX0 hXs hXt

lemma R_eq {m : ℕ} {x : ℝ} (h1 : X m ≤ x) (h2 : x < X (m + 1)) : (renewalCount X x).toNat = m := by
  rw [rc_eq hXs h1 h2]; rfl

lemma R_neg {x : ℝ} (hx : x < 0) : (renewalCount X x).toNat = 0 := by
  rw [rc_neg hX0 hXs hx]; rfl

lemma R_zero : (renewalCount X 0).toNat = 0 :=
  R_eq hX0 hXs hXt (m := 0) (by rw [hX0]) (by rw [← hX0]; exact hXs (Nat.zero_lt_one))

lemma R_mono : Monotone (fun x => (renewalCount X x).toNat) := by
  intro x y hxy
  simp only
  rcases lt_or_ge x 0 with hx | hx
  · rw [R_neg hX0 hXs hXt hx]; exact Nat.zero_le _
  obtain ⟨m, hm1, hm2⟩ := exists_m hX0 hXt hx
  obtain ⟨m', hm1', hm2'⟩ := exists_m hX0 hXt (hx.trans hxy)
  rw [R_eq hX0 hXs hXt hm1 hm2, R_eq hX0 hXs hXt hm1' hm2']
  have : X m < X (m' + 1) := by linarith
  have := hXs.lt_iff_lt.1 this
  omega

lemma R_rightconst (x : ℝ) : ∃ δ > 0, ∀ y, x ≤ y → y < x + δ →
    (renewalCount X y).toNat = (renewalCount X x).toNat := by
  rcases lt_or_ge x 0 with hx | hx
  · refine ⟨-x, by linarith, fun y hy1 hy2 => ?_⟩
    rw [R_neg hX0 hXs hXt hx, R_neg hX0 hXs hXt (by linarith)]
  obtain ⟨m, hm1, hm2⟩ := exists_m hX0 hXt hx
  refine ⟨X (m + 1) - x, by linarith, fun y hy1 hy2 => ?_⟩
  rw [R_eq hX0 hXs hXt hm1 hm2, R_eq hX0 hXs hXt (hm1.trans hy1) (by linarith)]

lemma R_leftjump (x : ℝ) : ∃ δ > 0, ∀ y, x - δ < y → y ≤ x →
    (renewalCount X x).toNat ≤ (renewalCount X y).toNat + 1 := by
  rcases lt_or_ge x 0 with hx | hx
  · exact ⟨1, one_pos, fun y _ _ => by rw [R_neg hX0 hXs hXt hx]; omega⟩
  obtain ⟨m, hm1, hm2⟩ := exists_m hX0 hXt hx
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · exact ⟨1, one_pos, fun y _ _ => by rw [R_eq hX0 hXs hXt hm1 hm2, h0]; omega⟩
  have hlt : X (m - 1) < X m := hXs (by omega)
  refine ⟨x - X (m - 1), by linarith, fun y hy1 hy2 => ?_⟩
  have hy0 : 0 ≤ y := by
    have := hXs.monotone (Nat.zero_le (m - 1)); rw [hX0] at this; linarith
  obtain ⟨m', hm1', hm2'⟩ := exists_m hX0 hXt hy0
  rw [R_eq hX0 hXs hXt hm1 hm2, R_eq hX0 hXs hXt hm1' hm2']
  have : X (m - 1) < X (m' + 1) := by linarith
  have := hXs.lt_iff_lt.1 this
  omega

end renewal


section busy
variable (a' : ℝ → ℝ) (S : ℝ → ℕ) (q : ℝ → ℝ)
  (ha_mono : Monotone a') (hS_mono : Monotone S)
  (hq : ∀ t, 0 ≤ t → q t = a' t - S (∫ s in (0:ℝ)..t, if 0 < q s then (1:ℝ) else 0))

/-- the busy indicator -/
noncomputable def ind (q : ℝ → ℝ) (s : ℝ) : ℝ := if 0 < q s then 1 else 0

lemma ind_nonneg (s : ℝ) : 0 ≤ ind q s := by unfold ind; split_ifs <;> norm_num
lemma ind_le_one (s : ℝ) : ind q s ≤ 1 := by unfold ind; split_ifs <;> norm_num
lemma ind_norm (s : ℝ) : ‖ind q s‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (ind_nonneg q s)]; exact ind_le_one q s

include ha_mono hS_mono hq in
lemma ind_integrable (T : ℝ) : IntegrableOn (ind q) (Set.Ioc 0 T) := by
  classical
  set J : Set ℝ := {t | 0 ≤ t ∧ IntegrableOn (ind q) (Set.Ioc 0 t)}
  set B : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..t, ind q s
  have hJ : J.OrdConnected := by
    refine ⟨fun x hx y hy z hz => ⟨hx.1.trans hz.1, hy.2.mono_set (Set.Ioc_subset_Ioc_right hz.2)⟩⟩
  have hBlip : ∀ t ∈ J, ∀ t' ∈ J, |B t - B t'| ≤ |t - t'| := by
    intro t ht t' ht'
    have i1 : IntervalIntegrable (ind q) volume 0 t :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).2 ht.2
    have i2 : IntervalIntegrable (ind q) volume 0 t' :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht'.1).2 ht'.2
    simp only [B]
    rw [intervalIntegral.integral_interval_sub_left i1 i2]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t') (b := t) (C := 1)
      (f := ind q) (fun x _ => ind_norm q x)
    rw [Real.norm_eq_abs] at this
    linarith [abs_sub_comm t t']
  have hBc : ContinuousOn B J := by
    rw [Metric.continuousOn_iff]
    intro t ht ε hε
    refine ⟨ε, hε, fun t' ht' hd => ?_⟩
    rw [Real.dist_eq] at hd ⊢
    exact lt_of_le_of_lt (hBlip t' ht' t ht) hd
  set B' := J.piecewise B (fun _ => 0)
  have hB'm : Measurable B' :=
    hBc.measurable_piecewise continuousOn_const hJ.measurableSet
  have hBB' : ∀ t, 0 ≤ t → B t = B' t := by
    intro t ht
    by_cases h : t ∈ J
    · simp [B', Set.piecewise, h]
    · have h' : ¬ IntegrableOn (ind q) (Set.Ioc 0 t) := fun hi => h ⟨ht, hi⟩
      simp only [B', Set.piecewise, h, if_false, B]
      rw [intervalIntegral.integral_of_le ht, integral_undef h']
  set g : ℝ → ℝ := fun s => if 0 < a' s - (S (B' s) : ℝ) then 1 else 0
  have hgm : Measurable g := by
    have h1 : Measurable a' := ha_mono.measurable
    have hmS : Monotone (fun r => (S r : ℝ)) := fun x y hxy => Nat.cast_le.2 (hS_mono hxy)
    have h2 : Measurable (fun r => (S r : ℝ)) := hmS.measurable
    have h3 : Measurable (fun s => a' s - (S (B' s) : ℝ)) := h1.sub (h2.comp hB'm)
    exact Measurable.ite (measurableSet_lt measurable_const h3) measurable_const measurable_const
  have hgi : IntegrableOn g (Set.Ioc 0 T) := by
    refine Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne hgm.aestronglyMeasurable ?_
    refine Eventually.of_forall fun s => ?_
    simp only [g]; split_ifs <;> norm_num
  refine hgi.congr_fun (fun s hs => ?_) measurableSet_Ioc
  have hs0 : 0 ≤ s := hs.1.le
  simp only [g, ind]
  rw [hq s hs0, ← hBB' s hs0]
  rfl

include ha_mono hS_mono hq in
lemma ind_ii (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : IntervalIntegrable (ind q) volume a b := by
  have h0 : ∀ c, 0 ≤ c → IntervalIntegrable (ind q) volume 0 c := fun c hc =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hc).2 (ind_integrable a' S q ha_mono hS_mono hq c)
  exact (h0 a ha).symm.trans (h0 b hb)


/-- the busy time -/
noncomputable def Bf (q : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0:ℝ)..t, ind q s

include ha_mono hS_mono hq in
lemma Bf_sub {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) : Bf q t - Bf q s = ∫ r in s..t, ind q r := by
  unfold Bf
  rw [intervalIntegral.integral_interval_sub_left (ind_ii a' S q ha_mono hS_mono hq 0 t le_rfl ht)
    (ind_ii a' S q ha_mono hS_mono hq 0 s le_rfl hs)]

include ha_mono hS_mono hq in
lemma Bf_inc {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : 0 ≤ Bf q t - Bf q s ∧ Bf q t - Bf q s ≤ t - s := by
  rw [Bf_sub a' S q ha_mono hS_mono hq hs (hs.trans hst)]
  constructor
  · exact intervalIntegral.integral_nonneg hst (fun r _ => ind_nonneg q r)
  · have := intervalIntegral.integral_mono_on hst (ind_ii a' S q ha_mono hS_mono hq s t hs (hs.trans hst))
      (intervalIntegrable_const (c := (1:ℝ))) (fun r _ => ind_le_one q r)
    simpa using this

include ha_mono hS_mono hq in
lemma Bf_const {s t c : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (h : ∀ r ∈ Set.Icc s t, ind q r = c) :
    Bf q t - Bf q s = c * (t - s) := by
  rw [Bf_sub a' S q ha_mono hS_mono hq hs (hs.trans hst)]
  rw [intervalIntegral.integral_congr (g := fun _ => c) (fun r hr => by
    rw [Set.uIcc_of_le hst] at hr; exact h r hr)]
  simp [mul_comm]

lemma Bf_zero : Bf q 0 = 0 := by simp [Bf]

lemma hq' : (∀ t, 0 ≤ t → q t = a' t - S (∫ s in (0:ℝ)..t, if 0 < q s then (1:ℝ) else 0)) →
    ∀ t, 0 ≤ t → q t = a' t - S (Bf q t) := fun h t ht => h t ht

variable (ha_rc : ∀ x, ∃ δ > 0, ∀ y, x ≤ y → y < x + δ → a' y = a' x)
  (hS_rc : ∀ x, ∃ δ > 0, ∀ y, x ≤ y → y < x + δ → S y = S x)
  (hS_lj : ∀ x, ∃ δ > 0, ∀ y, x - δ < y → y ≤ x → S x ≤ S y + 1)
  (ha_int : ∀ t, ∃ n : ℕ, a' t = n) (hq0 : q 0 = 0)

include ha_mono hS_mono hq ha_rc hS_rc in
lemma q_rc {t : ℝ} (ht : 0 ≤ t) : ∃ δ > 0, ∀ y, t ≤ y → y < t + δ → q y = q t := by
  obtain ⟨δ1, hδ1, h1⟩ := ha_rc t
  obtain ⟨δ2, hδ2, h2⟩ := hS_rc (Bf q t)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun y hy1 hy2 => ?_⟩
  have hB := Bf_inc a' S q ha_mono hS_mono hq ht hy1
  rw [hq' a' S q hq y (ht.trans hy1), hq' a' S q hq t ht,
    h1 y hy1 (by linarith [min_le_left δ1 δ2]),
    h2 (Bf q y) (by linarith) (by linarith [min_le_right δ1 δ2])]

include ha_mono hS_mono hq ha_rc hS_rc hS_lj ha_int hq0 in
lemma q_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ q t := by
  by_contra hcon
  push Not at hcon
  set E := {t : ℝ | 0 ≤ t ∧ q t < 0}
  have hEne : E.Nonempty := ⟨t, ht, hcon⟩
  have hEbdd : BddBelow E := ⟨0, fun s hs => hs.1⟩
  set t0 := sInf E
  have ht00 : 0 ≤ t0 := le_csInf hEne (fun s hs => hs.1)
  have hbefore : ∀ s, 0 ≤ s → s < t0 → 0 ≤ q s := by
    intro s hs hst
    by_contra hc
    push Not at hc
    have := csInf_le hEbdd ⟨hs, hc⟩
    linarith
  have ht0E : q t0 < 0 := by
    obtain ⟨δ, hδ, hrc⟩ := q_rc a' S q ha_mono hS_mono hq ha_rc hS_rc ht00
    obtain ⟨e, he, hlt⟩ := exists_lt_of_csInf_lt hEne (show t0 < t0 + δ by linarith)
    have := hrc e (csInf_le hEbdd he) hlt
    rw [← this]; exact he.2
  have ht0pos : 0 < t0 := by
    rcases eq_or_lt_of_le ht00 with h | h
    · rw [← h, hq0] at ht0E; exact absurd ht0E (lt_irrefl 0)
    · exact h
  -- integrality
  have hint : q t0 ≤ -1 := by
    obtain ⟨n, hn⟩ := ha_int t0
    rw [hq' a' S q hq t0 ht00, hn] at ht0E ⊢
    have : n < S (Bf q t0) := by exact_mod_cast (sub_neg.1 ht0E)
    have : (n : ℝ) + 1 ≤ S (Bf q t0) := by exact_mod_cast this
    linarith
  obtain ⟨δ3, hδ3, hlj⟩ := hS_lj (Bf q t0)
  set ε := min δ3 t0 / 2
  have hε : 0 < ε := by positivity
  have hεlt : ε < t0 := by have := min_le_right δ3 t0; simp only [ε]; linarith
  have hεlt3 : ε < δ3 := by have := min_le_left δ3 t0; simp only [ε]; linarith
  have hzero : ∀ r ∈ Set.Icc (t0 - ε) t0, ind q r = 0 := by
    intro r hr
    have hr0 : 0 ≤ r := by linarith [hr.1]
    rcases eq_or_lt_of_le hr.2 with hrt | hrt
    · rw [hrt]; simp [ind, not_lt.2 ht0E.le]
    have hB := Bf_inc a' S q ha_mono hS_mono hq hr0 hr.2
    have hS1 := hlj (Bf q r) (by linarith [hr.1]) (by linarith)
    have hS1' : (S (Bf q t0) : ℝ) ≤ S (Bf q r) + 1 := by exact_mod_cast hS1
    have hle : q r ≤ 0 := by
      rw [hq' a' S q hq r hr0]
      rw [hq' a' S q hq t0 ht00] at hint
      have := ha_mono hr.2
      linarith
    simp [ind, not_lt.2 hle]
  have hflat := Bf_const a' S q ha_mono hS_mono hq (by linarith) (by linarith) hzero
  simp only [zero_mul, sub_eq_zero] at hflat
  have hq1 := hbefore (t0 - ε) (by linarith) (by linarith)
  rw [hq' a' S q hq (t0 - ε) (by linarith), ← hflat] at hq1
  rw [hq' a' S q hq t0 ht00] at ht0E
  have := ha_mono (show t0 - ε ≤ t0 by linarith)
  linarith

end busy

lemma monotoneOn_leftlim {φ : ℝ → ℝ} (hφ : MonotoneOn φ (Set.Ici 0)) {t : ℝ} (ht : 0 < t) :
    ∃ l : ℝ, Tendsto φ (𝓝[<] t) (𝓝 l) := by
  set φm : ℝ → ℝ := fun s => φ (max s 0)
  have hm : Monotone φm := by
    intro a b hab
    exact hφ (show (0:ℝ) ≤ max a 0 from le_max_right _ _)
      (show (0:ℝ) ≤ max b 0 from le_max_right _ _) (max_le_max hab le_rfl)
  refine ⟨_, (hm.tendsto_nhdsLT t).congr' ?_⟩
  filter_upwards [Ioo_mem_nhdsLT ht] with s hs
  simp [φm, max_eq_left hs.1.le]

lemma null_of_flat (G : StieltjesFunction ℝ) (U : Set ℝ)
    (h : ∀ t ∈ U, (∃ q : ℚ, t < q ∧ G q = G t) ∧ Function.leftLim G t = G t) :
    G.measure U = 0 := by
  set N : Set ℝ := ⋃ (p : ℚ) (q : ℚ) (_ : G p = G q), Set.Ioc (p : ℝ) q
  have hN : G.measure N = 0 := by
    refine measure_iUnion_null fun p => measure_iUnion_null fun q => measure_iUnion_null fun h => ?_
    rw [StieltjesFunction.measure_Ioc, h, sub_self, ENNReal.ofReal_zero]
  have hflat : ∀ t ∈ U, ∃ q : ℚ, t < q ∧ G q = G t := fun t ht => (h t ht).1
  choose! f hf using hflat
  have hinj : Set.InjOn f (U \ N) := by
    have key : ∀ t ∈ U \ N, ∀ t' ∈ U \ N, t < t' → f t ≠ f t' := by
      intro t ht t' ht' htt' hfe
      obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn htt'
      have hft := hf t ht.1
      have hft' := hf t' ht'.1
      have h1 : G t ≤ G p := G.mono hp1.le
      have h2 : G p ≤ G (f t') := G.mono (hp2.trans hft'.1).le
      have hRq : G (f t') = G t := by rw [← hfe]; exact hft.2
      have hGeq : G p = G (f t') := by linarith
      apply ht'.2
      simp only [N, Set.mem_iUnion]
      exact ⟨p, f t', hGeq, hp2, hft'.1.le⟩
    intro t ht t' ht' hfe
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key t ht t' ht' h hfe
    · exact key t' ht' t ht h hfe.symm
  have hcount : (U \ N).Countable :=
    Set.MapsTo.countable_of_injOn (Set.mapsTo_univ _ _) hinj Set.countable_univ
  have hE : G.measure (U \ N) = 0 := by
    have : U \ N = ⋃ t ∈ U \ N, ({t} : Set ℝ) := (Set.biUnion_of_singleton _).symm
    rw [this, measure_biUnion_null_iff hcount]
    intro t ht
    rw [StieltjesFunction.measure_singleton, (h t ht.1).2, sub_self, ENNReal.ofReal_zero]
  apply measure_mono_null (show U ⊆ (U \ N) ∪ N by intro t ht; by_cases h : t ∈ N <;> simp [h, ht])
  exact measure_union_null hE hN


section busy2
variable (a' : ℝ → ℝ) (S : ℝ → ℕ) (q : ℝ → ℝ)
  (ha_mono : Monotone a') (hS_mono : Monotone S)
  (hq : ∀ t, 0 ≤ t → q t = a' t - S (∫ s in (0:ℝ)..t, if 0 < q s then (1:ℝ) else 0))
include ha_mono hS_mono hq

lemma Bf_contOn {t : ℝ} (ht : 0 ≤ t) : ContinuousWithinAt (Bf q) (Set.Ici 0) t := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨ε, hε, fun {y} hy hd => ?_⟩
  rw [Real.dist_eq] at hd ⊢
  have hy0 : 0 ≤ y := hy
  rcases le_total t y with h | h
  · have := Bf_inc a' S q ha_mono hS_mono hq ht h
    rw [abs_lt] at hd ⊢; constructor <;> linarith
  · have := Bf_inc a' S q ha_mono hS_mono hq hy0 h
    rw [abs_lt] at hd ⊢; constructor <;> linarith

lemma Bf_monoOn : MonotoneOn (Bf q) (Set.Ici 0) := fun s hs t _ hst => by
  have := Bf_inc a' S q ha_mono hS_mono hq hs hst; linarith

variable {m r : ℝ} (hm : 0 ≤ m) (hr : 0 < r)
include hm hr

lemma L_monoOn : MonotoneOn (fun t => m * (t - Bf q t) / r) (Set.Ici 0) := by
  intro s hs t _ hst
  have := Bf_inc a' S q ha_mono hS_mono hq hs hst
  simp only
  apply div_le_div_of_nonneg_right _ hr.le
  apply mul_le_mul_of_nonneg_left _ hm
  linarith

lemma L_zero : (fun t => m * (t - Bf q t) / r) 0 = 0 := by simp [Bf_zero]

lemma L_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ (fun t => m * (t - Bf q t) / r) t := by
  have := L_monoOn a' S q ha_mono hS_mono hq hm hr (le_refl (0:ℝ)) ht ht
  rw [L_zero a' S q ha_mono hS_mono hq hm hr] at this
  exact this

lemma L_cont {t : ℝ} (ht : 0 ≤ t) :
    ContinuousWithinAt (fun t => m * (t - Bf q t) / r) (Set.Ici 0) t :=
  ((continuousWithinAt_id.sub (Bf_contOn a' S q ha_mono hS_mono hq ht)).const_mul m).div_const r


lemma compl_L (ha_rc : ∀ x, ∃ δ > 0, ∀ y, x ≤ y → y < x + δ → a' y = a' x)
    (hS_rc : ∀ x, ∃ δ > 0, ∀ y, x ≤ y → y < x + δ → S y = S x) :
    StieltjesComplementary (fun t => q t / r) (fun t => m * (t - Bf q t) / r) := by
  set L : ℝ → ℝ := fun t => m * (t - Bf q t) / r with hL
  let G := JSEQA2Aux.extStieltjes L (L_zero a' S q ha_mono hS_mono hq hm hr)
    (fun t ht => L_nonneg a' S q ha_mono hS_mono hq hm hr ht)
    (L_monoOn a' S q ha_mono hS_mono hq hm hr)
    (fun t ht => (L_cont a' S q ha_mono hS_mono hq hm hr ht).mono (Set.Ici_subset_Ici.2 ht))
  have hG : ∀ x, G x = if 0 ≤ x then L x else 0 := fun x => rfl
  refine ⟨G, hG, ?_⟩
  set U := {t : ℝ | 0 ≤ t ∧ 0 < q t / r}
  have hU : G.measure U = 0 := by
    apply null_of_flat G U
    intro t ht
    have hqt : 0 < q t := by have := ht.2; exact (div_pos_iff_of_pos_right hr).1 this
    constructor
    · obtain ⟨δ, hδ, hrc⟩ := q_rc a' S q ha_mono hS_mono hq ha_rc hS_rc ht.1
      obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show t < t + δ by linarith)
      refine ⟨p, hp1, ?_⟩
      have hB := Bf_const a' S q ha_mono hS_mono hq (c := 1) ht.1 hp1.le (fun y hy => by
        have : q y = q t := hrc y hy.1 (lt_of_le_of_lt hy.2 hp2)
        simp [ind, this, hqt])
      rw [hG, hG, if_pos (ht.1.trans hp1.le), if_pos ht.1]
      simp only [L]
      congr 2
      linarith
    · have hmono : Monotone G := G.mono
      apply le_antisymm (hmono.leftLim_le le_rfl)
      rcases eq_or_lt_of_le ht.1 with h0 | hpos
      · rw [← h0, hG, if_pos le_rfl]
        have hL0 : L 0 = 0 := L_zero a' S q ha_mono hS_mono hq hm hr
        rw [hL0]
        have := hmono.le_leftLim (show (-1:ℝ) < 0 by norm_num)
        rw [hG, if_neg (by norm_num)] at this
        exact this
      · apply le_of_eq
        symm
        rw [← hmono.continuousWithinAt_Iio_iff_leftLim_eq, ← continuousWithinAt_Ioo_iff_Iio hpos]
        have hc := (L_cont a' S q ha_mono hS_mono hq hm hr ht.1).mono
          (show Set.Ioo 0 t ⊆ Set.Ici 0 from fun y hy => hy.1.le)
        apply hc.congr
        · intro y hy; rw [hG, if_pos hy.1.le]
        · rw [hG, if_pos ht.1]
  have : ∀ᵐ t ∂(G.measure.restrict (Set.Ici 0)), ENNReal.ofReal (q t / r) = 0 := by
    rw [ae_restrict_iff' measurableSet_Ici]
    apply measure_mono_null _ hU
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_Ici, ENNReal.ofReal_eq_zero,
      _root_.not_imp, not_le] at ht
    exact ht
  rw [lintegral_congr_ae this, lintegral_zero]


omit hm in
lemma q_cadlag (ha_rc : ∀ x, ∃ δ > 0, ∀ y, x ≤ y → y < x + δ → a' y = a' x)
    (hS_rc : ∀ x, ∃ δ > 0, ∀ y, x ≤ y → y < x + δ → S y = S x) :
    IsCadlag (fun t => q t / r) := by
  constructor
  · intro t ht
    obtain ⟨δ, hδ, hrc⟩ := q_rc a' S q ha_mono hS_mono hq ha_rc hS_rc ht
    have heq : (fun y => q y / r) =ᶠ[𝓝[≥] t] fun _ => q t / r := by
      filter_upwards [Ico_mem_nhdsGE (show t < t + δ by linarith)] with y hy
      rw [hrc y hy.1 hy.2]
    exact continuousWithinAt_const.congr_of_eventuallyEq heq rfl
  · intro t ht
    have h1 := ha_mono.tendsto_nhdsLT t
    have hSm : MonotoneOn (fun y => (S (Bf q y) : ℝ)) (Set.Ici 0) := fun a ha b hb hab =>
      Nat.cast_le.2 (hS_mono (Bf_monoOn a' S q ha_mono hS_mono hq ha hb hab))
    obtain ⟨l2, h2⟩ := monotoneOn_leftlim hSm ht
    refine ⟨_, ((h1.sub h2).div_const r).congr' ?_⟩
    filter_upwards [Ioo_mem_nhdsLT ht] with y hy
    rw [hq' a' S q hq y hy.1.le]

end busy2

lemma psum_zero {x : ℕ → ℝ} : partialSum x 0 = 0 := by simp [partialSum]

lemma psum_strictMono {x : ℕ → ℝ} (hx : ∀ i, 0 < x i) : StrictMono (partialSum x) := by
  apply strictMono_nat_of_lt_succ
  intro n
  simp only [partialSum]
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
  linarith [hx (n + 1)]

lemma scaled_mono {X : ℕ → ℝ} (hX0 : X 0 = 0) (hXs : StrictMono X) (hXt : Tendsto X atTop atTop)
    {c : ℝ} (hc : 0 < c) : Monotone (fun r => (renewalCount X (c * r)).toNat) :=
  fun a b hab => R_mono hX0 hXs hXt (mul_le_mul_of_nonneg_left hab hc.le)

lemma scaled_rc {X : ℕ → ℝ} (hX0 : X 0 = 0) (hXs : StrictMono X) (hXt : Tendsto X atTop atTop)
    {c : ℝ} (hc : 0 < c) (x : ℝ) : ∃ δ > 0, ∀ y, x ≤ y → y < x + δ →
      (renewalCount X (c * y)).toNat = (renewalCount X (c * x)).toNat := by
  obtain ⟨δ, hδ, h⟩ := R_rightconst hX0 hXs hXt (c * x)
  refine ⟨δ / c, div_pos hδ hc, fun y hy1 hy2 => h _ (mul_le_mul_of_nonneg_left hy1 hc.le) ?_⟩
  have : c * y < c * (x + δ / c) := mul_lt_mul_of_pos_left hy2 hc
  rw [mul_add, mul_div_cancel₀ _ hc.ne'] at this
  exact this

lemma scaled_lj {X : ℕ → ℝ} (hX0 : X 0 = 0) (hXs : StrictMono X) (hXt : Tendsto X atTop atTop)
    {c : ℝ} (hc : 0 < c) (x : ℝ) : ∃ δ > 0, ∀ y, x - δ < y → y ≤ x →
      (renewalCount X (c * x)).toNat ≤ (renewalCount X (c * y)).toNat + 1 := by
  obtain ⟨δ, hδ, h⟩ := R_leftjump hX0 hXs hXt (c * x)
  refine ⟨δ / c, div_pos hδ hc, fun y hy1 hy2 => h _ ?_ (mul_le_mul_of_nonneg_left hy2 hc.le)⟩
  have : c * (x - δ / c) < c * y := mul_lt_mul_of_pos_left hy1 hc
  rw [mul_sub, mul_div_cancel₀ _ hc.ne'] at this
  exact this

end JSEQR21Aux


namespace JSEQMWD
open JSEQA2Aux JSEQR21Aux

section renewal2
variable {X : ℕ → ℝ} (hX0 : X 0 = 0) (hXs : StrictMono X) (hXt : Tendsto X atTop atTop)
include hX0 hXs hXt

lemma R_ge_iff {y : ℝ} (hy : 0 ≤ y) (m : ℕ) : m ≤ (renewalCount X y).toNat ↔ X m ≤ y := by
  obtain ⟨m0, h1, h2⟩ := exists_m hX0 hXt hy
  rw [R_eq hX0 hXs hXt h1 h2]
  constructor
  · intro h; exact (hXs.monotone h).trans h1
  · intro h
    by_contra hc
    push Not at hc
    have := hXs.monotone (show m0 + 1 ≤ m by omega)
    linarith

end renewal2


/-! ### Single-server construction -/

noncomputable def ssW (Y : ℕ → ℝ) (c : ℝ) (α : ℝ → ℕ) (s : ℝ) : ℝ := Y (α s) / c
noncomputable def ssy (Y : ℕ → ℝ) (c : ℝ) (α : ℝ → ℕ) (s : ℝ) : ℝ := ssW Y c α s - s
noncomputable def ssI (Y : ℕ → ℝ) (c : ℝ) (α : ℝ → ℕ) (s : ℝ) : ℝ := skorokhodReg (ssy Y c α) s
noncomputable def ssq (Y : ℕ → ℝ) (c : ℝ) (α : ℝ → ℕ) (s : ℝ) : ℝ :=
  (α s : ℝ) - ((renewalCount Y (c * (s - ssI Y c α s))).toNat : ℝ)

section single
variable {Y : ℕ → ℝ} (hY0 : Y 0 = 0) (hYs : StrictMono Y) (hYt : Tendsto Y atTop atTop)
  {c : ℝ} (hc : 0 < c) {α : ℝ → ℕ} (hα_mono : Monotone α)
  (hα_rc : ∀ x, ∃ δ > 0, ∀ y, x ≤ y → y < x + δ → α y = α x) (hα0 : α 0 = 0)

include hYs hc hα_mono in
lemma ssW_mono : Monotone (ssW Y c α) := fun a b hab =>
  div_le_div_of_nonneg_right (hYs.monotone (hα_mono hab)) hc.le

include hY0 hYs hc in
lemma ssW_nonneg (s : ℝ) : 0 ≤ ssW Y c α s := by
  unfold ssW
  apply div_nonneg _ hc.le
  have := hYs.monotone (Nat.zero_le (α s)); rw [hY0] at this; exact this

include hYs hc hα_mono hα_rc in
lemma ssy_cadlag : IsCadlag (ssy Y c α) := by
  constructor
  · intro t _
    obtain ⟨δ, hδ, h⟩ := hα_rc t
    have heq : ssW Y c α =ᶠ[𝓝[≥] t] fun _ => ssW Y c α t := by
      filter_upwards [Ico_mem_nhdsGE (show t < t + δ by linarith)] with y hy
      simp only [ssW, h y hy.1 hy.2]
    exact (continuousWithinAt_const.congr_of_eventuallyEq heq rfl).sub continuousWithinAt_id
  · intro t _
    exact ⟨_, ((ssW_mono hYs hc hα_mono).tendsto_nhdsLT t).sub
      (continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds)⟩

include hY0 hα0 in
lemma ssy_zero : ssy Y c α 0 = 0 := by simp [ssy, ssW, hα0, hY0]

include hY0 hYs hc hα_mono hα_rc hα0 in
lemma ssI_le {t : ℝ} (ht : 0 ≤ t) : ssI Y c α t ≤ t := by
  apply reg_le _ ht
  intro r hr
  have := ssW_nonneg hY0 hYs hc (α := α) r
  simp only [ssy]
  exact max_le (by linarith [hr.2]) ht

include hY0 hYs hc hα_mono hα_rc hα0 in
lemma ssI_lip {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) : ssI Y c α r ≤ ssI Y c α s + (r - s) := by
  have hx := ssy_cadlag hYs hc hα_mono hα_rc
  apply reg_le_of_near _ hx hs hsr (by linarith)
  intro u hu
  have h1 := ssW_mono hYs hc hα_mono hu.1
  have h2 := neg_le_reg _ hx (t := s) (r := s) ⟨hs, le_rfl⟩
  simp only [ssy] at h2 ⊢
  linarith [hu.2]

include hY0 hYs hc hα_mono hα_rc hα0 in
lemma ssI_contOn : ContinuousOn (ssI Y c α) (Set.Ici 0) := by
  have hx := ssy_cadlag hYs hc hα_mono hα_rc
  rw [Metric.continuousOn_iff]
  intro t ht ε hε
  refine ⟨ε, hε, fun r hr hd => ?_⟩
  rw [Real.dist_eq] at hd ⊢
  rcases le_total t r with h | h
  · have h1 := ssI_lip hY0 hYs hc hα_mono hα_rc hα0 ht h
    have h2 := reg_mono _ hx ht hr h
    unfold ssI at h1 ⊢
    rw [abs_lt] at hd ⊢; constructor <;> linarith
  · have h1 := ssI_lip hY0 hYs hc hα_mono hα_rc hα0 hr h
    have h2 := reg_mono _ hx hr ht h
    unfold ssI at h1 ⊢
    rw [abs_lt] at hd ⊢; constructor <;> linarith

include hY0 hYs hc hα_mono hα_rc hα0 in
lemma ssI_mono : Monotone (ssI Y c α) := by
  have hx := ssy_cadlag hYs hc hα_mono hα_rc
  intro a b hab
  unfold ssI
  rcases lt_or_ge a 0 with ha | ha
  · have : skorokhodReg (ssy Y c α) a = 0 := by
      unfold skorokhodReg
      rw [Set.Icc_eq_empty (by linarith), Set.image_empty, Real.sSup_empty]
    rw [this]
    rcases lt_or_ge b 0 with hb | hb
    · unfold skorokhodReg
      rw [Set.Icc_eq_empty (by linarith), Set.image_empty, Real.sSup_empty]
    · exact reg_nonneg _ hx hb
  · exact reg_mono _ hx ha (ha.trans hab) hab

include hY0 hYs hYt hc hα_mono hα_rc hα0 in
lemma ssq_pos_iff {s : ℝ} (hs : 0 ≤ s) :
    0 < ssq Y c α s ↔ 0 < JSEQDelay.Diffusion.Gamma1 (ssy Y c α) s := by
  have hB : 0 ≤ c * (s - ssI Y c α s) :=
    mul_nonneg hc.le (by linarith [ssI_le hY0 hYs hc hα_mono hα_rc hα0 hs])
  have key := R_ge_iff hY0 hYs hYt hB (α s)
  simp only [ssq, JSEQDelay.Diffusion.Gamma1, ssy, ssW]
  unfold ssI at hB key ⊢
  rw [sub_pos, sub_add_eq_add_sub, sub_pos]
  constructor
  · intro h
    have h1 : ¬ α s ≤ (renewalCount Y (c * (s - skorokhodReg (ssy Y c α) s))).toNat := by
      intro h'; have : ((renewalCount Y (c * (s - skorokhodReg (ssy Y c α) s))).toNat : ℝ) ≥ α s :=
        by exact_mod_cast h'
      linarith
    rw [key] at h1
    push Not at h1
    have : s - skorokhodReg (ssy Y c α) s < Y (α s) / c := by rw [lt_div_iff₀ hc]; linarith
    linarith
  · intro h
    have h1 : ¬ Y (α s) ≤ c * (s - skorokhodReg (ssy Y c α) s) := by
      have h' : s - skorokhodReg (ssy Y c α) s < Y (α s) / c := by linarith
      rw [lt_div_iff₀ hc] at h'; push Not; linarith
    rw [← key] at h1
    push Not at h1
    exact_mod_cast h1


include hY0 hYs hc hα_mono hα_rc hα0 in
lemma ssI_deriv {x : ℝ} (hx0 : 0 ≤ x) :
    HasDerivWithinAt (ssI Y c α)
      (if 0 < JSEQDelay.Diffusion.Gamma1 (ssy Y c α) x then 0 else 1) (Set.Ioi x) x := by
  have hx := ssy_cadlag hYs hc hα_mono hα_rc
  split_ifs with hZ
  · obtain ⟨δ, hδ, hnear⟩ := eventually_near _ hx hx0 hZ
    apply (hasDerivWithinAt_const x _ (ssI Y c α x)).congr_of_eventuallyEq _ rfl
    filter_upwards [Ioo_mem_nhdsGT (show x < x + δ by linarith)] with r hr
    apply le_antisymm
    · have := reg_le_of_near _ hx (c := 0) hx0 hr.1.le le_rfl (fun u hu => by
        have h1 := (abs_lt.1 (hnear u ⟨hu.1, lt_of_le_of_lt hu.2 hr.2⟩)).1
        simp only [JSEQDelay.Diffusion.Gamma1] at h1
        linarith)
      simpa [ssI] using this
    · exact reg_mono _ hx hx0 (hx0.trans hr.1.le) hr.1.le
  · push Not at hZ
    have hZ0 := gamma1_nonneg _ hx hx0
    have hIx : ssI Y c α x = -ssy Y c α x := by
      simp only [JSEQDelay.Diffusion.Gamma1] at hZ hZ0; unfold ssI; linarith
    obtain ⟨δ, hδ, hrc⟩ := hα_rc x
    have hd : HasDerivWithinAt (fun r => ssI Y c α x + (r - x)) 1 (Set.Ioi x) x := by
      have := ((hasDerivAt_id x).sub_const x).const_add (ssI Y c α x)
      simpa using this.hasDerivWithinAt
    apply hd.congr_of_eventuallyEq _ (by simp)
    filter_upwards [Ioo_mem_nhdsGT (show x < x + δ by linarith)] with r hr
    have hWeq : ∀ u, x ≤ u → u < x + δ → ssW Y c α u = ssW Y c α x := fun u h1 h2 => by
      simp only [ssW, hrc u h1 h2]
    apply le_antisymm
    · have := reg_le_of_near _ hx (c := r - x) hx0 hr.1.le (by linarith [hr.1]) (fun u hu => by
        have := hWeq u hu.1 (lt_of_le_of_lt hu.2 hr.2)
        simp only [ssy] at hIx ⊢
        unfold ssI at hIx
        linarith [hu.2])
      exact this
    · have h1 := neg_le_reg _ hx (t := r) (r := r) ⟨hx0.trans hr.1.le, le_rfl⟩
      have := hWeq r hr.1.le hr.2
      simp only [ssy] at h1 hIx
      unfold ssI at hIx ⊢
      linarith

include hY0 hYs hYt hc hα_mono hα_rc hα0 in
/-- The single-server queue `ssq` satisfies the network equation (8) with (7). -/
lemma ssq_eq {t : ℝ} (ht : 0 ≤ t) :
    ssq Y c α t = (α t : ℝ) - ((renewalCount Y
      (c * ∫ s in (0:ℝ)..t, if 0 < ssq Y c α s then (1:ℝ) else 0)).toNat : ℝ) := by
  have hx := ssy_cadlag hYs hc hα_mono hα_rc
  set f' : ℝ → ℝ := fun x => if 0 < JSEQDelay.Diffusion.Gamma1 (ssy Y c α) x then 0 else 1
  have hmeas : Measurable f' := by
    have h1 : Measurable (ssy Y c α) :=
      (ssW_mono hYs hc hα_mono).measurable.sub measurable_id
    have h2 : Measurable (ssI Y c α) := (ssI_mono hY0 hYs hc hα_mono hα_rc hα0).measurable
    have h3 : Measurable (JSEQDelay.Diffusion.Gamma1 (ssy Y c α)) := h1.add h2
    exact Measurable.ite (measurableSet_lt measurable_const h3) measurable_const measurable_const
  have hint : IntervalIntegrable f' volume 0 t := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2 ?_
    refine Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
      hmeas.aestronglyMeasurable (Eventually.of_forall fun s => ?_)
    simp only [f']; split_ifs <;> norm_num
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
    ((ssI_contOn hY0 hYs hc hα_mono hα_rc hα0).mono Set.Icc_subset_Ici_self)
    (fun x hx' => ssI_deriv hY0 hYs hc hα_mono hα_rc hα0 hx'.1.le) hint
  have hI0 : ssI Y c α 0 = 0 := reg_zero _ hx (by rw [ssy_zero hY0 hα0])
  have hcongr : ∫ s in (0:ℝ)..t, (if 0 < ssq Y c α s then (1:ℝ) else 0) =
      ∫ s in (0:ℝ)..t, (1 - f' s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le ht] at hs
    simp only [f', ssq_pos_iff hY0 hYs hYt hc hα_mono hα_rc hα0 hs.1]
    split_ifs <;> norm_num
  rw [hcongr, intervalIntegral.integral_sub intervalIntegrable_const hint, hFTC, hI0]
  simp [ssq]

end single


/-! ### Single-server uniqueness -/
lemma busy_unique (a' : ℝ → ℝ) (S : ℝ → ℕ) (q1 q2 : ℝ → ℝ)
    (ha_mono : Monotone a') (hS_mono : Monotone S)
    (ha_rc : ∀ x, ∃ δ > 0, ∀ y, x ≤ y → y < x + δ → a' y = a' x)
    (hS_rc : ∀ x, ∃ δ > 0, ∀ y, x ≤ y → y < x + δ → S y = S x)
    (hq1 : ∀ t, 0 ≤ t → q1 t = a' t - S (∫ s in (0:ℝ)..t, if 0 < q1 s then (1:ℝ) else 0))
    (hq2 : ∀ t, 0 ≤ t → q2 t = a' t - S (∫ s in (0:ℝ)..t, if 0 < q2 s then (1:ℝ) else 0))
    {t : ℝ} (ht : 0 ≤ t) : q1 t = q2 t := by
  by_contra hcon
  set E := {t : ℝ | 0 ≤ t ∧ q1 t ≠ q2 t}
  have hEne : E.Nonempty := ⟨t, ht, hcon⟩
  have hEbdd : BddBelow E := ⟨0, fun s hs => hs.1⟩
  set t0 := sInf E
  have ht00 : 0 ≤ t0 := le_csInf hEne (fun s hs => hs.1)
  have hbefore : ∀ s, 0 ≤ s → s < t0 → q1 s = q2 s := by
    intro s hs hst
    by_contra hc
    have := csInf_le hEbdd ⟨hs, hc⟩
    linarith
  have hB : Bf q1 t0 = Bf q2 t0 := by
    unfold Bf
    apply intervalIntegral.integral_congr_ae
    have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ t0 := by
      rw [ae_iff]; simp
    filter_upwards [hne] with x hx hxI
    rw [Set.uIoc_of_le ht00] at hxI
    simp only [ind, hbefore x hxI.1.le (lt_of_le_of_ne hxI.2 hx)]
  have heq0 : q1 t0 = q2 t0 := by
    rw [hq' a' S q1 hq1 t0 ht00, hq' a' S q2 hq2 t0 ht00, hB]
  obtain ⟨δ1, hδ1, h1⟩ := q_rc a' S q1 ha_mono hS_mono hq1 ha_rc hS_rc ht00
  obtain ⟨δ2, hδ2, h2⟩ := q_rc a' S q2 ha_mono hS_mono hq2 ha_rc hS_rc ht00
  obtain ⟨e, he, hlt⟩ := exists_lt_of_csInf_lt hEne (show t0 < t0 + min δ1 δ2 by
    have := lt_min hδ1 hδ2; linarith)
  have hte := csInf_le hEbdd he
  apply he.2
  rw [h1 e hte (by linarith [min_le_left δ1 δ2]), h2 e hte (by linarith [min_le_right δ1 δ2]), heq0]


/-! ### The routing rule -/
open JSEQDelay.Diffusion in
lemma exists_routed {K : ℕ} (d0 : Fin K) (r : Fin K → ℝ) : ∃ k, RoutedTo r k := by
  classical
  obtain ⟨k0, -, hk0⟩ := Finset.exists_min_image Finset.univ r ⟨d0, Finset.mem_univ _⟩
  set M := Finset.univ.filter (fun k => ∀ l, r k ≤ r l)
  have hM : M.Nonempty := ⟨k0, by simp [M]; exact fun l => hk0 l (Finset.mem_univ _)⟩
  refine ⟨M.min' hM, ?_, ?_⟩
  · intro j hj
    have hmem := Finset.min'_mem M hM
    simp only [M, Finset.mem_filter] at hmem
    rcases lt_or_eq_of_le (hmem.2 j) with h | h
    · exact h
    · exfalso
      have : j ∈ M := by
        simp only [M, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, fun l => h ▸ hmem.2 l⟩
      have := Finset.min'_le M j this
      exact absurd hj (not_lt.2 this)
  · intro l _
    have hmem := Finset.min'_mem M hM
    simp only [M, Finset.mem_filter] at hmem
    exact hmem.2 l

open JSEQDelay.Diffusion in
lemma routed_unique {K : ℕ} {r : Fin K → ℝ} {k k' : Fin K} (h : RoutedTo r k) (h' : RoutedTo r k') :
    k = k' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := h'.1 k hlt; have := h.2 k' hlt.le; linarith
  · have := h.1 k' hlt; have := h'.2 k hlt.le; linarith

open JSEQDelay.Diffusion in
noncomputable def route {K : ℕ} (d0 : Fin K) (r : Fin K → ℝ) : Fin K :=
  Classical.choose (exists_routed d0 r)

open JSEQDelay.Diffusion in
lemma routed_iff {K : ℕ} (d0 : Fin K) (r : Fin K → ℝ) (k : Fin K) :
    RoutedTo r k ↔ route d0 r = k :=
  ⟨fun h => routed_unique (Classical.choose_spec (exists_routed d0 r)) h,
   fun h => h ▸ Classical.choose_spec (exists_routed d0 r)⟩

/-! ### Left limits of `Φ` -/

lemma comp_leftlim {f : ℝ → ℝ} (hf : IsCadlag f) {τ' : ℝ → ℝ} (hmono : MonotoneOn τ' (Set.Ici 0))
    (hnn : ∀ s, 0 ≤ s → 0 ≤ τ' s) {t : ℝ} (ht : 0 < t) :
    ∃ l, Tendsto (fun s => f (τ' s)) (𝓝[<] t) (𝓝 l) := by
  set τm : ℝ → ℝ := fun s => τ' (max s 0)
  have hm : Monotone τm := fun a b hab =>
    hmono (show (0:ℝ) ≤ max a 0 from le_max_right _ _) (show (0:ℝ) ≤ max b 0 from le_max_right _ _)
      (max_le_max hab le_rfl)
  have hev : ∀ᶠ s in 𝓝[<] t, f (τm s) = f (τ' s) := by
    filter_upwards [Ioo_mem_nhdsLT ht] with s hs
    simp [τm, max_eq_left hs.1.le]
  set L := Function.leftLim τm t
  have hT : Tendsto τm (𝓝[<] t) (𝓝 L) := hm.tendsto_leftLim t
  by_cases hA : ∃ s0 < t, τm s0 = L
  · obtain ⟨s0, hs0, hL⟩ := hA
    refine ⟨f L, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [Ioo_mem_nhdsLT hs0, hev] with s hs hfs
    rw [← hfs]
    have h1 := hm hs.1.le
    have h2 := hm.le_leftLim hs.2
    have h3 : L ≤ τm s := hL ▸ h1
    rw [show τm s = L from le_antisymm h2 h3]
  · push Not at hA
    have hlt : ∀ s < t, τm s < L := fun s hs => lt_of_le_of_ne (hm.le_leftLim hs) (hA s hs)
    have hLpos : 0 < L := by
      have := hlt (t / 2) (by linarith)
      have h0 : 0 ≤ τm (t / 2) := hnn _ (le_max_right _ _)
      linarith
    obtain ⟨l, hl⟩ := hf.2 L hLpos
    have hT' : Tendsto τm (𝓝[<] t) (𝓝[<] L) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hT
        (by filter_upwards [self_mem_nhdsWithin] with s hs using hlt s hs)
    exact ⟨l, (hl.comp hT').congr' hev⟩


open JSEQDelay.Diffusion

lemma tau_le' {K : ℕ} {τ : ℝ → Fin K → ℝ} (hτ : DelayFunction τ) {s : ℝ} (hs : 0 ≤ s) (k : Fin K) :
    τ s k ≤ s := by
  rcases eq_or_lt_of_le hs with h0 | hpos
  · subst h0
    by_contra hc
    push Not at hc
    have hε : 0 < τ 0 k / 2 := by linarith
    have h1 := hτ.2.1 k (Set.mem_Ici.2 (le_refl (0:ℝ))) (Set.mem_Ici.2 hε.le) hε.le
    have h2 := hτ.2.2 _ hε k
    simp only at h1
    linarith
  · exact hτ.2.2 s hpos k

lemma cadlag_leftlim {f : ℝ → ℝ} (hf : IsCadlag f) {t : ℝ} (ht : 0 < t) :
    ∃ l, Tendsto f (𝓝[<] t) (𝓝 l) := hf.2 t ht

lemma phi_leftlim {K : ℕ} {mu : Fin K → ℝ} {τ : ℝ → Fin K → ℝ} (hτ : DelayFunction τ)
    {Ψ : Path K → Path K → Path K} (hΨ : IsEstimator τ Ψ) {q a : Path K} (hD : IsD0Pair q a)
    {t : ℝ} (ht : 0 < t) (j : Fin K) :
    ∃ l, Tendsto (fun s => Phi mu τ Ψ q a s j) (𝓝[<] t) (𝓝 l) := by
  have hτm : MonotoneOn (fun s => τ s j) (Set.Ici 0) := hτ.2.1 j
  have hτn : ∀ s, 0 ≤ s → 0 ≤ τ s j := fun s hs => hτ.1 s hs j
  obtain ⟨l1, h1⟩ := comp_leftlim (hD.1 j) hτm hτn ht
  obtain ⟨l2, h2⟩ := (hD.2.1 j).2 t ht
  obtain ⟨l3, h3⟩ := comp_leftlim (hD.2.1 j) hτm hτn ht
  obtain ⟨l4, h4⟩ := monotoneOn_leftlim hτm ht
  obtain ⟨l5, h5⟩ := ((hΨ.2.1 q a hD).1 j).2 t ht
  have hid : Tendsto (fun s : ℝ => s) (𝓝[<] t) (𝓝 t) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  exact ⟨_, (((h1.add (h2.sub h3)).sub ((hid.sub h4).const_mul (mu j))).add h5)⟩

lemma leftLim_congr' {f g : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (hf : ∃ l, Tendsto f (𝓝[<] t) (𝓝 l))
    (heq : ∀ s ∈ Set.Ioo 0 t, f s = g s) : Function.leftLim f t = Function.leftLim g t := by
  obtain ⟨l, hl⟩ := hf
  have hg : Tendsto g (𝓝[<] t) (𝓝 l) := hl.congr' (by
    filter_upwards [Ioo_mem_nhdsLT ht] with s hs using heq s hs)
  rw [leftLim_eq_of_tendsto hl, leftLim_eq_of_tendsto hg]

lemma cadlag_congr {f g : ℝ → ℝ} (hf : IsCadlag f) (heq : ∀ t, 0 ≤ t → f t = g t) : IsCadlag g := by
  constructor
  · intro t ht
    exact (hf.1 t ht).congr (fun y hy => (heq y (ht.trans hy)).symm) (heq t ht).symm
  · intro t ht
    obtain ⟨l, hl⟩ := hf.2 t ht
    refine ⟨l, hl.congr' ?_⟩
    filter_upwards [Ioo_mem_nhdsLT ht] with s hs using heq s hs.1.le


/-! ### The candidate network for a routing sequence `d` -/
section net
variable {K : ℕ} {Ω : Type*} (u : ℕ → Ω → ℝ) (v : Fin K → ℕ → Ω → ℝ) (lam : ℝ)
  (mu : Fin K → ℝ) (τ : ℝ → Fin K → ℝ) (Ψ : Path K → Path K → Path K) (ω : Ω)

noncomputable def alphaD (d : ℕ → Fin K) (k : Fin K) (t : ℝ) : ℕ :=
  ((Finset.Icc 1 (arrivalCount u lam ω (max t 0))).filter (fun i => d i = k)).card

noncomputable def aD (d : ℕ → Fin K) : Path K := fun t k => (alphaD u lam ω d k t : ℝ)

noncomputable def qD (d : ℕ → Fin K) : Path K :=
  fun t k => ssq (partialSum (fun i => v k i ω)) (mu k) (alphaD u lam ω d k) t

variable {u v lam mu ω}
variable (hu : ∀ i ω, 0 < u i ω) (hv : ∀ k i ω, 0 < v k i ω) (hlam : 0 < lam)
  (hmu : ∀ k, 0 < mu k) (hω : GoodPath u v ω)

include hu hω hlam in
lemma N_mono : Monotone (fun t => arrivalCount u lam ω t) :=
  scaled_mono psum_zero (psum_strictMono (fun i => hu i ω)) hω.1 hlam

include hu hω hlam in
lemma N_rc (x : ℝ) : ∃ δ > 0, ∀ y, x ≤ y → y < x + δ →
    arrivalCount u lam ω y = arrivalCount u lam ω x :=
  scaled_rc psum_zero (psum_strictMono (fun i => hu i ω)) hω.1 hlam x

include hu hω hlam in
lemma N_zero : arrivalCount u lam ω 0 = 0 := by
  unfold arrivalCount
  rw [mul_zero]
  exact R_zero psum_zero (psum_strictMono (fun i => hu i ω)) hω.1

include hu hlam in
lemma sigma_pos {i : ℕ} (hi : 1 ≤ i) : 0 < arrivalEpoch u lam ω i := by
  unfold arrivalEpoch
  apply div_pos _ hlam
  have := psum_strictMono (fun i => hu i ω) (show 0 < i by omega)
  rw [psum_zero] at this; exact this

include hu hω hlam in
lemma N_lt {i : ℕ} {s : ℝ} (hs : 0 ≤ s) (hsi : s < arrivalEpoch u lam ω i) :
    arrivalCount u lam ω s < i := by
  have key := R_ge_iff psum_zero (psum_strictMono (fun i => hu i ω)) hω.1
    (mul_nonneg hlam.le hs) i
  unfold arrivalCount
  by_contra hc
  push Not at hc
  rw [key] at hc
  unfold arrivalEpoch at hsi
  rw [lt_div_iff₀ hlam] at hsi
  linarith

include hu hω hlam in
lemma alpha_mono (d : ℕ → Fin K) (k : Fin K) : Monotone (alphaD u lam ω d k) := by
  intro a b hab
  unfold alphaD
  exact Finset.card_le_card (Finset.filter_subset_filter _
    (Finset.Icc_subset_Icc_right (N_mono hu hlam hω (max_le_max hab le_rfl))))

include hu hω hlam in
lemma alpha_rc (d : ℕ → Fin K) (k : Fin K) (x : ℝ) : ∃ δ > 0, ∀ y, x ≤ y → y < x + δ →
    alphaD u lam ω d k y = alphaD u lam ω d k x := by
  rcases lt_or_ge x 0 with hx | hx
  · refine ⟨-x, by linarith, fun y _ hy2 => ?_⟩
    simp only [alphaD, max_eq_right hx.le, max_eq_right (show y ≤ 0 by linarith)]
  · obtain ⟨δ, hδ, h⟩ := N_rc hu hlam hω x
    refine ⟨δ, hδ, fun y hy1 hy2 => ?_⟩
    simp only [alphaD, max_eq_left hx, max_eq_left (hx.trans hy1), h y hy1 hy2]

include hu hω hlam in
lemma alpha_zero (d : ℕ → Fin K) (k : Fin K) : alphaD u lam ω d k 0 = 0 := by
  simp [alphaD, N_zero hu hlam hω]

lemma alpha_congr {d d' : ℕ → Fin K} {k : Fin K} {t : ℝ}
    (h : ∀ j, 1 ≤ j → j ≤ arrivalCount u lam ω (max t 0) → d j = d' j) :
    alphaD u lam ω d k t = alphaD u lam ω d' k t := by
  unfold alphaD
  congr 1
  apply Finset.filter_congr
  intro j hj
  rw [Finset.mem_Icc] at hj
  rw [h j hj.1 hj.2]

include hv hω in
lemma Y_facts (k : Fin K) : partialSum (fun i => v k i ω) 0 = 0 ∧
    StrictMono (partialSum (fun i => v k i ω)) ∧
    Tendsto (partialSum (fun i => v k i ω)) atTop atTop :=
  ⟨psum_zero, psum_strictMono (fun i => hv k i ω), hω.2 k⟩

include hu hv hlam hmu hω in
lemma qD_eq (d : ℕ → Fin K) (k : Fin K) {t : ℝ} (ht : 0 ≤ t) :
    qD u v lam mu ω d t k = aD u lam ω d t k -
      ((renewalCount (partialSum (fun i => v k i ω))
        (mu k * ∫ s in (0:ℝ)..t, if 0 < qD u v lam mu ω d s k then (1:ℝ) else 0)).toNat : ℝ) := by
  obtain ⟨hY0, hYs, hYt⟩ := Y_facts hv hω k
  exact ssq_eq hY0 hYs hYt (hmu k) (alpha_mono hu hlam hω d k) (alpha_rc hu hlam hω d k)
    (alpha_zero hu hlam hω d k) ht


include hu hv hlam hmu hω in
lemma qD_props (d : ℕ → Fin K) (k : Fin K) :
    IsCadlag (fun t => qD u v lam mu ω d t k) ∧ qD u v lam mu ω d 0 k = 0 ∧
    ∀ t, 0 ≤ t → 0 ≤ qD u v lam mu ω d t k := by
  obtain ⟨hY0, hYs, hYt⟩ := Y_facts hv hω k
  set a' : ℝ → ℝ := fun t => (alphaD u lam ω d k t : ℝ)
  set S : ℝ → ℕ := fun r => (renewalCount (partialSum (fun i => v k i ω)) (mu k * r)).toNat
  set q : ℝ → ℝ := fun t => qD u v lam mu ω d t k
  have ha_mono : Monotone a' := fun x y h => Nat.cast_le.2 (alpha_mono hu hlam hω d k h)
  have hS_mono : Monotone S := scaled_mono hY0 hYs hYt (hmu k)
  have hq : ∀ t, 0 ≤ t → q t = a' t - S (∫ s in (0:ℝ)..t, if 0 < q s then (1:ℝ) else 0) :=
    fun t ht => qD_eq hu hv hlam hmu hω d k ht
  have ha_rc : ∀ x, ∃ δ > 0, ∀ y, x ≤ y → y < x + δ → a' y = a' x := by
    intro x
    obtain ⟨δ, hδ, h⟩ := alpha_rc hu hlam hω d k x
    exact ⟨δ, hδ, fun y h1 h2 => by simp only [a', h y h1 h2]⟩
  have hS_rc := scaled_rc hY0 hYs hYt (hmu k)
  have hS_lj := scaled_lj hY0 hYs hYt (hmu k)
  have ha_int : ∀ t, ∃ m : ℕ, a' t = m := fun t => ⟨_, rfl⟩
  have hq0 : q 0 = 0 := by
    rw [hq 0 le_rfl]
    simp only [a', alpha_zero hu hlam hω d k, intervalIntegral.integral_same, S, mul_zero]
    rw [R_zero hY0 hYs hYt]; simp
  refine ⟨?_, hq0, fun t ht => q_nonneg a' S q ha_mono hS_mono hq ha_rc hS_rc hS_lj ha_int hq0 ht⟩
  have := q_cadlag a' S q ha_mono hS_mono hq one_pos ha_rc hS_rc
  exact cadlag_congr this (fun t _ => div_one _)

include hu hlam hω in
lemma aD_cadlag (d : ℕ → Fin K) (k : Fin K) : IsCadlag (fun t => aD u lam ω d t k) := by
  constructor
  · intro t _
    obtain ⟨δ, hδ, h⟩ := alpha_rc hu hlam hω d k t
    have heq : (fun t => aD u lam ω d t k) =ᶠ[𝓝[≥] t] fun _ => aD u lam ω d t k := by
      filter_upwards [Ico_mem_nhdsGE (show t < t + δ by linarith)] with y hy
      simp only [aD, h y hy.1 hy.2]
    exact continuousWithinAt_const.congr_of_eventuallyEq heq rfl
  · intro t _
    have hm : Monotone (fun t => aD u lam ω d t k) := fun x y h =>
      Nat.cast_le.2 (alpha_mono hu hlam hω d k h)
    exact ⟨_, hm.tendsto_nhdsLT t⟩

include hu hv hlam hmu hω in
lemma D0_D (d : ℕ → Fin K) : IsD0Pair (qD u v lam mu ω d) (aD u lam ω d) := by
  refine ⟨fun k => (qD_props hu hv hlam hmu hω d k).1, fun k => aD_cadlag hu hlam hω d k,
    ?_, ?_, fun t ht k => (qD_props hu hv hlam hmu hω d k).2.2 t ht⟩
  · funext k; exact (qD_props hu hv hlam hmu hω d k).2.1
  · funext k; simp [aD, alpha_zero hu hlam hω d k]

include hu hlam hω in
lemma qD_congr {d d' : ℕ → Fin K} {t : ℝ} (ht : 0 ≤ t)
    (h : ∀ j, 1 ≤ j → j ≤ arrivalCount u lam ω t → d j = d' j) (k : Fin K) :
    qD u v lam mu ω d t k = qD u v lam mu ω d' t k ∧ aD u lam ω d t k = aD u lam ω d' t k := by
  have hα : ∀ r ∈ Set.Icc 0 t, alphaD u lam ω d k r = alphaD u lam ω d' k r := by
    intro r hr
    apply alpha_congr
    intro j hj1 hj2
    apply h j hj1
    rw [max_eq_left hr.1] at hj2
    exact hj2.trans (N_mono hu hlam hω hr.2)
  have hI : ssI (partialSum (fun i => v k i ω)) (mu k) (alphaD u lam ω d k) t =
      ssI (partialSum (fun i => v k i ω)) (mu k) (alphaD u lam ω d' k) t := by
    unfold ssI skorokhodReg
    congr 1
    apply Set.image_congr
    intro r hr
    simp only [ssy, ssW, hα r hr]
  constructor
  · simp only [qD, ssq, hI, hα t ⟨ht, le_rfl⟩]
  · simp only [aD, hα t ⟨ht, le_rfl⟩]

include hu hv hlam hmu hω in
lemma Phi_congr (hΨ : IsEstimator τ Ψ) (hτ : DelayFunction τ) {d d' : ℕ → Fin K} {s : ℝ}
    (hs : 0 ≤ s) (h : ∀ j, 1 ≤ j → j ≤ arrivalCount u lam ω s → d j = d' j) (j : Fin K) :
    Phi mu τ Ψ (qD u v lam mu ω d) (aD u lam ω d) s j =
      Phi mu τ Ψ (qD u v lam mu ω d') (aD u lam ω d') s j := by
  have hsub : ∀ r, 0 ≤ r → r ≤ s → ∀ k, qD u v lam mu ω d r k = qD u v lam mu ω d' r k ∧
      aD u lam ω d r k = aD u lam ω d' r k := fun r hr hrs k =>
    qD_congr hu hlam hω hr (fun i h1 h2 => h i h1 (h2.trans (N_mono hu hlam hω hrs))) k
  have hτs := tau_le' hτ hs j
  have hτ0 := hτ.1 s hs j
  have hΨeq := hΨ.2.2 (qD u v lam mu ω d) (aD u lam ω d) (qD u v lam mu ω d') (aD u lam ω d')
    (D0_D hu hv hlam hmu hω d) (D0_D hu hv hlam hmu hω d') s hs
    (fun k r hr => (hsub r hr.1 (hr.2.trans (tau_le' hτ hs k)) k).1.symm)
    (fun r hr => funext fun k => (hsub r hr.1 hr.2 k).2.symm)
  simp only [Phi]
  rw [(hsub _ hτ0 hτs j).1, (hsub _ hτ0 hτs j).2, (hsub s hs le_rfl j).2, hΨeq]

include hu hv hlam hmu hω in
lemma leftLim_Phi_congr (hΨ : IsEstimator τ Ψ) (hτ : DelayFunction τ) {d d' : ℕ → Fin K} {i : ℕ}
    (hi : 1 ≤ i) (h : ∀ j, 1 ≤ j → j < i → d j = d' j) (j : Fin K) :
    Function.leftLim (fun s => Phi mu τ Ψ (qD u v lam mu ω d) (aD u lam ω d) s j)
        (arrivalEpoch u lam ω i) =
      Function.leftLim (fun s => Phi mu τ Ψ (qD u v lam mu ω d') (aD u lam ω d') s j)
        (arrivalEpoch u lam ω i) := by
  apply leftLim_congr' (sigma_pos hu hlam hi)
    (phi_leftlim hτ hΨ (D0_D hu hv hlam hmu hω d) (sigma_pos hu hlam hi) j)
  intro s hs
  exact Phi_congr τ Ψ hu hv hlam hmu hω hΨ hτ hs.1.le
    (fun l h1 h2 => h l h1 (lt_of_le_of_lt h2 (N_lt hu hlam hω hs.1.le hs.2))) j

end net

/-- The routing sequence, defined by strong recursion on the job index. -/
noncomputable def dSeq {K : ℕ} {Ω : Type*} (u : ℕ → Ω → ℝ) (v : Fin K → ℕ → Ω → ℝ) (lam : ℝ)
    (mu : Fin K → ℝ) (τ : ℝ → Fin K → ℝ) (Ψ : Path K → Path K → Path K) (ω : Ω) (d0 : Fin K)
    (i : ℕ) : Fin K :=
  route d0 (fun j => Function.leftLim (fun s => Phi mu τ Ψ
    (qD u v lam mu ω (fun l => if h : l < i then dSeq u v lam mu τ Ψ ω d0 l else d0))
    (aD u lam ω (fun l => if h : l < i then dSeq u v lam mu τ Ψ ω d0 l else d0)) s j)
    (arrivalEpoch u lam ω i))
termination_by i
decreasing_by all_goals exact h


section main
variable {K : ℕ} {Ω : Type*} {u : ℕ → Ω → ℝ} {v : Fin K → ℕ → Ω → ℝ} {lam : ℝ}
  {mu : Fin K → ℝ} {τ : ℝ → Fin K → ℝ} {Ψ : Path K → Path K → Path K} {ω : Ω}
  (hu : ∀ i ω, 0 < u i ω) (hv : ∀ k i ω, 0 < v k i ω) (hlam : 0 < lam)
  (hmu : ∀ k, 0 < mu k) (hω : GoodPath u v ω) (hτ : DelayFunction τ) (hΨ : IsEstimator τ Ψ)
include hu hv hlam hmu hω hτ hΨ

lemma dSeq_spec (d0 : Fin K) {i : ℕ} (hi : 1 ≤ i) :
    route d0 (fun j => Function.leftLim (fun s => Phi mu τ Ψ
      (qD u v lam mu ω (dSeq u v lam mu τ Ψ ω d0)) (aD u lam ω (dSeq u v lam mu τ Ψ ω d0)) s j)
      (arrivalEpoch u lam ω i)) = dSeq u v lam mu τ Ψ ω d0 i := by
  conv_rhs => rw [dSeq]
  congr 1
  funext j
  apply leftLim_Phi_congr τ Ψ hu hv hlam hmu hω hΨ hτ hi
  intro l _ hl
  simp [hl]

lemma dSeq_path (d0 : Fin K) :
    IsJSEQPath u v lam mu τ Ψ ω (qD u v lam mu ω (dSeq u v lam mu τ Ψ ω d0))
      (aD u lam ω (dSeq u v lam mu τ Ψ ω d0)) := by
  classical
  set dS := dSeq u v lam mu τ Ψ ω d0
  have hD := D0_D hu hv hlam hmu hω dS
  refine ⟨hD.2.2.1, hD.2.2.2.1, fun t ht k => qD_eq hu hv hlam hmu hω dS k ht, fun t ht k => ?_⟩
  simp only [aD, alphaD, max_eq_left ht]
  congr 1
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i hi
  rw [Finset.mem_Icc] at hi
  rw [routed_iff d0, dSeq_spec hu hv hlam hmu hω hτ hΨ d0 hi.1]

lemma sol_eq (d0 : Fin K) {q a : Path K} (hsol : IsJSEQPath u v lam mu τ Ψ ω q a) {t : ℝ}
    (ht : 0 ≤ t) :
    q t = qD u v lam mu ω (dSeq u v lam mu τ Ψ ω d0) t ∧
      a t = aD u lam ω (dSeq u v lam mu τ Ψ ω d0) t := by
  classical
  obtain ⟨hq0, ha0, hqeq, haeq⟩ := hsol
  set dS := dSeq u v lam mu τ Ψ ω d0
  set d' : ℕ → Fin K := fun i => route d0 (fun j =>
    Function.leftLim (fun s => Phi mu τ Ψ q a s j) (arrivalEpoch u lam ω i))
  have ha' : ∀ t, 0 ≤ t → ∀ k, a t k = aD u lam ω d' t k := by
    intro t ht k
    rw [haeq t ht k]
    simp only [aD, alphaD, max_eq_left ht]
    congr 1
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro i _
    rw [routed_iff d0]
  have hq' : ∀ t, 0 ≤ t → ∀ k, q t k = qD u v lam mu ω d' t k := by
    intro t ht k
    obtain ⟨hY0, hYs, hYt⟩ := Y_facts hv hω k
    apply busy_unique (fun t => (alphaD u lam ω d' k t : ℝ))
      (fun r => (renewalCount (partialSum (fun i => v k i ω)) (mu k * r)).toNat)
      (fun t => q t k) (fun t => qD u v lam mu ω d' t k)
      (fun x y h => Nat.cast_le.2 (alpha_mono hu hlam hω d' k h))
      (scaled_mono hY0 hYs hYt (hmu k))
      (fun x => by
        obtain ⟨δ, hδ, h⟩ := alpha_rc hu hlam hω d' k x
        exact ⟨δ, hδ, fun y h1 h2 => by simp only [h y h1 h2]⟩)
      (scaled_rc hY0 hYs hYt (hmu k)) _ _ ht
    · intro s hs
      rw [hqeq s hs k, ha' s hs k]
      rfl
    · intro s hs
      exact qD_eq hu hv hlam hmu hω d' k hs
  have hD' := D0_D hu hv hlam hmu hω d'
  have hD : IsD0Pair q a := by
    refine ⟨fun k => cadlag_congr (hD'.1 k) (fun t ht => (hq' t ht k).symm),
      fun k => cadlag_congr (hD'.2.1 k) (fun t ht => (ha' t ht k).symm), hq0, ha0,
      fun t ht k => ?_⟩
    rw [hq' t ht k]; exact hD'.2.2.2.2 t ht k
  have hPhi : ∀ s, 0 ≤ s → ∀ j, Phi mu τ Ψ q a s j =
      Phi mu τ Ψ (qD u v lam mu ω d') (aD u lam ω d') s j := by
    intro s hs j
    have hΨeq := hΨ.2.2 q a (qD u v lam mu ω d') (aD u lam ω d') hD hD' s hs
      (fun k r hr => (hq' r hr.1 k).symm) (fun r hr => funext fun k => (ha' r hr.1 k).symm)
    have hτ0 := hτ.1 s hs j
    simp only [Phi]
    rw [hq' _ hτ0 j, ha' _ hτ0 j, ha' s hs j, hΨeq]
  have hd : ∀ i, 1 ≤ i → d' i = dS i := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      have e1 : (fun j => Function.leftLim (fun s => Phi mu τ Ψ q a s j) (arrivalEpoch u lam ω i)) =
          fun j => Function.leftLim (fun s => Phi mu τ Ψ (qD u v lam mu ω dS) (aD u lam ω dS) s j)
            (arrivalEpoch u lam ω i) := by
        funext j
        rw [← leftLim_Phi_congr τ Ψ hu hv hlam hmu hω hΨ hτ (d := d') hi
          (fun l h1 h2 => ih l h2 h1) j]
        exact leftLim_congr' (sigma_pos hu hlam hi)
          (phi_leftlim hτ hΨ hD (sigma_pos hu hlam hi) j) (fun s hs => hPhi s hs.1.le j)
      show route d0 _ = dS i
      rw [e1]
      exact dSeq_spec hu hv hlam hmu hω hτ hΨ d0 hi
  constructor
  · funext k
    rw [hq' t ht k]
    exact (qD_congr hu hlam hω ht (fun j h1 _ => hd j h1) k).1
  · funext k
    rw [ha' t ht k]
    exact (qD_congr (v := v) (mu := mu) hu hlam hω ht (fun j h1 _ => hd j h1) k).2

end main

end JSEQMWD

open JSEQMWD JSEQDelay.Diffusion in
theorem solution {K : ℕ} (hK : 2 ≤ K) {Ω : Type*}
    (u : ℕ → Ω → ℝ) (v : Fin K → ℕ → Ω → ℝ)
    (hu : ∀ i ω, 0 < u i ω) (hv : ∀ k i ω, 0 < v k i ω)
    (lam : ℝ) (mu : Fin K → ℝ) (hlam : 0 < lam) (hmu : ∀ k, 0 < mu k)
    (τ : ℝ → Fin K → ℝ) (hτ : DelayFunction τ)
    (Ψ : Path K → Path K → Path K) (hΨ : IsEstimator τ Ψ)
    (ω : Ω) (hω : GoodPath u v ω) :
    (∃ q a : Path K, IsJSEQPath u v lam mu τ Ψ ω q a) ∧
    ∀ q a q' a' : Path K, IsJSEQPath u v lam mu τ Ψ ω q a →
      IsJSEQPath u v lam mu τ Ψ ω q' a' → ∀ t, 0 ≤ t → q t = q' t ∧ a t = a' t := by
  set d0 : Fin K := ⟨0, by omega⟩
  refine ⟨⟨_, _, dSeq_path hu hv hlam hmu hω hτ hΨ d0⟩, fun q a q' a' h h' t ht => ?_⟩
  obtain ⟨e1, e2⟩ := sol_eq hu hv hlam hmu hω hτ hΨ d0 h ht
  obtain ⟨e3, e4⟩ := sol_eq hu hv hlam hmu hω hτ hΨ d0 h' ht
  exact ⟨e1.trans e3.symm, e2.trans e4.symm⟩
