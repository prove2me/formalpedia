-- Prove2me | solution 1 for JSEQDelay.Diffusion.proposition_A_2_osc
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T11:01:08.697662+00:00
-- url     : https://prove2.me/submissions/d1c3802c-d45c-4feb-ae58-e7fa5f4811f3

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_RankBasedSDI_LoadBalancing_Reflection
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



lemma osc_core {s t O : ℝ} (hs : 0 ≤ s)
    (hO : ∀ v ∈ Set.Icc s t, ∀ w ∈ Set.Icc s t, |x v - x w| ≤ O)
    {r u : ℝ} (hr : r ∈ Set.Icc s t) (hu : u ∈ Set.Icc s t) (hru : r ≤ u) :
    |skorokhodReg x u - skorokhodReg x r| ≤ O ∧
    |JSEQDelay.Diffusion.Gamma1 x u - JSEQDelay.Diffusion.Gamma1 x r| ≤ O := by
  have hr0 : 0 ≤ r := hs.trans hr.1
  have hmono := reg_mono x hx hr0 (hr0.trans hru) hru
  have hO0 : 0 ≤ O := (abs_nonneg _).trans (hO r hr r hr)
  have hsub : ∀ v ∈ Set.Icc r u, v ∈ Set.Icc s t := fun v hv => ⟨hr.1.trans hv.1, hv.2.trans hu.2⟩
  have hRr := neg_le_reg x hx (t := r) (r := r) ⟨hr0, le_rfl⟩
  have h1 := reg_le_of_near x hx (c := O) hr0 hru hO0 (fun v hv => by
    have := (abs_le.1 (hO r hr v (hsub v hv))).2
    linarith)
  have hxu := (abs_le.1 (hO u hu r hr))
  have h2 := reg_le_of_near x hx (c := O - (x u - x r)) hr0 hru (by linarith) (fun v hv => by
    have := (abs_le.1 (hO u hu v (hsub v hv))).2
    linarith)
  simp only [JSEQDelay.Diffusion.Gamma1]
  constructor
  · rw [abs_le]; constructor <;> linarith
  · rw [abs_le]; constructor <;> linarith

end JSEQA2Aux

open JSEQA2Aux in
theorem solution (x : ℝ → ℝ) (hx : IsCadlag x) (hx0 : 0 ≤ x 0)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s < t) :
    JSEQDelay.Diffusion.osc (JSEQDelay.Diffusion.Gamma1 x) s t ≤ JSEQDelay.Diffusion.osc x s t ∧
    JSEQDelay.Diffusion.osc (skorokhodReg x) s t ≤ JSEQDelay.Diffusion.osc x s t := by
  by_cases htop : JSEQDelay.Diffusion.osc x s t = ⊤
  · rw [htop]; exact ⟨le_top, le_top⟩
  set O := (JSEQDelay.Diffusion.osc x s t).toReal
  have hO : ∀ v ∈ Set.Icc s t, ∀ w ∈ Set.Icc s t, |x v - x w| ≤ O := by
    intro v hv w hw
    rw [← ENNReal.ofReal_le_iff_le_toReal htop]
    unfold JSEQDelay.Diffusion.osc
    exact le_iSup₂_of_le w v (le_iSup_of_le ⟨hw, hv⟩ le_rfl)
  have key : ∀ r u, r ∈ Set.Icc s t → u ∈ Set.Icc s t →
      |skorokhodReg x u - skorokhodReg x r| ≤ O ∧
      |JSEQDelay.Diffusion.Gamma1 x u - JSEQDelay.Diffusion.Gamma1 x r| ≤ O := by
    intro r u hr hu
    rcases le_total r u with h | h
    · exact osc_core x hx hs hO hr hu h
    · have := osc_core x hx hs hO hu hr h
      rw [abs_sub_comm (skorokhodReg x u), abs_sub_comm (JSEQDelay.Diffusion.Gamma1 x u)]
      exact this
  have hfin : ENNReal.ofReal O = JSEQDelay.Diffusion.osc x s t := ENNReal.ofReal_toReal htop
  constructor
  · unfold JSEQDelay.Diffusion.osc
    refine iSup₂_le fun r u => iSup_le fun h => ?_
    rw [← JSEQDelay.Diffusion.osc, ← hfin]
    exact ENNReal.ofReal_le_ofReal (key r u h.1 h.2).2
  · unfold JSEQDelay.Diffusion.osc
    refine iSup₂_le fun r u => iSup_le fun h => ?_
    rw [← JSEQDelay.Diffusion.osc, ← hfin]
    exact ENNReal.ofReal_le_ofReal (key r u h.1 h.2).1
