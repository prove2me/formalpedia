-- Prove2me | solution 1 for OAI.DirectionalTransience.OperationalConstants.stationary_window_entropy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:00:13.830174+00:00
-- url     : https://prove2.me/submissions/d196a7f8-dcd1-4336-88d2-58342d4ef090

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal005
import Definitions.Def_OAIQ242Bal006
import Theorems.Thm_OAI_DirectionalTransience_OperationalConstants_conditional_episode_drops
import Theorems.Thm_OAI_DirectionalTransience_actualOccupation_window_kl_le

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_EntropyVariational
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience.Entropy

variable {X : Type*} [MeasurableSpace X]

lemma ExpBudget.nonneg (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {C : ℝ} (h : ExpBudget μ ν C) : 0 ≤ C := by
  have hh := h (fun _ => 0) measurable_const ⟨0,fun _ => by simp⟩
  simpa using hh

lemma ExpBudget.absolutelyContinuous (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {C : ℝ} (h : ExpBudget μ ν C) : μ ≪ ν := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hνs
  by_contra hμs
  have hp : 0 < μ.real s := ENNReal.toReal_pos hμs (measure_ne_top _ _)
  let t : ℝ := (C+1) / μ.real s
  have ht : 0 < t := div_pos (by linarith [h.nonneg μ ν]) hp
  let F : X → ℝ := s.indicator (fun _ => t)
  have hF : Measurable F := measurable_const.indicator hs
  have hh := h F hF ⟨t,fun x => by
    by_cases hx : x ∈ s
    · simp [F,hx,abs_of_pos ht]
    · simp [F,hx,ht.le]⟩
  have he : (∫ x, Real.exp (F x) ∂ν) = 1 := by
    have heq : (fun x => Real.exp (F x)) =ᵐ[ν] fun _ => (1:ℝ) := by
      filter_upwards [show ∀ᵐ x ∂ν, x ∉ s from by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hνs] with x hx
      simp [F,hx]
    simpa using integral_congr_ae heq
  rw [he,show (∫ x, F x ∂μ) = μ.real s * t by
    exact integral_indicator_const t hs] at hh
  dsimp [t] at hh
  rw [mul_div_cancel₀ _ hp.ne'] at hh
  linarith

lemma ExpBudget.finite_kl (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {C : ℝ} (h : ExpBudget μ ν C) : klDiv μ ν ≠ ∞ := by
  have hac := h.absolutelyContinuous μ ν
  let g : X → ℝ := fun x => (μ.rnDeriv ν x).toReal
  have hg : Measurable g := (Measure.measurable_rnDeriv μ ν).ennreal_toReal
  have hg0 (x : X) : 0 ≤ g x := ENNReal.toReal_nonneg
  have hgi : Integrable g ν := by
    simpa only [mul_one] using
      (integrable_toReal_rnDeriv_mul_iff hac (f := fun _ => (1:ℝ))).mpr (integrable_const 1)
  have hg1 : (∫ x, g x ∂ν) = 1 := by
    simpa only [mul_one,integral_const,probReal_univ,one_smul] using
      (integral_toReal_rnDeriv_mul hac (f := fun _ => (1:ℝ)))
  let F : X → ℝ := fun x => Real.log (max 1 (g x))
  have hF : Measurable F := (measurable_const.max hg).log
  have hF0 (x : X) : 0 ≤ F x := Real.log_nonneg (le_max_left _ _)
  have hFi : Integrable F μ := by
    apply integrable_of_bounded_truncated_integrals μ F hF hF0 (C+1)
    intro n
    have hFn : Measurable (fun x => min (n:ℝ) (F x)) := measurable_const.min hF
    have hBn : ∃ B : ℝ, ∀ x, |min (n:ℝ) (F x)| ≤ B :=
      ⟨n,fun x => by
        rw [abs_of_nonneg (le_min (Nat.cast_nonneg _) (hF0 x))]
        exact min_le_left _ _⟩
    have he := h _ hFn hBn
    have he₂ : (∫ x, Real.exp (min (n:ℝ) (F x)) ∂ν) ≤ 2 := by
      have hp := integral_mono (exp_integrable_of_bounded hFn hBn)
        ((integrable_const 1).add hgi) (fun x => by
          calc Real.exp (min (n:ℝ) (F x)) ≤ Real.exp (F x) :=
              Real.exp_le_exp.mpr (min_le_right _ _)
            _ = max 1 (g x) := Real.exp_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
            _ ≤ 1+g x := max_le (by linarith [hg0 x]) (by linarith))
      simpa only [Pi.add_apply,integral_add (integrable_const 1) hgi,integral_const,
        probReal_univ,one_smul,hg1,one_add_one_eq_two] using hp
    linarith
  have hpos : Integrable (fun x => g x * F x) ν :=
    (integrable_toReal_rnDeriv_mul_iff hac).mpr hFi
  have hlog : Integrable (fun x => g x * Real.log (g x)) ν := by
    apply (hpos.add (integrable_const 1)).mono' (hg.mul hg.log).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      change |g x * Real.log (g x)| ≤ g x * F x + 1
      apply abs_le.mpr
      constructor
      · have hlow : -1 ≤ g x * Real.log (g x) := by
          by_cases hx : g x = 0
          · simp [hx]
          have hl := mul_le_mul_of_nonneg_left (Real.neg_inv_le_log (hg0 x)) (hg0 x)
          rw [mul_neg,mul_inv_cancel₀ hx] at hl
          exact hl
        have hn : 0 ≤ g x * F x := mul_nonneg (hg0 x) (hF0 x)
        linarith
      · by_cases hx : g x = 0
        · simp [hx]
        have hl := mul_le_mul_of_nonneg_left
          (Real.log_le_log (lt_of_le_of_ne (hg0 x) (Ne.symm hx)) (le_max_right 1 (g x))) (hg0 x)
        change g x * Real.log (g x) ≤ g x * F x at hl
        linarith
  exact klDiv_ne_top hac ((integrable_rnDeriv_mul_log_iff hac).mp hlog)

lemma abs_logClip_le (n : ℕ) (x : ℝ) : |logClip n x| ≤ (n:ℝ) := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _,max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (min_le_left _ _)⟩

lemma abs_logClip_le_abs (n : ℕ) (x : ℝ) : |logClip n x| ≤ |x| := by
  unfold logClip
  rcases le_total x (n:ℝ) with hx|hx
  · rw [min_eq_right hx]
    rcases le_total (-(n:ℝ)) x with hn|hn
    · rw [max_eq_right hn]
    · rw [max_eq_left hn,abs_neg,abs_of_nonneg (Nat.cast_nonneg n)]
      exact (by linarith : (n:ℝ) ≤ -x).trans (neg_le_abs _)
  · rw [min_eq_left hx,max_eq_right (by linarith [Nat.cast_nonneg (α := ℝ) n]),abs_of_nonneg (Nat.cast_nonneg n)]
    exact hx.trans (le_abs_self _)

lemma logClip_eventually (x : ℝ) : ∀ᶠ n : ℕ in atTop, logClip n x = x := by
  obtain ⟨N,hN⟩ := exists_nat_ge |x|
  filter_upwards [eventually_ge_atTop N] with n hn
  have h : |x| ≤ (n:ℝ) := hN.trans (Nat.cast_le.mpr hn)
  rw [logClip,min_eq_right ((le_abs_self _).trans h),max_eq_right]
  linarith [neg_le_abs x]

lemma exp_logClip_log_le {u : ℝ} (hu : 0 < u) (n : ℕ) :
    Real.exp (logClip n (Real.log u)) ≤ 1+u := by
  by_cases h : 0 ≤ Real.log u
  · calc Real.exp (logClip n (Real.log u)) ≤ Real.exp (Real.log u) := by
            apply Real.exp_le_exp.mpr
            exact max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (min_le_right _ _)
         _ = u := Real.exp_log hu
         _ ≤ _ := by linarith
  · calc Real.exp (logClip n (Real.log u)) ≤ Real.exp 0 := by
            apply Real.exp_le_exp.mpr
            exact max_le (neg_nonpos.mpr (Nat.cast_nonneg n))
              ((min_le_right _ _).trans (le_of_not_ge h))
         _ = 1 := Real.exp_zero
         _ ≤ _ := by linarith

theorem kl_le_of_expBudget (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {C : ℝ} (h : ExpBudget μ ν C) :
    klDiv μ ν ≤ ENNReal.ofReal C := by
  have hfinite := h.finite_kl μ ν
  obtain ⟨hac,hllr⟩ := klDiv_ne_top_iff.mp hfinite
  let g : X → ℝ := fun x => (μ.rnDeriv ν x).toReal
  have hg : Measurable g := (Measure.measurable_rnDeriv μ ν).ennreal_toReal
  have hg0 (x : X) : 0 ≤ g x := ENNReal.toReal_nonneg
  have hgp : ∀ᵐ x ∂μ, 0 < g x := by
    filter_upwards [Measure.rnDeriv_pos hac,hac.ae_le (Measure.rnDeriv_lt_top μ ν)] with x hx ht
    exact ENNReal.toReal_pos hx.ne' ht.ne
  have hgi : Integrable g ν := by
    simpa only [mul_one] using
      (integrable_toReal_rnDeriv_mul_iff hac (f := fun _ => (1:ℝ))).mpr (integrable_const 1)
  have hg1 : (∫ x, g x ∂ν) = 1 := by
    simpa only [mul_one,integral_const,probReal_univ,one_smul] using
      (integral_toReal_rnDeriv_mul hac (f := fun _ => (1:ℝ)))
  let F : ℕ → X → ℝ := fun n x =>
    if g x = 0 then -(n:ℝ) else logClip n (Real.log (g x))
  have hFm (n : ℕ) : Measurable (F n) := by
    exact measurable_const.ite (measurableSet_eq_fun hg measurable_const)
      (measurable_const.max (measurable_const.min hg.log))
  have hFb (n : ℕ) (x : X) : |F n x| ≤ (n:ℝ) := by
    dsimp only [F]
    split_ifs
    · rw [abs_neg,abs_of_nonneg (Nat.cast_nonneg n)]
    · exact abs_logClip_le n _
  have hFdom (n : ℕ) : ∀ᵐ x ∂μ, ‖F n x‖ ≤ ‖llr μ ν x‖ := by
    filter_upwards [hgp] with x hx
    simp only [F,ite_eq_right hx.ne',llr,Real.norm_eq_abs]
    exact abs_logClip_le_abs n _
  have hFpt : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (llr μ ν x)) := by
    filter_upwards [hgp] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [logClip_eventually (Real.log (g x))] with n hn
    simpa only [F,ite_eq_right hx.ne',llr] using hn.symm
  have hFlim : Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, llr μ ν x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => ‖llr μ ν x‖)
      (fun n => (hFm n).aestronglyMeasurable) hllr.norm hFdom hFpt
  have heDom (n : ℕ) (x : X) : ‖Real.exp (F n x)‖ ≤ 1+g x := by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    dsimp only [F]
    split_ifs with hx
    · have he : Real.exp (-(n:ℝ)) ≤ 1 := by
        rw [←Real.exp_zero]
        exact Real.exp_le_exp.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))
      linarith [hg0 x]
    · exact exp_logClip_log_le (lt_of_le_of_ne (hg0 x) (Ne.symm hx)) n
  have hePt (x : X) : Tendsto (fun n => Real.exp (F n x)) atTop (𝓝 (g x)) := by
    by_cases hx : g x = 0
    · simp only [F,hx,ite_eq_left]
      exact Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
    · apply tendsto_const_nhds.congr'
      filter_upwards [logClip_eventually (Real.log (g x))] with n hn
      simp only [F,ite_eq_right hx,hn,Real.exp_log (lt_of_le_of_ne (hg0 x) (Ne.symm hx))]
  have heLim : Tendsto (fun n => ∫ x, Real.exp (F n x) ∂ν) atTop (𝓝 1) := by
    rw [←hg1]
    exact tendsto_integral_of_dominated_convergence (fun x => 1+g x)
      (fun n => (hFm n).exp.aestronglyMeasurable) ((integrable_const 1).add hgi)
      (fun n => ae_of_all _ (heDom n)) (ae_of_all _ hePt)
  have hbound (n : ℕ) := h (F n) (hFm n) ⟨n,hFb n⟩
  have hlimit := (hFlim.sub heLim).add (tendsto_const_nhds (x := (1:ℝ)))
  have hh := le_of_tendsto hlimit (Eventually.of_forall hbound)
  have hh' : (klDiv μ ν).toReal ≤ C := by
    rw [toReal_klDiv_of_measure_eq hac (by simp)]
    linarith
  rw [←ENNReal.ofReal_toReal hfinite]
  exact ENNReal.ofReal_le_ofReal hh'

end DirectionalTransience.Entropy

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_BadCrossingLaw
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma klDiv_le_log_of_domination {X : Type*} [MeasurableSpace X]
    (Q P : Measure X) [IsProbabilityMeasure Q] [IsProbabilityMeasure P]
    (K : ℝ) (hK : 0<K) (hdom : Q ≤ ENNReal.ofReal K • P) :
    klDiv Q P ≤ ENNReal.ofReal (Real.log K) := by
  apply Entropy.kl_le_of_expBudget
  intro F hF hB
  have hFQ := Entropy.integrable_of_bounded (μ:=Q) hF hB
  have heP := Entropy.exp_integrable_of_bounded (μ:=P) hF hB
  have heQ := Entropy.exp_integrable_of_bounded (μ:=Q) hF hB
  let I := ∫ x, Real.exp (F x) ∂P
  have hI : 0<I := integral_exp_pos heP
  let C := Real.log (K*I)
  have hC : Real.exp C=K*I := Real.exp_log (mul_pos hK hI)
  have hedom : (∫ x, Real.exp (F x) ∂Q) ≤ K*I := by
    have hh := integral_mono_measure hdom (ae_of_all _ (fun x => (Real.exp_pos (F x)).le))
      (heP.smul_measure ENNReal.ofReal_ne_top)
    rw [integral_smul_measure,ENNReal.toReal_ofReal hK.le,smul_eq_mul] at hh
    exact hh
  have hes : Integrable (fun x => Real.exp (F x-C)) Q := by
    simpa only [Real.exp_sub] using heQ.div_const (Real.exp C)
  have hexp : (∫ x, Real.exp (F x-C) ∂Q) ≤ 1 := by
    simp only [Real.exp_sub,integral_div,C,Real.exp_log (mul_pos hK hI)]
    exact (div_le_one (mul_pos hK hI)).mpr hedom
  have hh := integral_mono ((hFQ.sub (integrable_const C)).add (integrable_const 1)) hes
    (fun x => Real.add_one_le_exp (F x-C))
  change (∫ x, F x-C+1 ∂Q) ≤ _ at hh
  rw [integral_add (f:=fun x => F x-C) (g:=fun _=> (1:ℝ)) (hFQ.sub (integrable_const C)) (integrable_const 1),
    integral_sub (f:=F) (g:=fun _=>C) hFQ (integrable_const C)] at hh
  simp only [integral_const,probReal_univ,one_smul] at hh
  have hlog : C=Real.log K+Real.log I := Real.log_mul hK.ne' hI.ne'
  have hl := Real.log_le_sub_one_of_pos hI
  dsimp only [I] at hl hlog
  linarith

lemma cond_klDiv_le {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (s : Set X) (hpos : P s≠0) :
    klDiv P[|s] P ≤ ENNReal.ofReal (-Real.log (P.real s)) := by
  have := cond_isProbabilityMeasure hpos
  have hreal : 0<P.real s := ENNReal.toReal_pos hpos (measure_ne_top _ _)
  have heq : (P s)⁻¹=ENNReal.ofReal ((P.real s)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hreal,Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hdom : P[|s] ≤ ENNReal.ofReal ((P.real s)⁻¹) • P := by
    rw [ProbabilityTheory.cond,←heq]
    exact _root_.smul_le_smul_left _ Measure.restrict_le_self
  simpa only [Real.log_inv] using klDiv_le_log_of_domination P[|s] P _ (inv_pos.mpr hreal) hdom

lemma badCrossingEvent_pos {d : ℕ} (e : Direction d) (N : ℕ) (β D : ℝ)
    (P : Measure (Environment d)) (hN : 0<N)
    (hmass : (N:ℝ)^(-D) ≤ P.real (badCrossingEvent e N β)) :
    P (badCrossingEvent e N β) ≠ 0 := by
  have hr : 0<P.real (badCrossingEvent e N β) :=
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _).trans_le hmass
  exact ENNReal.toReal_pos_iff.mp hr |>.1.ne'

lemma badCrossing_cond_entropy {d : ℕ} (e : Direction d) (N : ℕ) (β D : ℝ)
    (P : Measure (Environment d)) [IsProbabilityMeasure P] (hN : 0<N)
    (hmass : (N:ℝ)^(-D) ≤ P.real (badCrossingEvent e N β)) :
    klDiv P[|badCrossingEvent e N β] P ≤ ENNReal.ofReal (D*Real.log (N:ℝ)) := by
  have hp := badCrossingEvent_pos e N β D P hN hmass
  apply (cond_klDiv_le P _ hp).trans
  apply ENNReal.ofReal_le_ofReal
  have hl := Real.log_le_log (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) (-D)) hmass
  rw [Real.log_rpow (Nat.cast_pos.mpr hN)] at hl
  linarith

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayTopology
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace DirectionalTransience.StationaryCompact

variable {H R : Type*}
  [TopologicalSpace H] [DiscreteTopology H] [Countable H]
  [TopologicalSpace R] [CompactSpace R] [T2Space R] [SecondCountableTopology R]

omit [DiscreteTopology H] [Countable H] [CompactSpace R] [T2Space R]
  [SecondCountableTopology R] in
lemma shift_continuous : Continuous (shift : EpisodeArray H R → EpisodeArray H R) := by
  unfold shift
  fun_prop

end DirectionalTransience.StationaryCompact

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeInjection
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma episodeBoundary_progress {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
    (ω : Environment d) (i : ℕ) :
    min i N ≤ episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    rw [episodeBoundary]
    split
    · have hh := episodeFinal_gt (k:=k) e f hef r fexp g χ b sfloor hR N
        (episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i) ω
      omega
    · omega

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayMap
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

lemma globalHorizontalCoordinate_joint_measurable {d : ℕ} (e : Direction d) :
    Measurable (fun p : (Environment d×ℕ)×HorizontalSpace e =>
      globalHorizontalCoordinate e p.1.2 p.1.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro z
  apply Measurable.subtype_mk
  exact (((Measure.measurable_coe (measurableSet_singleton z)).comp
    (globalHorizontalProfile_joint_measurable e)).ennreal_toReal)

lemma episodeCost_measurable {d : ℕ} (e : Direction d) (t : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (i : ℤ) : Measurable (fun ω => episodeCost e t ω i) := by
  have hm : Measurable (fun p : Environment d×ℕ => crossingQuenched (realPosition (step e)) 0 p.2 p.1) := by
    apply measurable_from_prod_countable_left
    intro n
    change Measurable (crossingQuenched (realPosition (step e)) 0 (n : ℝ))
    exact measurable_crossingQuenched _ _ _
  exact (((hm.comp (measurable_id.prodMk (ht i))).ennreal_toReal.log).sub
    ((hm.comp (measurable_id.prodMk (ht (i+1)))).ennreal_toReal.log)).ennreal_ofReal

lemma episodeSplicedRow_measurable {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (i : ℤ) (m a l : ℕ) (z : HorizontalSpace e) :
    Measurable (fun X : EpisodeInput e => episodeSplicedRow e t X i m a l z) := by
  have hw : Measurable (fun X : EpisodeInput e => X.1.1) := measurable_fst.comp measurable_fst
  have hU : Measurable (fun X : EpisodeInput e => X.1.2 (i,a)) :=
    (measurable_pi_apply (i,a)).comp (measurable_snd.comp measurable_fst)
  have hx : Measurable (fun X : EpisodeInput e => horizontalLift e (t X.1.1 i+l) (X.1.2 (i,a)+z)) :=
    (measurable_of_countable (fun p : ℕ×HorizontalSpace e => horizontalLift e (p.1+l) (p.2+z))).comp
      (((ht i).comp hw).prodMk hU)
  unfold episodeSplicedRow
  apply Measurable.ite (measurableSet_lt measurable_const (((ht (i+m)).comp hw).sub ((ht i).comp hw)))
  · exact measurable_current_row.comp (hw.prodMk hx)
  · have hev : Measurable (fun p : (((ℕ×HorizontalSpace e) → Row d)×(ℕ×HorizontalSpace e)) => p.1 p.2) :=
      measurable_from_prod_countable_left (fun q => measurable_pi_apply q)
    exact hev.comp ((((measurable_pi_apply (i,m)).comp measurable_snd).prodMk
      (measurable_const.prodMk (hU.add_const z))))

lemma actualArrayCoordinate_measurable {d : ℕ} (e : Direction d)
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (j : ℤ) (p : ℤ×ℕ) (z : HorizontalSpace e) :
    Measurable (fun X : EpisodeInput e => globalHorizontalCoordinate e (t X.1.1 j) X.1.1 (X.1.2 p+z)) := by
  have hw : Measurable (fun X : EpisodeInput e => X.1.1) := measurable_fst.comp measurable_fst
  have hU : Measurable (fun X : EpisodeInput e => X.1.2 p) :=
    (measurable_pi_apply p).comp (measurable_snd.comp measurable_fst)
  have ha : Measurable (fun X : EpisodeInput e => ((X.1.1,t X.1.1 j),X.1.2 p+z)) :=
    (hw.prodMk ((ht j).comp hw)).prodMk (hU.add_const z)
  have hm := (globalHorizontalCoordinate_joint_measurable e).comp ha
  simpa only [Function.comp_def] using hm

lemma actualArrayMap_measurable {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (hJ : ∀ i, Measurable fun ω => J ω i) : Measurable (actualArrayMap e t J) := by
  have hw : Measurable (fun X : EpisodeInput e => X.1.1) := measurable_fst.comp measurable_fst
  have hU (p : ℤ×ℕ) : Measurable (fun X : EpisodeInput e => X.1.2 p) :=
    (measurable_pi_apply p).comp (measurable_snd.comp measurable_fst)
  refine Measurable.prodMk (Measurable.of_eval fun i => ?_)
    (Measurable.prodMk (Measurable.of_eval fun p => ?_)
      (Measurable.prodMk (Measurable.of_eval fun p => ?_) (Measurable.of_eval fun p => ?_)))
  · have hc : Measurable (fun n : ℕ => (n : ℕ∞)) := measurable_of_countable _
    exact (hc.comp (((ht (i+1)).comp hw).sub ((ht i).comp hw))).prodMk
      ((hc.comp ((hJ i).comp hw)).prodMk ((episodeCost_measurable e t ht i).comp hw))
  · exact OnePoint.continuous_coe.measurable.comp ((hU p.2).sub (hU p.1))
  · exact actualArrayCoordinate_measurable e t ht _ _ _
  · exact episodeSplicedRow_measurable e t ht _ _ _ _ _

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_StationaryCompact
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace BoundedContinuousFunction
open scoped ENNReal Topology
namespace DirectionalTransience.StationaryCompact

variable {X Y : Type*} [MeasurableSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]

lemma sum_indicator_range (N M : ℕ) (hM : M ≤ N) (G : ℕ → ℝ) :
    (∑ i ∈ Finset.range N, (if i < M then G i else 0)) = ∑ i ∈ Finset.range M, G i := by
  have he : (Finset.range N).filter (fun i => i < M) = Finset.range M := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [←Finset.sum_filter, he]

lemma episodeOccupationRaw_integral (N : ℕ) (μ : Measure X) [IsFiniteMeasure μ]
    (A : X → Y) (hA : Measurable A) (M : X → ℕ) (hM : Measurable M)
    (hMN : ∀ x, M x ≤ N) (T : Y → Y) (hT : Measurable T)
    (F : Y →ᵇ ℝ) :
    (∫ y, F y ∂episodeOccupationRaw N μ A M T) =
      ∫ x, ∑ i ∈ Finset.range (M x), F (T^[i] (A x)) ∂μ := by
  have hi (i : ℕ) : Integrable (fun x => F (T^[i] (A x))) μ := by
    apply (integrable_const ‖F‖).mono' ((F.continuous.measurable.comp
      ((hT.iterate i).comp hA)).aestronglyMeasurable)
    exact Eventually.of_forall fun x => F.norm_coe_le_norm _
  have hm (i : ℕ) : MeasurableSet {x | i < M x} := measurableSet_lt measurable_const hM
  rw [episodeOccupationRaw]
  rw [integral_finsetSum_measure (fun i _ =>
    BoundedContinuousFunction.integrable ((μ.restrict {x | i < M x}).map
      (fun x => T^[i] (A x))) F)]
  calc (∑ i ∈ Finset.range N, ∫ y, F y ∂(μ.restrict {x | i < M x}).map
        (fun x => T^[i] (A x)))
      = ∑ i ∈ Finset.range N, ∫ x,
          Set.indicator {x | i < M x} (fun x => F (T^[i] (A x))) x ∂μ := by
          apply Finset.sum_congr rfl
          intro i _
          rw [integral_indicator (hm i)]
          exact integral_map ((hT.iterate i).comp hA).aemeasurable
            F.continuous.aestronglyMeasurable
    _ = ∫ x, ∑ i ∈ Finset.range N,
          Set.indicator {x | i < M x} (fun x => F (T^[i] (A x))) x ∂μ :=
          (integral_finsetSum _ (fun i _ => (hi i).indicator (hm i))).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [Set.indicator_apply,Set.mem_ofPred_eq]
        exact sum_indicator_range N (M x) (hMN x) _

lemma episodeOccupationRaw_mass (N : ℕ) (μ : Measure X) [IsFiniteMeasure μ]
    (A : X → Y) (hA : Measurable A) (M : X → ℕ) (hM : Measurable M)
    (hMN : ∀ x, M x ≤ N) (T : Y → Y) (hT : Measurable T) :
    (episodeOccupationRaw N μ A M T).real Set.univ = ∫ x, (M x : ℝ) ∂μ := by
  simpa using episodeOccupationRaw_integral N μ A hA M hM hMN T hT
    (BoundedContinuousFunction.const Y (1:ℝ))

end DirectionalTransience.StationaryCompact

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeRecordedAtlas
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

namespace EpisodeRecordedAtlas
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
  {q : Environment d → EpisodeState (k:=k) e f r} {J F : Environment d → ℕ}

lemma count_event (A : EpisodeRecordedAtlas q J F) (m j h : ℕ) :
    MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) m)]
      {ω | (q ω).height=m ∧ J ω=j ∧ F ω=h} := by
  have := A.countable
  have he : {ω | (q ω).height=m ∧ J ω=j ∧ F ω=h} =
      ⋃ l : {l : A.Label // (A.chart l).height=m ∧ A.stages l=j ∧ A.failures l=h}, (A.chart l.val).event := by
    ext ω
    constructor
    · rintro ⟨hm,hj,hf⟩
      obtain ⟨l,hl⟩ := A.cover ω
      refine Set.mem_iUnion.mpr ⟨⟨l,?_,?_,?_⟩,hl⟩
      · rw [A.correct l ω hl] at hm
        exact hm
      · exact (A.stages_correct l ω hl).symm.trans hj
      · exact (A.failures_correct l ω hl).symm.trans hf
    · intro hh
      obtain ⟨l,hl⟩ := Set.mem_iUnion.mp hh
      change (q ω).height=m ∧ J ω=j ∧ F ω=h
      rw [A.correct l ω hl,A.stages_correct l ω hl,A.failures_correct l ω hl]
      exact l.property
  rw [he]
  apply MeasurableSet.iUnion
  intro l
  have hm := (A.chart l.val).measurable_event
  rwa [l.property.1] at hm

end EpisodeRecordedAtlas
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeCounterChain
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma episodeRun_stopped {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d) (hq : N ≤ q.height) (n : ℕ) :
    episodeRun e f hef r fexp g χ b sfloor N q ω n=q ∧
    episodeSteps e f hef r fexp g χ b sfloor N q ω n=0 ∧
    episodeCount e f hef r fexp g χ b sfloor N q ω (episodeStageFails e f r fexp g χ b N) n=0 := by
  have hnr : ¬EpisodeReady e f r sfloor N q := fun h => (Nat.not_lt_of_ge hq) h.1
  induction n with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ n ih =>
    simp only [episodeRun,episodeSteps,episodeCount,ih.1,ih.2.1,ih.2.2,hnr,ite_false, if_false,false_and,add_zero,and_self]

lemma episodeCounterChain_actual {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
    (ω : Environment d) (i : ℕ) :
    let T := episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    let p := episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    (T<N → p.state=episodeInitial e f hef r sfloor hR T ω) ∧
    (N≤T → N≤p.state.height) ∧
    p.stages=EpisodeChainLedger.steps (k:=k) e f hef r fexp g χ b sfloor hR N ω i ∧
    p.failures=EpisodeChainLedger.count (k:=k) e f hef r fexp g χ b sfloor hR N ω
      (episodeStageFails e f r fexp g χ b N) i := by
  dsimp only
  induction i with
  | zero => exact ⟨fun _ => rfl,fun h => h.trans (Nat.zero_le _),rfl,rfl⟩
  | succ i ih =>
    let T := episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    let p := episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    by_cases ht : T<N
    <;> dsimp only [T] at ht
    · have he := ih.1 ht
      simp only [episodeBoundary,episodeCounterChain,EpisodeChainLedger.steps,EpisodeChainLedger.count,he,ite_eq_left ht]
      refine ⟨fun _ => rfl,?_,?_,?_⟩
      · intro hh
        exact hh.trans (Nat.le_add_right _ 1)
      · rw [ih.2.2.1]
      · rw [ih.2.2.2]
    · have hp := ih.2.1 (Nat.le_of_not_lt ht)
      have hz := episodeRun_stopped e f hef r fexp g χ b sfloor N p.state ω hp N
      dsimp only [p] at hz
      simp only [episodeBoundary,episodeCounterChain,EpisodeChainLedger.steps,EpisodeChainLedger.count,ite_eq_right ht,
        hz.1,hz.2.1,hz.2.2,add_zero]
      refine ⟨fun h => False.elim (ht h),?_,ih.2.2.1,ih.2.2.2⟩
      intro _
      exact hp.trans (Nat.le_add_right _ 1)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace EpisodeRecordedAtlas
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
  {q : Environment d → EpisodeState (k:=k) e f r} {J F : Environment d → ℕ}

lemma measurable_counts (A : EpisodeRecordedAtlas q J F) : Measurable (fun ω => (J ω,F ω)) := by
  apply measurable_to_countable'
  intro z
  have he : (fun ω => (J ω,F ω)) ⁻¹' {z} =
      ⋃ m : ℕ, {ω | (q ω).height=m ∧ J ω=z.1 ∧ F ω=z.2} := by
    ext ω
    constructor
    · intro h
      have hh : J ω=z.1 ∧ F ω=z.2 := Prod.mk.inj h
      exact Set.mem_iUnion.mpr ⟨(q ω).height,rfl,hh⟩
    · intro h
      obtain ⟨m,hm,hj,hf⟩ := Set.mem_iUnion.mp h
      exact Prod.ext hj hf
  rw [he]
  exact MeasurableSet.iUnion fun m => (rowSigma_le _) _ (A.count_event m z.1 z.2)

end EpisodeRecordedAtlas

namespace EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "Fail" => episodeStageFails (k:=k) e f r fexp g χ b N
local notation "J" => fun ω i => steps (k:=k) e f hef r fexp g χ b sfloor hR N ω i
local notation "C" => fun ω i => count (k:=k) e f hef r fexp g χ b sfloor hR N ω Fail i

lemma measurable_counts (i : ℕ) : Measurable (fun ω => (J ω i,C ω i)) := by
  have he : (fun ω => ((episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i).stages,
      (episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i).failures)) =
      (fun ω => (J ω i,C ω i)) := by
    funext ω
    have hh := episodeCounterChain_actual (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    exact Prod.ext hh.2.2.1 hh.2.2.2
  rw [←he]
  exact (episodeCounterAtlas (k:=k) e f hef r fexp g χ b sfloor hR N i).measurable_counts

end EpisodeChainLedger
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeNumber
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma episodeBoundary_mono {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ) (ω : Environment d) :
    Monotone (episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [episodeBoundary]
  split
  · exact (episodeFinal_gt (k:=k) e f hef r fexp g χ b sfloor hR N _ ω).le
  · exact le_refl _

namespace EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "M" => number (k:=k) e f hef r fexp g χ b sfloor hR N

lemma number_le (ω : Environment d) (n : ℕ) : M ω n ≤ n := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => rw [number]; split <;> omega

lemma number_measurable (n : ℕ) : Measurable (fun ω => M ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact ih.add (Measurable.ite (measurableSet_lt
      (episodeBoundary_measurable (k:=k) e f hef r fexp g χ b sfloor hR N n) measurable_const)
      measurable_const measurable_const)

lemma number_integrable (Q : Measure (Environment d)) [IsFiniteMeasure Q] (n : ℕ) :
    Integrable (fun ω => (M ω n:ℝ)) Q := by
  apply Entropy.integrable_of_bounded ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp
    (number_measurable (k:=k) e f hef r fexp g χ b sfloor hR N n))
  refine ⟨n,fun ω => ?_⟩
  dsimp only [Function.comp_def]
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast number_le (k:=k) e f hef r fexp g χ b sfloor hR N ω n

end EpisodeChainLedger
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience.EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "T" => episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "M" => number (k:=k) e f hef r fexp g χ b sfloor hR N

lemma number_mono (ω : Environment d) : Monotone (M ω) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [number]
  exact Nat.le_add_right _ _

lemma number_active (ω : Environment d) (i : ℕ) (ha : T ω i<N) : M ω i=i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hprev : T ω i<N := lt_of_le_of_lt
      (episodeBoundary_mono (k:=k) e f hef r fexp g χ b sfloor hR N ω (Nat.le_succ i)) ha
    rw [number,ite_eq_left hprev,ih hprev]

lemma number_stopped (ω : Environment d) (i : ℕ) (hi : N ≤ T ω i) (j : ℕ) : M ω (i+j)=M ω i := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hn : ¬T ω (i+j)<N := not_lt.mpr (hi.trans
      (episodeBoundary_mono (k:=k) e f hef r fexp g χ b sfloor hR N ω (Nat.le_add_right _ _)))
    rw [Nat.add_succ,number,ite_eq_right hn,add_zero,ih]

lemma active_iff_lt_number (ω : Environment d) (i : ℕ) : T ω i<N ↔ i<M ω N := by
  constructor
  · intro ha
    have hi := episodeBoundary_progress (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    have hin : i<N := by omega
    have hm : M ω (i+1)=i+1 := by rw [number,ite_eq_left ha,number_active (k:=k) e f hef r fexp g χ b sfloor hR N ω i ha]
    have hh := number_mono (k:=k) e f hef r fexp g χ b sfloor hR N ω (Nat.succ_le_of_lt hin)
    change M ω (i+1) ≤ M ω N at hh
    rw [hm] at hh
    exact Nat.lt_of_succ_le hh
  · intro hm
    by_contra ha
    have hi : i<N := lt_of_lt_of_le hm (number_le (k:=k) e f hef r fexp g χ b sfloor hR N ω N)
    have hh := number_stopped (k:=k) e f hef r fexp g χ b sfloor hR N ω i (Nat.le_of_not_lt ha) (N-i)
    rw [Nat.add_sub_of_le hi.le] at hh
    have hu := number_le (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    omega

lemma number_positive (ω : Environment d) (hN : 0<N) : 0<M ω N :=
  (active_iff_lt_number (k:=k) e f hef r fexp g χ b sfloor hR N ω 0).mp hN

end DirectionalTransience.EpisodeChainLedger

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeDropLedger
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience.EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "J" => steps (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "j" => stepMark (k:=k) e f hef r fexp g χ b sfloor hR N

lemma stepMark_sub (ω : Environment d) (i : ℕ) : j ω i=J ω (i+1)-J ω i := by
  rw [steps,Nat.add_sub_cancel_left]
  rfl

lemma stepMark_measurable (i : ℕ) : Measurable (fun ω => j ω i) := by
  have hi := (measurable_counts (k:=k) e f hef r fexp g χ b sfloor hR N i).fst
  have hj := (measurable_counts (k:=k) e f hef r fexp g χ b sfloor hR N (i+1)).fst
  have h : Measurable (fun ω => J ω (i+1)-J ω i) := hj.sub hi
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  exact funext (fun ω => stepMark_sub (k:=k) e f hef r fexp g χ b sfloor hR N ω i)

end DirectionalTransience.EpisodeChainLedger

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience.EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)

lemma injection_cost_nonneg (κ : ℝ≥0) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
    0 ≤ ((BoundedInjection.injectionMultiplier (r sfloor)*k+1:ℕ)*(-Real.log κ)) := by
  have hlog : Real.log (κ:ℝ) ≤ 0 := Real.log_nonpos hκ0.le hκ1
  exact mul_nonneg (Nat.cast_nonneg _) (neg_nonneg.mpr hlog)

end DirectionalTransience.EpisodeChainLedger

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_BadCrossingEpisodes
attribute [-instance] _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} {e f : Direction d} {D : ℝ}

lemma cost_nonneg (C : OperationalConstants ν e f D) : 0 ≤ C.injectionCost :=
  EpisodeChainLedger.injection_cost_nonneg (k:=C.k) (episodeScaleRadius ν e f) C.sfloor C.κ C.hκ0 C.hκ1

lemma finite_charge (C : OperationalConstants ν e f D) :
    ∃ L : ℕ, 0<L ∧ C.injectionCost ≤ 2*C.b*L := by
  obtain ⟨L,hL⟩ := exists_nat_gt (max 1 (C.injectionCost/(2*C.b)))
  refine ⟨L,?_,?_⟩
  · have : (0:ℝ)<L := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hL)
    exact_mod_cast this
  · have := (div_le_iff₀ (show 0<2*C.b by nlinarith [C.hb])).mp
      ((le_max_right _ _).trans hL.le)
    nlinarith

end OperationalConstants
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma episodeInputLaw_environment {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i) :
    (episodeInputLaw e ν Q t ht).map (fun X => X.1.1)=Q := by
  change Measure.map (Prod.fst ∘ Prod.fst) _=Q
  rw [←Measure.map_map measurable_fst measurable_fst]
  unfold episodeInputLaw
  rw [Measure.map_fst_prod,measure_univ,one_smul]
  exact Measure.fst_compProd Q (globalEpisodeAnchors e t ht)

lemma episodeInputLaw_env_integral {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (F : Environment d → ℝ) (hF : Measurable F) :
    (∫ X, F X.1.1 ∂episodeInputLaw e ν Q t ht)=(∫ ω, F ω ∂Q) := by
  have hh := integral_map ((measurable_fst.comp measurable_fst).aemeasurable)
    hF.aestronglyMeasurable (μ:=episodeInputLaw e ν Q t ht)
  change (∫ y, F y ∂Measure.map (fun X => X.1.1) (episodeInputLaw e ν Q t ht)) = _ at hh
  rw [episodeInputLaw_environment] at hh
  exact hh.symm

namespace EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "T" => episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "M" => number (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "t" => arrayTime (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "s" => arrayStages (k:=k) e f hef r fexp g χ b sfloor hR N

lemma arrayStages_measurable (i : ℤ) : Measurable (fun ω => s ω i) := by
  unfold arrayStages
  split
  · exact measurable_const
  · exact stepMark_measurable (k:=k) e f hef r fexp g χ b sfloor hR N i.toNat

lemma arrayTime_nat (ω : Environment d) (i : ℕ) : t ω i=T ω i := by
  simp only [arrayTime,Int.toNat_natCast]

lemma operational_raw_mass (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : Measure (Environment d)) [IsFiniteMeasure Q] :
    (actualOccupationRaw e ν Q t s (arrayTime_measurable (k:=k) e f hef r fexp g χ b sfloor hR N) N (fun ω => M ω N)).real Set.univ=
      ∫ ω, (M ω N:ℝ) ∂Q := by
  unfold actualOccupationRaw
  have hM : Measurable (fun X : EpisodeInput e => M X.1.1 N) :=
    (number_measurable (k:=k) e f hef r fexp g χ b sfloor hR N N).comp (measurable_fst.comp measurable_fst)
  rw [StationaryCompact.episodeOccupationRaw_mass N _ _
    (actualArrayMap_measurable e t s (arrayTime_measurable (k:=k) e f hef r fexp g χ b sfloor hR N)
      (arrayStages_measurable (k:=k) e f hef r fexp g χ b sfloor hR N)) _
    hM
    (fun X => number_le (k:=k) e f hef r fexp g χ b sfloor hR N X.1.1 N) _ StationaryCompact.shift_continuous.measurable]
  exact episodeInputLaw_env_integral e ν Q t _ _
    ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (number_measurable (k:=k) e f hef r fexp g χ b sfloor hR N N))

lemma operational_mass_positive (Q : Measure (Environment d)) [IsProbabilityMeasure Q] (hN : 0<N) :
    0<∫ ω, (M ω N:ℝ) ∂Q := by
  have hh := integral_mono (integrable_const (1:ℝ))
    (number_integrable (k:=k) e f hef r fexp g χ b sfloor hR N Q N) (fun ω => by
      change (1:ℝ) ≤ (M ω N:ℝ)
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (number_positive (k:=k) e f hef r fexp g χ b sfloor hR N ω hN)))
  simp only [integral_const,probReal_univ,one_smul] at hh
  exact lt_of_lt_of_le zero_lt_one hh

end EpisodeChainLedger
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BadOccupationLimit
attribute [-instance] _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

omit [IsProbabilityMeasure ν] in
lemma paddedStages_measurable (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (i : ℤ) : Measurable (fun ω => C.paddedStages hef N ω i) :=
  EpisodeChainLedger.arrayStages_measurable (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N i

end OperationalConstants
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_EntropyContinuousTests
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory TopologicalSpace
open scoped ENNReal Classical Topology BoundedContinuousFunction
namespace DirectionalTransience.Entropy

lemma exp_sub_le_exp_mul {x y : ℝ} (h : x≤y) :
    Real.exp y-Real.exp x ≤ Real.exp y*(y-x) := by
  rcases h.eq_or_lt with rfl | _
  · simp
  · have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (x-y)) (Real.exp_pos y).le
    rw [← Real.exp_add,add_sub_cancel] at hh
    nlinarith

lemma abs_exp_sub_le {x y B : ℝ} (hx : x≤B) (hy : y≤B) :
    |Real.exp x-Real.exp y| ≤ Real.exp B*|x-y| := by
  rcases le_total x y with h|h
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr h)),
      abs_of_nonpos (sub_nonpos.mpr h),neg_sub,neg_sub]
    exact (exp_sub_le_exp_mul h).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hy) (sub_nonneg.mpr h))
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)),abs_of_nonneg (sub_nonneg.mpr h)]
    exact (exp_sub_le_exp_mul h).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hx) (sub_nonneg.mpr h))

lemma abs_sub_min_le {x y B : ℝ} (hx : x≤B) : |x-min y B| ≤ |x-y| := by
  by_cases hy : y≤B
  · simp [min_eq_left hy]
  · have hy : B≤y := le_of_not_ge hy
    rw [min_eq_right hy,abs_of_nonpos (sub_nonpos.mpr hx),
      abs_of_nonpos (sub_nonpos.mpr (hx.trans hy))]
    linarith

section Approximation
variable {X : Type*} [TopologicalSpace X] [MetrizableSpace X] [MeasurableSpace X] [BorelSpace X]

lemma continuous_exp_test_approx (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (F : X → ℝ) (hF : Measurable F)
    (hB : ∃ B : ℝ, ∀ x, |F x|≤B) {ε : ℝ} (hε : 0<ε) :
    ∃ g : X →ᵇ ℝ,
      |(∫ x, F x ∂μ)-(∫ x, g x ∂μ)| ≤ ε ∧
      |(∫ x, Real.exp (F x) ∂ν)-(∫ x, Real.exp (g x) ∂ν)| ≤ ε := by
  obtain ⟨B,hB⟩ := hB
  let δ := ε/(Real.exp B+1)
  have hδ : 0<δ := div_pos hε (by positivity)
  have hi : Integrable F (μ+ν) := integrable_of_bounded hF ⟨B,hB⟩
  obtain ⟨g,hg,hgi⟩ := hi.exists_boundedContinuous_integral_sub_le hδ
  let k : X →ᵇ ℝ := min g (BoundedContinuousFunction.const X B)
  have hk : ∀ x, k x≤B := fun x => min_le_right (g x) B
  have hkB : ∃ b : ℝ, ∀ x, |k x|≤b :=
    ⟨‖k‖,fun x => by simpa only [Real.norm_eq_abs] using k.norm_coe_le_norm x⟩
  have hμF : Integrable F μ := integrable_of_bounded hF ⟨B,hB⟩
  have hνF : Integrable F ν := integrable_of_bounded hF ⟨B,hB⟩
  have herr (x : X) : |F x-k x|≤|F x-g x| := abs_sub_min_le ((le_abs_self _).trans (hB x))
  have hgμ : (∫ x, |F x-g x| ∂μ)≤δ := by
    have h1 := integral_add_measure ((hμF.sub (g.integrable μ)).norm)
      ((hνF.sub (g.integrable ν)).norm)
    simp only [Real.norm_eq_abs, Pi.sub_apply] at h1 hg
    rw [h1] at hg
    have hn : 0 ≤ ∫ x, |F x-g x| ∂ν := integral_nonneg (fun x => abs_nonneg (F x-g x))
    linarith
  have hgν : (∫ x, |F x-g x| ∂ν)≤δ := by
    have h1 := integral_add_measure ((hμF.sub (g.integrable μ)).norm)
      ((hνF.sub (g.integrable ν)).norm)
    simp only [Real.norm_eq_abs, Pi.sub_apply] at h1 hg
    rw [h1] at hg
    have hn : 0 ≤ ∫ x, |F x-g x| ∂μ := integral_nonneg (fun x => abs_nonneg (F x-g x))
    linarith
  have hkμ : (∫ x, |F x-k x| ∂μ)≤δ :=
    (integral_mono (hμF.sub (k.integrable μ)).abs (hμF.sub (g.integrable μ)).abs herr).trans hgμ
  have hkν : (∫ x, |F x-k x| ∂ν)≤δ :=
    (integral_mono (hνF.sub (k.integrable ν)).abs (hνF.sub (g.integrable ν)).abs herr).trans hgν
  have hδle : δ≤ε := by
    apply (div_le_iff₀ (show 0<Real.exp B+1 by positivity)).mpr
    nlinarith [Real.exp_pos B]
  refine ⟨k,?_,?_⟩
  · rw [← integral_sub hμF (k.integrable μ)]
    exact (abs_integral_le_integral_abs).trans (hkμ.trans hδle)
  · have heF : Integrable (fun x => Real.exp (F x)) ν := exp_integrable_of_bounded hF ⟨B,hB⟩
    have hek : Integrable (fun x => Real.exp (k x)) ν := exp_integrable_of_bounded k.continuous.measurable hkB
    rw [← integral_sub heF hek]
    calc
      _ ≤ ∫ x, |Real.exp (F x)-Real.exp (k x)| ∂ν := abs_integral_le_integral_abs
      _ ≤ ∫ x, Real.exp B*|F x-k x| ∂ν := integral_mono (heF.sub hek).abs
        (((hνF.sub (k.integrable ν)).abs).const_mul _) (fun x =>
          abs_exp_sub_le ((le_abs_self _).trans (hB x)) (hk x))
      _ = Real.exp B*(∫ x, |F x-k x| ∂ν) := integral_const_mul _ _
      _ ≤ Real.exp B*δ := mul_le_mul_of_nonneg_left hkν (Real.exp_pos B).le
      _ ≤ ε := by
        dsimp only [δ]
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (show 0<Real.exp B+1 by positivity)).mpr
        nlinarith

theorem expBudget_of_continuous (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {C : ℝ}
    (h : ∀ g : X →ᵇ ℝ, (∫ x, g x ∂μ)-(∫ x, Real.exp (g x) ∂ν)+1≤C) :
    ExpBudget μ ν C := by
  intro F hF hB
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨g,hg,hge⟩ := continuous_exp_test_approx μ ν F hF hB (half_pos hε)
  have h1 := (abs_le.mp hg).2
  have h2 := (abs_le.mp hge).1
  have h3 := h g
  linarith

end Approximation
end DirectionalTransience.Entropy

end

section

open MeasureTheory ProbabilityTheory InformationTheory TopologicalSpace Filter
open scoped ENNReal Topology BoundedContinuousFunction
namespace DirectionalTransience.Entropy

variable {X I : Type*} [TopologicalSpace X] [CompactSpace X] [MetrizableSpace X]
  [MeasurableSpace X] [BorelSpace X]

lemma kl_le_of_weak_limit {l : Filter I} [l.NeBot]
    (μs νs : I → ProbabilityMeasure X) (μ ν : ProbabilityMeasure X)
    (hμ : Tendsto μs l (𝓝 μ)) (hν : Tendsto νs l (𝓝 ν))
    {C : ℝ} (hC : 0≤C)
    (hbudget : ∀ᶠ i in l, klDiv (μs i : Measure X) (νs i : Measure X) ≤ ENNReal.ofReal C) :
    klDiv (μ : Measure X) (ν : Measure X) ≤ ENNReal.ofReal C := by
  apply kl_le_of_expBudget
  apply expBudget_of_continuous
  intro f
  let ef : X →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨fun x => Real.exp (f x), Real.continuous_exp.comp f.continuous⟩
  have h1 := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ f
  have h2 := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν ef
  apply le_of_tendsto ((h1.sub h2).add_const 1)
  filter_upwards [hbudget] with i hi
  exact expBudget_of_kl_le (μs i : Measure X) (νs i : Measure X) hC hi
    f f.continuous.measurable ⟨‖f‖,fun x => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x⟩

end DirectionalTransience.Entropy

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ReferenceContinuity
attribute [-instance] _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace DirectionalTransience.ReferenceClasses

section Reindex
variable {I J K R : Type*} [MeasurableSpace R]

lemma map_iid_eq_of_same_fibers (ν : Measure R) [IsProbabilityMeasure ν]
    (f : I → J) (g : I → K) (h : ∀ i i', f i = f i' ↔ g i = g i') :
    (Measure.infinitePi (fun _ : J => ν)).map (fun ξ i => ξ (f i)) =
      (Measure.infinitePi (fun _ : K => ν)).map (fun ξ i => ξ (g i)) := by
  classical
  let t : Set.range f → K := fun x => g (Classical.choose x.2)
  have ht (i : I) : t ⟨f i,Set.mem_range_self i⟩ = g i :=
    (h _ _).mp (Classical.choose_spec (Set.mem_range_self i))
  have htinj : Function.Injective t := by
    intro x y hxy
    apply Subtype.ext
    have hfg := (h (Classical.choose x.2) (Classical.choose y.2)).mpr hxy
    rw [Classical.choose_spec x.2,Classical.choose_spec y.2] at hfg
    exact hfg
  have h1 := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : J => ν)
    (f := (Subtype.val : Set.range f → J)) Subtype.val_injective
  have h2 := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : K => ν) htinj
  have hm : Measurable (fun ξ : Set.range f → R => fun i => ξ ⟨f i,Set.mem_range_self i⟩) := by
    fun_prop
  have hh := congrArg (fun μ : Measure (Set.range f → R) =>
    μ.map (fun ξ i => ξ ⟨f i,Set.mem_range_self i⟩)) (h1.trans h2.symm)
  rw [Measure.map_map hm (by fun_prop),Measure.map_map hm (by fun_prop)] at hh
  simpa only [Function.comp_def,ht] using hh

end Reindex

section FiniteCoordinates
variable {H R : Type*} [AddCommGroup H] [Countable H]
  [TopologicalSpace H] [DiscreteTopology H] [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (OnePoint H)] [BorelSpace (OnePoint H)] [MeasurableSpace R]

lemma reference_projection_eq {I : Type*} (ν : Measure R) [IsProbabilityMeasure ν]
    (O O' : Data H) (p : I → Site H)
    (h : ∀ i j, inputSite O (p i) = inputSite O (p j) ↔
      inputSite O' (p i) = inputSite O' (p j)) :
    (reference ν O).map (fun φ i => φ (p i)) =
      (reference ν O').map (fun φ i => φ (p i)) := by
  have hm (D : Data H) : Measurable (fields D : AllFields H R → _) :=
    Measurable.of_eval fun _ => measurable_pi_apply _
  rw [reference_apply,reference_apply,Measure.map_map (by fun_prop) (hm O),
    Measure.map_map (by fun_prop) (hm O')]
  exact map_iid_eq_of_same_fibers ν (inputSite O ∘ p) (inputSite O' ∘ p) h

omit [Countable H] [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (OnePoint H)] [BorelSpace (OnePoint H)] in
lemma inputSite_collision_clopen (p q : Site H) :
    IsClopen {O : Data H | inputSite O p = inputSite O q} := by
  rcases p with ⟨a,l,z⟩
  rcases q with ⟨b,l',z'⟩
  simp only [inputSite_eq_iff]
  by_cases h : l = l'
  · simp only [h,true_and]
    exact (offset_clopen a b (z-z')).preimage continuous_subtype_val
  · simp only [h,false_and,Set.ofPred_false]
    exact isClopen_empty

lemma reference_projection_locally_constant {I : Type*} [Finite I]
    (ν : Measure R) [IsProbabilityMeasure ν] (O : Data H) (p : I → Site H) :
    ∀ᶠ O' in 𝓝 O, (reference ν O').map (fun φ i => φ (p i)) =
      (reference ν O).map (fun φ i => φ (p i)) := by
  have hh : ∀ᶠ O' in 𝓝 O, ∀ i j,
      inputSite O' (p i) = inputSite O' (p j) ↔ inputSite O (p i) = inputSite O (p j) := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    have hc := inputSite_collision_clopen (p i) (p j)
    by_cases h : inputSite O (p i) = inputSite O (p j)
    · filter_upwards [hc.2.mem_nhds h] with O' h'
      exact iff_of_true h' h
    · filter_upwards [hc.1.isOpen_compl.mem_nhds h] with O' h'
      exact iff_of_false h' h
  filter_upwards [hh] with O' h'
  exact reference_projection_eq ν O' O p h'

end FiniteCoordinates
end DirectionalTransience.ReferenceClasses

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayClosed
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma closed_support_weak_limit {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [HasOuterApproxClosed X]
    (μ : ℕ → ProbabilityMeasure X) (ρ : ProbabilityMeasure X)
    (hlim : Tendsto μ atTop (𝓝 ρ)) (s : Set X) (hs : IsClosed s)
    (hμ : ∀ n, ∀ᵐ x ∂(μ n : Measure X), x∈s) :
    ∀ᵐ x ∂(ρ : Measure X), x∈s := by
  have he (n : ℕ) : (μ n : Measure X) s=1 :=
    (mem_ae_iff_prob_eq_one hs.measurableSet).mp (hμ n)
  have hle := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim hs
  simp only [he,limsup_const] at hle
  exact (mem_ae_iff_prob_eq_one hs.measurableSet).mpr
    (le_antisymm prob_le_one hle)

lemma actualOccupation_ae_of_invariant {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (hJ : ∀ i, Measurable fun ω => J ω i) (N : ℕ) (M : Environment d → ℕ)
    (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ)
    (s : Set (ActualEpisodeArray e)) (hs : MeasurableSet s)
    (ha : ∀ X, actualArrayMap e t J X∈s)
    (hshift : ∀ Y∈s, StationaryCompact.shift Y∈s) :
    ∀ᵐ Y ∂(actualOccupation e ν Q t J ht N M : Measure (ActualEpisodeArray e)), Y∈s := by
  have hiter (i : ℕ) (X : EpisodeInput e) :
      StationaryCompact.shift^[i] (actualArrayMap e t J X)∈s := by
    induction i with
    | zero => exact ha X
    | succ i hi =>
      rw [Function.iterate_succ_apply']
      exact hshift _ hi
  have hraw : ∀ᵐ Y ∂actualOccupationRaw e ν Q t J ht N M, Y∈s := by
    unfold actualOccupationRaw StationaryCompact.episodeOccupationRaw
    rw [ae_finsetSum_measure_iff]
    intro i _
    apply (ae_map_iff ((StationaryCompact.shift_continuous.measurable.iterate i).comp
      (actualArrayMap_measurable e t J ht hJ)).aemeasurable hs).mpr
    exact Filter.Eventually.of_forall (hiter i)
  have : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
  let ρ : FiniteMeasure (ActualEpisodeArray e) := ⟨actualOccupationRaw e ν Q t J ht N M,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  have hn : ρ≠0 := by
    intro hz
    have hh : (actualOccupationRaw e ν Q t J ht N M).real Set.univ=0 := by
      change (ρ : Measure (ActualEpisodeArray e)).real Set.univ=0
      rw [hz]
      simp
    linarith
  change ∀ᵐ Y ∂(ρ.normalize : Measure (ActualEpisodeArray e)), Y∈s
  rw [ρ.toMeasure_normalize_eq_of_nonzero hn]
  exact Measure.ae_smul_measure hraw _

lemma currentOffsets_closed {d : ℕ} (e : Direction d) :
    IsClosed {Y : ActualEpisodeArray e | ∀ j, ReferenceClasses.Consistent (currentOffsets e j Y)} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun j => ReferenceClasses.consistent_closed.preimage
    (currentOffsets_continuous e j)

lemma actual_currentOffsets {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (X : EpisodeInput e) (j : ℤ) :
    ReferenceClasses.Consistent (currentOffsets e j (actualArrayMap e t J X)) := by
  constructor
  · intro a
    simp [currentOffsets,actualArrayMap]
  · intro a b z h
    have he : X.1.2 (j,b)-X.1.2 (j,a)=z := OnePoint.coe_injective h
    change ((X.1.2 (j,a)-X.1.2 (j,b) : HorizontalSpace e):OnePoint (HorizontalSpace e))=((-z : HorizontalSpace e):OnePoint (HorizontalSpace e))
    rw [←he,neg_sub]
  · intro a b c z w h₁ h₂
    have h₁ : X.1.2 (j,b)-X.1.2 (j,a)=z := OnePoint.coe_injective h₁
    have h₂ : X.1.2 (j,c)-X.1.2 (j,b)=w := OnePoint.coe_injective h₂
    change ((X.1.2 (j,c)-X.1.2 (j,a) : HorizontalSpace e):OnePoint (HorizontalSpace e))=((z+w : HorizontalSpace e):OnePoint (HorizontalSpace e))
    rw [←h₁,←h₂]
    congr 1
    abel

lemma actualOccupation_currentOffsets {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (hJ : ∀ i, Measurable fun ω => J ω i) (N : ℕ) (M : Environment d → ℕ)
    (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ) :
    ∀ᵐ Y ∂(actualOccupation e ν Q t J ht N M : Measure (ActualEpisodeArray e)),
      ∀ j, ReferenceClasses.Consistent (currentOffsets e j Y) := by
  apply actualOccupation_ae_of_invariant e ν Q t J ht hJ N M hpos _
    (currentOffsets_closed e).measurableSet (actual_currentOffsets e t J)
  intro Y hY j
  exact hY (j+1)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal Classical
namespace DirectionalTransience

lemma currentWindowInclude_injective {d : ℕ} (e : Direction d) :
    Function.Injective (currentWindowInclude e) := by
  intro W W' h
  have h1 : W.1.1.1=W'.1.1.1 := congrArg (fun p => p.1.1) h
  have h2 : W.1.2=W'.1.2 := congrArg (fun p => p.1.2) h
  have h3 : W.2=W'.2 := congrArg (fun p => p.2) h
  exact Prod.ext (Prod.ext (Subtype.ext h1) h2) h3

lemma currentWindowInclude_typed {d : ℕ} (e : Direction d) (j : ℤ) (m : ℕ)
    (Y : ActualEpisodeArray e) (h : ReferenceClasses.Consistent (currentOffsets e j Y)) :
    currentWindowInclude e (typedCurrentArrayWindow e j m Y) = currentArrayWindow e j m Y := by
  simp only [typedCurrentArrayWindow,dite_eq_left h,currentWindowInclude,currentArrayWindow]

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ClosedEmbeddingWeak
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory TopologicalSpace Filter
open scoped Topology BoundedContinuousFunction
namespace DirectionalTransience.Entropy

lemma tendsto_of_map_closedEmbedding {X Y I : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [NormalSpace Y]
    (e : X → Y) (he : Topology.IsClosedEmbedding e)
    {l : Filter I} {μs : I → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (h : Tendsto (fun index => (μs index).map (f := e) he.continuous.aemeasurable) l
      (𝓝 (μ.map (f := e) he.continuous.aemeasurable))) : Tendsto μs l (𝓝 μ) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  obtain ⟨g,_,hg⟩ := f.exists_extension_norm_eq_of_isClosedEmbedding he
  have ht := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h g
  have hi (ρ : ProbabilityMeasure X) :
      (∫ y, g y ∂(ρ.map (f := e) he.continuous.aemeasurable : Measure Y))=
        ∫ x, f x ∂(ρ : Measure X) := by
    rw [ProbabilityMeasure.toMeasure_map,integral_map he.continuous.measurable.aemeasurable
      g.continuous.measurable.aestronglyMeasurable]
    exact congrArg (fun k : X → ℝ => ∫ x, k x ∂(ρ : Measure X)) hg
  simpa only [hi] using ht

end DirectionalTransience.Entropy

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_FiniteCoordinateApproximation
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Filter UniformSpace
open scoped Uniformity Topology
namespace DirectionalTransience.Entropy

lemma finite_coordinates_of_entourage {I R : Type*} [UniformSpace R]
    {V : Set ((I → R) × (I → R))} (hV : V ∈ 𝓤 (I → R)) :
    ∃ S : Finset I, ∀ x y : I → R, (∀ i ∈ S, x i=y i) → (x,y)∈V := by
  classical
  rw [Pi.uniformity] at hV
  refine Filter.iInf_sets_induct hV ?_ ?_
  · exact ⟨∅,fun _ _ _ => Set.mem_univ _⟩
  · intro i V W hV hW
    obtain ⟨S,hS⟩ := hW
    obtain ⟨U,hU,hUV⟩ := Filter.mem_comap.mp hV
    refine ⟨insert i S,fun x y hxy => ⟨?_,hS x y (fun j hj => hxy j (Finset.mem_insert_of_mem hj))⟩⟩
    apply hUV
    change (x i,y i)∈U
    rw [hxy i (Finset.mem_insert_self _ _)]
    exact refl_mem_uniformity hU

lemma finite_coordinates_of_uniformContinuous {I R : Type*} [UniformSpace R]
    (f : (I → R) → ℝ) (hf : UniformContinuous f) {ε : ℝ} (hε : 0<ε) :
    ∃ S : Finset I, ∀ x y : I → R, (∀ i ∈ S, x i=y i) → |f x-f y|<ε := by
  have h := hf (Metric.dist_mem_uniformity hε)
  obtain ⟨S,hS⟩ := finite_coordinates_of_entourage h
  exact ⟨S,fun x y hxy => by simpa only [Set.mem_preimage,Set.mem_ofPred_eq,Real.dist_eq] using hS x y hxy⟩

lemma finiteFiller_continuous {I R : Type*} [TopologicalSpace R] (r : I → R) (S : Finset I) :
    Continuous (finiteFiller r S) := by
  classical
  apply continuous_pi
  intro i
  by_cases hi : i∈S
  · simpa only [finiteFiller, dite_eq_left hi] using (continuous_apply (⟨i,hi⟩ : S) : Continuous (fun x : S → R => x ⟨i,hi⟩))
  · simp only [finiteFiller, dite_eq_right hi]
    exact continuous_const

lemma finiteFiller_approx {I R : Type*} [UniformSpace R] [CompactSpace R]
    (f : C((I → R),ℝ)) (r : I → R) {ε : ℝ} (hε : 0<ε) :
    ∃ S : Finset I, ∀ x, |f x-f (finiteFiller r S (fun i => x i))|<ε := by
  obtain ⟨S,hS⟩ := finite_coordinates_of_uniformContinuous f (CompactSpace.uniformContinuous_of_continuous f.continuous) hε
  refine ⟨S,fun x => hS x _ ?_⟩
  intro i hi
  simp [finiteFiller,hi]

end DirectionalTransience.Entropy

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ReferenceFeller
attribute [-instance] _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped ENNReal Topology BoundedContinuousFunction
namespace DirectionalTransience.ReferenceClasses

variable {H R : Type*} [AddCommGroup H] [Countable H]
  [TopologicalSpace H] [DiscreteTopology H] [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (OnePoint H)] [BorelSpace (OnePoint H)]
  [UniformSpace R] [CompactSpace R] [SecondCountableTopology R]
  [MeasurableSpace R] [BorelSpace R]

lemma integral_uniform_error {Y : Type*} [TopologicalSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] (f g : Y →ᵇ ℝ)
    {ε : ℝ} (h : ∀ x, |f x-g x|≤ε) :
    |(∫ x, f x ∂μ)-(∫ x, g x ∂μ)|≤ε := by
  rw [← integral_sub (f.integrable μ) (g.integrable μ)]
  calc
    _ ≤ ∫ x, |f x-g x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _ : Y, ε ∂μ := integral_mono ((f.integrable μ).sub (g.integrable μ)).abs
      (integrable_const ε) h
    _ = ε := by simp

lemma reference_integral_continuous (ν : Measure R) [IsProbabilityMeasure ν]
    (f : (AllFields H R) →ᵇ ℝ) :
    Continuous (fun O : Data H => ∫ φ, f φ ∂reference ν O) := by
  have : Nonempty R := nonempty_of_isProbabilityMeasure ν
  let r : AllFields H R := fun _ => Classical.choice ‹Nonempty R›
  apply continuous_iff_continuousAt.mpr
  intro O
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨S,hS⟩ := Entropy.finiteFiller_approx f.toContinuousMap r (div_pos hε (show (0:ℝ)<3 by norm_num))
  let gf : C((S → R),ℝ) := ⟨fun x => f (Entropy.finiteFiller r S x),
    f.continuous.comp (Entropy.finiteFiller_continuous r S)⟩
  let g : (AllFields H R) →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun φ => gf (fun i : S => φ i),gf.continuous.comp (continuous_pi fun i => continuous_apply (i : Site H))⟩
  have heq : ∀ᶠ O' in 𝓝 O, (∫ φ, g φ ∂reference ν O')=(∫ φ, g φ ∂reference ν O) := by
    filter_upwards [reference_projection_locally_constant ν O (fun i : S => (i : Site H))] with O' hO'
    have hm : Measurable (fun φ : AllFields H R => fun i : S => φ i) := by fun_prop
    have hi (D : Data H) := integral_map hm.aemeasurable gf.continuous.measurable.aestronglyMeasurable
      (μ:=reference ν D)
    exact (hi O').symm.trans ((congrArg (fun μ => ∫ x, gf x ∂μ) hO').trans (hi O))
  have herr (D : Data H) : |(∫ φ, f φ ∂reference ν D)-(∫ φ, g φ ∂reference ν D)|≤ε/3 :=
    integral_uniform_error _ f g (fun φ => (hS φ).le)
  filter_upwards [heq] with O' hO'
  rw [Real.dist_eq]
  have h1 := herr O'
  have h2 := herr O
  rw [hO'] at h1
  have hh := abs_sub_le (∫ φ, f φ ∂reference ν O') (∫ φ, g φ ∂reference ν O) (∫ φ, f φ ∂reference ν O)
  rw [abs_sub_comm (∫ φ, g φ ∂reference ν O)] at hh
  linarith

theorem referenceProb_continuous (ν : Measure R) [IsProbabilityMeasure ν] :
    Continuous (referenceProb (H:=H) ν) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  exact reference_integral_continuous ν

end DirectionalTransience.ReferenceClasses

end

section

open MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped ENNReal Topology BoundedContinuousFunction
namespace DirectionalTransience.Entropy

variable {X Y I : Type*} [TopologicalSpace X]
  [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

lemma continuous_joint_integral [MeasurableSpace X] [BorelSpace X]
    (P : X → ProbabilityMeasure Y) (hP : Continuous P)
    (F : C(X × Y,ℝ)) : Continuous (fun x => ∫ y, F (x,y) ∂(P x : Measure Y)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hε2 : 0<ε/2 := half_pos hε
  have h1 : ∀ᶠ x' in 𝓝 x, ‖F.curry x'-F.curry x‖<ε/2 := by
    have hc : ContinuousAt (fun x' => ‖F.curry x'-F.curry x‖) x :=
      (F.curry.continuous.sub continuous_const).norm.continuousAt
    exact hc.eventually_lt continuousAt_const (by simpa using hε2)
  let g : Y →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact (F.curry x)
  have hg := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction g).comp hP
  have h2 : ∀ᶠ x' in 𝓝 x, dist (∫ y, g y ∂(P x' : Measure Y))
      (∫ y, g y ∂(P x : Measure Y)) < ε/2 :=
    (Metric.tendsto_nhds.mp hg.continuousAt) (ε/2) hε2
  filter_upwards [h1,h2] with x' hx' hx''
  have hint : |(∫ y, F (x',y) ∂(P x' : Measure Y))-(∫ y, F (x,y) ∂(P x' : Measure Y))| ≤
      ‖F.curry x'-F.curry x‖ := by
    exact ReferenceClasses.integral_uniform_error _
      (BoundedContinuousFunction.mkOfCompact (F.curry x')) g
      (fun y => by
        change |(F.curry x'-F.curry x) y| ≤ _
        simpa only [Real.norm_eq_abs] using (F.curry x'-F.curry x).norm_coe_le_norm y)
  rw [Real.dist_eq] at hx'' ⊢
  have hh := abs_sub_le (∫ y, F (x',y) ∂(P x' : Measure Y))
    (∫ y, F (x,y) ∂(P x' : Measure Y)) (∫ y, F (x,y) ∂(P x : Measure Y))
  change |(∫ y, F (x,y) ∂(P x' : Measure Y))-(∫ y, F (x,y) ∂(P x : Measure Y))|<ε/2 at hx''
  linarith

variable [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [SecondCountableTopology X] [SecondCountableTopology Y]

lemma compProdProb_tendsto (K : Kernel X Y) [IsMarkovKernel K]
    (hK : Continuous (kernelProb K))
    {l : Filter I} {μs : I → ProbabilityMeasure X} {μ : ProbabilityMeasure X}
    (hμ : Tendsto μs l (𝓝 μ)) : Tendsto (fun i => compProdProb (μs i) K) l (𝓝 (compProdProb μ K)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  let g : X →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => ∫ y, f (x,y) ∂K x,continuous_joint_integral _ hK f.toContinuousMap⟩
  have heq (ρ : ProbabilityMeasure X) :
      (∫ p, f p ∂(compProdProb ρ K : Measure (X×Y)))=(∫ x, g x ∂(ρ : Measure X)) := by
    exact integral_compProd (f.integrable ((ρ : Measure X).compProd K))
  simp_rw [heq]
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ g

end DirectionalTransience.Entropy

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Geometry_WindowWeak
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory TopologicalSpace Filter
open scoped ENNReal Classical Topology
namespace DirectionalTransience

lemma actualCurrentLaw_include {d : ℕ} (e : Direction d) (m : ℕ)
    (L : ProbabilityMeasure (ActualEpisodeArray e))
    (hc : ∀ᵐ Y ∂(L : Measure (ActualEpisodeArray e)), ReferenceClasses.Consistent (currentOffsets e 0 Y)) :
    (actualCurrentLaw e m L).map (f := currentWindowInclude e) (currentWindowInclude_continuous e).aemeasurable =
      L.map (f := (currentArrayWindow e 0 m)) (by first | (apply Continuous.aemeasurable; apply currentArrayWindow_continuous <;> assumption) | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability) := by
  apply Subtype.ext
  change ((L : Measure _).map (typedCurrentArrayWindow e 0 m)).map (currentWindowInclude e) = _
  rw [Measure.map_map (currentWindowInclude_continuous e).measurable (typedCurrentArrayWindow_measurable e 0 m)]
  apply Measure.map_congr
  filter_upwards [hc] with Y hY
  exact currentWindowInclude_typed e 0 m Y hY

lemma actualCurrentLaw_tendsto {d : ℕ} (e : Direction d) (m : ℕ)
    (Ls : ℕ → ProbabilityMeasure (ActualEpisodeArray e)) (L : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto Ls atTop (𝓝 L))
    (hc : ∀ n, ∀ᵐ Y ∂(Ls n : Measure (ActualEpisodeArray e)), ∀ j, ReferenceClasses.Consistent (currentOffsets e j Y)) :
    Tendsto (fun n => actualCurrentLaw e m (Ls n)) atTop (𝓝 (actualCurrentLaw e m L)) := by
  have hL := closed_support_weak_limit Ls L hlim _ (currentOffsets_closed e) hc
  apply Entropy.tendsto_of_map_closedEmbedding (currentWindowInclude e)
    ((currentWindowInclude_continuous e).isClosedEmbedding (currentWindowInclude_injective e))
  have hi (n : ℕ) := actualCurrentLaw_include e m (Ls n) ((hc n).mono fun _ h => h 0)
  simp_rw [hi,actualCurrentLaw_include e m L (hL.mono fun _ h => h 0)]
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous Ls L hlim
    (currentArrayWindow_continuous e 0 m)

lemma currentReferenceLaw_tendsto {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    {I : Type*} {l : Filter I} {Ws : I → ProbabilityMeasure (CurrentWindow e)} {W : ProbabilityMeasure (CurrentWindow e)}
    (h : Tendsto Ws l (𝓝 W)) :
    Tendsto (fun n => currentReferenceLaw e ν (Ws n)) l (𝓝 (currentReferenceLaw e ν W)) := by
  have hK : Continuous (Entropy.kernelProb (currentWindowReference e ν)) :=
    (ReferenceClasses.referenceProb_continuous ν).comp continuous_fst
  exact Entropy.compProdProb_tendsto (currentWindowReference e ν) hK
    (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous Ws W h continuous_fst)

theorem actualCurrentLaw_kl_weak_limit {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (m : ℕ)
    (Ls : ℕ → ProbabilityMeasure (ActualEpisodeArray e)) (L : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto Ls atTop (𝓝 L))
    (hc : ∀ n, ∀ᵐ Y ∂(Ls n : Measure (ActualEpisodeArray e)), ∀ j, ReferenceClasses.Consistent (currentOffsets e j Y))
    (C : ℝ) (hC : 0≤C)
    (hb : ∀ n, klDiv (actualCurrentLaw e m (Ls n) : Measure (CurrentWindow e))
      (currentReferenceLaw e ν (actualCurrentLaw e m (Ls n)) : Measure (CurrentWindow e)) ≤ ENNReal.ofReal C) :
    klDiv (actualCurrentLaw e m L : Measure (CurrentWindow e))
      (currentReferenceLaw e ν (actualCurrentLaw e m L) : Measure (CurrentWindow e)) ≤ ENNReal.ofReal C := by
  have ht := actualCurrentLaw_tendsto e m Ls L hlim hc
  exact Entropy.kl_le_of_weak_limit _ _ _ _ ht (currentReferenceLaw_tendsto e ν ht) hC (Filter.Eventually.of_forall hb)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_BadArraySampling
attribute [-instance] _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

lemma bad_raw_mass_pos (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (hN : C.sfloor ≤ (N:ℝ))
    (hmass : (N:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e N (1/2))) :
    0<(actualOccupationRaw e ν ((environmentLaw ν)[|badCrossingEvent e N (1/2)])
      (C.paddedTimes hef N) (C.paddedStages hef N) (C.paddedTimes_measurable hef N)
      N (C.activeCount hef N)).real Set.univ := by
  have hN0 : 0<N := by exact_mod_cast lt_of_lt_of_le zero_lt_one (C.hs.trans hN)
  have : IsProbabilityMeasure ((environmentLaw ν)[|badCrossingEvent e N (1/2)]) :=
    cond_isProbabilityMeasure (badCrossingEvent_pos e N (1/2) D (environmentLaw ν) hN0 hmass)
  have hpos := EpisodeChainLedger.operational_mass_positive (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N
    ((environmentLaw ν)[|badCrossingEvent e N (1/2)]) hN0
  have he := EpisodeChainLedger.operational_raw_mass (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ν
    ((environmentLaw ν)[|badCrossingEvent e N (1/2)])
  exact hpos.trans_eq he.symm

end OperationalConstants
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Entropy_BadWindowEntropy
attribute [-instance] _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)}
  {e f : Direction d} {D : ℝ}

lemma paddedTimes_stopping [IsProbabilityMeasure ν]
    (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (i : ℤ) (n : ℕ) :
    MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) n)]
      {ω | C.paddedTimes hef N ω i=n} :=
  episodeBoundary_height_event (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N i.toNat n

lemma paddedTimes_mono [IsProbabilityMeasure ν]
    (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (ω : Environment d) : Monotone (fun i : ℕ => C.paddedTimes hef N ω i) := by
  simpa only [paddedTimes,EpisodeChainLedger.arrayTime_nat] using
    episodeBoundary_mono (k:=C.k) e f hef (episodeScaleRadius ν e f)
      C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω

lemma paddedTimes_active [IsProbabilityMeasure ν]
    (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N i : ℕ) (ω : Environment d) :
    C.paddedTimes hef N ω i<N ↔ i<C.activeCount hef N ω := by
  simpa only [paddedTimes,EpisodeChainLedger.arrayTime_nat,activeCount] using
    EpisodeChainLedger.active_iff_lt_number (k:=C.k) e f hef (episodeScaleRadius ν e f)
      C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω i

lemma windowEntropyConstant_nonneg [IsProbabilityMeasure ν]
    (C : OperationalConstants ν e f D) (hD : 0≤D) :
    0≤C.windowEntropyConstant := mul_nonneg (mul_nonneg (by norm_num) hD) C.cost_nonneg

variable [IsProbabilityMeasure ν]

lemma bad_window_kl_le (C : OperationalConstants ν e f D) (hef : e.1≠f.1) (hD : 0≤D)
    (N m : ℕ) (hN : C.sfloor ≤ (N:ℝ))
    (hlarge : 32*C.b ≤ (1/2:ℝ)*Real.log (N:ℝ))
    (hmass : (N:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e N (1/2))) :
    let W := actualCurrentLaw e m
      (C.occupation hef N ((environmentLaw ν)[|badCrossingEvent e N (1/2)]))
    klDiv (W : Measure (CurrentWindow e)) (currentReferenceLaw e ν W : Measure (CurrentWindow e)) ≤
      ENNReal.ofReal ((m:ℝ)*C.windowEntropyConstant) := by
  let Q := (environmentLaw ν)[|badCrossingEvent e N (1/2)]
  have hN0 : 0<N := by exact_mod_cast lt_of_lt_of_le zero_lt_one (C.hs.trans hN)
  have : IsProbabilityMeasure Q :=
    cond_isProbabilityMeasure (badCrossingEvent_pos e N (1/2) D (environmentLaw ν) hN0 hmass)
  have hkl := badCrossing_cond_entropy e N (1/2) D (environmentLaw ν) hN0 hmass
  have hfin : klDiv Q (environmentLaw ν)≠∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkl
  have hpos := C.bad_raw_mass_pos hef N hN hmass
  have hb := actualOccupation_window_kl_le e ν Q hfin
    (C.paddedTimes hef N) (C.paddedStages hef N)
    (C.paddedTimes_measurable hef N) (C.paddedStages_measurable hef N)
    (C.paddedTimes_stopping hef N) (C.paddedTimes_mono hef N) N m (C.activeCount hef N)
    (C.paddedTimes_active hef N) hpos
  have he := EpisodeChainLedger.operational_raw_mass (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ν Q
  change (actualOccupationRaw e ν Q (C.paddedTimes hef N) (C.paddedStages hef N)
    (C.paddedTimes_measurable hef N) N (C.activeCount hef N)).real Set.univ = _ at he
  rw [he] at hb hpos
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  have hlog : 0≤Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN0.ne')
  have hkreal : (klDiv Q (environmentLaw ν)).toReal ≤ D*Real.log (N:ℝ) := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hkl
    rwa [ENNReal.toReal_ofReal (mul_nonneg hD hlog)] at hh
  obtain ⟨L,hL,hcharge⟩ := C.finite_charge
  have hl := (C.conditional_episode_drops hef hD N hN hlarge hmass L hL hcharge).1
  have hd := mul_le_mul_of_nonneg_left hl hD
  have hbudget : (klDiv Q (environmentLaw ν)).toReal ≤
      C.windowEntropyConstant*(∫ ω, (C.activeCount hef N ω:ℝ) ∂Q) := by
    unfold windowEntropyConstant
    dsimp only [Q]
    nlinarith only [hkreal,hd]
  apply (div_le_iff₀ hpos).mpr
  have hh := mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg m)
  simpa only [activeCount,mul_assoc] using hh

lemma bad_occupation_currentOffsets (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (hN : C.sfloor≤(N:ℝ))
    (hmass : (N:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e N (1/2))) :
    ∀ᵐ Y ∂(C.occupation hef N ((environmentLaw ν)[|badCrossingEvent e N (1/2)]) : Measure (ActualEpisodeArray e)),
      ∀ j, ReferenceClasses.Consistent (currentOffsets e j Y) :=
  actualOccupation_currentOffsets e ν _ (C.paddedTimes hef N) (C.paddedStages hef N)
    (C.paddedTimes_measurable hef N) (C.paddedStages_measurable hef N) N (C.activeCount hef N)
    (C.bad_raw_mass_pos hef N hN hmass)

theorem bad_limit_window_entropy (C : OperationalConstants ν e f D) (hef : e.1≠f.1) (hD : 0≤D)
    (Ns : ℕ → ℕ)
    (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hlarge : ∀ n, 32*C.b ≤ (1/2:ℝ)*Real.log (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2)))
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto (fun n => C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)])) atTop (𝓝 ρ)) (m : ℕ) :
    klDiv (actualCurrentLaw e m ρ : Measure (CurrentWindow e))
      (currentReferenceLaw e ν (actualCurrentLaw e m ρ) : Measure (CurrentWindow e)) ≤
      ENNReal.ofReal ((m:ℝ)*C.windowEntropyConstant) :=
  actualCurrentLaw_kl_weak_limit e ν m _ ρ hlim
    (fun n => C.bad_occupation_currentOffsets hef (Ns n) (hN n) (hmass n))
    ((m:ℝ)*C.windowEntropyConstant) (mul_nonneg (Nat.cast_nonneg m) (C.windowEntropyConstant_nonneg hD))
    (fun n => C.bad_window_kl_le hef hD (Ns n) m (hN n) (hlarge n) (hmass n))

end OperationalConstants
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_StationaryWindowEntropy
attribute [-instance] _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma stationary_currentWindow_law {d : ℕ} (e : Direction d) (m : ℕ)
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hstat : MeasurePreserving StationaryCompact.shift (ρ : Measure (ActualEpisodeArray e))
      (ρ : Measure (ActualEpisodeArray e))) (i : ℤ) :
    (ρ : Measure (ActualEpisodeArray e)).map (typedCurrentArrayWindow e i m) =
      (actualCurrentLaw e m ρ : Measure (CurrentWindow e)) := by
  have hs' (j : ℤ) : (ρ : Measure (ActualEpisodeArray e)).map (typedCurrentArrayWindow e (j+1) m)=
      (ρ : Measure (ActualEpisodeArray e)).map (typedCurrentArrayWindow e j m) := by
    calc
      _ = (ρ : Measure (ActualEpisodeArray e)).map (typedCurrentArrayWindow e j m ∘ StationaryCompact.shift) := rfl
      _ = ((ρ : Measure (ActualEpisodeArray e)).map StationaryCompact.shift).map (typedCurrentArrayWindow e j m) :=
        (Measure.map_map (typedCurrentArrayWindow_measurable e j m) hstat.measurable).symm
      _ = _ := by rw [hstat.map_eq]
  induction i using Int.induction_on with
  | zero => rfl
  | succ i hi => exact (hs' i).trans hi
  | pred i hi =>
    have hh := hs' (-(i:ℤ)-1)
    simp only [sub_add_cancel] at hh
    exact hh.symm.trans hi

namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

theorem stationary_window_entropy_oai (C : OperationalConstants ν e f D) (hef : e.1≠f.1) (hD : 0≤D)
    (Ns : ℕ → ℕ)
    (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hlarge : ∀ n, 32*C.b ≤ (1/2:ℝ)*Real.log (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2)))
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto (fun n => C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)])) atTop (𝓝 ρ))
    (hstat : MeasurePreserving StationaryCompact.shift (ρ : Measure (ActualEpisodeArray e))
      (ρ : Measure (ActualEpisodeArray e))) (i : ℤ) (m : ℕ) :
    let W := (ρ : Measure (ActualEpisodeArray e)).map (typedCurrentArrayWindow e i m)
    klDiv W (W.fst.compProd (currentWindowReference e ν)) ≤
      ENNReal.ofReal ((m:ℝ)*C.windowEntropyConstant) := by
  dsimp only
  rw [stationary_currentWindow_law e m ρ hstat i]
  exact C.bad_limit_window_entropy hef hD Ns hN hlarge hmass ρ hlim m

end OperationalConstants
end DirectionalTransience

end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.OperationalConstants.stationary_window_entropy_oai := @OAI.DirectionalTransience.OperationalConstants.stationary_window_entropy_oai
