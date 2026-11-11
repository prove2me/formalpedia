-- Prove2me | solution 1 for OAI.DirectionalTransience.OperationalConstants.conditional_episode_drops
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:55:19.199128+00:00
-- url     : https://prove2.me/submissions/8fb4c3de-3131-4d73-b388-6bca80196287

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal005
import Theorems.Thm_OAI_DirectionalTransience_EpisodeChainLedger_mean_episode_drops_local
import Theorems.Thm_OAI_DirectionalTransience_actual_expected_stages

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
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma badCrossingEvent_measurable {d : ℕ} (e : Direction d) (N : ℕ) (β : ℝ) :
    MeasurableSet (badCrossingEvent e N β) :=
  measurableSet_lt (measurable_crossingQuenched _ _ _).ennreal_toReal measurable_const

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

lemma badCrossing_cond_drop {d : ℕ} (e : Direction d) (N : ℕ) (β : ℝ)
    (P : Measure (Environment d)) (hN : 0<N)
    (hpositive : ∀ᵐ ω ∂P, 0<(crossingQuenched (realPosition (step e)) 0 N ω).toReal) :
    ∀ᵐ ω ∂P[|badCrossingEvent e N β],
      β*Real.log (N:ℝ) ≤ -Real.log (crossingQuenched (realPosition (step e)) 0 N ω).toReal := by
  have hc := (cond_absolutelyContinuous (μ:=P) (s:=badCrossingEvent e N β))
  filter_upwards [hc.ae_le hpositive,ae_cond_mem (badCrossingEvent_measurable e N β)] with ω hp hb
  have hl := Real.log_lt_log hp hb
  rw [Real.log_rpow (Nat.cast_pos.mpr hN)] at hl
  linarith

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeGlobalRetention
attribute [-instance] _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma coordinate_survival_lower {d : ℕ} (e : Direction d) (ω : Environment d)
    (κ : ℝ≥0) (hκ : ∀ y, κ ≤ (ω y).1 e) (H : ℕ) :
    (κ : ℝ≥0∞)^H ≤ crossingQuenched (realPosition (step e)) 0 H ω := by
  induction H with
  | zero => simp [crossingQuenched_zero]
  | succ H ih =>
    have hh := crossingQuenched_lower_step (realPosition (step e)) ω 0 e hκ (H:=H) (by positivity)
    rw [signed_direction_unit] at hh
    simpa only [Nat.cast_add,Nat.cast_one,pow_succ',Nat.succ_eq_add_one] using
      (mul_le_mul_right ih (κ : ℝ≥0∞)).trans hh

end DirectionalTransience

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

lemma height_pos (C : OperationalConstants ν e f D) :
    ∀ s, C.sfloor ≤ s → 0 < episodeStageH C.χ C.b s := by
  intro s hs
  have hpos : 0 < s := lt_of_lt_of_le zero_lt_one (C.hs.trans hs)
  exact_mod_cast (mul_pos hpos (Real.exp_pos _)).trans_le (C.height s hs)

theorem conditional_episode_drops_oai [IsProbabilityMeasure ν]
    (C : OperationalConstants ν e f D) (hef : e.1≠f.1) (hD : 0≤D)
    (N : ℕ) (hN : C.sfloor ≤ (N:ℝ)) (hlarge : 32*C.b ≤ (1/2:ℝ)*Real.log (N:ℝ))
    (hmass : (N:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e N (1/2)))
    (L : ℕ) (hL : 0<L) (hcharge : C.injectionCost ≤ 2*C.b*L) :
    let Q := (environmentLaw ν)[|badCrossingEvent e N (1/2)]
    (3/8*Real.log (N:ℝ) ≤ C.injectionCost*(∫ ω, (C.activeCount hef N ω:ℝ) ∂Q)) ∧
    ((∫ ω, (C.activeCount hef N ω:ℝ) ∂Q) ≤ Real.log (N:ℝ)/(16*C.b)+1) ∧
    (1/4*Real.log (N:ℝ) ≤ ∫ ω, ∑ i∈Finset.range N,
      if C.stagesAt hef N ω i ≤ L then C.dropAt hef N ω i else 0 ∂Q) := by
  let Q := (environmentLaw ν)[|badCrossingEvent e N (1/2)]
  have hN0 : 0<N := by exact_mod_cast lt_of_lt_of_le zero_lt_one (C.hs.trans hN)
  have hpos := badCrossingEvent_pos e N (1/2) D (environmentLaw ν) hN0 hmass
  have : IsProbabilityMeasure Q := cond_isProbabilityMeasure hpos
  have hκQ : ∀ᵐ ω ∂Q, ∀ y u, C.κ ≤ (ω y).1 u :=
    (cond_absolutelyContinuous (μ:=environmentLaw ν) (s:=badCrossingEvent e N (1/2))).ae_le C.rows
  have hpositive : ∀ᵐ ω ∂environmentLaw ν,
      0<(crossingQuenched (realPosition (step e)) 0 N ω).toReal := by
    filter_upwards [C.rows] with ω hω
    apply ENNReal.toReal_pos
    · exact ne_of_gt ((ENNReal.pow_pos (ENNReal.coe_pos.mpr C.hκ0) N).trans_le
        (coordinate_survival_lower e ω C.κ (fun y => hω y e) N))
    · exact crossingQuenched_ne_top _ _ _ _
  have hkl := badCrossing_cond_entropy e N (1/2) D (environmentLaw ν) hN0 hmass
  have hj := actual_expected_stages (k:=C.k) ν e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.K D (1/2) C.radius_nonneg N C.hs hN
    C.hf.le C.hg C.hb C.hK hD C.height C.stages Q hkl C.coeff C.small hlarge
  have hh := EpisodeChainLedger.mean_episode_drops_local (k:=C.k) e f hef
    (episodeScaleRadius ν e f) C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N
    C.order C.hf.le C.hb (lt_of_lt_of_le zero_lt_one C.hs) C.height_pos
    C.κ C.hκ0 C.hκ1 (lt_of_lt_of_le (by norm_num) C.hk) C.hbκ Q hκQ (1/2)
    (badCrossing_cond_drop e N (1/2) (environmentLaw ν) hN0 hpositive) hj L hL hcharge
  dsimp only [activeCount,injectionCost,stagesAt,dropAt]
  dsimp only [Q] at hh
  refine ⟨?_,?_,?_⟩
  · convert hh.1 using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · convert hh.2.1 using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · have hn : (1/2:ℝ)/2 = 1/4 := by norm_num
    rw [hn] at hh
    exact hh.2.2

end OperationalConstants
end DirectionalTransience

end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.OperationalConstants.conditional_episode_drops_oai := @OAI.DirectionalTransience.OperationalConstants.conditional_episode_drops_oai
