-- Prove2me | solution 1 for OAI.DirectionalTransience.OperationalConstants.bad_array_finite_marks
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:55:15.461041+00:00
-- url     : https://prove2.me/submissions/fe3d2b89-7dc0-462f-946d-d7180a45af4a

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal005
import Definitions.Def_OAIQ242Bal006
import Theorems.Thm_OAI_DirectionalTransience_OperationalConstants_bad_limit_drop_moment
import Theorems.Thm_OAI_DirectionalTransience_OperationalConstants_bad_limit_length_moment
import Theorems.Thm_OAI_DirectionalTransience_OperationalConstants_bad_occupation_stationary_limit
import Theorems.Thm_OAI_DirectionalTransience_OperationalConstants_conditional_episode_drops
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_AnchorMoments
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.state_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience.AnchorSampling

variable {I H : Type*} [Countable H] [MeasurableSpace H] [MeasurableSingletonClass H]

omit [Countable H] [MeasurableSingletonClass H] in
lemma atomMass_mem (ν : Measure H) [IsProbabilityMeasure ν] (x : H) :
    ν.real {x} ∈ Set.Icc (0:ℝ) 1 := ⟨measureReal_nonneg,measureReal_le_one⟩

omit [Countable H] [MeasurableSingletonClass H] in
lemma atomError_bound (ν : Measure H) [IsProbabilityMeasure ν] (F : H → H) (u v : H) :
    ‖atomError ν F u v‖≤1 := by
  have h := atomMass_mem ν (F u)
  rw [Real.norm_eq_abs,abs_le]
  unfold atomError
  split_ifs <;> constructor <;> linarith [h.1,h.2]

lemma integral_atomError (ν : Measure H) [IsProbabilityMeasure ν] (F : H → H) (u : H) :
    (∫ v, atomError ν F u v ∂ν)=0 := by
  have hi : Integrable (fun v : H => if v=F u then (1:ℝ) else 0) ν :=
    (integrable_const (1:ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => by split_ifs <;> norm_num)
  have he : (∫ v : H, (if v=F u then (1:ℝ) else 0) ∂ν)=ν.real {F u} := by
    simpa only [Set.indicator_apply,Set.mem_singleton_iff,Pi.one_apply] using
      (integral_indicator_one (μ:=ν) (measurableSet_singleton (F u)))
  simp only [atomError,integral_sub hi (integrable_const _),he,integral_const,probReal_univ,smul_eq_mul,one_mul,sub_self]

lemma pair_sampling_test (μ ν : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : H → H) (G : H → ℝ) (C : ℝ) (hG : ∀ u, ‖G u‖≤C) :
    (∫ p : H×H, G p.1*atomError ν F p.1 p.2 ∂μ.prod ν)=0 := by
  have hb (p : H×H) : ‖G p.1*atomError ν F p.1 p.2‖≤C := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (atomError_bound ν F p.1 p.2) (norm_nonneg _)).trans
      (by simpa using hG p.1)
  have hi := (integrable_const C (μ:=μ.prod ν)).mono' (measurable_of_countable _).aestronglyMeasurable
    (Filter.Eventually.of_forall hb)
  rw [integral_prod _ hi]
  simp only [integral_const_mul,integral_atomError,mul_zero,integral_zero]

lemma infinitePi_sampling_test (μ : I → Measure H) [∀ i, IsProbabilityMeasure (μ i)]
    (p q : I) (hpq : p≠q) (F : H → H) (G : H → ℝ) (C : ℝ) (hG : ∀ u, ‖G u‖≤C) :
    (∫ U, G (U p)*atomError (μ q) F (U p) (U q) ∂Measure.infinitePi μ)=0 := by
  have he := Measure.infinitePi_map_eval_prod (P:=μ) hpq
  have hm : Measurable (fun U : I → H => (U p,U q)) := (measurable_pi_apply p).prodMk (measurable_pi_apply q)
  rw [←integral_map hm.aemeasurable (measurable_of_countable
    (fun t : H×H => G t.1*atomError (μ q) F t.1 t.2)).aestronglyMeasurable,he]
  exact pair_sampling_test _ _ F G C hG

omit [Countable H] [MeasurableSingletonClass H] in
lemma infinitePi_pair_fresh (μ : I → Measure H) [∀ i, IsProbabilityMeasure (μ i)]
    (p b c : I) (hpc : p≠c) (hbc : b≠c) :
    (Measure.infinitePi μ).map (fun U : I → H => ((U p,U b),U c)) =
      ((Measure.infinitePi μ).map (fun U => (U p,U b))).prod (μ c) := by
  have hind := (iIndepFun_infinitePi (P:=μ) (X:= fun _ x => x) (fun _ => measurable_id)).indepFun_prodMk
    (fun i => measurable_pi_apply i) p b c hpc hbc
  rw [IndepFun.map_prod_eq_prod_map_map
    ((measurable_pi_apply p).prodMk (measurable_pi_apply b)).aemeasurable
    (measurable_pi_apply c).aemeasurable hind,Measure.infinitePi_map_eval]

lemma infinitePi_atomError_cross_fresh (μ : I → Measure H) [∀ i, IsProbabilityMeasure (μ i)]
    (ν : Measure H) [IsProbabilityMeasure ν] (p b c : I) (hc : μ c=ν)
    (hpc : p≠c) (hbc : b≠c) (F : H → H) :
    (∫ U, atomError ν F (U p) (U b)*atomError ν F (U p) (U c) ∂Measure.infinitePi μ)=0 := by
  let Ψ : (H×H)×H → ℝ := fun w => atomError ν F w.1.1 w.1.2*atomError ν F w.1.1 w.2
  have hΨm : Measurable Ψ := measurable_of_countable _
  have hm : Measurable (fun U : I → H => ((U p,U b),U c)) := by fun_prop
  have hb (w) : ‖Ψ w‖≤1 := by
    change ‖atomError ν F w.1.1 w.1.2*atomError ν F w.1.1 w.2‖≤1
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (atomError_bound _ _ _ _) (norm_nonneg _)).trans
      (by simpa using atomError_bound ν F w.1.1 w.1.2)
  have hΨi : Integrable Ψ (((Measure.infinitePi μ).map (fun U => (U p,U b))).prod ν) :=
    (integrable_const (1:ℝ)).mono' hΨm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  change (∫ U, Ψ ((U p,U b),U c) ∂Measure.infinitePi μ)=0
  rw [←integral_map hm.aemeasurable hΨm.aestronglyMeasurable,
    infinitePi_pair_fresh μ p b c hpc hbc,hc,integral_prod _ hΨi]
  simp only [Ψ,integral_const_mul,integral_atomError,mul_zero,integral_zero]

lemma infinitePi_atomError_cross (μ : I → Measure H) [∀ i, IsProbabilityMeasure (μ i)]
    (ν : Measure H) [IsProbabilityMeasure ν] (p b c : I) (hb : μ b=ν) (hc : μ c=ν)
    (hbc : b≠c) (F : H → H) :
    (∫ U, atomError ν F (U p) (U b)*atomError ν F (U p) (U c) ∂Measure.infinitePi μ)=0 := by
  by_cases hpc : p=c
  · have hpb : p≠b := by simpa [hpc] using hbc.symm
    simpa only [mul_comm] using infinitePi_atomError_cross_fresh μ ν p c b hb hpb hbc.symm F
  · exact infinitePi_atomError_cross_fresh μ ν p b c hc hpc hbc F

lemma atomError_eval_measurable (ν : Measure H) (F : H → H) (p b : I) :
    Measurable (fun U : I→H => atomError ν F (U p) (U b)) := by
  have hm : Measurable (fun U : I→H => (U p,U b)) :=
    (measurable_pi_apply p).prodMk (measurable_pi_apply b)
  exact (measurable_of_countable (fun t : H×H => atomError ν F t.1 t.2)).comp hm

lemma atomError_eval_product_integrable (μ : I → Measure H) [∀ i, IsProbabilityMeasure (μ i)]
    (ν : Measure H) [IsProbabilityMeasure ν] (F : H→H) (p b c : I) :
    Integrable (fun U => atomError ν F (U p) (U b)*atomError ν F (U p) (U c)) (Measure.infinitePi μ) := by
  apply (integrable_const (1:ℝ)).mono'
    ((atomError_eval_measurable ν F p b).mul (atomError_eval_measurable ν F p c)).aestronglyMeasurable
  filter_upwards [] with U
  change ‖atomError ν F (U p) (U b)*atomError ν F (U p) (U c)‖≤1
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (atomError_bound _ _ _ _) (norm_nonneg _)).trans
    (by simpa using atomError_bound ν F (U p) (U b))

theorem infinitePi_sample_sum_sq (μ : I → Measure H) [∀ i, IsProbabilityMeasure (μ i)]
    (ν : Measure H) [IsProbabilityMeasure ν] (p : I) (S : Finset I)
    (hlaw : ∀ b∈S, μ b=ν) (F : H→H) :
    (∫ U, (∑ b∈S, atomError ν F (U p) (U b))^2 ∂Measure.infinitePi μ)≤S.card := by
  classical
  have hprod := atomError_eval_product_integrable μ ν F p
  have he (U : I→H) : (∑ b∈S, atomError ν F (U p) (U b))^2 =
      ∑ b∈S, ∑ c∈S, atomError ν F (U p) (U b)*atomError ν F (U p) (U c) := by
    simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun b _ => integrable_finsetSum _ (fun c _ => hprod b c))]
  simp_rw [integral_finsetSum _ (fun c _ => hprod _ c)]
  calc
    (∑ b∈S, ∑ c∈S, ∫ U, atomError ν F (U p) (U b)*atomError ν F (U p) (U c) ∂Measure.infinitePi μ)
      = ∑ b∈S, ∫ U, atomError ν F (U p) (U b)*atomError ν F (U p) (U b) ∂Measure.infinitePi μ := by
        apply Finset.sum_congr rfl
        intro b hb
        apply Finset.sum_eq_single b
        · intro c hc hcb
          exact infinitePi_atomError_cross μ ν p b c (hlaw b hb) (hlaw c hc) hcb.symm F
        · intro h
          exact False.elim (h hb)
    _ ≤ ∑ _b∈S, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro b hb
      have hle : (∫ U, atomError ν F (U p) (U b)*atomError ν F (U p) (U b) ∂Measure.infinitePi μ)≤
          ∫ _U : I→H, (1:ℝ) ∂Measure.infinitePi μ := by
        apply integral_mono (hprod b b) (integrable_const _)
        intro U
        have hh := atomError_bound ν F (U p) (U b)
        rw [Real.norm_eq_abs,abs_le] at hh
        nlinarith [sq_nonneg (atomError ν F (U p) (U b))]
      simpa using hle
    _ = S.card := by simp

theorem infinitePi_sample_average_sq (μ : I → Measure H) [∀ i, IsProbabilityMeasure (μ i)]
    (ν : Measure H) [IsProbabilityMeasure ν] (p : I) (S : Finset I)
    (hlaw : ∀ b∈S, μ b=ν) (F : H→H) :
    (∫ U, ((S.card:ℝ)⁻¹*∑ b∈S, atomError ν F (U p) (U b))^2 ∂Measure.infinitePi μ)≤(S.card:ℝ)⁻¹ := by
  simp_rw [mul_pow,integral_const_mul]
  have hh := mul_le_mul_of_nonneg_left (infinitePi_sample_sum_sq μ ν p S hlaw F)
    (sq_nonneg (S.card:ℝ)⁻¹)
  apply hh.trans_eq
  by_cases hs : S.card=0
  · simp [hs]
  · have hn : (S.card:ℝ)≠0 := Nat.cast_ne_zero.mpr hs
    field_simp

end DirectionalTransience.AnchorSampling

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
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_Sampling
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped ENNReal NNReal BigOperators Classical Topology
namespace DirectionalTransience

lemma arrayOffsetTest_mem {d : ℕ} (e : Direction d) (p q : ℤ×ℕ) (z : HorizontalSpace e)
    (X : ActualEpisodeArray e) : arrayOffsetTest e p q z X∈Set.Icc (0:ℝ) 1 := by
  change (if _ then (1:ℝ) else 0)∈Set.Icc (0:ℝ) 1
  split_ifs <;> norm_num

lemma arrayProfileTest_mem {d : ℕ} (e : Direction d) (j : ℤ) (p : ℤ×ℕ) (z : HorizontalSpace e)
    (X : ActualEpisodeArray e) : arrayProfileTest e j p z X∈Set.Icc (0:ℝ) 1 := (X.2.2.1 (j,p,z)).property

lemma arraySamplingError_bound {d : ℕ} (e : Direction d) (p : ℤ×ℕ) (j : ℤ)
    (z : HorizontalSpace e) (n : ℕ) (X : ActualEpisodeArray e) : ‖arraySamplingError e p j z n X‖≤1 := by
  have hsum0 : 0≤∑ b∈Finset.range n, arrayOffsetTest e p (j,b) z X :=
    Finset.sum_nonneg (fun b _ => (arrayOffsetTest_mem e p (j,b) z X).1)
  have hsum1 : (∑ b∈Finset.range n, arrayOffsetTest e p (j,b) z X)≤(n:ℝ) := by
    calc _ ≤ ∑ _b∈Finset.range n, (1:ℝ) :=
      Finset.sum_le_sum fun b _ => (arrayOffsetTest_mem e p (j,b) z X).2
    _ = _ := by simp
  have ha0 : 0≤(n:ℝ)⁻¹*∑ b∈Finset.range n, arrayOffsetTest e p (j,b) z X :=
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) hsum0
  have ha1 : (n:ℝ)⁻¹*∑ b∈Finset.range n, arrayOffsetTest e p (j,b) z X≤1 := by
    apply (mul_le_mul_of_nonneg_left hsum1 (inv_nonneg.mpr (Nat.cast_nonneg n))).trans
    by_cases hn : n=0
    · simp [hn]
    · rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn)]
  have hw := arrayProfileTest_mem e j p z X
  change |(n:ℝ)⁻¹*(∑ b∈Finset.range n, arrayOffsetTest e p (j,b) z X)-arrayProfileTest e j p z X|≤1
  rw [abs_le]
  constructor <;> linarith [hw.1,hw.2]

lemma actual_array_error_atom {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (X : EpisodeInput e) (p : ℤ×ℕ) (j : ℤ)
    (z : HorizontalSpace e) (n : ℕ) (hn : 0<n) :
    arraySamplingError e p j z n (actualArrayMap e t J X) =
      (n:ℝ)⁻¹*∑ b∈Finset.range n,
        AnchorSampling.atomError (episodeProfile e t X.1.1 j) (fun u => u+z) (X.1.2 p) (X.1.2 (j,b)) := by
  have he b : arrayOffsetTest e p (j,b) z (actualArrayMap e t J X) =
      (if X.1.2 (j,b)=X.1.2 p+z then (1:ℝ) else 0) := by
    simp only [arrayOffsetTest,ContinuousMap.coe_mk,actualArrayMap,finiteOffsetTest,OnePoint.coe_injective.eq_iff]
    congr 1
    apply propext
    constructor
    · intro h
      exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
    · intro h
      exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))
  have hw : arrayProfileTest e j p z (actualArrayMap e t J X)=
      (episodeProfile e t X.1.1 j).real {X.1.2 p+z} := rfl
  change (n:ℝ)⁻¹*(∑ b∈Finset.range n, arrayOffsetTest e p (j,b) z (actualArrayMap e t J X))-
    arrayProfileTest e j p z (actualArrayMap e t J X)=_
  simp_rw [he,hw,AnchorSampling.atomError,Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  rw [mul_sub,←mul_assoc,inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn.ne'),one_mul]
  congr 2
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> rfl

lemma actual_array_sampling_sq_conditional {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (ω : Environment d) (ξ : EpisodeAuxiliary e) (p : ℤ×ℕ) (j : ℤ)
    (z : HorizontalSpace e) (n : ℕ) (hn : 0<n) :
    (∫ U, (arraySamplingError e p j z n (actualArrayMap e t J ((ω,U),ξ)))^2
      ∂globalEpisodeAnchors e t ht ω)≤(n:ℝ)⁻¹ := by
  let f : ℕ ↪ ℤ×ℕ := ⟨fun b => (j,b),fun a b h => (Prod.mk.inj h).2⟩
  let S := (Finset.range n).map f
  have hcard : S.card=n := by simp [S]
  have hh := AnchorSampling.infinitePi_sample_average_sq
    (fun q : ℤ×ℕ => episodeProfile e t ω q.1) (episodeProfile e t ω j) p S
    (fun b hb => by obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hb; rfl) (fun u => u+z)
  simp only [hcard] at hh
  simp only [globalEpisodeAnchors,AnchorSampling.anchorKernel,Kernel.coe_mk]
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards [] with U
  rw [actual_array_error_atom e t J _ p j z n hn]
  simp only [S,Finset.sum_map,f]
  rfl

lemma actual_array_offset {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (X : EpisodeInput e) (p q : ℤ×ℕ)
    (z : HorizontalSpace e) :
    arrayOffsetTest e p q z (actualArrayMap e t J X) =
      (if X.1.2 q=X.1.2 p+z then (1:ℝ) else 0) := by
  simp only [arrayOffsetTest,ContinuousMap.coe_mk,actualArrayMap,finiteOffsetTest,
    OnePoint.coe_injective.eq_iff]
  congr 1
  apply propext
  constructor
  · intro h
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  · intro h
    exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))

lemma actual_array_profile {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (X : EpisodeInput e) (p : ℤ×ℕ) (j : ℤ)
    (z : HorizontalSpace e) :
    arrayProfileTest e j p z (actualArrayMap e t J X)=
      (episodeProfile e t X.1.1 j).real {X.1.2 p+z} := rfl

lemma actual_array_sampling_test_conditional {d : ℕ} (e : Direction d)
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (ω : Environment d) (ξ : EpisodeAuxiliary e) (p q : ℤ×ℕ) (hpq : p≠q)
    (z : HorizontalSpace e) (g : C(ℝ,ℝ)) :
    (∫ U, g (arrayProfileTest e q.1 p z (actualArrayMap e t J ((ω,U),ξ)))*
      (arrayOffsetTest e p q z (actualArrayMap e t J ((ω,U),ξ))-
        arrayProfileTest e q.1 p z (actualArrayMap e t J ((ω,U),ξ)))
      ∂globalEpisodeAnchors e t ht ω)=0 := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f:=fun x : ℝ => g x) g.continuous.continuousOn
  have hG (u : HorizontalSpace e) :
      ‖g ((episodeProfile e t ω q.1).real {u+z})‖≤C := by
    apply hC
    exact ⟨measureReal_nonneg,measureReal_le_one⟩
  have hh := AnchorSampling.infinitePi_sampling_test
    (fun q : ℤ×ℕ => episodeProfile e t ω q.1) p q hpq (fun u => u+z)
    (fun u => g ((episodeProfile e t ω q.1).real {u+z})) C hG
  simp only [globalEpisodeAnchors,AnchorSampling.anchorKernel,Kernel.coe_mk]
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards [] with U
  rw [actual_array_offset,actual_array_profile]
  unfold AnchorSampling.atomError
  congr 2
  split_ifs <;> rfl

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SamplingLaw
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

lemma restrict_compProd_fst {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (Q : Measure Ω) [SFinite Q] (K : Kernel Ω A) [IsSFiniteKernel K]
    (s : Set Ω) (hs : MeasurableSet s) :
    (Q.compProd K).restrict (Prod.fst ⁻¹' s)=(Q.restrict s).compProd K := by
  ext B hB
  rw [Measure.restrict_apply hB,Measure.compProd_apply (hB.inter (hs.preimage measurable_fst)),
    Measure.compProd_apply hB,←lintegral_indicator hs]
  apply lintegral_congr
  intro ω
  by_cases hω : ω∈s
  · have he : Prod.mk ω ⁻¹' Prod.fst ⁻¹' s = (Set.univ : Set A) := by
      ext a
      simp [hω]
    simp [Set.indicator_of_mem hω,he]
  · have he : Prod.mk ω ⁻¹' Prod.fst ⁻¹' s = (∅ : Set A) := by
      ext a
      simp [hω]
    simp [Set.indicator_of_notMem hω,he]

lemma episodeInputLaw_restrict {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (s : Set (Environment d)) (hs : MeasurableSet s) :
    (episodeInputLaw e ν Q t ht).restrict {X | X.1.1∈s}=
      episodeInputLaw e ν (Q.restrict s) t ht := by
  unfold episodeInputLaw
  rw [←restrict_compProd_fst Q (globalEpisodeAnchors e t ht) s hs,
    Measure.restrict_prod_eq_prod_univ]
  congr 1
  ext X
  simp

lemma actualArray_integrable {d : ℕ} (e : Direction d)
    (μ : Measure (EpisodeInput e)) [IsFiniteMeasure μ]
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (F : C(ActualEpisodeArray e,ℝ)) : Integrable (fun X => F (actualArrayMap e t J X)) μ := by
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn F.continuous.continuousOn
  apply (integrable_const C).mono'
    ((F.continuous.measurable.comp (actualArrayMap_measurable e t J ht hJ)).aestronglyMeasurable)
  exact Eventually.of_forall fun X => hC _ (Set.mem_univ _)

lemma actual_array_sampling_sq_law {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (p : ℤ×ℕ) (j : ℤ) (z : HorizontalSpace e) (n : ℕ) (hn : 0<n) :
    (∫ X, (arraySamplingError e p j z n (actualArrayMap e t J X))^2
      ∂episodeInputLaw e ν Q t ht)≤Q.real Set.univ*(n:ℝ)⁻¹ := by
  let F : C(ActualEpisodeArray e,ℝ) := ⟨fun Y => (arraySamplingError e p j z n Y)^2,by fun_prop⟩
  have hi := actualArray_integrable e (episodeInputLaw e ν Q t ht) t J ht hJ F
  change (∫ X, F (actualArrayMap e t J X) ∂((Q.compProd (globalEpisodeAnchors e t ht)).prod
    (episodeAuxiliaryLaw e ν)))≤_
  rw [integral_prod_symm _ hi]
  have hc (ξ : EpisodeAuxiliary e) :
      (∫ w, F (actualArrayMap e t J (w,ξ)) ∂Q.compProd (globalEpisodeAnchors e t ht))≤
        Q.real Set.univ*(n:ℝ)⁻¹ := by
    have hm : Measurable (fun w => F (actualArrayMap e t J (w,ξ))) :=
      (F.continuous.measurable.comp (actualArrayMap_measurable e t J ht hJ)).comp measurable_prodMk_right
    have hib : Integrable (fun w => F (actualArrayMap e t J (w,ξ)))
        (Q.compProd (globalEpisodeAnchors e t ht)) := by
      apply (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
      filter_upwards [] with w
      change ‖(arraySamplingError e p j z n (actualArrayMap e t J (w,ξ)))^2‖≤1
      rw [norm_pow]
      exact (pow_le_pow_left₀ (norm_nonneg _) (arraySamplingError_bound _ _ _ _ _ _) 2).trans_eq (one_pow _)
    rw [Measure.integral_compProd hib]
    have hbound ω := actual_array_sampling_sq_conditional e t J ht ω ξ p j z n hn
    calc
      _ ≤ (∫ _ω, (n:ℝ)⁻¹ ∂Q) := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun ω => integral_nonneg fun U => sq_nonneg _)
          (integrable_const _)
        exact Eventually.of_forall hbound
      _ = _ := by simp [integral_const,smul_eq_mul]
  have hnon : 0≤Q.real Set.univ*(n:ℝ)⁻¹ := mul_nonneg measureReal_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  calc
    _ ≤ (∫ _ξ, Q.real Set.univ*(n:ℝ)⁻¹ ∂episodeAuxiliaryLaw e ν) := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun ξ => integral_nonneg fun w => sq_nonneg _)
        (integrable_const _)
      exact Eventually.of_forall hc
    _ = _ := by simp [integral_const,smul_eq_mul]

lemma actual_array_sampling_test_law {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (p q : ℤ×ℕ) (hpq : p≠q) (z : HorizontalSpace e) (g : C(ℝ,ℝ)) :
    (∫ X, g (arrayProfileTest e q.1 p z (actualArrayMap e t J X))*
      (arrayOffsetTest e p q z (actualArrayMap e t J X)-
        arrayProfileTest e q.1 p z (actualArrayMap e t J X))
      ∂episodeInputLaw e ν Q t ht)=0 := by
  let F : C(ActualEpisodeArray e,ℝ) := ⟨fun Y => g (arrayProfileTest e q.1 p z Y)*
      (arrayOffsetTest e p q z Y-arrayProfileTest e q.1 p z Y),by fun_prop⟩
  have hi := actualArray_integrable e (episodeInputLaw e ν Q t ht) t J ht hJ F
  change (∫ X, F (actualArrayMap e t J X) ∂((Q.compProd (globalEpisodeAnchors e t ht)).prod
    (episodeAuxiliaryLaw e ν)))=0
  rw [integral_prod_symm _ hi]
  have hz (ξ : EpisodeAuxiliary e) :
      (∫ w, F (actualArrayMap e t J (w,ξ)) ∂Q.compProd (globalEpisodeAnchors e t ht))=0 := by
    obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn F.continuous.continuousOn
    have hm : Measurable (fun w => F (actualArrayMap e t J (w,ξ))) :=
      (F.continuous.measurable.comp (actualArrayMap_measurable e t J ht hJ)).comp measurable_prodMk_right
    have hib := (integrable_const C (μ:=Q.compProd (globalEpisodeAnchors e t ht))).mono' hm.aestronglyMeasurable
      (Eventually.of_forall fun w => hC _ (Set.mem_univ _))
    rw [Measure.integral_compProd hib]
    have he ω : (∫ U, F (actualArrayMap e t J ((ω,U),ξ)) ∂globalEpisodeAnchors e t ht ω)=0 :=
      actual_array_sampling_test_conditional e t J ht ω ξ p q hpq z g
    simp only [he,integral_zero]
  simp only [hz,integral_zero]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

lemma arrayOffsetTest_shift {d : ℕ} (e : Direction d) (p q : ℤ×ℕ)
    (z : HorizontalSpace e) (Y : ActualEpisodeArray e) :
    arrayOffsetTest e p q z (StationaryCompact.shift Y)=
      arrayOffsetTest e (p.1+1,p.2) (q.1+1,q.2) z Y := rfl

lemma arrayProfileTest_shift {d : ℕ} (e : Direction d) (j : ℤ) (p : ℤ×ℕ)
    (z : HorizontalSpace e) (Y : ActualEpisodeArray e) :
    arrayProfileTest e j p z (StationaryCompact.shift Y)=
      arrayProfileTest e (j+1) (p.1+1,p.2) z Y := rfl

lemma arrayOffsetTest_iterate {d : ℕ} (e : Direction d) (p q : ℤ×ℕ)
    (z : HorizontalSpace e) (Y : ActualEpisodeArray e) (r : ℕ) :
    arrayOffsetTest e p q z (StationaryCompact.shift^[r] Y)=
      arrayOffsetTest e (p.1+r,p.2) (q.1+r,q.2) z Y := by
  induction r generalizing p q with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply',arrayOffsetTest_shift,ih]
    simp only [Nat.cast_add,Nat.cast_one,add_left_comm,add_comm]

lemma arrayProfileTest_iterate {d : ℕ} (e : Direction d) (j : ℤ) (p : ℤ×ℕ)
    (z : HorizontalSpace e) (Y : ActualEpisodeArray e) (r : ℕ) :
    arrayProfileTest e j p z (StationaryCompact.shift^[r] Y)=
      arrayProfileTest e (j+r) (p.1+r,p.2) z Y := by
  induction r generalizing j p with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply',arrayProfileTest_shift,ih]
    simp only [Nat.cast_add,Nat.cast_one,add_left_comm,add_comm]

lemma arraySamplingError_iterate {d : ℕ} (e : Direction d) (p : ℤ×ℕ) (j : ℤ)
    (z : HorizontalSpace e) (n r : ℕ) (Y : ActualEpisodeArray e) :
    arraySamplingError e p j z n (StationaryCompact.shift^[r] Y)=
      arraySamplingError e (p.1+r,p.2) (j+r) z n Y := by
  change (n:ℝ)⁻¹*(∑ b∈Finset.range n, arrayOffsetTest e p (j,b) z (StationaryCompact.shift^[r] Y))-
    arrayProfileTest e j p z (StationaryCompact.shift^[r] Y)=_
  simp only [arrayOffsetTest_iterate,arrayProfileTest_iterate]
  rfl

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_SamplingLimit
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal Topology
namespace DirectionalTransience.Sampling

variable {X : Type*} [MeasurableSpace X]

theorem ae_tendsto_zero_of_sq_integrals {μ : Measure X} (f : ℕ → X → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (b : ℕ → ℝ) (hb : Summable b)
    (hbound : ∀ n, ∫⁻ x, ENNReal.ofReal ((f n x)^2) ∂μ ≤ ENNReal.ofReal (b n)) :
    ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 0) := by
  have hm (n) : AEMeasurable (fun x => ENNReal.ofReal ((f n x)^2)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((hf n).aemeasurable.pow_const 2)
  have hfin : (∫⁻ x, ∑' n, ENNReal.ofReal ((f n x)^2) ∂μ) < ∞ := by
    rw [lintegral_tsum hm]
    exact (ENNReal.tsum_le_tsum hbound).trans_lt hb.tsum_ofReal_lt_top
  filter_upwards [ae_lt_top' (AEMeasurable.tsum hm) hfin.ne] with x hx
  have hs := ENNReal.summable_toReal hx.ne
  have he : (fun n => (ENNReal.ofReal ((f n x)^2)).toReal) = (fun n => (f n x)^2) := by
    funext n
    exact ENNReal.toReal_ofReal (sq_nonneg _)
  rw [he] at hs
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs.tendsto_atTop_zero
  simp only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] at ht
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using ht)

section Compact
variable [TopologicalSpace X] [CompactSpace X] [BorelSpace X]

lemma sq_integral_bound_of_weak_limit (μs : ℕ → ProbabilityMeasure X)
    (μ : ProbabilityMeasure X) (hμ : Tendsto μs atTop (𝓝 μ))
    (f : C(X,ℝ)) {b : ℝ}
    (hb : ∀ k, ∫ x, (f x)^2 ∂(μs k : Measure X) ≤ b) :
    ∫ x, (f x)^2 ∂μ ≤ b := by
  let g : C(X,ℝ) := ⟨fun x => (f x)^2, f.continuous.pow 2⟩
  have ht := (ProbabilityMeasure.continuous_integral_continuousMap g).continuousAt.tendsto.comp hμ
  exact le_of_tendsto ht (Eventually.of_forall hb)

theorem ae_sampling_of_weak_limit (μs : ℕ → ProbabilityMeasure X)
    (μ : ProbabilityMeasure X) (hμ : Tendsto μs atTop (𝓝 μ))
    (e : ℕ → C(X,ℝ)) (b : ℕ → ℝ) (hb : Summable b)
    (he : ∀ k n, ∫ x, (e n x)^2 ∂(μs k : Measure X) ≤ b n) :
    ∀ᵐ x ∂(μ : Measure X), Tendsto (fun n => e n x) atTop (𝓝 0) := by
  apply ae_tendsto_zero_of_sq_integrals (fun n => e n) (fun n => (e n).continuous.aestronglyMeasurable) b hb
  intro n
  have hi : Integrable (fun x => (e n x)^2) (μ : Measure X) :=
    ((e n).continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun x => sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (sq_integral_bound_of_weak_limit μs μ hμ (e n) (fun k => he k n))

end Compact
end DirectionalTransience.Sampling

end

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal Topology
namespace DirectionalTransience.Sampling

variable {X : Type*} [MeasurableSpace X]

lemma cutoff_tendsto (w : ℝ) (hw : 0 ≤ w) :
    Tendsto (fun n : ℕ => max 0 (1-(n:ℝ)*w)) atTop (𝓝 (if w=0 then 1 else 0)) := by
  by_cases h : w=0
  · simp [h]
  · rw [ite_eq_right h]
    have hp : 0 < w := lt_of_le_of_ne hw (Ne.symm h)
    obtain ⟨N,hN⟩ := exists_nat_gt (1/w)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N:ℝ) ≤ n := Nat.cast_le.mpr hn
    have hnw : 1 < (n:ℝ)*w := (div_lt_iff₀ hp).mp (hN.trans_le hn')
    exact (max_eq_left (by linarith)).symm

theorem ae_zero_of_sampling_tests {μ : Measure X} [IsFiniteMeasure μ]
    (w I : X → ℝ) (hw : Measurable w) (hI : Measurable I)
    (hw01 : ∀ x, w x ∈ Set.Icc (0:ℝ) 1)
    (hI01 : ∀ x, I x ∈ Set.Icc (0:ℝ) 1)
    (htest : ∀ g : C(ℝ,ℝ), (∫ x, g (w x)*(I x-w x) ∂μ)=0) :
    ∀ᵐ x ∂μ, w x=0 → I x=0 := by
  classical
  let F : ℕ → X → ℝ := fun n x => max 0 (1-(n:ℝ)*w x)*(I x-w x)
  let G : X → ℝ := fun x => if w x=0 then I x else 0
  have hFm (n : ℕ) : Measurable (F n) := by dsimp [F]; fun_prop
  have hGm : Measurable G := by
    dsimp [G]
    exact Measurable.ite (hw (measurableSet_singleton 0)) hI measurable_const
  have hgb x : 0 ≤ G x ∧ G x ≤ 1 := by
    dsimp [G]
    split_ifs
    · exact hI01 x
    · norm_num
  have hFb (n : ℕ) (x : X) : ‖F n x‖ ≤ 1 := by
    have hc0 : 0 ≤ max 0 (1-(n:ℝ)*w x) := le_max_left _ _
    have hc1 : max 0 (1-(n:ℝ)*w x) ≤ 1 := by
      apply max_le (by norm_num)
      have hh := mul_nonneg (Nat.cast_nonneg n) (hw01 x).1
      linarith
    have hsub : |I x-w x| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [(hI01 x).1,(hI01 x).2,(hw01 x).1,(hw01 x).2]
    dsimp [F]
    rw [abs_mul, abs_of_nonneg hc0]
    exact (mul_le_mul_of_nonneg_left hsub hc0).trans (by simpa using hc1)
  have hFlim (x : X) : Tendsto (fun n => F n x) atTop (𝓝 (G x)) := by
    have hh := (cutoff_tendsto (w x) (hw01 x).1).mul_const (I x-w x)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [G]
    split_ifs with h <;> simp [h]
  have hi := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ : X => (1:ℝ))
    (fun n => (hFm n).aestronglyMeasurable) (integrable_const 1)
    (fun n => Eventually.of_forall (hFb n)) (Eventually.of_forall hFlim)
  have hFzero (n : ℕ) : (∫ x, F n x ∂μ)=0 := by
    exact htest ⟨fun t => max 0 (1-(n:ℝ)*t),by fun_prop⟩
  simp only [hFzero] at hi
  have hGzero : (∫ x, G x ∂μ)=0 := tendsto_nhds_unique hi tendsto_const_nhds
  have hGi : Integrable G μ := (integrable_const (1:ℝ)).mono' hGm.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hgb x).1]; exact (hgb x).2)
  have hz := (integral_eq_zero_iff_of_nonneg (fun x => (hgb x).1) hGi).mp hGzero
  filter_upwards [hz] with x hx h
  simpa [G,h] using hx

section Compact
variable [TopologicalSpace X] [CompactSpace X] [BorelSpace X]

theorem sampling_tests_weak_limit (μs : ℕ → ProbabilityMeasure X)
    (μ : ProbabilityMeasure X) (hμ : Tendsto μs atTop (𝓝 μ))
    (w I : C(X,ℝ))
    (htest : ∀ k (g : C(ℝ,ℝ)),
      (∫ x, g (w x)*(I x-w x) ∂(μs k : Measure X))=0) :
    ∀ g : C(ℝ,ℝ), (∫ x, g (w x)*(I x-w x) ∂(μ : Measure X))=0 := by
  intro g
  let F : C(X,ℝ) := ⟨fun x => g (w x)*(I x-w x),by fun_prop⟩
  have ht := (ProbabilityMeasure.continuous_integral_continuousMap F).continuousAt.tendsto.comp hμ
  have he (k) : (∫ x, F x ∂(μs k : Measure X))=0 := htest k g
  change Tendsto (fun k => ∫ x, F x ∂(μs k : Measure X)) atTop _ at ht
  simp only [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

end Compact
end DirectionalTransience.Sampling

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
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_OccupationSampling
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

lemma actualOccupationRaw_integral {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (N : ℕ) (M : Environment d → ℕ) (hM : Measurable M) (F : C(ActualEpisodeArray e,ℝ)) :
    (∫ Y, F Y ∂actualOccupationRaw e ν Q t J ht N M)=
      ∑ i∈Finset.range N, ∫ X, F (StationaryCompact.shift^[i] (actualArrayMap e t J X))
        ∂episodeInputLaw e ν (Q.restrict {ω | i<M ω}) t ht := by
  unfold actualOccupationRaw StationaryCompact.episodeOccupationRaw
  rw [integral_finsetSum_measure (fun i _ =>
    F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  apply Finset.sum_congr rfl
  intro i _
  have hm : Measurable (fun X : EpisodeInput e => StationaryCompact.shift^[i] (actualArrayMap e t J X)) :=
    (StationaryCompact.shift_continuous.measurable.iterate i).comp (actualArrayMap_measurable e t J ht hJ)
  rw [integral_map hm.aemeasurable F.continuous.aestronglyMeasurable]
  have hr : (episodeInputLaw e ν Q t ht).restrict {X | i<M X.1.1}=
      episodeInputLaw e ν (Q.restrict {ω | i<M ω}) t ht :=
    episodeInputLaw_restrict e ν Q t ht {ω | i<M ω} (measurableSet_lt measurable_const hM)
  change (∫ X, F (StationaryCompact.shift^[i] (actualArrayMap e t J X))
    ∂(episodeInputLaw e ν Q t ht).restrict {X | i<M X.1.1})=_
  rw [hr]

lemma episodeInputLaw_real_univ {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i) :
    (episodeInputLaw e ν Q t ht).real Set.univ=Q.real Set.univ := by
  simp [Measure.real,episodeInputLaw,Measure.prod_apply,Measure.compProd_apply,
    measure_univ]

lemma actualOccupationRaw_mass {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (N : ℕ) (M : Environment d → ℕ) (hM : Measurable M) :
    (actualOccupationRaw e ν Q t J ht N M).real Set.univ=
      ∑ i∈Finset.range N, (Q.restrict {ω | i<M ω}).real Set.univ := by
  have h := actualOccupationRaw_integral e ν Q t J ht hJ N M hM (1 : C(ActualEpisodeArray e,ℝ))
  simpa only [ContinuousMap.one_apply,integral_const,smul_eq_mul,mul_one,
    episodeInputLaw_real_univ] using h

lemma actualOccupationRaw_sampling_sq {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (N : ℕ) (M : Environment d → ℕ) (hM : Measurable M)
    (p : ℤ×ℕ) (j : ℤ) (z : HorizontalSpace e) (n : ℕ) (hn : 0<n) :
    (∫ Y, (arraySamplingError e p j z n Y)^2 ∂actualOccupationRaw e ν Q t J ht N M)≤
      (actualOccupationRaw e ν Q t J ht N M).real Set.univ*(n:ℝ)⁻¹ := by
  let F : C(ActualEpisodeArray e,ℝ) := ⟨fun Y => (arraySamplingError e p j z n Y)^2,by fun_prop⟩
  change (∫ Y, F Y ∂actualOccupationRaw e ν Q t J ht N M)≤_
  rw [actualOccupationRaw_integral e ν Q t J ht hJ N M hM F,
    actualOccupationRaw_mass e ν Q t J ht hJ N M hM,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  simp only [F,ContinuousMap.coe_mk,arraySamplingError_iterate]
  exact actual_array_sampling_sq_law e ν (Q.restrict {ω | i<M ω}) t J ht hJ _ _ z n hn

lemma actualOccupationRaw_sampling_test {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (N : ℕ) (M : Environment d → ℕ) (hM : Measurable M)
    (p q : ℤ×ℕ) (hpq : p≠q) (z : HorizontalSpace e) (g : C(ℝ,ℝ)) :
    (∫ Y, g (arrayProfileTest e q.1 p z Y)*
      (arrayOffsetTest e p q z Y-arrayProfileTest e q.1 p z Y)
      ∂actualOccupationRaw e ν Q t J ht N M)=0 := by
  let F : C(ActualEpisodeArray e,ℝ) := ⟨fun Y => g (arrayProfileTest e q.1 p z Y)*
      (arrayOffsetTest e p q z Y-arrayProfileTest e q.1 p z Y),
      (g.continuous.comp (arrayProfileTest e q.1 p z).continuous).mul
        ((arrayOffsetTest e p q z).continuous.sub (arrayProfileTest e q.1 p z).continuous)⟩
  change (∫ Y, F Y ∂actualOccupationRaw e ν Q t J ht N M)=_
  rw [actualOccupationRaw_integral e ν Q t J ht hJ N M hM F]
  apply Finset.sum_eq_zero
  intro i _
  simp only [F,ContinuousMap.coe_mk,arrayProfileTest_iterate,arrayOffsetTest_iterate]
  have hneq : (p.1+(i:ℤ),p.2)≠(q.1+(i:ℤ),q.2) := by
    intro he
    apply hpq
    apply Prod.ext
    · exact add_right_cancel (congrArg Prod.fst he)
    · have hh := congrArg (fun r : ℤ×ℕ => r.2) he
      exact hh
  exact actual_array_sampling_test_law e ν (Q.restrict {ω | i<M ω}) t J ht hJ
    (p.1+(i:ℤ),p.2) (q.1+(i:ℤ),q.2) hneq z g

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal BigOperators Classical Topology
namespace DirectionalTransience

lemma actualOccupation_integral {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (N : ℕ) (M : Environment d → ℕ)
    (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ)
    (F : ActualEpisodeArray e → ℝ) :
    (∫ Y, F Y ∂(actualOccupation e ν Q t J ht N M : Measure (ActualEpisodeArray e)))=
      ((actualOccupationRaw e ν Q t J ht N M).real Set.univ)⁻¹ *
        ∫ Y, F Y ∂actualOccupationRaw e ν Q t J ht N M := by
  have : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
  let ρ : FiniteMeasure (ActualEpisodeArray e) := ⟨actualOccupationRaw e ν Q t J ht N M,(by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  have hn : ρ≠0 := by
    intro hz
    have hh : (actualOccupationRaw e ν Q t J ht N M).real Set.univ=0 := by
      change (ρ : Measure (ActualEpisodeArray e)).real Set.univ=0
      rw [hz]
      simp
    linarith
  change (∫ Y, F Y ∂(ρ.normalize : Measure (ActualEpisodeArray e)))=_
  rw [←ρ.average_eq_integral_normalize hn,average,integral_smul_measure]
  simp only [ENNReal.toReal_inv,smul_eq_mul]
  rfl

lemma actualOccupation_sampling_sq {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (N : ℕ) (M : Environment d → ℕ) (hM : Measurable M)
    (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ)
    (p : ℤ×ℕ) (j : ℤ) (z : HorizontalSpace e) (n : ℕ) (hn : 0<n) :
    (∫ Y, (arraySamplingError e p j z n Y)^2
      ∂(actualOccupation e ν Q t J ht N M : Measure (ActualEpisodeArray e)))≤(n:ℝ)⁻¹ := by
  rw [actualOccupation_integral e ν Q t J ht N M hpos]
  have hb := actualOccupationRaw_sampling_sq e ν Q t J ht hJ N M hM p j z n hn
  exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hpos.le)).trans_eq
    (by rw [←mul_assoc,inv_mul_cancel₀ hpos.ne',one_mul])

lemma actualOccupation_sampling_test {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (N : ℕ) (M : Environment d → ℕ) (hM : Measurable M)
    (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ)
    (p q : ℤ×ℕ) (hpq : p≠q) (z : HorizontalSpace e) (g : C(ℝ,ℝ)) :
    (∫ Y, g (arrayProfileTest e q.1 p z Y)*
      (arrayOffsetTest e p q z Y-arrayProfileTest e q.1 p z Y)
      ∂(actualOccupation e ν Q t J ht N M : Measure (ActualEpisodeArray e)))=0 := by
  rw [actualOccupation_integral e ν Q t J ht N M hpos,
    actualOccupationRaw_sampling_test e ν Q t J ht hJ N M hM p q hpq z g,mul_zero]

section WeakLimit
variable {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : ℕ → Measure (Environment d)) [∀ r, IsFiniteMeasure (Q r)]
    (t J : ℕ → Environment d → ℤ → ℕ)
    (ht : ∀ r i, Measurable fun ω => t r ω i) (hJ : ∀ r i, Measurable fun ω => J r ω i)
    (N : ℕ → ℕ) (M : ℕ → Environment d → ℕ) (hM : ∀ r, Measurable (M r))
    (hpos : ∀ r, 0<(actualOccupationRaw e ν (Q r) (t r) (J r) (ht r) (N r) (M r)).real Set.univ)
    (L : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto (fun r => actualOccupation e ν (Q r) (t r) (J r) (ht r) (N r) (M r)) atTop (𝓝 L))

include hJ hM hpos hlim

theorem actualOccupation_limit_sampling (p : ℤ×ℕ) (j : ℤ) (z : HorizontalSpace e) :
    ∀ᵐ Y ∂(L : Measure (ActualEpisodeArray e)),
      Tendsto (fun n => arraySamplingError e p j z (2^n) Y) atTop (𝓝 0) := by
  apply Sampling.ae_sampling_of_weak_limit _ L hlim (fun n => arraySamplingError e p j z (2^n))
    (fun n => ((2:ℕ)^n:ℝ)⁻¹)
  · simpa only [Nat.cast_pow,Nat.cast_ofNat,inv_pow] using
      summable_geometric_of_norm_lt_one (x:=((2:ℝ)⁻¹)) (by norm_num)
  · intro r n
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using actualOccupation_sampling_sq e ν (Q r) (t r) (J r) (ht r) (hJ r) (N r) (M r)
      (hM r) (hpos r) p j z (2^n) (pow_pos (by norm_num) n)

theorem actualOccupation_limit_zero (p q : ℤ×ℕ) (hpq : p≠q) (z : HorizontalSpace e) :
    ∀ᵐ Y ∂(L : Measure (ActualEpisodeArray e)),
      arrayProfileTest e q.1 p z Y=0 → arrayOffsetTest e p q z Y=0 := by
  apply Sampling.ae_zero_of_sampling_tests (arrayProfileTest e q.1 p z) (arrayOffsetTest e p q z)
    (arrayProfileTest e q.1 p z).continuous.measurable (arrayOffsetTest e p q z).continuous.measurable
    (arrayProfileTest_mem e q.1 p z) (arrayOffsetTest_mem e p q z)
  apply Sampling.sampling_tests_weak_limit _ L hlim
  intro r g
  exact actualOccupation_sampling_test e ν (Q r) (t r) (J r) (ht r) (hJ r) (N r) (M r)
    (hM r) (hpos r) p q hpq z g

end WeakLimit
end DirectionalTransience

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

lemma episode_counts_le_loops {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r)
    (ω : Environment d) (test : EpisodeState (k:=k) e f r → Environment d → Prop) (n : ℕ) :
    episodeSteps e f hef r fexp g χ b sfloor N q ω n ≤ n ∧
    episodeCount e f hef r fexp g χ b sfloor N q ω test n ≤ n := by
  induction n with
  | zero => exact ⟨le_refl _,le_refl _⟩
  | succ n ih =>
    rw [episodeSteps,episodeCount]
    constructor <;> split <;> omega

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

lemma stepMark_sum (ω : Environment d) (n : ℕ) : ∑ i ∈ Finset.range n, j ω i=J ω n := by
  induction n with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,steps]
  | succ n ih => rw [Finset.sum_range_succ,ih,steps]; rfl

end DirectionalTransience.EpisodeChainLedger

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience.EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "j" => stepMark (k:=k) e f hef r fexp g χ b sfloor hR N

lemma stepMark_le (ω : Environment d) (i : ℕ) : j ω i ≤ N := by
  unfold stepMark
  split
  · exact (episode_counts_le_loops e f hef r fexp g χ b sfloor N _ ω
      (episodeStageFails e f r fexp g χ b N) N).1
  · exact Nat.zero_le _

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
local notation "M" => number (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "t" => arrayTime (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "s" => arrayStages (k:=k) e f hef r fexp g χ b sfloor hR N

lemma arrayStages_measurable (i : ℤ) : Measurable (fun ω => s ω i) := by
  unfold arrayStages
  split
  · exact measurable_const
  · exact stepMark_measurable (k:=k) e f hef r fexp g χ b sfloor hR N i.toNat

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

omit [IsProbabilityMeasure ν] in
lemma activeCount_measurable (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) : Measurable (C.activeCount hef N) :=
  EpisodeChainLedger.number_measurable (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N N

end OperationalConstants
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_ArrayMarkTests
attribute [-instance] _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma cutENNReal_nonneg (B : ℝ≥0) (x : ℝ≥0∞) : 0 ≤ cutENNReal B x := ENNReal.toReal_nonneg
lemma cutENNReal_le (B : ℝ≥0) (x : ℝ≥0∞) : cutENNReal B x ≤ B := by
  change (min x (B:ℝ≥0∞)).toReal ≤ (B:ℝ≥0∞).toReal
  exact ENNReal.toReal_mono ENNReal.coe_ne_top (min_le_right _ _)

lemma actualOccupationRaw_env_test {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (N : ℕ) (M : Environment d → ℕ) (hM : Measurable M)
    (F : C(ActualEpisodeArray e,ℝ)) (G : ℕ → Environment d → ℝ)
    (hG : ∀ i, Measurable (G i))
    (hFG : ∀ i X, F (StationaryCompact.shift^[i] (actualArrayMap e t J X))=G i X.1.1) :
    (∫ Y, F Y ∂actualOccupationRaw e ν Q t J ht N M)=
      ∑ i∈Finset.range N, ∫ ω in {ω | i<M ω}, G i ω ∂Q := by
  rw [actualOccupationRaw_integral e ν Q t J ht hJ N M hM F]
  apply Finset.sum_congr rfl
  intro i _
  simp only [hFG]
  exact episodeInputLaw_env_integral e ν (Q.restrict {ω | i<M ω}) t ht (G i) (hG i)

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_OperationalMarkBounds
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
variable {d : ℕ} {ν : Measure (Row d)}
  {e f : Direction d} {D : ℝ}

lemma stagesAt_measurable (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N i : ℕ) : Measurable (fun ω => C.stagesAt hef N ω i) :=
  EpisodeChainLedger.stepMark_measurable (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N i

lemma stagesAt_integrable (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N i : ℕ) (Q : Measure (Environment d)) [IsFiniteMeasure Q] :
    Integrable (fun ω => (C.stagesAt hef N ω i:ℝ)) Q := by
  apply Integrable.of_bound
    (((measurable_of_countable (fun n:ℕ => (n:ℝ))).comp (C.stagesAt_measurable hef N i)).aestronglyMeasurable) N
  filter_upwards [] with ω
  rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
  change (C.stagesAt hef N ω i:ℝ) ≤ (N:ℝ)
  apply Nat.cast_le.mpr
  exact EpisodeChainLedger.stepMark_le (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω i

lemma actual_stageMark (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N i : ℕ) (X : EpisodeInput e) :
    ((StationaryCompact.shift^[i] (actualArrayMap e (C.paddedTimes hef N)
      (C.paddedStages hef N) X)).1 0).2.1 = (C.stagesAt hef N X.1.1 i:ℕ∞) := by
  rw [arrayMark_iterate]
  simp only [zero_add,actualArrayMap,paddedStages,EpisodeChainLedger.arrayStages,
    Int.natCast_nonneg,not_lt.mpr,ite_false, if_false,Int.toNat_natCast,stagesAt]

lemma stageMarkCut_actual (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N i : ℕ) (B : ℝ≥0) (X : EpisodeInput e) :
    stageMarkCut e B 0 (StationaryCompact.shift^[i] (actualArrayMap e (C.paddedTimes hef N)
      (C.paddedStages hef N) X)) = min (C.stagesAt hef N X.1.1 i:ℝ) B := by
  change (min (((StationaryCompact.shift^[i] (actualArrayMap e (C.paddedTimes hef N)
      (C.paddedStages hef N) X)).1 0).2.1).toENNReal (B:ℝ≥0∞)).toReal = _
  rw [C.actual_stageMark]
  simp only [ENat.toENNReal_coe]
  rw [ENNReal.toReal_min (ENNReal.natCast_ne_top _) ENNReal.coe_ne_top]
  simp

variable [IsProbabilityMeasure ν]

lemma raw_stageMark_bound (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (Q : Measure (Environment d)) [IsFiniteMeasure Q] (B : ℝ≥0) :
    (∫ Y, stageMarkCut e B 0 Y ∂actualOccupationRaw e ν Q
      (C.paddedTimes hef N) (C.paddedStages hef N) (C.paddedTimes_measurable hef N)
      N (C.activeCount hef N)) ≤
      ∫ ω, (EpisodeChainLedger.steps (k:=C.k) e f hef (episodeScaleRadius ν e f)
        C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω N:ℝ) ∂Q := by
  rw [actualOccupationRaw_env_test e ν Q (C.paddedTimes hef N) (C.paddedStages hef N)
    (C.paddedTimes_measurable hef N) (C.paddedStages_measurable hef N) N (C.activeCount hef N)
    (C.activeCount_measurable hef N) (stageMarkCut e B 0)
    (fun i ω => min (C.stagesAt hef N ω i:ℝ) B)
    (fun i => (((measurable_of_countable (fun n:ℕ => (n:ℝ))).comp (C.stagesAt_measurable hef N i)).min measurable_const))
    (fun i X => C.stageMarkCut_actual hef N i B X)]
  have hsum : (∫ ω, (EpisodeChainLedger.steps (k:=C.k) e f hef (episodeScaleRadius ν e f)
        C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω N:ℝ) ∂Q) =
      ∑ i∈Finset.range N, ∫ ω, (C.stagesAt hef N ω i:ℝ) ∂Q := by
    rw [←integral_finsetSum (Finset.range N) (fun i _ => C.stagesAt_integrable hef N i Q)]
    apply integral_congr_ae
    filter_upwards [] with ω
    dsimp only [stagesAt]
    exact_mod_cast (EpisodeChainLedger.stepMark_sum (k:=C.k) e f hef (episodeScaleRadius ν e f)
      C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω N).symm
  rw [hsum]
  apply Finset.sum_le_sum
  intro i _
  apply (integral_mono ((C.stagesAt_integrable hef N i Q).inf (integrable_const _)).integrableOn
    (C.stagesAt_integrable hef N i Q).integrableOn (fun _ => min_le_left _ _)).trans
  exact setIntegral_le_integral (C.stagesAt_integrable hef N i Q)
    (Filter.Eventually.of_forall (fun _ => Nat.cast_nonneg _))

end OperationalConstants
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_RawDropBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma mark_lintegral_bound_of_weak_limit
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hlim : Tendsto μs atTop (𝓝 μ)) (F : C(X,ℝ≥0∞)) (A : ℝ)
    (hbound : ∀ n (B : ℝ≥0), ∫ x, cutENNReal B (F x) ∂(μs n : Measure X) ≤ A) :
    (∫⁻ x, F x ∂(μ : Measure X)) ≤ ENNReal.ofReal A := by
  have hcut (B : ℝ≥0) : ∫ x, cutENNReal B (F x) ∂(μ : Measure X) ≤ A := by
    let G : C(X,ℝ) := (cutENNReal B).comp F
    exact le_of_tendsto ((ProbabilityMeasure.continuous_integral_continuousMap G).continuousAt.tendsto.comp hlim)
      (Filter.Eventually.of_forall (fun n => hbound n B))
  have hcut' (n : ℕ) : (∫⁻ x, min (F x) (n:ℝ≥0∞) ∂(μ : Measure X)) ≤ ENNReal.ofReal A := by
    let G : C(X,ℝ) := (cutENNReal (n:ℝ≥0)).comp F
    have hG : Integrable G (μ : Measure X) :=
      G.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hn := ENNReal.ofReal_le_ofReal (hcut n)
    change ENNReal.ofReal (∫ x, G x ∂(μ : Measure X)) ≤ ENNReal.ofReal A at hn
    rw [ofReal_integral_eq_lintegral_ofReal hG (Filter.Eventually.of_forall (fun x => cutENNReal_nonneg _ _))] at hn
    convert hn using 1
    all_goals try with_reducible_and_instances rfl
    apply lintegral_congr
    intro x
    change min (F x) (n:ℝ≥0∞) = ENNReal.ofReal ((min (F x) ((n:ℝ≥0):ℝ≥0∞)).toReal)
    rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))]
    simp
  have he (x : X) : (⨆ n : ℕ, min (F x) (n:ℝ≥0∞))=F x := by
    rw [←inf_iSup_eq,ENNReal.iSup_natCast,inf_top_eq]
  rw [show (fun x => F x)=(fun x => ⨆ n : ℕ, min (F x) (n:ℝ≥0∞)) from funext (fun x => (he x).symm)]
  rw [lintegral_iSup (fun n => F.continuous.measurable.min measurable_const)
    (fun n m h x => min_le_min_left _ (by exact_mod_cast h))]
  exact iSup_le hcut'

lemma mark_integrable_of_lintegral_bound
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : X → ℝ≥0∞) (hF : Measurable F) (A : ℝ)
    (hbound : (∫⁻ x, F x ∂μ) ≤ ENNReal.ofReal A) :
    (∀ᵐ x ∂μ, F x<∞) ∧ Integrable (fun x => (F x).toReal) μ := by
  have hfin : (∫⁻ x, F x ∂μ)<∞ := hbound.trans_lt ENNReal.ofReal_lt_top
  exact ⟨ae_lt_top' hF.aemeasurable hfin.ne,
    integrable_toReal_of_lintegral_ne_top hF.aemeasurable hfin.ne⟩

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

theorem bad_array_sampling_limit (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (hD : 0≤D) (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop)
    (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hlarge : ∀ n, 32*C.b ≤ (1/2:ℝ)*Real.log (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2))) :
    ∃ ρ : ProbabilityMeasure (ActualEpisodeArray e), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      Tendsto (fun n => C.occupation hef (Ns (φ n))
        ((environmentLaw ν)[|badCrossingEvent e (Ns (φ n)) (1/2)])) atTop (𝓝 ρ) ∧
      MeasurePreserving StationaryCompact.shift (ρ : Measure (ActualEpisodeArray e))
        (ρ : Measure (ActualEpisodeArray e)) ∧
      (∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), ∀ p j z,
        Tendsto (fun n => arraySamplingError e p j z (2^n) Y) atTop (𝓝 0)) ∧
      (∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), ∀ p q z, p≠q →
        arrayProfileTest e q.1 p z Y=0 → arrayOffsetTest e p q z Y=0) := by
  obtain ⟨ρ,φ,hφ,hlim,hstat⟩ := C.bad_occupation_stationary_limit hef hD Ns hNs hN hlarge hmass
  refine ⟨ρ,φ,hφ,hlim,hstat,?_,?_⟩
  · apply ae_all_iff.mpr
    intro p
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro z
    exact actualOccupation_limit_sampling e ν
      (fun n => (environmentLaw ν)[|badCrossingEvent e (Ns (φ n)) (1/2)])
      (fun n => C.paddedTimes hef (Ns (φ n))) (fun n => C.paddedStages hef (Ns (φ n)))
      (fun n => C.paddedTimes_measurable hef (Ns (φ n)))
      (fun n => C.paddedStages_measurable hef (Ns (φ n)))
      (fun n => Ns (φ n)) (fun n => C.activeCount hef (Ns (φ n)))
      (fun n => C.activeCount_measurable hef (Ns (φ n)))
      (fun n => C.bad_raw_mass_pos hef (Ns (φ n)) (hN (φ n)) (hmass (φ n))) ρ hlim p j z
  · apply ae_all_iff.mpr
    intro p
    apply ae_all_iff.mpr
    intro q
    apply ae_all_iff.mpr
    intro z
    by_cases hpq : p=q
    · exact Filter.Eventually.of_forall (fun _ h => (h hpq).elim)
    · exact (actualOccupation_limit_zero e ν
        (fun n => (environmentLaw ν)[|badCrossingEvent e (Ns (φ n)) (1/2)])
        (fun n => C.paddedTimes hef (Ns (φ n))) (fun n => C.paddedStages hef (Ns (φ n)))
        (fun n => C.paddedTimes_measurable hef (Ns (φ n)))
        (fun n => C.paddedStages_measurable hef (Ns (φ n)))
        (fun n => Ns (φ n)) (fun n => C.activeCount hef (Ns (φ n)))
        (fun n => C.activeCount_measurable hef (Ns (φ n)))
        (fun n => C.bad_raw_mass_pos hef (Ns (φ n)) (hN (φ n)) (hmass (φ n))) ρ hlim p q hpq z).mono
        (fun _ h _ => h)

end OperationalConstants
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_BadStageMoment
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
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

lemma bad_stageMark_bound (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (hD : 0≤D) (N : ℕ) (hN : C.sfloor ≤ (N:ℝ))
    (hlarge : 32*C.b ≤ (1/2:ℝ)*Real.log (N:ℝ))
    (hmass : (N:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e N (1/2)))
    (B : ℝ≥0) :
    (∫ Y, stageMarkCut e B 0 Y ∂(C.occupation hef N
      ((environmentLaw ν)[|badCrossingEvent e N (1/2)]) : Measure (ActualEpisodeArray e))) ≤
      C.injectionCost/(6*C.b) := by
  let Q := (environmentLaw ν)[|badCrossingEvent e N (1/2)]
  have hN0 : 0<N := by exact_mod_cast lt_of_lt_of_le zero_lt_one (C.hs.trans hN)
  have : IsProbabilityMeasure Q := cond_isProbabilityMeasure
    (badCrossingEvent_pos e N (1/2) D (environmentLaw ν) hN0 hmass)
  let M : ℝ := ∫ ω, (C.activeCount hef N ω:ℝ) ∂Q
  let J : ℝ := ∫ ω, (EpisodeChainLedger.steps (k:=C.k) e f hef (episodeScaleRadius ν e f)
        C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω N:ℝ) ∂Q
  have hM : 0<M := EpisodeChainLedger.operational_mass_positive (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N Q hN0
  have he := EpisodeChainLedger.operational_raw_mass (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ν Q
  have hkl := badCrossing_cond_entropy e N (1/2) D (environmentLaw ν) hN0 hmass
  have hj := actual_expected_stages (k:=C.k) ν e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.K D (1/2) C.radius_nonneg N C.hs hN
    C.hf.le C.hg C.hb C.hK hD C.height C.stages Q hkl C.coeff C.small hlarge
  change 2*C.b*J ≤ (1/2:ℝ)/4*Real.log (N:ℝ) at hj
  obtain ⟨L,hL,hcharge⟩ := C.finite_charge
  have hm := (C.conditional_episode_drops hef hD N hN hlarge hmass L hL hcharge).1
  change 3/8*Real.log (N:ℝ) ≤ C.injectionCost*M at hm
  have hJM : 6*C.b*J ≤ C.injectionCost*M := by nlinarith only [hj,hm]
  have hraw := C.raw_stageMark_bound hef N Q B
  have hmean : M⁻¹*J ≤ C.injectionCost/(6*C.b) := by
    apply (le_div_iff₀ (show 0<6*C.b by nlinarith [C.hb])).mpr
    have hh := mul_le_mul_of_nonneg_left hJM (inv_nonneg.mpr hM.le)
    have hid : M⁻¹*(C.injectionCost*M)=C.injectionCost := by field_simp
    rw [hid] at hh
    nlinarith only [hh]
  change (∫ Y, stageMarkCut e B 0 Y ∂(actualOccupation e ν Q
    (C.paddedTimes hef N) (C.paddedStages hef N) (C.paddedTimes_measurable hef N)
    N (C.activeCount hef N) : Measure (ActualEpisodeArray e))) ≤ _
  rw [actualOccupation_integral e ν Q _ _ _ _ _ (C.bad_raw_mass_pos hef N hN hmass)]
  have he' : (actualOccupationRaw e ν Q (C.paddedTimes hef N) (C.paddedStages hef N)
    (C.paddedTimes_measurable hef N) N (C.activeCount hef N)).real Set.univ=M := he
  rw [he']
  exact (mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hM.le)).trans hmean

lemma bad_limit_finite_stages (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (hD : 0≤D) (Ns : ℕ → ℕ)
    (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hlarge : ∀ n, 32*C.b ≤ (1/2:ℝ)*Real.log (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2)))
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto (fun n => C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)])) atTop (𝓝 ρ)) :
    (∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), (Y.1 0).2.1<⊤) ∧
      Integrable (fun Y => ((Y.1 0).2.1).toENNReal.toReal) (ρ : Measure (ActualEpisodeArray e)) := by
  let F : C(ActualEpisodeArray e,ℝ≥0∞) := ⟨fun Y => ((Y.1 0).2.1).toENNReal,
    ENat.continuous_toENNReal.comp (by fun_prop)⟩
  have hh := mark_lintegral_bound_of_weak_limit _ ρ hlim F (C.injectionCost/(6*C.b))
    (fun n B => C.bad_stageMark_bound hef hD (Ns n) (hN n) (hlarge n) (hmass n) B)
  have hf := mark_integrable_of_lintegral_bound (ρ : Measure (ActualEpisodeArray e)) F
    F.continuous.measurable _ hh
  refine ⟨hf.1.mono (fun Y h => ?_),hf.2⟩
  change ((Y.1 0).2.1).toENNReal<∞ at h
  simpa using h

end OperationalConstants
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_OperationalLengthMarks
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
variable {d : ℕ} {ν : Measure (Row d)}
  {e f : Direction d} {D : ℝ}

lemma actual_lengthMark (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N i : ℕ) (X : EpisodeInput e) :
    ((StationaryCompact.shift^[i] (actualArrayMap e (C.paddedTimes hef N)
      (C.paddedStages hef N) X)).1 0).1 =
      ((episodeBoundary (k:=C.k) e f hef (episodeScaleRadius ν e f) C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N X.1.1 (i+1)-
        episodeBoundary (k:=C.k) e f hef (episodeScaleRadius ν e f) C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N X.1.1 i:ℕ):ℕ∞) := by
  rw [arrayMark_iterate]
  simp only [zero_add,actualArrayMap,paddedTimes,EpisodeChainLedger.arrayTime,Int.toNat_natCast,
    show (i:ℤ)+1=((i+1:ℕ):ℤ) by omega]

end OperationalConstants
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Renewal_PositiveLengthMark
attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_standardBorel
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

lemma raw_lengthUnit (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N : ℕ) (Q : Measure (Environment d)) [IsFiniteMeasure Q] :
    (∫ Y, lengthUnitTest e Y ∂actualOccupationRaw e ν Q
      (C.paddedTimes hef N) (C.paddedStages hef N) (C.paddedTimes_measurable hef N) N (C.activeCount hef N)) =
    (actualOccupationRaw e ν Q (C.paddedTimes hef N) (C.paddedStages hef N)
      (C.paddedTimes_measurable hef N) N (C.activeCount hef N)).real Set.univ := by
  let T := episodeBoundary (k:=C.k) e f hef (episodeScaleRadius ν e f)
    C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N
  have hm (i : ℕ) : Measurable (fun ω => (min (T ω (i+1)-T ω i) 1:ℕ)) :=
    ((episodeBoundary_measurable (k:=C.k) e f hef (episodeScaleRadius ν e f)
      C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N (i+1)).sub
      (episodeBoundary_measurable (k:=C.k) e f hef (episodeScaleRadius ν e f)
      C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N i)).min measurable_const
  rw [actualOccupationRaw_env_test e ν Q _ _ _ (C.paddedStages_measurable hef N) N _
    (C.activeCount_measurable hef N) (lengthUnitTest e)
    (fun i ω => (min (T ω (i+1)-T ω i) 1:ℕ))
    (fun i => (measurable_of_countable (fun n:ℕ => (n:ℝ))).comp (hm i))
    (fun i X => by
      change (min (((StationaryCompact.shift^[i] (actualArrayMap e (C.paddedTimes hef N)
        (C.paddedStages hef N) X)).1 0).1).toENNReal (1:ℝ≥0∞)).toReal = _
      rw [C.actual_lengthMark]
      change (min ((T X.1.1 (i+1)-T X.1.1 i:ℕ):ℝ≥0∞) 1).toReal = _
      generalize T X.1.1 (i+1)-T X.1.1 i = n
      simp only [ENNReal.toReal_min (ENNReal.natCast_ne_top _) ENNReal.one_ne_top,
        ENNReal.toReal_natCast,ENNReal.toReal_one,Nat.cast_min,Nat.cast_one]),
    actualOccupationRaw_mass e ν Q _ _ _ (C.paddedStages_measurable hef N) N _ (C.activeCount_measurable hef N)]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∫ ω in {ω | i<C.activeCount hef N ω}, ((min (T ω (i+1)-T ω i) 1:ℕ):ℝ) ∂Q) =
      ∫ ω in {ω | i<C.activeCount hef N ω}, (1:ℝ) ∂Q := by
      apply setIntegral_congr_fun (measurableSet_lt measurable_const (C.activeCount_measurable hef N))
      intro ω hω
      have ha : T ω i<N := (EpisodeChainLedger.active_iff_lt_number (k:=C.k) e f hef (episodeScaleRadius ν e f)
        C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N ω i).mpr hω
      have hh := episodeFinal_gt (k:=C.k) e f hef (episodeScaleRadius ν e f)
        C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N (T ω i) ω
      have hp : T ω i<T ω (i+1) := by
        change T ω i < if T ω i<N then _ else _
        rw [ite_eq_left ha]
        exact hh
      have hmin : min (T ω (i+1)-T ω i) 1=1 := by omega
      simp only [hmin,Nat.cast_one]
    _ = _ := by simp

lemma bad_limit_positive_length (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (Ns : ℕ → ℕ) (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2)))
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto (fun n => C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)])) atTop (𝓝 ρ)) :
    ∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), 0<(Y.1 0).1 := by
  have he (n : ℕ) : (∫ Y, lengthUnitTest e Y ∂(C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)]):Measure (ActualEpisodeArray e)))=1 := by
    change (∫ Y, lengthUnitTest e Y ∂(actualOccupation e ν _ _ _ _ _ _:Measure _))=1
    rw [actualOccupation_integral e ν _ _ _ _ _ _ (C.bad_raw_mass_pos hef (Ns n) (hN n) (hmass n)),C.raw_lengthUnit]
    exact inv_mul_cancel₀ (ne_of_gt (C.bad_raw_mass_pos hef (Ns n) (hN n) (hmass n)))
  have hconv := (ProbabilityMeasure.continuous_integral_continuousMap (lengthUnitTest e)).continuousAt.tendsto.comp hlim
  have hl : Tendsto (fun n => ∫ Y, lengthUnitTest e Y ∂(C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)]):Measure (ActualEpisodeArray e))) atTop (𝓝 (1:ℝ)) := by
    simp_rw [he]
    exact tendsto_const_nhds
  have hi : (∫ Y, lengthUnitTest e Y ∂(ρ:Measure (ActualEpisodeArray e)))=1 :=
    tendsto_nhds_unique hconv hl
  have hz : (∫ Y, 1-lengthUnitTest e Y ∂(ρ:Measure (ActualEpisodeArray e)))=0 := by
    rw [integral_sub (integrable_const _)
      ((lengthUnitTest e).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
      integral_const,probReal_univ,one_smul,hi,sub_self]
  have hnon (Y : ActualEpisodeArray e) : 0≤1-lengthUnitTest e Y := by
    exact sub_nonneg.mpr (cutENNReal_le 1 _)
  have hae := (integral_eq_zero_iff_of_nonneg hnon
    ((1-lengthUnitTest e).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp hz
  filter_upwards [hae] with Y hY
  by_contra hh
  have hh : (Y.1 0).1=0 := le_antisymm (le_of_not_gt hh) bot_le
  have htest : lengthUnitTest e Y=0 := by simp [lengthUnitTest,cutENNReal,hh]
  rw [htest] at hY
  norm_num at hY

end OperationalConstants
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_BadFiniteArray
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

lemma logLengthMark_real {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (hf : (Y.1 0).1<⊤) :
    (logLengthMark e Y).toReal = Real.log (1+((Y.1 0).1.toNat:ℝ)) := by
  have he := ENat.natCast_toNat hf.ne
  change (ENNReal.log (1+(Y.1 0).1.toENNReal)).toENNReal.toReal=_
  generalize (Y.1 0).1.toNat=n at he ⊢
  rw [←he,ENat.toENNReal_coe]
  rw [ENNReal.log_pos_real (by positivity) (by finiteness),EReal.real_coe_toENNReal,
    ENNReal.toReal_add ENNReal.one_ne_top (ENNReal.natCast_ne_top n)]
  simp only [ENNReal.toReal_one,ENNReal.toReal_natCast]
  rw [ENNReal.toReal_ofReal (Real.log_nonneg (le_add_of_nonneg_right (Nat.cast_nonneg n)))]

namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

theorem bad_array_finite_marks_oai (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (hD : 0≤D) (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop)
    (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hlarge : ∀ n, 32*C.b ≤ (1/2:ℝ)*Real.log (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2))) :
    ∃ ρ : ProbabilityMeasure (ActualEpisodeArray e), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      Tendsto (fun n => C.occupation hef (Ns (φ n))
        ((environmentLaw ν)[|badCrossingEvent e (Ns (φ n)) (1/2)])) atTop (𝓝 ρ) ∧
      MeasurePreserving StationaryCompact.shift (ρ : Measure (ActualEpisodeArray e))
        (ρ : Measure (ActualEpisodeArray e)) ∧
      (∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), ∀ p j z,
        Tendsto (fun n => arraySamplingError e p j z (2^n) Y) atTop (𝓝 0)) ∧
      (∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), ∀ p q z, p≠q →
        arrayProfileTest e q.1 p z Y=0 → arrayOffsetTest e p q z Y=0) ∧
      (∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)),
        0<(Y.1 0).1 ∧ (Y.1 0).1<⊤ ∧ (Y.1 0).2.1<⊤ ∧ (Y.1 0).2.2<∞) ∧
      Integrable (fun Y => ((Y.1 0).2.1).toENNReal.toReal) (ρ : Measure (ActualEpisodeArray e)) ∧
      Integrable (fun Y => Real.log (1+((Y.1 0).1.toNat:ℝ))) (ρ : Measure (ActualEpisodeArray e)) ∧
      Integrable (fun Y => (Y.1 0).2.2.toReal) (ρ : Measure (ActualEpisodeArray e)) ∧
      C.b ≤ ∫ Y, (Y.1 0).2.2.toReal ∂(ρ : Measure (ActualEpisodeArray e)) := by
  obtain ⟨ρ,φ,hφ,hlim,hstat,hsample,hzero⟩ := C.bad_array_sampling_limit hef hD Ns hNs hN hlarge hmass
  have hJ := C.bad_limit_finite_stages hef hD (fun n => Ns (φ n)) (fun n => hN (φ n))
    (fun n => hlarge (φ n)) (fun n => hmass (φ n)) ρ hlim
  have hc := C.bad_limit_drop_moment hef hD (fun n => Ns (φ n)) (fun n => hN (φ n))
    (fun n => hlarge (φ n)) (fun n => hmass (φ n)) ρ hlim
  have hh := C.bad_limit_length_moment hef hD (fun n => Ns (φ n)) (fun n => hN (φ n))
    (fun n => hlarge (φ n)) (fun n => hmass (φ n)) ρ hlim
  have hpos := C.bad_limit_positive_length hef (fun n => Ns (φ n)) (fun n => hN (φ n))
    (fun n => hmass (φ n)) ρ hlim
  refine ⟨ρ,φ,hφ,hlim,hstat,hsample,hzero,?_,hJ.2,?_,hc.2.1,hc.2.2⟩
  · filter_upwards [hpos,hh.1,hJ.1,hc.1] with Y ha hb hj hk
    exact ⟨ha,hb,hj,hk⟩
  · exact hh.2.congr (hh.1.mono (fun Y hY => logLengthMark_real e Y hY))

end OperationalConstants
end DirectionalTransience

end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.OperationalConstants.bad_array_finite_marks_oai := @OAI.DirectionalTransience.OperationalConstants.bad_array_finite_marks_oai
