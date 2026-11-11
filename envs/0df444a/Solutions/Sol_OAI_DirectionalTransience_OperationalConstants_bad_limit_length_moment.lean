-- Prove2me | solution 1 for OAI.DirectionalTransience.OperationalConstants.bad_limit_length_moment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:55:18.124208+00:00
-- url     : https://prove2.me/submissions/489c78e9-3c17-44b5-9751-88a38a6efec7

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal005
import Definitions.Def_OAIQ242Bal006
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
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_StageRetention
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical
namespace DirectionalTransience

lemma stageStop_le {d k : ℕ} (e f : Direction d) (a Gminus Gplus B : ℝ)
    (π : Environment d → LayerTupleProfile (k:=k) e a) (H R : ℕ) (ω : Environment d) :
    stageStop e f a Gminus Gplus B π H R ω  ≤  min H R := hittingBtwn_le ω

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

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeLength
attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma episodeStageScale_pos {d k : ℕ} (e f : Direction d) (r : ℝ → ℝ)
    (fexp g χ b : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) (ω : Environment d) (hs : 0 < q.scale) :
    0 < episodeStageScale e f r fexp g χ b N q ω := by
  unfold episodeStageScale
  split <;> positivity

lemma episodeStageScale_le {d k : ℕ} (e f : Direction d) (r : ℝ → ℝ)
    (fexp g χ b : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) (ω : Environment d)
    (hf : 0 ≤ fexp) (hg : 0 ≤ g) (hb : 0 ≤ b) (hs : 0 ≤ q.scale) :
    episodeStageScale e f r fexp g χ b N q ω ≤ q.scale*Real.exp (g*b) := by
  unfold episodeStageScale
  split
  · exact le_rfl
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hs

lemma episodeStageLength_le {d k : ℕ} (e f : Direction d) (r : ℝ → ℝ)
    (fexp g χ b : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r) (ω : Environment d) (hs : 0 ≤ q.scale) :
    (episodeStageLength e f r fexp g χ b N q ω : ℝ) ≤ q.scale*Real.exp (χ*b) := by
  have hh := (stageStop_le e f q.height (r (q.scale*Real.exp (-fexp*b)))
    (r (q.scale*Real.exp (g*b))) ((k:ℝ)*b) (fun _ => q.profile.toLayerProfile)
    (episodeStageH χ b q.scale) (N-q.height) ω).trans (min_le_left _ _)
  exact (show (episodeStageLength e f r fexp g χ b N q ω : ℝ) ≤ (episodeStageH χ b q.scale : ℝ) by exact_mod_cast hh).trans
    (Nat.floor_le (mul_nonneg hs (Real.exp_pos _).le))

lemma episodeRun_length_scale {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d)
    (hf : 0 ≤ fexp) (hg : 0 ≤ g) (hb : 0 ≤ b) (hq : 0 < q.scale) (n : ℕ) :
    let p := episodeRun e f hef r fexp g χ b sfloor N q ω n
    let J := episodeSteps e f hef r fexp g χ b sfloor N q ω n
    0 < p.scale ∧ p.scale ≤ q.scale*Real.exp (g*b)^J ∧
      (p.height:ℝ) ≤ (q.height:ℝ)+(J:ℝ)*q.scale*Real.exp (g*b)^J*Real.exp (χ*b) := by
  induction n with
  | zero => simpa only [episodeRun,episodeSteps,pow_zero,mul_one,Nat.cast_zero,zero_mul,add_zero] using ⟨hq,le_rfl,le_rfl⟩
  | succ n ih =>
    dsimp only at ih ⊢
    rw [episodeRun,episodeSteps]
    by_cases hr : EpisodeReady e f r sfloor N (episodeRun e f hef r fexp g χ b sfloor N q ω n)
    · rw [ite_eq_left hr,ite_eq_left hr]
      let p := episodeRun e f hef r fexp g χ b sfloor N q ω n
      let J := episodeSteps e f hef r fexp g χ b sfloor N q ω n
      have hE : 1 ≤ Real.exp (g*b) := Real.one_le_exp_iff.mpr (mul_nonneg hg hb)
      have hpow : Real.exp (g*b)^J ≤ Real.exp (g*b)^(J+1) := by
        rw [pow_succ]
        exact le_mul_of_one_le_right (by positivity) hE
      refine ⟨episodeStageScale_pos e f r fexp g χ b N p ω ih.1,?_,?_⟩
      · change episodeStageScale e f r fexp g χ b N p ω ≤ _
        calc
          _ ≤ p.scale*Real.exp (g*b) := episodeStageScale_le e f r fexp g χ b N p ω hf hg hb ih.1.le
          _ ≤ (q.scale*Real.exp (g*b)^J)*Real.exp (g*b) := mul_le_mul_of_nonneg_right ih.2.1 (Real.exp_pos _).le
          _ = q.scale*Real.exp (g*b)^(J+1) := by rw [pow_succ,mul_assoc]
      · rw [episodeStageNext_height,Nat.cast_add]
        have hl := episodeStageLength_le e f r fexp g χ b N p ω ih.1.le
        have hlq := mul_le_mul_of_nonneg_right ih.2.1 (Real.exp_pos (χ*b)).le
        have hunit : (p.height:ℝ)+(episodeStageLength e f r fexp g χ b N p ω : ℝ) ≤
            (q.height:ℝ)+((J:ℝ)+1)*q.scale*Real.exp (g*b)^J*Real.exp (χ*b) := by
          dsimp only [p,J] at hl hlq ⊢
          nlinarith [ih.2.2]
        apply hunit.trans
        rw [Nat.cast_add,Nat.cast_one]
        exact add_le_add_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ ((J:ℝ)+1)*q.scale))
          (Real.exp_pos _).le) _
    · simpa only [ite_eq_right hr,add_zero] using ih

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

end OperationalConstants
end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Stationary_EpisodeLogLength
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

private lemma episode_log_geometric_bound (A B h : ℝ) (J : ℕ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hh : 0 ≤ h)
    (hbound : h ≤ (J:ℝ)*A*Real.exp B^J) :
    Real.log (1+h) ≤ (Real.log (1+A)+1+B)*(1+(J:ℝ)) := by
  have hJ : (J:ℝ) ≤ Real.exp (J:ℝ) := by linarith [Real.add_one_le_exp (J:ℝ)]
  have hE : 1 ≤ Real.exp ((1+B)*(J:ℝ)) := Real.one_le_exp_iff.mpr (by positivity)
  have hprod : Real.exp (J:ℝ)*Real.exp B^J = Real.exp ((1+B)*(J:ℝ)) := by
    rw [←Real.exp_nat_mul,←Real.exp_add]
    congr 1
    ring
  have hmul := mul_le_mul_of_nonneg_right hJ (mul_nonneg hA (by positivity : 0 ≤ Real.exp B^J))
  have hl : 1+h ≤ (1+A)*Real.exp ((1+B)*(J:ℝ)) := by
    have he : Real.exp (J:ℝ)*(A*Real.exp B^J) = A*Real.exp ((1+B)*(J:ℝ)) := by
      rw [←hprod]
      ring
    rw [he] at hmul
    nlinarith
  have hlog := Real.log_le_log (by positivity : 0 < 1+h) hl
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne',Real.log_exp] at hlog
  have hlogA : 0 ≤ Real.log (1+A) := Real.log_nonneg (by linarith)
  have hjA := mul_nonneg hlogA (Nat.cast_nonneg J : (0:ℝ) ≤ J)
  nlinarith

lemma episodeRun_logLength {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d)
    (hf : 0 ≤ fexp) (hg : 0 ≤ g) (hb : 0 ≤ b) (hq : 0 < q.scale) (n : ℕ) :
    let p := episodeRun e f hef r fexp g χ b sfloor N q ω n
    let J := episodeSteps e f hef r fexp g χ b sfloor N q ω n
    Real.log (1+(p.height-q.height:ℕ)) ≤
      (Real.log (1+q.scale*Real.exp (χ*b))+1+g*b)*(1+(J:ℝ)) := by
  dsimp only
  have hlen := (episodeRun_length_scale e f hef r fexp g χ b sfloor N q ω hf hg hb hq n).2.2
  have hmono := episodeRun_height_mono e f hef r fexp g χ b sfloor N q ω n
  apply episode_log_geometric_bound (q.scale*Real.exp (χ*b)) (g*b) _ _
    (by positivity) (mul_nonneg hg hb) (Nat.cast_nonneg _)
  rw [Nat.cast_sub hmono]
  nlinarith [hlen]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

theorem episode_log_length_bound {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N t : ℕ)
    (ω : Environment d) (hf : 0 ≤ fexp) (hg : 0 ≤ g) (hb : 0 ≤ b) (hs : 0 < sfloor) :
    Real.log (1+((episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω).height-t:ℕ)) ≤
      (Real.log 2+Real.log (1+sfloor*Real.exp (χ*b))+1+g*b)*
        (1+(episodeStageCount (k:=k) e f hef r fexp g χ b sfloor hR N t ω : ℝ)) := by
  let q := episodeInitial (k:=k) e f hef r sfloor hR t ω
  let p := episodeRun e f hef r fexp g χ b sfloor N q ω N
  let J := episodeSteps e f hef r fexp g χ b sfloor N q ω N
  have h := episodeRun_logLength e f hef r fexp g χ b sfloor N q ω hf hg hb hs N
  have hm := episodeRun_height_mono e f hef r fexp g χ b sfloor N q ω N
  have hqt : q.height=t+1 := rfl
  have he : p.height-t=(p.height-q.height)+1 := by dsimp only [p] at ⊢; omega
  change Real.log (1+(p.height-t:ℕ)) ≤ _
  rw [he,Nat.cast_add,Nat.cast_one]
  have hl := Real.log_le_log (by positivity : 0 < 1+((p.height-q.height:ℕ):ℝ)+1)
    (show 1+((p.height-q.height:ℕ):ℝ)+1 ≤ 2*(1+((p.height-q.height:ℕ):ℝ)) by nlinarith [(show (0:ℝ) ≤ (p.height-q.height:ℕ) from Nat.cast_nonneg _)])
  rw [Real.log_mul (by norm_num) (by positivity)] at hl
  have htwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hjtwo := mul_nonneg htwo (Nat.cast_nonneg J : (0:ℝ) ≤ J)
  change Real.log (1+((p.height-q.height:ℕ):ℝ)) ≤
    (Real.log (1+sfloor*Real.exp (χ*b))+1+g*b)*(1+(J:ℝ)) at h
  change Real.log (1+(((p.height-q.height:ℕ):ℝ)+1)) ≤
    (Real.log 2+Real.log (1+sfloor*Real.exp (χ*b))+1+g*b)*(1+(J:ℝ))
  rw [add_assoc] at hl
  nlinarith

end DirectionalTransience

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_OperationalLengthMarks
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

lemma raw_actual_test_mono {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (N : ℕ) (M : Environment d → ℕ) (hM : Measurable M)
    (F G : C(ActualEpisodeArray e,ℝ))
    (hFG : ∀ i X, F (StationaryCompact.shift^[i] (actualArrayMap e t J X)) ≤
      G (StationaryCompact.shift^[i] (actualArrayMap e t J X))) :
    (∫ Y, F Y ∂actualOccupationRaw e ν Q t J ht N M) ≤
      ∫ Y, G Y ∂actualOccupationRaw e ν Q t J ht N M := by
  rw [actualOccupationRaw_integral e ν Q t J ht hJ N M hM F,
    actualOccupationRaw_integral e ν Q t J ht hJ N M hM G]
  apply Finset.sum_le_sum
  intro i _
  have hm : Measurable (fun X => StationaryCompact.shift^[i] (actualArrayMap e t J X)) :=
    (StationaryCompact.shift_continuous.measurable.iterate i).comp (actualArrayMap_measurable e t J ht hJ)
  apply integral_mono
    ((F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).comp_measurable hm)
    ((G.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).comp_measurable hm)
  exact hFG i

namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)}
  {e f : Direction d} {D : ℝ}

lemma lengthCost_nonneg (C : OperationalConstants ν e f D) : 0≤C.lengthCost := by
  have hs : 0≤C.sfloor := le_trans (by norm_num) C.hs
  have hl := Real.log_nonneg (show 1≤1+C.sfloor*Real.exp (C.χ*C.b) by linarith [mul_nonneg hs (Real.exp_pos (C.χ*C.b)).le])
  have ht := Real.log_nonneg (by norm_num : (1:ℝ)≤2)
  have hg := mul_nonneg C.hg.le C.hb.le
  unfold lengthCost
  linarith

lemma actual_lengthMark (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N i : ℕ) (X : EpisodeInput e) :
    ((StationaryCompact.shift^[i] (actualArrayMap e (C.paddedTimes hef N)
      (C.paddedStages hef N) X)).1 0).1 =
      ((episodeBoundary (k:=C.k) e f hef (episodeScaleRadius ν e f) C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N X.1.1 (i+1)-
        episodeBoundary (k:=C.k) e f hef (episodeScaleRadius ν e f) C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N X.1.1 i:ℕ):ℕ∞) := by
  rw [arrayMark_iterate]
  simp only [zero_add,actualArrayMap,paddedTimes,EpisodeChainLedger.arrayTime,Int.toNat_natCast,
    show (i:ℤ)+1=((i+1:ℕ):ℤ) by omega]

lemma logLengthCut_actual_le (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (N i : ℕ) (B : ℝ≥0) (X : EpisodeInput e) :
    logLengthCut e B (StationaryCompact.shift^[i] (actualArrayMap e (C.paddedTimes hef N)
      (C.paddedStages hef N) X)) ≤ C.lengthCost*(1+(C.stagesAt hef N X.1.1 i:ℝ)) := by
  let T := episodeBoundary (k:=C.k) e f hef (episodeScaleRadius ν e f) C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N X.1.1
  have hlog : 0≤Real.log (1+(T (i+1)-T i:ℕ)) := Real.log_nonneg (by exact le_add_of_nonneg_right (Nat.cast_nonneg _))
  change (min (ENNReal.log (1+((StationaryCompact.shift^[i] (actualArrayMap e (C.paddedTimes hef N)
      (C.paddedStages hef N) X)).1 0).1.toENNReal)).toENNReal (B:ℝ≥0∞)).toReal ≤ _
  rw [C.actual_lengthMark]
  change (min (ENNReal.log (1+(T (i+1)-T i:ℕ))).toENNReal (B:ℝ≥0∞)).toReal ≤ _
  have he : (ENNReal.log (1+(T (i+1)-T i:ℕ))).toENNReal =
      ENNReal.ofReal (Real.log (1+(T (i+1)-T i:ℕ))) := by
    generalize T (i+1)-T i = n
    rw [ENNReal.log_pos_real (by positivity) (by finiteness), EReal.real_coe_toENNReal,
      ENNReal.toReal_add ENNReal.one_ne_top (ENNReal.natCast_ne_top n)]
    simp
  rw [he,ENNReal.toReal_min ENNReal.ofReal_ne_top ENNReal.coe_ne_top,
    ENNReal.toReal_ofReal hlog]
  apply (min_le_left _ _).trans
  by_cases ha : T i<N
  · have hh := episode_log_length_bound (k:=C.k) e f hef (episodeScaleRadius ν e f)
      C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N (T i) X.1.1
      C.hf.le C.hg.le C.hb.le (lt_of_lt_of_le zero_lt_one C.hs)
    simpa only [T,episodeBoundary,ite_eq_left ha,lengthCost,stagesAt,EpisodeChainLedger.stepMark,episodeStageCount] using hh
  · have heq : T (i+1)=T i := by simp only [T,episodeBoundary,ite_eq_right ha]
    rw [heq,Nat.sub_self,Nat.cast_zero,add_zero,Real.log_one]
    exact mul_nonneg C.lengthCost_nonneg (by positivity)

end OperationalConstants
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience
namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

lemma bad_logLengthCut_bound (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (hD : 0≤D) (N : ℕ) (hN : C.sfloor ≤ (N:ℝ))
    (hlarge : 32*C.b ≤ (1/2:ℝ)*Real.log (N:ℝ))
    (hmass : (N:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e N (1/2)))
    (B : ℝ≥0) :
    (∫ Y, logLengthCut e B Y ∂(C.occupation hef N
      ((environmentLaw ν)[|badCrossingEvent e N (1/2)]) : Measure (ActualEpisodeArray e))) ≤
      C.lengthCost*(1+C.injectionCost/(6*C.b)) := by
  let Q := (environmentLaw ν)[|badCrossingEvent e N (1/2)]
  let μ : ProbabilityMeasure (ActualEpisodeArray e) := C.occupation hef N Q
  let G : C(ActualEpisodeArray e,ℝ) := (ContinuousMap.const _ C.lengthCost)*(1+stageMarkCut e (N:ℝ≥0) 0)
  have hh := raw_actual_test_mono e ν Q (C.paddedTimes hef N) (C.paddedStages hef N)
    (C.paddedTimes_measurable hef N) (C.paddedStages_measurable hef N) N (C.activeCount hef N)
    (C.activeCount_measurable hef N) (logLengthCut e B) G (fun i X => by
      change _ ≤ C.lengthCost*(1+stageMarkCut e (N:ℝ≥0) 0
        (StationaryCompact.shift^[i] (actualArrayMap e (C.paddedTimes hef N) (C.paddedStages hef N) X)))
      rw [C.stageMarkCut_actual hef N i]
      have hj : (C.stagesAt hef N X.1.1 i:ℝ)≤(N:ℝ) := by
        exact_mod_cast EpisodeChainLedger.stepMark_le (k:=C.k) e f hef (episodeScaleRadius ν e f)
          C.fexp C.g C.χ C.b C.sfloor C.radius_nonneg N X.1.1 i
      rw [show ((N:ℝ≥0):ℝ)=(N:ℝ) by simp,min_eq_left hj]
      exact C.logLengthCut_actual_le hef N i B X)
  have hm : (∫ Y, logLengthCut e B Y ∂(μ : Measure (ActualEpisodeArray e)))≤
      ∫ Y, G Y ∂(μ : Measure (ActualEpisodeArray e)) := by
    change (∫ Y, logLengthCut e B Y ∂(actualOccupation e ν Q
      (C.paddedTimes hef N) (C.paddedStages hef N) (C.paddedTimes_measurable hef N) N (C.activeCount hef N):Measure _)) ≤
      ∫ Y, G Y ∂(actualOccupation e ν Q (C.paddedTimes hef N) (C.paddedStages hef N)
      (C.paddedTimes_measurable hef N) N (C.activeCount hef N):Measure _)
    rw [actualOccupation_integral e ν Q _ _ _ _ _ (C.bad_raw_mass_pos hef N hN hmass),
      actualOccupation_integral e ν Q _ _ _ _ _ (C.bad_raw_mass_pos hef N hN hmass)]
    exact mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr ENNReal.toReal_nonneg)
  apply hm.trans
  change (∫ Y, C.lengthCost*(1+stageMarkCut e (N:ℝ≥0) 0 Y) ∂(μ:Measure _))≤_
  rw [integral_const_mul,integral_add (integrable_const _)
    ((stageMarkCut e (N:ℝ≥0) 0).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
    integral_const,probReal_univ,one_smul]
  exact mul_le_mul_of_nonneg_left (add_le_add_right (C.bad_stageMark_bound hef hD N hN hlarge hmass (N:ℝ≥0)) 1)
    C.lengthCost_nonneg

lemma bad_limit_length_moment_oai (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (hD : 0≤D) (Ns : ℕ → ℕ)
    (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hlarge : ∀ n, 32*C.b ≤ (1/2:ℝ)*Real.log (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2)))
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto (fun n => C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)])) atTop (𝓝 ρ)) :
    (∀ᵐ Y ∂(ρ : Measure (ActualEpisodeArray e)), (Y.1 0).1<⊤) ∧
      Integrable (fun Y => (logLengthMark e Y).toReal) (ρ : Measure (ActualEpisodeArray e)) := by
  have hh := mark_lintegral_bound_of_weak_limit _ ρ hlim (logLengthMark e)
    (C.lengthCost*(1+C.injectionCost/(6*C.b)))
    (fun n B => C.bad_logLengthCut_bound hef hD (Ns n) (hN n) (hlarge n) (hmass n) B)
  have hf := mark_integrable_of_lintegral_bound (ρ : Measure (ActualEpisodeArray e)) (logLengthMark e)
    (logLengthMark e).continuous.measurable _ hh
  refine ⟨hf.1.mono (fun Y h => ?_),hf.2⟩
  by_contra hn
  have he : (Y.1 0).1=⊤ := top_le_iff.mp (le_of_not_gt hn)
  have ht : logLengthMark e Y=∞ := by simp [logLengthMark,he]
  rw [ht] at h
  exact (lt_irrefl _ h)

end OperationalConstants
end DirectionalTransience

end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.OperationalConstants.bad_limit_length_moment_oai := @OAI.DirectionalTransience.OperationalConstants.bad_limit_length_moment_oai
