-- Prove2me | solution 1 for GoldieRenewal.Rates.theorem_3_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T03:39:23.526234+00:00
-- url     : https://prove2.me/submissions/cb3c3755-1ea8-4718-bd66-a44623855940
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GoldieRenewal_Rates_Transforms
import Definitions.Def_GoldieRenewal_Rates_Model
import Definitions.Def_GoldieRenewal_Rates_Expansion
import Theorems.Thm_GoldieRenewal_Kesten_lemma_9_4
import Theorems.Thm_GoldieRenewal_Rates_theorem_3_2_i

open MeasureTheory ProbabilityTheory
open GoldieRenewal.Rates
open QueueingFundamentals.MG1 (convPow)

lemma convPow_ac_aux (μ ν : Measure ℝ) [SFinite ν] (h : μ ≪ ν) :
    ∀ n, convPow μ n ≪ convPow ν n := by
  intro n
  induction n with
  | zero => exact Measure.AbsolutelyContinuous.refl _
  | succ n ih =>
    show Measure.map _ _ ≪ Measure.map _ _
    exact (ih.prod h).map (by fun_prop)

lemma tilted_prob_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : Ω → ℝ) (hM : Measurable M) (hM_nonneg : ∀ᵐ ω ∂P, 0 ≤ M ω) (κ : ℝ) (hκ : 0 < κ)
    (h_2_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ κ) ∂P = 1) :
    IsProbabilityMeasure (tiltedLaw P M κ) := by
  constructor
  have hS : MeasurableSet {ω | 0 < M ω} := measurableSet_lt measurable_const hM
  unfold tiltedLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_map (by fun_prop) (by fun_prop)]
  rw [← h_2_3]
  conv_rhs => rw [← lintegral_add_compl _ hS]
  have h2 : ∫⁻ ω in {ω | 0 < M ω}ᶜ, ENNReal.ofReal (|M ω| ^ κ) ∂P = 0 := by
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    refine (ae_restrict_iff' hS.compl).2 (hM_nonneg.mono fun ω h hω => ?_)
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hω
    have : M ω = 0 := le_antisymm hω h
    simp [this, Real.zero_rpow (ne_of_gt hκ)]
  rw [h2, add_zero]
  apply setLIntegral_congr_fun hS
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω
  simp only [abs_of_pos hω, Real.rpow_def_of_pos hω, mul_comm]

lemma tilted_spread_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : Ω → ℝ) (hM : Measurable M) (hM_nonneg : ∀ᵐ ω ∂P, 0 ≤ M ω) (κ : ℝ) (hκ : 0 < κ)
    (h_2_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ κ) ∂P = 1)
    (h_3_4 : SpreadOut (logLawGivenNonzero P M)) :
    SpreadOut (tiltedLaw P M κ) := by
  have := tilted_prob_aux P M hM hM_nonneg κ hκ h_2_3
  have hS : MeasurableSet {ω | 0 < M ω} := measurableSet_lt measurable_const hM
  have hac : logLawGivenNonzero P M ≪ tiltedLaw P M κ := by
    unfold logLawGivenNonzero tiltedLaw ProbabilityTheory.cond
    have h1 : Measure.map (fun ω => Real.log |M ω|) ((P {ω | M ω ≠ 0})⁻¹ • P.restrict {ω | M ω ≠ 0})
        ≪ Measure.map (fun ω => Real.log |M ω|) (P.restrict {ω | M ω ≠ 0}) :=
      Measure.smul_absolutelyContinuous.map (by fun_prop)
    have h2 : P.restrict {ω | M ω ≠ 0} = P.restrict {ω | 0 < M ω} := by
      apply Measure.restrict_congr_set
      filter_upwards [hM_nonneg] with ω h
      apply propext
      show M ω ≠ 0 ↔ 0 < M ω
      constructor
      · intro h'; exact lt_of_le_of_ne h (Ne.symm h')
      · intro h'; exact ne_of_gt h'
    have h3 : Measure.map (fun ω => Real.log |M ω|) (P.restrict {ω | 0 < M ω})
        = Measure.map (fun ω => Real.log (M ω)) (P.restrict {ω | 0 < M ω}) := by
      apply Measure.map_congr
      refine (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun ω hω => ?_)
      simp only [Set.mem_setOf_eq] at hω
      simp [abs_of_pos hω]
    rw [h2, h3] at h1
    rw [h2]
    refine h1.trans (withDensity_absolutelyContinuous' ?_ ?_)
    · exact Measurable.aemeasurable (by measurability)
    exact Filter.Eventually.of_forall fun x => by simp [Real.exp_pos]
  obtain ⟨n, hn, hsing⟩ := h_3_4
  refine ⟨n, hn, fun h => hsing ?_⟩
  exact h.mono_ac (convPow_ac_aux _ _ hac n) (Measure.AbsolutelyContinuous.refl _)

lemma tail_antitone_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) : Measurable (fun t : ℝ => P.real {ω | t < Z ω}) := by
  apply Antitone.measurable
  intro a b hab
  refine measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)
  simp only [Set.mem_setOf_eq] at hω ⊢
  linarith

lemma tail_of_moment_aux {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y Z : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hlaw : P.map X = P.map Z) (s : ℝ) (hs : 0 < s)
    (hfin : ∫⁻ ω, ENNReal.ofReal |max (X ω) 0 ^ s - max (Y ω) 0 ^ s| ∂P < ⊤) :
    IntegrableOn (fun t : ℝ => (P.real {ω | t < Z ω} - P.real {ω | t < Y ω}) * t ^ (s - 1))
      (Set.Ioi 0) := by
  have key : ∀ t : ℝ, P.real {ω | t < X ω} = P.real {ω | t < Z ω} := by
    intro t
    have h1 := Measure.map_apply (μ := P) hX (measurableSet_Ioi (a := t))
    have h2 := Measure.map_apply (μ := P) hZ (measurableSet_Ioi (a := t))
    rw [hlaw] at h1
    simp only [measureReal_def]
    exact congrArg ENNReal.toReal (h1.symm.trans h2)
  have hb := (GoldieRenewal.Kesten.lemma_9_4 P s hs X Y hX hY).1
  simp only [key] at hb
  have hlt := lt_of_le_of_lt hb (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  refine ⟨?_, ?_⟩
  · exact (((tail_antitone_aux P Z).sub (tail_antitone_aux P Y)).mul
      (by measurability)).aestronglyMeasurable
  · unfold HasFiniteIntegral
    refine lt_of_le_of_lt (le_of_eq ?_) hlt
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [Set.mem_Ioi] at ht
    simp only []
    rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.le _)]

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M R : Ω → ℝ) (hM : Measurable M) (hR : Measurable R) (hM_nonneg : ∀ᵐ ω ∂P, 0 ≤ M ω)
    (h_indep : IndepFun R M P) (κ β : ℝ) (hκ : 0 < κ) (hβ : 0 < β)
    (h_2_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ κ) ∂P = 1)
    (h_3_3 : ∫⁻ ω, ENNReal.ofReal (|M ω| ^ (κ + β)) ∂P < ⊤)
    (h_3_4 : SpreadOut (logLawGivenNonzero P M)) :
    (IsProbabilityMeasure (tiltedLaw P M κ) ∧ SpreadOut (tiltedLaw P M κ)) ∧
    (StoneConditions (tiltedLaw P M κ) β →
      -- (i)
      (IntegrableOn (fun t : ℝ =>
          (P.real {ω | t < R ω} - P.real {ω | t < M ω * R ω}) * t ^ (κ + β - 1))
          (Set.Ioi 0) → ExpansionPos P M R κ β) ∧
      -- (ii)
      (IntegrableOn (fun t : ℝ =>
          (P.real {ω | R ω < -t} - P.real {ω | M ω * R ω < -t}) * t ^ (κ + β - 1))
          (Set.Ioi 0) → ExpansionNeg P M R κ β) ∧
      -- (iii)
      (∀ Ψ : ℝ → Ω → ℝ, Measurable (Function.uncurry Ψ) →
        P.map (fun ω => Ψ (R ω) ω) = P.map R →
        IndepFun R (fun ω => (M ω, fun t => Ψ t ω)) P →
        (∫⁻ ω, ENNReal.ofReal
            |max (Ψ (R ω) ω) 0 ^ (κ + β) - max (M ω * R ω) 0 ^ (κ + β)| ∂P < ⊤ →
          ExpansionPos P M R κ β) ∧
        (∫⁻ ω, ENNReal.ofReal
            |max (-Ψ (R ω) ω) 0 ^ (κ + β) - max (-(M ω * R ω)) 0 ^ (κ + β)| ∂P < ⊤ →
          ExpansionNeg P M R κ β))) := by
  refine ⟨⟨tilted_prob_aux P M hM hM_nonneg κ hκ h_2_3,
    tilted_spread_aux P M hM hM_nonneg κ hκ h_2_3 h_3_4⟩, fun h_stone => ?_⟩
  have e1 : ∀ t : ℝ, {ω | t < -R ω} = {ω | R ω < -t} := by
    intro t; ext ω; simp only [Set.mem_setOf_eq]; constructor <;> intro h <;> linarith
  have e2 : ∀ t : ℝ, {ω | t < M ω * -R ω} = {ω | M ω * R ω < -t} := by
    intro t; ext ω; simp only [Set.mem_setOf_eq, mul_neg]; constructor <;> intro h <;> linarith
  have e3 : ∀ t : ℝ, {ω | t < -(M ω * R ω)} = {ω | M ω * R ω < -t} := by
    intro t; ext ω; simp only [Set.mem_setOf_eq]; constructor <;> intro h <;> linarith
  have hi : IntegrableOn (fun t : ℝ =>
      (P.real {ω | t < R ω} - P.real {ω | t < M ω * R ω}) * t ^ (κ + β - 1))
      (Set.Ioi 0) → ExpansionPos P M R κ β := fun h =>
    theorem_3_2_i P M R hM hR hM_nonneg h_indep κ β hκ hβ h_2_3 h_3_3 h_3_4 h_stone h
  have hii : IntegrableOn (fun t : ℝ =>
      (P.real {ω | R ω < -t} - P.real {ω | M ω * R ω < -t}) * t ^ (κ + β - 1))
      (Set.Ioi 0) → ExpansionNeg P M R κ β := by
    intro h
    have hind' : IndepFun (fun ω => -R ω) M P := h_indep.comp measurable_neg measurable_id
    have h' : IntegrableOn (fun t : ℝ =>
        (P.real {ω | t < -R ω} - P.real {ω | t < M ω * -R ω}) * t ^ (κ + β - 1))
        (Set.Ioi 0) := by
      simp only [e1, e2]; exact h
    have hneg := theorem_3_2_i P M (fun ω => -R ω) hM hR.neg hM_nonneg hind' κ β hκ hβ
      h_2_3 h_3_3 h_3_4 h_stone h'
    simpa only [ExpansionPos, ExpansionNeg, CPlus, CMinus, contourTermPos, contourTermNeg,
      gPos, gNeg, e1, e2] using hneg
  refine ⟨hi, hii, fun Ψ hΨ hlaw _ => ⟨fun hfin => ?_, fun hfin => ?_⟩⟩
  · have hX : Measurable (fun ω => Ψ (R ω) ω) := hΨ.comp (hR.prodMk measurable_id)
    exact hi (tail_of_moment_aux P (fun ω => Ψ (R ω) ω) (fun ω => M ω * R ω) R hX
      (hM.mul hR) hR hlaw (κ + β) (by linarith) hfin)
  · have hX : Measurable (fun ω => Ψ (R ω) ω) := hΨ.comp (hR.prodMk measurable_id)
    have hlaw' : P.map (fun ω => -Ψ (R ω) ω) = P.map (fun ω => -R ω) := by
      have a1 : P.map (fun ω => -Ψ (R ω) ω) = (P.map (fun ω => Ψ (R ω) ω)).map Neg.neg :=
        (Measure.map_map measurable_neg hX).symm
      have a2 : P.map (fun ω => -R ω) = (P.map R).map Neg.neg :=
        (Measure.map_map measurable_neg hR).symm
      rw [a1, a2, hlaw]
    have := tail_of_moment_aux P (fun ω => -Ψ (R ω) ω) (fun ω => -(M ω * R ω))
      (fun ω => -R ω) hX.neg (hM.mul hR).neg hR.neg hlaw' (κ + β) (by linarith) hfin
    apply hii
    simpa only [e1, e3] using this
