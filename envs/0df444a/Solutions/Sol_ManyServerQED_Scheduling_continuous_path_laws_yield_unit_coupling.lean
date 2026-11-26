-- Prove2me | solution 1 for ManyServerQED.Scheduling.continuous_path_laws_yield_unit_coupling
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T01:03:03.351208+00:00
-- url     : https://prove2.me/submissions/9e97d0a7-129c-4dd5-a1df-b5bcb218811b

import Theorems.Thm_Reiman84_QueueLength_weakConvD_of_fdd_and_modulus
import Definitions.Def_DurrettProbability_Donsker

open Set Filter Topology MeasureTheory ProbabilityTheory
open DurrettProbability Reiman84.QueueLength
open scoped ENNReal NNReal


private abbrev I := Icc (0:ℝ) 1

private noncomputable def atUnit (f : PathSpace) (t : ℝ) : Fin 1 → ℝ :=
  fun _ => f (Set.projIcc 0 1 zero_le_one t)

private theorem cont_atUnit (f : PathSpace) : Continuous (atUnit f) := by
  apply continuous_pi
  intro i
  exact f.continuous.comp continuous_projIcc

private theorem cont_atUnit_eval (t : ℝ) : Continuous (fun f : PathSpace => atUnit f t) := by
  apply continuous_pi
  intro i
  exact continuous_eval_const _

private def modBad (d ε : ℝ) : Set PathSpace :=
  {f | ∃ s t : I, dist s t ≤ d ∧ ε ≤ ‖(fun _ : Fin 1 => f s) - (fun _ : Fin 1 => f t)‖}

private theorem isClosed_modBad (d ε : ℝ) : IsClosed (modBad d ε) := by
  let R : Set (I × I) := {p | dist p.1 p.2 ≤ d}
  have hr : IsClosed R := isClosed_le (continuous_fst.dist continuous_snd) continuous_const
  let Q : Set (PathSpace × (I × I)) :=
    {p | p.2 ∈ R ∧ ε ≤ ‖(fun _ : Fin 1 => p.1 p.2.1) - (fun _ : Fin 1 => p.1 p.2.2)‖}
  have h₁ : Continuous (fun p : PathSpace × (I × I) => (fun _ : Fin 1 => p.1 p.2.1)) := by
    apply continuous_pi
    intro i
    exact continuous_eval.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have h₂ : Continuous (fun p : PathSpace × (I × I) => (fun _ : Fin 1 => p.1 p.2.2)) := by
    apply continuous_pi
    intro i
    exact continuous_eval.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  have hQ : IsClosed Q :=
    (hr.preimage continuous_snd).inter (isClosed_le continuous_const (h₁.sub h₂).norm)
  have him := isClosedMap_fst_of_compactSpace Q hQ
  convert him using 1
  ext f
  change (∃ s t : I, dist s t ≤ d ∧ _) ↔ ∃ p ∈ Q, p.1 = f
  constructor
  · rintro ⟨s,t,h₁,h₂⟩
    exact ⟨(f,s,t),⟨h₁,h₂⟩,rfl⟩
  · rintro ⟨⟨p,s,t⟩,⟨h₁,h₂⟩,rfl⟩
    exact ⟨s,t,h₁,h₂⟩

set_option maxHeartbeats 1100000 in
theorem solution (μn : ℕ → ProbabilityMeasure PathSpace) (μ : ProbabilityMeasure PathSpace)
    (hμ : Tendsto μn atTop (𝓝 μ)) :
    WeakConvD (fun n => (μn n : Measure PathSpace))
      (fun _ f t => fun _ : Fin 1 => f (Set.projIcc 0 1 zero_le_one t))
      (μ : Measure PathSpace)
      (fun f t => fun _ : Fin 1 => f (Set.projIcc 0 1 zero_le_one t)) := by
  change WeakConvD (fun n => (μn n : Measure PathSpace)) (fun _ => atUnit) (μ : Measure PathSpace) atUnit
  have hc (f : PathSpace) : IsCadlag01 (atUnit f) :=
    ⟨fun _ _ => (cont_atUnit f).continuousWithinAt,
      fun t _ => ⟨atUnit f t,(cont_atUnit f).continuousWithinAt⟩⟩
  apply weakConvD_of_fdd_and_modulus
  · intro n
    infer_instance
  · infer_instance
  · intro n
    refine ⟨(measurable_pi_lambda _ (fun t => (cont_atUnit_eval (clamp01 t)).measurable)).aemeasurable, ?_⟩
    exact ae_of_all _ hc
  · exact fun t => (cont_atUnit_eval t).measurable
  · exact fun f => (cont_atUnit f).continuousOn
  · intro m τ hτ f hfb hf
    obtain ⟨C,hC⟩ := hfb
    obtain ⟨L,hL⟩ := hf
    let F (p : PathSpace) := f (fun i => atUnit p (τ i))
    have hF : Continuous F := hL.continuous.comp (continuous_pi fun i => cont_atUnit_eval (τ i))
    let g := BoundedContinuousFunction.mkOfBound ⟨F,hF⟩ (2*C) (by
      intro x y
      rw [Real.dist_eq]
      change |F x - F y| ≤ 2*C
      have hFx : |F x| ≤ C := hC (fun i => atUnit x (τ i))
      have hFy : |F y| ≤ C := hC (fun i => atUnit y (τ i))
      exact (abs_sub (F x) (F y)).trans (by linarith))
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ) g
  · intro ε hε η hη
    let d (m : ℕ) : ℝ := 1 / ((m:ℝ)+1)
    have hd : Tendsto d atTop (𝓝 0) := by
      exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    have hdpos (m : ℕ) : 0 < d m := by dsimp [d]; positivity
    have hdant : Antitone d := by
      intro a b hab
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hab)
    let A (m : ℕ) := modBad (d m) ε
    have hA (m : ℕ) : IsClosed (A m) := isClosed_modBad _ _
    have hAm : Antitone A := by
      intro a b hab f hf
      obtain ⟨s,t,hst,hf⟩ := hf
      exact ⟨s,t,hst.trans (hdant hab),hf⟩
    have hEmpty : (⋂ m, A m) = ∅ := by
      apply eq_empty_iff_forall_notMem.2
      intro f hf
      have hCont : Continuous (fun t : I => fun _ : Fin 1 => f t) :=
        continuous_pi (fun _ => f.continuous)
      obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuous_iff.mp
        (CompactSpace.uniformContinuous_of_continuous hCont) ε hε
      obtain ⟨m,hm⟩ := ((tendsto_order.1 hd).2 δ hδ).exists
      obtain ⟨s,t,hst,hfa⟩ := mem_iInter.1 hf m
      exact (not_lt_of_ge hfa) (by
        simpa only [dist_eq_norm] using hmod (hst.trans_lt hm))
    have hL := tendsto_measure_iInter_atTop (μ := (μ : Measure PathSpace))
      (fun m => (hA m).measurableSet.nullMeasurableSet) hAm ⟨0, measure_ne_top _ _⟩
    rw [hEmpty, measure_empty] at hL
    obtain ⟨m,hm⟩ := ((tendsto_order.1 hL).2 (ENNReal.ofReal η) (ENNReal.ofReal_pos.2 hη)).exists
    have hLS := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ (hA m)
    obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt (hLS.trans_lt hm))
    refine ⟨d m,hdpos m,N,fun n hn => (measure_mono ?_).trans (hN n hn).le⟩
    rintro f ⟨s,hs,t,ht,hst,hf⟩
    have hcl (a : ℝ) (ha : a ∈ I) : Set.projIcc 0 1 zero_le_one a = (⟨a,ha⟩:I) := by
      apply Subtype.ext
      simp [Set.projIcc,max_eq_right ha.1,min_eq_right ha.2]
    refine ⟨⟨s,hs⟩,⟨t,ht⟩,?_,?_⟩
    · simpa only [Subtype.dist_eq, Real.dist_eq] using hst
    · change ε ≤ ‖(fun _ : Fin 1 => f (Set.projIcc 0 1 zero_le_one s)) -
          (fun _ : Fin 1 => f (Set.projIcc 0 1 zero_le_one t))‖ at hf
      rwa [hcl s hs, hcl t ht] at hf

