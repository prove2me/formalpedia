-- Prove2me | solution 1 for ManyServerQED.Scheduling.weak_continuous_path_laws_control_norm_and_modulus
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T02:23:45.239354+00:00
-- url     : https://prove2.me/submissions/eb2ebb91-71ce-423c-85ea-95dcf583d318

import Mathlib
import Definitions.Def_DurrettProbability_Donsker

open Set Filter Topology MeasureTheory ProbabilityTheory DurrettProbability
open scoped ENNReal NNReal
private abbrev I := Icc (0:ℝ) 1

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

theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ℕ → Ω → PathSpace) (Y : Ω' → PathSpace)
    (h : TendstoInDistribution X atTop Y (fun _ => P) P')
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ A > 0, ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | A ≤ ‖X n ω‖ ∨ ∃ s t : Set.Icc (0:ℝ) 1,
        dist s t ≤ δ ∧ ε ≤ |X n ω s-X n ω t|} ≤ ENNReal.ofReal η := by
  let μn : ℕ → ProbabilityMeasure PathSpace := fun n =>
    ⟨P.map (X n),Measure.isProbabilityMeasure_map (h.forall_aemeasurable n)⟩
  let μ : ProbabilityMeasure PathSpace :=
    ⟨P'.map Y,Measure.isProbabilityMeasure_map h.aemeasurable_limit⟩
  have hμ : Tendsto μn atTop (𝓝 μ) := h.tendsto
  have hPos : 0 < η/2 := by linarith
  have small_closed_family (B : ℕ → Set PathSpace) (hB : ∀ m, IsClosed (B m))
      (hA : Antitone B) (h0 : (⋂ m, B m) = ∅) :
      ∃ m, ∀ᶠ n in atTop, (μn n : Measure PathSpace) (B m) ≤ ENNReal.ofReal (η/2) := by
    have hL := tendsto_measure_iInter_atTop (μ := (μ : Measure PathSpace))
      (fun m => (hB m).measurableSet.nullMeasurableSet) hA ⟨0,measure_ne_top _ _⟩
    rw [h0,measure_empty] at hL
    obtain ⟨m,hm⟩ := ((tendsto_order.1 hL).2 (ENNReal.ofReal (η/2)) (ENNReal.ofReal_pos.2 hPos)).exists
    have hLS := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ (hB m)
    exact ⟨m,(eventually_lt_of_limsup_lt (hLS.trans_lt hm)).mono (fun _ h => h.le)⟩
  let B (m : ℕ) : Set PathSpace := {f | (m:ℝ)+1 ≤ ‖f‖}
  have hB (m : ℕ) : IsClosed (B m) := isClosed_le continuous_const continuous_norm
  have hBA : Antitone B := by
    intro m n hmn f hf
    have hc : (m:ℝ) ≤ n := by exact_mod_cast hmn
    exact le_trans (add_le_add_left hc 1) hf
  have hB0 : (⋂ m, B m) = ∅ := by
    apply eq_empty_iff_forall_notMem.2
    intro f hf
    obtain ⟨m,hm⟩ := exists_nat_gt ‖f‖
    have hh : (m:ℝ)+1 ≤ ‖f‖ := (Set.mem_iInter.1 hf) m
    linarith
  obtain ⟨m,hm⟩ := small_closed_family B hB hBA hB0
  let d (l : ℕ) : ℝ := 1/((l:ℝ)+1)
  have hd : Tendsto d atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hdpos (l : ℕ) : 0 < d l := by dsimp [d]; positivity
  have hdant : Antitone d := by
    intro i j hij
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hij)
  let C (l : ℕ) := modBad (d l) ε
  have hC (l : ℕ) : IsClosed (C l) := isClosed_modBad _ _
  have hCA : Antitone C := by
    rintro i j h f ⟨s,t,hst,hεt⟩
    exact ⟨s,t,hst.trans (hdant h),hεt⟩
  have hC0 : (⋂ l, C l) = ∅ := by
    apply eq_empty_iff_forall_notMem.2
    intro f hf
    have hCont : Continuous (fun t : I => fun _ : Fin 1 => f t) :=
      continuous_pi (fun _ => f.continuous)
    obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous hCont) ε hε
    obtain ⟨l,hl⟩ := ((tendsto_order.1 hd).2 δ hδ).exists
    obtain ⟨s,t,hst,hεt⟩ := mem_iInter.1 hf l
    exact (not_lt_of_ge hεt) (by simpa only [dist_eq_norm] using hmod (hst.trans_lt hl))
  obtain ⟨l,hl⟩ := small_closed_family C hC hCA hC0
  refine ⟨(m:ℝ)+1,by positivity,d l,hdpos l,?_⟩
  filter_upwards [hm,hl] with n hmn hln
  have hIncl : {ω | (m:ℝ)+1 ≤ ‖X n ω‖ ∨ ∃ s t : I,
      dist s t ≤ d l ∧ ε ≤ |X n ω s-X n ω t|} ⊆ X n ⁻¹' (B m ∪ C l) := by
    rintro ω (h1 | ⟨s,t,hst,h2⟩)
    · exact Or.inl h1
    · apply Or.inr
      refine ⟨s,t,hst,?_⟩
      have hh : |X n ω s-X n ω t| ≤ ‖(fun _ : Fin 1 => X n ω s) - (fun _ : Fin 1 => X n ω t)‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm ((fun _ : Fin 1 => X n ω s) -
          (fun _ : Fin 1 => X n ω t)) (0:Fin 1)
      exact h2.trans hh
  refine (measure_mono hIncl).trans ?_
  rw [← Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) ((hB m).measurableSet.union (hC l).measurableSet)]
  change (μn n : Measure PathSpace) (B m ∪ C l) ≤ _
  refine (measure_union_le _ _).trans ((add_le_add hmn hln).trans_eq ?_)
  rw [← ENNReal.ofReal_add hPos.le hPos.le]
  congr 1
  ring
