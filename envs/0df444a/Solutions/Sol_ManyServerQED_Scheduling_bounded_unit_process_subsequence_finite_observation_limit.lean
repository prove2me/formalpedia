-- Prove2me | solution 1 for ManyServerQED.Scheduling.bounded_unit_process_subsequence_finite_observation_limit
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T03:54:54.314567+00:00
-- url     : https://prove2.me/submissions/c88dba4c-6ca6-4197-9f47-28d3ce811b08

import Theorems.Thm_ManyServerQED_Scheduling_bounded_continuous_unit_processes_have_tight_subsequence
import Theorems.Thm_ManyServerQED_Scheduling_eventual_continuous_modulus_bound_can_be_made_uniform
import Theorems.Thm_ManyServerQED_Scheduling_measurable_polygonal_approximation_on_unit_interval

open Filter Topology Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling

private abbrev I := Icc (0:ℝ) 1

set_option maxHeartbeats 1800000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {k : ℕ} [MeasurableSpace C(Icc (0:ℝ) 1, Fin k → ℝ)] [BorelSpace C(Icc (0:ℝ) 1, Fin k → ℝ)]
    (X : ℕ → Ω → ℝ → Fin k → ℝ)
    (hX : ∀ n t, t ∈ Icc (0:ℝ) 1 → Measurable (fun ω => X n ω t))
    (A : ℝ) (hA : ∀ n ω t, t ∈ Icc (0:ℝ) 1 → ‖X n ω t‖ ≤ A)
    (hM : ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) 1, ∃ t ∈ Icc (0:ℝ) 1, |s-t| ≤ δ ∧
        ε ≤ ‖X n ω s-X n ω t‖} ≤ ENNReal.ofReal η) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ μ : ProbabilityMeasure C(Icc (0:ℝ) 1, Fin k → ℝ),
      ∀ (m : ℕ) (τ : Fin m → Icc (0:ℝ) 1),
        TendstoInDistribution (fun n ω j => X (r n) ω (τ j)) atTop
          (fun (p : C(Icc (0:ℝ) 1, Fin k → ℝ)) j => p (τ j))
          (fun _ => P) (μ : Measure C(Icc (0:ℝ) 1, Fin k → ℝ)) := by
  classical
  choose Y hY hYA hYE using fun n =>
    measurable_polygonal_approximation_on_unit_interval n (X n) (hX n)
  have hMesh : Tendsto (fun n : ℕ => 1/((n+1:ℕ):ℝ)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.div_atTop
    simpa only [Nat.cast_add,Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds
  have hErr (ε : ℝ) (he : 0 < ε) :
      Tendsto (fun n => P {ω | ∃ s : I, ε ≤ ‖Y n ω s-X n ω s‖}) atTop (𝓝 0) := by
    apply ENNReal.tendsto_nhds_zero.2
    intro η hη
    obtain ⟨v,_,hv,hvη⟩ := ENNReal.lt_iff_exists_real_btwn.1 hη
    obtain ⟨δ,hδ,hSmall⟩ := hM (ε/2) v (by positivity) (ENNReal.ofReal_pos.1 hv)
    filter_upwards [hSmall,(tendsto_order.1 hMesh).2 _ hδ] with n hn hnδ
    refine (measure_mono ?_).trans (hn.trans hvη.le)
    intro ω hω
    by_contra hb
    have hE : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, |s-t| ≤ 1/((n+1:ℕ):ℝ) →
        ‖X n ω s-X n ω t‖ ≤ ε/2 := by
      intro s hs t ht hst
      exact (lt_of_not_ge (fun he => hb ⟨s,hs,t,ht,hst.trans hnδ.le,he⟩)).le
    obtain ⟨t,ht⟩ := hω
    exact not_le_of_gt (show ε/2 < ε by linarith) (ht.trans (hYE n ω _ hE t))
  have hYMod (ε η : ℝ) (he : 0 < ε) (hη : 0 < η) :
      ∃ δ > 0, ∀ᶠ n in atTop,
        P {ω | ∃ s t : I, dist s t ≤ δ ∧ ε ≤ dist (Y n ω s) (Y n ω t)} ≤ ENNReal.ofReal η := by
    obtain ⟨δ,hδ,hB⟩ := hM (ε/3) (η/2) (by positivity) (by positivity)
    have hSmall := (tendsto_order.1 (hErr (ε/3) (by positivity))).2 (ENNReal.ofReal (η/2))
      (ENNReal.ofReal_pos.2 (by positivity))
    let F (n : ℕ) := {ω | ∃ s : I, ε/3 ≤ ‖Y n ω s-X n ω s‖}
    let G (n : ℕ) := {ω | ∃ s ∈ Icc (0:ℝ) 1, ∃ t ∈ Icc (0:ℝ) 1, |s-t| ≤ δ ∧
      ε/3 ≤ ‖X n ω s-X n ω t‖}
    refine ⟨δ,hδ,?_⟩
    filter_upwards [hB,hSmall] with n hn hne
    calc
      _ ≤ P (F n ∪ G n) := by
        apply measure_mono
        rintro ω ⟨s,t,hst,hb⟩
        by_contra hNot
        have hs : ‖Y n ω s-X n ω s‖ < ε/3 := lt_of_not_ge (fun h => hNot (Or.inl ⟨s,h⟩))
        have ht : ‖Y n ω t-X n ω t‖ < ε/3 := lt_of_not_ge (fun h => hNot (Or.inl ⟨t,h⟩))
        have hsu : |(s:ℝ)-(t:ℝ)| ≤ δ := by simpa only [Subtype.dist_eq,Real.dist_eq] using hst
        have hX : ‖X n ω s-X n ω t‖ < ε/3 :=
          lt_of_not_ge (fun he => hNot (Or.inr ⟨s,s.2,t,t.2,hsu,he⟩))
        have h1 := dist_triangle (Y n ω s) (X n ω s) (Y n ω t)
        have h2 := dist_triangle (X n ω s) (X n ω t) (Y n ω t)
        rw [dist_comm (X n ω t) (Y n ω t)] at h2
        simp only [dist_eq_norm] at h1 h2 hb
        linarith only [h1,h2,hs,ht,hX,hb]
      _ ≤ P (F n)+P (G n) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (η/2)+ENNReal.ofReal (η/2) := add_le_add hne.le hn
      _ = ENNReal.ofReal η := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
  obtain ⟨r,hr,μ,hL⟩ := bounded_continuous_unit_processes_have_tight_subsequence Y hY A
    (fun n ω => hYA n ω A (hA n ω))
    (fun ε η he hη => eventual_continuous_modulus_bound_can_be_made_uniform Y hY ε η he hη
      (hYMod ε η he hη))
  refine ⟨r,hr,μ,?_⟩
  let : IsProbabilityMeasure (μ : Measure C(I, Fin k → ℝ)) := μ.prop
  intro m τ
  let f (p : C(I,Fin k → ℝ)) (i : Fin m) := p (τ i)
  have hf : Continuous f := continuous_pi (fun i => continuous_eval_const (τ i))
  let V (n : ℕ) (ω : Ω) (i : Fin m) := X (r n) ω (τ i)
  have hV (n : ℕ) : AEMeasurable (V n) P :=
    aemeasurable_pi_lambda _ (fun i => (hX _ _ (τ i).2).aemeasurable)
  have hL' : TendstoInDistribution (fun n ω => f (Y (r n) ω)) atTop f (fun _ => P)
      (μ : Measure C(I, Fin k → ℝ)) := hL.continuous_comp hf
  refine tendstoInDistribution_of_tendstoInMeasure_sub V f hL' ?_ hV
  rw [tendstoInMeasure_iff_norm]
  intro ε he
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    ((hErr ε he).comp hr.tendsto_atTop) (Eventually.of_forall (fun _ => zero_le)) ?_
  apply Eventually.of_forall
  intro n
  apply measure_mono
  intro ω hbad
  by_contra hGood
  apply (not_le_of_gt (show ‖(V - (fun n ω => f (Y (r n) ω))) n ω - (0:Ω → Fin m → Fin k → ℝ) ω‖ < ε from ?_)) hbad
  apply (pi_norm_lt_iff he).2
  intro j
  simpa only [Pi.sub_apply,Pi.zero_apply,sub_zero,V,f,norm_sub_rev] using
    (lt_of_not_ge (fun h => hGood ⟨τ j,h⟩) : ‖Y (r n) ω (τ j)-X (r n) ω (τ j)‖ < ε)
