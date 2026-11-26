-- Prove2me | solution 1 for ManyServerQED.Scheduling.eventual_continuous_modulus_bound_can_be_made_uniform
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T03:26:04.842388+00:00
-- url     : https://prove2.me/submissions/11b1addc-c126-433f-b00f-72b9286d636e

import Mathlib

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

private abbrev I := Icc (0:ℝ) 1

private def modulusBad {k : ℕ} (d e : ℝ) : Set C(I,Fin k → ℝ) :=
  {f | ∃ s t : I, dist s t ≤ d ∧ e ≤ dist (f s) (f t)}

private theorem closed_modulusBad {k : ℕ} (d e : ℝ) : IsClosed (modulusBad (k := k) d e) := by
  let R : Set (I × I) := {p | dist p.1 p.2 ≤ d}
  have hr : IsClosed R := isClosed_le (continuous_fst.dist continuous_snd) continuous_const
  let Q : Set (C(I,Fin k → ℝ) × (I × I)) :=
    {p | p.2 ∈ R ∧ e ≤ dist (p.1 p.2.1) (p.1 p.2.2)}
  have h₁ : Continuous (fun p : C(I,Fin k → ℝ) × (I × I) => p.1 p.2.1) :=
    continuous_eval.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have h₂ : Continuous (fun p : C(I,Fin k → ℝ) × (I × I) => p.1 p.2.2) :=
    continuous_eval.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  have hQ : IsClosed Q :=
    (hr.preimage continuous_snd).inter (isClosed_le continuous_const (h₁.dist h₂))
  have him := isClosedMap_fst_of_compactSpace Q hQ
  convert him using 1
  ext f
  change (∃ s t : I, dist s t ≤ d ∧ _) ↔ ∃ p ∈ Q, p.1 = f
  constructor
  · rintro ⟨s,t,h₁,h₂⟩
    exact ⟨(f,s,t),⟨h₁,h₂⟩,rfl⟩
  · rintro ⟨⟨p,s,t⟩,⟨h₁,h₂⟩,rfl⟩
    exact ⟨s,t,h₁,h₂⟩

set_option maxHeartbeats 1200000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {k : ℕ} [MeasurableSpace C(Icc (0:ℝ) 1, Fin k → ℝ)] [BorelSpace C(Icc (0:ℝ) 1, Fin k → ℝ)]
    (X : ℕ → Ω → C(Icc (0:ℝ) 1, Fin k → ℝ)) (hX : ∀ n, Measurable (X n))
    (e η : ℝ) (he : 0 < e) (hη : 0 < η)
    (h : ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s t : Icc (0:ℝ) 1, dist s t ≤ δ ∧ e ≤ dist (X n ω s) (X n ω t)}
        ≤ ENNReal.ofReal η) :
    ∃ d > 0, ∀ n,
      P {ω | ∃ s t : Icc (0:ℝ) 1, dist s t ≤ d ∧ e ≤ dist (X n ω s) (X n ω t)}
        ≤ ENNReal.ofReal η := by
  classical
  let E := Fin k → ℝ
  obtain ⟨d,hd,hTail⟩ := h
  obtain ⟨N,hN⟩ := eventually_atTop.1 hTail
  let D (n : ℕ) (r : ℝ) := {ω | ∃ s t : I, dist s t ≤ r ∧ e ≤ dist (X n ω s) (X n ω t)}
  have hAnti (n : ℕ) : Monotone (D n) := by
    intro r s hrs ω
    rintro ⟨u,v,h,r⟩
    exact ⟨u,v,h.trans hrs,r⟩
  have hSingle (n : ℕ) : ∃ r > 0, P (D n r) ≤ ENNReal.ofReal η := by
    let r (j : ℕ) := 1/((j:ℝ)+1)
    have hR : Antitone r := by
      intro j l hj
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hj 1)
    have h0 : (⋂ j, D n (r j)) = ∅ := by
      apply eq_empty_iff_forall_notMem.2
      intro ω hw
      obtain ⟨δ,hδ,hU⟩ := Metric.uniformContinuous_iff.1
        (CompactSpace.uniformContinuous_of_continuous (X n ω).continuous) e he
      obtain ⟨j,hj⟩ := exists_nat_gt (1/δ)
      have hj' : r j < δ := by
        dsimp [r]
        apply (div_lt_iff₀ (by positivity : 0 < (j:ℝ)+1)).2
        have h' := (div_lt_iff₀ hδ).1 hj
        nlinarith
      obtain ⟨u,v,huv,hv⟩ := mem_iInter.1 hw j
      exact (not_le_of_gt (hU (huv.trans_lt hj'))) hv
    have hM (j : ℕ) : MeasurableSet (D n (r j)) :=
      (hX n) ((closed_modulusBad (r j) e).measurableSet)
    have hT := tendsto_measure_iInter_atTop (μ := P) (fun j => (hM j).nullMeasurableSet)
      (fun a b hab => hAnti n (hR hab)) ⟨0,measure_ne_top _ _⟩
    rw [h0,measure_empty] at hT
    obtain ⟨j,hj⟩ := ((tendsto_order.1 hT).2 _ (ENNReal.ofReal_pos.2 hη)).exists
    exact ⟨r j,by dsimp [r]; positivity,hj.le⟩
  choose ρ hρ hB using hSingle
  have hMin (S : Finset ℕ) : ∃ r > 0, r ≤ d ∧ ∀ n ∈ S, r ≤ ρ n := by
    induction S using Finset.induction_on with
    | empty => exact ⟨d,hd,le_rfl,by simp⟩
    | @insert i S hi hiS =>
        obtain ⟨r,hr,hrd,hrS⟩ := hiS
        refine ⟨min (ρ i) r,lt_min (hρ i) hr,(min_le_right _ _).trans hrd,fun j hj => ?_⟩
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact min_le_left _ _
        · exact (min_le_right _ _).trans (hrS j hj)
  obtain ⟨r,hr,hrd,hR⟩ := hMin (Finset.range N)
  refine ⟨r,hr,fun n => ?_⟩
  by_cases hn : N ≤ n
  · exact (measure_mono (hAnti n hrd)).trans (hN n hn)
  · exact (measure_mono (hAnti n (hR n (Finset.mem_range.2 (lt_of_not_ge hn))))).trans (hB n)
