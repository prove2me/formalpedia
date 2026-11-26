-- Prove2me | solution 1 for ManyServerQED.Scheduling.bounded_continuous_unit_processes_have_tight_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T03:26:04.37014+00:00
-- url     : https://prove2.me/submissions/ca472e6c-7290-4565-87ee-0b4f1b61cfb4

import Mathlib

open Filter Topology Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

private abbrev UnitInterval := Icc (0:ℝ) 1

set_option maxHeartbeats 1600000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {k : ℕ} [MeasurableSpace C(Icc (0:ℝ) 1, Fin k → ℝ)]
    [BorelSpace C(Icc (0:ℝ) 1, Fin k → ℝ)]
    (X : ℕ → Ω → C(Icc (0:ℝ) 1, Fin k → ℝ)) (hX : ∀ n, Measurable (X n))
    (A : ℝ) (hA : ∀ n ω t, ‖X n ω t‖ ≤ A)
    (hM : ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ > 0, ∀ n,
      P {ω | ∃ s t : Icc (0:ℝ) 1, dist s t ≤ δ ∧ ε ≤ dist (X n ω s) (X n ω t)}
        ≤ ENNReal.ofReal η) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ μ : ProbabilityMeasure C(Icc (0:ℝ) 1,Fin k → ℝ),
      TendstoInDistribution (fun n => X (r n)) atTop
        (id : C(Icc (0:ℝ) 1,Fin k → ℝ) → C(Icc (0:ℝ) 1,Fin k → ℝ))
        (fun _ => P) (μ : Measure C(Icc (0:ℝ) 1,Fin k → ℝ)) := by
  classical
  let E := Fin k → ℝ
  let Law (n : ℕ) : ProbabilityMeasure C(UnitInterval,E) :=
    ⟨P.map (X n),Measure.isProbabilityMeasure_map (hX n).aemeasurable⟩
  let S := range Law
  have hS : IsTightMeasureSet {((μ : ProbabilityMeasure C(UnitInterval,E)) : Measure C(UnitInterval,E)) |
      μ ∈ S} := by
    apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.2
    intro η hη
    obtain ⟨e,_,he,heη⟩ := ENNReal.lt_iff_exists_real_btwn.1 hη
    have he0 := ENNReal.ofReal_pos.1 he
    let u (j : ℕ) := 1/((j:ℝ)+1)
    have hu (j : ℕ) : 0 < u j := by dsimp [u]; positivity
    let w (j : ℕ) := e/2 * ((1/2:ℝ)^j)
    have hw (j : ℕ) : 0 < w j := by dsimp [w]; positivity
    choose δ hδ hδN using fun j => hM (u j) (w j) (hu j) (hw j)
    let F := BoundedContinuousFunction UnitInterval E
    let G : Set F := {f | (∀ s, ‖f s‖ ≤ A) ∧
      ∀ j (s t : UnitInterval), dist s t ≤ δ j → dist (f s) (f t) ≤ u j}
    have hG (_f : F) (_t : UnitInterval) (hf : _f ∈ G) : _f _t ∈ Metric.closedBall (0:E) A := by
      rw [Metric.mem_closedBall,dist_zero_right]
      exact hf.1 _t
    have hEqu : UniformEquicontinuous (fun (f : G) (s : UnitInterval) => f.1 s) := by
      apply Metric.uniformEquicontinuous_iff.2
      intro ε hε
      obtain ⟨j,hj⟩ := exists_nat_gt (1/ε)
      have hSmall : u j < ε := by
        dsimp [u]
        apply (div_lt_iff₀ (by positivity : 0 < (j:ℝ)+1)).2
        have hj0 := (div_lt_iff₀ hε).1 hj
        nlinarith
      exact ⟨δ j,hδ j,fun s t hst f => (f.2.2 j s t hst.le).trans_lt hSmall⟩
    have hCompact : IsCompact (closure G) := BoundedContinuousFunction.arzela_ascoli
      (Metric.closedBall (0:E) A) (isCompact_closedBall _ _) G hG hEqu.equicontinuous
    let eMap : C(UnitInterval,E) ≃ᵢ BoundedContinuousFunction UnitInterval E :=
      ContinuousMap.isometryEquivBoundedOfCompact UnitInterval E
    let K : Set C(UnitInterval,E) := eMap.symm '' closure G
    have hK : IsCompact K := hCompact.image eMap.symm.isometry.continuous
    refine ⟨K,hK,?_⟩
    rintro μ ⟨v,⟨n,rfl⟩,rfl⟩
    change (P.map (X n)) Kᶜ ≤ η
    rw [Measure.map_apply (hX n) hK.isClosed.measurableSet.compl]
    let H (j : ℕ) := {ω | ∃ s t : UnitInterval, dist s t ≤ δ j ∧
      u j ≤ dist (X n ω s) (X n ω t)}
    calc
      _ ≤ P (⋃ j, H j) := by
        apply measure_mono
        intro ω hω
        by_contra! hOutside
        apply hω
        change X n ω ∈ eMap.symm '' closure G
        refine ⟨eMap (X n ω),subset_closure ?_,eMap.symm_apply_apply _⟩
        refine ⟨hA n ω,fun j s t hst => ?_⟩
        change dist (X n ω s) (X n ω t) ≤ u j
        exact (lt_of_not_ge (fun hD => hOutside (mem_iUnion.2 ⟨j,s,t,hst,hD⟩))).le
      _ ≤ ∑' j, P (H j) := measure_iUnion_le _
      _ ≤ ∑' j, ENNReal.ofReal (w j) := ENNReal.tsum_le_tsum (fun j => hδN j n)
      _ = ENNReal.ofReal e := by
        simp_rw [w,ENNReal.ofReal_mul (half_pos he0).le]
        rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg,
          tsum_geometric_two, ← ENNReal.ofReal_mul (half_pos he0).le, div_mul_cancel₀ e two_ne_zero]
        · exact fun _ => by positivity
        · exact summable_geometric_two
      _ ≤ η := heη.le
  have hC := isCompact_closure_of_isTightMeasureSet hS
  obtain ⟨μ,hμ,r,hr,hLim⟩ := hC.isSeqCompact (x := Law) (fun n => subset_closure (mem_range_self n))
  refine ⟨r,hr,μ,fun n => (hX (r n)).aemeasurable,measurable_id.aemeasurable,?_⟩
  have heq : (⟨(μ : Measure C(UnitInterval,E)).map id,
      Measure.isProbabilityMeasure_map measurable_id.aemeasurable⟩ : ProbabilityMeasure C(UnitInterval,E)) = μ :=
    Subtype.ext Measure.map_id
  exact heq.symm ▸ hLim
