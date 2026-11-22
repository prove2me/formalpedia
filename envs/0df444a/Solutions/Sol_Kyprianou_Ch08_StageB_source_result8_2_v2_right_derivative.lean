-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_2_v2_right_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:44:52.673801+00:00
-- url     : https://prove2.me/submissions/238b93e1-a4a1-4439-b6c8-800e6fdaa459

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch08 Kyprianou.Ch08.StageB

private lemma tendsto_openTail_right {n : Measure ℝ} {x : ℝ} (hfin : n (Set.Ici x) < ⊤) :
    Tendsto (fun t => (n (Set.Ici t)).toReal) (𝓝[>] x) (𝓝 ((n (Set.Ioi x)).toReal)) := by
  have hmono : Antitone (fun t : ℝ => n (Set.Ici t)) := fun a b hab => measure_mono (fun y hy => mem_Ici.2 (le_trans hab (mem_Ici.1 hy)))
  have hUnion : (⋃ k : ℕ, Set.Ici (x + 1 / ((k : ℝ) + 1))) = Set.Ioi x := by
    ext y
    constructor
    · intro hy
      obtain ⟨k, hky⟩ := Set.mem_iUnion.1 hy
      have h1 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      have h2 := mem_Ici.1 hky
      exact mem_Ioi.2 (by linarith)
    · intro hy
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr (mem_Ioi.1 hy))
      have hk' : (1 : ℝ) / ((k : ℝ) + 1) < y - x := by simpa using hk
      exact Set.mem_iUnion.2 ⟨k, mem_Ici.2 (by linarith)⟩
  have htm : Tendsto (fun t : ℝ => n (Set.Ici t)) (𝓝[>] x) (𝓝 (n (Set.Ioi x))) := by
    refine tendsto_order.2 ⟨fun z hz => ?_, fun z hz => ?_⟩
    · have hmonoseq : Monotone (fun k : ℕ => Set.Ici (x + 1 / ((k : ℝ) + 1))) := by
        intro a b hab
        refine Ici_subset_Ici.mpr ?_
        have ha : (0 : ℝ) < (a : ℝ) + 1 := by positivity
        have hle : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hab 1
        have hdiv := one_div_le_one_div_of_le ha hle
        linarith
      have htend := MeasureTheory.tendsto_measure_iUnion_atTop (μ := n) hmonoseq
      beta_reduce at htend
      rw [hUnion] at htend
      obtain ⟨k, hkev⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 htend).1 z hz)
      have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      have hxsk : x < x + 1 / ((k : ℝ) + 1) := by linarith
      filter_upwards [Ioo_mem_nhdsGT hxsk] with t ht
      exact lt_of_lt_of_le (hkev k le_rfl) (hmono (le_of_lt ht.2))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact lt_of_le_of_lt (measure_mono (fun y hy => mem_Ioi.2 (lt_of_lt_of_le ht (mem_Ici.1 hy)))) hz
  have hIoi_ne : n (Set.Ioi x) ≠ ⊤ := ne_top_of_le_ne_top hfin.ne (measure_mono (fun y hy => mem_Ici.2 (le_of_lt (mem_Ioi.1 hy))))
  exact (ENNReal.tendsto_toReal hIoi_ne).comp htm

private lemma w_hasDeriv_of_raw {ψ : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {q : ℝ} {n : Measure ℝ} {x : ℝ}
    (hWraw : HasDerivWithinAt (fun y => W q x * Real.exp (∫ t in x..y, Phi ψ q + (n (Set.Ici t)).toReal)) (W q x * (Phi ψ q + (n (Set.Ioi x)).toReal)) (Set.Ici x) x)
    (hRep : HasQExcursionScaleRepresentation ψ q (W q) n) (hx : 0 < x) (hxa0 : x < x + 1)
    (hWx : W q x = W q (x + 1) * Real.exp (-(∫ t in x..x + 1, Phi ψ q + (n (Set.Ici t)).toReal))) :
    HasDerivWithinAt (W q) (W q x * (Phi ψ q + (n (Set.Ioi x)).toReal)) (Set.Ici x) x := by
  refine hWraw.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [Ico_mem_nhdsGE hxa0] with y hy
    rcases eq_or_lt_of_le hy.1 with rfl | hxy
    · simp [intervalIntegral.integral_same, Real.exp_zero]
    · show W q y = W q x * Real.exp (∫ t in x..y, Phi ψ q + (n (Set.Ici t)).toReal)
      have hy_pos : 0 < y := lt_trans hx hxy
      have hWy : W q y = W q (x + 1) * Real.exp (-(∫ t in y..x + 1, Phi ψ q + (n (Set.Ici t)).toReal)) := (hRep.2 y (x + 1) hy_pos hy.2).2
      have h1 : IntervalIntegrable (fun t => Phi ψ q + (n (Set.Ici t)).toReal) volume x y := (intervalIntegrable_iff_integrableOn_Icc_of_le hxy.le).2 ((hRep.2 x y hx hxy).1)
      have h2 : IntervalIntegrable (fun t => Phi ψ q + (n (Set.Ici t)).toReal) volume y (x + 1) := (intervalIntegrable_iff_integrableOn_Icc_of_le hy.2.le).2 ((hRep.2 y (x + 1) hy_pos hy.2).1)
      have hsplit : (∫ t in x..x + 1, Phi ψ q + (n (Set.Ici t)).toReal) = (∫ t in x..y, Phi ψ q + (n (Set.Ici t)).toReal) + (∫ t in y..x + 1, Phi ψ q + (n (Set.Ici t)).toReal) := (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
      have hexp : Real.exp (-((∫ t in x..y, Phi ψ q + (n (Set.Ici t)).toReal) + (∫ t in y..x + 1, Phi ψ q + (n (Set.Ici t)).toReal))) * Real.exp (∫ t in x..y, Phi ψ q + (n (Set.Ici t)).toReal) = Real.exp (-(∫ t in y..x + 1, Phi ψ q + (n (Set.Ici t)).toReal)) := by rw [← Real.exp_add]; congr 1; ring
      rw [hWy, hWx, hsplit, mul_assoc, hexp]
  · simp [intervalIntegral.integral_same, Real.exp_zero]

theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (q : ℝ) (n : Measure ℝ)
    (hLaw : HasActualQExcursionHeightLaw P D ψ q n) (hRep : HasQExcursionScaleRepresentation ψ q (W q) n) :
    ∀ x : ℝ, 0 < x → ∃ dRight : ℝ, HasDerivWithinAt (W q) dRight (Set.Ici x) x ∧
      dRight = (Phi ψ q + (n (Set.Ioi x)).toReal) * W q x := by
  intro x hx
  have hTail : ∀ h : ℝ, 0 < h → n (Set.Ici h) < ⊤ := fun h hh => (hLaw.2 1 h one_pos hh).1
  have hcoeff : Tendsto (fun t => Phi ψ q + (n (Set.Ici t)).toReal) (𝓝[>] x) (𝓝 (Phi ψ q + (n (Set.Ioi x)).toReal)) := tendsto_const_nhds.add (tendsto_openTail_right (hTail x hx))
  have hxa0 : x < x + 1 := by linarith
  have hInt_a0 : IntegrableOn (fun t => Phi ψ q + (n (Set.Ici t)).toReal) (Set.Icc x (x + 1)) volume := (hRep.2 x (x + 1) hx hxa0).1
  have hWx : W q x = W q (x + 1) * Real.exp (-(∫ t in x..x + 1, Phi ψ q + (n (Set.Ici t)).toReal)) := (hRep.2 x (x + 1) hx hxa0).2
  have hmeas : StronglyMeasurableAtFilter (fun t => Phi ψ q + (n (Set.Ici t)).toReal) (𝓝[>] x) volume := AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem (Integrable.aestronglyMeasurable hInt_a0) (mem_of_superset (Ioo_mem_nhdsGT hxa0) (fun y hy => mem_Icc.2 ⟨le_of_lt hy.1, le_of_lt hy.2⟩))
  have hF : HasDerivWithinAt (fun y => ∫ t in x..y, Phi ψ q + (n (Set.Ici t)).toReal) (Phi ψ q + (n (Set.Ioi x)).toReal) (Set.Ici x) x := intervalIntegral.integral_hasDerivWithinAt_of_tendsto_ae_right IntervalIntegrable.refl hmeas (hcoeff.mono_left inf_le_left)
  have hExp : HasDerivWithinAt (fun y => Real.exp (∫ t in x..y, Phi ψ q + (n (Set.Ici t)).toReal)) (Phi ψ q + (n (Set.Ioi x)).toReal) (Set.Ici x) x := by simpa [intervalIntegral.integral_same, Real.exp_zero] using hF.exp
  have hWraw : HasDerivWithinAt (fun y => W q x * Real.exp (∫ t in x..y, Phi ψ q + (n (Set.Ici t)).toReal)) (W q x * (Phi ψ q + (n (Set.Ioi x)).toReal)) (Set.Ici x) x := hExp.const_mul (W q x)
  have hW : HasDerivWithinAt (W q) (W q x * (Phi ψ q + (n (Set.Ioi x)).toReal)) (Set.Ici x) x := w_hasDeriv_of_raw hWraw hRep hx hxa0 hWx
  exact ⟨W q x * (Phi ψ q + (n (Set.Ioi x)).toReal), hW, by ring⟩
