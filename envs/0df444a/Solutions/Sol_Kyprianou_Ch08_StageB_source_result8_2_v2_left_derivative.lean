-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_2_v2_left_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T18:19:12.943282+00:00
-- url     : https://prove2.me/submissions/e17a5f4c-550f-417c-a416-4aeb6170d493

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open Kyprianou.Ch08 Kyprianou.Ch08.StageB

private lemma tendsto_closedTail_left {n : Measure ℝ} {x : ℝ} (hx : 0 < x)
    (hTail : ∀ h : ℝ, 0 < h → n (Set.Ici h) < ⊤) :
    Tendsto (fun t => (n (Set.Ici t)).toReal) (𝓝[≤] x) (𝓝 ((n (Set.Ici x)).toReal)) := by
  have hfin : n (Set.Ici x) < ⊤ := hTail x hx
  have hmono : Antitone (fun t : ℝ => n (Set.Ici t)) :=
    fun a b hab => measure_mono (fun y hy => mem_Ici.2 (le_trans hab (mem_Ici.1 hy)))
  have hInter : (⋂ k : ℕ, Set.Ici (x - 1 / ((k : ℝ) + 1))) = Set.Ici x := by
    ext y
    constructor
    · intro hy
      by_contra hlt
      have hlt' : y < x := lt_of_not_ge fun h => hlt (mem_Ici.2 h)
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt')
      have hk' : (1 : ℝ) / ((k : ℝ) + 1) < x - y := by simpa using hk
      have hyk := mem_Ici.1 (Set.mem_iInter.1 hy k)
      linarith
    · intro hy
      refine Set.mem_iInter.2 fun k => mem_Ici.2 (by have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := (by positivity); linarith [mem_Ici.1 hy])
  have htm : Tendsto (fun t : ℝ => n (Set.Ici t)) (𝓝[≤] x) (𝓝 (n (Set.Ici x))) := by
    refine tendsto_order.2 ⟨fun z hz => ?_, fun z hz => ?_⟩
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact hz.trans_le (hmono ht)
    · have hanti : Antitone (fun k : ℕ => Set.Ici (x - 1 / ((k : ℝ) + 1))) := by
        intro a b hab
        refine Ici_subset_Ici.mpr ?_
        have ha : (0 : ℝ) < (a : ℝ) + 1 := by positivity
        have hab' : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hab 1
        have hdiv := one_div_le_one_div_of_le ha hab'
        linarith
      have hmeas : ∀ k : ℕ, NullMeasurableSet (Set.Ici (x - 1 / ((k : ℝ) + 1))) n :=
        fun k => measurableSet_Ici.nullMeasurableSet
      obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt hx
      have hfin' : ∃ (k : ℕ), n (Set.Ici (x - 1 / ((k : ℝ) + 1))) ≠ ⊤ :=
        ⟨k₀, (hTail _ (sub_pos.mpr (by simpa using hk₀))).ne⟩
      have htend := MeasureTheory.tendsto_measure_iInter_atTop hmeas hanti hfin'
      beta_reduce at htend
      rw [hInter] at htend
      have hev := (tendsto_order.1 htend).2 z hz
      obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 hev
      have hδ : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      filter_upwards [Ioc_mem_nhdsLE (sub_lt_self x hδ)] with t ht
      exact lt_of_le_of_lt (hmono (le_of_lt ht.1)) (hk k le_rfl)
  exact (ENNReal.tendsto_toReal hfin.ne).comp htm

private lemma w_hasDeriv_of_raw_left {ψ : ℝ → ℝ} {W : ℝ → ℝ → ℝ} {q : ℝ} {n : Measure ℝ} {x : ℝ}
    (hWraw : HasDerivWithinAt (fun y => W q x * Real.exp (∫ t in x..y, Phi ψ q + (n (Set.Ici t)).toReal)) (W q x * (Phi ψ q + (n (Set.Ici x)).toReal)) (Set.Iic x) x)
    (hRep : HasQExcursionScaleRepresentation ψ q (W q) n) (hx : 0 < x)
    (ha0pos : 0 < x / 2) (ha0lt : x / 2 < x) :
    HasDerivWithinAt (W q) (W q x * (Phi ψ q + (n (Set.Ici x)).toReal)) (Set.Iic x) x := by
  refine hWraw.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [Ioc_mem_nhdsLE ha0lt] with y hy
    rcases eq_or_lt_of_le hy.2 with rfl | hxy
    · simp [intervalIntegral.integral_same, Real.exp_zero]
    · show W q y = W q x * Real.exp (∫ t in x..y, Phi ψ q + (n (Set.Ici t)).toReal)
      have hWy : W q y = W q x * Real.exp (-(∫ t in y..x, Phi ψ q + (n (Set.Ici t)).toReal)) :=
        (hRep.2 y x (lt_trans ha0pos hy.1) hxy).2
      rw [hWy, intervalIntegral.integral_symm y x]
  · simp [intervalIntegral.integral_same, Real.exp_zero]

theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (q : ℝ) (n : Measure ℝ)
    (hLaw : HasActualQExcursionHeightLaw P D ψ q n) (hRep : HasQExcursionScaleRepresentation ψ q (W q) n) :
    ∀ x : ℝ, 0 < x → ∃ dLeft : ℝ, HasDerivWithinAt (W q) dLeft (Set.Iic x) x ∧
      dLeft = (Phi ψ q + (n (Set.Ici x)).toReal) * W q x := by
  intro x hx
  have hTail : ∀ h : ℝ, 0 < h → n (Set.Ici h) < ⊤ := fun h hh => (hLaw.2 1 h one_pos hh).1
  have hcoeff : Tendsto (fun t => Phi ψ q + (n (Set.Ici t)).toReal) (𝓝[≤] x) (𝓝 (Phi ψ q + (n (Set.Ici x)).toReal)) :=
    tendsto_const_nhds.add (tendsto_closedTail_left hx hTail)
  have ha0pos : 0 < x / 2 := by linarith
  have ha0lt : x / 2 < x := by linarith
  have hInt_a0 : IntegrableOn (fun t => Phi ψ q + (n (Set.Ici t)).toReal) (Set.Icc (x / 2) x) volume :=
    (hRep.2 (x / 2) x ha0pos ha0lt).1
  have hmeas : StronglyMeasurableAtFilter (fun t => Phi ψ q + (n (Set.Ici t)).toReal) (𝓝[≤] x) volume :=
    AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem (Integrable.aestronglyMeasurable hInt_a0)
      (mem_of_superset (Ioc_mem_nhdsLE ha0lt) (fun y hy => mem_Icc.2 ⟨le_of_lt hy.1, hy.2⟩))
  have hF0 : HasDerivWithinAt (fun u => ∫ t in u..x, Phi ψ q + (n (Set.Ici t)).toReal)
      (-(Phi ψ q + (n (Set.Ici x)).toReal)) (Set.Iic x) x :=
    intervalIntegral.integral_hasDerivWithinAt_of_tendsto_ae_left IntervalIntegrable.refl hmeas
      (hcoeff.mono_left inf_le_left)
  have hF : HasDerivWithinAt (fun y => ∫ t in x..y, Phi ψ q + (n (Set.Ici t)).toReal)
      (Phi ψ q + (n (Set.Ici x)).toReal) (Set.Iic x) x := by
    have hneg := hF0.neg
    rw [neg_neg] at hneg
    have hfun : (fun y => ∫ t in x..y, Phi ψ q + (n (Set.Ici t)).toReal) = (fun y => -(∫ t in y..x, Phi ψ q + (n (Set.Ici t)).toReal)) := funext fun y => intervalIntegral.integral_symm y x
    rw [hfun]
    exact hneg
  have hExp : HasDerivWithinAt (fun y => Real.exp (∫ t in x..y, Phi ψ q + (n (Set.Ici t)).toReal))
      (Phi ψ q + (n (Set.Ici x)).toReal) (Set.Iic x) x := by
    simpa [intervalIntegral.integral_same, Real.exp_zero] using hF.exp
  have hWraw : HasDerivWithinAt (fun y => W q x * Real.exp (∫ t in x..y, Phi ψ q + (n (Set.Ici t)).toReal))
      (W q x * (Phi ψ q + (n (Set.Ici x)).toReal)) (Set.Iic x) x :=
    hExp.const_mul (W q x)
  have hW : HasDerivWithinAt (W q) (W q x * (Phi ψ q + (n (Set.Ici x)).toReal)) (Set.Iic x) x :=
    w_hasDeriv_of_raw_left hWraw hRep hx ha0pos ha0lt
  exact ⟨W q x * (Phi ψ q + (n (Set.Ici x)).toReal), hW, by ring⟩
