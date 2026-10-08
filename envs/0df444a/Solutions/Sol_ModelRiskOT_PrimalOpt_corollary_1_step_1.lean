-- Prove2me | solution 1 for ModelRiskOT.PrimalOpt.corollary_1_step_1
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T02:26:05.803978+00:00
-- url     : https://prove2.me/submissions/b0d1a0bd-0dc8-49e2-be1d-9a8eb16b0f82

import Definitions.Def_ModelRiskOT_PrimalOpt_GrowthAssumptions
import Definitions.Def_ModelRiskOT_PrimalOpt_PCompactness

set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal
namespace PrimalOptCodex
open ModelRiskOT.PrimalOpt

lemma nominal_le_primal_phi {E : Type*} [TopologicalSpace E]
    (c : E → E → ℝ) (hc : ModelRiskOT.Duality.AssumptionA1 c)
    (f : E → ℝ) (lam : ℝ) (x : E) : (f x : EReal) ≤ phiLam c f lam x := by
  have h : (f x : EReal) - ((lam*c x x : ℝ) : EReal) ≤ phiLam c f lam x :=
    le_iSup_of_le x le_rfl
  simpa [(hc.eq_zero_iff x x).mpr rfl] using h

lemma gamma_displacement_bounded {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : E → E → ℝ) (f : E → ℝ) (hA1 : ModelRiskOT.Duality.AssumptionA1 c)
    (hA3 : AssumptionA3 c) (hA4 : AssumptionA4 c f) (lam : ℝ) (hlam : 0 < lam) :
    ∃ R : ℝ, 0 < R ∧ ∀ K : Set E, ∀ p ∈ gammaSet c f lam K 1, ‖p.1-p.2‖ ≤ R := by
  obtain ⟨g,_,_,hg,C,hC,hgrow⟩ := hA3
  obtain ⟨Cf,hCf,hgain⟩ := hA4.2 (lam/2) (half_pos hlam)
  have he : ∀ᶠ z : ℝ in atTop, 2+2/lam ≤ g z :=
    hg.eventually (eventually_ge_atTop (2+2/lam))
  obtain ⟨r,hr⟩ := eventually_atTop.1 he
  let R := max (max C Cf) (max r 1)
  refine ⟨R,?_,?_⟩
  · have h : 1 ≤ R := (le_max_right r 1).trans (le_max_right _ _)
    linarith
  · intro K p hp
    by_contra hh
    have hn : R < ‖p.1-p.2‖ := lt_of_not_ge hh
    have hc : C < ‖p.1-p.2‖ := lt_of_le_of_lt
      ((le_max_left C Cf).trans (le_max_left _ _)) hn
    have hf : Cf < ‖p.1-p.2‖ := lt_of_le_of_lt
      ((le_max_right C Cf).trans (le_max_left _ _)) hn
    have hrr : r ≤ ‖p.1-p.2‖ := ((le_max_left r 1).trans (le_max_right _ _)).trans hn.le
    have hcost := (hr _ hrr).trans (hgrow p.1 p.2 hc)
    have hpay := hgain p.1 p.2 hf
    have hlow : ((f p.1-1 : ℝ) : EReal) ≤ ((f p.2-lam*c p.1 p.2 : ℝ) : EReal) := by
      rw [EReal.coe_sub]
      exact (EReal.sub_le_sub (nominal_le_primal_phi c hA1 f lam p.1) (le_refl (1 : EReal))).trans hp.2
    have hv := EReal.coe_le_coe_iff.mp hlow
    have heq : (2/lam)*lam = 2 := div_mul_cancel₀ _ (ne_of_gt hlam)
    have hm := mul_le_mul_of_nonneg_left hcost hlam.le
    nlinarith

lemma gamma_closure_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [LocallyCompactSpace E] (c : E → E → ℝ) (f : E → ℝ)
    (hA1 : ModelRiskOT.Duality.AssumptionA1 c) (hA3 : AssumptionA3 c)
    (hA4 : AssumptionA4 c f) (lam : ℝ) (hlam : 0 < lam)
    (K : Set E) (hK : IsCompact K) : IsCompact (closure (gammaSet c f lam K 1)) := by
  letI : ProperSpace E := ProperSpace.of_locallyCompactSpace ℝ
  obtain ⟨R,hR,hbound⟩ := gamma_displacement_bounded c f hA1 hA3 hA4 lam hlam
  obtain ⟨r,_,hr⟩ := hK.isBounded.exists_pos_norm_le
  have hs : gammaSet c f lam K 1 ⊆ K ×ˢ Metric.closedBall (0 : E) (r+R) := by
    intro p hp
    refine ⟨hp.1,?_⟩
    rw [Metric.mem_closedBall,dist_zero_right]
    have ht : ‖p.2‖ ≤ ‖p.1‖ + ‖p.1-p.2‖ := by
      have h := norm_sub_le p.1 (p.1-p.2)
      simpa only [sub_sub_cancel] using h
    exact ht.trans (add_le_add (hr p.1 hp.1) (hbound K p hp))
  apply (hK.prod (isCompact_closedBall (0 : E) (r+R))).of_isClosed_subset isClosed_closure
  exact (hK.isClosed.prod Metric.isClosed_closedBall).closure_subset_iff.mpr hs

lemma growth_compactness_complete {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [LocallyCompactSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
    (c : E → E → ℝ) (f : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (hA1 : ModelRiskOT.Duality.AssumptionA1 c) (hA3 : AssumptionA3 c)
    (hA4 : AssumptionA4 c f) (lam : ℝ) (hlam : 0 < lam) : PCompactness c f μ lam := by
  intro ε hε
  obtain ⟨K,_,hK,hμK⟩ := (MeasurableSet.univ : MeasurableSet (Set.univ : Set E)).exists_isCompact_lt_add
    (measure_ne_top μ _) (ne_of_gt (ENNReal.ofReal_pos.mpr hε))
  have he : 1 < μ K + ENNReal.ofReal ε := by simpa using hμK
  have hfin : μ K + ENNReal.ofReal ε ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨measure_ne_top μ _,ENNReal.ofReal_ne_top⟩
  have hh := (ENNReal.toReal_lt_toReal (by simp : (1 : ENNReal) ≠ ∞) hfin).mpr he
  rw [ENNReal.toReal_one,ENNReal.toReal_add (measure_ne_top μ _) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hε.le] at hh
  refine ⟨K,hK,by linarith,1,by norm_num,?_⟩
  exact gamma_closure_compact c f hA1 hA3 hA4 lam hlam K hK

end PrimalOptCodex



set_option autoImplicit false
open MeasureTheory ModelRiskOT.PrimalOpt
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [LocallyCompactSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
    (c : E → E → ℝ) (f : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (hA1 : ModelRiskOT.Duality.AssumptionA1 c) (hA2 : AssumptionA2 f μ) (hA3 : AssumptionA3 c)
    (hA4 : AssumptionA4 c f) (lam : ℝ) (hlam : 0 < lam) :
    PCompactness c f μ lam := by
  exact PrimalOptCodex.growth_compactness_complete c f μ hA1 hA3 hA4 lam hlam

#print axioms solution
