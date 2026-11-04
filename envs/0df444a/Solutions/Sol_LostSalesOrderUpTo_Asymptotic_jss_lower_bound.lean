-- Prove2me | solution 1 for LostSalesOrderUpTo.Asymptotic.jss_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T04:48:26.745538+00:00
-- url     : https://prove2.me/submissions/f376c291-247b-4bae-8e26-42aebaacbe2d

import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder
import Theorems.Thm_CappedBaseStock_lower_certificate_bound

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

/-- The lower bound of Janakiraman, Seshadri and Shanthikumar (2005), quoted on p. 13. -/
theorem solution (P : CappedBaseStock.DemandLaw)
    (c : CappedBaseStock.Parameters) :
    ENNReal.ofReal (backorderOptimalCost (leadTimeLaw P c.L) c.h
        (c.p / ((c.L : ℝ) + 1))) ≤ CappedBaseStock.OPT P c := by
  let μ : Measure ℝ≥0 := leadTimeLaw P c.L
  let D : CappedBaseStock.DemandPath → ℝ≥0 :=
    fun d ↦ ∑ i ∈ Finset.range (c.L + 1), d i
  have hD : Measurable D := by
    dsimp only [D]
    fun_prop
  have : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure ((CappedBaseStock.demandPathLaw P).map D)
    exact Measure.isProbabilityMeasure_map hD.aemeasurable
  have heval (i : ℕ) :
      Integrable (fun d : CappedBaseStock.DemandPath ↦ (d i : ℝ))
        (CappedBaseStock.demandPathLaw P) :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ P.law) i).integrable_comp_of_integrable
      P.finiteMean
  have hmean : Integrable (fun d : ℝ≥0 ↦ (d : ℝ)) μ := by
    change Integrable (fun d : ℝ≥0 ↦ (d : ℝ))
      ((CappedBaseStock.demandPathLaw P).map D)
    apply (integrable_map_measure (g := fun d : ℝ≥0 ↦ (d : ℝ))
      (by fun_prop) hD.aemeasurable).2
    change Integrable (fun d : CappedBaseStock.DemandPath ↦
      ((∑ i ∈ Finset.range (c.L + 1), d i : ℝ≥0) : ℝ))
      (CappedBaseStock.demandPathLaw P)
    simp only [NNReal.coe_sum]
    exact integrable_finsetSum _ (fun i _ ↦ heval i)
  have hmean_eq : (∫ d : ℝ≥0, (d : ℝ) ∂μ) =
      ((c.L : ℝ) + 1) * CappedBaseStock.mean P := by
    change (∫ d : ℝ≥0, (d : ℝ)
      ∂((CappedBaseStock.demandPathLaw P).map D)) = _
    rw [integral_map hD.aemeasurable (by fun_prop)]
    simp only [D, NNReal.coe_sum]
    rw [integral_finsetSum _ (fun i _ ↦ heval i)]
    have hi (i : ℕ) :
        (∫ d : CappedBaseStock.DemandPath, (d i : ℝ)
          ∂CappedBaseStock.demandPathLaw P) = CappedBaseStock.mean P := by
      have hp := measurePreserving_eval_infinitePi (fun _ : ℕ ↦ P.law) i
      calc
        _ = ∫ x : ℝ≥0, (x : ℝ)
            ∂((CappedBaseStock.demandPathLaw P).map (fun d ↦ d i)) :=
          (integral_map hp.measurable.aemeasurable (by fun_prop)).symm
        _ = CappedBaseStock.mean P := by
          change (∫ x : ℝ≥0, (x : ℝ)
            ∂Measure.map (Function.eval i) (Measure.infinitePi (fun _ : ℕ ↦ P.law))) = _
          rw [hp.map_eq]
          rfl
    simp only [hi, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one]
  have hL : 0 < (c.L : ℝ) + 1 := by positivity
  have hb : 0 ≤ c.p / ((c.L : ℝ) + 1) := div_nonneg c.penalty_pos.le hL.le
  have hcost_nonneg (S : ℝ≥0) :
      0 ≤ backorderCost μ c.h (c.p / ((c.L : ℝ) + 1)) S :=
    add_nonneg
      (mul_nonneg c.holding_pos.le (integral_nonneg fun _ ↦ le_max_right _ _))
      (mul_nonneg hb (integral_nonneg fun _ ↦ le_max_right _ _))
  have hcertificate : ENNReal.ofReal
      (backorderOptimalCost μ c.h (c.p / ((c.L : ℝ) + 1))) ≤
        CappedBaseStock.lowerCertificate P c := by
    unfold CappedBaseStock.lowerCertificate
    refine le_iInf fun rz ↦ ?_
    obtain ⟨hr, hrmean, hz, _, hwindow⟩ := rz.property
    let r : ℝ := rz.val.1
    let z : ℝ := rz.val.2
    let S : ℝ≥0 := ⟨((c.L : ℝ) + 1) * r + z,
      add_nonneg (mul_nonneg hL.le hr) hz⟩
    have hshort_le : expectedShortfall μ S ≤
        ((c.L : ℝ) + 1) * (CappedBaseStock.mean P - r) := by
      apply (ENNReal.ofReal_le_ofReal_iff
        (mul_nonneg hL.le (sub_nonneg.mpr hrmean))).1
      have hshort_integrable :
          Integrable (fun d : ℝ≥0 ↦ max ((d : ℝ) - (S : ℝ)) 0) μ :=
        (hmean.sub (integrable_const _)).pos_part
      calc
        ENNReal.ofReal (expectedShortfall μ S) =
            ∫⁻ d : ℝ≥0, ENNReal.ofReal (max ((d : ℝ) - (S : ℝ)) 0) ∂μ :=
          ofReal_integral_eq_lintegral_ofReal hshort_integrable
            (Eventually.of_forall fun _ ↦ le_max_right _ _)
        _ = ∫⁻ d, ENNReal.ofReal (max ((D d : ℝ) - (S : ℝ)) 0)
            ∂CappedBaseStock.demandPathLaw P :=
          lintegral_map (by fun_prop) hD
        _ ≤ ∫⁻ d, CappedBaseStock.certificateExcess d r z (c.L + 1)
            ∂CappedBaseStock.demandPathLaw P := by
          apply lintegral_mono
          intro d
          have hinv : 0 ≤ CappedBaseStock.finiteInventory d r (c.L + 1) := by
            unfold CappedBaseStock.finiteInventory
            exact Finset.le_sup'_of_le _ (by simp : 0 ∈ Finset.range (c.L + 1 + 1))
              (by simp)
          have hraw : (D d : ℝ) - (S : ℝ) ≤
              CappedBaseStock.finiteInventory d r (c.L + 1) +
                (∑ i ∈ Finset.range (c.L + 1), ((d i : ℝ) - r)) - z := by
            change ((∑ i ∈ Finset.range (c.L + 1), d i : ℝ≥0) : ℝ) -
              (((c.L : ℝ) + 1) * r + z) ≤ _
            simp only [NNReal.coe_sum, Finset.sum_sub_distrib, Finset.sum_const,
              Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
            linarith only [hinv]
          calc
            _ = ENNReal.ofReal ((D d : ℝ) - (S : ℝ)) := by simp
            _ ≤ _ := ENNReal.ofReal_le_ofReal hraw
        _ ≤ ENNReal.ofReal (((c.L : ℝ) + 1) * (CappedBaseStock.mean P - r)) :=
          hwindow
    have hbalance : expectedShortfall μ S - expectedHolding μ S =
        ((c.L : ℝ) + 1) * CappedBaseStock.mean P - (S : ℝ) := by
      have hp : Integrable (fun d : ℝ≥0 ↦ max ((d : ℝ) - (S : ℝ)) 0) μ :=
        (hmean.sub (integrable_const _)).pos_part
      have hm : Integrable (fun d : ℝ≥0 ↦ max ((S : ℝ) - (d : ℝ)) 0) μ :=
        ((integrable_const _).sub hmean).pos_part
      have hparts (d : ℝ≥0) :
          max ((d : ℝ) - (S : ℝ)) 0 - max ((S : ℝ) - (d : ℝ)) 0 =
            (d : ℝ) - (S : ℝ) := by
        simpa only [neg_sub] using max_zero_sub_max_neg_zero_eq_self ((d : ℝ) - (S : ℝ))
      unfold expectedShortfall expectedHolding
      rw [← integral_sub hp hm]
      simp_rw [hparts]
      rw [integral_sub hmean (integrable_const _), hmean_eq]
      simp
    have hholding_le : expectedHolding μ S ≤ z := by
      have hS : (S : ℝ) = ((c.L : ℝ) + 1) * r + z := rfl
      rw [hS] at hbalance
      linarith only [hbalance, hshort_le]
    have hcost_le : backorderCost μ c.h (c.p / ((c.L : ℝ) + 1)) S ≤
        c.h * z + c.p * (CappedBaseStock.mean P - r) := by
      calc
        _ ≤ c.h * z + (c.p / ((c.L : ℝ) + 1)) *
            (((c.L : ℝ) + 1) * (CappedBaseStock.mean P - r)) :=
          add_le_add (mul_le_mul_of_nonneg_left hholding_le c.holding_pos.le)
            (mul_le_mul_of_nonneg_left hshort_le hb)
        _ = _ := by field_simp [hL.ne']
    have hopt_le : backorderOptimalCost μ c.h (c.p / ((c.L : ℝ) + 1)) ≤
        backorderCost μ c.h (c.p / ((c.L : ℝ) + 1)) S := by
      apply csInf_le
      · exact ⟨0, by rintro _ ⟨T, rfl⟩; exact hcost_nonneg T⟩
      · exact ⟨S, rfl⟩
    exact ENNReal.ofReal_le_ofReal (hopt_le.trans hcost_le)
  exact hcertificate.trans (CappedBaseStock.lower_certificate_bound P c)
