-- Prove2me | solution 1 for Hermite1DimdLEAN.localizationIncludingZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:34:29.931675+00:00
-- url     : https://prove2.me/submissions/aec57ef8-2903-4321-a6f9-52f2bc336ccc

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_BasisLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_ImportedAnalyticInputs
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Theorems.Thm_Hermite1DimdLEAN_oneVariableLocalization
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_phi0_localization
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
namespace Hermite1DimdLEAN
private lemma measurable_ofReal_gaussianDensity (d : ℕ) :
    Measurable (fun z : CSpace d => ENNReal.ofReal (gaussianDensity d z)) := by
  unfold gaussianDensity
  fun_prop
private lemma gaussianDensity_ofReal_lt_top (d : ℕ) :
    ∀ᵐ x : CSpace d, ENNReal.ofReal (gaussianDensity d x) < ⊤ := by
  simp_all
private lemma toReal_gaussianDensity_one (z : CSpace 1) :
    (ENNReal.ofReal (gaussianDensity 1 z)).toReal =
      (1 / Real.pi) * Real.exp (-‖z 0‖ ^ 2) := by
  have hnonneg : 0 ≤ Real.pi⁻¹ * Real.exp (-‖z 0‖ ^ 2) := by positivity
  simp [gaussianDensity, hnonneg]
private lemma measurableSet_complex_annulus
    (j : ℕ) :
    MeasurableSet (HermiteLEAN.annulus j) := by
  have hge : MeasurableSet {z : ℂ | (j : ℝ) ≤ ‖z‖} :=
    measurableSet_le measurable_const measurable_norm
  have hlt : MeasurableSet {z : ℂ | ‖z‖ < (j : ℝ) + 1} :=
    measurableSet_lt measurable_norm measurable_const
  simpa [HermiteLEAN.annulus, Set.ofPred_and] using hge.inter hlt
private theorem annulusMass_oneDimPhi_eq_annulusIntegralSq
    (k n j : ℕ) :
    annulusMass (d := 1) (fun _ => j) (oneDimLift (oneDimPhi k n)) =
      HermitekLEAN.annulusIntegralSq (HermitekLEAN.Phi k n) j := by
  classical
  change
    annulusMass (d := 1) (fun _ => j) (fun z => HermitekLEAN.Phi k n (z 0)) =
      HermitekLEAN.annulusIntegralSq (HermitekLEAN.Phi k n) j
  unfold annulusMass HermitekLEAN.annulusIntegralSq HermiteLEAN.annulusIntegralSq
  rw [gaussianMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_ofReal_gaussianDensity 1) (gaussianDensity_ofReal_lt_top 1)]
  calc
    ∫ z : CSpace 1,
        (ENNReal.ofReal (gaussianDensity 1 z)).toReal •
          (if z ∈ productAnnulus (d := 1) (fun _ => j) then ‖HermitekLEAN.Phi k n (z 0)‖ ^ 2 else 0)
          ∂(volume : Measure (CSpace 1))
        =
      ∫ z : CSpace 1,
        ((1 / Real.pi) * Real.exp (-‖z 0‖ ^ 2)) *
          (if z ∈ productAnnulus (d := 1) (fun _ => j) then ‖HermitekLEAN.Phi k n (z 0)‖ ^ 2 else 0)
          ∂(volume : Measure (CSpace 1)) := by
          apply integral_congr_ae
          filter_upwards with z
          rw [toReal_gaussianDensity_one z]
          simp [smul_eq_mul]
    _ =
      (1 / Real.pi) *
        ∫ z : CSpace 1,
          if z ∈ productAnnulus (d := 1) (fun _ => j) then
            ‖HermitekLEAN.Phi k n (z 0)‖ ^ 2 * Real.exp (-‖z 0‖ ^ 2)
          else 0 ∂(volume : Measure (CSpace 1)) := by
          have hrew :
              ∫ z : CSpace 1,
                ((1 / Real.pi) * Real.exp (-‖z 0‖ ^ 2)) *
                  (if z ∈ productAnnulus (d := 1) (fun _ => j) then ‖HermitekLEAN.Phi k n (z 0)‖ ^
                      2 else 0)
                  ∂(volume : Measure (CSpace 1)) =
              ∫ z : CSpace 1,
                (1 / Real.pi) *
                  (if z ∈ productAnnulus (d := 1) (fun _ => j) then
                    ‖HermitekLEAN.Phi k n (z 0)‖ ^ 2 * Real.exp (-‖z 0‖ ^ 2)
                  else 0) ∂(volume : Measure (CSpace 1)) := by
                apply integral_congr_ae
                filter_upwards with z
                by_cases hz : z ∈ productAnnulus (d := 1) (fun _ => j) <;> simp [hz,
                    mul_left_comm, mul_comm]
          exact hrew.trans (MeasureTheory.integral_const_mul _ _)
    _ =
      (1 / Real.pi) *
        ∫ z : ℂ,
          if z ∈ HermiteLEAN.annulus j then
            ‖HermitekLEAN.Phi k n z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
          else 0 ∂(volume : Measure ℂ) := by
          let e : CSpace 1 ≃ᵐ ℂ := MeasurableEquiv.funUnique (Fin 1) ℂ
          have hEq0 :=
            ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℂ).integral_comp'
              (f := e)
              (fun z : ℂ =>
                if z ∈ HermiteLEAN.annulus j then
                  ‖HermitekLEAN.Phi k n z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
                else 0))
          have he : ∀ z : CSpace 1, e z = z 0 := fun _ => rfl
          have h := congrArg ((1 / Real.pi) * ·) hEq0
          simp only [productAnnulus, HermiteLEAN.annulus, he, Set.mem_ofPred_eq,
            Fin.forall_fin_one, Nat.cast_add, Nat.cast_one] at h ⊢
          exact h
    _ =
      (1 / Real.pi) *
        ∫ z in HermiteLEAN.annulus j,
          ‖HermitekLEAN.Phi k n z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ∂(volume : Measure ℂ) := by
          congr 1
          rw [← MeasureTheory.integral_indicator (measurableSet_complex_annulus j)]
          simp [Set.indicator]
private lemma zero_shift_exp_compare
    (k j : ℕ) (c0 : ℝ) (hc0 : 0 < c0) :
    Real.exp (-c0 * (posPart ((j : ℝ) - ((k + 5 : ℕ) : ℝ))) ^ 2) ≤
      Real.exp c0 *
        Real.exp (-((c0 / 4) * (posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ))) ^ 2)) := by
  by_cases hsmall : j ≤ k + 4
  · have hx : posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ)) = 0 := by
      apply max_eq_right
      exact sub_nonpos.mpr (by exact_mod_cast hsmall)
    have hy : posPart ((j : ℝ) - ((k + 5 : ℕ) : ℝ)) = 0 := by
      apply max_eq_right
      exact sub_nonpos.mpr (by exact_mod_cast Nat.le_trans hsmall (Nat.le_succ _))
    rw [hx, hy]
    simpa using (Real.one_le_exp_iff.mpr hc0.le)
  · have hbig : k + 5 ≤ j := by omega
    have hx :
        posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ)) =
          (j : ℝ) - ((k + 4 : ℕ) : ℝ) := by
      apply max_eq_left
      exact sub_nonneg.mpr (by exact_mod_cast Nat.le_trans (Nat.le_succ _) hbig)
    have hy :
        posPart ((j : ℝ) - ((k + 5 : ℕ) : ℝ)) =
          (j : ℝ) - ((k + 5 : ℕ) : ℝ) := by
      apply max_eq_left
      exact sub_nonneg.mpr (by exact_mod_cast hbig)
    have hrel :
        (j : ℝ) - ((k + 4 : ℕ) : ℝ) =
          ((j : ℝ) - ((k + 5 : ℕ) : ℝ)) + 1 := by
      norm_num [Nat.cast_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    rw [hx, hy, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    let y : ℝ := (j : ℝ) - ((k + 5 : ℕ) : ℝ)
    have hybound : 2 * y ≤ y ^ 2 + 1 := by nlinarith only [sq_nonneg (y - 1)]
    have hsq : (y + 1) ^ 2 ≤ 4 * (y ^ 2 + 1) := by nlinarith only [hybound]
    have hsq' :
        ((j : ℝ) - ((k + 4 : ℕ) : ℝ)) ^ 2 ≤
          4 * (((j : ℝ) - ((k + 5 : ℕ) : ℝ)) ^ 2 + 1) := by
      rw [hrel]
      exact hsq
    nlinarith only [hc0, hsq']
end Hermite1DimdLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped BigOperators ComplexConjugate
noncomputable section
open Hermite1DimdLEAN
namespace Hermite1DimdLEAN
theorem _root_.solution
    (k : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ n j : ℕ,
        annulusMass (d := 1) (fun _ => j) (oneDimLift (oneDimPhi k n)) ≤
          C *
            Real.exp
              (-c *
                max (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 ^ 2) := by
  /-
  Scaffolding guidance:
  derive the `n = 0` case directly from the explicit formula, then package
  the all-`n` statement for downstream reuse.
  -/
  obtain ⟨C1, c1, hC1, hc1, hloc1⟩ := oneVariableLocalization k
  obtain ⟨C0, c0, hC0, hc0, hloc0⟩ := HermitekLEAN.phi0_localization k
  let C : ℝ := max C1 (C0 * Real.exp c0)
  let c : ℝ := min c1 (c0 / 4)
  refine ⟨C, c, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le hC1 (le_max_left _ _)
  · exact lt_min hc1 (by positivity)
  · intro n j
    by_cases hn : n = 0
    · subst hn
      have hexact :
          max (|((j : ℕ) : ℝ) - Real.sqrt ((0 : ℕ) : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 =
            posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ)) := by simp [Real.sqrt_zero, posPart]
      rw [annulusMass_oneDimPhi_eq_annulusIntegralSq]
      have hphi0 :
          HermitekLEAN.annulusIntegralSq (HermitekLEAN.Phi k 0) j ≤
            C0 * Real.exp (-c0 * (posPart ((j : ℝ) - ((k + 5 : ℕ) : ℝ))) ^ 2) := by
        simpa [oneDimPhi, HermitekLEAN.phi0, HermitekLEAN.posPart, HermiteLEAN.posPart,
          _root_.posPart_def] using hloc0 j
      have hcompare := zero_shift_exp_compare k j c0 hc0
      have hCle : C0 * Real.exp c0 ≤ C := le_max_right _ _
      have hcle : c ≤ c0 / 4 := min_le_right _ _
      calc
        HermitekLEAN.annulusIntegralSq (HermitekLEAN.Phi k 0) j
            ≤ C0 * Real.exp (-c0 * (posPart ((j : ℝ) - ((k + 5 : ℕ) : ℝ))) ^ 2) := hphi0
        _ ≤ (C0 * Real.exp c0) *
              Real.exp (-((c0 / 4) * (posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ))) ^ 2)) := by
              have := mul_le_mul_of_nonneg_left hcompare (le_of_lt hC0)
              simpa [mul_assoc, mul_left_comm, mul_comm] using this
        _ ≤ C * Real.exp (-((c0 / 4) * (posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ))) ^ 2)) := by
              have hexp_nonneg :
                  0 ≤ Real.exp (-((c0 / 4) * (posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ))) ^ 2)) := by
                positivity
              exact mul_le_mul_of_nonneg_right hCle hexp_nonneg
        _ ≤ C * Real.exp (-(c * (posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ))) ^ 2)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              apply Real.exp_le_exp.mpr
              nlinarith only [hcle, sq_nonneg (posPart ((j : ℝ) - ((k + 4 : ℕ) : ℝ)))]
        _ = C * Real.exp (-c *
              max (|((j : ℕ) : ℝ) - Real.sqrt ((0 : ℕ) : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 ^ 2) := by
              simp_all
    · have hn1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
      have hbase := hloc1 n j hn1
      have hCle : C1 ≤ C := le_max_left _ _
      have hcle : c ≤ c1 := min_le_left _ _
      calc
        annulusMass (d := 1) (fun _ => j) (oneDimLift (oneDimPhi k n))
            ≤ C1 *
              Real.exp
                (-c1 *
                  max (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 ^ 2) := hbase
        _ ≤ C *
              Real.exp
                (-c1 *
                  max (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 ^ 2) := by
              have hexp_nonneg :
                  0 ≤ Real.exp
                    (-c1 *
                      max (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 ^ 2) := by
                positivity
              exact mul_le_mul_of_nonneg_right hCle hexp_nonneg
        _ ≤ C *
              Real.exp
                (-c *
                  max (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 ^ 2) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              apply Real.exp_le_exp.mpr
              nlinarith only [
                hcle,
                sq_nonneg (max (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0)
              ]
end Hermite1DimdLEAN
