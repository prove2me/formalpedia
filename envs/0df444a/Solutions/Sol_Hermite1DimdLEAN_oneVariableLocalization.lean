-- Prove2me | solution 1 for Hermite1DimdLEAN.oneVariableLocalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:33:33.958657+00:00
-- url     : https://prove2.me/submissions/08c4f006-a859-436e-b9e7-40aa954e6231

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_BasisLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_ImportedAnalyticInputs
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
public import Theorems.Thm_HermitekLEAN_single_basis_localization
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
      ∀ n j : ℕ, 1 ≤ n →
        annulusMass (d := 1) (fun _ => j) (oneDimLift (oneDimPhi k n)) ≤
          C *
            Real.exp
              (-c *
                max (|((j : ℕ) : ℝ) - Real.sqrt (n : ℝ)| - ((k + 4 : ℕ) : ℝ)) 0 ^ 2) := by
  /-
  Scaffolding guidance:
  the scaffold keeps the quantifier/hypothesis shape `n ≥ 1`.
  The imported theorem is existential in the localization constants and should
  not be silently strengthened.
  -/
  obtain ⟨C, c, hC, hc, hloc⟩ := HermitekLEAN.single_basis_localization k
  refine ⟨C, c, hC, hc, ?_⟩
  intro n j hn
  rw [annulusMass_oneDimPhi_eq_annulusIntegralSq]
  exact hloc n j hn
end Hermite1DimdLEAN
