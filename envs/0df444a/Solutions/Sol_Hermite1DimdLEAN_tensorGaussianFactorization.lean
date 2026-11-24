-- Prove2me | solution 1 for Hermite1DimdLEAN.tensorGaussianFactorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:03:02.338427+00:00
-- url     : https://prove2.me/submissions/e1f32b2e-b046-41f6-9e43-2de0225b5374

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_BasisLocalization
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_ImportedAnalyticInputs
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
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
private lemma integral_funUnique_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ℂ → E) :
    ∫ z : CSpace 1, φ (z 0) ∂(volume : Measure (CSpace 1)) =
      ∫ z : ℂ, φ z ∂(volume : Measure ℂ) := by
  have hEq0 :=
    ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℂ).integral_comp'
      (f := MeasurableEquiv.funUnique (Fin 1) ℂ) φ)
  exact hEq0
private lemma gaussianDensity_succ_split
    (d : ℕ) (z : CSpace (d + 1)) :
    gaussianDensity (d + 1) z =
      gaussianDensity 1 (fun _ : Fin 1 => z 0) *
        gaussianDensity d (fun q : Fin d => z (Fin.succ q)) := by
  unfold gaussianDensity
  rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_one]
  rw [pow_succ, neg_add, Real.exp_add]
  field_simp [Real.pi_pos.ne']
private lemma gaussianDensity_eq_prod
    (d : ℕ) (z : CSpace d) :
    gaussianDensity d z =
      ∏ q : Fin d, gaussianDensity 1 (fun _ : Fin 1 => z q) := by
  induction d with
  | zero =>
      simp [gaussianDensity]
  | succ d ih =>
      rw [gaussianDensity_succ_split, ih, Fin.prod_univ_succ]
private lemma integrable_weighted_coord_of_integrable_gaussian
    (f g : ℂ → ℂ)
    (hfg :
      Integrable
        (fun z : CSpace 1 => f (z 0) * conj (g (z 0)))
        (gaussianMeasure 1)) :
    Integrable
      (fun z : ℂ =>
        (((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) *
          (f z * conj (g z)))
      (volume : Measure ℂ) := by
  have hsmul :
      Integrable
        (fun z : CSpace 1 =>
          (ENNReal.ofReal (gaussianDensity 1 z)).toReal •
            (f (z 0) * conj (g (z 0))))
        (volume : Measure (CSpace 1)) := by
    rw [gaussianMeasure] at hfg
    exact
      (integrable_withDensity_iff_integrable_smul'
        (measurable_ofReal_gaussianDensity 1) (gaussianDensity_ofReal_lt_top 1)).1 hfg
  let e : ℂ ≃ᵐ CSpace 1 := (MeasurableEquiv.funUnique (Fin 1) ℂ).symm
  have hcomp :
      Integrable
        (fun z : ℂ =>
          (ENNReal.ofReal (gaussianDensity 1 (e z))).toReal •
            (f ((e z) 0) * conj (g ((e z) 0))))
        (volume : Measure ℂ) := by
    have h :=
      (MeasureTheory.volume_preserving_funUnique (Fin 1) ℂ).symm.integrable_comp_of_integrable
        (g := fun z : CSpace 1 =>
          (ENNReal.ofReal (gaussianDensity 1 z)).toReal •
            (f (z 0) * conj (g (z 0))))
        hsmul
    refine h.congr ?_
    filter_upwards with z
    rfl
  convert hcomp using 1
  ext z
  have hdens :
      (ENNReal.ofReal (gaussianDensity 1 (e z))).toReal =
        (1 / Real.pi) * Real.exp (-‖z‖ ^ 2) := by
    have hnonneg' : 0 ≤ π⁻¹ * Real.exp (-‖z‖ ^ 2) := by positivity
    simpa [e, gaussianDensity] using (ENNReal.toReal_ofReal hnonneg')
  rw [hdens]
  simp [e, Algebra.smul_def, mul_assoc, mul_left_comm]
private theorem gaussianInner_oneDim_eq_weighted_coord
    (f g : ℂ → ℂ) :
    gaussianInner (d := 1) (fun z : CSpace 1 => f (z 0)) (fun z : CSpace 1 => g (z 0)) =
      ∫ z : ℂ,
        (((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) *
          (f z * conj (g z))
        ∂(volume : Measure ℂ) := by
  unfold gaussianInner
  rw [gaussianMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_ofReal_gaussianDensity 1) (gaussianDensity_ofReal_lt_top 1)]
  have hEq :
      ∫ x : CSpace 1,
          (((1 / Real.pi) * Real.exp (-‖x 0‖ ^ 2) : ℝ) : ℂ) *
            (f (x 0) * conj (g (x 0)))
          ∂(volume : Measure (CSpace 1)) =
        ∫ z : ℂ,
          (((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) *
            (f z * conj (g z))
          ∂(volume : Measure ℂ) :=
    integral_funUnique_one (fun z : ℂ =>
      (((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) * (f z * conj (g z)))
  calc
    ∫ z : CSpace 1,
        (ENNReal.ofReal (gaussianDensity 1 z)).toReal •
          (f (z 0) * conj (g (z 0)))
        ∂(volume : Measure (CSpace 1)) =
      ∫ z : CSpace 1,
        (((1 / Real.pi) * Real.exp (-‖z 0‖ ^ 2) : ℝ) : ℂ) *
          (f (z 0) * conj (g (z 0)))
        ∂(volume : Measure (CSpace 1)) := by
          apply integral_congr_ae
          filter_upwards with z
          rw [toReal_gaussianDensity_one z]
          simp [Algebra.smul_def, mul_assoc, mul_left_comm]
    _ = ∫ z : ℂ,
        (((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) *
          (f z * conj (g z))
        ∂(volume : Measure ℂ) := hEq
private lemma density_prod_identity
    (d : ℕ) (F G : Fin d → ℂ → ℂ) (z : CSpace d) :
    (gaussianDensity d z : ℂ) *
        ((∏ q : Fin d, F q (z q)) * conj (∏ q : Fin d, G q (z q))) =
      ∏ q : Fin d,
        ((((1 / Real.pi) * Real.exp (-‖z q‖ ^ 2) : ℝ) : ℂ) *
          (F q (z q) * conj (G q (z q)))) := by
  rw [gaussianDensity_eq_prod]
  simp [gaussianDensity, Finset.prod_mul_distrib, mul_assoc, mul_left_comm]
private lemma density_smul_prod_identity
    (d : ℕ) (F G : Fin d → ℂ → ℂ) (z : CSpace d) :
    (((ENNReal.ofReal (gaussianDensity d z)).toReal : ℂ) *
        ∏ q : Fin d, F q (z q) * conj (G q (z q))) =
      ∏ q : Fin d,
        ((((1 / Real.pi) * Real.exp (-‖z q‖ ^ 2) : ℝ) : ℂ) *
          (F q (z q) * conj (G q (z q)))) := by
  have hnonneg : 0 ≤ gaussianDensity d z := by
    unfold gaussianDensity
    positivity
  rw [ENNReal.toReal_ofReal hnonneg, Finset.prod_mul_distrib, ← map_prod]
  exact density_prod_identity d F G z
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
    (d : ℕ) (F G : Fin d → ℂ → ℂ)
    (hFG :
      ∀ q : Fin d,
        Integrable
            (fun z : CSpace 1 => F q (z 0) * conj (G q (z 0)))
            (gaussianMeasure 1)) :
    Integrable
        (fun z : CSpace d => ∏ q : Fin d, F q (z q) * conj (G q (z q)))
        (gaussianMeasure d) ∧
      gaussianInner (d := d) (fun z => ∏ q : Fin d, F q (z q)) (fun z => ∏ q : Fin d, G q (z q)) =
        ∏ q : Fin d,
          gaussianInner (d := 1) (fun z : CSpace 1 => F q (z 0)) (fun z : CSpace 1 => G q (z 0))
              := by
  have hcoord :
      ∀ q : Fin d,
        Integrable
          (fun z : ℂ =>
            (((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) *
              (F q z * conj (G q z)))
          (volume : Measure ℂ) := by
    intro q
    exact integrable_weighted_coord_of_integrable_gaussian (F q) (G q) (hFG q)
  have hprod_volume :
      Integrable
        (fun z : CSpace d =>
          ∏ q : Fin d,
            ((((1 / Real.pi) * Real.exp (-‖z q‖ ^ 2) : ℝ) : ℂ) *
              (F q (z q) * conj (G q (z q)))))
        (volume : Measure (CSpace d)) := by
    rw [MeasureTheory.volume_pi]
    exact MeasureTheory.Integrable.fintype_prod hcoord
  have hintegrable :
      Integrable
        (fun z : CSpace d => ∏ q : Fin d, F q (z q) * conj (G q (z q)))
        (gaussianMeasure d) := by
    rw [gaussianMeasure, MeasureTheory.integrable_withDensity_iff_integrable_smul']
    · refine hprod_volume.congr ?_
      filter_upwards with z
      exact (density_smul_prod_identity d F G z).symm
    · exact measurable_ofReal_gaussianDensity d
    · exact gaussianDensity_ofReal_lt_top d
  constructor
  · exact hintegrable
  · unfold gaussianInner
    rw [gaussianMeasure]
    rw [integral_withDensity_eq_integral_toReal_smul
      (measurable_ofReal_gaussianDensity d) (gaussianDensity_ofReal_lt_top d)]
    calc
      ∫ z : CSpace d,
          (ENNReal.ofReal (gaussianDensity d z)).toReal •
            ((fun z => ∏ q : Fin d, F q (z q)) z *
              conj ((fun z => ∏ q : Fin d, G q (z q)) z))
          ∂(volume : Measure (CSpace d)) =
        ∫ z : CSpace d,
          (ENNReal.ofReal (gaussianDensity d z)).toReal •
            (∏ q : Fin d, F q (z q) * conj (G q (z q)))
          ∂(volume : Measure (CSpace d)) := by
            apply integral_congr_ae
            filter_upwards with z
            simp [Finset.prod_mul_distrib]
      _ =
        ∫ z : CSpace d,
          ∏ q : Fin d,
            ((((1 / Real.pi) * Real.exp (-‖z q‖ ^ 2) : ℝ) : ℂ) *
              (F q (z q) * conj (G q (z q))))
          ∂(volume : Measure (CSpace d)) := by
            apply integral_congr_ae
            filter_upwards with z
            exact density_smul_prod_identity d F G z
      _ = ∏ q : Fin d,
            ∫ z : ℂ,
              (((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) *
                (F q z * conj (G q z))
              ∂(volume : Measure ℂ) := by
              rw [MeasureTheory.volume_pi]
              exact
                MeasureTheory.integral_fintype_prod_eq_prod
                  (fun q : Fin d => fun z : ℂ =>
                    ((((1 / Real.pi) * Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ) *
                      (F q z * conj (G q z))))
      _ = ∏ q : Fin d,
            gaussianInner (d := 1) (fun z : CSpace 1 => F q (z 0))
              (fun z : CSpace 1 => G q (z 0)) := by
            apply Finset.prod_congr rfl
            intro q hq
            symm
            exact gaussianInner_oneDim_eq_weighted_coord (F q) (G q)
end Hermite1DimdLEAN
