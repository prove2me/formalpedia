-- Prove2me | solution 1 for Hermite1DimdLEAN.annulusRotationAveraging
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:33:31.208923+00:00
-- url     : https://prove2.me/submissions/e7791f0e-67ba-4e6f-bf35-5d455264d838

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Theorems.Thm_Hermite1DimdLEAN_annulusRotationInvariant
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
private lemma measurableSet_productAnnulus
    {d : ℕ} (j : MultiIndex d) :
    MeasurableSet (productAnnulus j) := by
  classical
  have h :
      MeasurableSet (⋂ q : Fin d, {z : CSpace d | (j q : ℝ) ≤ ‖z q‖ ∧ ‖z q‖ < (j q : ℝ) + 1}) := by
    refine MeasurableSet.iInter (f := fun q : Fin d => {z : CSpace d | (j q : ℝ) ≤ ‖z q‖ ∧ ‖z q‖ <
        (j q : ℝ) + 1}) ?_
    intro q
    have hge : MeasurableSet {z : CSpace d | (j q : ℝ) ≤ ‖z q‖} :=
      measurableSet_le measurable_const (measurable_norm.comp (continuous_apply q).measurable)
    have hlt : MeasurableSet {z : CSpace d | ‖z q‖ < (j q : ℝ) + 1} :=
      measurableSet_lt (measurable_norm.comp (continuous_apply q).measurable) measurable_const
    simpa [Set.ofPred_and] using hge.inter hlt
  simpa [productAnnulus, Set.ofPred_forall] using h
private lemma gaussianMeasure_map_eq_of_density
    {d : ℕ} {f : CSpace d → CSpace d}
    (hvol : MeasurePreserving f (volume : Measure (CSpace d)) (volume : Measure (CSpace d)))
    (hmeas : MeasurableEmbedding f)
    (hdens : ∀ z : CSpace d,
      ENNReal.ofReal (gaussianDensity d (f z)) = ENNReal.ofReal (gaussianDensity d z)) :
    Measure.map f (gaussianMeasure d) = gaussianMeasure d := by
  classical
  let dens : CSpace d → ENNReal := fun z => ENNReal.ofReal (gaussianDensity d z)
  change Measure.map f (volume.withDensity dens) = volume.withDensity dens
  ext s hs
  have hs' : MeasurableSet (f ⁻¹' s) := measurableSet_preimage hmeas.measurable hs
  rw [Measure.map_apply_of_aemeasurable hmeas.measurable.aemeasurable hs,
    withDensity_apply _ hs', withDensity_apply _ hs]
  rw [← MeasureTheory.lintegral_indicator (hs := hs'),
    ← MeasureTheory.lintegral_indicator (hs := hs)]
  simpa [Set.preimage, Set.indicator, Set.mem_ofPred_eq, dens, hdens] using
    (hvol.lintegral_comp_emb hmeas (fun x => if x ∈ s then dens x else 0))
private lemma gaussian_lintegral_rotate_eq
    {d : ℕ} (ω : _root_.Circle) (g : CSpace d → ENNReal) :
    ∫⁻ z : CSpace d, g (fun q => (ω : ℂ) * z q) ∂ gaussianMeasure d =
      ∫⁻ z : CSpace d, g z ∂ gaussianMeasure d := by
  classical
  let f : CSpace d → CSpace d := fun z q => (ω : ℂ) * z q
  have hvol : MeasurePreserving f (volume : Measure (CSpace d)) (volume : Measure (CSpace d)) :=
    MeasureTheory.volume_preserving_pi (f := fun _ : Fin d => mulCircleLIE ω)
      (fun _ => (mulCircleLIE ω).measurePreserving)
  have hmeas : MeasurableEmbedding f := by
    let inv : CSpace d → CSpace d := fun z q => (((ω⁻¹ : _root_.Circle) : ℂ) * z q)
    have hinv : Function.LeftInverse inv f := by
      intro z
      funext q
      simp [f, inv]
    have hcont : Continuous f := by fun_prop
    exact hcont.measurableEmbedding hinv.injective
  have hdens : ∀ z : CSpace d,
      ENNReal.ofReal (gaussianDensity d (f z)) = ENNReal.ofReal (gaussianDensity d z) := by
    intro z
    have hω : ‖(ω : ℂ)‖ = 1 := Circle.norm_coe ω
    simp [f, gaussianDensity, hω]
  have hgauss : MeasurePreserving f (gaussianMeasure d) (gaussianMeasure d) :=
    ⟨hmeas.measurable, gaussianMeasure_map_eq_of_density hvol hmeas hdens⟩
  exact hgauss.lintegral_comp_emb hmeas g
private lemma fourier_mk_eq_exp
    (n : ℤ) (θ : ℝ) :
    (fourier n (QuotientAddGroup.mk θ : Circle) : ℂ) =
      Complex.exp (Complex.I * (n : ℂ) * θ) := by
  rw [fourier_coe_apply]
  congr 1
  simp only [T, HermiteLEAN.T]
  push_cast
  field_simp
private lemma annulusRotationInvariantCircle
    {d : ℕ} (j : MultiIndex d) (t : Circle) (z : CSpace d) :
    z ∈ productAnnulus j ↔
      (fun q => (fourier (T := Hermite1DimdLEAN.T) (1 : ℤ) t : ℂ) * z q) ∈ productAnnulus j := by
  induction t using Quotient.inductionOn with
  | h θ =>
      rw [fourier_mk_eq_exp]
      simpa using (annulusRotationInvariant (j := j) (t := θ) (z := z))
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
    {d : ℕ} (j : MultiIndex d) (F : CSpace d → ENNReal) (hF : Measurable F) :
    by
      classical
      exact
        ∫⁻ z : CSpace d,
            if _h : z ∈ productAnnulus j then
              ∫⁻ t : Hermite1DimdLEAN.Circle,
                  F (fun q => (fourier (T := Hermite1DimdLEAN.T) (1 : ℤ) t : ℂ) * z q)
                    ∂ AddCircle.haarAddCircle
            else 0
          ∂ gaussianMeasure d
          =
        ∫⁻ z : CSpace d, if _h : z ∈ productAnnulus j then F z else 0 ∂ gaussianMeasure d := by
  classical
  let G : CSpace d → ENNReal := fun z => if z ∈ productAnnulus j then F z else 0
  have hG : Measurable G := hF.piecewise (measurableSet_productAnnulus j) measurable_const
  let : MeasureTheory.SFinite (gaussianMeasure d) := by
    change MeasureTheory.SFinite
      ((volume : Measure (CSpace d)).withDensity (fun z => ENNReal.ofReal (gaussianDensity d z)))
    infer_instance
  calc
    ∫⁻ z : CSpace d,
        if h : z ∈ productAnnulus j then
          ∫⁻ t : Hermite1DimdLEAN.Circle,
              F (fun q => (fourier (T := Hermite1DimdLEAN.T) (1 : ℤ) t : ℂ) * z q)
                ∂ AddCircle.haarAddCircle
        else 0
      ∂ gaussianMeasure d
      = ∫⁻ z : CSpace d,
          ∫⁻ t : Hermite1DimdLEAN.Circle,
              G (fun q => (fourier (T := Hermite1DimdLEAN.T) (1 : ℤ) t : ℂ) * z q)
                ∂ AddCircle.haarAddCircle
          ∂ gaussianMeasure d := by
            refine lintegral_congr_ae ?_
            filter_upwards with z
            by_cases hz : z ∈ productAnnulus j
            · simp only [hz, ↓reduceDIte, fourier_apply, one_smul]
              refine lintegral_congr_ae ?_
              filter_upwards with t
              have hrot :
                  (fun q => (fourier (T := Hermite1DimdLEAN.T) (1 : ℤ) t : ℂ) * z q) ∈
                    productAnnulus j :=
                (annulusRotationInvariantCircle (j := j) (t := t) (z := z)).mp hz
              have hrot' :
                  (fun q => ((AddCircle.toCircle t : _root_.Circle) : ℂ) * z q) ∈
                    productAnnulus j := by simpa [fourier_one] using hrot
              simp only [G]
              simp_all
            · have hzero :
                ∫⁻ t : Hermite1DimdLEAN.Circle,
                    G (fun q => (fourier (T := Hermite1DimdLEAN.T) (1 : ℤ) t : ℂ) * z q)
                  ∂ AddCircle.haarAddCircle = 0 := by
                    refine lintegral_eq_zero_of_ae_eq_zero ?_
                    filter_upwards with t
                    have hrot :
                        (fun q => (fourier (T := Hermite1DimdLEAN.T) (1 : ℤ) t : ℂ) * z q) ∉
                          productAnnulus j := fun hz' =>
                      hz ((annulusRotationInvariantCircle (j := j) (t := t) (z := z)).mpr hz')
                    simp only [G, Pi.zero_apply]
                    simp_all
              simp_all
    _ = ∫⁻ t : Hermite1DimdLEAN.Circle,
          ∫⁻ z : CSpace d,
              G (fun q => (fourier (T := Hermite1DimdLEAN.T) (1 : ℤ) t : ℂ) * z q)
            ∂ gaussianMeasure d
        ∂ AddCircle.haarAddCircle := by
          rw [MeasureTheory.lintegral_lintegral_swap]
          · have hpair :
                Measurable (fun p : CSpace d × Hermite1DimdLEAN.Circle =>
                  G (fun q => (fourier (T := Hermite1DimdLEAN.T) (1 : ℤ) p.2 : ℂ) * p.1 q)) := by
                  refine hG.comp ?_
                  fun_prop
            exact hpair.aemeasurable
    _ = ∫⁻ t : Hermite1DimdLEAN.Circle,
          ∫⁻ z : CSpace d, G z ∂ gaussianMeasure d
        ∂ AddCircle.haarAddCircle := by
          refine lintegral_congr_ae ?_
          filter_upwards with t
          simpa [fourier_one] using
            (gaussian_lintegral_rotate_eq (ω := AddCircle.toCircle t) (g := G))
    _ = ∫⁻ z : CSpace d, G z ∂ gaussianMeasure d := by
          simp_all
    _ = ∫⁻ z : CSpace d, if h : z ∈ productAnnulus j then F z else 0 ∂ gaussianMeasure d := by rfl
end Hermite1DimdLEAN
