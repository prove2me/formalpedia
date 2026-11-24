-- Prove2me | solution 1 for Hermite1DimdLEAN.annulusOrthogonality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:33:46.108948+00:00
-- url     : https://prove2.me/submissions/e1b48d0a-cfe8-40e4-ba81-f46f9acd05be

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Theorems.Thm_Hermite1DimdLEAN_oneVariableAngularFactorization
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
private lemma oneDimPhi_phaseLaw
    (k n : ℕ) (t : ℝ) (z : ℂ) :
    oneDimPhi k n (Complex.exp (Complex.I * t) * z) =
      Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * t)) * oneDimPhi k n z := by
  obtain ⟨radial, hradial⟩ := oneVariableAngularFactorization k n
  have hz : ((‖z‖ : ℂ) * Complex.exp (Complex.I * z.arg)) = z := by
    simp [mul_comm Complex.I (z.arg : ℂ)]
  have hrot :
      Complex.exp (Complex.I * t) * z =
        ((‖z‖ : ℂ) * Complex.exp (Complex.I * (t + z.arg))) := by
    rw [mul_add, Complex.exp_add]
    conv_lhs => rw [← hz]
    ring
  have hleft :
      oneDimPhi k n ((‖z‖ : ℂ) * Complex.exp (Complex.I * (t + z.arg))) =
        Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * (t + z.arg))) *
          radial.eval₂ (algebraMap ℝ ℂ) ‖z‖ := by simpa using hradial ‖z‖ (t + z.arg)
  have hright :
      oneDimPhi k n z =
        Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * z.arg)) *
          radial.eval₂ (algebraMap ℝ ℂ) ‖z‖ := by simpa [hz] using hradial ‖z‖ z.arg
  have hexp :
      Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * (t + z.arg))) =
        Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * t)) *
          Complex.exp (Complex.I * (((n : ℤ) - (k : ℤ) : ℂ) * z.arg)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hrot, hleft, hexp, hright]
  ring
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
private lemma productAnnulus_rotate_one_iff
    {d : ℕ} (j : MultiIndex d) (q0 : Fin d) (ω : _root_.Circle) (z : CSpace d) :
    Function.update z q0 ((ω : ℂ) * z q0) ∈ productAnnulus j ↔ z ∈ productAnnulus j := by
  have hω : ‖(ω : ℂ)‖ = 1 := _root_.Circle.norm_coe ω
  constructor <;> intro hz <;> intro q
  · by_cases hq : q = q0
    · subst hq
      simpa [productAnnulus, Function.update, Complex.norm_mul, hω] using hz q
    · simpa [productAnnulus, Function.update, hq] using hz q
  · by_cases hq : q = q0
    · subst hq
      simpa [productAnnulus, Function.update, Complex.norm_mul, hω] using hz q
    · simpa [productAnnulus, Function.update, hq] using hz q
private lemma rotate_one_volume_preserving
    {d : ℕ} (q0 : Fin d) (ω : _root_.Circle) :
    MeasurePreserving
      (fun z : CSpace d => Function.update z q0 ((ω : ℂ) * z q0))
      (volume : Measure (CSpace d)) (volume : Measure (CSpace d)) := by
  classical
  let f : Fin d → ℂ → ℂ := fun i => if h : i = q0 then fun z => (ω : ℂ) * z else id
  have hf : ∀ i : Fin d, MeasurePreserving (f i) (volume : Measure ℂ) (volume : Measure ℂ) := by
    intro i
    by_cases h : i = q0
    · subst h
      have hfeq : ⇑(mulCircleLIE ω) = f i := by
        funext z
        simp only [f, dite_true]
        rfl
      rw [← hfeq]
      exact (mulCircleLIE ω).measurePreserving
    · simpa [f, h] using
        (show MeasurePreserving (id : ℂ → ℂ) (volume : Measure ℂ) (volume : Measure ℂ) from
          ⟨measurable_id, by simp⟩)
  have hpi :
      MeasurePreserving
        (fun z : CSpace d => fun i => f i (z i))
        (volume : Measure (CSpace d)) (volume : Measure (CSpace d)) := by
    simpa [MeasureTheory.Measure.pi, f] using
      (MeasureTheory.volume_preserving_pi (f := f) hf)
  have hfun :
      (fun z : CSpace d => fun i => f i (z i)) =
        fun z => Function.update z q0 ((ω : ℂ) * z q0) := by
    funext z i
    by_cases h : i = q0
    · subst h
      simp [f]
    · simp [f, h]
  simpa [hfun] using hpi
private lemma rotate_one_measurableEmbedding
    {d : ℕ} (q0 : Fin d) (ω : _root_.Circle) :
    MeasurableEmbedding (fun z : CSpace d => Function.update z q0 ((ω : ℂ) * z q0)) := by
  classical
  let f : CSpace d → CSpace d := fun z => Function.update z q0 ((ω : ℂ) * z q0)
  let g : CSpace d → CSpace d := fun z => Function.update z q0 (((ω⁻¹ : _root_.Circle) : ℂ) * z q0)
  have hf : Measurable f := by fun_prop
  have hcont : Continuous f := by fun_prop
  have hgf : Function.LeftInverse g f := by
    intro z
    funext q
    by_cases hq : q = q0
    · subst hq
      simp [f, g, Function.update]
    · simp [f, g, Function.update, hq]
  have hrange : MeasurableSet (Set.range f) :=
    MeasureTheory.measurableSet_range_of_continuous_injective hcont hgf.injective
  exact MeasurableEmbedding.of_measurable_inverse hf hrange (by fun_prop) hgf
private lemma rotate_one_gaussian_preserving
    {d : ℕ} (q0 : Fin d) (ω : _root_.Circle) :
    MeasurePreserving
      (fun z : CSpace d => Function.update z q0 ((ω : ℂ) * z q0))
      (gaussianMeasure d) (gaussianMeasure d) := by
  classical
  let f : CSpace d → CSpace d := fun z => Function.update z q0 ((ω : ℂ) * z q0)
  have hvol := (rotate_one_volume_preserving (q0 := q0) (ω := ω))
  have hmeas : MeasurableEmbedding f := rotate_one_measurableEmbedding (q0 := q0) (ω := ω)
  have hdens : ∀ z : CSpace d,
      ENNReal.ofReal (gaussianDensity d (f z)) = ENNReal.ofReal (gaussianDensity d z) := by
    intro z
    have hsum :
        ∑ q : Fin d, ‖Function.update z q0 ((ω : ℂ) * z q0) q‖ ^ 2 =
          ∑ q : Fin d, ‖z q‖ ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro q hq
      by_cases h : q = q0
      · subst q
        have hω : ‖(ω : ℂ)‖ = 1 := Circle.norm_coe ω
        simp [hω]
      · simp [Function.update, h]
    simp [f, gaussianDensity, hsum]
  exact ⟨hmeas.measurable, gaussianMeasure_map_eq_of_density hvol hmeas hdens⟩
private lemma PhiKappaAlpha_rotate_one
    {d : ℕ} (κ α : MultiIndex d) (q0 : Fin d) (t : ℝ) (z : CSpace d) :
    PhiKappaAlpha κ α (Function.update z q0 (Complex.exp (Complex.I * t) * z q0)) =
      Complex.exp (Complex.I * (((α q0 : ℤ) - (κ q0 : ℤ) : ℂ) * t)) * PhiKappaAlpha κ α z := by
  classical
  unfold PhiKappaAlpha
  have hupdate :
      (fun q : Fin d =>
        oneDimPhi (κ q) (α q) (Function.update z q0 (Complex.exp (Complex.I * t) * z q0) q)) =
        Function.update
          (fun q : Fin d => oneDimPhi (κ q) (α q) (z q))
          q0
          (oneDimPhi (κ q0) (α q0) (Complex.exp (Complex.I * t) * z q0)) := by
    funext q
    by_cases hq : q = q0
    · simp_all
    · simp [Function.update, hq]
  rw [hupdate, Finset.prod_update_of_mem (s := Finset.univ) (i := q0) (by simp), oneDimPhi_phaseLaw]
  conv_rhs => rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (s := Finset.univ) (i := q0) (by
      simp)]
  ring
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
    {d : ℕ} (κ j α β : MultiIndex d) (hαβ : α ≠ β) :
    annulusInner j (PhiKappaAlpha κ α) (PhiKappaAlpha κ β) = 0 := by
  classical
  obtain ⟨q0, hq0⟩ : ∃ q0 : Fin d, α q0 ≠ β q0 := by simpa [funext_iff] using hαβ
  let n : ℤ := (α q0 : ℤ) - (β q0 : ℤ)
  have hn : n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hq0)
  let t : ℝ := Real.pi / (n : ℝ)
  let ω : _root_.Circle := _root_.Circle.exp t
  let rot : CSpace d → CSpace d :=
    fun z => Function.update z q0 ((ω : ℂ) * z q0)
  let H : CSpace d → ℂ := fun z =>
    if z ∈ productAnnulus j then
      PhiKappaAlpha κ α z * conj (PhiKappaAlpha κ β z)
    else 0
  have hω : (ω : ℂ) = Complex.exp (Complex.I * t) := by simp [ω, _root_.Circle.coe_exp, mul_comm]
  have hpres :
      MeasurePreserving rot (gaussianMeasure d) (gaussianMeasure d) := by
    simpa [rot, hω] using rotate_one_gaussian_preserving (q0 := q0) (ω := ω)
  have hmeas : MeasurableEmbedding rot := by
    simpa [rot, hω] using rotate_one_measurableEmbedding (q0 := q0) (ω := ω)
  have hcomp :
      ∫ z : CSpace d, H (rot z) ∂ gaussianMeasure d
        = ∫ z : CSpace d, H z ∂ gaussianMeasure d := by
    simpa [rot] using (MeasurePreserving.integral_comp hpres hmeas H)
  have hneg_point : ∀ z : CSpace d, H (rot z) = - H z := by
    intro z
    by_cases hz : z ∈ productAnnulus j
    · have hzrot : rot z ∈ productAnnulus j := by
        simpa [rot, hω] using
          (productAnnulus_rotate_one_iff (j := j) (q0 := q0) (ω := ω) (z := z)).2 hz
      have hαrot :=
        PhiKappaAlpha_rotate_one (κ := κ) (α := α) (q0 := q0) (t := t) (z := z)
      have hβrot :=
        PhiKappaAlpha_rotate_one (κ := κ) (α := β) (q0 := q0) (t := t) (z := z)
      have hrot_eq : rot z = Function.update z q0 (Complex.exp (Complex.I * t) * z q0) := by
        simp [rot, hω]
      simp only [hzrot, ↓reduceIte, hz, H]
      rw [hrot_eq, hαrot, hβrot]
      have hconj :
          conj (Complex.exp (Complex.I * ((((β q0 : ℤ) - (κ q0 : ℤ) : ℂ) * t)))) =
            Complex.exp (-Complex.I * ((((β q0 : ℤ) - (κ q0 : ℤ) : ℂ) * t))) := by
        rw [← Complex.exp_conj]
        simp [mul_comm]
      rw [map_mul, hconj]
      have hphase :
          Complex.exp (Complex.I * ((((α q0 : ℤ) - (κ q0 : ℤ) : ℂ) * t))) *
              Complex.exp (-Complex.I * ((((β q0 : ℤ) - (κ q0 : ℤ) : ℂ) * t))) =
            (-1 : ℂ) := by
        have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
        have hnt : ((n : ℂ) * t) = (Real.pi : ℂ) := by
          have hntR : (n : ℝ) * (Real.pi / (n : ℝ)) = Real.pi := by field_simp [hnR]
          simpa [t] using congrArg Complex.ofReal hntR
        have hntI : Complex.I * ((n : ℂ) * t) = (Real.pi : ℂ) * Complex.I := by
          simpa [mul_comm] using congrArg (fun x : ℂ => Complex.I * x) hnt
        have hexpsum :
            Complex.I * ((((α q0 : ℤ) - (κ q0 : ℤ) : ℂ) * t)) +
                -Complex.I * ((((β q0 : ℤ) - (κ q0 : ℤ) : ℂ) * t)) =
              Complex.I * ((n : ℂ) * t) := by
          simp only [n]
          push_cast
          ring
        rw [← Complex.exp_add, hexpsum, hntI]
        simpa [mul_comm] using Complex.exp_pi_mul_I
      have hneg_core :
          Complex.exp (Complex.I * ((((α q0 : ℤ) - (κ q0 : ℤ) : ℂ) * t))) * PhiKappaAlpha κ α z *
              (Complex.exp (-Complex.I * ((((β q0 : ℤ) - (κ q0 : ℤ) : ℂ) * t))) *
                conj (PhiKappaAlpha κ β z)) =
            -(PhiKappaAlpha κ α z * conj (PhiKappaAlpha κ β z)) := by
        linear_combination (PhiKappaAlpha κ α z * conj (PhiKappaAlpha κ β z)) * hphase
      simpa [H, hz] using hneg_core
    · have hzrot : rot z ∉ productAnnulus j := by
        intro hzrot
        exact hz <|
          (productAnnulus_rotate_one_iff (j := j) (q0 := q0) (ω := ω) (z := z)).1
            (by simpa [rot, hω] using hzrot)
      simp [H, hz, hzrot]
  have hneg_int :
      ∫ z : CSpace d, H (rot z) ∂ gaussianMeasure d
        = - ∫ z : CSpace d, H z ∂ gaussianMeasure d := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hneg_point),
      MeasureTheory.integral_neg]
  have hzero_int : ∫ z : CSpace d, H z ∂ gaussianMeasure d = 0 :=
    CharZero.eq_neg_self_iff.mp (hcomp.symm.trans hneg_int)
  simpa [annulusInner, H] using hzero_int
end Hermite1DimdLEAN
