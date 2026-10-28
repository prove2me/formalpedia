-- Prove2me | solution 1 for IntroMatrixConc.Sampling.variance_bound
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T06:49:14.975852+00:00
-- url     : https://prove2.me/submissions/b65e21ac-a01d-4156-95d7-64a6f22e95b0

import Definitions.Def_TroppMatrixConcentration_spectral
import Definitions.Def_TroppMatrixConcentration_probability
import Definitions.Def_IntroMatrixConc_Sampling_Defs
import Init
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex


section
namespace Queelius.MatrixSampling
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Ω E F : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem centered_bilinear (b : E →L[ℝ] E →L[ℝ] F) (X : Ω → E)
    (hX : Integrable X μ) (hXX : Integrable (fun ω => b (X ω) (X ω)) μ) :
    (∫ ω, b (X ω - ∫ η, X η ∂μ) (X ω - ∫ η, X η ∂μ) ∂μ) =
      (∫ ω, b (X ω) (X ω) ∂μ) - b (∫ η, X η ∂μ) (∫ η, X η ∂μ) := by
  let m := ∫ η, X η ∂μ
  have hXm : Integrable (fun ω => b (X ω) m) μ := (b.flip m).integrable_comp hX
  have hmX : Integrable (fun ω => b m (X ω)) μ := (b m).integrable_comp hX
  have hcc : Integrable (fun _ : Ω => b m m) μ := integrable_const _
  have h1 : (∫ ω, b (X ω) m ∂μ) = b m m := (b.flip m).integral_comp_comm hX
  have h2 : (∫ ω, b m (X ω) ∂μ) = b m m := (b m).integral_comp_comm hX
  change (∫ ω, b (X ω-m) (X ω-m) ∂μ) = _
  simp only [map_sub,ContinuousLinearMap.sub_apply]
  calc
    _ = (∫ ω, b (X ω) (X ω)-b m (X ω) ∂μ) -
        (∫ ω, b (X ω) m-b m m ∂μ) := integral_sub (hXX.sub hmX) (hXm.sub hcc)
    _ = _ := by
      rw [integral_sub hXX hmX,integral_sub hXm hcc,h1,h2]
      simp [m]

theorem centered_bilinear_integrable (b : E →L[ℝ] E →L[ℝ] F) (X : Ω → E)
    (hX : Integrable X μ) (hXX : Integrable (fun ω => b (X ω) (X ω)) μ) :
    Integrable (fun ω => b (X ω - ∫ η, X η ∂μ) (X ω - ∫ η, X η ∂μ)) μ := by
  simp only [map_sub,ContinuousLinearMap.sub_apply]
  exact (hXX.sub ((b _).integrable_comp hX)).sub
    (((b.flip _).integrable_comp hX).sub (integrable_const _))

variable [MeasurableSpace E] [BorelSpace E]

theorem independent_zero_bilinear (b : E →L[ℝ] E →L[ℝ] F) {X Y : Ω → E}
    (h : IndepFun X Y μ) (hX : Integrable X μ) (hY : Integrable Y μ)
    (hmX : (∫ ω, X ω ∂μ)=0) (hmY : (∫ ω,Y ω ∂μ)=0) :
    (∫ ω, b (X ω) (Y ω) ∂μ) = 0 := by
  rw [h.integral_bilin hX hY b,hmX,hmY]
  simp

theorem sum_bilinear_zero_mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : E →L[ℝ] E →L[ℝ] F) (X : ι → Ω → E)
    (hInd : iIndepFun X μ) (hInt : ∀ i, Integrable (X i) μ)
    (hProd : ∀ i j, Integrable (fun ω => b (X i ω) (X j ω)) μ)
    (hm : ∀ i, (∫ ω, X i ω ∂μ)=0) :
    (∫ ω, b (∑ i, X i ω) (∑ j, X j ω) ∂μ) =
      ∑ i, ∫ ω, b (X i ω) (X i ω) ∂μ := by
  simp only [map_sum,ContinuousLinearMap.sum_apply]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hProd j i))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finset_sum _ (fun j _ => hProd j i)]
  apply Finset.sum_eq_single i
  · intro j hj hji
    exact independent_zero_bilinear μ b (hInd.indepFun hji) (hInt j) (hInt i) (hm j) (hm i)
  · simp
end Queelius.MatrixSampling

end



section
namespace Queelius.MatrixSampling
open MeasureTheory ProbabilityTheory Matrix TroppMatrixConcentration
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
set_option maxHeartbeats 2000000
variable {p q : ℕ}

noncomputable def gramLeft (p q : ℕ) :
    Matrix (Fin p) (Fin q) ℂ →L[ℝ]
      (Matrix (Fin p) (Fin q) ℂ →L[ℝ] Matrix (Fin p) (Fin p) ℂ) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun X => LinearMap.toContinuousLinearMap {
      toFun := fun Y => X * Y.conjTranspose
      map_add' := by intro Y Z; simp only [conjTranspose_add,Matrix.mul_add]
      map_smul' := by intro a Y; simp [conjTranspose_smul,Matrix.mul_smul]
    }
    map_add' := by intro X Y; ext Z i j; simp [Matrix.add_mul]
    map_smul' := by intro a X; ext Y i j; simp [Matrix.smul_mul]
  }
noncomputable def gramRight (p q : ℕ) :
    Matrix (Fin p) (Fin q) ℂ →L[ℝ]
      (Matrix (Fin p) (Fin q) ℂ →L[ℝ] Matrix (Fin q) (Fin q) ℂ) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun X => LinearMap.toContinuousLinearMap {
      toFun := fun Y => X.conjTranspose * Y
      map_add' := by intro Y Z; simp only [Matrix.mul_add]
      map_smul' := by intro a Y; simp [Matrix.mul_smul]
    }
    map_add' := by intro X Y; ext Z i j; simp [conjTranspose_add,Matrix.add_mul]
    map_smul' := by intro a X; ext Y i j; simp [conjTranspose_smul,Matrix.smul_mul]
  }

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

 theorem bounded_integrable (X : Ω → Matrix (Fin p) (Fin q) ℂ) (L : ℝ)
    (hM : Measurable X) (hb : ∀ᵐ ω ∂μ, ‖X ω‖ ≤ L) : Integrable X μ :=
  (integrable_const L).mono' hM.aestronglyMeasurable hb

 theorem centered_left (X : Ω → Matrix (Fin p) (Fin q) ℂ)
    (hX : Integrable X μ) (hXX : Integrable (fun ω => X ω * (X ω).conjTranspose) μ) :
    (∫ ω, (X ω - ∫ η,X η ∂μ)*(X ω-∫ η,X η ∂μ).conjTranspose ∂μ) =
      (∫ ω, X ω*(X ω).conjTranspose ∂μ) -
        (∫ η,X η ∂μ)*(∫ η,X η ∂μ).conjTranspose :=
  centered_bilinear μ (gramLeft p q) X hX hXX

 theorem centered_right (X : Ω → Matrix (Fin p) (Fin q) ℂ)
    (hX : Integrable X μ) (hXX : Integrable (fun ω => (X ω).conjTranspose * X ω) μ) :
    (∫ ω, (X ω - ∫ η,X η ∂μ).conjTranspose*(X ω-∫ η,X η ∂μ) ∂μ) =
      (∫ ω, (X ω).conjTranspose*X ω ∂μ) -
        (∫ η,X η ∂μ).conjTranspose*(∫ η,X η ∂μ) :=
  centered_bilinear μ (gramRight p q) X hX hXX

 theorem centered_left_norm_le [NeZero p] (X : Ω → Matrix (Fin p) (Fin q) ℂ)
    (hX : Integrable X μ) (hXX : Integrable (fun ω => X ω * (X ω).conjTranspose) μ) :
    ‖∫ ω, (X ω - ∫ η,X η ∂μ)*(X ω-∫ η,X η ∂μ).conjTranspose ∂μ‖ ≤
      ‖∫ ω, X ω*(X ω).conjTranspose ∂μ‖ := by
  apply CStarAlgebra.norm_le_norm_of_nonneg_of_le
  · exact integral_nonneg (fun ω => (Matrix.posSemidef_self_mul_conjTranspose _).nonneg)
  · rw [centered_left μ X hX hXX]
    exact sub_le_self _ (Matrix.posSemidef_self_mul_conjTranspose _).nonneg

 theorem centered_right_norm_le [NeZero q] (X : Ω → Matrix (Fin p) (Fin q) ℂ)
    (hX : Integrable X μ) (hXX : Integrable (fun ω => (X ω).conjTranspose * X ω) μ) :
    ‖∫ ω, (X ω - ∫ η,X η ∂μ).conjTranspose*(X ω-∫ η,X η ∂μ) ∂μ‖ ≤
      ‖∫ ω, (X ω).conjTranspose*X ω ∂μ‖ := by
  apply CStarAlgebra.norm_le_norm_of_nonneg_of_le
  · exact integral_nonneg (fun ω => (Matrix.posSemidef_conjTranspose_mul_self _).nonneg)
  · rw [centered_right μ X hX hXX]
    exact sub_le_self _ (Matrix.posSemidef_conjTranspose_mul_self _).nonneg

 theorem centered_secondMoment_le [NeZero p] [NeZero q]
    (X : Ω → Matrix (Fin p) (Fin q) ℂ) (L : ℝ)
    (hM : Measurable X) (hb : ∀ᵐ ω ∂μ, spectralNorm (X ω) ≤ L) :
    rectSecondMoment μ (fun ω => X ω - ∫ η,X η ∂μ) ≤ rectSecondMoment μ X := by
  have hX := bounded_integrable μ X L hM hb
  have hL := (gramLeft p q).integrable_of_bilin_of_bdd_left L hX.aestronglyMeasurable hb hX
  have hR := (gramRight p q).integrable_of_bilin_of_bdd_left L hX.aestronglyMeasurable hb hX
  exact max_le_max (centered_left_norm_le μ X hX hL) (centered_right_norm_le μ X hX hR)
end Queelius.MatrixSampling

end

section
namespace Queelius.MatrixSampling
open MeasureTheory ProbabilityTheory Matrix TroppMatrixConcentration IntroMatrixConc.Sampling
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
set_option maxHeartbeats 2000000
variable {Ω E F : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem iid_bilinear_average {n : ℕ} (hn : 0<n)
    (b : E →L[ℝ] E →L[ℝ] F) (X₀ : Ω → E) (X : Fin n → Ω → E) (L : ℝ)
    (hInd : iIndepFun X μ) (hCopy : ∀ k, IdentDistrib (X k) X₀ μ μ)
    (hInt : Integrable X₀ μ) (hBound : ∀ᵐ ω ∂μ, ‖X₀ ω‖ ≤ L)
    (hMean : (∫ ω,X₀ ω ∂μ)=0) :
    (∫ ω, b (((n:ℝ)⁻¹) • ∑ k,X k ω) (((n:ℝ)⁻¹) • ∑ k,X k ω) ∂μ) =
      ((n:ℝ)⁻¹) • (∫ ω,b (X₀ ω) (X₀ ω) ∂μ) := by
  have hi (k : Fin n) : Integrable (X k) μ := (hCopy k).symm.integrable_snd hInt
  have hb (k : Fin n) : ∀ᵐ ω ∂μ, ‖X k ω‖ ≤ L :=
    (hCopy k).symm.ae_snd (isClosed_le continuous_norm continuous_const).measurableSet hBound
  have hp (i j : Fin n) : Integrable (fun ω => b (X i ω) (X j ω)) μ :=
    b.integrable_of_bilin_of_bdd_left L (hi i).aestronglyMeasurable (hb i) (hi j)
  have hm (k : Fin n) : (∫ ω,X k ω ∂μ)=0 := (hCopy k).integral_eq.trans hMean
  have hd (k : Fin n) : (∫ ω,b (X k ω) (X k ω) ∂μ) = (∫ ω,b (X₀ ω) (X₀ ω) ∂μ) :=
    ((hCopy k).comp (b.continuous.clm_apply continuous_id).measurable).integral_eq
  have hs := sum_bilinear_zero_mean μ b X hInd hi hp hm
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_smul]
  rw [integral_smul,hs]
  simp only [hd,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
  congr 1
  have hnr : (n:ℝ) ≠ 0 := by positivity
  field_simp

end Queelius.MatrixSampling

end

section
open MeasureTheory ProbabilityTheory TroppMatrixConcentration IntroMatrixConc.Sampling
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
set_option maxHeartbeats 2500000
noncomputable section
namespace Queelius.MatrixSampling

theorem sampling_centering {Ω : Type*} {p q n : ℕ} (hn : 0<n)
    (R : Fin n → Ω → Matrix (Fin p) (Fin q) ℂ) (B : Matrix (Fin p) (Fin q) ℂ) (ω : Ω) :
    ((n:ℝ)⁻¹) • ∑ k, (R k ω-B) = samplingEstimator R ω-B := by
  have hnr : (n:ℝ) ≠ 0 := by positivity
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_sub]
  rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul,inv_mul_cancel₀ hnr,one_smul]
  rfl

 theorem variance_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d₁ d₂ n : ℕ} [NeZero d₁] [NeZero d₂]
    (R₀ : Ω → Matrix (Fin d₁) (Fin d₂) ℂ)
    (R : Fin n → Ω → Matrix (Fin d₁) (Fin d₂) ℂ)
    (B : Matrix (Fin d₁) (Fin d₂) ℂ) (L : ℝ)
    (hn : 0 < n)
    (hMeas₀ : Measurable R₀) (hMeas : ∀ k, Measurable (R k))
    (hIndep : iIndepFun R μ)
    (hCopies : ∀ k, IdentDistrib (R k) R₀ μ μ)
    (hMean : (∫ ω, R₀ ω ∂μ) = B)
    (hBound : ∀ᵐ ω ∂μ, spectralNorm (R₀ ω) ≤ L) :
    rectSecondMoment μ (fun ω => samplingEstimator R ω - B) ≤
      rectSecondMoment μ R₀ / n := by
  let X₀ := fun ω => R₀ ω-B
  let X := fun k ω => R k ω-B
  have hi₀ := bounded_integrable μ R₀ L hMeas₀ hBound
  have hi : Integrable X₀ μ := hi₀.sub (integrable_const _)
  have hb : ∀ᵐ ω ∂μ, ‖X₀ ω‖ ≤ L+‖B‖ := by
    filter_upwards [hBound] with ω hω
    exact (norm_sub_le _ _).trans (add_le_add hω le_rfl)
  have hm : (∫ ω,X₀ ω ∂μ)=0 := by
    change (∫ ω,R₀ ω-B ∂μ)=0
    rw [integral_sub hi₀ (integrable_const B),hMean]
    simp
  have hc (k : Fin n) : IdentDistrib (X k) X₀ μ μ := (hCopies k).sub_const B
  have hind : iIndepFun X μ := hIndep.comp (fun _ x => x-B) (fun _ => measurable_id.sub measurable_const)
  have hL := iid_bilinear_average μ hn (gramLeft d₁ d₂) X₀ X (L+‖B‖) hind hc hi hb hm
  have hR := iid_bilinear_average μ hn (gramRight d₁ d₂) X₀ X (L+‖B‖) hind hc hi hb hm
  dsimp [X] at hL hR
  simp only [sampling_centering hn] at hL hR
  change (∫ ω,(samplingEstimator R ω-B)*(samplingEstimator R ω-B).conjTranspose ∂μ) =
    ((n:ℝ)⁻¹) • (∫ ω,X₀ ω*(X₀ ω).conjTranspose ∂μ) at hL
  change (∫ ω,(samplingEstimator R ω-B).conjTranspose*(samplingEstimator R ω-B) ∂μ) =
    ((n:ℝ)⁻¹) • (∫ ω,(X₀ ω).conjTranspose*X₀ ω ∂μ) at hR
  have hpos : 0 ≤ (n:ℝ)⁻¹ := by positivity
  have hcenter : rectSecondMoment μ X₀ ≤ rectSecondMoment μ R₀ := by
    simpa only [hMean] using centered_secondMoment_le μ R₀ L hMeas₀ hBound
  unfold rectSecondMoment TroppMatrixConcentration.spectralNorm
  rw [hL,hR]
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hpos]
  rw [← mul_max_of_nonneg _ _ hpos]
  calc
    _ ≤ (n:ℝ)⁻¹ * rectSecondMoment μ R₀ := mul_le_mul_of_nonneg_left hcenter hpos
    _ = _ := by rw [div_eq_mul_inv]; exact mul_comm _ _
end Queelius.MatrixSampling

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d₁ d₂ n : ℕ} [NeZero d₁] [NeZero d₂]
    (R₀ : Ω → Matrix (Fin d₁) (Fin d₂) ℂ)
    (R : Fin n → Ω → Matrix (Fin d₁) (Fin d₂) ℂ)
    (B : Matrix (Fin d₁) (Fin d₂) ℂ) (L : ℝ)
    (hn : 0 < n)
    (hMeas₀ : Measurable R₀) (hMeas : ∀ k, Measurable (R k))
    (hIndep : iIndepFun R μ)
    (hCopies : ∀ k, IdentDistrib (R k) R₀ μ μ)
    (hMean : (∫ ω, R₀ ω ∂μ) = B)
    (hBound : ∀ᵐ ω ∂μ, spectralNorm (R₀ ω) ≤ L) :
    rectSecondMoment μ (fun ω => samplingEstimator R ω - B) ≤
      rectSecondMoment μ R₀ / n :=
  Queelius.MatrixSampling.variance_bound μ R₀ R B L hn hMeas₀ hMeas hIndep hCopies hMean hBound

end

section
namespace Queelius.MatrixSampling.Controls
open MeasureTheory ProbabilityTheory TroppMatrixConcentration IntroMatrixConc.Sampling
open scoped Matrix.Norms.L2Operator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
variable {p q : ℕ}

theorem estimator_one (X : Fin 1 → Ω → Matrix (Fin p) (Fin q) ℂ) (ω : Ω) :
    samplingEstimator X ω = X 0 ω := by
  simp [samplingEstimator]

theorem estimator_repeated {n : ℕ} (hn : 0<n) (X : Ω → Matrix (Fin p) (Fin q) ℂ) (ω : Ω) :
    samplingEstimator (fun _ : Fin n => X) ω = X ω := by
  have hnR : (n:ℝ) ≠ 0 := by positivity
  simp only [samplingEstimator,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul,inv_mul_cancel₀ hnR,one_smul]

theorem constant_zero_error {n : ℕ} (hn : 0<n) (B : Matrix (Fin p) (Fin q) ℂ) :
    rectSecondMoment μ (fun ω => samplingEstimator (fun _ : Fin n => fun _ : Ω => B) ω-B)=0 := by
  simp [estimator_repeated hn,rectSecondMoment,TroppMatrixConcentration.spectralNorm]

theorem correlated_two_failure (X : Ω → Matrix (Fin p) (Fin q) ℂ)
    (hMean : (∫ ω,X ω ∂μ)=0) (hPositive : 0 < rectSecondMoment μ X) :
    ¬ rectSecondMoment μ (fun ω => samplingEstimator (fun _ : Fin 2 => X) ω-0) ≤
      rectSecondMoment μ X/2 := by
  simp only [estimator_repeated (by decide : 0<2),sub_zero]
  linarith

/-- Exact finite equal-weight sign computation underlying the dependence control. -/
theorem repeated_signs_control :
    (((-1:ℝ)+(-1))/2)^2/2 + (((1:ℝ)+1)/2)^2/2=1 ∧ (1/2:ℝ)<1 := by
  norm_num
end Queelius.MatrixSampling.Controls

end
