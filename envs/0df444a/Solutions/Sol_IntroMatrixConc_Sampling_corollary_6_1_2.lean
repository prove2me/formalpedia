-- Prove2me | solution 1 for IntroMatrixConc.Sampling.corollary_6_1_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T06:31:39.279689+00:00
-- url     : https://prove2.me/submissions/f2bc4706-022b-48d9-ae64-2ff378a7b18e

import Init
import Mathlib
import Definitions.Def_IntroMatrixConc_Sampling_Defs
import Theorems.Thm_TroppMatrixConcentration_matrix_bernstein

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

theorem sampling_expectation_arithmetic (n L m v ell : ℝ) (hn : 0 < n)
    (hell : 0 ≤ ell) (hv : v ≤ m/n) :
    Real.sqrt (2*v*ell)+(2*L/n)*ell/3  ≤ 
      Real.sqrt (2*m*ell/n)+2*L*ell/(3*n) := by
  have hs : 2*v*ell  ≤  2*m*ell/n := by
    calc
      _  ≤  2*(m/n)*ell := by gcongr
      _ = _ := by ring
  apply add_le_add (Real.sqrt_le_sqrt hs)
  exact le_of_eq (by ring)

theorem sampling_tail_exponent (n L m v t : ℝ) (hn : 0 < n) (hL : 0 < L)
    (hm : 0 ≤ m) (hv0 : 0 ≤ v) (hv : v ≤ m/n) (ht : 0 < t) :
    -(t^2/2)/(v+(2*L/n)*t/3)  ≤ 
      (- (n*t^2)/2)/(m+2*L*t/3) := by
  have ha : 0  <  v+(2*L/n)*t/3 := by positivity
  have hb : 0  <  m/n+(2*L/n)*t/3 := by positivity
  have hc : 0  <  m+2*L*t/3 := by positivity
  have hd : v+(2*L/n)*t/3  ≤  m/n+(2*L/n)*t/3 := by linarith
  calc
    _  ≤  -(t^2/2)/(m/n+(2*L/n)*t/3) := by
      rw [neg_div,neg_div]
      exact neg_le_neg (div_le_div_of_nonneg_left (by positivity) ha hd)
    _ = _ := by field_simp <;> ring

/-- Total division at a zero denominator prevents a blind monotonicity step. -/
theorem zero_denominator_control : ¬ (-(1:ℝ)/0  ≤  -(1:ℝ)/1) := by norm_num

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

theorem Queelius.MatrixSampling.variance_submission {Ω : Type*} [MeasurableSpace Ω]
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

section
namespace Queelius.MatrixSampling
open MeasureTheory ProbabilityTheory Matrix TroppMatrixConcentration IntroMatrixConc.Sampling
open scoped Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 2500000
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {p q n : ℕ}

theorem mean_norm_le (X : Ω → Matrix (Fin p) (Fin q) ℂ) (L : ℝ)
    (hb : ∀ᵐ ω ∂μ, ‖X ω‖ ≤ L) : ‖∫ ω, X ω ∂μ‖ ≤ L := by
  simpa using norm_integral_le_of_norm_le_const hb

theorem radius_nonneg (X : Ω → Matrix (Fin p) (Fin q) ℂ) (L : ℝ)
    (hb : ∀ᵐ ω ∂μ, ‖X ω‖ ≤ L) : 0 ≤ L :=
  (norm_nonneg _).trans (mean_norm_le μ X L hb)

theorem copy_bound (R₀ : Ω → Matrix (Fin p) (Fin q) ℂ)
    (R : Fin n → Ω → Matrix (Fin p) (Fin q) ℂ) (L : ℝ)
    (hc : ∀ k, IdentDistrib (R k) R₀ μ μ)
    (hb : ∀ᵐ ω ∂μ, ‖R₀ ω‖ ≤ L) (k : Fin n) : ∀ᵐ ω ∂μ, ‖R k ω‖ ≤ L :=
  (hc k).symm.ae_snd (isClosed_le continuous_norm continuous_const).measurableSet hb

theorem estimator_integrable (R : Fin n → Ω → Matrix (Fin p) (Fin q) ℂ)
    (hi : ∀ k, Integrable (R k) μ) : Integrable (samplingEstimator R) μ :=
  (integrable_finset_sum Finset.univ (fun k _ => hi k)).smul ((n:ℝ)⁻¹)

theorem estimator_mean (hn : 0<n) (R : Fin n → Ω → Matrix (Fin p) (Fin q) ℂ)
    (B : Matrix (Fin p) (Fin q) ℂ) (hi : ∀ k, Integrable (R k) μ)
    (hm : ∀ k, (∫ ω,R k ω ∂μ)=B) : (∫ ω,samplingEstimator R ω ∂μ)=B := by
  unfold samplingEstimator
  rw [integral_smul,integral_finset_sum _ (fun k _ => hi k)]
  simp only [hm,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul,inv_mul_cancel₀ (by positivity : (n:ℝ)≠0),one_smul]

theorem estimator_bound (hn : 0<n) (R : Fin n → Ω → Matrix (Fin p) (Fin q) ℂ)
    (L : ℝ) (hb : ∀ k, ∀ᵐ ω ∂μ, ‖R k ω‖ ≤ L) :
    ∀ᵐ ω ∂μ, ‖samplingEstimator R ω‖ ≤ L := by
  filter_upwards [ae_all_iff.mpr hb] with ω hω
  have hn0 : 0 ≤ (n:ℝ)⁻¹ := by positivity
  calc
    ‖samplingEstimator R ω‖ = (n:ℝ)⁻¹ * ‖∑ k,R k ω‖ := by
      simp [samplingEstimator,norm_smul,Real.norm_eq_abs,abs_of_nonneg hn0]
    _ ≤ (n:ℝ)⁻¹ * ∑ k, ‖R k ω‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hn0
    _ ≤ (n:ℝ)⁻¹ * ∑ _k : Fin n,L :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => hω k)) hn0
    _ = L := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp

noncomputable def samplingSummands (R : Fin n → Ω → Matrix (Fin p) (Fin q) ℂ)
    (B : Matrix (Fin p) (Fin q) ℂ) : Fin n → Ω → Matrix (Fin p) (Fin q) ℂ :=
  fun k ω => (n:ℝ)⁻¹ • (R k ω-B)

theorem summands_sum (hn : 0<n) (R : Fin n → Ω → Matrix (Fin p) (Fin q) ℂ)
    (B : Matrix (Fin p) (Fin q) ℂ) (ω : Ω) :
    (∑ k,samplingSummands R B k ω)=samplingEstimator R ω-B := by
  simp only [samplingSummands,← Finset.smul_sum,sampling_centering hn]

theorem summands_data (hn : 0<n) (R : Fin n → Ω → Matrix (Fin p) (Fin q) ℂ)
    (B : Matrix (Fin p) (Fin q) ℂ) (L : ℝ)
    (hm : ∀ k, Measurable (R k)) (hi : ∀ k, Integrable (R k) μ)
    (hind : iIndepFun R μ) (hmean : ∀ k,(∫ ω,R k ω ∂μ)=B)
    (hb : ∀ k,∀ᵐ ω ∂μ,‖R k ω‖≤L) (hB : ‖B‖≤L) :
    (∀ k,Measurable (samplingSummands R B k)) ∧
    (∀ k,Integrable (samplingSummands R B k) μ) ∧
    iIndepFun (samplingSummands R B) μ ∧
    (∀ k,(∫ ω,samplingSummands R B k ω ∂μ)=0) ∧
    (∀ k,∀ᵐ ω ∂μ,‖samplingSummands R B k ω‖≤2*L/n) := by
  refine ⟨fun k => ((hm k).sub measurable_const).const_smul ((n:ℝ)⁻¹),
    fun k => ((hi k).sub (integrable_const B)).smul ((n:ℝ)⁻¹),
    hind.comp (fun _ x => (n:ℝ)⁻¹ • (x-B)) (fun _ => (measurable_id.sub measurable_const).const_smul ((n:ℝ)⁻¹)),?_,?_⟩
  · intro k
    simp only [samplingSummands,integral_smul,integral_sub (hi k) (integrable_const B),hmean]
    simp
  · intro k
    filter_upwards [hb k] with ω hω
    calc
      ‖samplingSummands R B k ω‖ = (n:ℝ)⁻¹ * ‖R k ω-B‖ := by
        simp [samplingSummands,norm_smul,Real.norm_eq_abs,abs_of_nonneg (show 0≤(n:ℝ)⁻¹ by positivity)]
      _ ≤ (n:ℝ)⁻¹*(2*L) := mul_le_mul_of_nonneg_left
        ((norm_sub_le _ _).trans (by linarith)) (by positivity)
      _ = _ := by ring
end
end Queelius.MatrixSampling

end

section
namespace Queelius.MatrixSampling
open MeasureTheory ProbabilityTheory Matrix TroppMatrixConcentration IntroMatrixConc.Sampling
open scoped Matrix.Norms.L2Operator
set_option maxHeartbeats 2500000
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {p q N : ℕ}

theorem uncentered_bilinear
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (b : Matrix (Fin p) (Fin q) ℂ →L[ℝ] Matrix (Fin p) (Fin q) ℂ →L[ℝ] F)
    (S : Fin N → Ω → Matrix (Fin p) (Fin q) ℂ) (L : ℝ)
    (hi : ∀ k, Integrable (S k) μ) (hind : iIndepFun S μ)
    (hb : ∀ k, ∀ᵐ ω ∂μ, ‖S k ω-∫ η,S k η ∂μ‖ ≤ L) :
    (∫ ω,b ((∑ k,S k ω)-∫ η,∑ k,S k η ∂μ) ((∑ k,S k ω)-∫ η,∑ k,S k η ∂μ) ∂μ) =
      ∑ k,∫ ω,b (S k ω-∫ η,S k η ∂μ) (S k ω-∫ η,S k η ∂μ) ∂μ := by
  let X := fun k ω => S k ω-∫ η,S k η ∂μ
  have hX (k : Fin N) : Integrable (X k) μ := (hi k).sub (integrable_const _)
  have hzero (k : Fin N) : (∫ ω,X k ω ∂μ)=0 := by
    simp [X,integral_sub (hi k) (integrable_const _)]
  have hprod (i j : Fin N) : Integrable (fun ω => b (X i ω) (X j ω)) μ :=
    b.integrable_of_bilin_of_bdd_left L (hX i).aestronglyMeasurable (hb i) (hX j)
  have hIndX : iIndepFun X μ :=
    hind.comp (fun k x => x-∫ η,S k η ∂μ) (fun _ => measurable_id.sub measurable_const)
  have hsum (ω : Ω) : (∑ k,X k ω)=(∑ k,S k ω)-∫ η,∑ k,S k η ∂μ := by
    simp only [X,Finset.sum_sub_distrib,integral_finset_sum _ (fun k _ => hi k)]
  simpa only [hsum] using sum_bilinear_zero_mean μ b X hIndX hX hprod hzero

theorem uncentered_variance
    (S : Fin N → Ω → Matrix (Fin p) (Fin q) ℂ) (L : ℝ)
    (hi : ∀ k, Integrable (S k) μ) (hind : iIndepFun S μ)
    (hb : ∀ k, ∀ᵐ ω ∂μ, spectralNorm (S k ω-∫ η,S k η ∂μ) ≤ L) :
    rectSecondMoment μ (fun ω => (∑ k,S k ω)-∫ η,∑ k,S k η ∂μ) =
      max (spectralNorm (∑ k,∫ ω,(S k ω-∫ η,S k η ∂μ)*
        (S k ω-∫ η,S k η ∂μ).conjTranspose ∂μ))
      (spectralNorm (∑ k,∫ ω,(S k ω-∫ η,S k η ∂μ).conjTranspose*
        (S k ω-∫ η,S k η ∂μ) ∂μ)) := by
  have hL := uncentered_bilinear μ (gramLeft p q) S L hi hind hb
  have hR := uncentered_bilinear μ (gramRight p q) S L hi hind hb
  unfold rectSecondMoment
  exact congrArg₂ (fun x y => max (spectralNorm x) (spectralNorm y)) hL hR

/-- The expectation and tail portion of the open uncentered matrix Bernstein target.
This is an explicit proposition parameter, not an axiom or a proof of concentration. -/
def BernsteinRule (p q : ℕ) : Prop :=
  ∀ {N : ℕ} (S : Fin N → Ω → Matrix (Fin p) (Fin q) ℂ) (L : ℝ), 0≤L →
    (∀ k,Measurable (S k)) → (∀ k,Integrable (S k) μ) → iIndepFun S μ →
    (∀ k,∀ᵐ ω ∂μ,spectralNorm (S k ω-∫ η,S k η ∂μ)≤L) →
    let Z := fun ω => (∑ k,S k ω)-∫ η,∑ k,S k η ∂μ
    let V := rectSecondMoment μ Z
    (∫ ω,spectralNorm (Z ω) ∂μ) ≤ Real.sqrt (2*V*Real.log (p+q)) + L*Real.log (p+q)/3 ∧
    ∀ t : ℝ,0≤t → (μ {ω | t≤ spectralNorm (Z ω)}).toReal ≤
      (p+q:ℕ)*Real.exp (-(t^2/2)/(V+L*t/3))
end Queelius.MatrixSampling

end

section
namespace Queelius.MatrixSampling
open MeasureTheory ProbabilityTheory Matrix TroppMatrixConcentration IntroMatrixConc.Sampling
open scoped Matrix.Norms.L2Operator
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {p q : ℕ}

theorem zero_radius (R : Ω → Matrix (Fin p) (Fin q) ℂ)
    (hb : ∀ᵐ ω ∂μ, spectralNorm (R ω) ≤ 0) :
    (∀ᵐ ω ∂μ, R ω = 0) ∧ (∫ ω, R ω ∂μ) = 0 ∧ rectSecondMoment μ R = 0 := by
  have hz : ∀ᵐ ω ∂μ, R ω = 0 := by
    filter_upwards [hb] with ω hω
    exact norm_eq_zero.mp (le_antisymm hω (norm_nonneg _))
  refine ⟨hz, ?_, ?_⟩
  · exact (integral_congr_ae hz).trans (integral_zero Ω _)
  · have hl : (∫ ω, R ω * (R ω).conjTranspose ∂μ) = 0 := by
      have he : (fun ω => R ω * (R ω).conjTranspose) =ᵐ[μ] fun _ => 0 := by
        filter_upwards [hz] with ω hω
        simp [hω]
      simpa using integral_congr_ae he
    have hr : (∫ ω, (R ω).conjTranspose * R ω ∂μ) = 0 := by
      have he : (fun ω => (R ω).conjTranspose * R ω) =ᵐ[μ] fun _ => 0 := by
        filter_upwards [hz] with ω hω
        simp [hω]
      simpa using integral_congr_ae he
    simp [rectSecondMoment, hl, hr, TroppMatrixConcentration.spectralNorm]

theorem empty_estimator_control
    (R : Fin 0 → Ω → Matrix (Fin p) (Fin q) ℂ) (B : Matrix (Fin p) (Fin q) ℂ) (ω : Ω) :
    samplingEstimator R ω - B = -B := by simp [samplingEstimator]

end Queelius.MatrixSampling

end

section
namespace Queelius.MatrixSampling
open MeasureTheory ProbabilityTheory TroppMatrixConcentration IntroMatrixConc.Sampling
open scoped Matrix.Norms.L2Operator
set_option maxHeartbeats 80000
theorem sampling_of_bernstein {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d₁ d₂ n : ℕ} [NeZero d₁] [NeZero d₂]
    (hBernstein : BernsteinRule μ d₁ d₂)
    (R₀ : Ω → Matrix (Fin d₁) (Fin d₂) ℂ)
    (R : Fin n → Ω → Matrix (Fin d₁) (Fin d₂) ℂ)
    (B : Matrix (Fin d₁) (Fin d₂) ℂ) (L : ℝ)
    (hn : 0 < n)
    (hMeas₀ : Measurable R₀) (hMeas : ∀ k, Measurable (R k))
    (hIndep : iIndepFun R μ)
    (hCopies : ∀ k, IdentDistrib (R k) R₀ μ μ)
    (hMean : (∫ ω, R₀ ω ∂μ) = B)
    (hBound : ∀ᵐ ω ∂μ, spectralNorm (R₀ ω) ≤ L) :
    Integrable (fun ω => spectralNorm (samplingEstimator R ω - B)) μ ∧
    (∫ ω, spectralNorm (samplingEstimator R ω - B) ∂μ) ≤
      Real.sqrt (2 * rectSecondMoment μ R₀ * Real.log (d₁ + d₂) / n) +
        2 * L * Real.log (d₁ + d₂) / (3 * n) ∧
    ∀ t : ℝ, 0 ≤ t →
      (μ {ω | t ≤ spectralNorm (samplingEstimator R ω - B)}).toReal ≤
        (d₁ + d₂ : ℕ) * Real.exp
          ((-((n : ℝ) * t ^ 2) / 2) /
            (rectSecondMoment μ R₀ + 2 * L * t / 3)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hL : 0 ≤ L := radius_nonneg μ R₀ L hBound
  have hi₀ := bounded_integrable μ R₀ L hMeas₀ hBound
  have hi (k : Fin n) : Integrable (R k) μ := (hCopies k).symm.integrable_snd hi₀
  have hb (k : Fin n) : ∀ᵐ ω ∂μ, ‖R k ω‖ ≤ L := copy_bound μ R₀ R L hCopies hBound k
  have hm (k : Fin n) : (∫ ω, R k ω ∂μ) = B := (hCopies k).integral_eq.trans hMean
  have hB : ‖B‖ ≤ L := hMean ▸ mean_norm_le μ R₀ L hBound
  have hError : Integrable (fun ω => samplingEstimator R ω - B) μ :=
    (estimator_integrable μ R hi).sub (integrable_const B)
  have hErrBound : ∀ᵐ ω ∂μ, ‖samplingEstimator R ω - B‖ ≤ 2*L := by
    filter_upwards [estimator_bound μ hn R L hb] with ω hω
    exact (norm_sub_le _ _).trans (by linarith)
  let X := samplingSummands R B
  obtain ⟨hXm, hXi, hXind, hXzero, hXb⟩ := summands_data μ hn R B L hMeas hi hIndep hm hb hB
  have hZero : (∫ ω, ∑ k, X k ω ∂μ) = 0 := by
    rw [integral_finset_sum _ (fun k _ => hXi k)]
    simp only [X, hXzero, Finset.sum_const_zero]
  have hXbound : ∀ k, ∀ᵐ ω ∂μ, spectralNorm (X k ω - ∫ η, X k η ∂μ) ≤ 2*L/n := by
    intro k
    change ∀ᵐ ω ∂μ, ‖X k ω - ∫ η, X k η ∂μ‖ ≤ 2*L/n
    simpa only [X, hXzero, sub_zero] using hXb k
  have hConc := hBernstein X (2*L/n) (by positivity) hXm hXi hXind hXbound
  dsimp only at hConc
  simp only [hZero, sub_zero, X, summands_sum hn] at hConc
  have hErrorMean : (∫ ω, samplingEstimator R ω - B ∂μ) = 0 := by
    rw [integral_sub (estimator_integrable μ R hi) (integrable_const B), estimator_mean μ hn R B hi hm]
    simp
  rw [hErrorMean] at hConc
  simp only [sub_zero] at hConc
  have hVar := variance_bound μ R₀ R B L hn hMeas₀ hMeas hIndep hCopies hMean hBound
  have hV : 0 ≤ rectSecondMoment μ (fun ω => samplingEstimator R ω - B) :=
    (norm_nonneg _).trans (le_max_left _ _)
  have hM : 0 ≤ rectSecondMoment μ R₀ := (norm_nonneg _).trans (le_max_left _ _)
  have hd : (1 : ℝ) ≤ (d₁ + d₂ : ℕ) := by
    exact_mod_cast (show 1 ≤ d₁ + d₂ from by have := NeZero.pos d₁; omega)
  have hlog : 0 ≤ Real.log (d₁ + d₂) := by
    exact Real.log_nonneg (by exact_mod_cast hd)
  refine ⟨hError.norm, hConc.1.trans (sampling_expectation_arithmetic _ _ _ _ _ hnR hlog hVar), ?_⟩
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), neg_zero, zero_div, add_zero, Real.exp_zero, mul_one]
    exact measureReal_le_one.trans hd
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  by_cases hL0 : L = 0
  · have hz : μ {ω | t ≤ spectralNorm (samplingEstimator R ω - B)} = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hErrBound] with ω hω
      change ¬ t ≤ ‖samplingEstimator R ω - B‖
      rw [hL0] at hω
      linarith
    rw [hz, ENNReal.toReal_zero]
    positivity
  · have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
    apply (hConc.2 t ht).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    exact sampling_tail_exponent _ _ _ _ _ hnR hLpos hM hV hVar htpos
end Queelius.MatrixSampling

end

section
namespace Queelius.MatrixSampling
open MeasureTheory ProbabilityTheory TroppMatrixConcentration
open scoped Matrix.Norms.L2Operator

theorem bernsteinTail_le_plain (d : ℕ) (v L t : ℝ) :
    bernsteinTail d v L t ≤ (d:ℝ)*Real.exp (-(t^2/2)/(v+L*t/3)) := by
  unfold bernsteinTail
  split_ifs with hd ht
  · subst t
    simp
  · positivity
  · exact le_rfl

theorem bernstein_rule {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p q : ℕ) [NeZero p] [NeZero q] :
    BernsteinRule μ p q := by
  intro N S L hL hm hi hind hb
  let X := fun k ω => S k ω - ∫ η,S k η ∂μ
  have hXm (k : Fin N) : Measurable (X k) := (hm k).sub measurable_const
  have hXzero (k : Fin N) : (∫ ω,X k ω ∂μ) = 0 := by
    simp [X,integral_sub (hi k) (integrable_const _)]
  have hXind : iIndepFun X μ :=
    hind.comp (fun k x => x-∫ η,S k η ∂μ) (fun _ => measurable_id.sub measurable_const)
  have hsum (ω : Ω) : (∑ k,X k ω)=(∑ k,S k ω)-∫ η,∑ k,S k η ∂μ := by
    simp only [X,Finset.sum_sub_distrib,integral_finset_sum _ (fun k _ => hi k)]
  have h := TroppMatrixConcentration.matrix_bernstein μ X L hL hXm hXind hXzero hb
  dsimp only at h
  simp only [hsum] at h
  refine ⟨h.2.1,?_⟩
  intro t ht
  exact (h.2.2 t ht).trans (bernsteinTail_le_plain _ _ _ _)
end Queelius.MatrixSampling

end

section
namespace Queelius.MatrixSampling
open MeasureTheory ProbabilityTheory TroppMatrixConcentration IntroMatrixConc.Sampling
open scoped Matrix.Norms.L2Operator
set_option maxHeartbeats 80000
theorem sampling_complete {Ω : Type*} [MeasurableSpace Ω]
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
    Integrable (fun ω => spectralNorm (samplingEstimator R ω - B)) μ ∧
    (∫ ω, spectralNorm (samplingEstimator R ω - B) ∂μ) ≤
      Real.sqrt (2 * rectSecondMoment μ R₀ * Real.log (d₁ + d₂) / n) +
        2 * L * Real.log (d₁ + d₂) / (3 * n) ∧
    ∀ t : ℝ, 0 ≤ t →
      (μ {ω | t ≤ spectralNorm (samplingEstimator R ω - B)}).toReal ≤
        (d₁ + d₂ : ℕ) * Real.exp
          ((-((n : ℝ) * t ^ 2) / 2) /
            (rectSecondMoment μ R₀ + 2 * L * t / 3)) :=
  sampling_of_bernstein μ (bernstein_rule μ d₁ d₂) R₀ R B L hn hMeas₀ hMeas hIndep hCopies hMean hBound
end Queelius.MatrixSampling

end

section
open MeasureTheory ProbabilityTheory TroppMatrixConcentration
open scoped Matrix.Norms.L2Operator
namespace Queelius.MatrixSampling

/-- Tropp, Corollary 6.1.2, p. 77 (PDF p. 83). -/
theorem bernstein_complete {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d₁ d₂ N : ℕ} [NeZero d₁] [NeZero d₂]
    (S : Fin N → Ω → Matrix (Fin d₁) (Fin d₂) ℂ)
    (L : ℝ) (hL : 0 ≤ L)
    (hMeas : ∀ k, Measurable (S k))
    (hInt : ∀ k, Integrable (S k) μ)
    (hIndep : iIndepFun S μ)
    (hBound : ∀ k, ∀ᵐ ω ∂μ,
      spectralNorm (S k ω - ∫ ω, S k ω ∂μ) ≤ L) :
    let Z := fun ω => ∑ k, S k ω
    let V := rectSecondMoment μ (fun ω => Z ω - ∫ ω, Z ω ∂μ)
    V = max
      (spectralNorm (∑ k, ∫ ω,
        (S k ω - ∫ η, S k η ∂μ) * (S k ω - ∫ η, S k η ∂μ).conjTranspose ∂μ))
      (spectralNorm (∑ k, ∫ ω,
        (S k ω - ∫ η, S k η ∂μ).conjTranspose * (S k ω - ∫ η, S k η ∂μ) ∂μ)) ∧
    (∫ ω, spectralNorm (Z ω - ∫ η, Z η ∂μ) ∂μ) ≤
      Real.sqrt (2 * V * Real.log (d₁ + d₂)) + L * Real.log (d₁ + d₂) / 3 ∧
    ∀ t : ℝ, 0 ≤ t →
      (μ {ω | t ≤ spectralNorm (Z ω - ∫ η, Z η ∂μ)}).toReal ≤
        (d₁ + d₂ : ℕ) * Real.exp (-(t ^ 2 / 2) / (V + L * t / 3)) := by
  dsimp only
  exact ⟨uncentered_variance μ S L hInt hIndep hBound,
    bernstein_rule μ d₁ d₂ S L hL hMeas hInt hIndep hBound⟩

end Queelius.MatrixSampling

namespace Queelius.MatrixSampling
open MeasureTheory ProbabilityTheory TroppMatrixConcentration
open scoped Matrix.Norms.L2Operator

theorem bernstein_zero_positive_control (d : ℕ) (t : ℝ) (ht : 0 < t) :
    bernsteinTail d 0 0 t = 0 ∧
      (d:ℝ)*Real.exp (-(t^2/2)/(0+(0:ℝ)*t/3)) = d := by
  simp [bernsteinTail,ne_of_gt ht]

theorem bernstein_zero_origin_control (d : ℕ) : bernsteinTail d 0 0 0 = d := by
  simp [bernsteinTail]

end Queelius.MatrixSampling

end

alias solution := Queelius.MatrixSampling.bernstein_complete
