-- Prove2me | solution 1 for OAI.IsingPerceptron.enriched_poisson_root_variance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:15:31.644915+00:00
-- url     : https://prove2.me/submissions/8f52d1fd-8994-452e-9867-cdaf0ace821c

import Mathlib
import Definitions.Def_OAIQ258003

section
-- module Solutions.OAIQ258_II.IsingPerceptron_CountableMonomialGG
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countable Monomial G G. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma gaussian_weighted_sum_law {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    HasLaw (fun g : ι → ℝ => ∑ i, a i * g i)
      (gaussianReal 0 ((∑ i, a i ^ 2).toNNReal))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  have hi : iIndepFun (fun i => fun g : ι → ℝ => a i * g i)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    iIndepFun_pi (fun _ => by fun_prop)
  have hl i : HasLaw (fun g : ι → ℝ => g i) (gaussianReal 0 1)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).hasLaw
  have hg := hi.hasGaussianLaw_fun_sum (fun i => (gaussianReal_const_mul (hl i) (a i)).hasGaussianLaw)
  refine ⟨(by fun_prop : Measurable (fun g : ι → ℝ => ∑ i, a i * g i)).aemeasurable, ?_⟩
  rw [hg.map_eq_gaussianReal]
  congr 1
  · have hI i : Integrable (fun g : ι → ℝ => a i * g i)
        (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
      ((measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).integrable_comp_of_integrable
        ((memLp_id_gaussianReal 1).integrable le_rfl)).const_mul (a i)
    rw [integral_finsetSum _ (fun i _ => hI i)]
    simp_rw [integral_const_mul]
    have hz i : (∫ g : ι → ℝ, g i ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = 0 := by
      simpa using (hl i).integral_eq
    simp [hz]
  · congr 1
    have hv i : Var[fun x : ℝ => a i*x; gaussianReal 0 1] = a i^2 := by
      simpa only [id_eq, variance_id_gaussianReal, NNReal.coe_one, mul_one] using
        (variance_const_mul (a i) id (gaussianReal 0 1))
    have hvsum := variance_sum_pi (μ := fun _ : ι => gaussianReal 0 1)
      (X := fun i x => a i * x) (fun i => (memLp_id_gaussianReal 2).const_mul (a i))
    rw [show (∑ i : ι, fun ω : ι → ℝ => a i * ω i) =
      (fun ω => ∑ i, a i * ω i) from by ext; simp] at hvsum
    simpa only [hv] using hvsum

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ReplicaEnergyCovarianceBound
attribute [-instance] _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.spinLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replica Energy Covariance Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma pathIncrement_nonneg {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (i : ℕ) :
    0 ≤ pathIncrement q i := by
  cases i with
  | zero => exact h0
  | succ i => exact sub_nonneg.mpr (hq (Nat.le_succ i))

lemma pathAmplitude_sq {q : ℕ → ℝ} (hq : Monotone q) (h0 : 0 ≤ q 0) (i : ℕ) :
    pathAmplitude q i ^ 2 = pathIncrement q i := Real.sq_sqrt (pathIncrement_nonneg hq h0 i)

lemma tensorFeature_cross {J : Type*} [Fintype J] (p : ℕ) (x y : J → ℝ) :
    (∑ i : Fin p → J, tensorFeature p x i * tensorFeature p y i) =
      (∑ j, x j*y j)^p := by
  classical
  simp only [tensorFeature,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin p) (j : J) => x j * y j)]
  simp

lemma spinValue_sq (x : Fin 2) : spinValue x ^ 2 = 1 := by
  simp only [spinValue]; split_ifs <;> norm_num

lemma spinCoordinate_cross {N : ℕ} (x y : Spin N) :
    (∑ i, spinCoordinate x i * spinCoordinate y i) = spinOverlap x y := by
  simp only [spinCoordinate,div_mul_div_comm,← pow_two,
    Real.sq_sqrt (Nat.cast_nonneg N),← Finset.sum_div,spinOverlap]

lemma spinOverlap_self {N : ℕ} (hN : 0 < N) (x : Spin N) : spinOverlap x x = 1 := by
  simp only [spinOverlap,← pow_two,spinValue_sq,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one]
  exact div_self (Nat.cast_ne_zero.mpr hN.ne')

lemma monomialPath_monotone (n d : ℕ) : Monotone (monomialPath n d) := by
  intro i j hij
  apply pow_le_pow_left₀
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) (Nat.cast_nonneg _)

lemma monomialPath_nonneg (n d i : ℕ) : 0 ≤ monomialPath n d i :=
  pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _

lemma monomialPath_diag_le_one (n d : ℕ) : monomialPath n d n ≤ 1 := by
  apply pow_le_one₀
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · apply (div_le_one (by positivity : (0:ℝ) < (n+1:ℕ))).mpr
    exact Nat.cast_le.mpr (Nat.le_succ n)

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_MonomialGgAtMinimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Monomial Gg At Minimum. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma logMean_const_add_integrable {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {b : ℝ} {F : A → ℝ}
    (hF : Integrable (fun a => Real.exp (b*F a)) μ) (c : ℝ) :
    Integrable (fun a => Real.exp (b*(c+F a))) μ := by
  simpa only [mul_add,Real.exp_add] using hF.const_mul (Real.exp (b*c))

lemma logMean_abs_sub_le {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] {b : ℝ} (hb : 0 < b)
    {F G : A → ℝ} (hF : Integrable (fun a => Real.exp (b*F a)) μ)
    (hG : Integrable (fun a => Real.exp (b*G a)) μ) {C : ℝ}
    (h : ∀ a, |F a-G a| ≤ C) : |logMean b μ F-logMean b μ G| ≤ C := by
  apply abs_le.mpr
  have hu : logMean b μ F ≤ C+logMean b μ G := by
    rw [← logMean_const_add μ hb.ne' hG C]
    exact logMean_mono μ hb hF (logMean_const_add_integrable hG C)
      (fun a => by linarith [(abs_le.mp (h a)).2])
  have hl : logMean b μ G ≤ C+logMean b μ F := by
    rw [← logMean_const_add μ hb.ne' hF C]
    exact logMean_mono μ hb hG (logMean_const_add_integrable hF C)
      (fun a => by linarith [(abs_le.mp (h a)).1])
  constructor <;> linarith

theorem cascadeRecursion_lipschitz {S : Type*} [SeminormedAddCommGroup S]
    [MeasurableSpace S] [MeasurableAdd₂ S]
    (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure S)
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure S))
    {F : S → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    {L : ℝ} (hLip : ∀ x y, |F x-F y| ≤ L*‖x-y‖)
    (hb : ∀ i < n, 0 < b i) :
    ∀ x y, |cascadeRecursion n b μ (fun _ p => p.1+p.2) F x-
      cascadeRecursion n b μ (fun _ p => p.1+p.2) F y| ≤ L*‖x-y‖ := by
  induction n generalizing b μ with
  | zero => exact hLip
  | succ n ih =>
    let G := cascadeRecursion n (fun i => b (i+1)) (fun i => μ (i+1)) (fun _ p => p.1+p.2) F
    have hGm : Measurable G := measurable_cascadeRecursion n _ _
      (fun _ => measurable_fst.add measurable_snd) hF
    have hGG : HasLinearGrowth G := cascadeRecursion_linearGrowth n _ _
      (fun i hi => hμ (i+1) (by omega)) hF hG (fun i hi => hb (i+1) (by omega))
    have hGi (x : S) : Integrable (fun a => Real.exp (b 0*G (x+a))) (μ 0 : Measure S) :=
      integrable_exp_of_linearGrowth _ (hμ 0 (by omega))
        (hGm.comp (measurable_const.add measurable_id)) (hGG.add_left x) _
    intro x y
    apply logMean_abs_sub_le _ (hb 0 (by omega)) (hGi x) (hGi y)
    intro a
    simpa only [add_sub_add_right_eq_sub] using ih (fun i => b (i+1)) (fun i => μ (i+1))
      (fun i hi => hμ (i+1) (by omega)) (fun i hi => hb (i+1) (by omega)) (x+a) (y+a)

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_EnrichedFieldCap
attribute [-instance] _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.spinLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enriched Field Cap. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

variable {I : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

omit [Fintype I] [MeasurableSingletonClass I] in
lemma finiteLogIntegral_eq_logMean (ν : Measure I) (H : I → ℝ) :
    finiteLogIntegral ν H = logMean 1 ν H := by simp [finiteLogIntegral,logMean]

lemma measurable_finiteLogIntegral (ν : Measure I) : Measurable (finiteLogIntegral ν) := by
  unfold finiteLogIntegral
  have hm : Measurable (fun p : (I → ℝ) × I => Real.exp (p.1 p.2)) :=
    measurable_from_prod_countable_left (fun i => (measurable_pi_apply i).exp)
  exact hm.stronglyMeasurable.integral_prod_right.measurable.log

lemma finiteLogIntegral_lipschitz (ν : Measure I) [IsProbabilityMeasure ν] (H G : I → ℝ) :
    |finiteLogIntegral ν H-finiteLogIntegral ν G| ≤ ‖H-G‖ := by
  rw [finiteLogIntegral_eq_logMean,finiteLogIntegral_eq_logMean]
  apply logMean_abs_sub_le ν (by norm_num)
    (show Integrable (fun x => Real.exp (1*H x)) ν from Integrable.of_finite)
    (show Integrable (fun x => Real.exp (1*G x)) ν from Integrable.of_finite)
  intro x
  simpa only [Pi.sub_apply,Real.norm_eq_abs] using norm_le_pi_norm (H-G) x

lemma finiteLogIntegral_linearGrowth (ν : Measure I) [IsProbabilityMeasure ν] :
    HasLinearGrowth (finiteLogIntegral ν) := by
  refine ⟨0,1,le_rfl,zero_le_one,fun H => ?_⟩
  simpa only [finiteLogIntegral,Pi.zero_apply,Real.exp_zero,integral_const,probReal_univ,
    one_smul,Real.log_one,sub_zero,one_mul,zero_add] using finiteLogIntegral_lipschitz ν H 0

lemma measurable_energyRecursion (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) :
    Measurable (energyRecursion n b μ ν) :=
  measurable_cascadeRecursion n b μ (fun _ => measurable_fst.add measurable_snd)
    (measurable_finiteLogIntegral ν)

lemma energyRecursion_lipschitz (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ)))
    (hb : ∀ i < n, 0 < b i) (H G : I → ℝ) :
    |energyRecursion n b μ ν H-energyRecursion n b μ ν G| ≤ ‖H-G‖ := by
  simpa only [one_mul,energyRecursion] using cascadeRecursion_lipschitz n b μ hμ
    (measurable_finiteLogIntegral ν) (finiteLogIntegral_linearGrowth ν)
    (L := 1) (fun H G => by simpa only [one_mul] using finiteLogIntegral_lipschitz ν H G) hb H G

end IsingPerceptron

namespace IsingPerceptron

lemma perturbationWeight_sum (N : ℕ) :
    (∑ j : Fin N, perturbationWeight j) = 1-(1/2 : ℝ)^N := by
  rw [Fin.sum_univ_eq_sum_range]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    simp only [perturbationWeight,pow_succ]
    ring

lemma perturbationWeight_nonneg (j : ℕ) : 0 ≤ perturbationWeight j := by
  exact pow_nonneg (by norm_num) _
lemma perturbationWeight_le_one (j : ℕ) : perturbationWeight j ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

lemma spinValue_abs (x : Fin 2) : |spinValue x| = 1 := by
  simp only [spinValue]
  split_ifs <;> norm_num

lemma spinCoordinate_abs {N : ℕ} (x : Spin N) (i : Fin N) :
    |spinCoordinate x i| = 1/Real.sqrt N := by
  simp only [spinCoordinate,abs_div,spinValue_abs,abs_of_nonneg (Real.sqrt_nonneg _)]

lemma tensorFeature_spin_abs {N p : ℕ} (x : Spin N) (i : Fin p → Fin N) :
    |tensorFeature p (spinCoordinate x) i| = (1/Real.sqrt N)^p := by
  simp only [tensorFeature,Finset.abs_prod,spinCoordinate_abs,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin]

lemma enrichedLevelCoefficient_abs {N : ℕ} (n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ)
    (i : ℕ) (x y : Spin N) (j : EnrichedBlock N) :
    |enrichedLevelCoefficient n h u i x j| = |enrichedLevelCoefficient n h u i y j| := by
  rcases j with j | ⟨j,t⟩
  · simp only [enrichedLevelCoefficient,abs_mul,spinValue_abs]
  · simp only [enrichedLevelCoefficient,abs_mul,tensorFeature_spin_abs]

lemma sum_scaled_cross {J : Type*} [Fintype J] (c : ℝ) (v w : J → ℝ) :
    (∑ j, (c*v j)*(c*w j)) = c^2*(∑ j, v j*w j) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma enrichedLevelCoefficient_cross {N : ℕ} (hN : 0 < N) (n : ℕ) {h : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (u : Fin N → ℝ) (i : ℕ) (x y : Spin N) :
    (∑ j : EnrichedBlock N, enrichedLevelCoefficient n h u i x j * enrichedLevelCoefficient n h u i y j) =
      N*pathIncrement h i*spinOverlap x y +
      ∑ j : Fin N, (Real.sqrt N*perturbationScale N*perturbationWeight j*u j)^2 *
        pathIncrement (monomialPath n (monomialIndex j).2) i * (spinOverlap x y)^(monomialIndex j).1 := by
  classical
  rw [Fintype.sum_sum_type,Fintype.sum_sigma]
  simp only [enrichedLevelCoefficient]
  rw [sum_scaled_cross,pathAmplitude_sq hh h0]
  have he : (∑ j : Fin N, spinValue (x j)*spinValue (y j)) = N*spinOverlap x y := by
    rw [spinOverlap,mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hN.ne')]
  rw [he]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j _
    rw [sum_scaled_cross,tensorFeature_cross,spinCoordinate_cross,mul_pow,
      pathAmplitude_sq (monomialPath_monotone n _) (monomialPath_nonneg n _ 0)]

lemma enrichedLevelCoefficient_variance {N : ℕ} (hN : 0 < N) (n : ℕ) {h : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (u : Fin N → ℝ) (i : ℕ) (x : Spin N) :
    (∑ j : EnrichedBlock N, (enrichedLevelCoefficient n h u i x j)^2) =
      N*pathIncrement h i +
      ∑ j : Fin N, (Real.sqrt N*perturbationScale N*perturbationWeight j*u j)^2 *
        pathIncrement (monomialPath n (monomialIndex j).2) i := by
  simpa only [← pow_two,spinOverlap_self hN,one_pow,mul_one] using
    enrichedLevelCoefficient_cross hN n hh h0 u i x x

lemma enrichedRoot_envelope_sq {N : ℕ} (hN : 0 < N) (n : ℕ) {h : ℕ → ℝ}
    (hh : Monotone h) (h0 : 0 ≤ h 0) (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2) (x : Spin N) :
    (∑ j : EnrichedBlock N, |enrichedLevelCoefficient n h u 0 x j|^2) ≤ N*h 0+4*N*(perturbationScale N)^2 := by
  simp only [sq_abs,enrichedLevelCoefficient_variance hN n hh h0 u 0 x,pathIncrement]
  apply add_le_add_right
  calc
    _ ≤ ∑ j : Fin N, (4*N*(perturbationScale N)^2)*perturbationWeight j := by
      apply Finset.sum_le_sum
      intro j _
      have hv : monomialPath n (monomialIndex j).2 0 ≤ 1 :=
        (monomialPath_monotone n (monomialIndex j).2 (Nat.zero_le n)).trans
          (monomialPath_diag_le_one n (monomialIndex j).2)
      have hw := perturbationWeight_nonneg j
      have hw1 := perturbationWeight_le_one j
      have hu2 : (u j)^2 ≤ 4 := by
        have hab := abs_le.mp (hu j)
        nlinarith
      have he : (Real.sqrt N*perturbationScale N*perturbationWeight j*u j)^2 =
          N*(perturbationScale N)^2*(perturbationWeight j)^2*(u j)^2 := by
        simp only [mul_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
      rw [he]
      calc
        _ ≤ N*(perturbationScale N)^2*(perturbationWeight j)^2*(u j)^2 :=
          mul_le_of_le_one_right (by positivity) hv
        _ ≤ N*(perturbationScale N)^2*(perturbationWeight j)^2*4 :=
          mul_le_mul_of_nonneg_left hu2 (by positivity)
        _ ≤ (4*N*(perturbationScale N)^2)*perturbationWeight j := by
          have hww : (perturbationWeight j)^2 ≤ perturbationWeight j := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hww (show 0 ≤ 4*N*(perturbationScale N)^2 by positivity)]
    _ = (4*N*(perturbationScale N)^2)*(1-(1/2 : ℝ)^N) := by
      rw [← Finset.mul_sum,perturbationWeight_sum]
    _ ≤ _ := mul_le_of_le_one_right (by positivity)
      (by linarith [pow_nonneg (show (0 : ℝ) ≤ 1/2 by norm_num) N])

lemma variance_le_square_about_const {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Ω → ℝ} (hF : MemLp F 2 μ) (a : ℝ) :
    Var[F; μ] ≤ ∫ x, (F x-a)^2 ∂μ := by
  have hs := variance_eq_sub (hF.sub (memLp_const a))
  simp only [Pi.sub_apply, Pi.pow_apply] at hs
  change Var[fun x => F x-a; μ] = _ at hs
  rw [variance_sub_const hF.aestronglyMeasurable a] at hs
  linarith [sq_nonneg (∫ x, F x-a ∂μ)]

lemma gaussian_coord_memLp {n : ℕ} {F : (Fin n → ℝ) → ℝ} {c : Fin n → ℝ}
    (hm : Measurable F)
    (hl : ∀ x y, |F x-F y| ≤ ∑ i, c i*|x i-y i|) (p : ℝ≥0) :
    MemLp F p (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  have hcoord (i : Fin n) : MemLp (fun x : Fin n → ℝ => c i*|x i|) p
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
    have h := (memLp_id_gaussianReal p).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i)
    simpa only [Function.comp_def, id_eq, Pi.abs_apply] using h.abs.const_mul (c i)
  have hb := (memLp_const |F 0|).add (memLp_finsetSum Finset.univ (fun i _ => hcoord i))
  apply hb.mono' hm.aestronglyMeasurable
  refine Eventually.of_forall fun x => ?_
  have hx := hl x 0
  simp only [Pi.zero_apply, sub_zero] at hx
  simp only [Pi.add_apply, Real.norm_eq_abs]
  linarith [abs_sub_abs_le_abs_sub (F x) (F 0)]

lemma gaussian_variance_of_slope {F : ℝ → ℝ} (hm : Measurable F) {c : ℝ}
    (hl : ∀ x y, |F x-F y| ≤ c*|x-y|) : Var[F; gaussianReal 0 1] ≤ c^2 := by
  have hLp : MemLp F 2 (gaussianReal 0 1) := by
    apply ((memLp_const |F 0|).add ((memLp_id_gaussianReal 2).abs.const_mul c)).mono'
      hm.aestronglyMeasurable
    refine Eventually.of_forall fun x => ?_
    have hx := hl x 0
    simp only [sub_zero] at hx
    simp only [Real.norm_eq_abs, Pi.add_apply, Pi.abs_apply, id_eq]
    linarith [abs_sub_abs_le_abs_sub (F x) (F 0)]
  have hsq : (∫ x : ℝ, x^2 ∂gaussianReal 0 1) = 1 := by
    have h := variance_eq_sub (memLp_id_gaussianReal (μ := 0) (v := 1) 2)
    simpa only [variance_id_gaussianReal, NNReal.coe_one, integral_id_gaussianReal,
      sq, mul_zero, sub_zero, Pi.pow_apply, id_eq] using h.symm
  calc
    _ ≤ ∫ x, (F x-F 0)^2 ∂gaussianReal 0 1 := variance_le_square_about_const hLp _
    _ ≤ ∫ x : ℝ, c^2*x^2 ∂gaussianReal 0 1 := by
      apply integral_mono (hLp.sub (memLp_const _)).integrable_sq
        ((memLp_id_gaussianReal 2).integrable_sq.const_mul _)
      intro x
      have hx := hl x 0
      simp only [sub_zero] at hx
      have hh := pow_le_pow_left₀ (abs_nonneg (F x-F 0)) hx 2
      simpa only [sq_abs, mul_pow, Pi.sub_apply, id_eq] using hh
    _ = c^2 := by rw [integral_const_mul, hsq, mul_one]

lemma gaussian_slope_memLp {F : ℝ → ℝ} (hm : Measurable F) {c : ℝ}
    (hl : ∀ x y, |F x-F y| ≤ c*|x-y|) (p : ℝ≥0) :
    MemLp F p (gaussianReal 0 1) := by
  apply ((memLp_const |F 0|).add ((memLp_id_gaussianReal p).abs.const_mul c)).mono'
    hm.aestronglyMeasurable
  refine Eventually.of_forall fun x => ?_
  have hx := hl x 0
  simp only [sub_zero] at hx
  simp only [Real.norm_eq_abs, Pi.add_apply, Pi.abs_apply, id_eq]
  linarith [abs_sub_abs_le_abs_sub (F x) (F 0)]

lemma variance_prod_le_fiber {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : A × B → ℝ} (hLp : MemLp F 2 (μ.prod ν))
    (hsecLp : ∀ b, MemLp (fun a => F (a,b)) 2 μ)
    (hGLp : MemLp (fun b => ∫ a, F (a,b) ∂μ) 2 ν) {C : ℝ}
    (hvar : ∀ b, Var[fun a => F (a,b); μ] ≤ C) :
    Var[F; μ.prod ν] ≤ C + Var[fun b => ∫ a, F (a,b) ∂μ; ν] := by
  have hsec : ∀ b, (∫ a, F (a,b)^2 ∂μ) ≤ C + (∫ a, F (a,b) ∂μ)^2 := by
    intro b
    have h := hvar b
    rw [variance_eq_sub (hsecLp b)] at h
    simp only [Pi.pow_apply] at h
    linarith
  have hs := integral_mono hLp.integrable_sq.integral_prod_right
    ((integrable_const C).add hGLp.integrable_sq) hsec
  simp only [Pi.add_apply] at hs
  rw [integral_add (integrable_const _) hGLp.integrable_sq, integral_const,
    probReal_univ, one_smul] at hs
  rw [variance_eq_sub hLp, variance_eq_sub hGLp]
  simp only [Pi.pow_apply]
  rw [integral_prod_symm _ hLp.integrable_sq,
    integral_prod_symm _ (hLp.integrable (by norm_num))]
  linarith

theorem gaussian_variance_coordinate_bound (n : ℕ) {F : (Fin n → ℝ) → ℝ}
    (hm : Measurable F) {c : Fin n → ℝ}
    (hl : ∀ x y, |F x-F y| ≤ ∑ i, c i*|x i-y i|) :
    Var[F; Measure.pi (fun _ : Fin n => gaussianReal 0 1)] ≤ ∑ i, (c i)^2 := by
  induction n with
  | zero =>
    have hF : F = fun _ => F (fun i : Fin 0 => i.elim0) := by
      funext x
      congr 1
      funext i
      exact i.elim0
    rw [hF, variance_eq_integral measurable_const.aemeasurable]
    simp
  | succ n ih =>
    let μ := gaussianReal (0 : ℝ) (1 : ℝ≥0)
    let ν := Measure.pi (fun _ : Fin n => μ)
    have hcons : Measurable (fun z : ℝ × (Fin n → ℝ) => (Fin.cons z.1 z.2 : Fin (n+1) → ℝ)) := by
      apply Measurable.of_eval
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero] using
          (measurable_fst : Measurable (Prod.fst : ℝ × (Fin n → ℝ) → ℝ))
      · simpa only [Fin.cons_succ, Function.comp_def] using (measurable_pi_apply j).comp
          (measurable_snd : Measurable (Prod.snd : ℝ × (Fin n → ℝ) → (Fin n → ℝ)))
    have hFm : Measurable (fun z : ℝ × (Fin n → ℝ) => F (Fin.cons z.1 z.2)) := hm.comp hcons
    have hsm (x : Fin n → ℝ) : Measurable (fun a => F (Fin.cons a x)) :=
      hFm.comp (measurable_id.prodMk measurable_const)
    have hsl (x : Fin n → ℝ) : ∀ a b,
        |F (Fin.cons a x)-F (Fin.cons b x)| ≤ c 0*|a-b| := by
      intro a b
      simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
        sub_self, abs_zero, mul_zero, Finset.sum_const_zero, add_zero] using
        hl (Fin.cons a x) (Fin.cons b x)
    have hsi (x : Fin n → ℝ) : Integrable (fun a => F (Fin.cons a x)) μ :=
      (gaussian_slope_memLp (hsm x) (hsl x) 1).integrable (by norm_num)
    have hGm : Measurable (fun x => ∫ a, F (Fin.cons a x) ∂μ) :=
      hFm.stronglyMeasurable.integral_prod_left'.measurable
    have hGl : ∀ x y, |(∫ a, F (Fin.cons a x) ∂μ)-(∫ a, F (Fin.cons a y) ∂μ)| ≤
        ∑ i : Fin n, c i.succ*|x i-y i| := by
      intro x y
      rw [← integral_sub (hsi x) (hsi y)]
      have hB (a : ℝ) : |F (Fin.cons a x)-F (Fin.cons a y)| ≤
          ∑ i : Fin n, c i.succ*|x i-y i| := by
        simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
          sub_self, abs_zero, mul_zero, zero_add] using hl (Fin.cons a x) (Fin.cons a y)
      simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
        (norm_integral_le_of_norm_le_const (μ := μ)
          (f := fun a => F (Fin.cons a x)-F (Fin.cons a y))
          (Eventually.of_forall (fun a => by simpa only [Real.norm_eq_abs] using hB a)))
    have hGLp := gaussian_coord_memLp hGm hGl 2
    have hpres := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm
    have hLp : MemLp (fun z : ℝ × (Fin n → ℝ) => F (Fin.cons z.1 z.2)) 2 (μ.prod ν) := by
      have h := (gaussian_coord_memLp hm hl 2).comp_measurePreserving hpres
      simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove,
        cast_eq, ENNReal.coe_ofNat, ν] using h
    have hprod := variance_prod_le_fiber hLp
      (fun x => gaussian_slope_memLp (hsm x) (hsl x) 2) hGLp
      (fun x => gaussian_variance_of_slope (hsm x) (hsl x))
    have heq : Var[fun z : ℝ × (Fin n → ℝ) => F (Fin.cons z.1 z.2); μ.prod ν] =
        Var[F; Measure.pi (fun _ : Fin (n+1) => μ)] := by
      have h := hpres.variance_fun_comp hm.aemeasurable
      simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove, cast_eq] using h
    rw [heq] at hprod
    have ht := ih hGm hGl
    rw [Fin.sum_univ_succ]
    change _ ≤ c 0 ^ 2 + Var[(fun b => ∫ a, F (Fin.cons a b) ∂μ); ν] at hprod
    dsimp only [ν, μ] at hprod ht ⊢
    linarith

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_MemLpOfAbsBound
attribute [-instance] _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.spinLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mem Lp Of Abs Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron
lemma memLp_of_abs_bound {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [IsFiniteMeasure μ] {F : A → ℝ} (hm : Measurable F) {K : ℝ}
    (hb : ∀ a, |F a| ≤ K) (p : ℝ≥0∞) : MemLp F p μ :=
  MemLp.of_bound hm.aestronglyMeasurable K
    (Eventually.of_forall (fun a => by simpa only [Real.norm_eq_abs] using hb a))

lemma integral_abs_le_bound {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [IsProbabilityMeasure μ] {F : A → ℝ} {K : ℝ}
    (hb : ∀ a, |F a| ≤ K) : |∫ a, F a ∂μ| ≤ K := by
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := μ) (f := F) (C := K)
      (Eventually.of_forall (fun a => by simpa only [Real.norm_eq_abs] using hb a)))

lemma variance_le_of_oscillation {A : Type*} [MeasurableSpace A] {μ : Measure A}
    [IsProbabilityMeasure μ] {F : A → ℝ} (hm : Measurable F) {K c : ℝ}
    (hb : ∀ a, |F a| ≤ K) (hc : 0 ≤ c) (ho : ∀ a b, |F a - F b| ≤ c) :
    variance F μ ≤ c ^ 2 := by
  have hLp := memLp_of_abs_bound hm hb 2 (μ := μ)
  have hi := hLp.integrable (by norm_num)
  have hcenter : ∀ a, |F a - ∫ b, F b ∂μ| ≤ c := by
    intro a
    have h := integral_abs_le_bound (μ := μ) (F := fun b => F a - F b) (ho a)
    simpa only [integral_sub (integrable_const _) hi, integral_const,
      probReal_univ, one_smul] using h
  rw [variance_eq_integral hm.aemeasurable]
  have hisq := (hLp.sub (memLp_const (∫ a, F a ∂μ))).integrable_sq
  have h := integral_mono hisq (integrable_const (c ^ 2)) (fun a =>
    sq_le_sq.mpr (by simpa only [abs_of_nonneg hc, Pi.sub_apply] using hcenter a))
  simpa using h

lemma variance_prod_le {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : A × B → ℝ} (hm : Measurable F) {K c : ℝ} (hb : ∀ z, |F z| ≤ K)
    (hc : 0 ≤ c) (ho : ∀ b a a', |F (a, b) - F (a', b)| ≤ c) :
    variance F (μ.prod ν) ≤ c ^ 2 + variance (fun b => ∫ a, F (a, b) ∂μ) ν := by
  have hLp := memLp_of_abs_bound hm hb 2 (μ := μ.prod ν)
  have hGm : Measurable (fun b => ∫ a, F (a, b) ∂μ) :=
    hm.stronglyMeasurable.integral_prod_left'.measurable
  have hGb : ∀ b, |∫ a, F (a, b) ∂μ| ≤ K := fun b =>
    integral_abs_le_bound (fun a => hb (a, b))
  have hGLp := memLp_of_abs_bound hGm hGb 2 (μ := ν)
  have hsec : ∀ b, (∫ a, F (a, b) ^ 2 ∂μ) ≤ c ^ 2 + (∫ a, F (a, b) ∂μ) ^ 2 := by
    intro b
    have hm' : Measurable (fun a => F (a, b)) := hm.comp (measurable_id.prodMk measurable_const)
    have h := variance_le_of_oscillation (μ := μ) hm' (fun a => hb (a, b)) hc (ho b)
    rw [variance_eq_sub (memLp_of_abs_bound hm' (fun a => hb (a, b)) 2)] at h
    simp only [Pi.pow_apply] at h
    linarith
  have hs := integral_mono hLp.integrable_sq.integral_prod_right
    ((integrable_const (c ^ 2)).add hGLp.integrable_sq) hsec
  simp only [Pi.add_apply] at hs
  rw [integral_add (integrable_const _) hGLp.integrable_sq, integral_const,
    probReal_univ, one_smul] at hs
  rw [variance_eq_sub hLp, variance_eq_sub hGLp]
  simp only [Pi.pow_apply]
  rw [integral_prod_symm _ hLp.integrable_sq,
    integral_prod_symm _ (hLp.integrable (by norm_num))]
  linarith

lemma variance_pi_boundedDifferences {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (n : ℕ)
    {F : (Fin n → A) → ℝ} (hm : Measurable F) {K c : ℝ}
    (hb : ∀ x, |F x| ≤ K) (hc : 0 ≤ c)
    (ho : ∀ (i : Fin n) x y, (∀ j, j ≠ i → x j = y j) → |F x - F y| ≤ c) :
    variance F (Measure.pi (fun _ : Fin n => μ)) ≤ n * c ^ 2 := by
  induction n with
  | zero =>
    have hF : F = fun _ => F (fun i : Fin 0 => i.elim0) := by
      funext x
      congr 1
      funext i
      exact i.elim0
    rw [hF, variance_eq_integral measurable_const.aemeasurable]
    simp
  | succ n ih =>
    let ν := Measure.pi (fun _ : Fin n => μ)
    have hcons : Measurable (fun z : A × (Fin n → A) => (Fin.cons z.1 z.2 : Fin (n + 1) → A)) := by
      apply Measurable.of_eval
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero] using (measurable_fst : Measurable (Prod.fst : A × (Fin n → A) → A))
      · simpa only [Fin.cons_succ, Function.comp_def] using (measurable_pi_apply j).comp
          (measurable_snd : Measurable (Prod.snd : A × (Fin n → A) → (Fin n → A)))
    have hFm : Measurable (fun z : A × (Fin n → A) => F (Fin.cons z.1 z.2)) := hm.comp hcons
    have hGb : ∀ x, |∫ a, F (Fin.cons a x) ∂μ| ≤ K := fun x =>
      integral_abs_le_bound (fun a => hb (Fin.cons a x))
    have hGm : Measurable (fun x => ∫ a, F (Fin.cons a x) ∂μ) :=
      hFm.stronglyMeasurable.integral_prod_left'.measurable
    have hGosc : ∀ (i : Fin n) x y, (∀ j, j ≠ i → x j = y j) →
        |(∫ a, F (Fin.cons a x) ∂μ) - ∫ a, F (Fin.cons a y) ∂μ| ≤ c := by
      intro i x y hxy
      have hmsec : ∀ x : Fin n → A, Measurable (fun a => F (Fin.cons a x)) :=
        fun x => hFm.comp (measurable_id.prodMk measurable_const)
      have hisec : ∀ x : Fin n → A, Integrable (fun a => F (Fin.cons a x)) μ :=
        fun x => (memLp_of_abs_bound (hmsec x) (fun a => hb (Fin.cons a x)) 1).integrable le_rfl
      have h := integral_abs_le_bound (μ := μ) (F := fun a => F (Fin.cons a x) - F (Fin.cons a y))
        (fun a => ho i.succ (Fin.cons a x) (Fin.cons a y) (fun j => by
          refine Fin.cases ?_ (fun l => ?_) j
          · intro _; simp
          · intro hl
            simp only [Fin.cons_succ]
            exact hxy l (fun h => hl (congrArg Fin.succ h))))
      simpa only [integral_sub (hisec x) (hisec y)] using h
    have hsec : ∀ (x : Fin n → A) a a', |F (Fin.cons a x) - F (Fin.cons a' x)| ≤ c := by
      intro x a a'
      apply ho 0
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · intro h; exact (h rfl).elim
      · intro _; simp
    have hprod := variance_prod_le (μ := μ) (ν := ν) hFm
      (fun z => hb (Fin.cons z.1 z.2)) hc hsec
    have htail := ih hGm hGb hGosc
    have heq : variance (fun z : A × (Fin n → A) => F (Fin.cons z.1 z.2)) (μ.prod ν) =
        variance F (Measure.pi (fun _ : Fin (n + 1) => μ)) := by
      have h := ((measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm).variance_fun_comp hm.aemeasurable
      simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove, cast_eq] using h
    rw [heq] at hprod
    simp only [Nat.cast_add, Nat.cast_one]
    dsimp only [ν] at hprod
    nlinarith

variable {I : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

omit [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma finite_linear_vector_bound {m : ℕ} {a : I → Fin m → ℝ} {c : Fin m → ℝ}
    (hc : ∀ j, 0 ≤ c j) (ha : ∀ x j, |a x j| ≤ c j) (g g' : Fin m → ℝ) :
    ‖(fun x => ∑ j, a x j * g j) - (fun x => ∑ j, a x j * g' j)‖ ≤
      ∑ j, c j * |g j-g' j| := by
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun j _ => mul_nonneg (hc j) (abs_nonneg _)))).mpr
  intro x
  simp only [Pi.sub_apply,Real.norm_eq_abs,← Finset.sum_sub_distrib,← mul_sub]
  exact (Finset.abs_sum_le_sum_abs _ _).trans <| Finset.sum_le_sum (fun j _ => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (ha x j) (abs_nonneg _))

lemma measurable_rootEnergy (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) {m : ℕ} (H : I → ℝ) (a : I → Fin m → ℝ) :
    Measurable (rootEnergy n b μ ν H a) := by
  apply (measurable_energyRecursion n b μ ν).comp
  fun_prop

lemma rootEnergy_gaussian_slope (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m : ℕ} (H : I → ℝ) (a : I → Fin m → ℝ) (c : Fin m → ℝ)
    (hc : ∀ j, 0 ≤ c j) (ha : ∀ x j, |a x j| ≤ c j) (g g' : Fin m → ℝ) :
    |rootEnergy n b μ ν H a g-rootEnergy n b μ ν H a g'| ≤ ∑ j, c j*|g j-g' j| := by
  refine (energyRecursion_lipschitz n b μ ν hμ hb _ _).trans ?_
  have heq : (fun x => H x+∑ j, a x j*g j) - (fun x => H x+∑ j, a x j*g' j) =
      (fun x => ∑ j, a x j*g j) - (fun x => ∑ j, a x j*g' j) := by
    ext x
    simp only [Pi.sub_apply,add_sub_add_left_eq_sub]
  rw [heq]
  exact finite_linear_vector_bound hc ha g g'

theorem rootEnergy_gaussian_variance (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m : ℕ} (H : I → ℝ) (a : I → Fin m → ℝ) (c : Fin m → ℝ)
    (hc : ∀ j, 0 ≤ c j) (ha : ∀ x j, |a x j| ≤ c j) :
    Var[rootEnergy n b μ ν H a; Measure.pi (fun _ : Fin m => gaussianReal 0 1)] ≤ ∑ j, (c j)^2 :=
  gaussian_variance_coordinate_bound m (measurable_rootEnergy n b μ ν H a)
    (rootEnergy_gaussian_slope n b μ ν hμ hb H a c hc ha)

lemma rootEnergy_base_lipschitz (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m : ℕ} (H G : I → ℝ) (a : I → Fin m → ℝ) (g : Fin m → ℝ) :
    |rootEnergy n b μ ν H a g-rootEnergy n b μ ν G a g| ≤ ‖H-G‖ := by
  have he := energyRecursion_lipschitz n b μ ν hμ hb
    (fun x => H x+∑ j, a x j*g j) (fun x => G x+∑ j, a x j*g j)
  have heq : (fun x => H x+∑ j, a x j*g j) - (fun x => G x+∑ j, a x j*g j) = H-G := by
    ext x
    simp only [Pi.sub_apply,add_sub_add_right_eq_sub]
  rw [heq] at he
  exact he

variable {A : Type*} [MeasurableSpace A]

omit [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace A] in
lemma patternBase_bound {M : ℕ} {φ : A → I → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (y : Fin M → A) : ‖patternBase φ y‖ ≤ M*K := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg M) hK)).mpr
  intro x
  simp only [patternBase,Real.norm_eq_abs]
  calc
    _ ≤ ∑ r : Fin M, |φ (y r) x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : Fin M, K := Finset.sum_le_sum (fun r _ => hφ (y r) x)
    _ = _ := by simp

omit [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace A] in
lemma patternBase_one_change {M : ℕ} {φ : A → I → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (i : Fin M) (y y' : Fin M → A)
    (he : ∀ j, j ≠ i → y j=y' j) : ‖patternBase φ y-patternBase φ y'‖ ≤ 2*K := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) hK)).mpr
  intro x
  have hsum : (∑ r : Fin M, (φ (y r) x-φ (y' r) x)) = φ (y i) x-φ (y' i) x := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [he j hji,sub_self]
    · simp
  simp only [Pi.sub_apply,patternBase,Real.norm_eq_abs,← Finset.sum_sub_distrib,hsum]
  linarith [abs_sub (φ (y i) x) (φ (y' i) x),hφ (y i) x,hφ (y' i) x]

theorem pattern_root_energy_variance (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m M : ℕ} (a : I → Fin m → ℝ) (c : Fin m → ℝ)
    (hc : ∀ j, 0 ≤ c j) (ha : ∀ x j, |a x j| ≤ c j)
    (P : Measure A) [IsProbabilityMeasure P] {φ : A → I → ℝ}
    (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K) (hφ : ∀ y x, |φ y x| ≤ K) :
    Var[(fun p : (Fin m → ℝ) × (Fin M → A) => rootEnergy n b μ ν (patternBase φ p.2) a p.1);
      (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod (Measure.pi (fun _ : Fin M => P))]
      ≤ (∑ j, (c j)^2)+M*(2*K)^2 := by
  let γ := Measure.pi (fun _ : Fin m => gaussianReal 0 1)
  let ρ := Measure.pi (fun _ : Fin M => P)
  let F : (Fin m → ℝ) × (Fin M → A) → ℝ :=
    fun p => rootEnergy n b μ ν (patternBase φ p.2) a p.1
  let F₀ : (Fin m → ℝ) → ℝ := rootEnergy n b μ ν 0 a
  have hFm : Measurable F := by
    apply (measurable_energyRecursion n b μ ν).comp
    apply Measurable.of_eval
    intro x
    apply Measurable.add
    · exact (Finset.measurable_sum _ (fun r _ => ((measurable_pi_apply x).comp hm).comp
        ((measurable_pi_apply r).comp measurable_snd)))
    · fun_prop
  have hfl (y : Fin M → A) : MemLp (fun g => F (g,y)) 2 γ :=
    gaussian_coord_memLp (measurable_rootEnergy n b μ ν (patternBase φ y) a)
      (rootEnergy_gaussian_slope n b μ ν hμ hb (patternBase φ y) a c hc ha) 2
  have h0l : MemLp F₀ 2 γ :=
    gaussian_coord_memLp (measurable_rootEnergy n b μ ν 0 a)
      (rootEnergy_gaussian_slope n b μ ν hμ hb 0 a c hc ha) 2
  have hdiff (g : Fin m → ℝ) (y : Fin M → A) : |F (g,y)-F₀ g| ≤ M*K := by
    exact (rootEnergy_base_lipschitz n b μ ν hμ hb (patternBase φ y) 0 a g).trans
      (by simpa only [sub_zero] using patternBase_bound hK hφ y)
  have hLp : MemLp F 2 (γ.prod ρ) := by
    have hz : MemLp (fun p : (Fin m → ℝ) × (Fin M → A) => F₀ p.1) 2 (γ.prod ρ) :=
      h0l.comp_measurePreserving (measurePreserving_fst (μ := γ) (ν := ρ))
    apply (hz.abs.add (memLp_const (M*K))).mono' hFm.aestronglyMeasurable
    apply ae_of_all
    intro p
    simp only [Pi.add_apply,Pi.abs_apply,Real.norm_eq_abs]
    linarith [hdiff p.1 p.2,abs_sub_abs_le_abs_sub (F p) (F₀ p.1)]
  let G : (Fin M → A) → ℝ := fun y => ∫ g, F (g,y) ∂γ
  have hGm : Measurable G := hFm.stronglyMeasurable.integral_prod_left'.measurable
  have hGb (y : Fin M → A) : |G y| ≤ |∫ g, F₀ g ∂γ|+M*K := by
    have hh := integral_abs_le_bound (μ := γ) (fun g => hdiff g y)
    rw [integral_sub ((hfl y).integrable (by norm_num)) (h0l.integrable (by norm_num))] at hh
    dsimp only [G]
    linarith [abs_sub_abs_le_abs_sub (∫ g, F (g,y) ∂γ) (∫ g, F₀ g ∂γ)]
  have hGLp : MemLp G 2 ρ := memLp_of_abs_bound hGm hGb 2
  have hosc (i : Fin M) (y y' : Fin M → A) (he : ∀ j, j ≠ i → y j=y' j) :
      |G y-G y'| ≤ 2*K := by
    have hd (g : Fin m → ℝ) : |F (g,y)-F (g,y')| ≤ 2*K :=
      (rootEnergy_base_lipschitz n b μ ν hμ hb (patternBase φ y) (patternBase φ y') a g).trans
        (patternBase_one_change hK hφ i y y' he)
    have hh := integral_abs_le_bound (μ := γ) hd
    simpa only [integral_sub ((hfl y).integrable (by norm_num))
      ((hfl y').integrable (by norm_num)),G] using hh
  have hv := variance_prod_le_fiber hLp hfl hGLp
    (fun y => rootEnergy_gaussian_variance n b μ ν hμ hb (patternBase φ y) a c hc ha)
  have hbvar := variance_pi_boundedDifferences P M hGm hGb (by positivity : 0 ≤ 2*K) hosc
  change Var[F; γ.prod ρ] ≤ _
  change Var[G; ρ] ≤ _ at hbvar
  linarith

end IsingPerceptron

namespace IsingPerceptron

lemma enrichedIncrementLaw_moments (N n : ℕ) (h : ℕ → ℝ) (u : Fin N → ℝ) (i : ℕ) :
    ExponentialNormMoments (enrichedIncrementLaw N n h u i : Measure (Spin N → ℝ)) := by
  apply finite_gaussian_exponentialNormMoments (measurable_enrichedIncrement N n h u i)
    (fun _ => 0) (fun x => (∑ j, (enrichedCoefficientsFin N n h u i x j)^2).toNNReal)
  intro x
  exact (gaussian_weighted_sum_law (enrichedCoefficientsFin N n h u i x)).map_eq

variable {I A : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace A]

lemma pattern_root_energy_memLp (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m M : ℕ} (a : I → Fin m → ℝ) (c : Fin m → ℝ)
    (hc : ∀ j, 0 ≤ c j) (ha : ∀ x j, |a x j| ≤ c j)
    (P : Measure A) [IsProbabilityMeasure P] {φ : A → I → ℝ}
    (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K) (hφ : ∀ y x, |φ y x| ≤ K) :
    MemLp (fun p : (Fin m → ℝ) × (Fin M → A) => rootEnergy n b μ ν (patternBase φ p.2) a p.1) 2
      ((Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod (Measure.pi (fun _ : Fin M => P))) := by
  let γ := Measure.pi (fun _ : Fin m => gaussianReal 0 1)
  let ρ := Measure.pi (fun _ : Fin M => P)
  let F : (Fin m → ℝ) × (Fin M → A) → ℝ :=
    fun p => rootEnergy n b μ ν (patternBase φ p.2) a p.1
  let F₀ : (Fin m → ℝ) → ℝ := rootEnergy n b μ ν 0 a
  have hFm : Measurable F := by
    apply (measurable_energyRecursion n b μ ν).comp
    apply Measurable.of_eval
    intro x
    apply Measurable.add
    · exact (Finset.measurable_sum _ (fun r _ => ((measurable_pi_apply x).comp hm).comp
        ((measurable_pi_apply r).comp measurable_snd)))
    · fun_prop
  have h0l : MemLp F₀ 2 γ :=
    gaussian_coord_memLp (measurable_rootEnergy n b μ ν 0 a)
      (rootEnergy_gaussian_slope n b μ ν hμ hb 0 a c hc ha) 2
  have hdiff (g : Fin m → ℝ) (y : Fin M → A) : |F (g,y)-F₀ g| ≤ M*K := by
    exact (rootEnergy_base_lipschitz n b μ ν hμ hb (patternBase φ y) 0 a g).trans
      (by simpa only [sub_zero] using patternBase_bound hK hφ y)
  have hLp : MemLp F 2 (γ.prod ρ) := by
    have hz : MemLp (fun p : (Fin m → ℝ) × (Fin M → A) => F₀ p.1) 2 (γ.prod ρ) :=
      h0l.comp_measurePreserving (measurePreserving_fst (μ := γ) (ν := ρ))
    apply (hz.abs.add (memLp_const (M*K))).mono' hFm.aestronglyMeasurable
    apply ae_of_all
    intro p
    simp only [Pi.add_apply,Pi.abs_apply,Real.norm_eq_abs]
    linarith [hdiff p.1 p.2,abs_sub_abs_le_abs_sub (F p) (F₀ p.1)]
  exact hLp

end IsingPerceptron

namespace IsingPerceptron

lemma poissonMass_succ (r : ℝ≥0) (n : ℕ) :
    poissonMass r (n+1) * (n+1) = r * poissonMass r n := by
  unfold poissonMass
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp

lemma poisson_first_hasSum (r : ℝ≥0) :
    HasSum (fun n : ℕ => poissonMass r n * n) (r : ℝ) := by
  have hs := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  have he : (fun n : ℕ => poissonMass r (n+1) * (n+1)) =
      fun n => (r : ℝ) * poissonMass r n := funext (poissonMass_succ r)
  have hs' : HasSum (fun n : ℕ => poissonMass r (n+1) * ((n+1 : ℕ) : ℝ)) (r : ℝ) := by
    simp only [Nat.cast_add,Nat.cast_one]
    rw [he]
    simpa only [mul_one,poissonMass] using hs
  have h := (hasSum_nat_add_iff (f := fun n : ℕ => poissonMass r n * n) 1).mp hs'
  simpa [poissonMass] using h

lemma poisson_second_hasSum (r : ℝ≥0) :
    HasSum (fun n : ℕ => poissonMass r n * (n : ℝ)^2) ((r : ℝ)^2+r) := by
  have hs := ((poisson_first_hasSum r).add (hasSum_one_poissonMeasure r)).mul_left (r : ℝ)
  have he (n : ℕ) : poissonMass r (n+1) * ((n+1 : ℕ) : ℝ)^2 =
      (r : ℝ) * (poissonMass r n * n + poissonMass r n) := by
    push_cast
    calc
      _ = (poissonMass r (n+1) * (n+1)) * (n+1) := by ring
      _ = _ := by rw [poissonMass_succ]; ring
  have hs' : HasSum (fun n : ℕ => poissonMass r (n+1) * ((n+1 : ℕ) : ℝ)^2)
      ((r : ℝ) * (r+1)) := by
    simp_rw [he]
    exact hs
  have h := (hasSum_nat_add_iff (f := fun n : ℕ => poissonMass r n * (n : ℝ)^2) 1).mp hs'
  simpa [poissonMass, pow_two, mul_add] using h

lemma poisson_cast_memLp (r : ℝ≥0) : MemLp (fun n : ℕ => (n : ℝ)) 2 (poissonMeasure r) := by
  apply (memLp_two_iff_integrable_sq (Measurable.of_discrete.aestronglyMeasurable)).mpr
  apply integrable_poissonMeasure_iff.mpr
  simpa only [Real.norm_eq_abs, abs_sq, poissonMass] using
    (poisson_second_hasSum r).summable

lemma poisson_cast_mean (r : ℝ≥0) : (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = r := by
  rw [integral_poissonMeasure]
  exact (poisson_first_hasSum r).tsum_eq

lemma poisson_cast_second (r : ℝ≥0) : (∫ n : ℕ, (n : ℝ)^2 ∂poissonMeasure r) = (r : ℝ)^2+r := by
  rw [integral_poissonMeasure]
  exact (poisson_second_hasSum r).tsum_eq

lemma poisson_cast_variance (r : ℝ≥0) : Var[(fun n : ℕ => (n : ℝ)); poissonMeasure r] = r := by
  rw [variance_eq_sub (poisson_cast_memLp r)]
  simp only [Pi.pow_apply, poisson_cast_second, poisson_cast_mean]
  ring

lemma integral_prod_sub_sq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P) :
    (∫ p : Ω × Ω, (X p.1-X p.2)^2 ∂P.prod P) = 2*Var[X;P] := by
  have hi := hX.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hLp : MemLp (fun p : Ω × Ω => X p.1-X p.2) 2 (P.prod P) :=
    (hX.comp_measurePreserving (measurePreserving_fst (μ := P) (ν := P))).sub
      (hX.comp_measurePreserving (measurePreserving_snd (μ := P) (ν := P)))
  rw [integral_prod _ hLp.integrable_sq]
  have he (x : Ω) : (∫ y, (X x-X y)^2 ∂P) =
      (X x)^2-2*X x*(∫ y, X y ∂P)+(∫ y, (X y)^2 ∂P) := by
    simp_rw [sub_sq]
    rw [integral_add (f := fun y => (X x)^2-2*X x*X y) (g := fun y => (X y)^2)
      ((integrable_const _).sub (hi.const_mul _)) hX.integrable_sq,
      integral_sub (f := fun _ => (X x)^2) (g := fun y => 2*X x*X y)
      (integrable_const _) (hi.const_mul _), integral_const,
      integral_const_mul, probReal_univ, one_smul]
  simp_rw [he]
  rw [integral_add (f := fun x => (X x)^2-2*X x*(∫ y, X y ∂P))
    (g := fun _ => ∫ y, (X y)^2 ∂P)
    (hX.integrable_sq.sub ((hi.const_mul 2).mul_const _)) (integrable_const _),
    integral_sub (f := fun x => (X x)^2) (g := fun x => 2*X x*(∫ y, X y ∂P))
      hX.integrable_sq ((hi.const_mul 2).mul_const _),integral_const,
    integral_mul_const,integral_const_mul,probReal_univ,one_smul,
    variance_eq_sub hX]
  simp only [Pi.pow_apply]
  ring

lemma variance_of_distance_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    {K : ℝ} (_hK : 0 ≤ K) (h : ∀ x y, |X x-X y| ≤ K*|Y x-Y y|) :
    Var[X;P] ≤ K^2 * Var[Y;P] := by
  have hDX := (hX.comp_measurePreserving (measurePreserving_fst (μ := P) (ν := P))).sub
      (hX.comp_measurePreserving (measurePreserving_snd (μ := P) (ν := P)))
  have hDY := (hY.comp_measurePreserving (measurePreserving_fst (μ := P) (ν := P))).sub
      (hY.comp_measurePreserving (measurePreserving_snd (μ := P) (ν := P)))
  have he := integral_mono hDX.integrable_sq (hDY.integrable_sq.const_mul (K^2))
    (show ∀ p : Ω × Ω, (X p.1-X p.2)^2 ≤ K^2*(Y p.1-Y p.2)^2 from fun p => by
      simpa only [mul_pow,sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (h p.1 p.2) 2)
  simp only [Pi.sub_apply,Function.comp_apply] at he
  rw [integral_const_mul,integral_prod_sub_sq P hX,integral_prod_sub_sq P hY] at he
  linarith

lemma nat_abs_step_bound {F : ℕ → ℝ} {K : ℝ} (h : ∀ m, |F (m+1)-F m| ≤ K) :
    ∀ m n, |F m-F n| ≤ K*|(m : ℝ)-n| := by
  have hle (n d : ℕ) : |F (n+d)-F n| ≤ K*d := by
    induction d with
    | zero => simp
    | succ d ih =>
      calc
        _ ≤ |F (n+d+1)-F (n+d)|+|F (n+d)-F n| := by
          simpa only [Nat.add_assoc] using abs_sub_le (F (n+d+1)) (F (n+d)) (F n)
        _ ≤ K+K*d := add_le_add (h (n+d)) ih
        _ = K*(d+1 : ℕ) := by push_cast <;> ring
  intro m n
  rcases le_total n m with hnm | hmn
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hnm
    simpa only [Nat.cast_add,add_sub_cancel_left,abs_of_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d)] using hle n d
  · obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [abs_sub_comm (F m) (F (m+d)),show (m : ℝ)-(m+d : ℕ) = -(d : ℝ) by push_cast; ring]
    simp only [abs_neg,abs_of_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    exact hle m d

lemma nat_step_memLp {P : Measure ℕ} [IsProbabilityMeasure P]
    (hP : MemLp (fun n : ℕ => (n : ℝ)) 2 P) {F : ℕ → ℝ} {K : ℝ}
    (h : ∀ m, |F (m+1)-F m| ≤ K) : MemLp F 2 P := by
  apply ((hP.const_mul K).add (memLp_const |F 0|)).mono' Measurable.of_discrete.aestronglyMeasurable
  apply ae_of_all
  intro m
  have hh := nat_abs_step_bound h m 0
  simp only [Nat.cast_zero,sub_zero,abs_of_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m)] at hh
  simp only [Pi.add_apply,Real.norm_eq_abs]
  linarith [abs_sub_abs_le_abs_sub (F m) (F 0)]

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_VarianceOfConditionalCenterBound
attribute [-instance] _root_.OAI.IsingPerceptron.enrichedCoordinateLaw_probability _root_.OAI.IsingPerceptron.enrichedGibbsReference_probability _root_.OAI.IsingPerceptron.spinLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Variance Of Conditional Center Bound. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

theorem variance_of_conditional_center_bound {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : A × B → ℝ} {X : A → ℝ} (hF : Measurable F) (hX : MemLp X 2 μ)
    (hi : ∀ a, Integrable (fun b => (F (a,b)-X a)^2) ν)
    (hc : ∀ a, ∫ b, F (a,b) ∂ν = X a) {C : A → ℝ} (hC : Integrable C μ)
    (hb : ∀ a, (∫ b, (F (a,b)-X a)^2 ∂ν) ≤ C a) :
    MemLp F 2 (μ.prod ν) ∧ Var[F; μ.prod ν] ≤ (∫ a, C a ∂μ)+Var[X; μ] := by
  let D : A × B → ℝ := fun p => F p-X p.1
  have hd : AEStronglyMeasurable D (μ.prod ν) :=
    hF.aestronglyMeasurable.sub (hX.aestronglyMeasurable.comp_measurePreserving
      (measurePreserving_fst (μ := μ) (ν := ν)))
  have hdi : Integrable (fun p => (D p)^2) (μ.prod ν) := by
    apply (integrable_prod_iff (hd.pow 2)).mpr
    refine ⟨ae_of_all _ hi, ?_⟩
    have hnorm : (fun a => ∫ b, ‖(D (a,b))^2‖ ∂ν) =
        fun a => ∫ b, (D (a,b))^2 ∂ν := by
      ext a
      apply integral_congr_ae
      apply ae_of_all
      intro b
      exact Real.norm_of_nonneg (sq_nonneg _)
    change Integrable (fun a => ∫ b, ‖(D (a,b))^2‖ ∂ν) μ
    rw [hnorm]
    apply hC.mono' (hd.pow 2).integral_prod_right'
    apply ae_of_all
    intro a
    change ‖∫ b, (D (a,b))^2 ∂ν‖ ≤ C a
    rw [Real.norm_of_nonneg (integral_nonneg (fun b => sq_nonneg (D (a,b))))]
    exact hb a
  have hDLp : MemLp D 2 (μ.prod ν) := (memLp_two_iff_integrable_sq hd).mpr hdi
  have hfLp : MemLp F 2 (μ.prod ν) := by
    convert hDLp.add (hX.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := ν))) using 1
    all_goals try with_reducible_and_instances rfl
    ext p
    simp [D]
  refine ⟨hfLp, ?_⟩
  have hsecLp (a : A) : MemLp (fun b => F (a,b)) 2 ν := by
    have hdm : Measurable (fun b => F (a,b)-X a) :=
      (hF.comp (measurable_const.prodMk measurable_id)).sub measurable_const
    have hL := (memLp_two_iff_integrable_sq hdm.aestronglyMeasurable).mpr (hi a)
    convert hL.add (memLp_const (X a)) using 1
    all_goals try with_reducible_and_instances rfl
    ext b
    simp
  have hsec (a : A) : (∫ b, F (a,b)^2 ∂ν) ≤ C a+(X a)^2 := by
    have hv := hb a
    have he := variance_eq_integral (hsecLp a).aemeasurable
    rw [hc a] at he
    rw [← he, variance_eq_sub (hsecLp a)] at hv
    simp only [Pi.pow_apply,hc a] at hv
    linarith
  have hh := integral_mono hfLp.integrable_sq.integral_prod_left
    (hC.add hX.integrable_sq) hsec
  simp only [Pi.add_apply] at hh
  rw [integral_add hC hX.integrable_sq] at hh
  rw [variance_eq_sub hfLp,variance_eq_sub hX]
  simp only [Pi.pow_apply]
  rw [integral_prod _ hfLp.integrable_sq,
    integral_prod _ (hfLp.integrable (by norm_num))]
  simp_rw [hc]
  linarith

theorem poisson_count_variance {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    [IsProbabilityMeasure Q] (r : ℝ≥0) {F : ℕ × Ω → ℝ} (hF : Measurable F)
    (hL : ∀ m, MemLp (fun ω => F (m,ω)) 2 Q) {C D K : ℝ} (hK : 0 ≤ K)
    (hv : ∀ m, Var[(fun ω => F (m,ω)); Q] ≤ C+D*m)
    (hs : ∀ m, |(∫ ω, F (m+1,ω) ∂Q)-(∫ ω, F (m,ω) ∂Q)| ≤ K) :
    MemLp F 2 ((poissonMeasure r).prod Q) ∧
      Var[F; (poissonMeasure r).prod Q] ≤ C+D*r+K^2*r := by
  let X := fun m => ∫ ω, F (m,ω) ∂Q
  have hx : MemLp X 2 (poissonMeasure r) := nat_step_memLp (poisson_cast_memLp r) hs
  have hc : Integrable (fun m : ℕ => C+D*m) (poissonMeasure r) :=
    (integrable_const C).add (((poisson_cast_memLp r).integrable (by norm_num)).const_mul D)
  have hh := variance_of_conditional_center_bound (poissonMeasure r) Q hF hx
    (fun m => ((hL m).sub (memLp_const (X m))).integrable_sq) (fun _ => rfl) hc
    (fun m => by
      rw [← variance_eq_integral (hL m).aemeasurable]
      exact hv m)
  refine ⟨hh.1, ?_⟩
  have hhx := variance_of_distance_bound (poissonMeasure r) hx (poisson_cast_memLp r) hK
    (nat_abs_step_bound hs)
  rw [poisson_cast_variance] at hhx
  have hmean : (∫ m : ℕ, C+D*m ∂poissonMeasure r) = C+D*r := by
    rw [integral_add (integrable_const C)
      (((poisson_cast_memLp r).integrable (by norm_num)).const_mul D),
      integral_const,probReal_univ,one_smul,integral_const_mul,poisson_cast_mean]
  rw [hmean] at hh
  linarith [hh.2]

lemma infinite_prefix_preserving {A : Type*} [MeasurableSpace A] (P : Measure A)
    [IsProbabilityMeasure P] (M : ℕ) :
    MeasurePreserving (fun y : ℕ → A => fun i : Fin M => y i)
      (Measure.infinitePi (fun _ : ℕ => P)) (Measure.pi (fun _ : Fin M => P)) := by
  refine ⟨Measurable.of_eval (fun index => measurable_pi_apply (index : ℕ)), ?_⟩
  rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,Measure.infinitePi_eq_pi]

lemma rootPrefix_preserving {m : ℕ} {A : Type*} [MeasurableSpace A] (P : Measure A)
    [IsProbabilityMeasure P] (M : ℕ) :
    MeasurePreserving (rootPrefix (m := m) (A := A) M)
      ((Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod (Measure.infinitePi (fun _ : ℕ => P)))
      ((Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod (Measure.pi (fun _ : Fin M => P))) :=
  (MeasurePreserving.id _).prod (infinite_prefix_preserving P M)

lemma patternBase_prefix_succ {I A : Type*} [Fintype I] (φ : A → I → ℝ)
    (y : ℕ → A) (M : ℕ) :
    patternBase φ (fun i : Fin (M+1) => y i) = patternBase φ (fun i : Fin M => y i)+φ (y M) := by
  ext x
  simp only [patternBase,Fin.sum_univ_castSucc,Fin.val_castSucc,Fin.val_last,Pi.add_apply]

lemma rootEnergy_prefix_step {I A : Type*} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m : ℕ} (a : I → Fin m → ℝ) {φ : A → I → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (p : InfiniteRootData m A) (M : ℕ) :
    |rootEnergy n b μ ν (patternBase φ (fun i : Fin (M+1) => p.2 i)) a p.1-
      rootEnergy n b μ ν (patternBase φ (fun i : Fin M => p.2 i)) a p.1| ≤ K := by
  apply (rootEnergy_base_lipschitz n b μ ν hμ hb _ _ a p.1).trans
  rw [patternBase_prefix_succ,add_sub_cancel_left]
  exact (pi_norm_le_iff_of_nonneg hK).mpr (fun x => by simpa only [Real.norm_eq_abs] using hφ (p.2 M) x)

lemma integral_difference_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} (hX : Integrable X P) (hY : Integrable Y P)
    {K : ℝ} (h : ∀ ω, |X ω-Y ω| ≤ K) : |(∫ ω, X ω ∂P)-(∫ ω, Y ω ∂P)| ≤ K := by
  rw [← integral_sub hX hY,← Real.norm_eq_abs]
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ := P) (f := fun ω => X ω-Y ω) (C := K)
    (ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs] using h ω))

variable {I A : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
variable [MeasurableSpace A]

lemma measurable_infinitePatternRoot (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure (I → ℝ))
    (ν : Measure I) {m : ℕ} (a : I → Fin m → ℝ) {φ : A → I → ℝ} (hm : Measurable φ) :
    Measurable (infinitePatternRoot n b μ ν a φ) := by
  apply measurable_from_prod_countable_right
  intro M
  apply (measurable_energyRecursion n b μ ν).comp
  apply Measurable.of_eval
  intro x
  exact (Finset.measurable_sum Finset.univ (fun i (_ : i ∈ (Finset.univ : Finset (Fin M))) =>
    ((measurable_pi_apply x).comp hm).comp
    ((measurable_pi_apply (i : ℕ)).comp measurable_snd))).add
    (by fun_prop : Measurable (fun p : InfiniteRootData m A => ∑ j, a x j*p.1 j))

lemma infinitePatternRoot_fixed_variance (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m : ℕ} (a : I → Fin m → ℝ) (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j)
    (ha : ∀ x j, |a x j| ≤ c j) (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → I → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K) (hφ : ∀ y x, |φ y x| ≤ K)
    (M : ℕ) :
    let Q := (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod (Measure.infinitePi (fun _ : ℕ => P))
    MemLp (fun p => infinitePatternRoot n b μ ν a φ (M,p)) 2 Q ∧
      Var[(fun p => infinitePatternRoot n b μ ν a φ (M,p));Q] ≤ (∑ j, (c j)^2)+M*(2*K)^2 := by
  have hL := pattern_root_energy_memLp n b μ ν hμ hb a c hc ha P hm hK hφ (M := M)
  have hv := pattern_root_energy_variance n b μ ν hμ hb a c hc ha P hm hK hφ (M := M)
  have hp := rootPrefix_preserving (m := m) P M
  constructor
  · simpa only [infinitePatternRoot, Function.comp_def, rootPrefix] using
      hL.comp_measurePreserving hp
  · simpa only [infinitePatternRoot, Function.comp_def, rootPrefix] using
      (hp.variance_fun_comp hL.aemeasurable).le.trans hv

theorem infinitePatternRoot_poisson_variance (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure (I → ℝ)) (ν : Measure I) [IsProbabilityMeasure ν]
    (hμ : ∀ i < n, ExponentialNormMoments (μ i : Measure (I → ℝ))) (hb : ∀ i < n, 0 < b i)
    {m : ℕ} (a : I → Fin m → ℝ) (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j)
    (ha : ∀ x j, |a x j| ≤ c j) (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → I → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K) (hφ : ∀ y x, |φ y x| ≤ K)
    (r : ℝ≥0) :
    let Q := (poissonMeasure r).prod ((Measure.pi (fun _ : Fin m => gaussianReal 0 1)).prod
      (Measure.infinitePi (fun _ : ℕ => P)))
    MemLp (infinitePatternRoot n b μ ν a φ) 2 Q ∧
      Var[infinitePatternRoot n b μ ν a φ;Q] ≤ (∑ j, (c j)^2)+(2*K)^2*r+K^2*r := by
  have hh := infinitePatternRoot_fixed_variance n b μ ν hμ hb a c hc ha P hm hK hφ
  apply poisson_count_variance _ r (measurable_infinitePatternRoot n b μ ν a hm)
    (fun M => (hh M).1) hK
  · intro M
    simpa only [mul_comm (M : ℝ)] using (hh M).2
  · intro M
    apply integral_difference_bound _ ((hh (M+1)).1.integrable (by norm_num))
      ((hh M).1.integrable (by norm_num))
    exact fun p => rootEnergy_prefix_step n b μ ν hμ hb a hK hφ p M

end IsingPerceptron

namespace IsingPerceptron

lemma enriched_poisson_root_variance_oai {N : ℕ} (hN : 0 < N) (n : ℕ) (b : ℕ → ℝ)
    (hb : ∀ i < n, 0 < b i) {h : ℕ → ℝ} (hh : Monotone h) (h0 : 0 ≤ h 0)
    (u : Fin N → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν]
    {A : Type*} [MeasurableSpace A] (P : Measure A) [IsProbabilityMeasure P]
    {φ : A → Spin N → ℝ} (hm : Measurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hφ : ∀ y x, |φ y x| ≤ K) (r : ℝ≥0) :
    let μ := fun i => enrichedIncrementLaw N n h u (i+1)
    let Q := (poissonMeasure r).prod ((Measure.pi (fun _ : Fin (EnrichedRootSize N) => gaussianReal 0 1)).prod
      (Measure.infinitePi (fun _ : ℕ => P)))
    let X := infinitePatternRoot n b μ ν (enrichedCoefficientsFin N n h u 0) φ
    MemLp X 2 Q ∧ Var[X;Q] ≤ N*h 0+4*N*(perturbationScale N)^2+5*K^2*r := by
  let x₀ : Spin N := fun _ => 0
  let c := fun j => |enrichedCoefficientsFin N n h u 0 x₀ j|
  have H := infinitePatternRoot_poisson_variance n b
    (fun i => enrichedIncrementLaw N n h u (i+1)) ν
    (fun i _ => enrichedIncrementLaw_moments N n h u (i+1)) hb
    (enrichedCoefficientsFin N n h u 0) c (fun _ => abs_nonneg _)
    (fun x j => (enrichedLevelCoefficient_abs n h u 0 x x₀ _).le) P hm hK hφ r
  have hc : (∑ j, (c j)^2) ≤ N*h 0+4*N*(perturbationScale N)^2 := by
    have he := (Fintype.equivFin (EnrichedBlock N)).symm.sum_comp
      (fun j => |enrichedLevelCoefficient n h u 0 x₀ j|^2)
    change (∑ j, |enrichedLevelCoefficient n h u 0 x₀ ((Fintype.equivFin _).symm j)|^2) ≤ _
    rw [he]
    exact enrichedRoot_envelope_sq hN n hh h0 u hu x₀
  refine ⟨H.1, ?_⟩
  linarith [H.2]

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.IsingPerceptron.enriched_poisson_root_variance_oai.{u_1} := @OAI.IsingPerceptron.enriched_poisson_root_variance_oai.{u_1}
