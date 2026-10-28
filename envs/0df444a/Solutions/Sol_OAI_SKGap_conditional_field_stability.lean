-- Prove2me | solution 1 for OAI.SKGap.conditional_field_stability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:43:47.287996+00:00
-- url     : https://prove2.me/submissions/4e1c61c3-6ebf-412c-9720-0ad7145d9112

import Mathlib
import Definitions.Def_OAIQ072A000
import Theorems.Thm_OAI_SKGap_conditional_empirical_simultaneous

section
-- module Solutions.OAIQ072_SK.Compat
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ScalarParametersJoined
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction

namespace SKGap

lemma continuous_scalarQMoment : Continuous scalarQMoment := by
  let f : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup (fun x => tanh x^2) (by fun_prop) 1
    (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (tanh x))] using (tanh_sq_lt_one x).le)
  exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction f

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_ConditionalBadSet
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma isClosed_badFieldSet (n : ℕ) (j A ε c : ℝ) : IsClosed (badFieldSet n j A ε c) := by
  let X := ↥(Set.Icc (0 : Fin n → ℝ) (fun _=>A)) × ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
  let : CompactSpace ↥(Set.Icc (0 : Fin n → ℝ) (fun _=>A)) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  let : CompactSpace ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  let S : Set (X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ))) :=
    {p | (∑ i,((p.1.1:Fin n → ℝ) i-spinVariance p.2.2 i)^2) ≤ ε^2*(n:ℝ) ∧
      quadraticForm (fieldHessian j (plantedInteraction j p.2.1) p.2.2 p.1.1) (p.1.2:EuclideanSpace ℝ (Fin n)).ofLp ≤ c}
  have ha (i : Fin n) : Continuous (fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) =>
      (p.1.1:Fin n → ℝ) i) :=
    (continuous_apply i).comp (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))
  have hx (i : Fin n) : Continuous (fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) =>
      (p.1.2:EuclideanSpace ℝ (Fin n)).ofLp i) :=
    (continuous_apply i).comp ((PiLp.continuous_ofLp 2 (fun _ : Fin n=>ℝ)).comp
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)))
  have hy (i : Fin n) : Continuous (fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) =>
      tanh (p.2.2 i)) := continuous_tanh.comp ((continuous_apply i).comp (continuous_snd.comp continuous_snd))
  have hS : IsClosed S := by
    apply IsClosed.inter
    · exact isClosed_le (f := fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) =>
        ∑ i,((p.1.1:Fin n → ℝ) i-spinVariance p.2.2 i)^2)
        (g := fun _ => ε^2*(n:ℝ)) (by
        apply continuous_finsetSum
        intro i _
        exact ((ha i).sub (continuous_const.sub ((hy i).pow 2))).pow 2) continuous_const
    · exact isClosed_le (f := fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) =>
        quadraticForm (fieldHessian j (plantedInteraction j p.2.1) p.2.2 p.1.1)
          (p.1.2:EuclideanSpace ℝ (Fin n)).ofLp) (g := fun _=>c) (by
        dsimp [X,quadraticForm,fieldHessian,hessianCore,plantedInteraction,onsager,overlap,magnetization]
        apply continuous_finsetSum; intro i _
        apply continuous_finsetSum; intro k _
        apply Continuous.mul _ (hx k)
        apply Continuous.mul (hx i)
        apply Continuous.add continuous_const
        apply Continuous.mul _ (Real.continuous_sqrt.comp (ha k))
        apply Continuous.mul (Real.continuous_sqrt.comp (ha i))
        exact (((continuous_const.mul (continuous_const.sub
          ((continuous_finsetSum _ (fun l _ => (hy l).pow 2)).div_const _))).mul continuous_const).sub
          ((by fun_prop : Continuous (fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) => p.2.1 i k)).add continuous_const)).sub
          (((continuous_const.mul (hy i))).mul (hy k))) continuous_const
  have hproj := isClosedMap_snd_of_compactSpace S hS
  convert hproj using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  constructor
  · rintro ⟨a,ha,hclose,x,hx,hquad⟩
    have ha' : a ∈ Icc (0 : Fin n → ℝ) (fun _=>A) := ⟨fun i=>(ha i).1,fun i=>(ha i).2⟩
    have hx' : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hx
    exact ⟨((⟨a,ha'⟩,⟨x,hx'⟩),p),⟨hclose,hquad⟩,rfl⟩
  · rintro ⟨⟨⟨a,x⟩,p'⟩,hS,rfl⟩
    exact ⟨a,fun i=>⟨a.2.1 i,a.2.2 i⟩,hS.1,x,by simpa only [Metric.mem_sphere,dist_zero_right] using x.2,hS.2⟩

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianRegression
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal
namespace SKGap.GaussianRegression

theorem law_eq_of_mean_covariance {Ω Ω' ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype ι] [DecidableEq ι]
    {P : Measure Ω} {P' : Measure Ω'} {X : Ω → ι → ℝ} {Y : Ω' → ι → ℝ}
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y P')
    (hm : ∀ i, (∫ w, X w i ∂P) = ∫ w, Y w i ∂P')
    (hc : ∀ i k, cov[fun w => X w i, fun w => X w k; P] =
      cov[fun w => Y w i, fun w => Y w k; P']) :
    P.map X = P'.map Y := by
  classical
  have := hX.isProbabilityMeasure
  have := hY.isProbabilityMeasure
  apply Measure.ext_of_charFunDual
  ext L
  rw [hX.charFunDual_map_eq,hY.charFunDual_map_eq]
  let c : ι → ℝ := fun i => L (fun k => if i=k then 1 else 0)
  have hL (x : ι → ℝ) : L x = ∑ i, x i * c i := by
    simpa only [c, smul_eq_mul, ContinuousLinearMap.coe_coe] using L.toLinearMap.pi_apply_eq_sum_univ x
  have hLX : L ∘ X = fun w => ∑ i, X w i*c i := funext (fun w => hL (X w))
  have hLY : L ∘ Y = fun w => ∑ i, Y w i*c i := funext (fun w => hL (Y w))
  have hiX (i : ι) := (hX.eval i).memLp_two
  have hiY (i : ι) := (hY.eval i).memLp_two
  have hem : (∫ w, (L ∘ X) w ∂P) = ∫ w, (L ∘ Y) w ∂P' := by
    rw [hLX,hLY]
    rw [integral_finsetSum _ (fun i _ => ((hX.eval i).integrable.mul_const _)),
      integral_finsetSum _ (fun i _ => ((hY.eval i).integrable.mul_const _))]
    simp only [integral_mul_const,hm]
  have hev : Var[L ∘ X; P] = Var[L ∘ Y; P'] := by
    rw [← covariance_self (hX.map L).aemeasurable,
      ← covariance_self (hY.map L).aemeasurable]
    rw [hLX,hLY]
    rw [covariance_fun_sum_fun_sum (fun i => (hiX i).mul_const _) (fun i => (hiX i).mul_const _),
      covariance_fun_sum_fun_sum (fun i => (hiY i).mul_const _) (fun i => (hiY i).mul_const _)]
    simp only [covariance_mul_const_left,covariance_mul_const_right,hc]
  rw [hev,hem]

end SKGap.GaussianRegression
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal

lemma coordinate_hasLaw {κ : Type*} [Fintype κ] (i : κ) :
    HasLaw (fun g : κ → ℝ => g i) (gaussianReal 0 1) (gaussianCoordinates κ) :=
  ⟨(measurable_pi_apply i).aemeasurable,
    (measurePreserving_eval (fun _ : κ => gaussianReal 0 1) i).map_eq⟩

lemma coordinates_gaussian {κ : Type*} [Fintype κ] :
    HasGaussianLaw (fun g : κ → ℝ => g) (gaussianCoordinates κ) :=
  (iIndepFun_pi (fun _ : κ => aemeasurable_id)).hasGaussianLaw
    (fun i => (coordinate_hasLaw i).hasGaussianLaw)

lemma coordinate_covariance {κ : Type*} [Fintype κ] [DecidableEq κ] (i k : κ) :
    cov[fun g : κ → ℝ => g i,fun g : κ → ℝ => g k;gaussianCoordinates κ] =
      if i=k then 1 else 0 := by
  by_cases h : i=k
  · subst k
    rw [ite_eq_left rfl,covariance_self (measurable_pi_apply i).aemeasurable,
      (coordinate_hasLaw i).variance_eq]
    simp
  · rw [ite_eq_right h]
    exact ((iIndepFun_pi (fun _ : κ => aemeasurable_id)).indepFun h).covariance_eq_zero
      (coordinate_hasLaw i).hasGaussianLaw.memLp_two (coordinate_hasLaw k).hasGaussianLaw.memLp_two

lemma linear_gaussian_mean {κ : Type*} [Fintype κ] (a : κ → ℝ) :
    (∫ g, ∑ i, a i*g i ∂gaussianCoordinates κ) = 0 := by
  rw [integral_finsetSum _ (fun i _ => (coordinate_hasLaw i).hasGaussianLaw.integrable.const_mul _)]
  simp [integral_const_mul,(coordinate_hasLaw _).integral_eq]

lemma matrix_sample_gaussian {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) :
    HasGaussianLaw (fun g => A*ᵥg) (gaussianCoordinates κ) :=
  coordinates_gaussian.map_fun (GaussianRegression.matrixCLM A)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GOEGaussian
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma goeEntryCoeff_sample (r : ℝ) (g : MatrixCoordinates ι → ℝ) (i k : ι) :
    (goeEntryCoeff r*ᵥg) (i,k) = goeMatrix r g i k := by
  simp only [mulVec,dotProduct,goeEntryCoeff,mul_assoc,add_mul]
  rw [← Finset.mul_sum,Finset.sum_add_distrib]
  simp [goeMatrix]

lemma goe_matrix_gaussian (r : ℝ) :
    HasGaussianLaw (fun (g : MatrixCoordinates ι → ℝ) (p : ι × ι) => goeMatrix r g p.1 p.2) (gaussianCoordinates (MatrixCoordinates ι)) := by
  have hh := matrix_sample_gaussian (goeEntryCoeff (ι := ι) r)
  simpa only [show (fun g => goeEntryCoeff (ι := ι) r*ᵥg) =
    (fun g p => goeMatrix r g p.1 p.2) from funext (fun g => funext (fun p => goeEntryCoeff_sample r g p.1 p.2))] using hh

lemma goe_mean_zero (r : ℝ) (i k : ι) :
    (∫ g, goeMatrix r g i k ∂gaussianCoordinates (MatrixCoordinates ι))=0 := by
  simpa only [← goeEntryCoeff_sample,mulVec,dotProduct] using linear_gaussian_mean (goeEntryCoeff (ι := ι) r (i,k))

lemma goe_entry_cov {r : ℝ} (hr : 0 ≤ r) (i k l m : ι) :
    cov[fun g => goeMatrix r g i k,fun g => goeMatrix r g l m;
      gaussianCoordinates (MatrixCoordinates ι)] =
    r*((if i=l then 1 else 0)*(if k=m then 1 else 0)+
       (if i=m then 1 else 0)*(if k=l then 1 else 0)) := by
  let μ := gaussianCoordinates (MatrixCoordinates ι)
  have hm (a : MatrixCoordinates ι) := (coordinate_hasLaw a).hasGaussianLaw.memLp_two
  change cov[fun g : MatrixCoordinates ι → ℝ => sqrt (2*r)/2*(g (.inl (i,k))+g (.inl (k,i))),
    fun g => sqrt (2*r)/2*(g (.inl (l,m))+g (.inl (m,l))); μ]=_
  rw [covariance_const_mul_left,covariance_const_mul_right]
  change sqrt (2*r)/2*(sqrt (2*r)/2*cov[(fun g => g (.inl (i,k))) + (fun g => g (.inl (k,i))),
    (fun g => g (.inl (l,m))) + (fun g => g (.inl (m,l)));gaussianCoordinates (MatrixCoordinates ι)]) = _
  rw [covariance_add_left (hm _) (hm _) ((hm _).add (hm _)),
    covariance_add_right (hm _) (hm _) (hm _),
    covariance_add_right (hm _) (hm _) (hm _)]
  simp only [coordinate_covariance,Sum.inl.injEq,Prod.mk.injEq]
  have hs : (sqrt (2*r)/2)^2=r/2 := by rw [div_pow,sq_sqrt (by positivity)]; ring
  have hs' : sqrt (2*r)/2*(sqrt (2*r)/2)=r/2 := by nlinarith only [hs]
  rw [← mul_assoc,hs']
  have hind (p q : Prop) [Decidable p] [Decidable q] :
      (if p ∧ q then (1:ℝ) else 0)=(if p then 1 else 0)*(if q then 1 else 0) := by
    split_ifs <;> simp_all
  simp_rw [hind]
  ring

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianDisintegration
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal
namespace SKGap.GaussianRegression

lemma residual_joint_gaussian {Ω ι κ : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] {P : Measure Ω} {X : Ω → ι → ℝ} {Y : Ω → κ → ℝ}
    (hXY : HasGaussianLaw (fun w => (X w,Y w)) P) (K : Matrix ι κ ℝ) :
    HasGaussianLaw (fun w => (X w-K*ᵥ Y w,Y w)) P :=
  hXY.map_fun (((ContinuousLinearMap.fst ℝ (ι → ℝ) (κ → ℝ))-
    (matrixCLM K).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (κ → ℝ))).prod
    (ContinuousLinearMap.snd ℝ (ι → ℝ) (κ → ℝ)))

end SKGap.GaussianRegression
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_EmpiricalLaw
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
namespace SKGap

variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma empiricalLaw_coe (y : ι → ℝ) : (empiricalLaw y : Measure ℝ) =
    (Fintype.card ι : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (y i) := rfl

lemma integral_empiricalLaw (y : ι → ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂empiricalLaw y) = (Fintype.card ι : ℝ)⁻¹ * ∑ i, f (y i) := by
  rw [empiricalLaw_coe, integral_smul_measure,
    integral_finsetSum_measure (fun i _ => integrable_dirac (by simp))]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]

lemma card_mul_integral_empiricalLaw (y : ι → ℝ) (f : ℝ → ℝ) :
    (Fintype.card ι : ℝ)*(∫ x, f x ∂empiricalLaw y) = ∑ i, f (y i) := by
  rw [integral_empiricalLaw, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast (Fintype.card_pos (α := ι)).ne'), one_mul]

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianTiltMass
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open Set Filter Topology
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction

namespace SKGap

lemma absorb_finite_exponential_factor (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ r : ℝ,
      (M:ℝ)*exp ((n:ℝ)*r) ≤ exp ((n:ℝ)*(r+ε)) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (log ((M:ℝ)+1)/ε)
  refine ⟨N,?_⟩
  intro n hn r
  have hcast : (N:ℝ) ≤ n := by exact_mod_cast hn
  have hnlog : log ((M:ℝ)+1) ≤ (n:ℝ)*ε := by
    have h := (div_lt_iff₀ hε).mp hN
    nlinarith
  have he : (M:ℝ) ≤ exp ((n:ℝ)*ε) := by
    have h := exp_le_exp.mpr hnlog
    rw [exp_log (by positivity)] at h
    linarith
  calc
    _ ≤ exp ((n:ℝ)*ε)*exp ((n:ℝ)*r) := mul_le_mul_of_nonneg_right he (exp_pos _).le
    _ = _ := by rw [← exp_add]; congr 1; ring

end SKGap

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_RegressionMoments
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap.GaussianRegression
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators
variable {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
  {P : Measure Ω} {X : Ω → ι → ℝ} {Y : Ω → κ → ℝ}

lemma residual_mean_zero (hXY : HasGaussianLaw (fun w => (X w,Y w)) P)
    (K : Matrix ι κ ℝ) (hx : ∀ i, (∫ w, X w i ∂P)=0)
    (hy : ∀ k, (∫ w, Y w k ∂P)=0) (i : ι) :
    (∫ w, (X w-K*ᵥY w) i ∂P)=0 := by
  have hK : Integrable (fun w => ∑ k,K i k*Y w k) P :=
    ((hXY.snd.map (matrixCLM K)).eval i).integrable
  change (∫ w, X w i-∑ k, K i k*Y w k ∂P)=0
  rw [integral_sub (hXY.fst.eval i).integrable hK,
    integral_finsetSum _ (fun k _ => (hXY.snd.eval k).integrable.const_mul _)]
  simp only [integral_const_mul,hx,hy,mul_zero,Finset.sum_const_zero,sub_zero]

lemma residual_cross_covariance (hXY : HasGaussianLaw (fun w => (X w,Y w)) P)
    (K : Matrix ι κ ℝ)
    (hc : ∀ i k, cov[fun w => X w i,fun w => Y w k;P]=
      ∑ l, K i l*cov[fun w => Y w l,fun w => Y w k;P]) (i : ι) (k : κ) :
    cov[fun w => (X w-K*ᵥY w) i,fun w => Y w k;P]=0 := by
  have := hXY.isProbabilityMeasure
  have hK : MemLp (fun w => ∑ l,K i l*Y w l) 2 P :=
    ((hXY.snd.map (matrixCLM K)).eval i).memLp_two
  change cov[fun w => X w i-∑ l,K i l*Y w l,fun w => Y w k;P]=0
  rw [covariance_fun_sub_left (hXY.fst.eval i).memLp_two hK (hXY.snd.eval k).memLp_two,
    covariance_fun_sum_left (fun l => (hXY.snd.eval l).memLp_two.const_mul _) (hXY.snd.eval k).memLp_two]
  simp only [covariance_const_mul_left,hc,sub_self]

lemma residual_covariance (hXY : HasGaussianLaw (fun w => (X w,Y w)) P)
    (K : Matrix ι κ ℝ)
    (hc : ∀ i k, cov[fun w => X w i,fun w => Y w k;P]=
      ∑ l, K i l*cov[fun w => Y w l,fun w => Y w k;P]) (i k : ι) :
    cov[fun w => (X w-K*ᵥY w) i,fun w => (X w-K*ᵥY w) k;P]=
      cov[fun w => X w i,fun w => X w k;P]-
      ∑ l, K i l*cov[fun w => Y w l,fun w => X w k;P] := by
  have := hXY.isProbabilityMeasure
  have hR := (residual_joint_gaussian hXY K).fst
  have hK (q : ι) : MemLp (fun w => ∑ l,K q l*Y w l) 2 P :=
    ((hXY.snd.map (matrixCLM K)).eval q).memLp_two
  change cov[fun w => (X w-K*ᵥY w) i,fun w => X w k-∑ l,K k l*Y w l;P]=_
  rw [covariance_fun_sub_right (hR.eval i).memLp_two (hXY.fst.eval k).memLp_two (hK k),
    covariance_fun_sum_right (fun l => (hXY.snd.eval l).memLp_two.const_mul _) (hR.eval i).memLp_two]
  simp only [covariance_const_mul_right,residual_cross_covariance hXY K hc,mul_zero,
    Finset.sum_const_zero,sub_zero]
  change cov[fun w => X w i-∑ l,K i l*Y w l,fun w => X w k;P]=_
  rw [covariance_fun_sub_left (hXY.fst.eval i).memLp_two (hK i) (hXY.fst.eval k).memLp_two,
    covariance_fun_sum_left (fun l => (hXY.snd.eval l).memLp_two.const_mul _) (hXY.fst.eval k).memLp_two]
  simp only [covariance_const_mul_left]

end SKGap.GaussianRegression
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Posterior_GOEObservation
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma observationCoeff_sample (r v : ℝ) (m : ι → ℝ) (g : MatrixCoordinates ι → ℝ) :
    observationCoeff r v m*ᵥg=goeObservation r v m g := by
  ext i
  change (∑ a, ((∑ k, m k*goeEntryCoeff r (i,k) a)+sqrt v*(if a=Sum.inr i then 1 else 0))*g a)=
    (∑ k, goeMatrix r g i k*m k)+sqrt v*g (.inr i)
  rw [show (∑ a, ((∑ k, m k*goeEntryCoeff r (i,k) a)+sqrt v*(if a=Sum.inr i then 1 else 0))*g a)=
    (∑ a, (∑ k, m k*goeEntryCoeff r (i,k) a)*g a)+sqrt v*g (.inr i) by
      simp [add_mul,Finset.sum_add_distrib]]
  congr 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have hh := goeEntryCoeff_sample r g i k
  change (∑ a, m k*goeEntryCoeff r (i,k) a*g a)=goeMatrix r g i k*m k
  rw [show (∑ a, m k*goeEntryCoeff r (i,k) a*g a)=m k*((goeEntryCoeff r*ᵥg) (i,k)) by
    simp only [mulVec,dotProduct,Finset.mul_sum,mul_assoc]]
  rw [hh,mul_comm]

lemma goe_observation_joint_gaussian (r v : ℝ) (m : ι → ℝ) :
    HasGaussianLaw (fun g => ((fun p : ι × ι => goeMatrix r g p.1 p.2),goeObservation r v m g))
      (gaussianCoordinates (MatrixCoordinates ι)) := by
  have hh := coordinates_gaussian.map_fun
    ((GaussianRegression.matrixCLM (goeEntryCoeff (ι := ι) r)).prod
      (GaussianRegression.matrixCLM (observationCoeff r v m)))
  apply hh.congr
  filter_upwards [] with g
  simp only [ContinuousLinearMap.prod_apply,GaussianRegression.matrixCLM_apply,
    observationCoeff_sample]
  congr 1
  funext p
  exact goeEntryCoeff_sample r g p.1 p.2

lemma goe_noise_cov (r : ℝ) (i k l : ι) :
    cov[fun g => goeMatrix r g i k,fun g => g (.inr l);gaussianCoordinates (MatrixCoordinates ι)]=0 := by
  have hm (a : MatrixCoordinates ι) := (coordinate_hasLaw a).hasGaussianLaw.memLp_two
  change cov[fun g : MatrixCoordinates ι → ℝ => sqrt (2*r)/2*(g (.inl (i,k))+g (.inl (k,i))),
    fun g => g (.inr l);gaussianCoordinates (MatrixCoordinates ι)]=0
  rw [covariance_const_mul_left]
  change sqrt (2*r)/2*cov[(fun g => g (.inl (i,k)))+(fun g => g (.inl (k,i))),
    fun g => g (.inr l);gaussianCoordinates (MatrixCoordinates ι)]=0
  rw [covariance_add_left (hm _) (hm _) (hm _)]
  simp [coordinate_covariance]

lemma goe_mulVec_memLp (r : ℝ) (m : ι → ℝ) (i : ι) :
    MemLp (fun g => (goeMatrix r g*ᵥm) i) 2 (gaussianCoordinates (MatrixCoordinates ι)) := by
  have hh := memLp_finsetSum (Finset.univ : Finset ι)
    (fun k _ => (goe_matrix_gaussian (ι := ι) r).eval (i,k) |>.memLp_two.mul_const (m k))
  simpa only [mulVec,dotProduct] using hh

lemma goe_entry_observation_cov {r : ℝ} (hr : 0 ≤ r) (v : ℝ) (m : ι → ℝ) (i k l : ι) :
    cov[fun g => goeMatrix r g i k,fun g => goeObservation r v m g l;
      gaussianCoordinates (MatrixCoordinates ι)] =
      r*((if i=l then m k else 0)+(if k=l then m i else 0)) := by
  have hW := (goe_matrix_gaussian (ι := ι) r).eval (i,k) |>.memLp_two
  have hM := goe_mulVec_memLp r m l
  have hN := (coordinate_hasLaw (Sum.inr l : MatrixCoordinates ι)).hasGaussianLaw.memLp_two.const_mul (sqrt v)
  change cov[fun g => goeMatrix r g i k,(fun g => (goeMatrix r g*ᵥm) l)+
    (fun g => sqrt v*g (.inr l));gaussianCoordinates (MatrixCoordinates ι)] = _
  rw [covariance_add_right hW hM hN,covariance_const_mul_right,goe_noise_cov,mul_zero,add_zero]
  change cov[fun g => goeMatrix r g i k,fun g => ∑ a, goeMatrix r g l a*m a;_]=_
  rw [covariance_fun_sum_right (fun a => (goe_matrix_gaussian (ι := ι) r).eval (l,a) |>.memLp_two.mul_const (m a)) hW]
  simp only [covariance_mul_const_right,goe_entry_cov hr]
  by_cases hil : i=l <;> by_cases hkl : k=l <;>
    simp [hil,hkl,mul_add,add_mul,Finset.sum_add_distrib]

lemma goe_mulVec_noise_cov (r : ℝ) (m : ι → ℝ) (i l : ι) :
    cov[fun g => (goeMatrix r g*ᵥm) i,fun g => g (.inr l);gaussianCoordinates (MatrixCoordinates ι)]=0 := by
  change cov[fun g => ∑ a, goeMatrix r g i a*m a,fun g => g (.inr l);_]=_
  rw [covariance_fun_sum_left
    (fun a => (goe_matrix_gaussian (ι := ι) r).eval (i,a) |>.memLp_two.mul_const (m a))
    (coordinate_hasLaw (Sum.inr l : MatrixCoordinates ι)).hasGaussianLaw.memLp_two]
  simp [covariance_mul_const_left,goe_noise_cov]

end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma goe_mulVec_cov {r : ℝ} (hr : 0 ≤ r) (m : ι → ℝ) (i l : ι) :
    cov[fun g => (goeMatrix r g*ᵥm) i,fun g => (goeMatrix r g*ᵥm) l;
      gaussianCoordinates (MatrixCoordinates ι)] =
    r*((if i=l then ∑ k, m k^2 else 0)+m i*m l) := by
  have hc (k : ι) : cov[fun g => goeMatrix r g i k,fun g => (goeMatrix r g*ᵥm) l;
      gaussianCoordinates (MatrixCoordinates ι)] =
      r*((if i=l then m k else 0)+(if k=l then m i else 0)) := by
    simpa only [goeObservation,sqrt_zero,zero_mul,add_zero] using
      goe_entry_observation_cov hr 0 m i k l
  change cov[fun g => ∑ k, goeMatrix r g i k*m k,fun g => (goeMatrix r g*ᵥm) l;_]=_
  rw [covariance_fun_sum_left
    (fun k => (goe_matrix_gaussian (ι := ι) r).eval (i,k) |>.memLp_two.mul_const (m k))
    (goe_mulVec_memLp r m l)]
  simp only [covariance_mul_const_left,hc]
  by_cases h : i=l
  · subst l
    simp [mul_add,add_mul,mul_assoc,← pow_two,Finset.sum_add_distrib,← Finset.mul_sum]
  · simp [h,mul_ite,ite_mul]
    ring

lemma goe_observation_mean (r v : ℝ) (m : ι → ℝ) (i : ι) :
    (∫ g, goeObservation r v m g i ∂gaussianCoordinates (MatrixCoordinates ι))=0 := by
  simpa only [← observationCoeff_sample,mulVec,dotProduct] using
    linear_gaussian_mean (observationCoeff r v m i)

lemma goe_observation_cov {r v : ℝ} (hr : 0 ≤ r) (hv : 0 ≤ v) (m : ι → ℝ) (i l : ι) :
    cov[fun g => goeObservation r v m g i,fun g => goeObservation r v m g l;
      gaussianCoordinates (MatrixCoordinates ι)] =
      (r*(∑ k,m k^2)+v)*(if i=l then 1 else 0)+r*m i*m l := by
  have hm (k : ι) := goe_mulVec_memLp r m k
  have hn (k : ι) := (coordinate_hasLaw (Sum.inr k : MatrixCoordinates ι)).hasGaussianLaw.memLp_two
  change cov[(fun g => (goeMatrix r g*ᵥm) i)+(fun g => sqrt v*g (.inr i)),
    (fun g => (goeMatrix r g*ᵥm) l)+(fun g => sqrt v*g (.inr l));_]=_
  rw [covariance_add_left (hm i) ((hn i).const_mul _) ((hm l).add ((hn l).const_mul _)),
    covariance_add_right (hm i) (hm l) ((hn l).const_mul _),
    covariance_add_right ((hn i).const_mul _) (hm l) ((hn l).const_mul _)]
  have hback : cov[fun g => g (.inr i),fun g => (goeMatrix r g*ᵥm) l;
      gaussianCoordinates (MatrixCoordinates ι)]=0 := by
    rw [covariance_comm,goe_mulVec_noise_cov]
  rw [covariance_const_mul_right,goe_mulVec_noise_cov,mul_zero,add_zero,
    covariance_const_mul_left,hback,mul_zero,
    covariance_const_mul_left,covariance_const_mul_right,coordinate_covariance,
    goe_mulVec_cov hr]
  simp only [Sum.inr.injEq]
  by_cases hil : i=l
  · simp only [hil,ite_true,mul_one]
    rw [mul_self_sqrt hv]
    ring
  · simp only [hil,ite_false,mul_zero,zero_add,add_zero]
    ring

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_GOEBilinearCov
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma goe_entry_mulVec_cov {r : ℝ} (hr : 0 ≤ r) (v : ι → ℝ) (i k l : ι) :
    cov[fun g => goeMatrix r g i k,fun g => (goeMatrix r g*ᵥv) l;
      gaussianCoordinates (MatrixCoordinates ι)] =
      r*((if i=l then v k else 0)+(if k=l then v i else 0)) := by
  simpa only [goeObservation,sqrt_zero,zero_mul,add_zero] using
    goe_entry_observation_cov hr 0 v i k l

lemma goe_mulVec_cross_cov {r : ℝ} (hr : 0 ≤ r) (u v : ι → ℝ) (i l : ι) :
    cov[fun g => (goeMatrix r g*ᵥu) i,fun g => (goeMatrix r g*ᵥv) l;
      gaussianCoordinates (MatrixCoordinates ι)] =
    r*((if i=l then u⬝ᵥv else 0)+v i*u l) := by
  change cov[fun g => ∑ k,goeMatrix r g i k*u k,fun g => (goeMatrix r g*ᵥv) l;_]=_
  rw [covariance_fun_sum_left
    (fun k => (goe_matrix_gaussian (ι := ι) r).eval (i,k) |>.memLp_two.mul_const (u k))
    (goe_mulVec_memLp r v l)]
  simp only [covariance_mul_const_left,goe_entry_mulVec_cov hr]
  by_cases hil : i=l
  · subst l
    simp only [ite_true,mul_add,add_mul,Finset.sum_add_distrib]
    have hsum : (∑ k,r*v k*u k)=r*(u⬝ᵥv) := by
      simp only [dotProduct,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hsum]
    simp [mul_ite,ite_mul,mul_assoc]
  · simp [hil,mul_ite,ite_mul]
    ring

lemma goeBilinear_memLp (r : ℝ) (x y : ι → ℝ) :
    MemLp (goeBilinear r x y) 2 (gaussianCoordinates (MatrixCoordinates ι)) := by
  exact memLp_finsetSum _ (fun i _ => (goe_mulVec_memLp r y i).const_mul (x i))

lemma goe_bilinear_cov {r : ℝ} (hr : 0 ≤ r) (x y u v : ι → ℝ) :
    cov[goeBilinear r x y,goeBilinear r u v;gaussianCoordinates (MatrixCoordinates ι)] =
    r*((x⬝ᵥu)*(y⬝ᵥv)+(x⬝ᵥv)*(y⬝ᵥu)) := by
  change cov[fun g => ∑ i,x i*(goeMatrix r g*ᵥy) i,
    fun g => ∑ k,u k*(goeMatrix r g*ᵥv) k;_]=_
  rw [covariance_fun_sum_fun_sum (fun i => (goe_mulVec_memLp r y i).const_mul (x i))
    (fun k => (goe_mulVec_memLp r v k).const_mul (u k))]
  simp only [covariance_const_mul_left,covariance_const_mul_right,goe_mulVec_cross_cov hr]
  have hsum (i : ι) : (∑ k,u k*(x i*(r*((if i=k then y⬝ᵥv else 0)+v i*y k))))=
      r*((x i*u i)*(y⬝ᵥv)+(x i*v i)*(y⬝ᵥu)) := by
    simp only [mul_add,Finset.sum_add_distrib]
    have hf : (∑ k,u k*(x i*(r*(v i*y k))))=(r*(x i*v i))*(y⬝ᵥu) := by
      simp only [dotProduct,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hf]
    simp [mul_ite]
    ring
  simp_rw [hsum]
  simp only [mul_add,Finset.sum_add_distrib]
  have h1 : (∑ i,r*((x i*u i)*(y⬝ᵥv)))=r*((x⬝ᵥu)*(y⬝ᵥv)) := by
    rw [← Finset.mul_sum,← Finset.sum_mul]
    rfl
  have h2 : (∑ i,r*((x i*v i)*(y⬝ᵥu)))=r*((x⬝ᵥv)*(y⬝ᵥu)) := by
    rw [← Finset.mul_sum,← Finset.sum_mul]
    rfl
  rw [h1,h2]

end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma unitRow_dot {u : ι → ℝ} (hu : u⬝ᵥu=1) (κ : ℝ) (i : ι) :
    unitRow κ u i⬝ᵥu=κ*u i := by
  simp only [unitRow,add_dotProduct,single_one_dotProduct,smul_dotProduct,hu,smul_eq_mul,mul_one]
  ring

lemma unitRow_dot_unitRow {u : ι → ℝ} (hu : u⬝ᵥu=1) (κ : ℝ) (i l : ι) :
    unitRow κ u i⬝ᵥunitRow κ u l=(if i=l then 1 else 0)+(κ^2-1)*u i*u l := by
  simp only [unitRow,add_dotProduct,dotProduct_add,smul_dotProduct,dotProduct_smul,
    single_one_dotProduct,dotProduct_single_one,hu,smul_eq_mul,mul_one]
  by_cases hil : i=l <;> simp [hil] <;> ring

lemma goeBlockResidual_cov {r : ℝ} (hr : 0 ≤ r) {u : ι → ℝ} (hu : u⬝ᵥu=1)
    (κ ell : ℝ) (i k l a : ι) :
    cov[fun g => goeBlockResidual r κ ell u g i k,
      fun g => goeBlockResidual r κ ell u g l a;gaussianCoordinates (MatrixCoordinates ι)] =
    r*((if i=l then 1 else 0)*(if k=a then 1 else 0)+(if i=a then 1 else 0)*(if k=l then 1 else 0))+
    r*(κ^2-1)*((if i=l then 1 else 0)*u k*u a+(if k=a then 1 else 0)*u i*u l+
      (if i=a then 1 else 0)*u k*u l+(if k=l then 1 else 0)*u i*u a)+
    2*r*(ell^2-2*κ^2+1)*u i*u k*u l*u a := by
  have hB (i k : ι) := goeBilinear_memLp r (unitRow κ u i) (unitRow κ u k)
  have hU := goeBilinear_memLp r u u
  change cov[goeBilinear r (unitRow κ u i) (unitRow κ u k)+
    (fun g => ((ell-κ^2)*u i*u k)*goeBilinear r u u g),
    goeBilinear r (unitRow κ u l) (unitRow κ u a)+
    (fun g => ((ell-κ^2)*u l*u a)*goeBilinear r u u g);_]=_
  rw [covariance_add_left (hB i k) (hU.const_mul _) ((hB l a).add (hU.const_mul _)),
    covariance_add_right (hB i k) (hB l a) (hU.const_mul _),
    covariance_add_right (hU.const_mul _) (hB l a) (hU.const_mul _)]
  simp only [covariance_const_mul_left,covariance_const_mul_right,goe_bilinear_cov hr,
    unitRow_dot_unitRow hu,unitRow_dot hu,hu]
  have hUT (q : ι) : u⬝ᵥunitRow κ u q=κ*u q := by rw [dotProduct_comm,unitRow_dot hu]
  simp only [hUT]
  ring

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ScalarFixedPointJoined
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal

namespace SKGap
open Filter
open scoped Topology

lemma gaussianF_zero : gaussianF 0 = 0 := by simp [gaussianF, gaussianAverage]

end SKGap

namespace SKGap
open Filter
open scoped Topology

lemma gaussianF_le_self {s : ℝ} (hs : 0 ≤ s) : gaussianF s ≤ s := by
  have h := gaussianF_lipschitz.dist_le_mul s hs 0 (by simp)
  rw [gaussianF_zero, dist_zero_right, NNReal.coe_one, one_mul, dist_zero_right,
    Real.norm_eq_abs, abs_of_nonneg (gaussianF_nonneg hs), Real.norm_eq_abs, abs_of_nonneg hs] at h
  exact h

end SKGap

namespace SKGap

lemma gaussianF_pos {s : ℝ} (hs : 0 < s) : 0 < gaussianF s := by
  rw [gaussianF_eq_square hs.le, gaussianAverage_eq_integral (by fun_prop) s hs.le]
  have hv : s.toNNReal ≠ 0 := by exact_mod_cast (show 0 < s.toNNReal from Real.toNNReal_pos.mpr hs).ne'
  have := nullSingletonClass_gaussianReal (μ := s) hv
  have hsupp : Function.support (fun y : ℝ => tanh y ^ 2) = ({0} : Set ℝ)ᶜ := by
    ext y
    simp only [Function.mem_support, mem_compl_iff, mem_singleton_iff, ne_eq, sq_eq_zero_iff]
    have he : tanh y = 0 ↔ y = 0 := by
      simpa only [tanh_zero] using (show tanh y = tanh 0 ↔ y = 0 from tanh_injective.eq_iff)
    exact not_congr he
  rw [integral_pos_iff_support_of_nonneg (fun y => sq_nonneg (tanh y)) integrable_tanh_sq,
    hsupp, measure_compl (measurableSet_singleton 0) (by simp)]
  simp

lemma scalarFixedPoint_spec {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t) :
    0 ≤ scalarFixedPoint j t ∧ scalarFixedPoint j t = t+j*gaussianF (scalarFixedPoint j t) := by
  simp only [scalarFixedPoint, dite_eq_left (show 0 < j ∧ j < 1 ∧ 0 ≤ t from ⟨hj, hj1, ht⟩)]
  exact (exists_gaussian_fixed hj hj1 ht).choose_spec.1

lemma scalarFixedPoint_bounds {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t) :
    t ≤ scalarFixedPoint j t ∧ scalarFixedPoint j t ≤ t/(1-j) := by
  obtain ⟨hs, he⟩ := scalarFixedPoint_spec hj hj1 ht
  constructor
  · nlinarith [gaussianF_nonneg hs]
  · apply (le_div_iff₀ (by linarith : 0 < 1-j)).mpr
    nlinarith [gaussianF_le_self hs]

lemma scalarQ_spec {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t) :
    scalarQ j t = (∫ y, tanh y^2 ∂gaussianReal (scalarFixedPoint j t) (scalarFixedPoint j t).toNNReal) ∧
      scalarQ j t = (scalarFixedPoint j t-t)/j ∧ scalarQ j t ≤ t/(1-j) := by
  obtain ⟨hs, he⟩ := scalarFixedPoint_spec hj hj1 ht
  refine ⟨?_, ?_, ?_⟩
  · exact (gaussianF_eq_square hs).trans (gaussianAverage_eq_integral (by fun_prop) _ hs)
  · dsimp [scalarQ]; apply (eq_div_iff hj.ne').mpr; nlinarith
  · exact (gaussianF_le_self hs).trans (scalarFixedPoint_bounds hj hj1 ht).2

lemma scalar_fixed_pos {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 < t) :
    0 < scalarFixedPoint j t ∧ 0 < scalarQ j t := by
  have hs := ht.trans_le (scalarFixedPoint_bounds hj hj1 ht.le).1
  exact ⟨hs, gaussianF_pos hs⟩

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_EqualityCurve
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal

lemma scalarQMoment_curve {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t) :
    scalarQMoment (scalarCurve j t)=scalarQ j t := (scalarQ_spec hj hj1 ht).1.symm

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RankCovariance
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma rankOneCovarianceInverse_mul (s r : ℝ) (m : ι → ℝ)
    (hs : s ≠ 0) (hS : s+r*(m⬝ᵥm) ≠ 0) :
    rankOneCovarianceInverse s r m * rankOneCovariance s r m=1 := by
  simp only [rankOneCovarianceInverse,rankOneCovariance,Matrix.sub_mul,Matrix.mul_add,
    Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,Matrix.mul_one,
    Matrix.vecMulVec_mul_vecMulVec]
  ext i k
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.vecMulVec_apply,Pi.smul_apply]
  field_simp [hs,hS]
  ring

lemma rankOneCovarianceInverse_mulVec (s r : ℝ) (m y : ι → ℝ) (i : ι) :
    (rankOneCovarianceInverse s r m*ᵥy) i =
      s⁻¹*y i-r/(s*(s+r*(m⬝ᵥm)))*(m⬝ᵥy)*m i := by
  simp only [rankOneCovarianceInverse,Matrix.sub_mulVec,Matrix.smul_mulVec,
    Matrix.one_mulVec,Matrix.vecMulVec_mulVec,Pi.sub_apply,Pi.smul_apply,
    smul_eq_mul,op_smul_eq_smul]
  ring

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_GOERegression
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma goeCrossCovariance_mulVec (r : ℝ) (m y : ι → ℝ) (i k : ι) :
    (goeCrossCovariance r m*ᵥy) (i,k)=r*(m k*y i+m i*y k) := by
  simp [goeCrossCovariance,mulVec,dotProduct,add_mul,mul_add,Finset.sum_add_distrib,
    mul_assoc]

lemma goeRegressionCoefficient_mulVec (r v : ℝ) (m y : ι → ℝ) (i k : ι) :
    (goeRegressionCoefficient r v m*ᵥy) (i,k) =
      r/(r*(m⬝ᵥm)+v)*(m k*y i+m i*y k)-
      (2*r^2/((r*(m⬝ᵥm)+v)*(v+2*r*(m⬝ᵥm))))*(m⬝ᵥy)*m i*m k := by
  rw [goeRegressionCoefficient,← Matrix.mulVec_mulVec,goeCrossCovariance_mulVec]
  simp only [rankOneCovarianceInverse_mulVec]
  have hden : r*(m⬝ᵥm)+v+r*(m⬝ᵥm)=v+2*r*(m⬝ᵥm) := by ring
  rw [hden]
  ring

lemma goe_observation_cov_matrix {r v : ℝ} (hr : 0 ≤ r) (hv : 0 ≤ v) (m : ι → ℝ) :
    (fun i l => cov[fun g => goeObservation r v m g i,fun g => goeObservation r v m g l;
      gaussianCoordinates (MatrixCoordinates ι)])=rankOneCovariance (r*(m⬝ᵥm)+v) r m := by
  ext i l
  rw [goe_observation_cov hr hv]
  simp only [rankOneCovariance,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,Matrix.vecMulVec_apply,dotProduct,← pow_two]
  ring

lemma goe_regression_covariance {r v : ℝ} (hr : 0 ≤ r) (hv : 0 < v) (m : ι → ℝ)
    (p : ι × ι) (l : ι) :
    cov[fun g => goeMatrix r g p.1 p.2,fun g => goeObservation r v m g l;
      gaussianCoordinates (MatrixCoordinates ι)] =
    ∑ k, goeRegressionCoefficient r v m p k *
      cov[fun g => goeObservation r v m g k,fun g => goeObservation r v m g l;
        gaussianCoordinates (MatrixCoordinates ι)] := by
  have hq : 0 ≤ m⬝ᵥm := Finset.sum_nonneg (fun k _ => mul_self_nonneg (m k))
  have hs : 0 < r*(m⬝ᵥm)+v := add_pos_of_nonneg_of_pos (mul_nonneg hr hq) hv
  have hS : 0 < r*(m⬝ᵥm)+v+r*(m⬝ᵥm) := add_pos_of_pos_of_nonneg hs (mul_nonneg hr hq)
  have hmat := goe_observation_cov_matrix hr hv.le m
  rw [goe_entry_observation_cov hr]
  change goeCrossCovariance r m p l =
    (goeRegressionCoefficient r v m * (show Matrix ι ι ℝ from fun k l => cov[fun g => goeObservation r v m g k,
      fun g => goeObservation r v m g l;gaussianCoordinates (MatrixCoordinates ι)])) p l
  rw [hmat,goeRegressionCoefficient,Matrix.mul_assoc,
    rankOneCovarianceInverse_mul _ _ _ hs.ne' hS.ne',Matrix.mul_one]

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_GOEBlockExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem goeRegressionCoefficient_block_mean {r v c : ℝ} (hr : 0 ≤ r) (hv : 0 < v)
    {u : ι → ℝ} (hu : u⬝ᵥu=1) (z : ι → ℝ) :
    (fun i k => (goeRegressionCoefficient r v (c • u)*ᵥz) (i,k))=
      vecMulVec u ((r*c/(r*c^2+v)) • (z-(u⬝ᵥz) • u))+
      vecMulVec ((r*c/(r*c^2+v)) • (z-(u⬝ᵥz) • u)) u+
      (2*r*c/(v+2*r*c^2)*(u⬝ᵥz)) • vecMulVec u u := by
  have hs : r*c^2+v ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos (mul_nonneg hr (sq_nonneg c)) hv)
  have hS : v+2*r*c^2 ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hv (by positivity))
  ext i k
  change (goeRegressionCoefficient r v (c • u)*ᵥz) (i,k)=
    u i*(r*c/(r*c^2+v)*(z k-(u⬝ᵥz)*u k))+
    (r*c/(r*c^2+v)*(z i-(u⬝ᵥz)*u i))*u k+
    (2*r*c/(v+2*r*c^2)*(u⬝ᵥz))*(u i*u k)
  rw [goeRegressionCoefficient_mulVec]
  simp only [smul_dotProduct,dotProduct_smul,smul_eq_mul,hu,mul_one,Pi.smul_apply]
  have hcc : c*c=c^2 := by ring
  rw [hcc]
  field_simp
  ring

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_EmpiricalConditionalData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius

lemma empiricalUnit_unit {n : ℕ} [NeZero n] (y : Fin n → ℝ)
    (hq : 0 < scalarQMoment (empiricalLaw y)) :
    (empiricalUnit y (scalarQMoment (empiricalLaw y))).ofLp⬝ᵥ
      (empiricalUnit y (scalarQMoment (empiricalLaw y))).ofLp=1 := by
  have hn : 0 < (n:ℝ) := by exact_mod_cast NeZero.pos n
  have hsum : ∑ i,tanh (y i)^2=(n:ℝ)*scalarQMoment (empiricalLaw y) := by
    simpa only [scalarQMoment,Fintype.card_fin] using (card_mul_integral_empiricalLaw y (fun x=>tanh x^2)).symm
  simp only [empiricalUnit,WithLp.ofLp_toLp,dotProduct,← sq,div_pow,Real.sq_sqrt (mul_nonneg hn.le hq.le)]
  rw [← Finset.sum_div,hsum,div_self (mul_pos hn hq).ne']

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Posterior_ConditionalObservationData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma scalarA_empirical_sum {n : ℕ} [NeZero n] (j t σ : ℝ) (y : Fin n → ℝ) :
    ∑ i,tanh (y i)*(y i-scalarD j (empiricalLaw y,t,σ))=
      (n:ℝ)*scalarA j (empiricalLaw y,t,σ) := by
  simp only [scalarA,scalarM,integral_empiricalLaw,Fintype.card_fin]
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [mul_sub,← mul_assoc,mul_inv_cancel₀ hn,one_mul]
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _; ring
  · rw [← Finset.sum_mul]
    field_simp

lemma empirical_unit_scale {n : ℕ} [NeZero n] (y : Fin n → ℝ) {q : ℝ} (hq : 0 < q) :
    sqrt ((n:ℝ)*q) • (empiricalUnit y q).ofLp=(fun i=>tanh (y i)) := by
  have hc : sqrt ((n:ℝ)*q) ≠ 0 := ne_of_gt (sqrt_pos.mpr (mul_pos (by exact_mod_cast NeZero.pos n) hq))
  ext i
  simp only [empiricalUnit,WithLp.ofLp_toLp,Pi.smul_apply,smul_eq_mul]
  field_simp

lemma empirical_Z_formula {n : ℕ} [NeZero n] (y : Fin n → ℝ) (d : ℝ) {s : ℝ} (hs : 0 < s) :
    sqrt s • (empiricalGramColumns y d s 2).ofLp=(fun i=>(y i-d)/(sqrt (n:ℝ)*sqrt s)) := by
  have hn : sqrt (n:ℝ) ≠ 0 := ne_of_gt (sqrt_pos.mpr (by exact_mod_cast NeZero.pos n))
  have hss : sqrt s ≠ 0 := (sqrt_pos.mpr hs).ne'
  ext i
  simp only [empiricalGramColumns,gramCoordinates,Matrix.cons_val,Pi.smul_apply,
    WithLp.ofLp_toLp,smul_eq_mul]
  field_simp
  rw [Real.sq_sqrt hs.le]
  ring

lemma empirical_unit_center_dot {n : ℕ} [NeZero n] (j t σ : ℝ) (y : Fin n → ℝ) :
    (empiricalUnit y (scalarQMoment (empiricalLaw y))).ofLp⬝ᵥ
      (fun i=>y i-scalarD j (empiricalLaw y,t,σ))=
    (n:ℝ)*scalarA j (empiricalLaw y,t,σ)/sqrt ((n:ℝ)*scalarQMoment (empiricalLaw y)) := by
  simp only [empiricalUnit,WithLp.ofLp_toLp,dotProduct,div_mul_eq_mul_div,← Finset.sum_div]
  rw [scalarA_empirical_sum]

lemma empirical_unit_observation_dot {n : ℕ} [NeZero n] (j t σ B : ℝ)
    (y : Fin n → ℝ) (hq : 0 < scalarQMoment (empiricalLaw y)) :
    (empiricalUnit y (scalarQMoment (empiricalLaw y))).ofLp⬝ᵥ
      (fun i=>y i-scalarD j (empiricalLaw y,t,σ)+B*tanh (y i))=
    (n:ℝ)*(scalarA j (empiricalLaw y,t,σ)+B*scalarQMoment (empiricalLaw y))/
      sqrt ((n:ℝ)*scalarQMoment (empiricalLaw y)) := by
  let q := scalarQMoment (empiricalLaw y)
  let u := (empiricalUnit y q).ofLp
  let c := sqrt ((n:ℝ)*q)
  have hc : c ≠ 0 := ne_of_gt (sqrt_pos.mpr (mul_pos (by exact_mod_cast NeZero.pos n) hq))
  have hc2 : c^2=(n:ℝ)*q := sq_sqrt (mul_nonneg (Nat.cast_nonneg n) hq.le)
  have hu : u⬝ᵥu=1 := empiricalUnit_unit y hq
  have hscale : c • u=(fun i=>tanh (y i)) := empirical_unit_scale y hq
  have heq : (fun i=>y i-scalarD j (empiricalLaw y,t,σ)+B*tanh (y i))=
      (fun i=>y i-scalarD j (empiricalLaw y,t,σ))+B • (c • u) := by
    rw [hscale]; rfl
  rw [heq,dotProduct_add,dotProduct_smul,dotProduct_smul,hu,empirical_unit_center_dot]
  simp only [smul_eq_mul,mul_one]
  change (n:ℝ)*scalarA j (empiricalLaw y,t,σ)/c+B*c=(n:ℝ)*(scalarA j (empiricalLaw y,t,σ)+B*q)/c
  field_simp
  linear_combination B*hc2
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_GOEResidualCov
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma goe_cross_row_dot (r : ℝ) (m : ι → ℝ) (l a : ι) :
    m⬝ᵥ(fun b => goeCrossCovariance r m (l,a) b)=2*r*m l*m a := by
  simp only [dotProduct,goeCrossCovariance,mul_add,Finset.sum_add_distrib]
  simp [mul_ite,mul_assoc]
  ring

lemma goeRegressionResidual_cov {r v : ℝ} (hr : 0 ≤ r) (hv : 0 < v)
    (m : ι → ℝ) (i k l a : ι) :
    cov[fun g => goeRegressionResidual r v m g (i,k),
      fun g => goeRegressionResidual r v m g (l,a);gaussianCoordinates (MatrixCoordinates ι)] =
    r*((if i=l then 1 else 0)*(if k=a then 1 else 0)+(if i=a then 1 else 0)*(if k=l then 1 else 0))-
    r^2/(r*(m⬝ᵥm)+v)*((if i=l then 1 else 0)*m k*m a+(if k=a then 1 else 0)*m i*m l+
      (if i=a then 1 else 0)*m k*m l+(if k=l then 1 else 0)*m i*m a)+
    4*r^3/((r*(m⬝ᵥm)+v)*(v+2*r*(m⬝ᵥm)))*m i*m k*m l*m a := by
  unfold goeRegressionResidual
  rw [GaussianRegression.residual_covariance
    (goe_observation_joint_gaussian r v m) (goeRegressionCoefficient r v m)
    (goe_regression_covariance hr hv m)]
  have hc (b : ι) : cov[fun g => goeObservation r v m g b,
      fun g => goeMatrix r g l a;gaussianCoordinates (MatrixCoordinates ι)] =
      goeCrossCovariance r m (l,a) b := by
    rw [covariance_comm,goe_entry_observation_cov hr]
    rfl
  simp only [hc]
  change cov[fun g => goeMatrix r g i k,fun g => goeMatrix r g l a;_] -
    (goeRegressionCoefficient r v m*ᵥ(fun b => goeCrossCovariance r m (l,a) b)) (i,k)=_
  rw [goe_entry_cov hr,goeRegressionCoefficient_mulVec,goe_cross_row_dot]
  have he (p q : ι) (x : ℝ) : (if p=q then x else 0)=(if q=p then 1 else 0)*x := by
    by_cases hpq : p=q <;> simp [hpq,Ne.symm]
  simp only [goeCrossCovariance]
  rw [he l i (m a),he a i (m l),he l k (m a),he a k (m l)]
  ring

lemma goeRegressionResidual_gaussian (r v : ℝ) (m : ι → ℝ) :
    HasGaussianLaw (goeRegressionResidual r v m) (gaussianCoordinates (MatrixCoordinates ι)) :=
  (GaussianRegression.residual_joint_gaussian (goe_observation_joint_gaussian r v m)
    (goeRegressionCoefficient r v m)).fst

lemma goeRegressionResidual_mean (r v : ℝ) (m : ι → ℝ) (p : ι × ι) :
    (∫ g, goeRegressionResidual r v m g p ∂gaussianCoordinates (MatrixCoordinates ι))=0 := by
  exact GaussianRegression.residual_mean_zero (goe_observation_joint_gaussian r v m)
    (goeRegressionCoefficient r v m) (fun p => goe_mean_zero r p.1 p.2)
    (goe_observation_mean r v m) p

end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma blockCoefficient_sample (r κ ell : ℝ) (u : ι → ℝ) (g : MatrixCoordinates ι → ℝ) :
    blockCoefficient κ ell u*ᵥ(fun p => goeMatrix r g p.1 p.2)=
      fun p => goeBlockResidual r κ ell u g p.1 p.2 := by
  ext p
  simp only [mulVec,dotProduct,blockCoefficient,goeBlockResidual,goeBilinear,
    Fintype.sum_prod_type,add_mul,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro k _ <;> ring

lemma goeBlockResidual_gaussian (r κ ell : ℝ) (u : ι → ℝ) :
    HasGaussianLaw (fun g (p : ι × ι) => goeBlockResidual r κ ell u g p.1 p.2)
      (gaussianCoordinates (MatrixCoordinates ι)) := by
  exact ((goe_matrix_gaussian (ι := ι) r).map_fun
    (GaussianRegression.matrixCLM (blockCoefficient κ ell u))).congr
      (Filter.Eventually.of_forall (blockCoefficient_sample r κ ell u))

lemma goeBlockResidual_mean (r κ ell : ℝ) (u : ι → ℝ) (p : ι × ι) :
    (∫ g, goeBlockResidual r κ ell u g p.1 p.2 ∂gaussianCoordinates (MatrixCoordinates ι))=0 := by
  have he (g : MatrixCoordinates ι → ℝ) : goeBlockResidual r κ ell u g p.1 p.2=
      (blockCoefficient κ ell u*ᵥ(fun q => goeMatrix r g q.1 q.2)) p :=
    (congrFun (blockCoefficient_sample r κ ell u g) p).symm
  simp only [he,mulVec,dotProduct]
  rw [integral_finsetSum _ (fun q _ => ((goe_matrix_gaussian r).eval q).integrable.const_mul _)]
  simp only [integral_const_mul,goe_mean_zero,mul_zero,Finset.sum_const_zero]

lemma block_regression_cov_algebra {r v c : ℝ} (hr : 0 ≤ r) (hv : 0 < v)
    {u : ι → ℝ} (hu : u⬝ᵥu=1) (i k l a : ι) :
    cov[fun g => goeRegressionResidual r v (c • u) g (i,k),
      fun g => goeRegressionResidual r v (c • u) g (l,a);gaussianCoordinates (MatrixCoordinates ι)] =
    cov[fun g => goeBlockResidual r (sqrt (v/(r*c^2+v))) (sqrt (v/(v+2*r*c^2))) u g i k,
      fun g => goeBlockResidual r (sqrt (v/(r*c^2+v))) (sqrt (v/(v+2*r*c^2))) u g l a;
      gaussianCoordinates (MatrixCoordinates ι)] := by
  have hs : 0 < r*c^2+v := add_pos_of_nonneg_of_pos (mul_nonneg hr (sq_nonneg c)) hv
  have hS : 0 < v+2*r*c^2 := add_pos_of_pos_of_nonneg hv (by positivity)
  rw [goeRegressionResidual_cov hr hv,goeBlockResidual_cov hr hu]
  simp only [smul_dotProduct,dotProduct_smul,smul_eq_mul,hu,mul_one,Pi.smul_apply]
  have hq : c*c=c^2 := by ring
  rw [hq,sq_sqrt (div_nonneg hv.le hs.le),sq_sqrt (div_nonneg hv.le hS.le)]
  field_simp
  ring

theorem goe_regression_residual_law {r v c : ℝ} (hr : 0 ≤ r) (hv : 0 < v)
    {u : ι → ℝ} (hu : u⬝ᵥu=1) :
    (gaussianCoordinates (MatrixCoordinates ι)).map (goeRegressionResidual r v (c • u))=
    (gaussianCoordinates (MatrixCoordinates ι)).map (fun g p =>
      goeBlockResidual r (sqrt (v/(r*c^2+v))) (sqrt (v/(v+2*r*c^2))) u g p.1 p.2) := by
  apply GaussianRegression.law_eq_of_mean_covariance (goeRegressionResidual_gaussian r v (c • u))
    (goeBlockResidual_gaussian r _ _ u)
  · intro p
    rw [goeRegressionResidual_mean,goeBlockResidual_mean]
  · intro p q
    exact block_regression_cov_algebra hr hv hu p.1 p.2 q.1 q.2

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Posterior_GOEPointwisePosterior
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.conditionalGoeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real GaussianDensity GaussianRegression
open scoped BigOperators ENNReal NNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in

theorem conditionalGoeLaw_block {r v c : ℝ} (hr : 0 ≤ r) (hv : 0 < v)
    {u : ι → ℝ} (hu : u⬝ᵥu=1) (z : ι → ℝ) :
    conditionalGoeLaw r v (c • u) z =
      (gaussianCoordinates (MatrixCoordinates ι)).map (fun g p =>
        goeBlockResidual r (sqrt (v/(r*c^2+v))) (sqrt (v/(v+2*r*c^2))) u g p.1 p.2+
        (goeRegressionCoefficient r v (c • u)*ᵥz) p) := by
  rw [conditionalGoeLaw,goe_regression_residual_law hr hv hu,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (goeBlockResidual_gaussian r _ _ u).aemeasurable]
  rfl

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ConditionalMeanScalar
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real
lemma conditional_perp_mean_scalar {N q s : ℝ} (hN : 0 < N) (hq : 0 < q) (hs : 0 < s)
    (j a B w u : ℝ) :
    (j/N*sqrt (N*q)/s)*(w+B*sqrt (N*q)*u-(N*(a+B*q)/sqrt (N*q))*u)=
      j*sqrt (q/s)*(w/(sqrt N*sqrt s))-j*a/s*u := by
  have hn := (sqrt_pos.mpr hN).ne'
  have hq' := (sqrt_pos.mpr hq).ne'
  have hs' := (sqrt_pos.mpr hs).ne'
  rw [sqrt_mul hN.le,sqrt_div hq.le]
  field_simp
  ring_nf
  simp only [sq_sqrt hN.le,sq_sqrt hq.le,sq_sqrt hs.le]
  have hcube : sqrt N^3=N*sqrt N := by
    linear_combination sqrt N*(sq_sqrt hN.le)
  rw [hcube]
  ring

lemma conditional_parallel_mean_scalar {N q S : ℝ} (hN : 0 < N) (hq : 0 < q)
    (j a B : ℝ) :
    (2*(j/N)*sqrt (N*q)/S)*((N*(a+B*q))/sqrt (N*q))=2*j*(a+B*q)/S := by
  have hc : sqrt (N*q) ≠ 0 := (sqrt_pos.mpr (mul_pos hN hq)).ne'
  by_cases hS : S=0
  · simp [hS]
  · field_simp

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ConditionalEmpiricalLaw
attribute [-instance] _root_.OAI.SKGap.conditionalGoeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma empirical_observation_covariance {n : ℕ} [NeZero n] (j t σ : ℝ) (y : Fin n → ℝ)
    (hq : 0 ≤ scalarQMoment (empiricalLaw y)) :
    (j/(n:ℝ))*sqrt ((n:ℝ)*scalarQMoment (empiricalLaw y))^2+(t+σ^2)=
      scalarS j (empiricalLaw y,t,σ) ∧
    (t+σ^2)+2*(j/(n:ℝ))*sqrt ((n:ℝ)*scalarQMoment (empiricalLaw y))^2=
      scalarS j (empiricalLaw y,t,σ)+j*scalarQMoment (empiricalLaw y) := by
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [sq_sqrt (mul_nonneg (Nat.cast_nonneg n) hq)]
  dsimp [scalarS]
  constructor <;> field_simp <;> ring

lemma empirical_conditional_mean {n : ℕ} [NeZero n] {j t σ : ℝ}
    (hj : 0 ≤ j) (ht : 0 < t) (y : Fin n → ℝ)
    (hq : 0 < scalarQMoment (empiricalLaw y)) :
    let p : ScalarPoint := (empiricalLaw y,t,σ)
    let q := scalarQMoment p.1
    let s := scalarS j p
    let u := (empiricalUnit y q).ofLp
    let Z := sqrt s • (empiricalGramColumns y (scalarD j p) s 2).ofLp
    (fun i k=>(goeRegressionCoefficient (j/(n:ℝ)) (t+σ^2) (fun l=>tanh (y l))*ᵥ
      empiricalObservation j t σ y) (i,k))=
      vecMulVec u ((j*sqrt (q/s)) • Z-(j*scalarA j p/s) • u)+
      vecMulVec ((j*sqrt (q/s)) • Z-(j*scalarA j p/s) • u) u+
      (2*j*(scalarA j p+j*scalarBMoment p.1*q)/(s+j*q)) • vecMulVec u u := by
  dsimp only
  let p : ScalarPoint := (empiricalLaw y,t,σ)
  let q := scalarQMoment p.1
  let s := scalarS j p
  let B := j*scalarBMoment p.1
  let c := sqrt ((n:ℝ)*q)
  let u := (empiricalUnit y q).ofLp
  let Z := sqrt s • (empiricalGramColumns y (scalarD j p) s 2).ofLp
  have hn : 0 < (n:ℝ) := by exact_mod_cast NeZero.pos n
  have hv : 0 < t+σ^2 := add_pos_of_pos_of_nonneg ht (sq_nonneg _)
  have hs : 0 < s := add_pos_of_pos_of_nonneg hv (mul_nonneg hj hq.le)
  have hu : u⬝ᵥu=1 := empiricalUnit_unit y hq
  have hscale : c • u=(fun i=>tanh (y i)) := empirical_unit_scale y hq
  have hc := empirical_observation_covariance j t σ y hq.le
  have hdot : u⬝ᵥempiricalObservation j t σ y=(n:ℝ)*(scalarA j p+B*q)/c :=
    empirical_unit_observation_dot j t σ B y hq
  have hmean := goeRegressionCoefficient_block_mean (c := c) (div_nonneg hj hn.le) hv hu
    (empiricalObservation j t σ y)
  rw [hscale] at hmean
  rw [hc.1,hc.2,hdot] at hmean
  have hperp : ((j/(n:ℝ))*c/s) • (empiricalObservation j t σ y-
      ((n:ℝ)*(scalarA j p+B*q)/c) • u)=
      (j*sqrt (q/s)) • Z-(j*scalarA j p/s) • u := by
    ext i
    have hzi := congrFun (empirical_Z_formula y (scalarD j p) hs) i
    change Z i=(y i-scalarD j p)/(sqrt (n:ℝ)*sqrt s) at hzi
    have hmi := congrFun hscale i
    change c*u i=tanh (y i) at hmi
    change (j/(n:ℝ)*c/s)*(y i-scalarD j p+B*tanh (y i)-
      ((n:ℝ)*(scalarA j p+B*q)/c)*u i)=
      j*sqrt (q/s)*Z i-j*scalarA j p/s*u i
    rw [← hmi,hzi]
    convert conditional_perp_mean_scalar hn hq hs j (scalarA j p) B
      (y i-scalarD j p) (u i) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  rw [hperp] at hmean
  have hparallel := conditional_parallel_mean_scalar (S := s+j*q) hn hq j (scalarA j p) B
  rw [hparallel] at hmean
  exact hmean

theorem empirical_conditional_law {n : ℕ} [NeZero n] {j t σ : ℝ}
    (hj : 0 ≤ j) (ht : 0 < t) (y : Fin n → ℝ)
    (hq : 0 < scalarQMoment (empiricalLaw y)) :
    conditionalGoeLaw (j/(n:ℝ)) (t+σ^2) (fun i=>tanh (y i)) (empiricalObservation j t σ y)=
      (gaussianCoordinates (MatrixCoordinates (Fin n))).map
        (fun g p=>empiricalConditionalGoe j t σ y g p.1 p.2) := by
  let q := scalarQMoment (empiricalLaw y)
  have hn : 0 < (n:ℝ) := by exact_mod_cast NeZero.pos n
  have hv : 0 < t+σ^2 := add_pos_of_pos_of_nonneg ht (sq_nonneg _)
  have hh := conditionalGoeLaw_block (c := sqrt ((n:ℝ)*q)) (div_nonneg hj hn.le) hv
    (empiricalUnit_unit y hq) (empiricalObservation j t σ y)
  rw [empirical_unit_scale y hq] at hh
  rw [(empirical_observation_covariance j t σ y hq.le).1,
    (empirical_observation_covariance j t σ y hq.le).2] at hh
  rw [hh]
  congr 1
  funext g p
  have hmean := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ=>M p.1 p.2)
    (empirical_conditional_mean (σ := σ) hj ht y hq)
  change _+_=empiricalConditionalGoe j t σ y g p.1 p.2
  dsimp only [empiricalConditionalGoe,conditionalBlockMatrix]
  dsimp only at hmean
  rw [hmean]
  simp only [Matrix.add_apply,conditionalKappa,conditionalEll]
  ring
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ConditionalHessianLaw
attribute [-instance] _root_.OAI.SKGap.conditionalGoeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma scalarQMoment_empirical_overlap {n : ℕ} [NeZero n] (y : Fin n → ℝ) :
    scalarQMoment (empiricalLaw y)=overlap y := by
  simp only [scalarQMoment,integral_empiricalLaw,Fintype.card_fin,overlap,magnetization,
    div_eq_mul_inv,mul_comm]

lemma empirical_columns_zero_outer {n : ℕ} [NeZero n] (y : Fin n → ℝ) (d s j : ℝ) :
    j • vecMulVec (empiricalGramColumns y d s 0).ofLp (empiricalGramColumns y d s 0).ofLp=
      (j/(n:ℝ)) • vecMulVec (fun _=>1) (fun _=>1) := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hn : sqrt (n:ℝ) ≠ 0 := (sqrt_pos.mpr (by exact_mod_cast NeZero.pos n)).ne'
  ext i k
  simp only [empiricalGramColumns,gramCoordinates,Matrix.cons_val,WithLp.ofLp_toLp,
    Matrix.smul_apply,smul_eq_mul,vecMulVec_apply,mul_one]
  field_simp
  rw [Real.sq_sqrt (Nat.cast_nonneg n)]

lemma empirical_unit_outer {n : ℕ} [NeZero n] (y : Fin n → ℝ) {q : ℝ} (hq : 0 < q) (j : ℝ) :
    (2*j*q) • vecMulVec (empiricalUnit y q).ofLp (empiricalUnit y q).ofLp=
      (2*j/(n:ℝ)) • vecMulVec (magnetization y) (magnetization y) := by
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hc : sqrt ((n:ℝ)*q) ≠ 0 := (sqrt_pos.mpr (mul_pos (by exact_mod_cast NeZero.pos n) hq)).ne'
  ext i k
  simp only [empiricalUnit,WithLp.ofLp_toLp,Matrix.smul_apply,smul_eq_mul,vecMulVec_apply,magnetization]
  field_simp
  rw [Real.sq_sqrt (mul_nonneg hq.le (Nat.cast_nonneg n))]
  ring

lemma empiricalConditionalMiddle_literal {n : ℕ} [NeZero n] (j t σ : ℝ) (y : Fin n → ℝ)
    (hq : 0 < scalarQMoment (empiricalLaw y)) (g : MatrixCoordinates (Fin n) → ℝ) :
    empiricalConditionalMiddle j t σ y g=
      plantedInteraction j (empiricalConditionalGoe j t σ y g)+
      (2*j/(n:ℝ)) • vecMulVec (magnetization y) (magnetization y)-
      onsager j y • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  dsimp only [empiricalConditionalMiddle,empiricalConditionalGoe,plantedInteraction]
  rw [empirical_columns_zero_outer,empirical_unit_outer y hq,
    scalarBMoment,scalarQMoment_empirical_overlap]
  rfl

lemma fieldHessian_diagonalHessian {n : ℕ} (j : ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
    (y a : Fin n → ℝ) :
    fieldHessian j (plantedInteraction j W) y a = diagonalHessian a
      (plantedInteraction j W+(2*j/(n:ℝ)) • vecMulVec (magnetization y) (magnetization y)-
        onsager j y • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  ext i k
  simp only [fieldHessian,hessianCore,diagonalHessian,diagonalRoot,Matrix.sub_apply,
    Matrix.one_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.add_apply,
    Matrix.smul_apply,smul_eq_mul,vecMulVec_apply]
  ring

lemma empiricalConditionalGoe_hessian {n : ℕ} [NeZero n] (j t σ : ℝ) (y a : Fin n → ℝ)
    (hq : 0 < scalarQMoment (empiricalLaw y)) (g : MatrixCoordinates (Fin n) → ℝ) :
    fieldHessian j (plantedInteraction j (empiricalConditionalGoe j t σ y g)) y a=
      diagonalHessian a (empiricalConditionalMiddle j t σ y g) := by
  rw [empiricalConditionalMiddle_literal j t σ y hq g,fieldHessian_diagonalHessian]

lemma quadraticForm_dotProduct {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    quadraticForm M x=x⬝ᵥ(M*ᵥx) := by
  simp only [quadraticForm,dotProduct,Matrix.mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro k _; ring

lemma quadraticForm_margin {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} {m : ℝ}
    (hM : (M-m • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖=1) : m ≤ quadraticForm M x.ofLp := by
  have hh := hM.dotProduct_mulVec_nonneg x.ofLp
  have hxx : x.ofLp⬝ᵥx.ofLp=1 := by
    have he := EuclideanSpace.real_norm_sq_eq x
    rw [hx,one_pow] at he
    simpa only [dotProduct,pow_two] using he.symm
  simp only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_sub,dotProduct_smul,smul_eq_mul,hxx,mul_one] at hh
  rw [quadraticForm_dotProduct]
  linarith

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

lemma measurable_conditionalGoe_map {n : ℕ} [NeZero n] (j t σ : ℝ) (y : Fin n → ℝ) :
    Measurable (fun g (p : Fin n × Fin n) => empiricalConditionalGoe j t σ y g p.1 p.2) := by
  dsimp [empiricalConditionalGoe,conditionalBlockMatrix,goeBlockResidual,goeBilinear,
    Matrix.mulVec,dotProduct,goeMatrix]
  fun_prop

lemma measurable_badField_fiber {n : ℕ} (j A ε c : ℝ) (y : Fin n → ℝ) :
    MeasurableSet {W : (Fin n × Fin n) → ℝ | ((fun i k=>W (i,k)),y) ∈ badFieldSet n j A ε c} :=
  ((isClosed_badFieldSet n j A ε c).preimage (by fun_prop)).measurableSet

lemma conditional_bad_le_freshbad {n : ℕ} [NeZero n] {j t σ A ε c m : ℝ}
    (hj : 0 ≤ j) (ht : 0 < t) (hcm : c < m) (y : Fin n → ℝ)
    (hq : 0 < scalarQMoment (empiricalLaw y)) :
    (conditionalGoeLaw (j/(n:ℝ)) (t+σ^2) (magnetization y) (empiricalObservation j t σ y)).real
      {W | ((fun i k=>W (i,k)),y) ∈ badFieldSet n j A ε c} ≤
    (gaussianCoordinates (MatrixCoordinates (Fin n))).real
      {g | ∃ a, (∀ i,a i ∈ Icc 0 A) ∧
        (∑ i,(a i-(1-tanh (y i)^2))^2) ≤ ε^2*(n:ℝ) ∧
        ¬(diagonalHessian a (empiricalConditionalMiddle j t σ y g)-
          m • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef} := by
  rw [show magnetization y=(fun i=>tanh (y i)) from rfl,empirical_conditional_law hj ht y hq]
  unfold Measure.real
  rw [Measure.map_apply (measurable_conditionalGoe_map j t σ y) (measurable_badField_fiber j A ε c y)]
  apply ENNReal.toReal_mono (by finiteness)
  apply measure_mono
  intro g hg
  obtain ⟨a,ha,hclose,x,hx,hquad⟩ := hg
  refine ⟨a,ha,hclose,?_⟩
  intro hpsd
  rw [empiricalConditionalGoe_hessian j t σ y a hq g] at hquad
  exact (not_le_of_gt hcm) ((quadraticForm_margin hpsd x hx).trans hquad)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ConditionalStability
attribute [-instance] _root_.OAI.SKGap.conditionalGoeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

theorem conditional_field_stability_oai {j A R t0 T : ℝ}
    (hj : 0 < j) (hj1 : j < 1) (hA : 1 ≤ A) (hsub : sqrt j*A < 1)
    (hR : 0 ≤ R) (ht0 : 0 < t0) :
    ∃ m ν σ0 : ℝ, 0 < m ∧ 0 < ν ∧ 0 < σ0 ∧
    ∃ U : Set (ScalarTimeDomain R t0 T), IsOpen U ∧ scalarEqualitySet j R t0 T ⊆ U ∧
    ∀ R1 : ℝ, 1 ≤ R1 → ∃ ε c : ℝ, ∃ N : ℕ, 0 < ε ∧ 0 < c ∧ 0 < N ∧
    ∀ (n : ℕ) [NeZero n], N ≤ n → ∀ x ∈ U, ∀ y : Fin n → ℝ,
    empiricalLaw y=(x.1 : ProbabilityMeasure ℝ) →
    (∑ i,if R1 < |y i| then y i^2 else 0) ≤ ν*(n:ℝ) →
    ∀ σ : ℝ, |σ| ≤ σ0 →
    (conditionalGoeLaw (j/(n:ℝ)) ((x.2:ℝ)+σ^2) (magnetization y)
      (empiricalObservation j x.2 σ y)).real
      {W | ((fun i k=>W (i,k)),y) ∈ badFieldSet n j A ε m} ≤ exp (-c*(n:ℝ)) := by
  obtain ⟨m,ν,σ0,hm,hν,hσ0,U,hU,hKU,hbound⟩ :=
    conditional_empirical_simultaneous (T := T) hj hj1 hA hsub hR ht0
  let V : Set (ScalarTimeDomain R t0 T) := {x | 0 < scalarQMoment (x.1:ProbabilityMeasure ℝ)}
  have hV : IsOpen V := isOpen_lt continuous_const
    (continuous_scalarQMoment.comp (continuous_subtype_val.comp continuous_fst))
  have hKV : scalarEqualitySet j R t0 T ⊆ V := by
    intro x hx
    change 0 < scalarQMoment (x.1:ProbabilityMeasure ℝ)
    rw [hx,scalarQMoment_curve hj hj1 (ht0.le.trans x.2.2.1)]
    exact (scalar_fixed_pos hj hj1 (ht0.trans_le x.2.2.1)).2
  refine ⟨m/2,ν,σ0,half_pos hm,hν,hσ0,U∩V,hU.inter hV,fun x hx=>⟨hKU hx,hKV hx⟩,?_⟩
  intro R1 hR1
  obtain ⟨ε,c,N,hε,hc,hN,hb⟩ := hbound R1 hR1
  obtain ⟨M,hM⟩ := absorb_finite_exponential_factor 103 (half_pos hc)
  refine ⟨ε,c/2,max N M,hε,half_pos hc,lt_of_lt_of_le hN (le_max_left _ _),?_⟩
  intro n _ hn x hx y hP hy σ hσ
  have hq : 0 < scalarQMoment (empiricalLaw y) := by rw [hP]; exact hx.2
  apply (conditional_bad_le_freshbad hj.le (ht0.trans_le x.2.2.1) (by linarith : m/2 < m) y hq).trans
  apply (hb n ((le_max_left N M).trans hn) x hx.1 y hP hy σ hσ).trans
  simpa only [Nat.cast_ofNat,show (n:ℝ)*(-c)= -c*(n:ℝ) from by ring,
    show (n:ℝ)*(-c+c/2)= -(c/2)*(n:ℝ) from by ring] using
    hM n ((le_max_right N M).trans hn) (-c)
end SKGap
end
end

end OAI
end

theorem solution : type_of% @OAI.SKGap.conditional_field_stability_oai := @OAI.SKGap.conditional_field_stability_oai
