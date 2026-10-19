-- Prove2me | solution 1 for OAI.ClassicalON.ising_edge_mean_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T02:55:12.755429+00:00
-- url     : https://prove2.me/submissions/4ebccc8d-b4e8-4186-8789-075a73b1cceb

import Mathlib
import Definitions.Def_OAIQWCO002
import Theorems.Thm_OAI_ClassicalON_ising_edge_covariance_nonneg

section
-- module Solutions.OAIQW_ClassicalON.FiniteVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uF uR uS uV uΩ

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace ClassicalON

theorem hasDerivAt_integral_compact
    {Ω : Type uΩ} {F : Type uF} [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f fd : ℝ → Ω → F)
    (hf : Continuous (Function.uncurry f)) (hfd : Continuous (Function.uncurry fd))
    (hd : ∀ t ω, HasDerivAt (fun u => f u ω) (fd t ω) t) (t : ℝ) :
    HasDerivAt (fun u => ∫ ω, f u ω ∂μ) (∫ ω, fd t ω ∂μ) t := by
  have hi (u : ℝ) : Integrable (f u) μ :=
    (hf.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hdi (u : ℝ) : Integrable (fd u) μ :=
    (hfd.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  obtain ⟨C, hC⟩ := (((isCompact_closedBall t 1).prod
    (isCompact_univ : IsCompact (Set.univ : Set Ω))).image hfd).isBounded.exists_norm_le
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.closedBall t 1) (bound := fun _ => C)
    (Metric.closedBall_mem_nhds t zero_lt_one)
    (Filter.Eventually.of_forall fun u => (hi u).aestronglyMeasurable)
    (hi t) (hdi t).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω u hu => hC _ ⟨(u, ω), ⟨hu, Set.mem_univ _⟩, rfl⟩)
    (integrable_const C)
    (Filter.Eventually.of_forall fun ω u _ => hd u ω)).2

open scoped Matrix

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AssociationCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX uY

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace ClassicalON

section CompactIntegral
variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {μ : Measure X} [IsFiniteMeasure μ]

theorem compact_integrable {f : X → ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem compact_integral_pos [IsProbabilityMeasure μ] {w : X → ℝ}
    (hw : Continuous w) (hp : ∀ x,0<w x) : 0<∫ x,w x ∂μ := by
  apply (integral_pos_iff_support_of_nonneg (fun x => (hp x).le) (compact_integrable hw)).2
  have he : Function.support w=univ := by ext x; simp [Function.mem_support,(hp x).ne']
  rw [he,measure_univ]
  exact zero_lt_one

end CompactIntegral

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.GibbsDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uX

noncomputable section
open MeasureTheory
namespace ClassicalON

section
variable {X : Type uX} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem hasDerivAt_exponentialIntegral {H A f : X → ℝ}
    (hH : Continuous H) (hA : Continuous A) (hf : Continuous f) (t : ℝ) :
    HasDerivAt (fun u => ∫ x,Real.exp (H x+u*A x)*f x ∂μ)
      (∫ x,Real.exp (H x+t*A x)*(f x*A x) ∂μ) t := by
  apply hasDerivAt_integral_compact μ
    (fun u x => Real.exp (H x+u*A x)*f x)
    (fun u x => Real.exp (H x+u*A x)*(f x*A x)) (by fun_prop) (by fun_prop)
  intro u x
  exact ((((hasDerivAt_id u).mul_const (A x)).const_add (H x)).exp.mul_const (f x)).congr_deriv (by simp only [id_eq]; ring)

theorem hasDerivAt_exponentialMean {H A f : X → ℝ}
    (hH : Continuous H) (hA : Continuous A) (hf : Continuous f) (t : ℝ) :
    HasDerivAt (fun u => exponentialMean μ (fun x => H x+u*A x) f)
      (exponentialMean μ (fun x => H x+t*A x) (fun x => f x*A x)-
        exponentialMean μ (fun x => H x+t*A x) f*
        exponentialMean μ (fun x => H x+t*A x) A) t := by
  have hN := hasDerivAt_exponentialIntegral μ hH hA hf t
  have hD := hasDerivAt_exponentialIntegral μ hH hA continuous_const t (f := fun _ => 1)
  simp only [mul_one,one_mul] at hD
  have hz : (∫ x,Real.exp (H x+t*A x) ∂μ)≠0 :=
    (compact_integral_pos (by fun_prop) (fun x => Real.exp_pos _)).ne'
  exact (hN.div hD hz).congr_deriv (by unfold exponentialMean weightedMean; field_simp)

end
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.WeightedLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uX

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ClassicalON

section
variable {X : Type uX} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
  {w : X → ℝ}

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
theorem weightedMean_const_mul (c : ℝ) (f : X → ℝ) :
    weightedMean μ w (fun x => c*f x)=c*weightedMean μ w f := by
  unfold weightedMean
  simp only [show (fun x => w x*(c*f x))=(fun x => c*(w x*f x)) from by funext; ring,
    integral_const_mul]
  ring

theorem weightedMean_sum (hw : Continuous w) {E : Type uE} [Fintype E] (f : E → X → ℝ)
    (hf : ∀ e,Continuous (f e)) : weightedMean μ w (fun x => ∑ e,f e x)=
      ∑ e,weightedMean μ w (f e) := by
  unfold weightedMean
  simp_rw [Finset.mul_sum]
  have hI (e : E) : Integrable (fun x => w x*f e x) μ := compact_integrable (by fun_prop)
  rw [integral_finsetSum _ (fun e _ => hI e),Finset.sum_div]

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
theorem exponentialMean_const_mul (H : X → ℝ) (c : ℝ) (f : X → ℝ) :
    exponentialMean μ H (fun x => c*f x)=c*exponentialMean μ H f :=
  weightedMean_const_mul μ c f

theorem exponentialMean_sum {E : Type uE} [Fintype E] {H : X → ℝ}
    (hH : Continuous H) (f : E → X → ℝ) (hf : ∀ e,Continuous (f e)) :
    exponentialMean μ H (fun x => ∑ e,f e x)=∑ e,exponentialMean μ H (f e) :=
  weightedMean_sum μ hH.rexp f hf

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] in
theorem exponentialMean_zero (f : X → ℝ) :
    exponentialMean μ (fun _ => 0) f=∫ x,f x ∂μ := by
  simp [exponentialMean,weightedMean]

end
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.FerromagneticMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uX

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace ClassicalON

section
variable {X : Type uX} {E : Type uE} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [Fintype E] (μ : Measure X) [IsProbabilityMeasure μ]
  (T : E → X → ℝ)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem continuous_edgeHamiltonian (hT : ∀ e,Continuous (T e)) (b : E → ℝ) :
    Continuous (edgeHamiltonian T b) := by
  exact continuous_finsetSum _ (fun e _ => continuous_const.mul (hT e))

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] in
theorem edgeMean_zero (f : X → ℝ) : edgeMean μ T (fun _ => 0) f=∫ x,f x ∂μ := by
  have hz : edgeHamiltonian T (fun _ => 0)=(fun _ => 0) := by funext x; simp [edgeHamiltonian]
  unfold edgeMean
  rw [hz,exponentialMean_zero]

theorem edgeMean_direction_derivative (hT : ∀ e,Continuous (T e)) (b d : E → ℝ)
    (e : E) (t : ℝ) :
    HasDerivAt (fun u => edgeMean μ T (fun g => b g+u*d g) (T e))
      (∑ g,d g*(edgeMean μ T (fun h => b h+t*d h) (fun x => T e x*T g x)-
        edgeMean μ T (fun h => b h+t*d h) (T e)*
        edgeMean μ T (fun h => b h+t*d h) (T g))) t := by
  have he (u : ℝ) (x : X) : edgeHamiltonian T (fun g => b g+u*d g) x=
      edgeHamiltonian T b x+u*edgeHamiltonian T d x := by
    simp only [edgeHamiltonian,add_mul,Finset.sum_add_distrib,Finset.mul_sum,mul_assoc]
  have hd := hasDerivAt_exponentialMean μ (continuous_edgeHamiltonian T hT b)
    (continuous_edgeHamiltonian T hT d) (hT e) t
  simp_rw [← he] at hd
  change HasDerivAt (fun u => exponentialMean μ (edgeHamiltonian T (fun g => b g+u*d g)) (T e)) _ _
  apply hd.congr_deriv
  rw [show (fun x => T e x*edgeHamiltonian T d x)=
    (fun x => ∑ g,d g*(T e x*T g x)) by funext; simp only [edgeHamiltonian,Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring]
  rw [exponentialMean_sum μ (continuous_edgeHamiltonian T hT _) _ (fun g => by fun_prop)]
  change (∑ g,exponentialMean μ _ (fun x => d g*(T e x*T g x)))-
    exponentialMean μ _ (T e)*exponentialMean μ _ (fun x => ∑ g,d g*T g x)=_
  rw [exponentialMean_sum μ (continuous_edgeHamiltonian T hT _) _ (fun g => by fun_prop)]
  simp only [exponentialMean_const_mul,Finset.mul_sum,← Finset.sum_sub_distrib,edgeMean]
  apply Finset.sum_congr rfl
  intro g _
  ring

theorem edgeMean_mono_couplings (hT : ∀ e,Continuous (T e))
    (hCov : EdgeCovarianceNonneg μ T) {a b : E → ℝ}
    (ha : ∀ e,0≤a e) (hab : ∀ e,a e≤b e) (e : E) :
    edgeMean μ T a (T e)≤edgeMean μ T b (T e) := by
  let d := fun g => b g-a g
  let F := fun t => edgeMean μ T (fun g => a g+t*d g) (T e)
  have hD := edgeMean_direction_derivative μ T hT a d e
  have hM : MonotoneOn F (Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (fun t _ => (hD t).continuousAt.continuousWithinAt)
      (fun t _ => (hD t).hasDerivWithinAt)
    intro t ht
    apply Finset.sum_nonneg
    intro g _
    apply mul_nonneg (sub_nonneg.mpr (hab g))
    apply sub_nonneg.mpr
    apply hCov
    intro h
    have ht0 : 0≤t := (interior_subset ht).1
    exact add_nonneg (ha h) (mul_nonneg ht0 (sub_nonneg.mpr (hab h)))
  have hh := hM (by simp : (0 : ℝ)∈Icc 0 1) (by simp : (1 : ℝ)∈Icc 0 1) (by norm_num)
  simpa only [F,d,zero_mul,add_zero,one_mul,add_sub_cancel] using hh

theorem edgeMean_nonneg (hT : ∀ e,Continuous (T e)) (hCov : EdgeCovarianceNonneg μ T)
    (h0 : ∀ e,0≤∫ x,T e x ∂μ) (b : E → ℝ) (hb : ∀ e,0≤b e) (e : E) :
    0≤edgeMean μ T b (T e) := by
  have hh := edgeMean_mono_couplings μ T hT hCov (fun _ => le_rfl) hb e
  rw [edgeMean_zero] at hh
  exact (h0 e).trans hh

end
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.ProductMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uV uX

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ClassicalON

variable {V : Type uV} {I : Type uI} {X : Type uX} [Fintype V] [DecidableEq V]

theorem site_grouping (a : I → X → ℝ) (l : List (V×I)) (x : V → X) :
    (l.map (fun p => a p.2 (x p.1))).prod =
      ∏ v,((retainedIndices v l).map (fun i => a i (x v))).prod := by
  induction l with
  | nil => simp [retainedIndices]
  | cons p l ih =>
    have hv (v : V) :
        ((retainedIndices v (p::l)).map (fun i => a i (x v))).prod =
        (if p.1=v then a p.2 (x p.1) else 1)*
          ((retainedIndices v l).map (fun i => a i (x v))).prod := by
      by_cases h : p.1=v
      · subst v; simp [retainedIndices]
      · simp [retainedIndices,h]
    simp only [List.map_cons,List.prod_cons,ih,hv,Finset.prod_mul_distrib]
    congr 1
    simp

theorem independent_moments_nonneg [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (a : I → X → ℝ)
    (hm : ∀ l : List I,0≤∫ x,(l.map (fun i => a i x)).prod ∂μ)
    (l : List (V×I)) :
    0≤∫ x : V → X,(l.map (fun p => a p.2 (x p.1))).prod ∂Measure.pi (fun _ => μ) := by
  simp_rw [site_grouping a l]
  rw [integral_fintype_prod_eq_prod (fun v x =>
    (List.map (fun i => a i x) (retainedIndices v l)).prod)]
  exact Finset.prod_nonneg (fun v _ => hm (retainedIndices v l))

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.IsingPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace ClassicalON

theorem signValue_product_moment (l : List Unit) :
    0≤∫ t,(l.map (fun _ => signValue t)).prod ∂signLaw := by
  have he (t : Bool) : (l.map (fun _ => signValue t)).prod=signValue t^l.length := by simp
  simp_rw [he]
  simp only [signLaw,integral_smul_measure,ENNReal.toReal_inv,ENNReal.toReal_ofNat,
    smul_eq_mul,integral_count,Fintype.sum_bool,signValue,Bool.false_eq_true,ite_false,ite_true,
    one_pow]
  have hh : -1≤(-1 : ℝ)^l.length := by
    simpa only [abs_pow,abs_neg,abs_one,one_pow] using neg_abs_le ((-1 : ℝ)^l.length)
  norm_num at *
  linarith

variable {V : Type uV} {E : Type uE} [Fintype V]

theorem ising_reference_mean_nonneg (left right : E → V) (e : E) :
    0≤∫ s,isingEnergy left right e s ∂isingReference := by
  classical
  have hh := independent_moments_nonneg (V := V) signLaw (fun (_ : Unit) t => signValue t)
    signValue_product_moment [(left e,()),(right e,())]
  simpa only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,isingEnergy,
    isingReference] using hh

variable [Fintype E]

theorem ising_edge_mean_nonneg_oai (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e) (e : E) :
    0 ≤ isingMean left right b (isingEnergy left right e) := by
  apply edgeMean_nonneg isingReference (isingEnergy left right)
    (fun _ => continuous_of_discreteTopology)
  · exact ising_edge_covariance_nonneg left right
  · exact ising_reference_mean_nonneg left right
  · exact hb

end ClassicalON

end

end OAI
end

theorem solution.{uE, uV} : type_of% @OAI.ClassicalON.ising_edge_mean_nonneg_oai.{uE, uV} := @OAI.ClassicalON.ising_edge_mean_nonneg_oai.{uE, uV}
