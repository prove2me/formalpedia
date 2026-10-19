-- Prove2me | solution 1 for OAI.FiniteEntropySeparation.chosen_terminal_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:24:11.115419+00:00
-- url     : https://prove2.me/submissions/f57d474b-bb0a-4e18-b3d1-aa2dfddbcd1f

import Mathlib
import Definitions.Def_FiniteEntropySeparation
import Definitions.Def_OAIQWFE002
import Theorems.Thm_OAI_FiniteEntropySeparation_Model_matrixHeatLaw_blocks_eventually
import Theorems.Thm_OAI_FiniteEntropySeparation_Model_matrixHeatLaw_totalSecond_tendsto

section
-- module Solutions.OAIQW_FiniteEntropySeparation.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Filter

namespace FiniteEntropySeparation

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 theorem trace_add {M : VonNeumannAlgebra H} (τ : TracialVector M)
    (A B : H →L[ℂ] H) : trace τ (A + B) = trace τ A + trace τ B := by
  simp [trace]

 theorem trace_smul {M : VonNeumannAlgebra H} (τ : TracialVector M)
    (z : ℂ) (A : H →L[ℂ] H) : trace τ (z • A) = z * trace τ A := by
  simp [trace]

 theorem trace_sum {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {α : Type u1} (s : Finset α) (A : α → H →L[ℂ] H) :
    trace τ (∑ a ∈ s, A a) = ∑ a ∈ s, trace τ (A a) := by
  simp [trace]

omit [CompleteSpace H] in
 theorem commutatorKernel_cons {n : ℕ} (P : H →L[ℂ] H)
    (X : Fin n → H →L[ℂ] H) (i j : Fin n) (w : List (Fin n)) :
    commutatorKernel P X i (j :: w) =
      (if j = i then P * wordEval X w else 0) + X j * commutatorKernel P X i w := by
  simp only [commutatorKernel, List.length_cons, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ,
    List.take_zero, List.take_succ_cons, List.drop_succ_cons, Nat.zero_add,
    wordEval, List.map_nil, List.prod_nil, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp [List.map_cons, List.prod_cons, mul_assoc]

omit [CompleteSpace H] in
 theorem commutator_word {n : ℕ} (P a : H →L[ℂ] H) (X : Fin n → H →L[ℂ] H)
    (i : Fin n) (c : ℂ)
    (h : ∀ j, a * X j = X j * a + if j = i then c • P else 0)
    (w : List (Fin n)) :
    a * wordEval X w = wordEval X w * a + c • commutatorKernel P X i w := by
  induction w with
  | nil => simp [wordEval]
  | cons j w ih =>
    have hw : wordEval X (j :: w) = X j * wordEval X w := by simp [wordEval]
    rw [hw, commutatorKernel_cons, ← mul_assoc, h, add_mul, mul_assoc, ih]
    by_cases hji : j = i <;>
      simp [hji, mul_add, mul_assoc, smul_add, _root_.add_assoc, _root_.add_comm,
        _root_.add_left_comm]

namespace Fock

open scoped lp
variable {ι : Type} [DecidableEq ι]

 theorem creation_commutes_rightCreation (i j : ι) :
    Commute (creation i) (rightCreation j) := by
  show creation i * rightCreation j = rightCreation j * creation i
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change creation i (rightCreation j (lp.single 2 w z)) =
    rightCreation j (creation i (lp.single 2 w z))
  simp

 theorem rightAnnihilation_creation (i j : ι) :
    star (rightCreation i) * creation j = creation j * star (rightCreation i) +
      if i = j then vacuumProjection else 0 := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change star (rightCreation i) (creation j (lp.single 2 w z)) =
    creation j (star (rightCreation i) (lp.single 2 w z)) +
      (if i = j then vacuumProjection else 0) (lp.single 2 w z)
  induction w using List.reverseRecOn with
  | nil =>
    rw [creation_single, show [j] = [] ++ [j] from rfl, rightAnnihilation_single_append]
    by_cases h : i = j <;> simp [h]
  | append_singleton w k _ =>
    rw [creation_single, show j :: (w ++ [k]) = (j :: w) ++ [k] from rfl,
      rightAnnihilation_single_append]
    have hp : (if i = j then vacuumProjection else 0) (lp.single 2 (w ++ [k]) z) = 0 := by
      split_ifs <;> simp
    rw [hp, rightAnnihilation_single_append]
    by_cases h : i = k <;> simp [h]

theorem rightAnnihilation_semicircular (i j : ι) :
    star (rightCreation i) * semicircular j = semicircular j * star (rightCreation i) +
      if i = j then vacuumProjection else 0 := by
  have h : star (rightCreation i) * star (creation j) =
      star (creation j) * star (rightCreation i) := by
    simpa only [star_mul] using congrArg star (creation_commutes_rightCreation j i).eq
  rw [semicircular, mul_add, add_mul, rightAnnihilation_creation, h]
  abel

 theorem derivativeKernel_cons {n : ℕ} (i j : Fin n) (w : List (Fin n)) :
    derivativeKernel i (j :: w) =
      (if j = i then vacuumProjection * wordEval semicircular w else 0) +
        semicircular j * derivativeKernel i w := by
  simp only [derivativeKernel, List.length_cons, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ,
    List.take_zero, List.take_succ_cons, List.drop_succ_cons, Nat.zero_add,
    wordEval, List.map_nil, List.prod_nil, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp [List.map_cons, List.prod_cons, mul_assoc]

 theorem rightAnnihilation_word {n : ℕ} (i : Fin n) (w : List (Fin n)) :
    star (rightCreation i) * wordEval semicircular w =
      wordEval semicircular w * star (rightCreation i) + derivativeKernel i w := by
  induction w with
  | nil => simp [wordEval]
  | cons j w ih =>
    have hw : wordEval semicircular (j :: w) = semicircular j * wordEval semicircular w := by
      simp [wordEval]
    rw [hw, derivativeKernel_cons, ← mul_assoc, rightAnnihilation_semicircular,
      add_mul, mul_assoc, ih, mul_add]
    by_cases h : i = j <;> simp [h, eq_comm, mul_assoc, add_assoc, add_comm, add_left_comm]

 theorem trace_projection_product (A B : Space ι →L[ℂ] Space ι) :
    trace (tracialVector ι) (A * vacuumProjection * B) =
      trace (tracialVector ι) A * trace (tracialVector ι) B := by
  simp only [trace, tracialVector, vacuumProjection, mul_apply_eq_comp,
    InnerProductSpace.rankOne_apply, map_smul, inner_smul_right]
  exact mul_comm _ _

 theorem trace_derivativeKernel {n : ℕ} (i : Fin n) (w : List (Fin n)) :
    trace (tracialVector (Fin n)) (derivativeKernel i w) =
      derivativeMoment (tracialVector (Fin n)) semicircular i w := by
  rw [derivativeKernel, trace_sum]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp [trace_projection_product, wordMoment]

 theorem trace_semicircular_left (i : ι) (A : Space ι →L[ℂ] Space ι) :
    trace (tracialVector ι) (semicircular i * A) =
      trace (tracialVector ι) (star (rightCreation i) * A) := by
  simp only [trace, tracialVector, mul_apply_eq_comp]
  rw [← ContinuousLinearMap.adjoint_inner_left (semicircular i),
    ← ContinuousLinearMap.adjoint_inner_left (star (rightCreation i))]
  simp only [← ContinuousLinearMap.star_eq_adjoint, star_star,
    (semicircular_selfAdjoint i).star_eq, basisVector,
    semicircular_single_nil, rightCreation_single, List.nil_append]

theorem semicircular_integration_by_parts {n : ℕ} (i : Fin n) (w : List (Fin n)) :
    trace (tracialVector (Fin n)) (semicircular i * wordEval semicircular w) =
      derivativeMoment (tracialVector (Fin n)) semicircular i w := by
  rw [trace_semicircular_left, rightAnnihilation_word, trace_add, trace_derivativeKernel]
  suffices trace (tracialVector (Fin n))
      (wordEval semicircular w * star (rightCreation i)) = 0 by rw [this, zero_add]
  simp [trace, tracialVector, basisVector, mul_apply_eq_comp]

end Fock

end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianIBP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open scoped ENNReal NNReal Polynomial
open MeasureTheory ProbabilityTheory Filter
namespace FiniteEntropySeparation
 theorem gaussian_weight_integrable {E : Type u1} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) {f : ℝ → E} :
    Integrable f (gaussianReal μ v) ↔ Integrable (fun x => gaussianPDFReal μ v x • f x) := by
  rw [gaussianReal_of_var_ne_zero _ hv]
  simpa only [toReal_gaussianPDF] using integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF μ v) (Filter.Eventually.of_forall (fun _ => gaussianPDF_lt_top))
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7

noncomputable section
open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal
namespace FiniteEntropySeparation
 theorem integral_pi_prod {ι : Type u1} [Fintype ι] (f : ι → ℝ → ℝ)
    (s : ι → Set ℝ) (hs : ∀i,MeasurableSet (s i)) :
    ∫ x : ι → ℝ in Set.pi univ s, ∏ i,f i (x i) = ∏ i,∫ x in s i,f i x := by
  classical
  rw [← integral_indicator (MeasurableSet.univ_pi hs)]
  have he : (Set.pi univ s).indicator (fun x : ι → ℝ => ∏ i,f i (x i)) =
      fun x => ∏ i,(s i).indicator (f i) (x i) := by
    funext x
    by_cases h : ∀i,x i ∈ s i
    · simp [Set.indicator_of_mem,Set.mem_pi,h]
    · obtain ⟨i,hi⟩ := not_forall.mp h
      rw [Set.indicator_of_notMem (by simpa only [Set.mem_univ_pi] using not_forall.mpr ⟨i,hi⟩)]
      symm
      exact prod_eq_zero (mem_univ i) (Set.indicator_of_notMem hi _)
  rw [he,integral_fintype_prod_volume_eq_prod]
  simp only [integral_indicator,hs]
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal Topology
namespace FiniteEntropySeparation
 variable {ι : Type u1} [Fintype ι]
 theorem normalKernel_pos (s : ℝ) (x : EuclideanSpace ℝ ι) : 0<normalKernel s x := Real.exp_pos _
 theorem normalKernel_formula {s : ℝ} (hs : 0<s) (x : EuclideanSpace ℝ ι) :
    normalKernel s x = (Real.sqrt (2*Real.pi*s))⁻¹^(Fintype.card ι)*Real.exp (-‖x‖^2/(2*s)) := by
  rw [normalKernel,sub_eq_add_neg,Real.exp_add]
  simp only [neg_div]
  congr 1
  have hp : 0<2*Real.pi*s := by positivity
  rw [← Real.exp_log (show 0<(Real.sqrt (2*Real.pi*s))⁻¹^(Fintype.card ι) by positivity),Real.log_pow,Real.log_inv,Real.log_sqrt hp.le]
  congr 1
  ring
 theorem normalKernel_product {s : ℝ} (hs : 0<s) (x : EuclideanSpace ℝ ι) :
    normalKernel s x = ∏ i,gaussianPDFReal 0 ⟨s,hs.le⟩ (x i) := by
  classical
  rw [normalKernel_formula hs]
  simp only [gaussianPDFReal,sub_zero,prod_mul_distrib,prod_const,card_univ,← Real.exp_sum]
  congr 1
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs,sq_abs,← sum_div,sum_neg_distrib]
  rfl
 theorem normalKernel_integrable {s : ℝ} (hs : 0<s) : Integrable (normalKernel (ι := ι) s) := by
  rw [← (PiLp.volume_preserving_toLp ι).integrable_comp_emb (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  simpa only [Function.comp_def,normalKernel_product hs,WithLp.ofLp_toLp,volume_pi] using
    Integrable.fintype_prod (fun _ : ι => integrable_gaussianPDFReal 0 ⟨s,hs.le⟩)
 theorem normalKernel_integral {s : ℝ} (hs : 0<s) : ∫ x : EuclideanSpace ℝ ι,normalKernel s x = 1 := by
  rw [← (PiLp.volume_preserving_toLp ι).integral_comp (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  simp only [normalKernel_product hs,integral_fintype_prod_volume_eq_prod]
  have h : (∫ x : ℝ,gaussianPDFReal 0 ⟨s,hs.le⟩ x)=1 := integral_gaussianPDFReal_eq_one 0 (fun h => hs.ne' (congrArg (fun z : ℝ≥0 => (z:ℝ)) h))
  simp only [h,prod_const_one]
 theorem normalKernel_continuous_space (s : ℝ) : Continuous (normalKernel (ι := ι) s) := by
  unfold normalKernel
  fun_prop
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
 theorem normalKernel_le (s : ℝ) (hs : 0<s) (x : EuclideanSpace ℝ ι) :
    normalKernel s x ≤ Real.exp (-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)) := by
  apply Real.exp_le_exp.mpr
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (by positivity))
 theorem normalKernel_integrable_finite (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0<s) (x : EuclideanSpace ℝ ι) : Integrable (fun a => normalKernel s (x-a)) μ := by
  apply (integrable_const (Real.exp (-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)))).mono'
    (((normalKernel_continuous_space s).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  exact ae_of_all _ (fun a => by change ‖normalKernel s (x-a)‖≤_; rw [Real.norm_eq_abs,abs_of_pos (normalKernel_pos _ _)]; exact normalKernel_le s hs _)
 theorem smoothedDensity_pos (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0<s) (x : EuclideanSpace ℝ ι) : 0<smoothedDensity μ s x := by
  rw [smoothedDensity,integral_pos_iff_support_of_nonneg (fun a => (normalKernel_pos _ _).le) (normalKernel_integrable_finite μ hs x)]
  have h : Function.support (fun a => normalKernel s (x-a))=univ := by
    ext a; simp [Function.mem_support,(normalKernel_pos s (x-a)).ne']
  simp [h]
 theorem smoothedDensity_continuous (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0<s) : Continuous (smoothedDensity μ s) := by
  apply continuous_of_dominated (bound := fun _ => Real.exp (-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)))
  · intro x; exact (normalKernel_integrable_finite μ hs x).aestronglyMeasurable
  · intro x; exact ae_of_all _ (fun a => by change ‖normalKernel s (x-a)‖≤_; rw [Real.norm_eq_abs,abs_of_pos (normalKernel_pos _ _)]; exact normalKernel_le s hs _)
  · exact integrable_const _
  · exact ae_of_all _ (fun a => (normalKernel_continuous_space s).comp (continuous_id.sub continuous_const))
 theorem normalKernel_product_integrable (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0<s) : Integrable (fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => normalKernel s (z.2-z.1)) (μ.prod volume) := by
  apply (integrable_prod_iff (((normalKernel_continuous_space s).comp (continuous_snd.sub continuous_fst)).aestronglyMeasurable)).mpr
  constructor
  · exact ae_of_all _ (fun a => (normalKernel_integrable hs).comp_sub_right a)
  · simpa only [Function.comp_apply,Pi.sub_apply,Prod.fst,Prod.snd,Real.norm_eq_abs,abs_of_pos (normalKernel_pos _ _),integral_sub_right_eq_self,normalKernel_integral hs] using (integrable_const (1:ℝ) : Integrable (fun _ : EuclideanSpace ℝ ι => (1:ℝ)) μ)
 theorem smoothedDensity_integrable (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0<s) : Integrable (smoothedDensity μ s) := by
  exact (normalKernel_product_integrable μ hs).integral_prod_right
 theorem smoothedDensity_integral (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0<s) : ∫x,smoothedDensity μ s x = 1 := by
  unfold smoothedDensity
  rw [integral_integral_swap (f := fun x a => normalKernel s (x-a)) (show Integrable (fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => normalKernel s (z.1-z.2)) (volume.prod μ) from (normalKernel_product_integrable μ hs).swap)]
  simp only [integral_sub_right_eq_self,normalKernel_integral hs,integral_const,probReal_univ,one_smul]
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.NormalLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
 theorem map_withDensity_of_measurePreserving {α : Type u2} {β : Type u3} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → β} (hf : MeasurePreserving f μ ν)
    (g : β → ℝ≥0∞) (hg : Measurable g) :
    (μ.withDensity (g ∘ f)).map f = ν.withDensity g := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hf.measurable]
  change (∫⁻ a,(F ∘ f) a ∂μ.withDensity (g ∘ f)) = _
  rw [lintegral_withDensity_eq_lintegral_mul μ (hg.comp hf.measurable) (hF.comp hf.measurable),lintegral_withDensity_eq_lintegral_mul ν hg hF]
  exact hf.lintegral_comp (hg.mul hF)
 theorem productNormal_withDensity {s : ℝ} (hs : 0<s) :
    Measure.pi (fun _ : ι => gaussianReal 0 (⟨s,hs.le⟩ : ℝ≥0)) =
      volume.withDensity (fun x : ι → ℝ => ENNReal.ofReal (∏i,gaussianPDFReal 0 (⟨s,hs.le⟩ : ℝ≥0) (x i))) := by
  classical
  have hv : (⟨s,hs.le⟩ : ℝ≥0)≠0 := by
    intro h; exact hs.ne' (congrArg (fun x : ℝ≥0 => (x:ℝ)) h)
  have hi : Integrable (fun x : ι → ℝ => ∏i,gaussianPDFReal 0 (⟨s,hs.le⟩ : ℝ≥0) (x i)) :=
    Integrable.fintype_prod (fun _ => integrable_gaussianPDFReal 0 (⟨s,hs.le⟩ : ℝ≥0))
  let v : ℝ≥0 := ⟨s,hs.le⟩
  have : ∀i : ι,SigmaFinite (gaussianReal 0 v) := fun _ => inferInstance
  apply Measure.pi_eq (μ := fun _ : ι => gaussianReal 0 v)
  intro S hS
  rw [withDensity_apply _ (MeasurableSet.univ_pi hS)]
  rw [← ofReal_integral_eq_lintegral_ofReal hi.integrableOn (ae_of_all _ (fun x => prod_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _)))]
  rw [integral_pi_prod _ S hS,ENNReal.ofReal_prod_of_nonneg]
  · apply prod_congr rfl
    intro i _
    rw [gaussianReal_apply 0 hv]
    exact ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal 0 (⟨s,hs.le⟩ : ℝ≥0)).integrableOn
      (ae_of_all _ (gaussianPDFReal_nonneg _ _))
  · intro i _
    exact integral_nonneg (gaussianPDFReal_nonneg _ _)
 theorem normalLaw_eq_map {s : ℝ} (hs : 0<s) :
    normalLaw (ι := ι) s = (Measure.pi (fun _ : ι => gaussianReal 0 (⟨s,hs.le⟩ : ℝ≥0))).map (WithLp.toLp 2) := by
  rw [productNormal_withDensity hs]
  have he : (fun x : ι → ℝ => ENNReal.ofReal (∏i,gaussianPDFReal 0 (⟨s,hs.le⟩ : ℝ≥0) (x i))) =
       (fun x => ENNReal.ofReal (normalKernel s x)) ∘ WithLp.toLp 2 := by
    funext x; simp only [Function.comp_apply,normalKernel_product hs]
  rw [he]
  exact (map_withDensity_of_measurePreserving (PiLp.volume_preserving_toLp ι)
    (fun x => ENNReal.ofReal (normalKernel s x))
    (ENNReal.measurable_ofReal.comp (normalKernel_continuous_space s).measurable)).symm
 theorem normalLaw_eq_scaled {s : ℝ} (hs : 0<s) :
    normalLaw (ι := ι) s = (productGaussian ι).map (fun x => Real.sqrt s • WithLp.toLp 2 x) := by
  have hm : (productGaussian ι).map (fun x i => Real.sqrt s*x i) = Measure.pi (fun _ : ι => gaussianReal 0 (⟨s,hs.le⟩ : ℝ≥0)) := by
    change (Measure.pi (fun _ : ι => gaussianReal 0 1)).map (fun x i => Real.sqrt s * id (x i)) = _
    rw [Measure.pi_map_pi (fun _ => (measurable_id.const_mul (Real.sqrt s)).aemeasurable)]
    congr 1
    funext i
    simp only [id_eq]
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext; simp only [mul_one,NNReal.coe_mk,Real.sq_sqrt hs.le]
      rfl
  rw [normalLaw_eq_map hs,← hm]
  rw [Measure.map_map (show Measurable (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) from (PiLp.continuous_toLp 2 _).measurable) (by fun_prop)]
  congr 1
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianBlockTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
 theorem normalLaw_rotation (s : ℝ) (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    (normalLaw s).map U = normalLaw s := by
  have he : (fun x => ENNReal.ofReal (normalKernel s x)) =
      (fun x => ENNReal.ofReal (normalKernel s x)) ∘ U := by
    funext x
    simp [normalKernel]
  unfold normalLaw
  conv_lhs => rw [he]
  exact map_withDensity_of_measurePreserving U.measurePreserving _
    (ENNReal.measurable_ofReal.comp (normalKernel_continuous_space s).measurable)
 theorem normalLaw_measurePreserving (s : ℝ) (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    MeasurePreserving U (normalLaw s) (normalLaw s) :=
  ⟨U.continuous.measurable,normalLaw_rotation s U⟩
 theorem squareExp_density (x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (x^2/4) =
      (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-(1/4:ℝ)*x^2) := by
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,mul_assoc,← Real.exp_add]
  congr 2
  ring
 theorem squareExp_integrable : Integrable (fun x : ℝ => Real.exp (x^2/4)) (gaussianReal 0 1) := by
  rw [gaussian_weight_integrable one_ne_zero]
  simp only [smul_eq_mul,squareExp_density]
  exact (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1/4)).const_mul _
 theorem squareExp_integral : (∫x : ℝ,Real.exp (x^2/4) ∂gaussianReal 0 1) = Real.sqrt 2 := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul,squareExp_density]
  rw [integral_const_mul,integral_gaussian]
  have hp := Real.pi_pos
  have he : Real.pi / (1/4:ℝ)=4*Real.pi := by ring
  rw [he,Real.sqrt_mul (by norm_num : (0:ℝ)≤2),Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
  norm_num
  have hs : Real.sqrt Real.pi≠0 := (Real.sqrt_pos.mpr hp).ne'
  have h2 : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  field_simp
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
 theorem masked_exp_integrable (m : Finset ι) :
    Integrable (fun x : ι → ℝ => Real.exp ((∑i∈m,x i^2)/4)) (productGaussian ι) := by
  classical
  have he : (fun x : ι → ℝ => Real.exp ((∑i∈m,x i^2)/4)) =
      fun x => ∏i,if i∈m then Real.exp (x i^2/4) else 1 := by
    funext x
    rw [sum_div,Real.exp_sum]
    simp
  rw [he]
  apply Integrable.fintype_prod (f := fun i (x:ℝ) => if i∈m then Real.exp (x^2/4) else 1)
  intro i
  by_cases hi : i∈m
  · simpa [hi] using squareExp_integrable
  · simp [hi]
 theorem masked_exp_integral (m : Finset ι) :
    (∫x : ι → ℝ,Real.exp ((∑i∈m,x i^2)/4) ∂productGaussian ι) = Real.sqrt 2^m.card := by
  classical
  have he : (fun x : ι → ℝ => Real.exp ((∑i∈m,x i^2)/4)) =
      fun x => ∏i,if i∈m then Real.exp (x i^2/4) else 1 := by
    funext x
    rw [sum_div,Real.exp_sum]
    simp
  rw [he,productGaussian,integral_fintype_prod_eq_prod (fun i (x:ℝ) => if i∈m then Real.exp (x^2/4) else 1)]
  have hh i : (∫x : ℝ,if i∈m then Real.exp (x^2/4) else 1 ∂gaussianReal 0 1)=
      if i∈m then Real.sqrt 2 else 1 := by
    by_cases hi : i∈m <;> simp [hi,squareExp_integral]
  simp_rw [hh]
  simp
 theorem masked_square_tail (m : Finset ι) (u : ℝ) :
    (productGaussian ι) {x | u≤∑i∈m,x i^2} ≤
      ENNReal.ofReal (Real.exp (-u/4)*Real.sqrt 2^m.card) := by
  have hi := (masked_exp_integrable m).const_mul (Real.exp (-u/4))
  have hh := hi.measure_le_integral (Filter.Eventually.of_forall (fun x => by positivity))
    (s := {x | u≤∑i∈m,x i^2}) (fun x hx => by
      rw [← Real.exp_add,Real.one_le_exp_iff]
      dsimp at hx
      linarith)
  rw [integral_const_mul,masked_exp_integral] at hh
  exact hh
 theorem normalLaw_mask_tail (m : Finset ι) {s : ℝ} (hs : 0<s) (u : ℝ) :
    (normalLaw s) {x | u≤∑i∈m,x i^2} ≤
      ENNReal.ofReal (Real.exp (-u/(4*s))*Real.sqrt 2^m.card) := by
  classical
  rw [normalLaw_eq_scaled hs,Measure.map_apply (by fun_prop) (isClosed_le continuous_const (by fun_prop)).measurableSet]
  have he : (fun x : ι → ℝ => Real.sqrt s • WithLp.toLp 2 x) ⁻¹' {x : EuclideanSpace ℝ ι | u≤∑i∈m,x i^2} =
      {x | u/s≤∑i∈m,x i^2} := by
    ext x
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,PiLp.smul_apply,smul_eq_mul,mul_pow,Real.sq_sqrt hs.le,← mul_sum]
    rw [div_le_iff₀ hs,mul_comm]
  rw [he]
  convert masked_square_tail m (u/s) using 1 ; congr 2 ; ring_nf
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.CoordinateMask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Finset
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
 theorem coordinateMask_sq (m : Finset ι) (x : EuclideanSpace ℝ ι) :
    ‖coordinateMask m x‖^2=∑i∈m,x i^2 := by
  classical
  simp [coordinateMask,EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs]
 theorem coordinateMask_norm_le (m : Finset ι) (x : EuclideanSpace ℝ ι) :
    ‖coordinateMask m x‖≤‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [coordinateMask_sq,EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs,sq_abs]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ m) (fun i _ _ => sq_nonneg _)
 theorem coordinateMask_continuous (m : Finset ι) : Continuous (coordinateMask m) :=
  (coordinateMaskLinear m).continuous_of_finiteDimensional
 theorem coordinateMask_norm_sub (m : Finset ι) (x y : EuclideanSpace ℝ ι) :
    |‖coordinateMask m x‖-‖coordinateMask m y‖|≤‖x-y‖ := by
  calc
    _ ≤ ‖coordinateMask m x-coordinateMask m y‖ := abs_norm_sub_norm_le _ _
    _ = ‖coordinateMask m (x-y)‖ := by exact congrArg norm (map_sub (coordinateMaskLinear m) x y).symm
    _ ≤ _ := coordinateMask_norm_le _ _
 theorem normalLaw_coordinateMask_tail (m : Finset ι) {s r : ℝ} (hs : 0<s) (hr : 0≤r) :
    (normalLaw s) {x | r≤‖coordinateMask m x‖} ≤
      ENNReal.ofReal (Real.exp (-r^2/(4*s))*Real.sqrt 2^m.card) := by
  have he : {x : EuclideanSpace ℝ ι | r≤‖coordinateMask m x‖}={x | r^2≤∑i∈m,x i^2} := by
    ext x
    simp only [Set.mem_ofPred_eq,← coordinateMask_sq]
    exact (sq_le_sq₀ hr (norm_nonneg _)).symm
  rw [he]
  exact normalLaw_mask_tail m hs _
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
open Finset
namespace FiniteEntropySeparation
 theorem hermitianMatrix_continuous {n d : ℕ} (i : Fin n) :
    Continuous (fun a : MatrixCoordinates n d => hermitianMatrix a i) :=
  (continuous_apply i).comp (hermitianChart n d).continuous_of_finiteDimensional
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal
open Finset MeasureTheory Set
namespace FiniteEntropySeparation
 theorem matrix_column_bound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (k : Fin d) :
    (∑ j, Complex.normSq (A j k)) ≤ matrixOpNorm A ^ 2 := by
  let T := (Matrix.toEuclideanLin A).toContinuousLinearMap
  have he : T (EuclideanSpace.single k 1) = WithLp.toLp 2 (fun j => A j k) := by
    change Matrix.toEuclideanLin A (EuclideanSpace.single k 1) = _
    rw [Matrix.toLpLin_apply]
    congr 1
    simp [EuclideanSpace.single, Matrix.mulVec_single, Matrix.col, Matrix.transpose]
    rfl
  have hb := T.le_opNorm (EuclideanSpace.single k 1)
  rw [he, PiLp.norm_single, norm_one, mul_one] at hb
  have hn : ‖WithLp.toLp 2 (fun j => A j k)‖^2 = ∑ j, Complex.normSq (A j k) := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Complex.normSq_eq_norm_sq]
  rw [← hn]
  exact pow_le_pow_left₀ (norm_nonneg _) hb 2
 theorem matrix_frobenius_bound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    (∑ j, ∑ k, Complex.normSq (A j k)) ≤ (d : ℝ) * matrixOpNorm A ^ 2 := by
  rw [sum_comm]
  simpa using sum_le_sum (s := (univ : Finset (Fin d))) (fun k _ => matrix_column_bound A k)
 theorem coordinates_sq_bound {n d : ℕ} (a : MatrixCoordinates n d) (R : ℝ)
    (hR : 0 ≤ R) (ha : ∀ i, matrixOpNorm (hermitianMatrix a i) ≤ R) :
    ‖a‖^2 ≤ (n : ℝ)*d*R^2 := by
  rw [← hermitianChart_normSq]
  calc
    _ ≤ ∑ i : Fin n, (d : ℝ) * matrixOpNorm (hermitianMatrix a i)^2 :=
      sum_le_sum (fun i _ => matrix_frobenius_bound _)
    _ ≤ ∑ _i : Fin n, (d : ℝ)*R^2 := sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) hR).mpr (ha i)) (Nat.cast_nonneg d))
    _ = _ := by simp; ring
 theorem microstates_subset_closedBall {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ} (X : Fin n → H →L[ℂ] H)
    (R : ℝ) (hR : 0 ≤ R) (m d : ℕ) (ε : ℝ) :
    microstates τ X R m d ε ⊆ Metric.closedBall 0 (Real.sqrt ((n : ℝ)*d) * R) := by
  intro a ha
  rw [Metric.mem_closedBall, dist_zero_right]
  have hb := coordinates_sq_bound a R hR ha.1
  have he : (Real.sqrt ((n : ℝ)*d) * R)^2 = (n : ℝ)*d*R^2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hn : 0 ≤ Real.sqrt ((n : ℝ)*d) * R := by positivity
  nlinarith [norm_nonneg a]
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open scoped ComplexConjugate
open Finset
namespace FiniteEntropySeparation
 theorem matrixOpNorm_nonneg {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : 0 ≤ matrixOpNorm A := norm_nonneg _
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TracialRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

 theorem trace_unitaryG (g : G) :
    trace (tracialVector B N G) (unitaryG g) = if g = 1 then 1 else 0 := by
  change inner ℂ (basis empty) (unitaryG g (basis empty)) = _
  rw [unitaryG_basis]
  by_cases hg : g = 1 <;> simp [basis, leftG, empty, lp.inner_single_left, lp.single_apply, hg, eq_comm]

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.HeatTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

 theorem vacuumBoundary_eq_rankOne :
    vacuumBoundary (B := B) (N := N) (G := G) = vacuumRankOne (tracialVector B N G) := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change vacuumBoundary (lp.single 2 w z) = _
  rw [vacuumBoundary_single]
  by_cases hw : w = empty
  · subst w
    simp [vacuumRankOne, tracialVector, basis, lp.inner_single_left]
    simpa using (lp.single_smul (E := fun _ : Word B N G => ℂ) 2 (empty : Word B N G) z (1 : ℂ))
  · simp [hw, vacuumRankOne, tracialVector, basis, lp.inner_single_left, lp.single_apply, Ne.symm hw]

 theorem rightAnnihilationN_semicircularN (i j : N) :
    star (rightCreationN (B := B) (G := G) i) * semicircularN j =
      semicircularN j * star (rightCreationN i) + if i = j then
        vacuumRankOne (tracialVector B N G) else 0 := by
  have h : Commute (creationN (B := B) (G := G) j) (rightCreationN i) :=
    LabelHilbert.lift_commute _ _ _ _ (leftN_rightN j i)
  have hs := h.star_star.symm.eq
  rw [semicircularN, mul_add, add_mul, rightAnnihilationN_creationN, hs,
    vacuumBoundary_eq_rankOne]
  abel

 theorem rightAnnihilationN_commutes_semicircularB (i : N) (b : B) :
    Commute (star (rightCreationN (G := G) i)) (semicircularB b) := by
  have h : Commute (creationB (G := G) b) (rightCreationN i) :=
    LabelHilbert.lift_commute _ _ _ _ (leftB_rightN b i)
  exact (creationB_commutes_rightAnnihilationN b i).symm.add_right h.star_star.symm

 theorem rightAnnihilationN_background {i : N} {J : Set N} (hi : i ∉ J)
    {T : Space B N G →L[ℂ] Space B N G} (hT : T ∈ backgroundAlgebra J) :
    Commute (star (rightCreationN i)) T := by
  induction hT using Algebra.adjoin_induction with
  | mem T hT =>
    rcases hT with ((⟨b,rfl⟩ | ⟨g,rfl⟩) | ⟨j,hj,rfl⟩)
    · exact rightAnnihilationN_commutes_semicircularB i b
    · exact (unitaryG_commutes_rightAnnihilationN g i).symm
    · have hij : i ≠ j := fun h => hi (h ▸ hj)
      show _ * _ = _ * _
      simpa [hij] using rightAnnihilationN_semicircularN (B := B) (G := G) i j
  | algebraMap z => exact (Algebra.commute_algebraMap_left z _).symm
  | add T U _ _ hT hU => exact hT.add_right hU
  | mul T U _ _ hT hU => exact hT.mul_right hU

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixHilbertSchmidt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate Matrix.Norms.L2Operator
open Finset
namespace FiniteEntropySeparation
variable {n d : ℕ}
 theorem hsNorm_add (A B : Matrix (Fin d) (Fin d) ℂ) : hsNorm (A+B) ≤ hsNorm A+hsNorm B := by
  have he : hsVector (A+B)=hsVector A+hsVector B := by ext q; rfl
  simpa only [hsNorm,he] using norm_add_le (hsVector A) (hsVector B)
 theorem hsNorm_star (A : Matrix (Fin d) (Fin d) ℂ) : hsNorm A.conjTranspose=hsNorm A := by
  apply (sq_eq_sq₀ (hsNorm_nonneg _) (hsNorm_nonneg _)).mp
  simp only [hsNorm_sq,Matrix.conjTranspose_apply,Complex.star_def,Complex.normSq_conj]
  exact sum_comm
 theorem hsNorm_mul_left (A B : Matrix (Fin d) (Fin d) ℂ) :
    hsNorm (A*B) ≤ matrixOpNorm A*hsNorm B := by
  have hcol k : (∑j,Complex.normSq ((A*B) j k)) ≤ matrixOpNorm A^2*(∑j,Complex.normSq (B j k)) := by
    let x : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 (fun j => B j k)
    have hh := (matrixOperator A).le_opNorm x
    have hn : ‖matrixOperator A x‖^2 ≤ (matrixOpNorm A*‖x‖)^2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) hh 2
    simpa [matrixOperator,Matrix.toLpLin_apply,EuclideanSpace.norm_sq_eq,Matrix.mul_apply,
      Matrix.mulVec, dotProduct, x,Complex.normSq_eq_norm_sq,mul_pow,matrixOpNorm] using hn
  have hh := sum_le_sum (fun k (_ : k∈(univ:Finset (Fin d))) => hcol k)
  rw [sum_comm] at hh
  simp only [← mul_sum] at hh
  rw [sum_comm (f := fun i j : Fin d => Complex.normSq (B j i)),← hsNorm_sq,← hsNorm_sq] at hh
  have hb := hsNorm_nonneg B
  have hab := hsNorm_nonneg (A*B)
  have ha := matrixOpNorm_nonneg A
  apply (sq_le_sq₀ hab (mul_nonneg ha hb)).mp
  simpa only [mul_pow] using hh
 theorem hsNorm_mul_right (A B : Matrix (Fin d) (Fin d) ℂ) :
    hsNorm (A*B) ≤ hsNorm A*matrixOpNorm B := by
  rw [← hsNorm_star (A*B),Matrix.conjTranspose_mul]
  have hh := hsNorm_mul_left B.conjTranspose A.conjTranspose
  rw [hsNorm_star] at hh
  have he : matrixOpNorm B.conjTranspose=matrixOpNorm B := Matrix.l2_opNorm_conjTranspose B
  rw [he,mul_comm] at hh
  exact hh
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SpectralBlockMask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset MeasureTheory ProbabilityTheory
namespace FiniteEntropySeparation
variable {p d : ℕ}
 theorem blockMask_card (f : Fin d → Fin p) :
    (blockMask f).card = p*∑j : Fin d,(univ.filter (fun k => f k=f j)).card := by
  classical
  rw [blockMask,card_filter]
  simp only [Fintype.sum_prod_type]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_last,lt_self_iff_false,false_and,ite_false,sum_const_zero,add_zero,
    Fin.val_castSucc,Fin.is_lt,true_and]
  have he : (∑j : Fin d,∑k : Fin d,if f j=f k then 1 else 0)=
      ∑j : Fin d,(univ.filter (fun k => f k=f j)).card := by
    apply sum_congr rfl
    intro j _
    simp only [card_filter,eq_comm]
  simp only [he,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
 theorem blockMask_card_le (f : Fin d → Fin p) (hf : balancedBlocks f) :
    (blockMask f).card≤2*d^2 := by
  rw [blockMask_card,mul_sum]
  calc
    _ ≤ ∑j : Fin d,2*d := sum_le_sum (fun j _ => hf (f j))
    _ = _ := by simp; ring
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.VolumetricNet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory Metric Set
open scoped ENNReal NNReal
namespace FiniteEntropySeparation
 variable {E : Type u1} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
 theorem separated_card_bound (s : Finset E) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hs : ∀ c ∈ s, ‖c‖ ≤ R) (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → ε ≤ ‖c-d‖) :
    (s.card : ℝ) ≤ (1+2*R/ε)^Module.finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : ℝ := ε/2
  let ρ : ℝ := R+δ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let A := ⋃ c ∈ s, ball c δ
  have hD : Set.Pairwise (s : Set E) (fun c d => Disjoint (ball c δ) (ball d δ)) := by
    intro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    simpa [δ] using hsep c hc d hd hcd
  have hA : A ⊆ ball (0 : E) ρ := by
    refine iUnion₂_subset fun x hx => ball_subset_ball' ?_
    rw [dist_zero_right]
    dsimp [ρ]
    linarith [hs x hx]
  have hI : (s.card : ℝ≥0∞)*ENNReal.ofReal (δ^Module.finrank ℝ E)*μ (ball 0 1) ≤
      ENNReal.ofReal (ρ^Module.finrank ℝ E)*μ (ball 0 1) := by
    calc
      _ = μ A := by
        rw [show A = ⋃ c ∈ s, ball c δ from rfl, measure_biUnion_finset hD (fun _ _ => measurableSet_ball)]
        simp only [μ.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) ρ) := measure_mono hA
      _ = _ := μ.addHaar_ball_of_pos _ hρ
  have hJ : (s.card : ℝ≥0∞)*ENNReal.ofReal (δ^Module.finrank ℝ E) ≤ ENNReal.ofReal (ρ^Module.finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos μ _ zero_lt_one).ne' measure_ball_lt_top.ne).1 hI
  have hK : (s.card : ℝ)*δ^Module.finrank ℝ E ≤ ρ^Module.finrank ℝ E := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (pow_nonneg hδ.le _)] using
      ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) hJ
  have he : (1+2*R/ε)*δ = ρ := by dsimp [δ,ρ]; field_simp; ring
  apply (mul_le_mul_iff_left₀ (pow_pos hδ _)).mp
  rw [← mul_pow, he]
  exact hK
 theorem compact_finite_net (A : Set E) (hA : IsCompact A) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hAR : ∀ x ∈ A, ‖x‖ ≤ R) :
    ∃ s : Finset E, (∀ x ∈ s, x ∈ A) ∧ (∀ x ∈ A, ∃ y ∈ s, dist x y ≤ ε) ∧
      (s.card : ℝ) ≤ (1+2*R/ε)^Module.finrank ℝ E := by
  classical
  let e : ℝ≥0 := ⟨ε,hε.le⟩
  have he : e/2 ≠ 0 := ne_of_gt (div_pos (show 0 < e from hε) (by norm_num))
  obtain ⟨N,hNA,hNfin,hNcov⟩ := Metric.exists_finite_isCover_of_isCompact (ε := (e/2 : ℝ≥0)) he hA
  have hpn : packingNumber e A ≠ ⊤ := by
    have hb := packingNumber_two_mul_le_externalCoveringNumber (e/2) A
    rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ≥0) ≠ 0)] at hb
    exact ne_top_of_le_ne_top hNfin.encard_lt_top.ne (hb.trans hNcov.externalCoveringNumber_le_encard)
  let K := maximalSeparatedSet e A
  have hKfin : K.Finite := Set.encard_ne_top_iff.mp (by simpa [K, encard_maximalSeparatedSet hpn] using hpn)
  refine ⟨hKfin.toFinset, ?_, ?_, ?_⟩
  · intro x hx; exact maximalSeparatedSet_subset (by simpa using hx)
  · intro x hx
    obtain ⟨y,hy,hxy⟩ := isCover_maximalSeparatedSet hpn hx
    refine ⟨y, by simpa using hy, ?_⟩
    exact (edist_le_coe).mp hxy
  · apply separated_card_bound _ hR hε
    · intro x hx; exact hAR x (maximalSeparatedSet_subset (by simpa using hx))
    · intro x hx y hy hxy
      have hh := isSeparated_maximalSeparatedSet (ε := e) (A := A) (by simpa using hx) (by simpa using hy) hxy
      have hh' : e < nndist x y := by simpa only [edist_nndist, ENNReal.coe_lt_coe] using hh
      have hh'' : ε < dist x y := hh'
      simpa only [dist_eq_norm] using hh''.le
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixRotationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Matrix.Norms.L2Operator
open Finset Set
namespace FiniteEntropySeparation
variable {n d : ℕ}
 theorem unitary_matrix_norm {d : ℕ} (hd : 0<d) (U : unitary (Matrix (Fin d) (Fin d) ℂ)) :
    matrixOpNorm (U:Matrix (Fin d) (Fin d) ℂ)=1 := by
  have : NeZero d := ⟨by omega⟩
  exact CStarRing.norm_coe_unitary U
 theorem hsNorm_unitary_difference (hd : 0<d) (U V : unitary (Matrix (Fin d) (Fin d) ℂ))
    (A : Matrix (Fin d) (Fin d) ℂ) :
    hsNorm (star (U:Matrix (Fin d) (Fin d) ℂ)*A*(U:Matrix (Fin d) (Fin d) ℂ)-star (V:Matrix (Fin d) (Fin d) ℂ)*A*(V:Matrix (Fin d) (Fin d) ℂ)) ≤
      2*matrixOpNorm ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ))*hsNorm A := by
  have he : star (U:Matrix (Fin d) (Fin d) ℂ)*A*(U:Matrix (Fin d) (Fin d) ℂ)-star (V:Matrix (Fin d) (Fin d) ℂ)*A*(V:Matrix (Fin d) (Fin d) ℂ) =
    star (U:Matrix (Fin d) (Fin d) ℂ)*A*((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ))+
      star ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ))*A*(V:Matrix (Fin d) (Fin d) ℂ) := by rw [star_sub]; noncomm_ring
  rw [he]
  have hU : matrixOpNorm (star (U:Matrix (Fin d) (Fin d) ℂ))=1 := by
    rw [show matrixOpNorm (star (U:Matrix (Fin d) (Fin d) ℂ))=matrixOpNorm (U:Matrix (Fin d) (Fin d) ℂ) from Matrix.l2_opNorm_conjTranspose _]
    exact unitary_matrix_norm hd U
  have hUV : matrixOpNorm (star ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ)))=
      matrixOpNorm ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ)) := Matrix.l2_opNorm_conjTranspose _
  calc
    _ ≤ hsNorm (star (U:Matrix (Fin d) (Fin d) ℂ)*A*((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ)))+
      hsNorm (star ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ))*A*(V:Matrix (Fin d) (Fin d) ℂ)) := hsNorm_add _ _
    _ ≤ (matrixOpNorm (star (U:Matrix (Fin d) (Fin d) ℂ))*hsNorm A)*matrixOpNorm ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ))+
      (matrixOpNorm (star ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ)))*hsNorm A)*matrixOpNorm (V:Matrix (Fin d) (Fin d) ℂ) := by
      apply add_le_add
      · exact (hsNorm_mul_right _ _).trans (mul_le_mul_of_nonneg_right (hsNorm_mul_left _ _) (matrixOpNorm_nonneg _))
      · exact (hsNorm_mul_right _ _).trans (mul_le_mul_of_nonneg_right (hsNorm_mul_left _ _) (matrixOpNorm_nonneg _))
    _ = _ := by rw [hU,hUV,unitary_matrix_norm hd V]; ring
 theorem rotateCoordinates_sub_norm (hd : 0<d) (U V : unitary (Matrix (Fin d) (Fin d) ℂ))
    (a : MatrixCoordinates n d) :
    ‖rotateCoordinates U a-rotateCoordinates V a‖ ≤
      2*matrixOpNorm ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ))*‖a‖ := by
  have hnn := matrixOpNorm_nonneg ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ))
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤2*matrixOpNorm ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ))*‖a‖)).mp
  rw [← hermitianChart_normSq]
  have he (i : Fin n) : hermitianMatrix (rotateCoordinates U a-rotateCoordinates V a) i = hermitianMatrix (rotateCoordinates U a) i-hermitianMatrix (rotateCoordinates V a) i := congrFun (map_sub (hermitianChart n d) _ _) i
  simp_rw [he]
  change (∑i,∑j,∑k,Complex.normSq ((hermitianMatrix (rotateCoordinates U a) i-hermitianMatrix (rotateCoordinates V a) i) j k)) ≤ _
  simp_rw [hermitianMatrix_rotate,← hsNorm_sq]
  calc
    _ ≤ ∑i,(2*matrixOpNorm ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ))*hsNorm (hermitianMatrix a i))^2 := by
      apply sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (hsNorm_nonneg _) (hsNorm_unitary_difference hd U V _) _
    _ = _ := by
      simp_rw [mul_pow,← mul_sum,hsNorm_sq,hermitianChart_normSq]
 theorem isCompact_unitary_matrix (hd : 0<d) :
    IsCompact (unitary (Matrix (Fin d) (Fin d) ℂ) : Set (Matrix (Fin d) (Fin d) ℂ)) := by
  apply (Metric.isCompact_iff_isClosed_bounded).mpr
  refine ⟨isClosed_unitary,?_⟩
  rw [Metric.isBounded_iff_subset_closedBall (0 : Matrix (Fin d) (Fin d) ℂ)]
  refine ⟨1,fun U hU => ?_⟩
  rw [Metric.mem_closedBall,dist_zero_right]
  change matrixOpNorm U≤1
  exact (unitary_matrix_norm hd ⟨U,hU⟩).le
 theorem unitary_matrix_net (hd : 0<d) {ε : ℝ} (hε : 0<ε) :
    ∃ s : Finset (unitary (Matrix (Fin d) (Fin d) ℂ)),
      (∀ U : unitary (Matrix (Fin d) (Fin d) ℂ), ∃ V∈s,matrixOpNorm ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ))≤ε) ∧
      (s.card:ℝ)≤(1+2/ε)^(2*d^2) := by
  classical
  obtain ⟨s,hs,hcover,hcard⟩ := compact_finite_net _ (isCompact_unitary_matrix hd)
    (show (0:ℝ)≤1 by norm_num) hε (fun U hU => (unitary_matrix_norm hd ⟨U,hU⟩).le)
  let g : {U // U∈s} → unitary (Matrix (Fin d) (Fin d) ℂ) := fun U => ⟨U,hs U U.property⟩
  refine ⟨Finset.univ.image g, ?_, ?_⟩
  · intro U
    obtain ⟨V,hV,hUV⟩ := hcover U U.property
    refine ⟨g ⟨V,hV⟩,mem_image.mpr ⟨⟨V,hV⟩,mem_univ _,rfl⟩,?_⟩
    change ‖(U:Matrix (Fin d) (Fin d) ℂ)-V‖≤ε
    simpa only [dist_eq_norm] using hUV
  · have he : Module.finrank ℝ (Matrix (Fin d) (Fin d) ℂ)=2*d^2 := by
      rw [Module.finrank_matrix,Complex.finrank_real_complex]
      simp only [Fintype.card_fin]
      ring
    calc
      _ ≤ (s.card:ℝ) := by exact_mod_cast (Finset.card_image_le.trans_eq (by simp))
      _ ≤ _ := by simpa [he] using hcard
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.BlockEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset Set
open scoped Matrix.Norms.L2Operator ENNReal
namespace FiniteEntropySeparation
variable {p d n : ℕ}
 theorem matrixCoordinatesOfHermitian_continuous :
    Continuous (matrixCoordinatesOfHermitian : (Fin n → Matrix (Fin d) (Fin d) ℂ) → MatrixCoordinates n d) := by
  unfold matrixCoordinatesOfHermitian
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  rintro ⟨i,j,k⟩
  dsimp only
  split_ifs <;> fun_prop
 theorem rotateCoordinates_continuous_joint :
    Continuous (fun z : unitary (Matrix (Fin d) (Fin d) ℂ) × MatrixCoordinates n d => rotateCoordinates z.1 z.2) := by
  unfold rotateCoordinates
  apply matrixCoordinatesOfHermitian_continuous.comp
  apply continuous_pi
  intro i
  exact ((continuous_subtype_val.comp continuous_fst).star.mul ((hermitianMatrix_continuous i).comp continuous_snd)).mul
    (continuous_subtype_val.comp continuous_fst)
 theorem blockEvent_isClosed (hd : 0<d) (r M : ℝ) : IsClosed (blockEvent p d r M) := by
  have : CompactSpace (unitary (Matrix (Fin d) (Fin d) ℂ)) := isCompact_iff_compactSpace.mp (isCompact_unitary_matrix hd)
  have hf (f : Fin d → Fin p) : IsClosed {a : MatrixCoordinates (p+1) d |
      ∃U : unitary (Matrix (Fin d) (Fin d) ℂ),r≤‖coordinateMask (blockMask f) (rotateCoordinates U a)‖} := by
    have hh : IsClosed {z : unitary (Matrix (Fin d) (Fin d) ℂ) × MatrixCoordinates (p+1) d |
        r≤‖coordinateMask (blockMask f) (rotateCoordinates z.1 z.2)‖} :=
      isClosed_le continuous_const ((coordinateMask_continuous _).comp rotateCoordinates_continuous_joint).norm
    convert isClosedMap_snd_of_compactSpace _ hh using 1
    ext a
    simp only [Set.mem_ofPred_eq,Set.mem_image,Prod.exists]
    constructor
    · rintro ⟨U,hU⟩; exact ⟨U,a,hU,rfl⟩
    · rintro ⟨U,b,hU,rfl⟩; exact ⟨U,hU⟩
  have he : blockEvent p d r M = {a | ‖a‖≤M} ∩
      ⋃ f : Fin d → Fin p, ⋃ (_ : balancedBlocks f),
        {a | ∃U : unitary (Matrix (Fin d) (Fin d) ℂ),r≤‖coordinateMask (blockMask f) (rotateCoordinates U a)‖} := by
    ext a; simp [blockEvent]
  rw [he]
  exact (isClosed_le continuous_norm continuous_const).inter (isClosed_iUnion_of_finite (fun f => isClosed_iUnion_of_finite (fun _ => hf f)))
 theorem blockEvent_subset_net (hd : 0<d) {r M ε : ℝ} (hε : 0≤ε)
    (s : Finset (unitary (Matrix (Fin d) (Fin d) ℂ)))
    (hs : ∀U : unitary (Matrix (Fin d) (Fin d) ℂ),∃V∈s,matrixOpNorm ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ))≤ε) :
    blockEvent p d r M ⊆ ⋃ f : Fin d → Fin p, ⋃ (_ : balancedBlocks f), ⋃ V∈s,
      {a | r-2*ε*M≤‖coordinateMask (blockMask f) (rotateCoordinates V a)‖} := by
  intro a ha
  obtain ⟨haM,f,hf,U,hU⟩ := ha
  obtain ⟨V,hV,hUV⟩ := hs U
  refine mem_iUnion.mpr ⟨f,mem_iUnion.mpr ⟨hf,mem_iUnion.mpr ⟨V,mem_iUnion.mpr ⟨hV,?_⟩⟩⟩⟩
  have hh := coordinateMask_norm_sub (blockMask f) (rotateCoordinates U a) (rotateCoordinates V a)
  have hr := rotateCoordinates_sub_norm hd U V a
  have hb : 2*matrixOpNorm ((U:Matrix (Fin d) (Fin d) ℂ)-(V:Matrix (Fin d) (Fin d) ℂ))*‖a‖≤2*ε*M := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left hUV (by norm_num)) haM (norm_nonneg _) (by positivity)
  have hh' := (abs_le.mp (hh.trans (hr.trans hb))).2
  dsimp at *
  linarith
 theorem normalLaw_rotated_mask_tail {s r : ℝ} (hs : 0<s) (hr : 0≤r)
    (f : Fin d → Fin p) (U : unitary (Matrix (Fin d) (Fin d) ℂ)) :
    (normalLaw s) {a | r≤‖coordinateMask (blockMask f) (rotateCoordinates U a)‖} ≤
      ENNReal.ofReal (Real.exp (-r^2/(4*s))*Real.sqrt 2^(blockMask f).card) := by
  have hm := normalLaw_measurePreserving s (rotateLinearIsometryEquiv (n := p+1) U)
  have hE : MeasurableSet {a : MatrixCoordinates (p+1) d | r≤‖coordinateMask (blockMask f) a‖} :=
    (isClosed_le continuous_const (coordinateMask_continuous _).norm).measurableSet
  have he := hm.measure_preimage hE.nullMeasurableSet
  change (normalLaw s) {a | r≤‖coordinateMask (blockMask f) (rotateCoordinates U a)‖} = _ at he
  rw [he]
  exact normalLaw_coordinateMask_tail _ hs hr
 theorem blockEvent_gaussian_bound (hd : 0<d) {s r M ε : ℝ} (hs : 0<s) (hε : 0<ε)
    (hr : 0≤r-2*ε*M) :
    (normalLaw s) (blockEvent p d r M) ≤ ENNReal.ofReal
      ((p:ℝ)^d*(1+2/ε)^(2*d^2)*Real.exp (-(r-2*ε*M)^2/(4*s))*Real.sqrt 2^(2*d^2)) := by
  classical
  obtain ⟨S,hS,hcard⟩ := unitary_matrix_net hd hε
  have hsub := blockEvent_subset_net (p := p) (r := r) (M := M) hd hε.le S hS
  let K : ℝ := Real.exp (-(r-2*ε*M)^2/(4*s))*Real.sqrt 2^(2*d^2)
  have hK : 0≤K := by dsimp [K]; positivity
  have hbound (f : Fin d → Fin p) (hf : balancedBlocks f) (V : unitary (Matrix (Fin d) (Fin d) ℂ)) :
      (normalLaw s) {a | r-2*ε*M≤‖coordinateMask (blockMask f) (rotateCoordinates V a)‖}≤ENNReal.ofReal K := by
    apply (normalLaw_rotated_mask_tail hs hr f V).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact pow_le_pow_right₀ (by nlinarith [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num),Real.sqrt_nonneg (2:ℝ)] : (1:ℝ)≤Real.sqrt 2) (blockMask_card_le f hf)
  calc
    _ ≤ ∑f : Fin d → Fin p, ∑V∈S,ENNReal.ofReal K := by
      apply (measure_mono hsub).trans
      apply (measure_iUnion_fintype_le _ _).trans
      apply sum_le_sum
      intro f _
      by_cases hf : balancedBlocks f
      · have he : (⋃ (_ : balancedBlocks f), ⋃ V∈S, {a : MatrixCoordinates (p+1) d | r-2*ε*M≤‖coordinateMask (blockMask f) (rotateCoordinates V a)‖}) = ⋃ V∈S, {a : MatrixCoordinates (p+1) d | r-2*ε*M≤‖coordinateMask (blockMask f) (rotateCoordinates V a)‖} := by ext a; simp [hf]
        rw [he]
        exact (measure_biUnion_finset_le S _).trans (sum_le_sum (fun V _ => hbound f hf V))
      · simp [hf]
    _ = ENNReal.ofReal ((p:ℝ)^d*(S.card:ℝ)*K) := by
      simp only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_fun,Fintype.card_fin]
      simp only [ENNReal.ofReal_mul (show 0≤(p:ℝ)^d by positivity), ENNReal.ofReal_pow (show (0:ℝ)≤p by positivity), ENNReal.ofReal_natCast, Nat.cast_pow, ENNReal.ofReal_mul (show (0:ℝ)≤S.card by positivity), mul_assoc]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by positivity : 0≤(p:ℝ)^d)) hK
      simpa [K,mul_assoc] using hh
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.WordSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type u1}

 theorem conv_sum_splits (f g : Series α) (w : List α) :
    conv f g w = ∑ k ∈ range (w.length+1), f (w.take k) * g (w.drop k) := by
  induction w generalizing f with
  | nil => simp
  | cons a w ih =>
    rw [conv_cons, ih, List.length_cons]
    conv_rhs => rw [sum_range_succ']
    simp only [List.take_zero, List.drop_zero, List.take_succ_cons, List.drop_succ_cons, deriv_apply]
    ring

@[simp] theorem conv_zero_left (f : Series α) : conv 0 f = 0 := by
  funext w
  simp [conv_sum_splits]
@[simp] theorem conv_zero_right (f : Series α) : conv f 0 = 0 := by
  funext w
  simp [conv_sum_splits]

@[simp] theorem conv_unit_left (f : Series α) : conv unit f = f := by
  funext w
  cases w <;> simp [conv, deriv_unit]

theorem length_induction {P : List α → Prop} (w : List α)
    (h : ∀ w, (∀ v, v.length < w.length → P v) → P w) : P w :=
  (measure List.length).wf.induction w h

 theorem subst_cons (M f : Series α) (a : α) (w : List α) :
    subst M f (a::w) = conv M (subst M (deriv a f)) w := by
  rw [subst, conv_sum_splits]

 theorem subst_smul (M f : Series α) (c : ℂ) : subst M (c • f) = c • subst M f := by
  funext w
  induction w using length_induction generalizing f with
  | h w ih =>
    cases w with
    | nil => simp
    | cons a w =>
      simp only [subst, Pi.smul_apply, smul_eq_mul]
      simp_rw [show deriv a (c • f) = c • deriv a f from rfl]
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      rw [ih _ (by simp)]
      simp [mul_left_comm]

@[simp] theorem subst_zero (M : Series α) : subst M 0 = 0 := by
  have h := subst_smul M 0 0
  simpa using h
@[simp] theorem subst_unit (M : Series α) : subst M unit = unit := by
  funext w
  cases w with
  | nil => simp
  | cons a w => simp [subst_cons]

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SemicircularSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type} [DecidableEq α]

 theorem deriv_letter (i j : α) : deriv j (letter i) = if j=i then unit else 0 := by
  funext w
  cases w with
  | nil => by_cases h : j=i <;> simp [deriv, letter, unit, h]
  | cons a w => cases w <;> by_cases h : j=i <;> simp [deriv, letter, unit, h]
 theorem subst_letter_cons (M : Series α) (i j : α) (w : List α) :
    subst M (letter i) (j::w) = if j=i then M w else 0 := by
  rw [subst_cons, deriv_letter]
  split_ifs <;> simp
 theorem deriv_quadratic (i : α) : deriv i (quadratic : Series α) = letter i := by
  funext w
  cases w with
  | nil => rfl
  | cons a w => cases w <;> rfl

 theorem quadratic_subst_derivative {n : ℕ} (M : Series (Fin n)) (i : Fin n) (w : List (Fin n)) :
    subst M quadratic (i::w) = ∑ r : Fin w.length, if w[r.val] = i then
      M (w.take r.val) * M (w.drop (r.val+1)) else 0 := by
  rw [subst_cons, deriv_quadratic, conv_sum_splits, sum_range_succ]
  simp only [List.take_length, List.drop_length, subst_nil, letter_nil, mul_zero, add_zero]
  rw [← Fin.sum_univ_eq_sum_range (fun k => M (w.take k) * subst M (letter i) (w.drop k))]
  apply sum_congr rfl
  intro k hk
  rw [List.drop_eq_getElem_cons k.isLt, subst_letter_cons]
  split_ifs <;> simp

 theorem fockMoments_eq (p : ℕ) : fockMoments p = unit + subst (fockMoments p) quadratic := by
  funext w
  cases w with
  | nil => simp [fockMoments]
  | cons i w =>
    simp only [Pi.add_apply, unit_cons, zero_add, quadratic_subst_derivative]
    exact Fock.semicircular_integration_by_parts i w

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.Signal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation

theorem norm_sum_sq_orthogonal {H : Type u1} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type u2} [Fintype ι] (x : ι → H)
    (h : ∀ i j, i ≠ j → inner ℂ (x i) (x j) = 0) :
    ‖∑ i, x i‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  classical
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), sum_inner]
  have hs (i : ι) : inner ℂ (x i) (∑ j, x j) = inner ℂ (x i) (x i) := by
    rw [inner_sum]
    exact Finset.sum_eq_single i (fun j _ hji => h i j (Ne.symm hji)) (by simp)
  simp_rw [hs]
  simp only [map_sum, ← norm_sq_eq_re_inner (𝕜 := ℂ)]

namespace FreeTensor

variable {B N A : Type} [DecidableEq B] [DecidableEq N] [AddCommGroup A]
  [Fintype A] [DecidableEq A]

omit [Fintype A] in
 theorem groupUnitary_add (a b : A) :
    groupUnitary (B := B) (N := N) (a + b) = groupUnitary a * groupUnitary b :=
  unitaryG_mul _ _

 theorem groupUnitary_mul_characterProjection (a : A) (ψ : AddChar A ℂ) :
    groupUnitary (B := B) (N := N) a * characterProjection ψ = ψ a • characterProjection ψ := by
  unfold characterProjection
  rw [mul_smul_comm, Finset.mul_sum, smul_comm (ψ a)]
  congr 1
  rw [Finset.smul_sum]
  apply Fintype.sum_equiv (Equiv.addLeft a)
  intro b
  rw [mul_smul_comm]
  change ψ (-b) • (groupUnitary (B := B) (N := N) a * groupUnitary b) =
    ψ a • (ψ (-(a + b)) • groupUnitary (a + b))
  simp only [← groupUnitary_add, smul_smul]
  congr 1
  rw [neg_add, AddChar.map_add_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, add_neg_cancel]
  simp

 theorem characterProjection_mul (ψ φ : AddChar A ℂ) :
    characterProjection (B := B) (N := N) ψ * characterProjection φ =
      if ψ = φ then characterProjection ψ else 0 := by
  classical
  rw [characterProjection, smul_mul_assoc, Finset.sum_mul]
  simp only [smul_mul_assoc, groupUnitary_mul_characterProjection, smul_smul,
    ← Finset.sum_smul]
  have hs : (∑ a : A, ψ (-a) * φ a) = if ψ = φ then (Fintype.card A : ℂ) else 0 := by
    have he (a : A) : ψ (-a) * φ a = (-ψ + φ) a := by
      simp [AddChar.add_apply, AddChar.neg_apply, AddChar.map_neg_eq_inv]
    simp_rw [he]
    rw [AddChar.sum_eq_ite]
    congr 1
    exact propext neg_add_eq_zero
  rw [hs]
  by_cases h : ψ = φ
  · subst φ
    simp [Fintype.card_ne_zero, characterProjection]
  · simp only [h, ↓reduceIte, mul_zero,
      zero_smul ℂ (characterProjection (B := B) (N := N) φ)]

 theorem sum_characterProjection :
    ∑ ψ : AddChar A ℂ, characterProjection (B := B) (N := N) ψ = 1 := by
  classical
  unfold characterProjection
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp only [← Finset.sum_smul, AddChar.sum_apply_eq_ite, neg_eq_zero]
  simp [smul_smul, Fintype.card_ne_zero]

omit [Fintype A] in
 theorem trace_groupUnitary (a : A) :
    trace (tracialVector B N (Multiplicative A)) (groupUnitary a) = if a = 0 then 1 else 0 := by
  rw [trace_unitaryG]
  rfl

 theorem trace_characterProjection (ψ : AddChar A ℂ) :
    trace (tracialVector B N (Multiplicative A)) (characterProjection ψ) =
      (Fintype.card A : ℂ)⁻¹ := by
  rw [characterProjection, trace_smul, trace_sum]
  simp [trace_smul, trace_groupUnitary]

 theorem spectralSignal_selfAdjoint (y : AddChar A ℂ → ℝ) :
    IsSelfAdjoint (spectralSignal (B := B) (N := N) y) := by
  show star _ = _
  simp [spectralSignal,
    star_sum (R := Space B N (Multiplicative A) →L[ℂ] Space B N (Multiplicative A))]

 theorem spectralSignal_pow (y : AddChar A ℂ → ℝ) (k : ℕ) :
    spectralSignal (B := B) (N := N) y ^ k = ∑ ψ, ((y ψ : ℂ) ^ k) • characterProjection ψ := by
  classical
  induction k with
  | zero => simpa using (sum_characterProjection (B := B) (N := N) (A := A)).symm
  | succ k ih =>
    rw [pow_succ, ih, spectralSignal, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ψ _
    rw [smul_mul_assoc, Finset.mul_sum]
    simp only [mul_smul_comm, characterProjection_mul]
    simp only [smul_ite, smul_zero (M := ℂ) (A := Space B N (Multiplicative A) →L[ℂ] Space B N (Multiplicative A)),
      Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte, smul_smul, pow_succ]

 theorem trace_spectralSignal_pow (y : AddChar A ℂ → ℝ) (k : ℕ) :
    trace (tracialVector B N (Multiplicative A)) (spectralSignal y ^ k) =
      (Fintype.card A : ℂ)⁻¹ * ∑ ψ, (y ψ : ℂ) ^ k := by
  rw [spectralSignal_pow, trace_sum]
  simp only [trace_smul, trace_characterProjection, ← Finset.sum_mul]
  exact mul_comm _ _

 theorem characterProjection_orthogonal (ψ φ : AddChar A ℂ) (h : ψ ≠ φ)
    (v w : Space B N (Multiplicative A)) :
    inner ℂ (characterProjection ψ v) (characterProjection φ w) = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
    star_characterProjection, ← mul_apply_eq_comp, characterProjection_mul, ite_eq_right (Ne.symm h)]
  simp

 theorem spectralSignal_norm_le (y : AddChar A ℂ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hy : ∀ ψ, |y ψ| ≤ R) : ‖spectralSignal (B := B) (N := N) y‖ ≤ R := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ hR
  intro x
  have hx : ∑ ψ : AddChar A ℂ, characterProjection ψ x = x := by
    simpa only [sum_apply, one_apply_eq_self] using
      congrArg (fun T : Space B N (Multiplicative A) →L[ℂ] Space B N (Multiplicative A) => T x)
        (sum_characterProjection (B := B) (N := N) (A := A))
  have hn : ∑ ψ : AddChar A ℂ, ‖characterProjection ψ x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← norm_sum_sq_orthogonal _ (fun ψ φ h => characterProjection_orthogonal ψ φ h x x), hx]
  have hn' : ‖spectralSignal (B := B) (N := N) y x‖ ^ 2 =
      ∑ ψ : AddChar A ℂ, |y ψ| ^ 2 * ‖characterProjection ψ x‖ ^ 2 := by
    simp only [spectralSignal, sum_apply, smul_apply]
    rw [norm_sum_sq_orthogonal _ (by
      intro ψ φ h
      simp [characterProjection_orthogonal ψ φ h x x])]
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have hsq : ‖spectralSignal (B := B) (N := N) y x‖ ^ 2 ≤ R ^ 2 * ‖x‖ ^ 2 := by
    rw [hn', ← hn, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ψ _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (abs_nonneg _) (hy ψ) 2
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR (norm_nonneg x))).mp
  simpa only [mul_pow] using hsq

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TensorLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

omit [Group G] in
theorem signalSlice_semicircular [Group G] (g : G) (b : B) :
    (semicircularB b).comp (signalSlice (N := N) g) =
      (signalSlice g).comp (Fock.semicircular b) := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro w
  apply ContinuousLinearMap.ext
  intro z
  change semicircularB b (signalSlice g (lp.single 2 w z)) =
    signalSlice g (Fock.semicircular b (lp.single 2 w z))
  rw [signalSlice_single]
  cases w with
  | nil => simp [semicircularB, creationB_single, annihilationB_single, removeB, leftB]
  | cons c w =>
    simp only [semicircularB, add_apply, creationB_single, annihilationB_single, removeB,
      Fock.semicircular_single_cons, map_add, signalSlice_single, leftB]
    by_cases h : b = c <;> simp [h]

 theorem signalSlice_word (g : G) (w : List B) :
    ((w.map (semicircularB (N := N) (G := G))).prod).comp (signalSlice g) =
      (signalSlice g).comp ((w.map Fock.semicircular).prod) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    apply ContinuousLinearMap.ext
    intro x
    have hi := congrArg (fun T : Fock.Space B →L[ℂ] Space B N G => T x) ih
    have hc := congrArg (fun T : Fock.Space B →L[ℂ] Space B N G =>
      T ((w.map Fock.semicircular).prod x)) (signalSlice_semicircular (N := N) g b)
    simp only [ContinuousLinearMap.comp_apply] at hi hc
    simpa only [ContinuousLinearMap.comp_apply, List.map_cons, List.prod_cons,
      mul_apply_eq_comp, hi] using hc

 theorem signalSlice_vacuum_coefficient (g : G) (x : Fock.Space B) :
    inner ℂ (basis (empty : Word B N G)) (signalSlice g x) =
      if g = 1 then inner ℂ (Fock.basisVector []) x else 0 := by
  have h : (innerSL ℂ (basis (empty : Word B N G))).comp (signalSlice g) =
      if g = 1 then innerSL ℂ (Fock.basisVector ([] : List B)) else 0 := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    intro v
    apply ContinuousLinearMap.ext
    intro z
    by_cases hg : g = 1 <;> by_cases hv : v = [] <;>
      simp [hg, hv, basis, empty, Fock.basisVector, lp.inner_single_left, lp.single_apply, eq_comm]
  have hx := congrArg (fun f : Fock.Space B →L[ℂ] ℂ => f x) h
  by_cases hg : g = 1 <;> simpa [hg] using hx

theorem tensor_word_moment (w : List B) (g : G) :
    trace (tracialVector B N G) ((w.map semicircularB).prod * unitaryG g) =
      trace (Fock.tracialVector B) ((w.map Fock.semicircular).prod) *
        (if g = 1 then 1 else 0) := by
  change inner ℂ (basis (empty : Word B N G))
    (((w.map (semicircularB (N := N) (G := G))).prod * unitaryG (B := B) (N := N) g) (basis empty)) = _
  rw [mul_apply_eq_comp, unitaryG_basis]
  have hv : basis (leftG g (empty : Word B N G)) = signalSlice g (Fock.basisVector []) := by
    simp [leftG, empty]
  rw [hv, ← ContinuousLinearMap.comp_apply, signalSlice_word,
    ContinuousLinearMap.comp_apply, signalSlice_vacuum_coefficient]
  by_cases hg : g = 1 <;> simp [hg, trace, Fock.tracialVector]

 theorem unitaryG_commutes_creationB (g : G) (b : B) :
    Commute (unitaryG (N := N) g) (creationB b) := by
  apply LabelHilbert.lift_commute
  intro w
  rfl

 theorem unitaryG_commutes_semicircularB (g : G) (b : B) :
    Commute (unitaryG (N := N) g) (semicircularB b) := by
  apply (unitaryG_commutes_creationB g b).add_right
  simpa using (unitaryG_commutes_creationB (N := N) g⁻¹ b).star_star

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.NoiseTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G]

variable [DecidableEq B] [DecidableEq N] [DecidableEq G]

 theorem noise_basis_orthonormal : Orthonormal ℂ (fun w : List N =>
    basis (noiseWord (B := B) (G := G) w)) := by
  rw [orthonormal_iff_ite]
  intro v w
  by_cases h : v = w
  · subst w
    simp [basis, ]
  · have h' : noiseWord (B := B) (G := G) v ≠ noiseWord w :=
      fun hh => h (noiseWord_injective hh)
    simp [basis, lp.inner_single_left, lp.single_apply, h, h']

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.EquidiscreteSignal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation

 theorem equidiscreteAtom_abs_le {p : ℕ} (hp : 2 ≤ p) (l : Fin p) :
    |equidiscreteAtom p l| ≤ 1 := by
  have hd : 0 < (p : ℝ) - 1 := by
    have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hl : (l.val : ℝ) ≤ (p : ℝ) - 1 := by
    have hn : l.val + 1 ≤ p := l.isLt
    exact_mod_cast (show (l.val : ℤ) ≤ (p : ℤ) - 1 by omega)
  rw [abs_le, equidiscreteAtom]
  constructor
  · have h := div_nonneg (show 0 ≤ 2 * (l.val : ℝ) by positivity) hd.le
    linarith
  · have h : 2 * (l.val : ℝ) / ((p : ℝ) - 1) ≤ 2 := (div_le_iff₀ hd).mpr (by linarith)
    linarith

namespace FreeTensor
variable {B N : Type} [DecidableEq B] [DecidableEq N] (p : ℕ) [NeZero p]

 theorem equidiscreteSignal_selfAdjoint : IsSelfAdjoint (equidiscreteSignal (B := B) (N := N) p) :=
  spectralSignal_selfAdjoint _

 theorem equidiscreteSignal_norm_le (hp : 2 ≤ p) :
    ‖equidiscreteSignal (B := B) (N := N) p‖ ≤ 1 :=
  spectralSignal_norm_le _ 1 zero_le_one (fun _character => equidiscreteAtom_abs_le hp _)

 theorem equidiscreteSignal_moments (k : ℕ) :
    trace (tracialVector B N (Multiplicative (ZMod p))) (equidiscreteSignal p ^ k) =
      (p : ℂ)⁻¹ * ∑ l : Fin p, (equidiscreteAtom p l : ℂ) ^ k := by
  rw [equidiscreteSignal, trace_spectralSignal_pow]
  simp only [ZMod.card]
  congr 1
  exact (dualIndex p).sum_comp (fun l => (equidiscreteAtom p l : ℂ) ^ k)

 theorem characterProjection_mem_background {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (J : Set N) (ψ : AddChar A ℂ) :
    characterProjection (B := B) (N := N) ψ ∈ backgroundAlgebra J := by
  apply (backgroundAlgebra J).smul_mem
  apply (backgroundAlgebra J).sum_mem
  intro a _
  apply (backgroundAlgebra J).smul_mem
  exact Algebra.subset_adjoin (Or.inl (Or.inr ⟨Multiplicative.ofAdd a,rfl⟩))

 theorem equidiscreteSignal_mem_background (J : Set N) :
    equidiscreteSignal (B := B) (N := N) p ∈ backgroundAlgebra J := by
  apply (backgroundAlgebra J).sum_mem
  intro ψ _
  exact (backgroundAlgebra J).smul_mem (characterProjection_mem_background J ψ) _

 theorem characterProjection_commutes_B {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (ψ : AddChar A ℂ) (b : B) :
    Commute (characterProjection (B := B) (N := N) ψ) (semicircularB b) := by
  apply Commute.smul_left
  apply Commute.sum_left
  intro a _
  exact (unitaryG_commutes_semicircularB (Multiplicative.ofAdd a) b).smul_left _

 theorem equidiscreteSignal_commutes_B (b : B) :
    Commute (equidiscreteSignal (B := B) (N := N) p) (semicircularB b) := by
  apply Commute.sum_left
  intro ψ _
  exact (characterProjection_commutes_B ψ b).smul_left _

 theorem tensor_characterProjection_moment {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (w : List B) (ψ : AddChar A ℂ) :
    trace (tracialVector B N (Multiplicative A))
      ((w.map semicircularB).prod * characterProjection ψ) =
      trace (Fock.tracialVector B) ((w.map Fock.semicircular).prod) * (Fintype.card A : ℂ)⁻¹ := by
  simp only [characterProjection, mul_smul_comm, Finset.mul_sum, trace_smul, trace_sum,
    groupUnitary, tensor_word_moment]
  have hi (a : A) : (Multiplicative.ofAdd a = (1 : Multiplicative A)) ↔ a = 0 := Iff.rfl
  simp only [hi]
  simp
  ring

 theorem tensor_equidiscrete_moment (w : List B) (k : ℕ) :
    trace (tracialVector B N (Multiplicative (ZMod p)))
      ((w.map semicircularB).prod * equidiscreteSignal p ^ k) =
      trace (Fock.tracialVector B) ((w.map Fock.semicircular).prod) *
        ((p : ℂ)⁻¹ * ∑ l : Fin p, (equidiscreteAtom p l : ℂ) ^ k) := by
  rw [equidiscreteSignal, spectralSignal_pow, Finset.mul_sum, trace_sum]
  simp only [mul_smul_comm, trace_smul, tensor_characterProjection_moment, ZMod.card]
  rw [← Finset.sum_mul]
  have hs := (dualIndex p).sum_comp (fun l => (equidiscreteAtom p l : ℂ) ^ k)
  change _ = _ at hs
  rw [hs]
  ring

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.ActualTuple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

omit [Group G] in
theorem semicircularB_selfAdjoint [Group G] (b : B) : IsSelfAdjoint (semicircularB (N := N) (G := G) b) :=
  IsSelfAdjoint.add_star_self (creationB (N := N) (G := G) b)
 theorem semicircularN_selfAdjoint (i : N) : IsSelfAdjoint (semicircularN (B := B) (G := G) i) :=
  IsSelfAdjoint.add_star_self (creationN (B := B) (G := G) i)

 theorem semicircularB_mem_background (J : Set N) (b : B) :
    semicircularB (N := N) (G := G) b ∈ backgroundAlgebra J :=
  Algebra.subset_adjoin (Or.inl (Or.inl ⟨b,rfl⟩))

 theorem heatTuple_selfAdjoint {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {n : ℕ} (X S : Fin n → H →L[ℂ] H)
    (hX : ∀ i, IsSelfAdjoint (X i)) (hS : ∀ i, IsSelfAdjoint (S i)) (u : ℝ) (i : Fin n) :
    IsSelfAdjoint (heatTuple X S u i) := by
  change star (X i + (Real.sqrt u : ℂ) • S i) = _
  simp only [star_add, star_smul, Complex.star_def, Complex.conj_ofReal, (hX i).star_eq,
    (hS i).star_eq, heatTuple]

end FreeTensor

namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]

omit [NeZero p] in
theorem initialIndex_injective [NeZero p] : Function.Injective (initialIndex p) := Fin.castAdd_injective (p+1) (p+1)

omit [NeZero p] in
theorem auxiliaryIndex_injective [NeZero p] : Function.Injective (auxiliaryIndex p) := Fin.natAdd_injective (p+1) (p+1)

omit [NeZero p] in
theorem auxiliaryIndex_fresh [NeZero p] (i : Fin (p+1)) : auxiliaryIndex p i ∉ oldNoise p := by
  rintro ⟨j,h⟩
  have hv := congrArg Fin.val h
  simp only [initialIndex, auxiliaryIndex, Fin.val_castAdd, Fin.val_natAdd] at hv
  have hj := j.isLt
  omega

 theorem C_selfAdjoint (i : Fin (p+1)) : IsSelfAdjoint (C p i) := by
  induction i using Fin.lastCases with
  | last => rw [C_last]; exact equidiscreteSignal_selfAdjoint p
  | cast i => rw [C_castSucc]; exact semicircularB_selfAdjoint i

 theorem C_mem_background (J : Set (Fin ((p+1)+(p+1)))) (i : Fin (p+1)) :
    C p i ∈ backgroundAlgebra J := by
  induction i using Fin.lastCases with
  | last => rw [C_last]; exact equidiscreteSignal_mem_background p J
  | cast i => rw [C_castSucc]; exact semicircularB_mem_background J i

 theorem X_selfAdjoint (h : ℝ) (i : Fin (p+1)) : IsSelfAdjoint (X p h i) :=
  heatTuple_selfAdjoint (C p) (initialNoise p) (C_selfAdjoint p)
    (fun _index => semicircularN_selfAdjoint _) h i

omit [NeZero p] in
theorem auxiliaryNoise_selfAdjoint [NeZero p] (i : Fin (p+1)) : IsSelfAdjoint (auxiliaryNoise p i) :=
  semicircularN_selfAdjoint _

end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixHeatLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace FiniteEntropySeparation
variable {n d : ℕ}
 theorem integral_matrixHeatLaw (μ : Measure (MatrixCoordinates n d)) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0<s) (hd : 0<d) (f : MatrixCoordinates n d → ℝ) :
    (∫x,f x ∂matrixHeatLaw μ s) = ∫x,smoothedDensity μ (s/d) x*f x := by
  have hp : ∀x,0 ≤ smoothedDensity μ (s/d) x := fun x => integral_nonneg (fun y => (normalKernel_pos _ _).le)
  rw [matrixHeatLaw,integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (hp _),smul_eq_mul]
  · exact ENNReal.measurable_ofReal.comp (smoothedDensity_continuous μ (div_pos hs (by exact_mod_cast hd))).measurable
  · exact ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SpectralTestFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset Filter
open scoped Topology ComplexConjugate
namespace FiniteEntropySeparation
variable {n d : ℕ}
 theorem matrixMoment_second_hs (a : MatrixCoordinates n d) (i : Fin n) :
    (matrixMoment a [i,i]).re=(d:ℝ)⁻¹*hsNorm (hermitianMatrix a i)^2 := by
  rw [hsNorm_sq,← trace_conjTranspose_mul_re,(hermitianMatrix_isHermitian a i).eq]
  simp [matrixMoment,← Complex.ofReal_natCast,← Complex.ofReal_inv]
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SignalSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation
open Finset FreeSeries

section Product
variable {α A : Type} [DecidableEq α] [Monoid A]
 theorem option_word_product (B : α → A) (Y : A) (h : ∀ i, Commute Y (B i)) (w : List (Option α)) :
    (w.map (optionTuple B Y)).prod = ((w.filterMap id).map B).prod * Y^(w.count none) := by
  induction w with
  | nil => simp
  | cons a w ih =>
    cases a with
    | none =>
      simp only [List.map_cons, List.prod_cons, optionTuple, List.filterMap_cons, id_eq, ih]
      have hc := Commute.list_prod_right ((w.filterMap id).map B) Y (by
        intro x hx
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
        exact h i)
      simp only [List.count_cons_self]
      change Y * (((w.filterMap id).map B).prod * Y ^ w.count none) = _
      rw [← mul_assoc, hc.eq, mul_assoc, pow_succ']
      rfl
    | some i => simp [optionTuple, ih, mul_assoc]
end Product

namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]
 theorem signal_option_product (w : List (Option (Fin p))) :
    wordEval (C p) (w.map (optionFin p)) =
      ((w.filterMap id).map (semicircularB (N := Fin ((p+1)+(p+1))) (G := Multiplicative (ZMod p)))).prod *
        equidiscreteSignal p ^ (w.count none) := by
  unfold wordEval
  rw [List.map_map]
  have hf : (fun a => C p (optionFin p a)) = optionTuple semicircularB (equidiscreteSignal p) := by
    funext a
    cases a <;> simp [optionTuple]
  change (w.map (fun a => C p (optionFin p a))).prod = _
  rw [hf]
  exact option_word_product _ _ (equidiscreteSignal_commutes_B p) w
 theorem signal_option_moments (w : List (Option (Fin p))) :
    signalMoments p (w.map (optionFin p)) = fockMoments p (w.filterMap id) *
      trace (τ p) (equidiscreteSignal p ^ (w.count none)) := by
  unfold signalMoments wordMoment
  rw [signal_option_product, tensor_equidiscrete_moment, equidiscreteSignal_moments]
  rfl
end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.WickTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 theorem inner_commutatorKernel {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (i : Fin n) (w : List (Fin n)) (v : H) :
    inner ℂ v (commutatorKernel (vacuumRankOne τ) X i w τ.vacuum) =
      ∑ r : Fin w.length, if w[r.val] = i then
        inner ℂ v (wordEval X (w.take r.val) τ.vacuum) *
          wordMoment τ X (w.drop (r.val + 1)) else 0 := by
  rw [commutatorKernel, sum_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs
  · simp only [vacuumRankOne, mul_apply_eq_comp, InnerProductSpace.rankOne_apply,
      map_smul, inner_smul_right, wordMoment, trace]
    exact mul_comm _ _
  · simp

namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]

 theorem rightAnnihilationN_heat {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ j, X j ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ j, σ j ∉ J)
    (u : ℝ) (i j : Fin n) :
    star (rightCreationN (σ i)) * heatTuple X (fun k => semicircularN (σ k)) u j =
      heatTuple X (fun k => semicircularN (σ k)) u j * star (rightCreationN (σ i)) +
        if j = i then (Real.sqrt u : ℂ) • vacuumRankOne (tracialVector B N G) else 0 := by
  change _ * (X j + (Real.sqrt u : ℂ) • semicircularN (σ j)) = _
  rw [mul_add, mul_smul_comm, (rightAnnihilationN_background (hs i) (hX j)).eq,
    rightAnnihilationN_semicircularN]
  dsimp [heatTuple]
  by_cases hij : j = i
  · subst j
    simp only [ite_true, add_mul, smul_mul_assoc, add_assoc]
    congr 1
    exact smul_add _ _ _
  · have hneq : σ i ≠ σ j := fun h => hij (hσ h).symm
    simp only [ite_eq_right hij, ite_eq_right hneq, add_zero, add_mul, smul_mul_assoc]

theorem wick_testing {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ j, X j ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ j, σ j ∉ J)
    (u : ℝ) (js w : List (Fin n)) :
    inner ℂ (basis (noiseWord ((js.map σ).reverse)))
      (wordEval (heatTuple X (fun k => semicircularN (σ k)) u) w
        (tracialVector B N G).vacuum) =
      (Real.sqrt u : ℂ) ^ js.length *
        reverseDerivativeMoment (tracialVector B N G)
          (heatTuple X (fun k => semicircularN (σ k)) u) js w := by
  let Z := heatTuple X (fun k => semicircularN (σ k)) u
  change inner ℂ _ (wordEval Z w _) = _ * reverseDerivativeMoment _ Z js w
  induction js generalizing w with
  | nil => simp [reverseDerivativeMoment, wordMoment, trace, tracialVector]
  | cons i js ih =>
    have hvec : basis (noiseWord (((i :: js).map σ).reverse)) =
        rightCreationN (σ i) (basis (noiseWord ((js.map σ).reverse)) : Space B N G) := by
      simp only [List.map_cons, List.reverse_cons, basis, rightCreationN_single, rightN_noiseWord]
    rw [hvec, ← ContinuousLinearMap.adjoint_inner_right,
      ← ContinuousLinearMap.star_eq_adjoint]
    have hc := commutator_word (vacuumRankOne (tracialVector B N G))
      (star (rightCreationN (σ i))) Z i (Real.sqrt u : ℂ)
      (rightAnnihilationN_heat J X hX σ hσ hs u i) w
    have hc' := congrArg (fun T : Space B N G →L[ℂ] Space B N G =>
      T (tracialVector B N G).vacuum) hc
    have hz : star (rightCreationN (σ i)) (tracialVector B N G).vacuum = 0 := by
      simp [tracialVector, basis, empty]
    simp only [mul_apply_eq_comp, hz, map_zero, add_apply, zero_add, smul_apply] at hc'
    rw [hc', inner_smul_right, inner_commutatorKernel]
    simp_rw [ih]
    rw [reverseDerivativeMoment, List.length_cons, pow_succ, Finset.mul_sum,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    split_ifs <;> ring

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.CumulantResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace FiniteEntropySeparation
open Finset FreeSeries

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
 theorem inner_selfAdjoint_word {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (hX : ∀ i, IsSelfAdjoint (X i)) (i : Fin n) (w : List (Fin n)) :
    inner ℂ (X i τ.vacuum) (wordEval X w τ.vacuum) = wordMoment τ X (i::w) := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    (hX i).star_eq]
  rfl
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TwoNoiseFisher
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate lp
open MeasureTheory Filter
namespace FiniteEntropySeparation
section General
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem norm_sq_sqrt_pair [CompleteSpace H] {x y : H} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : inner ℂ x y = 0) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖(Real.sqrt a : ℂ) • x + (Real.sqrt b : ℂ) • y‖ ^ 2 = a + b := by
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_left, inner_smul_right, hxy]
  simp [norm_smul, hx, hy,
    Real.norm_eq_abs, Real.sq_sqrt ha, Real.sq_sqrt hb,
    abs_of_nonneg (Real.sqrt_nonneg a), abs_of_nonneg (Real.sqrt_nonneg b)]

end General

namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
 theorem noise_basis_test {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ j, X j ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ j, σ j ∉ J)
    (u : ℝ) (i : Fin n) (w : List (Fin n)) :
    inner ℂ (basis (noiseWord [σ i]))
      (wordEval (heatTuple X (fun k => semicircularN (σ k)) u) w
        (tracialVector B N G).vacuum) =
      (Real.sqrt u : ℂ) * derivativeMoment (tracialVector B N G)
        (heatTuple X (fun k => semicircularN (σ k)) u) i w := by
  simpa only [List.map_cons, List.map_nil, List.reverse_singleton, List.length_singleton, pow_one,
    reverseDerivativeMoment, derivativeMoment] using wick_testing J X hX σ hσ hs u [i] w

 theorem semicircularN_vacuum (i : N) :
    semicircularN i (tracialVector B N G).vacuum = basis (noiseWord [i]) := by
  simp [semicircularN, tracialVector, basis, creationN_single, annihilationN_single,
    removeN, empty, noiseWord_cons, noiseWord_nil]
end FreeTensor
namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]

omit [NeZero p] in
theorem noiseVector₀_norm [NeZero p] (i : Fin (p+1)) : ‖noiseVector₀ p i‖ = 1 := by
  simp [noiseVector₀, basis, lp.norm_single (E := fun _ => ℂ) (p := 2)]

omit [NeZero p] in
theorem noiseVector₁_norm [NeZero p] (i : Fin (p+1)) : ‖noiseVector₁ p i‖ = 1 := by
  simp [noiseVector₁, basis, lp.norm_single (E := fun _ => ℂ) (p := 2)]
 theorem noiseVector_orthogonal (i j : Fin (p+1)) : inner ℂ (noiseVector₀ p i) (noiseVector₁ p j) = 0 := by
  have hneq : [initialIndex p i] ≠ [auxiliaryIndex p j] := by
    intro he
    have he' : initialIndex p i = auxiliaryIndex p j := List.cons.inj he |>.1
    exact auxiliaryIndex_fresh p j ⟨i,he'⟩
  exact noise_basis_orthonormal.inner_eq_zero hneq

 theorem noiseVector₀_C (i j : Fin (p+1)) : inner ℂ (noiseVector₀ p i) (C p j (τ p).vacuum) = 0 := by
  have ht := noise_basis_test ∅ (C p) (C_mem_background p ∅) (initialIndex p)
    (initialIndex_injective p) (by simp) 0 i [j]
  simpa [heatTuple, wordEval, noiseVector₀] using ht
 theorem noiseVector₁_C (i j : Fin (p+1)) : inner ℂ (noiseVector₁ p i) (C p j (τ p).vacuum) = 0 := by
  have ht := noise_basis_test ∅ (C p) (C_mem_background p ∅) (auxiliaryIndex p)
    (auxiliaryIndex_injective p) (by simp) 0 i [j]
  simpa [heatTuple, wordEval, noiseVector₁] using ht

 theorem doublyNoised_vacuum (h s : ℝ) (i : Fin (p+1)) :
    doublyNoised p h s i (τ p).vacuum = C p i (τ p).vacuum +
      ((Real.sqrt h : ℂ) • noiseVector₀ p i + (Real.sqrt s : ℂ) • noiseVector₁ p i) := by
  change (C p i (τ p).vacuum + (Real.sqrt h : ℂ) •
    semicircularN (initialIndex p i) (τ p).vacuum) +
    (Real.sqrt s : ℂ) • semicircularN (auxiliaryIndex p i) (τ p).vacuum = _
  rw [semicircularN_vacuum, semicircularN_vacuum]
  simp only [noiseVector₀, noiseVector₁, add_assoc]

 theorem doublyNoised_variance (h s : ℝ) (hh : 0 ≤ h) (hs : 0 ≤ s) (i : Fin (p+1)) :
    ‖doublyNoised p h s i (τ p).vacuum‖ ^ 2 = ‖C p i (τ p).vacuum‖ ^ 2 + h+s := by
  have hc : inner ℂ (C p i (τ p).vacuum)
      ((Real.sqrt h : ℂ) • noiseVector₀ p i + (Real.sqrt s : ℂ) • noiseVector₁ p i) = 0 := by
    rw [← inner_conj_symm, inner_add_left, inner_smul_left, inner_smul_left,
      noiseVector₀_C, noiseVector₁_C]
    simp
  rw [doublyNoised_vacuum, norm_add_sq (𝕜 := ℂ), hc,
    norm_sq_sqrt_pair (noiseVector₀_norm p i) (noiseVector₁_norm p i)
      (noiseVector_orthogonal p i i) h s hh hs]
  simp
  ring

end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.SignalCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace FiniteEntropySeparation
open Finset FreeSeries
namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]
 theorem variance_nonneg (i : Fin (p+1)) : 0 ≤ variance p i := sq_nonneg _

omit [NeZero p] in
theorem fockMoments_one [NeZero p] (i : Fin p) : fockMoments p [i] = 0 := by
  have he := congrFun (fockMoments_eq p) [i]
  simpa [subst_cons, conv_nil, quadratic] using he

omit [NeZero p] in
theorem fockMoments_two [NeZero p] (i j : Fin p) : fockMoments p [i,j] = if j=i then 1 else 0 := by
  have he := congrFun (fockMoments_eq p) [i,j]
  simp only [Pi.add_apply, unit_cons, zero_add, subst_cons, conv_cons, subst_nil, conv_nil,
    FreeSeries.deriv_apply, quadratic] at he
  simpa [fockMoments] using he
 theorem C_offDiagonal (i j : Fin (p+1)) (hij : j ≠ i) : signalMoments p [i,j] = 0 := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact (hij rfl).elim
    | cast j =>
      have he := signal_option_moments p [none, some j]
      simpa [fockMoments_one] using he
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      have he := signal_option_moments p [some i, none]
      simpa [fockMoments_one] using he
    | cast j =>
      have hj : j ≠ i := fun h => hij (congrArg Fin.castSucc h)
      have he := signal_option_moments p [some i, some j]
      simpa [fockMoments_two, hj] using he
 theorem C_covariance (i j : Fin (p+1)) :
    signalMoments p [i,j] = if j=i then (variance p i : ℂ) else 0 := by
  by_cases hj : j=i
  · subst j
    rw [ite_eq_left rfl]
    have he := inner_selfAdjoint_word (τ p) (C p) (C_selfAdjoint p) i [i]
    simpa [signalMoments, wordEval, variance, inner_self_eq_norm_sq_to_K] using he.symm
  · rw [ite_eq_right hj]; exact C_offDiagonal p i j hj
 theorem variance_last_le_one (hp : 2 ≤ p) : variance p (Fin.last p) ≤ 1 := by
  have he := (C p (Fin.last p)).le_opNorm (τ p).vacuum
  rw [(τ p).norm_vacuum, mul_one, C_last] at he
  have hn := equidiscreteSignal_norm_le (B := Fin p) (N := Fin ((p+1)+(p+1))) p hp
  unfold variance
  rw [C_last]
  nlinarith [norm_nonneg (equidiscreteSignal p (τ p).vacuum)]
 theorem variance_castSucc (i : Fin p) : variance p i.castSucc = 1 := by
  have he := C_covariance p i.castSucc i.castSucc
  have ht := signal_option_moments p [some i,some i]
  simp only [List.map_cons, List.map_nil, optionFin_some, List.filterMap_cons, List.filterMap_nil,
    id_eq, fockMoments_two, ite_true] at ht
  simp at ht
  rw [ite_eq_left rfl, ht] at he
  exact_mod_cast he.symm
 theorem variance_le_one (hp : 2 ≤ p) (i : Fin (p+1)) : variance p i ≤ 1 := by
  induction i using Fin.lastCases with
  | last => exact variance_last_le_one p hp
  | cast i => rw [variance_castSucc]
end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TotalSecond
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset Filter Set
open scoped Topology
namespace FiniteEntropySeparation
variable {n d : ℕ}
 theorem totalSecond_matrix (a : MatrixCoordinates n d) : totalSecond (matrixMoment a)=(d:ℝ)⁻¹*‖a‖^2 := by
  simp only [totalSecond,matrixMoment_second_hs,hsNorm_sq,← mul_sum,hermitianChart_normSq]
 section Operators
 variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (τ : TracialVector M)
 theorem wordMoment_second (X : Fin n → H →L[ℂ] H) (hX : ∀i,IsSelfAdjoint (X i)) (i : Fin n) :
    (wordMoment τ X [i,i]).re=‖X i τ.vacuum‖^2 := by
  have he := inner_selfAdjoint_word τ X hX i [i]
  simpa [wordEval,inner_self_eq_norm_sq_to_K,← Complex.ofReal_pow] using (congrArg Complex.re he).symm
 end Operators
namespace Model
variable (p : ℕ) [NeZero p]
 theorem totalSecond_heat_le (hp : 2≤p) {h s : ℝ} (hh : 0≤h) (hs : 0 ≤ s) :
    totalSecond (wordMoment (τ p) (heatTuple (X p h) (auxiliaryNoise p) s))≤(p+1:ℝ)*(1+h+s) := by
  have hsa := FreeTensor.heatTuple_selfAdjoint (X p h) (auxiliaryNoise p) (X_selfAdjoint p h) (auxiliaryNoise_selfAdjoint p) s
  simp only [totalSecond,wordMoment_second (τ p) _ hsa]
  change (∑i : Fin (p+1),‖doublyNoised p h s i (τ p).vacuum‖^2)≤_
  simp only [doublyNoised_variance p h s hh hs]
  calc
    _ ≤ ∑i : Fin (p+1),(1+h+s) := sum_le_sum (fun i _ => by
      have hb := variance_le_one p hp i
      change ‖C p i (τ p).vacuum‖^2≤1 at hb
      linarith)
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.BlockGaussianQuantitative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
namespace FiniteEntropySeparation
variable {p d : ℕ}
 theorem two_pow_le_exp (k : ℕ) : (2:ℝ)^k≤Real.exp k := by
  have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) (show (2:ℝ)≤Real.exp 1 from by linarith [Real.add_one_le_exp (1:ℝ)]) k
  simpa only [← Real.exp_nat_mul,mul_one] using hh
 theorem blockEvent_gaussian_four (hd : 64≤d) {v : ℝ} (hv : 0<v)
    (hvs : Real.sqrt v≤(2:ℝ)^25) (hpv : 32768*v≤p) (hp : (p:ℝ)≤Real.exp 64) :
    (normalLaw (v/d)) (blockEvent p d (Real.sqrt ((p:ℝ)*d)/4) (4*Real.sqrt (v*p*d)))≤
      ENNReal.ofReal (Real.exp (-4*(d:ℝ)^2)) := by
  have hd0 : 0<d := by omega
  have hd' : (64:ℝ)≤d := by exact_mod_cast hd
  have hdpos : (0:ℝ)<d := by linarith
  have hp0 : 0<(p:ℝ) := by nlinarith
  have hpd : 0<(p:ℝ)*d := mul_pos hp0 hdpos
  have hsq : 0<Real.sqrt v := Real.sqrt_pos.mpr hv
  let ε : ℝ := 1/(64*Real.sqrt v)
  have hε : 0<ε := by dsimp [ε]; positivity
  have hroot : Real.sqrt (v*p*d)=Real.sqrt v*Real.sqrt ((p:ℝ)*d) := by
    rw [mul_assoc,Real.sqrt_mul hv.le]
  have hgap : Real.sqrt ((p:ℝ)*d)/4-2*ε*(4*Real.sqrt (v*p*d))=Real.sqrt ((p:ℝ)*d)/8 := by
    rw [hroot]
    dsimp [ε]
    field_simp
    ring
  have hbase : 1+2/ε≤Real.exp 34 := by
    have hb : 1+2/ε≤(2:ℝ)^34 := by
      have he : 1+2/ε=1+128*Real.sqrt v := by dsimp [ε]; field_simp; ring
      rw [he]
      norm_num at hvs ⊢
      linarith
    exact hb.trans (two_pow_le_exp 34)
  have htail : -((Real.sqrt ((p:ℝ)*d)/8)^2)/(4*(v/d))≤-128*(d:ℝ)^2 := by
    rw [div_pow,Real.sq_sqrt hpd.le]
    have he : -((p:ℝ)*d/(8:ℝ)^2)/(4*(v/d))=-(p:ℝ)*(d:ℝ)^2/(256*v) := by field_simp; ring
    rw [he]
    apply (div_le_iff₀ (by positivity : 0<256*v)).mpr
    have hh := mul_le_mul_of_nonneg_right hpv (sq_nonneg (d:ℝ))
    nlinarith
  have h1 : (p:ℝ)^d≤Real.exp ((d:ℝ)^2) := by
    calc
      _ ≤ (Real.exp 64)^d := pow_le_pow_left₀ hp0.le hp d
      _ = Real.exp ((d:ℝ)*64) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have h2 : (1+2/ε)^(2*d^2)≤Real.exp (68*(d:ℝ)^2) := by
    calc
      _ ≤ (Real.exp 34)^(2*d^2) := pow_le_pow_left₀ (by positivity) hbase _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h3 : Real.exp (-((Real.sqrt ((p:ℝ)*d)/8)^2)/(4*(v/d)))≤Real.exp (-128*(d:ℝ)^2) := Real.exp_le_exp.mpr htail
  have h4 : Real.sqrt 2^(2*d^2)≤Real.exp (2*(d:ℝ)^2) := by
    have hs : Real.sqrt 2≤Real.exp 1 := by
      apply le_trans (show Real.sqrt 2≤2 from by nlinarith [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num),Real.sqrt_nonneg (2:ℝ)])
      linarith [Real.add_one_le_exp (1:ℝ)]
    calc
      _ ≤ (Real.exp 1)^(2*d^2) := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hb := blockEvent_gaussian_bound (p := p) hd0 (div_pos hv hdpos) hε
    (show 0≤Real.sqrt ((p:ℝ)*d)/4-2*ε*(4*Real.sqrt (v*p*d)) by rw [hgap]; positivity)
  apply hb.trans
  apply ENNReal.ofReal_le_ofReal
  rw [hgap]
  calc
    _ ≤ Real.exp ((d:ℝ)^2)*Real.exp (68*(d:ℝ)^2)*Real.exp (-128*(d:ℝ)^2)*Real.exp (2*(d:ℝ)^2) :=
      mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le) h3 (by positivity) (by positivity)) h4 (by positivity) (by positivity)
    _ = Real.exp (-57*(d:ℝ)^2) := by simp only [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (d:ℝ)])
 theorem chosenP_ge_two : 2≤chosenP := by norm_num [chosenP]
 theorem chosenTime_pos : 0<chosenTime := by norm_num [chosenTime]
 theorem chosen_time_noise_budget : 256*chosenTime≤(chosenP:ℝ) := by norm_num [chosenTime,chosenP]
 theorem chosen_gaussian_block (hd : 64≤d) {h : ℝ} (hh : 0<h) (hh1 : h<1) :
    (normalLaw ((1+h+chosenTime)/d))
      (blockEvent chosenP d (Real.sqrt ((chosenP:ℝ)*d)/4) (4*Real.sqrt ((1+h+chosenTime)*chosenP*d)))≤
      ENNReal.ofReal (Real.exp (-4*(d:ℝ)^2)) := by
  apply blockEvent_gaussian_four hd (by have := chosenTime_pos; linarith)
  · apply (Real.sqrt_le_left (by positivity : (0:ℝ)≤(2:ℝ)^25)).mpr
    norm_num [chosenTime] at *
    linarith
  · norm_num [chosenP,chosenTime] at *
    linarith
  · simpa only [chosenP,Nat.cast_pow,Nat.cast_ofNat] using two_pow_le_exp 64
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory
namespace FiniteEntropySeparation
variable {E : Type u1} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
 theorem gaussianDecay_integrable {c : ℝ} (hc : 0<c) : Integrable (fun x : E => Real.exp (-c*‖x‖^2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (b := (c:ℂ)) (by simpa using hc) 0 (0:E)).re
  convert h using 1
  funext x
  simp only [zero_mul,add_zero]
  change Real.exp (-c*‖x‖^2) = (Complex.exp (-(c:ℂ)*(‖x‖:ℂ)^2)).re
  rw [← Complex.ofReal_pow,← Complex.ofReal_neg,← Complex.ofReal_mul,← Complex.ofReal_exp]
  rfl
 theorem polynomial_gaussian_bound {c : ℝ} (hc : 0<c) (m : ℕ) (r : ℝ) (hr : 0≤r) :
    (1+r)^m*Real.exp (-c*r) ≤
      ((m.factorial:ℝ)*(2/c)^m*Real.exp (c/2))*Real.exp (-(c/2)*r) := by
  have hy : 0≤(c/2)*(1+r) := by positivity
  have he := Real.pow_div_factorial_le_exp _ hy m
  have hf : 0<(m.factorial:ℝ) := by positivity
  have hh : (1+r)^m ≤ (m.factorial:ℝ)*(2/c)^m*Real.exp ((c/2)*(1+r)) := by
    have hpow : 0<(c/2)^m := by positivity
    have he' : (c/2)^m*(1+r)^m ≤ Real.exp ((c/2)*(1+r))*(m.factorial:ℝ) := by
      simpa only [mul_pow] using (div_le_iff₀ hf).mp he
    calc
      _ ≤ Real.exp ((c/2)*(1+r))*(m.factorial:ℝ)/(c/2)^m := (le_div_iff₀ hpow).mpr (by simpa [mul_comm] using he')
      _ = _ := by rw [div_eq_mul_inv,← inv_pow,inv_div]; ring
  apply (mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le).trans_eq
  calc
    _ = ((m.factorial:ℝ)*(2/c)^m)*(Real.exp ((c/2)*(1+r))*Real.exp (-c*r)) := by ring
    _ = ((m.factorial:ℝ)*(2/c)^m)*Real.exp (c/2 + -(c/2)*r) := by rw [← Real.exp_add]; congr 2; ring
    _ = _ := by rw [Real.exp_add]; ring
 theorem polynomial_gaussian_integrable {c : ℝ} (hc : 0<c) (m : ℕ) :
    Integrable (fun x : E => (1+‖x‖^2)^m*Real.exp (-c*‖x‖^2)) := by
  apply ((gaussianDecay_integrable (E := E) (show 0<c/2 by positivity)).const_mul
    ((m.factorial:ℝ)*(2/c)^m*Real.exp (c/2))).mono'
  · exact (by fun_prop : Continuous (fun x : E => (1+‖x‖^2)^m*Real.exp (-c*‖x‖^2))).aestronglyMeasurable
  · exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      exact polynomial_gaussian_bound hc m (‖x‖^2) (sq_nonneg _))
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianConvolutionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
 theorem normalKernel_shift_bounds {a b s D K : ℝ} (ha : 0<a) (hs : s∈Icc a b)
    (hD : |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)| ≤ D) (_hK : 0 ≤ K)
    (x y : EuclideanSpace ℝ ι) (hy : ‖y‖ ≤ K) :
    Real.exp (-D-(‖x‖^2+K^2)/a)  ≤  normalKernel s (x-y) ∧
    normalKernel s (x-y)  ≤  Real.exp (D+K^2/(2*b))*Real.exp (-‖x‖^2/(4*b)) := by
  have hs0 : 0<s := ha.trans_le hs.1
  have hb : 0<b := hs0.trans_le hs.2
  have hnorm : ‖x-y‖ ≤ ‖x‖+K := (norm_sub_le x y).trans (add_le_add le_rfl hy)
  have hnorm' : ‖x‖ ≤ ‖x-y‖+K := by
    calc _ = ‖(x-y)+y‖ := by rw [sub_add_cancel]
         _  ≤  ‖x-y‖+‖y‖ := norm_add_le _ _
         _  ≤  _ := add_le_add_right hy _
  have hu : ‖x-y‖^2 ≤ 2*(‖x‖^2+K^2) := by
    nlinarith [sq_nonneg (‖x‖-K),pow_le_pow_left₀ (norm_nonneg _) hnorm 2]
  have hl : ‖x‖^2 ≤ 2*(‖x-y‖^2+K^2) := by
    nlinarith [sq_nonneg (‖x-y‖-K),pow_le_pow_left₀ (norm_nonneg _) hnorm' 2]
  have hdivu : ‖x-y‖^2/(2*s) ≤ (‖x‖^2+K^2)/a := by
    calc _  ≤  ‖x-y‖^2/(2*a) := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith [hs.1])
         _  ≤  _ := by apply (div_le_iff₀ (show 0<2*a by positivity)).mpr; field_simp; nlinarith
  have hdivl : ‖x‖^2/(4*b)-K^2/(2*b) ≤ ‖x-y‖^2/(2*s) := by
    calc _  ≤  ‖x-y‖^2/(2*b) := by apply (le_div_iff₀ (show 0<2*b by positivity)).mpr; field_simp; nlinarith
         _  ≤  _ := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith [hs.2])
  constructor
  · apply Real.exp_le_exp.mpr
    have := (abs_le.mp hD).1
    linarith
  · rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := (abs_le.mp hD).2
    simp only [neg_div] at *
    linarith
 theorem smoothedDensity_bounds (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {a b s D K : ℝ} (ha : 0<a) (hs : s∈Icc a b)
    (hD : |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)| ≤ D) (hK : 0 ≤ K)
    (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) (x : EuclideanSpace ℝ ι) :
    Real.exp (-D-(‖x‖^2+K^2)/a)  ≤  smoothedDensity μ s x ∧
    smoothedDensity μ s x  ≤  Real.exp (D+K^2/(2*b))*Real.exp (-‖x‖^2/(4*b)) := by
  have hi := normalKernel_integrable_finite μ (ha.trans_le hs.1) x
  constructor
  · have h := integral_mono_ae (integrable_const (Real.exp (-D-(‖x‖^2+K^2)/a))) hi
      (hμ.mono (fun y hy => (normalKernel_shift_bounds ha hs hD hK x y hy).1))
    simpa only [smoothedDensity,integral_const,probReal_univ,one_smul] using h
  · have h := integral_mono_ae hi (integrable_const (Real.exp (D+K^2/(2*b))*Real.exp (-‖x‖^2/(4*b))))
      (hμ.mono (fun y hy => (normalKernel_shift_bounds ha hs hD hK x y hy).2))
    simpa only [smoothedDensity,integral_const,probReal_univ,one_smul] using h
 theorem smoothedDensity_log_bound (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {a b s D K : ℝ} (ha : 0<a) (hs : s∈Icc a b) (_hD0 : 0 ≤ D)
    (hD : |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)| ≤ D) (hK : 0 ≤ K)
    (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) (x : EuclideanSpace ℝ ι) :
    |Real.log (smoothedDensity μ s x)| ≤ D+(‖x‖^2+K^2)/a := by
  have hs0 := ha.trans_le hs.1
  have hb : 0<b := hs0.trans_le hs.2
  have hp := smoothedDensity_pos μ hs0 x
  obtain ⟨hl,hu⟩ := smoothedDensity_bounds μ ha hs hD hK hμ x
  rw [abs_le]
  constructor
  · have h := Real.log_le_log (Real.exp_pos _) hl
    rw [Real.log_exp] at h
    linarith
  · have hu' : smoothedDensity μ s x  ≤  Real.exp D := by
      unfold smoothedDensity
      have h := integral_mono_ae (normalKernel_integrable_finite μ hs0 x) (integrable_const (Real.exp D))
        (ae_of_all _ (fun y => (normalKernel_le s hs0 (x-y)).trans (Real.exp_le_exp.mpr (le_trans (le_abs_self _) hD))))
      simpa only [smoothedDensity,integral_const,probReal_univ,one_smul] using h
    have h := Real.log_le_log hp hu'
    rw [Real.log_exp] at h
    exact h.trans (le_add_of_nonneg_right (by positivity))
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory Set
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
 theorem smoothedLog_polynomial_bound (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {a b s D K : ℝ} (ha : 0<a) (hs : s∈Icc a b) (hD0 : 0 ≤ D)
    (hD : |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)| ≤ D) (hK : 0 ≤ K)
    (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) (x : EuclideanSpace ℝ ι) :
    |Real.log (smoothedDensity μ s x)| ≤ (D+(1+K^2)/a)*(1+‖x‖^2) := by
  apply (smoothedDensity_log_bound μ ha hs hD0 hD hK hμ x).trans
  have h : ‖x‖^2+K^2 ≤ (1+K^2)*(1+‖x‖^2) := by nlinarith [mul_nonneg (sq_nonneg K) (sq_nonneg ‖x‖)]
  have h' := div_le_div_of_nonneg_right h ha.le
  have h'' : D ≤ D*(1+‖x‖^2) := by nlinarith [mul_nonneg hD0 (sq_nonneg ‖x‖)]
  convert add_le_add h'' h' using 1 ; ring
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianEntropyIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open MeasureTheory Set
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
 theorem smoothedPolynomial_integrable (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s K : ℝ} (hs : 0<s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) (m : ℕ) :
    Integrable (fun x => (1+‖x‖^2)^m*smoothedDensity μ s x) := by
  let D := |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)|
  let A := Real.exp (D+K^2/(2*s))
  have hi := (polynomial_gaussian_integrable (E := EuclideanSpace ℝ ι) (c := 1/(4*s)) (by positivity) m).const_mul A
  apply hi.mono' (((continuous_const.add (continuous_norm.pow 2)).pow m).mul (smoothedDensity_continuous μ hs)).aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    simp only [Pi.mul_apply,Pi.add_apply,Pi.pow_apply]
    have hp := smoothedDensity_pos μ hs x
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (1+‖x‖^2)^m*smoothedDensity μ s x)]
    have h := (smoothedDensity_bounds μ hs (show s∈Icc s s from ⟨le_rfl,le_rfl⟩) (show |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)| ≤ D from le_rfl) hK hμ x).2
    have he : -‖x‖^2/(4*s)=-(1/(4*s))*‖x‖^2 := by ring
    rw [he] at h
    simpa only [A,mul_assoc,mul_left_comm] using mul_le_mul_of_nonneg_left h (show 0 ≤ (1+‖x‖^2)^m by positivity))
 theorem smoothedIntegrable_of_bound {F : Type u2} [NormedAddCommGroup F]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s K : ℝ} (hs : 0<s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K)
    {f : EuclideanSpace ℝ ι → F} (hf : AEStronglyMeasurable f) (C : ℝ) (m : ℕ)
    (hb : ∀x,‖f x‖ ≤ C*(1+‖x‖^2)^m*smoothedDensity μ s x) : Integrable f := by
  apply ((smoothedPolynomial_integrable μ hs hK hμ m).const_mul C).mono' hf
  exact ae_of_all _ (fun x => by simpa only [mul_assoc] using hb x)
 theorem smoothedLog_continuous (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0<s) : Continuous (fun x => Real.log (smoothedDensity μ s x)) :=
  (smoothedDensity_continuous μ hs).log (fun x => (smoothedDensity_pos μ hs x).ne')
 theorem smoothedEntropy_integrable (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s K : ℝ} (hs : 0<s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) :
    Integrable (fun x => smoothedDensity μ s x*Real.log (smoothedDensity μ s x)) := by
  let D := |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)|
  apply smoothedIntegrable_of_bound μ hs hK hμ
    (((smoothedDensity_continuous μ hs).mul (smoothedLog_continuous μ hs)).aestronglyMeasurable)
    (D+(1+K^2)/s) 1
  intro x
  simp only [Pi.mul_apply]
  simp only [Real.norm_eq_abs,abs_mul,abs_of_pos (smoothedDensity_pos μ hs x),pow_one]
  have h := smoothedLog_polynomial_bound μ hs (show s∈Icc s s from ⟨le_rfl,le_rfl⟩) (abs_nonneg _) (show |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)| ≤ D from le_rfl) hK hμ x
  nlinarith [mul_le_mul_of_nonneg_left h (smoothedDensity_pos μ hs x).le]
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianEntropyEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5

noncomputable section
open MeasureTheory Set Classical
namespace FiniteEntropySeparation
 theorem entropy_subprobability_bound {Ω : Type u1} [MeasurableSpace Ω] (ν : Measure Ω)
    (f g : Ω → ℝ) (hf : ∀x,0<f x) (hg : ∀x,0<g x)
    (hfi : Integrable f ν) (hgi : Integrable g ν)
    (hff : Integrable (fun x => f x*Real.log (f x)) ν)
    (hfg : Integrable (fun x => f x*Real.log (g x)) ν)
    (hfmass : ∫x,f x ∂ν=1) (hgmass : ∫x,g x ∂ν≤1) :
    -(∫x,f x*Real.log (f x) ∂ν) ≤ -(∫x,f x*Real.log (g x) ∂ν) := by
  have hp x : f x*Real.log (g x)-f x*Real.log (f x) ≤ g x-f x := by
    have hh := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos (hg x) (hf x))) (hf x).le
    rw [Real.log_div (hg x).ne' (hf x).ne'] at hh
    have he : f x*(g x/f x-1)=g x-f x := by field_simp [(hf x).ne']
    rw [he] at hh
    nlinarith
  have hi := integral_mono (hfg.sub hff) (hgi.sub hfi) hp
  simp only [Pi.sub_apply] at hi
  rw [integral_sub hfg hff,integral_sub hgi hfi,hfmass] at hi
  linarith
 theorem eventTilt_expand {Ω : Type u3} (g : Ω → ℝ) (E : Set Ω) (z : ℝ) (x : Ω) :
    eventTilt g E z x = g x/2+(Real.exp z-1)/2*E.indicator g x := by
  classical
  by_cases hx : x∈E <;> simp [eventTilt,hx] <;> ring
 theorem eventTilt_log {Ω : Type u4} (g : Ω → ℝ) (hg : ∀x,0<g x) (E : Set Ω) (z : ℝ) (x : Ω) :
    Real.log (eventTilt g E z x)=Real.log (g x)+(if x∈E then z else 0)-Real.log 2 := by
  classical
  by_cases hx : x∈E
  · simp only [eventTilt,hx,ite_true]
    rw [Real.log_mul (div_ne_zero (Real.exp_ne_zero z) (by norm_num : (2:ℝ)≠0)) (hg x).ne',
      Real.log_div (Real.exp_ne_zero z) (by norm_num : (2:ℝ)≠0),Real.log_exp]
    ring
  · simp only [eventTilt,hx,ite_false]
    rw [Real.log_mul (by norm_num : (1/2:ℝ)≠0) (hg x).ne',
      Real.log_div (by norm_num : (1:ℝ)≠0) (by norm_num : (2:ℝ)≠0),Real.log_one]
    ring
 theorem entropy_event_bound {Ω : Type u5} [MeasurableSpace Ω] (ν : Measure Ω)
    (f g : Ω → ℝ) (hf : ∀x,0<f x) (hg : ∀x,0<g x)
    (hfi : Integrable f ν) (hgi : Integrable g ν)
    (hff : Integrable (fun x => f x*Real.log (f x)) ν)
    (hfg : Integrable (fun x => f x*Real.log (g x)) ν)
    (hfmass : ∫x,f x ∂ν=1) (hgmass : ∫x,g x ∂ν=1)
    (E : Set Ω) (hE : MeasurableSet E) {z : ℝ} (hz : 0≤z)
    (hα : (1/2:ℝ)≤∫x in E,f x ∂ν) (hβ : (∫x in E,g x ∂ν)≤Real.exp (-z)) :
    -(∫x,f x*Real.log (f x) ∂ν) ≤ -(∫x,f x*Real.log (g x) ∂ν)-z/2+Real.log 2 := by
  classical
  have hi : Integrable (eventTilt g E z) ν := by
    have heq : eventTilt g E z = fun x => g x/2+(Real.exp z-1)/2*E.indicator g x := funext (eventTilt_expand g E z)
    rw [heq]
    exact (hgi.div_const 2).add ((hgi.indicator hE).const_mul _)
  have hm : (∫x,eventTilt g E z x ∂ν)≤1 := by
    simp only [eventTilt_expand]
    rw [integral_add (hgi.div_const 2) ((hgi.indicator hE).const_mul _),integral_div,
      integral_const_mul,integral_indicator hE,hgmass]
    have hb0 : 0≤∫x in E,g x ∂ν := integral_nonneg (fun x => (hg x).le)
    have h := mul_le_mul_of_nonneg_left hβ (Real.exp_pos z).le
    rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at h
    nlinarith
  have hp x : 0<eventTilt g E z x := by
    unfold eventTilt
    split_ifs
    · exact mul_pos (div_pos (Real.exp_pos z) (by norm_num)) (hg x)
    · exact mul_pos (by norm_num) (hg x)
  have he x : f x*Real.log (eventTilt g E z x)=f x*Real.log (g x)+z*E.indicator f x-Real.log 2*f x := by
    rw [eventTilt_log g hg]
    by_cases hx : x∈E <;> simp [hx] <;> ring
  have hlog : Integrable (fun x => f x*Real.log (eventTilt g E z x)) ν := by
    simp only [he]
    exact (hfg.add ((hfi.indicator hE).const_mul z)).sub (hfi.const_mul _)
  have hb := entropy_subprobability_bound ν f (eventTilt g E z) hf hp hfi hi hff hlog hfmass hm
  simp only [he] at hb
  have hj : Integrable (fun x => f x*Real.log (g x)+z*E.indicator f x) ν := hfg.add ((hfi.indicator hE).const_mul z)
  rw [integral_sub hj (hfi.const_mul (Real.log 2)),
    integral_add hfg ((hfi.indicator hE).const_mul z),integral_const_mul,integral_const_mul,
    integral_indicator hE,hfmass,mul_one] at hb
  nlinarith [mul_le_mul_of_nonneg_left hα hz]
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianCrossEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open MeasureTheory Set
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
 theorem smoothedSecond_integrable (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s K : ℝ} (hs : 0<s) (hK : 0≤K) (hμ : ∀ᵐy ∂μ,‖y‖≤K) :
    Integrable (fun x => smoothedDensity μ s x*‖x‖^2) := by
  have hi := (smoothedPolynomial_integrable μ hs hK hμ 1).sub (smoothedDensity_integrable μ hs)
  convert hi using 1
  funext x
  simp only [pow_one,Pi.sub_apply]
  ring
 theorem normalCross_integrable (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s K : ℝ} (hs : 0<s) (hK : 0≤K) (hμ : ∀ᵐy ∂μ,‖y‖≤K) (v : ℝ) :
    Integrable (fun x => smoothedDensity μ s x*Real.log (normalKernel v x)) := by
  have he x : smoothedDensity μ s x*Real.log (normalKernel v x)=
      smoothedDensity μ s x*(-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*v))-
      (smoothedDensity μ s x*‖x‖^2)/(2*v) := by rw [normalKernel,Real.log_exp]; ring
  simp only [he]
  exact ((smoothedDensity_integrable μ hs).mul_const _).sub ((smoothedSecond_integrable μ hs hK hμ).div_const _)
 theorem normalCross_integral (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s K : ℝ} (hs : 0<s) (hK : 0≤K) (hμ : ∀ᵐy ∂μ,‖y‖≤K) (v : ℝ) :
    -(∫x,smoothedDensity μ s x*Real.log (normalKernel v x))=
      (Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*v)+(∫x,smoothedDensity μ s x*‖x‖^2)/(2*v) := by
  have he x : smoothedDensity μ s x*Real.log (normalKernel v x)=
      smoothedDensity μ s x*(-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*v))-
      (smoothedDensity μ s x*‖x‖^2)/(2*v) := by rw [normalKernel,Real.log_exp]; ring
  simp only [he]
  rw [integral_sub ((smoothedDensity_integrable μ hs).mul_const _)
    ((smoothedSecond_integrable μ hs hK hμ).div_const _),integral_mul_const,integral_div,smoothedDensity_integral μ hs]
  ring
 theorem density_event_toReal {Ω : Type u2} [MeasurableSpace Ω] (ν : Measure Ω)
    (f : Ω → ℝ) (hf : Integrable f ν) (hf0 : ∀x,0≤f x) (E : Set Ω) (hE : MeasurableSet E) :
    ((ν.withDensity (fun x => ENNReal.ofReal (f x))) E).toReal=∫x in E,f x ∂ν := by
  rw [withDensity_apply _ hE,← ofReal_integral_eq_lintegral_ofReal hf.integrableOn (ae_of_all _ hf0),
    ENNReal.toReal_ofReal (integral_nonneg hf0)]
 theorem classicalEntropy_event_gaussian (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s K v z : ℝ} (hs : 0<s) (hK : 0≤K) (hμ : ∀ᵐy ∂μ,‖y‖≤K) (hv : 0<v) (hz : 0≤z)
    (E : Set (EuclideanSpace ℝ ι)) (hE : MeasurableSet E)
    (hα : ENNReal.ofReal (1/2:ℝ)≤(volume.withDensity (fun x => ENNReal.ofReal (smoothedDensity μ s x))) E)
    (hβ : normalLaw v E≤ENNReal.ofReal (Real.exp (-z))) :
    classicalEntropy μ s≤(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*v)+
      (∫x,smoothedDensity μ s x*‖x‖^2)/(2*v)-z/2+Real.log 2 := by
  have hfi := smoothedDensity_integrable μ hs
  have hgi := normalKernel_integrable (ι := ι) hv
  have hfm : (volume.withDensity (fun x => ENNReal.ofReal (smoothedDensity μ s x))) univ=1 := by
    rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ (fun x => (smoothedDensity_pos μ hs x).le)),smoothedDensity_integral μ hs]
    simp
  have hfE : (volume.withDensity (fun x => ENNReal.ofReal (smoothedDensity μ s x))) E≠⊤ :=
    ne_top_of_le_ne_top (by simp) ((measure_mono (subset_univ E)).trans_eq hfm)
  have ha := (ENNReal.ofReal_le_iff_le_toReal hfE).mp hα
  rw [density_event_toReal volume _ hfi (fun x => (smoothedDensity_pos μ hs x).le) E hE] at ha
  have hb := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hβ
  rw [normalLaw,density_event_toReal volume _ hgi (fun x => (normalKernel_pos v x).le) E hE,
    ENNReal.toReal_ofReal (Real.exp_pos _).le] at hb
  have he := entropy_event_bound volume (smoothedDensity μ s) (normalKernel v)
    (smoothedDensity_pos μ hs) (normalKernel_pos v) hfi hgi (smoothedEntropy_integrable μ hs hK hμ)
    (normalCross_integrable μ hs hK hμ v) (smoothedDensity_integral μ hs) (normalKernel_integral hv) E hE hz ha hb
  rwa [normalCross_integral μ hs hK hμ v] at he
variable {n d : ℕ}
 theorem integral_heatLaw_totalSecond (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0<s) :
    (∫x,totalSecond (matrixMoment x) ∂matrixHeatLaw μ s)=(d:ℝ)⁻¹*(∫x,smoothedDensity μ (s/d) x*‖x‖^2) := by
  rw [integral_matrixHeatLaw μ hs hd]
  simp only [totalSecond_matrix,mul_left_comm _ (d:ℝ)⁻¹,integral_const_mul]
 theorem normalizedEntropy_event_gaussian (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsProbabilityMeasure μ]
    {s K v : ℝ} (hs : 0<s) (hK : 0≤K) (hμ : ∀ᵐy ∂μ,‖y‖≤K) (hv : 0<v)
    (E : Set (MatrixCoordinates n d)) (hE : MeasurableSet E)
    (hα : ENNReal.ofReal (1/2:ℝ)≤ matrixHeatLaw μ s E)
    (hβ : normalLaw (v/d) E≤ENNReal.ofReal (Real.exp (-4*(d:ℝ)^2))) :
    normalizedMatrixEntropy μ s≤(n:ℝ)/2*Real.log (2*Real.pi*v)+
      (∫x,totalSecond (matrixMoment x) ∂matrixHeatLaw μ s)/(2*v)-2+Real.log 2/(d:ℝ)^2 := by
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have he := classicalEntropy_event_gaussian μ (div_pos hs hd') hK hμ (div_pos hv hd')
    (show 0≤4*(d:ℝ)^2 by positivity) E hE hα (by simpa only [neg_mul] using hβ)
  have hlog : Real.log (2*Real.pi*(v/d))=Real.log (2*Real.pi*v)-Real.log d := by
    rw [show 2*Real.pi*(v/d)=(2*Real.pi*v)/d by ring,Real.log_div (by positivity) hd'.ne']
  rw [hlog] at he
  rw [integral_heatLaw_totalSecond hd μ hs]
  unfold normalizedMatrixEntropy
  have hh := div_le_div_of_nonneg_right he (sq_nonneg (d:ℝ))
  simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul] at hh
  convert add_le_add hh (le_refl ((n:ℝ)/2*Real.log d)) using 1 <;> first | rfl | (field_simp; ring)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.TerminalGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Finset Set
open scoped Topology
namespace FiniteEntropySeparation

 theorem chosen_terminal_isotropic {D : ℕ → ℕ} (hD0 : ∀k,0<D k) (hD : Tendsto D atTop atTop)
    {h R δ Δ : ℝ} (hh0 : 0<h) (hh1 : h<1) (hR : 0≤R)
    (hδ : 0<δ) (hΔ : 0<Δ) (hδΔ : δ≤Δ/4)
    (hsep : ∀i j : Fin chosenP,i≠j → Δ≤|equidiscreteAtom chosenP i-equidiscreteAtom chosenP j|)
    (hq : ∀l : Fin chosenP,∀r : ℝ,|r-equidiscreteAtom chosenP l|≤δ → (3:ℝ)/4≤((spectralBasis chosenP l).eval r)^2)
    (hh : spectralGood chosenP δ Δ (wordMoment (Model.τ chosenP) (Model.X chosenP h)))
    (hn : ∀k,(diagonalMicrostates (Model.τ chosenP) (Model.X chosenP h) R k (D k)).Nonempty)
    (μ : (k:ℕ) → Measure (MatrixCoordinates (chosenP+1) (D k))) [∀k,IsProbabilityMeasure (μ k)]
    (hμ : ∀k,∀ᵐa ∂μ k,a∈diagonalMicrostates (Model.τ chosenP) (Model.X chosenP h) R k (D k)) :
    ∀ᶠk in atTop,normalizedMatrixEntropy (μ k) chosenTime≤
      ((chosenP+1:ℕ):ℝ)/2*Real.log (2*Real.pi*Real.exp 1*(1+h+chosenTime))-(3:ℝ)/2 := by
  let v := 1+h+chosenTime
  have hv : 0<v := by dsimp [v]; linarith [chosenTime_pos]
  have hconv := Model.matrixHeatLaw_totalSecond_tendsto chosenP hD0 hD hR hn μ hμ chosenTime_pos
  have hm := Model.totalSecond_heat_le chosenP chosenP_ge_two hh0.le chosenTime_pos.le
  have hlim : totalSecond (wordMoment (Model.τ chosenP) (heatTuple (Model.X chosenP h) (Model.auxiliaryNoise chosenP) chosenTime))<
      ((chosenP+1:ℕ):ℝ)*v+v/2 := by push_cast; dsimp [v] at *; linarith
  have he := hconv.eventually (gt_mem_nhds hlim)
  have hl := Model.matrixHeatLaw_blocks_eventually chosenP chosenP_ge_two hδ hΔ hδΔ hsep hq hh0 hh1 hh
    chosenTime_pos chosen_time_noise_budget R D hD0 μ hμ
  filter_upwards [he,hl,hD.eventually (eventually_ge_atTop 64)] with k hk hlow hdk
  have hnorm : ∀ᵐa ∂μ k,‖a‖≤Real.sqrt (((chosenP+1:ℕ):ℝ)*D k)*R := by
    filter_upwards [hμ k] with a ha
    have hb := microstates_subset_closedBall (Model.τ chosenP) (Model.X chosenP h) R hR k (D k) ((k+1:ℝ)⁻¹) ha
    simpa only [Metric.mem_closedBall,dist_zero_right] using hb
  have hb := normalizedEntropy_event_gaussian (hD0 k) (μ k) chosenTime_pos
    (show 0≤Real.sqrt (((chosenP+1:ℕ):ℝ)*D k)*R by positivity) hnorm hv
    _ (blockEvent_isClosed (hD0 k) _ _).measurableSet hlow (chosen_gaussian_block hdk hh0 hh1)
  have hmoment : (∫a,totalSecond (matrixMoment a) ∂matrixHeatLaw (μ k) chosenTime)/(2*v)≤
      ((chosenP+1:ℕ):ℝ)/2+1/4 := by
    apply (div_le_iff₀ (by positivity : 0<2*v)).mpr
    linarith
  have hdim : (2:ℝ)≤D k := by exact_mod_cast (show 2≤D k by omega)
  have hlogdim : Real.log 2/(D k:ℝ)^2≤(1:ℝ)/4 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<(D k:ℝ)^2)).mpr
    have hlog := Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)
    nlinarith
  have hlog : Real.log (2*Real.pi*Real.exp 1*v)=Real.log (2*Real.pi*v)+1 := by
    rw [show 2*Real.pi*Real.exp 1*v=(2*Real.pi*v)*Real.exp 1 by ring,
      Real.log_mul (by positivity) (Real.exp_ne_zero _),Real.log_exp]
  change _≤((chosenP+1:ℕ):ℝ)/2*Real.log (2*Real.pi*Real.exp 1*v)-3/2
  rw [hlog]
  linarith
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Finset Set
open scoped Topology
namespace FiniteEntropySeparation
namespace Model
variable (p : ℕ) [NeZero p]
 theorem isotropic_gaussian_correction {a : ℝ} (ha : 0<a) :
    ((p+1:ℕ):ℝ)/2*Real.log (2*Real.pi*Real.exp 1*(1+a))≤gaussianEntropy p a+1/(2*a) := by
  have hz : 0<2*Real.pi*Real.exp 1 := by positivity
  have hv := variance_nonneg p (Fin.last p)
  have hl : Real.log (1+a)-Real.log (a+variance p (Fin.last p))≤1/a := by
    have he : Real.log (1+a)-Real.log a≤1/a := by
      rw [← Real.log_div (by positivity) ha.ne']
      have hb := Real.log_le_sub_one_of_pos (div_pos (by positivity : 0<1+a) ha)
      have he : (1+a)/a-1=1/a := by field_simp; ring
      rwa [he] at hb
    have hm := Real.log_le_log ha (show a≤a+variance p (Fin.last p) by linarith)
    linarith
  rw [Real.log_mul hz.ne' (by positivity)]
  unfold gaussianEntropy
  rw [Fin.sum_univ_castSucc]
  simp only [variance_castSucc,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  push_cast
  have he : 1/(2*a)=(1/2:ℝ)*(1/a) := by ring
  rw [he,add_comm a 1]
  nlinarith
end Model
 theorem chosen_gaussian_correction {h : ℝ} (hh : 0<h) :
    ((chosenP+1:ℕ):ℝ)/2*Real.log (2*Real.pi*Real.exp 1*(1+h+chosenTime))≤
      Model.gaussianEntropy chosenP (h+chosenTime)+(1:ℝ)/2 := by
  have ht : 1≤h+chosenTime := by norm_num [chosenTime] at *; linarith
  have hb := Model.isotropic_gaussian_correction chosenP (show 0<h+chosenTime by linarith)
  have hc : 1/(2*(h+chosenTime))≤(1:ℝ)/2 := by
    apply (div_le_iff₀ (by positivity : 0<2*(h+chosenTime))).mpr
    linarith
  rw [← add_assoc] at hb
  linarith
 theorem chosen_terminal_gaussian_oai {D : ℕ → ℕ} (hD0 : ∀k,0<D k) (hD : Tendsto D atTop atTop)
    {h R δ Δ : ℝ} (hh0 : 0<h) (hh1 : h<1) (hR : 0≤R)
    (hδ : 0<δ) (hΔ : 0<Δ) (hδΔ : δ≤Δ/4)
    (hsep : ∀i j : Fin chosenP,i≠j → Δ≤|equidiscreteAtom chosenP i-equidiscreteAtom chosenP j|)
    (hq : ∀l : Fin chosenP,∀r : ℝ,|r-equidiscreteAtom chosenP l|≤δ → (3:ℝ)/4≤((spectralBasis chosenP l).eval r)^2)
    (hh : spectralGood chosenP δ Δ (wordMoment (Model.τ chosenP) (Model.X chosenP h)))
    (hn : ∀k,(diagonalMicrostates (Model.τ chosenP) (Model.X chosenP h) R k (D k)).Nonempty)
    (μ : (k:ℕ) → Measure (MatrixCoordinates (chosenP+1) (D k))) [∀k,IsProbabilityMeasure (μ k)]
    (hμ : ∀k,∀ᵐa ∂μ k,a∈diagonalMicrostates (Model.τ chosenP) (Model.X chosenP h) R k (D k)) :
    ∀ᶠk in atTop,normalizedMatrixEntropy (μ k) chosenTime≤Model.gaussianEntropy chosenP (h+chosenTime)-1 := by
  filter_upwards [chosen_terminal_isotropic hD0 hD hh0 hh1 hR hδ hΔ hδΔ hsep hq hh hn μ hμ] with k hk
  linarith [chosen_gaussian_correction hh0]
end FiniteEntropySeparation

end

end OAI
end

theorem solution : type_of% @OAI.FiniteEntropySeparation.chosen_terminal_gaussian_oai := @OAI.FiniteEntropySeparation.chosen_terminal_gaussian_oai
