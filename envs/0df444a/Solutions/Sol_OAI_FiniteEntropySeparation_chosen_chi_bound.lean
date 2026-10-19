-- Prove2me | solution 1 for OAI.FiniteEntropySeparation.chosen_chi_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:21:42.227279+00:00
-- url     : https://prove2.me/submissions/63c60231-6538-4f3f-b4bf-818de7cae9e0

import Mathlib
import Definitions.Def_FiniteEntropySeparation
import Definitions.Def_OAIQWFE002
import Theorems.Thm_OAI_FiniteEntropySeparation_FreeTensor_freeFisher_le_liminf_matrixFisher
import Theorems.Thm_OAI_FiniteEntropySeparation_Model_heatFisher_shift_intervalIntegrable
import Theorems.Thm_OAI_FiniteEntropySeparation_chosen_terminal_gaussian
import Theorems.Thm_OAI_FiniteEntropySeparation_flow_to_chiStar_gap

section
-- module Solutions.OAIQW_FiniteEntropySeparation.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
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

theorem ConjugateSystem.unique {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} {X : Fin n → H →L[ℂ] H} {ξ η : Fin n → H}
    (hξ : ConjugateSystem τ X ξ) (hη : ConjugateSystem τ X η) : ξ = η := by
  funext i
  have hmem : ξ i - η i ∈ polynomialL2 τ X :=
    (polynomialL2 τ X).sub_mem (hξ i).1 (hη i).1
  have hker : polynomialL2 τ X ≤ (innerSL ℂ (ξ i - η i)).ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨w, rfl⟩
      change inner ℂ (ξ i - η i) (wordEval X w τ.vacuum) = 0
      rw [inner_sub_left, (hξ i).2 w, (hη i).2 w, sub_self]
    · exact (innerSL ℂ (ξ i - η i)).isClosed_ker
  have hd : inner ℂ (ξ i - η i) (ξ i - η i) = 0 := hker hmem
  exact sub_eq_zero.mp ((inner_self_eq_zero).mp hd)

theorem freeFisher_eq_of_conjugate {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} {X : Fin n → H →L[ℂ] H} {ξ : Fin n → H}
    (hξ : ConjugateSystem τ X ξ) :
    freeFisher τ X = ENNReal.ofReal (∑ i, ‖ξ i‖ ^ 2) := by
  apply le_antisymm
  · exact iInf_le_of_le ξ (iInf_le_of_le hξ le_rfl)
  · refine le_iInf fun η => le_iInf fun hη => ?_
    rw [hξ.unique τ hη]

 theorem wordVector_mem_polynomialL2 {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (w : List (Fin n)) :
    wordEval X w τ.vacuum ∈ polynomialL2 τ X :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w, rfl⟩)

 theorem projectedConjugate_system {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (η : Fin n → H)
    (hη : ∀ i w, inner ℂ (η i) (wordEval X w τ.vacuum) = derivativeMoment τ X i w) :
    ConjugateSystem τ X (projectedConjugate τ X η) := by
  intro i
  refine ⟨(polynomialL2 τ X).starProjection_apply_mem _, fun w => ?_⟩
  have h := (polynomialL2 τ X).starProjection_inner_eq_zero (η i)
    (wordEval X w τ.vacuum) (wordVector_mem_polynomialL2 τ X w)
  rw [inner_sub_left, hη i w] at h
  exact (sub_eq_zero.mp h).symm

theorem freeFisher_le_testVectors {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (η : Fin n → H)
    (hη : ∀ i w, inner ℂ (η i) (wordEval X w τ.vacuum) = derivativeMoment τ X i w) :
    freeFisher τ X ≤ ENNReal.ofReal (∑ i, ‖η i‖ ^ 2) := by
  rw [freeFisher_eq_of_conjugate τ (projectedConjugate_system τ X η hη)]
  apply ENNReal.ofReal_le_ofReal
  apply Finset.sum_le_sum
  intro i _
  exact pow_le_pow_left₀ (norm_nonneg _) ((polynomialL2 τ X).norm_starProjection_apply_le _) _

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

 theorem trace_vacuumRankOne_product {M : VonNeumannAlgebra H} (τ : TracialVector M)
    (A B : H →L[ℂ] H) : trace τ (A * vacuumRankOne τ * B) = trace τ A * trace τ B := by
  simp only [trace, vacuumRankOne, mul_apply_eq_comp, InnerProductSpace.rankOne_apply,
    map_smul, inner_smul_right]
  exact mul_comm _ _

 theorem trace_commutatorKernel {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (i : Fin n) (w : List (Fin n)) :
    trace τ (commutatorKernel (vacuumRankOne τ) X i w) = derivativeMoment τ X i w := by
  rw [commutatorKernel, trace_sum]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp [trace_vacuumRankOne_product, wordMoment]

theorem commutator_integration_by_parts {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (a : H →L[ℂ] H) (i : Fin n) (c : ℂ)
    (h : ∀ j, a * X j = X j * a + if j = i then c • vacuumRankOne τ else 0)
    (hz : a τ.vacuum = 0) (w : List (Fin n)) :
    inner ℂ (star a τ.vacuum) (wordEval X w τ.vacuum) = c * derivativeMoment τ X i w := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  change trace τ (a * wordEval X w) = _
  rw [commutator_word _ _ _ _ _ h, trace_add, trace_smul, trace_commutatorKernel]
  have hzero : trace τ (wordEval X w * a) = 0 := by
    simp [trace, mul_apply_eq_comp, hz]
  rw [hzero, zero_add]

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
 theorem normalKernel_continuousOn : ContinuousOn (fun z : ℝ × EuclideanSpace ℝ ι => normalKernel z.1 z.2) {z | 0<z.1} := by
  unfold normalKernel
  apply Real.continuous_exp.comp_continuousOn
  apply ContinuousOn.sub
  · apply continuousOn_const.mul
    apply ContinuousOn.log
    · fun_prop
    · intro z hz; exact ne_of_gt (by dsimp at hz ⊢; positivity)
  · apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro z hz; exact ne_of_gt (by dsimp at hz ⊢; positivity)
 theorem normalKernel_hasDeriv_time {s : ℝ} (hs : 0<s) (x : EuclideanSpace ℝ ι) :
    HasDerivAt (fun t => normalKernel t x)
      ((-(Fintype.card ι:ℝ)/(2*s)+‖x‖^2/(2*s^2))*normalKernel s x) s := by
  have hp : 2*Real.pi*s≠0 := by positivity
  have hd := (((((hasDerivAt_id s).const_mul (2*Real.pi)).log hp).const_mul (-(Fintype.card ι:ℝ)/2)).sub
    ((hasDerivAt_const s (‖x‖^2)).div ((hasDerivAt_id s).const_mul 2) (by positivity))).exp
  convert hd using 1
  · rfl
  · dsimp only [normalKernel,id_eq,Pi.sub_apply,Pi.div_apply]
    rw [mul_comm _ (Real.exp _)]
    congr 1
    field_simp [hs.ne',Real.pi_ne_zero]
    ring
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianDifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped Topology
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
 theorem normalKernel_hasDeriv_coordinate_at (s : ℝ) (x : EuclideanSpace ℝ ι) (i : ι) (r : ℝ) :
    HasDerivAt (fun t : ℝ => normalKernel s (x+t • EuclideanSpace.single i 1))
      (normalGradient s (x+r • EuclideanSpace.single i 1) i) r := by
  have hd : HasDerivAt (fun t : ℝ => ‖x+t • EuclideanSpace.single i 1‖^2) (2*(x i+r)) r := by
    have h := ((hasDerivAt_const r x).add ((hasDerivAt_id r).smul_const (EuclideanSpace.single i 1))).norm_sq
    simpa [real_inner_comm,PiLp.inner_apply,EuclideanSpace.single] using h
  have h := ((hasDerivAt_const r (-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s))).sub (hd.div_const (2*s))).exp
  convert h using 1
  · rfl
  · dsimp only [Pi.sub_apply,normalGradient]
    simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,EuclideanSpace.single,PiLp.single_apply,ite_true,mul_one,normalKernel]
    ring
 theorem normalGradient_hasDeriv_coordinate (s : ℝ) (x : EuclideanSpace ℝ ι) (i : ι) (r : ℝ) :
    HasDerivAt (fun t : ℝ => normalGradient s (x+t • EuclideanSpace.single i 1) i)
      (normalSecond s (x+r • EuclideanSpace.single i 1) i) r := by
  have h := (((hasDerivAt_const r (x i)).add (hasDerivAt_id r)).neg.div_const s).mul (normalKernel_hasDeriv_coordinate_at s x i r)
  simp only [normalGradient,normalSecond,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,
    EuclideanSpace.single,PiLp.single_apply,ite_true,mul_one,Pi.neg_apply,Pi.add_apply,id_eq] at h ⊢
  convert h using 1 <;> first | rfl | ring
 omit [DecidableEq ι] in
 theorem normal_heatEquation (s : ℝ) (x : EuclideanSpace ℝ ι) :
    normalTimeDerivative s x = (1/2:ℝ)*∑ i,normalSecond s x i := by
  unfold normalTimeDerivative normalSecond
  rw [← sum_mul,sum_sub_distrib,← sum_div,sum_const,card_univ,nsmul_eq_mul]
  have hn : ‖x‖^2=∑i,(x i)^2 := by simp [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs]
  rw [hn]
  ring
 omit [DecidableEq ι] in
 theorem normalTimeDerivative_continuousOn :
    ContinuousOn (fun z : ℝ × EuclideanSpace ℝ ι => normalTimeDerivative z.1 z.2) {z | 0<z.1} := by
  unfold normalTimeDerivative
  apply ContinuousOn.mul _ normalKernel_continuousOn
  apply ContinuousOn.add
  · exact continuousOn_const.div (by fun_prop) (fun z hz => mul_ne_zero (by norm_num) (ne_of_gt hz))
  · exact (continuous_snd.norm.pow 2).continuousOn.div ((continuous_const.mul (continuous_fst.pow 2)).continuousOn) (fun z hz => mul_ne_zero (by norm_num) (pow_ne_zero _ (ne_of_gt hz)))
 omit [DecidableEq ι] in
 theorem normalGradient_continuous (s : ℝ) (i : ι) : Continuous (fun x : EuclideanSpace ℝ ι => normalGradient s x i) := by
  unfold normalGradient
  exact (((PiLp.continuous_apply 2 _ i).neg).div_const s).mul (normalKernel_continuous_space s)
 omit [DecidableEq ι] in
 theorem normalSecond_continuous (s : ℝ) (i : ι) : Continuous (fun x : EuclideanSpace ℝ ι => normalSecond s x i) := by
  unfold normalSecond
  exact ((((PiLp.continuous_apply 2 _ i).pow 2).div_const (s^2)).sub continuous_const).mul (normalKernel_continuous_space s)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.CompactIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace FiniteEntropySeparation
variable {E : Type u1} {F : Type u2} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
 omit [NormedSpace ℝ E] [BorelSpace E] [NormedSpace ℝ F] in
 theorem integrable_of_compact_ae (μ : Measure E) [IsFiniteMeasure μ] {K : Set E} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ,x∈K) {f : E → F} (hm : AEStronglyMeasurable f μ) (hf : ContinuousOn f K) : Integrable f μ := by
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hf
  apply (integrable_const C).mono' hm
  filter_upwards [hμ] with x hx
  exact hC x hx
 theorem hasDerivAt_integral_compact {E : Type u1} {F : Type u2}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [SecondCountableTopology E] (μ : Measure E) [IsFiniteMeasure μ] {K : Set E} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ,x∈K) (f f' : ℝ → E → F) {a b t : ℝ} (ha : a<t) (hb : t<b)
    (hf : ∀s∈Icc a b,Continuous (f s)) (hf' : ∀s∈Icc a b,Continuous (f' s))
    (hc : ContinuousOn (fun z : ℝ × E => f' z.1 z.2) (Icc a b ×ˢ K))
    (hd : ∀s∈Icc a b,∀x∈K,HasDerivAt (fun u => f u x) (f' s x) s) :
    Integrable (f' t) μ ∧ HasDerivAt (fun u => ∫ x,f u x ∂μ) (∫ x,f' t x ∂μ) t := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hc
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Icc a b) (bound := fun _ => C) (Icc_mem_nhds ha hb)
  · filter_upwards [Icc_mem_nhds ha hb] with s hs
    exact (hf s hs).aestronglyMeasurable
  · exact integrable_of_compact_ae μ hK hμ (hf t ⟨ha.le,hb.le⟩).aestronglyMeasurable (hf t ⟨ha.le,hb.le⟩).continuousOn
  · exact (hf' t ⟨ha.le,hb.le⟩).aestronglyMeasurable
  · filter_upwards [hμ] with x hx s hs
    exact hC (s,x) ⟨hs,hx⟩
  · exact integrable_const _
  · filter_upwards [hμ] with x hx s hs
    exact hd s hs x hx
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
 theorem smoothedDensity_hasDeriv_time (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) (hμ : ∀ᵐ a ∂μ,a∈K)
    {s : ℝ} (hs : 0<s) (x : EuclideanSpace ℝ ι) :
    HasDerivAt (fun t => smoothedDensity μ t x) (smoothedTimeDerivative μ s x) s := by
  apply (hasDerivAt_integral_compact μ hK hμ (fun t a => normalKernel t (x-a)) (fun t a => normalTimeDerivative t (x-a))
    (a := s/2) (b := s+1) (by linarith) (by linarith) ?_ ?_ ?_ ?_).2
  · intro t ht; exact (normalKernel_continuous_space t).comp (continuous_const.sub continuous_id)
  · intro t ht
    unfold normalTimeDerivative normalKernel
    fun_prop
  · apply normalTimeDerivative_continuousOn.comp ((continuous_fst.prodMk (continuous_const.sub continuous_snd)).continuousOn)
    intro z hz; dsimp; linarith [hz.1.1]
  · intro t ht a ha
    exact normalKernel_hasDeriv_time (by linarith [ht.1]) (x-a)
 theorem smoothedDensity_hasDeriv_coordinate [DecidableEq ι] (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) (hμ : ∀ᵐ a ∂μ,a∈K)
    (s : ℝ) (x : EuclideanSpace ℝ ι) (i : ι) (r : ℝ) :
    HasDerivAt (fun t => smoothedDensity μ s (x+t • EuclideanSpace.single i 1))
      (smoothedGradient μ s (x+r • EuclideanSpace.single i 1) i) r := by
  apply (hasDerivAt_integral_compact μ hK hμ (fun t a => normalKernel s (x+t • EuclideanSpace.single i 1-a))
    (fun t a => normalGradient s (x+t • EuclideanSpace.single i 1-a) i) (a := r-1) (b := r+1) (by linarith) (by linarith) ?_ ?_ ?_ ?_).2
  · intro t ht; exact (normalKernel_continuous_space s).comp (continuous_const.sub continuous_id)
  · intro t ht; exact (normalGradient_continuous s i).comp (continuous_const.sub continuous_id)
  · exact ((normalGradient_continuous s i).comp ((continuous_const.add (continuous_fst.smul continuous_const)).sub continuous_snd)).continuousOn
  · intro t ht a ha
    simpa only [add_sub_right_comm] using normalKernel_hasDeriv_coordinate_at s (x-a) i t
 theorem smoothedGradient_hasDeriv_coordinate [DecidableEq ι] (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) (hμ : ∀ᵐ a ∂μ,a∈K)
    (s : ℝ) (x : EuclideanSpace ℝ ι) (i : ι) (r : ℝ) :
    HasDerivAt (fun t => smoothedGradient μ s (x+t • EuclideanSpace.single i 1) i)
      (smoothedSecond μ s (x+r • EuclideanSpace.single i 1) i) r := by
  apply (hasDerivAt_integral_compact μ hK hμ (fun t a => normalGradient s (x+t • EuclideanSpace.single i 1-a) i)
    (fun t a => normalSecond s (x+t • EuclideanSpace.single i 1-a) i) (a := r-1) (b := r+1) (by linarith) (by linarith) ?_ ?_ ?_ ?_).2
  · intro t ht; exact (normalGradient_continuous s i).comp (continuous_const.sub continuous_id)
  · intro t ht; exact (normalSecond_continuous s i).comp (continuous_const.sub continuous_id)
  · exact ((normalSecond_continuous s i).comp ((continuous_const.add (continuous_fst.smul continuous_const)).sub continuous_snd)).continuousOn
  · intro t ht a ha
    simpa only [add_sub_right_comm] using normalGradient_hasDeriv_coordinate s (x-a) i t
 theorem smoothed_heatEquation (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) (hμ : ∀ᵐ a ∂μ,a∈K) (s : ℝ) (x : EuclideanSpace ℝ ι) :
    smoothedTimeDerivative μ s x = (1/2:ℝ)*∑i, smoothedSecond μ s x i := by
  classical
  unfold smoothedTimeDerivative smoothedSecond
  simp only [normal_heatEquation,integral_const_mul]
  rw [integral_finsetSum]
  intro i hi
  exact integrable_of_compact_ae μ hK hμ (((normalSecond_continuous s i).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (((normalSecond_continuous s i).comp (continuous_const.sub continuous_id)).continuousOn)
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
 theorem matrixMoment_continuous {n d : ℕ} (w : List (Fin n)) :
    Continuous (fun a : MatrixCoordinates n d => matrixMoment a w) := by
  have hp : Continuous (fun a : MatrixCoordinates n d => (w.map (hermitianMatrix a)).prod) := by
    induction w with
    | nil => simpa using (continuous_const : Continuous (fun _ : MatrixCoordinates n d => (1 : Matrix (Fin d) (Fin d) ℂ)))
    | cons i w ih => simpa using (hermitianMatrix_continuous i).matrix_mul ih
  unfold matrixMoment Matrix.trace
  exact continuous_const.mul (continuous_finsetSum _ (fun i _ => hp.matrix_elem i i))
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
 theorem matrixOpNorm_continuous {d : ℕ} : Continuous (matrixOpNorm (d := d)) := by
  exact ((Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin d) (n := Fin d)).trans
    LinearMap.toContinuousLinearMap).toLinearMap.continuous_of_finiteDimensional.norm
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
 theorem microstates_measurable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ} (X : Fin n → H →L[ℂ] H)
    (R : ℝ) (m d : ℕ) (ε : ℝ) : MeasurableSet (microstates τ X R m d ε) := by
  simp only [microstates, ofPred_and, ofPred_forall]
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro i
    exact (isClosed_le (matrixOpNorm_continuous.comp (hermitianMatrix_continuous i)) continuous_const).measurableSet
  · apply MeasurableSet.iInter
    intro w
    apply MeasurableSet.iInter
    intro hw
    exact (isOpen_lt (((matrixMoment_continuous w).sub continuous_const).norm) continuous_const).measurableSet
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
 theorem microstates_volume_lt_top {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ} (X : Fin n → H →L[ℂ] H)
    (R : ℝ) (hR : 0 ≤ R) (m d : ℕ) (ε : ℝ) : volume (microstates τ X R m d ε) < ⊤ :=
  (measure_mono (microstates_subset_closedBall τ X R hR m d ε)).trans_lt
    (isCompact_closedBall (0 : MatrixCoordinates n d) _).measure_lt_top
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.FisherVariational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5

noncomputable section
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Filter
namespace FiniteEntropySeparation
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 theorem conjugate_polynomial_pairing {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} {X : Fin n → H →L[ℂ] H} {ξ : Fin n → H}
    (hξ : ConjugateSystem τ X ξ) (i : Fin n) (p : WordPolynomial n) :
    inner ℂ (ξ i) (polynomialVector τ X p) = polynomialDerivative τ X i p := by
  simp only [polynomialVector, polynomialDerivative, Finsupp.linearCombination_apply,
    Finsupp.sum, inner_sum, inner_smul_right, (hξ i).2, smul_eq_mul]

theorem norm_sq_eq_iSup_dense {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ι : Type} (v : ι → H) (ξ : H)
    (hξ : ξ ∈ (Submodule.span ℂ (Set.range v)).topologicalClosure) :
    ENNReal.ofReal (‖ξ‖ ^ 2) =
      ⨆ p : ι →₀ ℂ, ENNReal.ofReal
        (2 * (inner ℂ ξ (Finsupp.linearCombination ℂ v p)).re -
          ‖Finsupp.linearCombination ℂ v p‖ ^ 2) := by
  let Q : H → ℝ := fun z => 2 * (inner ℂ ξ z).re - ‖z‖ ^ 2
  have hQ : Continuous Q := by fun_prop
  let b := ⨆ p : ι →₀ ℂ, ENNReal.ofReal (Q (Finsupp.linearCombination ℂ v p))
  change ENNReal.ofReal (‖ξ‖ ^ 2) = b
  apply le_antisymm
  · have hc : IsClosed {z : H | ENNReal.ofReal (Q z) ≤ b} :=
      isClosed_le (ENNReal.continuous_ofReal.comp hQ) continuous_const
    have hs : (Submodule.span ℂ (Set.range v) : Set H) ⊆ {z | ENNReal.ofReal (Q z) ≤ b} := by
      intro z hz
      rw [← Finsupp.range_linearCombination] at hz
      obtain ⟨p,rfl⟩ := hz
      exact le_iSup (fun p : ι →₀ ℂ => ENNReal.ofReal (Q (Finsupp.linearCombination ℂ v p))) p
    have hh := hc.closure_subset_iff.mpr hs hξ
    have he : Q ξ = ‖ξ‖ ^ 2 := by
      have hself : (inner ℂ ξ ξ).re = ‖ξ‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) ξ).symm
      dsimp [Q]
      rw [hself]
      ring
    change ENNReal.ofReal (Q ξ) ≤ b at hh
    rwa [he] at hh
  · refine iSup_le fun p => ENNReal.ofReal_le_ofReal ?_
    have h := norm_sub_sq (𝕜 := ℂ) ξ (Finsupp.linearCombination ℂ v p)
    change ‖ξ - Finsupp.linearCombination ℂ v p‖ ^ 2 =
      ‖ξ‖ ^ 2 - 2 * (inner ℂ ξ (Finsupp.linearCombination ℂ v p)).re +
        ‖Finsupp.linearCombination ℂ v p‖ ^ 2 at h
    dsimp [Q]
    nlinarith [sq_nonneg ‖ξ - Finsupp.linearCombination ℂ v p‖]

 theorem freeFisher_variational {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) {ξ : Fin n → H}
    (hξ : ConjugateSystem τ X ξ) :
    freeFisher τ X = ∑ i, ⨆ p : WordPolynomial n, ENNReal.ofReal (fisherTest τ X i p) := by
  rw [freeFisher_eq_of_conjugate τ hξ, ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
  apply Finset.sum_congr rfl
  intro i _
  have h := norm_sq_eq_iSup_dense (fun w => wordEval X w τ.vacuum) (ξ i) (hξ i).1
  change ENNReal.ofReal (‖ξ i‖ ^ 2) =
    ⨆ p : WordPolynomial n, ENNReal.ofReal
      (2 * (inner ℂ (ξ i) (polynomialVector τ X p)).re - ‖polynomialVector τ X p‖ ^ 2) at h
  simpa only [conjugate_polynomial_pairing τ hξ, fisherTest] using h

 theorem freeFisher_lt_top_iff {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) :
    freeFisher τ X < ⊤ ↔ ∃ ξ, ConjugateSystem τ X ξ := by
  constructor
  · intro h
    by_contra! hn
    have he : freeFisher τ X = ⊤ := by simp [freeFisher, hn]
    rw [he] at h
    exact lt_irrefl _ h
  · rintro ⟨ξ,hξ⟩
    rw [freeFisher_eq_of_conjugate τ hξ]
    exact ENNReal.ofReal_lt_top

 theorem exists_conjugate_of_fisher_le {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (c : ℝ)
    (h : freeFisher τ X ≤ ENNReal.ofReal c) : ∃ ξ, ConjugateSystem τ X ξ :=
  (freeFisher_lt_top_iff τ X).mp (h.trans_lt ENNReal.ofReal_lt_top)

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

 theorem leftGenerator_mem (k : Generator B N G) : leftGenerator k ∈ algebra B N G :=
  (mem_algebra_iff _).mpr (generators_commute k)

 theorem semicircularB_mem (b : B) : semicircularB (N := N) (G := G) b ∈ algebra B N G :=
  leftGenerator_mem (.inl b)
 theorem semicircularN_mem (i : N) : semicircularN (B := B) (G := G) i ∈ algebra B N G :=
  leftGenerator_mem (.inr (.inl i))
 theorem unitaryG_mem (g : G) : unitaryG (B := B) (N := N) g ∈ algebra B N G :=
  leftGenerator_mem (.inr (.inr g))

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

theorem heat_freeFisher_le {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J)
    (u : ℝ) (hu : 0 < u) :
    freeFisher (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u) ≤
      ENNReal.ofReal ((n : ℝ) / u) := by
  let Z := heatTuple X (fun i => semicircularN (σ i)) u
  let η : Fin n → Space B N G := fun i =>
    ((Real.sqrt u)⁻¹ : ℂ) • basis (leftN (σ i) empty)
  have hc (i j : Fin n) : star (rightCreationN (σ i)) * Z j =
      Z j * star (rightCreationN (σ i)) +
        if j = i then (Real.sqrt u : ℂ) • vacuumRankOne (tracialVector B N G) else 0 := by
    change _ * (X j + (Real.sqrt u : ℂ) • semicircularN (σ j)) = _
    rw [mul_add, mul_smul_comm, (rightAnnihilationN_background (hs i) (hX j)).eq,
      rightAnnihilationN_semicircularN]
    change _ = (X j + (Real.sqrt u : ℂ) • semicircularN (σ j)) *
      star (rightCreationN (σ i)) +
      if j = i then (Real.sqrt u : ℂ) • vacuumRankOne (tracialVector B N G) else 0
    by_cases hij : j = i
    · subst j
      simp only [ite_true, add_mul, smul_mul_assoc, add_assoc]
      congr 1
      exact smul_add _ _ _
    · have hneq : σ i ≠ σ j := fun h => hij (hσ h).symm
      simp only [hij, hneq, ↓reduceIte, add_zero, add_mul, smul_mul_assoc]
  have hu' : Real.sqrt u ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hu)
  have hη (i : Fin n) (w : List (Fin n)) :
      inner ℂ (η i) (wordEval Z w (tracialVector B N G).vacuum) =
        derivativeMoment (tracialVector B N G) Z i w := by
    have h := commutator_integration_by_parts (tracialVector B N G) Z
      (star (rightCreationN (σ i))) i (Real.sqrt u) (hc i)
      (by simp [tracialVector, basis, empty]) w
    simp only [star_star, tracialVector, basis, rightCreationN_single] at h
    have he : rightN (σ i) (empty : Word B N G) = leftN (σ i) empty := by
      simp [rightN_eq_append, empty, leftN, push, append]
    rw [he] at h
    change inner ℂ (((Real.sqrt u : ℂ)⁻¹) • lp.single 2 (leftN (σ i) empty) 1)
      (wordEval Z w (lp.single 2 empty 1)) = _
    rw [inner_smul_left, h]
    simp [hu', tracialVector, basis]
  refine (freeFisher_le_testVectors (tracialVector B N G) Z η hη).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hnorm (i : Fin n) : ‖η i‖ ^ 2 = u⁻¹ := by
    simp [η, norm_smul, basis, norm_inv,
      lp.norm_single (E := fun _ : Word B N G => ℂ) (p := 2),
      abs_of_nonneg (Real.sqrt_nonneg u), inv_pow, Real.sq_sqrt (le_of_lt hu)]
  simp [hnorm, div_eq_mul_inv]

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.FisherLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Filter
namespace FiniteEntropySeparation
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 theorem wordEval_append {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {n : ℕ} (X : Fin n → H →L[ℂ] H) (u v : List (Fin n)) :
    wordEval X (u ++ v) = wordEval X u * wordEval X v := by
  simp [wordEval]

 theorem star_wordEval {n : ℕ} (X : Fin n → H →L[ℂ] H)
    (hX : ∀ i, IsSelfAdjoint (X i)) (w : List (Fin n)) :
    star (wordEval X w) = wordEval X w.reverse := by
  induction w with
  | nil => simp [wordEval]
  | cons i w ih =>
    simp only [wordEval, List.map_cons, List.prod_cons, star_mul, (hX i).star_eq,
      List.reverse_cons, List.map_append, List.prod_append, ] at *
    rw [ih]
    simp

 theorem inner_wordVector {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (hX : ∀ i, IsSelfAdjoint (X i)) (u v : List (Fin n)) :
    inner ℂ (wordEval X u τ.vacuum) (wordEval X v τ.vacuum) =
      wordMoment τ X (u.reverse ++ v) := by
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    star_wordEval X hX u]
  simp only [wordMoment, trace, wordEval_append, mul_apply_eq_comp]

theorem polynomialVector_norm_sq_eq_of_moments
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
    (τ : TracialVector M) (ρ : TracialVector N) {n : ℕ}
    (X : Fin n → H →L[ℂ] H) (Y : Fin n → K →L[ℂ] K)
    (hX : ∀ i, IsSelfAdjoint (X i)) (hY : ∀ i, IsSelfAdjoint (Y i))
    (hm : ∀ w, wordMoment τ X w = wordMoment ρ Y w) (p : WordPolynomial n) :
    ‖polynomialVector τ X p‖ ^ 2 = ‖polynomialVector ρ Y p‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ)]
  congr 1
  simp only [polynomialVector, Finsupp.linearCombination_apply, Finsupp.sum,
    sum_inner, inner_sum, inner_smul_left, inner_smul_right, inner_wordVector τ X hX,
    inner_wordVector ρ Y hY, hm]

 theorem derivativeMoment_eq_of_moments
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
    (τ : TracialVector M) (ρ : TracialVector N) {n : ℕ}
    (X : Fin n → H →L[ℂ] H) (Y : Fin n → K →L[ℂ] K)
    (hm : ∀ w, wordMoment τ X w = wordMoment ρ Y w) (i : Fin n) (w : List (Fin n)) :
    derivativeMoment τ X i w = derivativeMoment ρ Y i w := by
  simp only [derivativeMoment, hm]

theorem freeFisher_eq_of_wordMoments
    {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
    (τ : TracialVector M) (ρ : TracialVector N) {n : ℕ}
    (X : Fin n → H →L[ℂ] H) (Y : Fin n → K →L[ℂ] K)
    (hX : ∀ i, IsSelfAdjoint (X i)) (hY : ∀ i, IsSelfAdjoint (Y i))
    (hm : ∀ w, wordMoment τ X w = wordMoment ρ Y w)
    (heX : ∃ ξ, ConjugateSystem τ X ξ) (heY : ∃ ξ, ConjugateSystem ρ Y ξ) :
    freeFisher τ X = freeFisher ρ Y := by
  obtain ⟨ξ,hξ⟩ := heX
  obtain ⟨η,hη⟩ := heY
  rw [freeFisher_variational τ X hξ, freeFisher_variational ρ Y hη]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg iSup
  funext p
  apply congrArg ENNReal.ofReal
  unfold fisherTest
  rw [polynomialVector_norm_sq_eq_of_moments τ ρ X Y hX hY hm]
  congr 2
  simp only [polynomialDerivative, Finsupp.linearCombination_apply, Finsupp.sum,
    derivativeMoment_eq_of_moments τ ρ X Y hm]

namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
 theorem heat_conjugates_exist {n : ℕ} (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J)
    (u : ℝ) (hu : 0 < u) :
    ∃ ξ, ConjugateSystem (tracialVector B N G)
      (heatTuple X (fun i => semicircularN (σ i)) u) ξ :=
  exists_conjugate_of_fisher_le _ _ (n/u) (heat_freeFisher_le J X hX σ hσ hs u hu)

end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MicrostatesSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology
namespace FiniteEntropySeparation
 theorem matrixVolumeEntropy_ne_bot_volume {n d : ℕ} (hd : 0<d) (s : Set (MatrixCoordinates n d))
    (hs : matrixVolumeEntropy s ≠ ⊥) : volume s ≠ 0 := by
  intro h
  apply hs
  rw [matrixVolumeEntropy,h,ENNReal.log_zero,EReal.coe_mul_bot_of_pos (by positivity),EReal.bot_add]
 theorem matrixVolumeEntropy_coe {n d : ℕ} (s : Set (MatrixCoordinates n d))
    (hs : volume s ≠ 0) (ht : volume s ≠ ⊤) :
    matrixVolumeEntropy s = (((d:ℝ)^2)⁻¹*Real.log (volume s).toReal+(n:ℝ)/2*Real.log d:ℝ) := by
  rw [matrixVolumeEntropy, ENNReal.log_pos_real' (ENNReal.toReal_pos hs ht)]
  simp only [← EReal.coe_mul,← EReal.coe_add]
 theorem exists_strictMono_diagonal (P : ℕ → ℕ → Prop)
    (hP : ∀k L,∃d,L<d ∧ P k d) : ∃D : ℕ → ℕ, StrictMono D ∧ ∀k,P k (D k) := by
  classical
  choose f hf hfP using hP
  let D : ℕ → ℕ := fun k => Nat.rec (f 0 0) (fun k d => f (k+1) d) k
  refine ⟨D,strictMono_nat_of_lt_succ (fun k => hf (k+1) (D k)),?_⟩
  intro k
  cases k with
  | zero => exact hfP 0 0
  | succ k => exact hfP (k+1) (D k)
 variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ} (X : Fin n → H →L[ℂ] H)
 theorem exists_microstate_dimensions {R b : ℝ} (hb : (b:EReal)<chiCutoff τ X R) :
    ∃D : ℕ → ℕ, StrictMono D ∧ (∀k,0<D k) ∧
      ∀k,(b:EReal)< matrixVolumeEntropy (diagonalMicrostates τ X R k (D k)) := by
  have hP (k L : ℕ) : ∃d,L<d ∧ 0<d ∧
      (b:EReal)< matrixVolumeEntropy (diagonalMicrostates τ X R k d) := by
    have he : 0<(k+1:ℝ)⁻¹ := by positivity
    have hl := hb.trans_le (iInf_le_of_le k (iInf_le _ ⟨(k+1:ℝ)⁻¹,he⟩))
    have hfreq := frequently_lt_of_lt_limsup (h := hl)
    obtain ⟨d,hd,hb'⟩ := (frequently_atTop.mp hfreq) L
    exact ⟨d+1,by omega,by omega,by simpa [matrixVolumeEntropy,diagonalMicrostates] using hb'⟩
  obtain ⟨D,hD,h⟩ := exists_strictMono_diagonal (fun k d => 0<d ∧
    (b:EReal)< matrixVolumeEntropy (diagonalMicrostates τ X R k d)) hP
  exact ⟨D,hD,fun k => (h k).1,fun k => (h k).2⟩
 theorem diagonalMicrostates_measurable (R : ℝ) (k d : ℕ) :
    MeasurableSet (diagonalMicrostates τ X R k d) := microstates_measurable τ X R k d _
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

 theorem conv_add_left (f g h : Series α) : conv (f+g) h = conv f h + conv g h := by
  funext w
  simp only [conv_sum_splits, Pi.add_apply, add_mul, sum_add_distrib]
 theorem conv_add_right (f g h : Series α) : conv f (g+h) = conv f g + conv f h := by
  funext w
  simp only [conv_sum_splits, Pi.add_apply, mul_add, sum_add_distrib]
 theorem conv_smul_left (c : ℂ) (f g : Series α) : conv (c • f) g = c • conv f g := by
  funext w
  simp only [conv_sum_splits, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_sum]
 theorem conv_smul_right (c : ℂ) (f g : Series α) : conv f (c • g) = c • conv f g := by
  funext w
  simp only [conv_sum_splits, Pi.smul_apply, smul_eq_mul, mul_sum]
  apply sum_congr rfl
  intro k _
  ring
@[simp] theorem conv_zero_left (f : Series α) : conv 0 f = 0 := by
  funext w
  simp [conv_sum_splits]
@[simp] theorem conv_zero_right (f : Series α) : conv f 0 = 0 := by
  funext w
  simp [conv_sum_splits]
 theorem deriv_conv (a : α) (f g : Series α) :
    deriv a (conv f g) = f [] • deriv a g + conv (deriv a f) g := rfl

@[simp] theorem conv_unit_left (f : Series α) : conv unit f = f := by
  funext w
  cases w <;> simp [conv, deriv_unit]

 theorem conv_assoc (f g h : Series α) : conv (conv f g) h = conv f (conv g h) := by
  funext w
  induction w generalizing f g h with
  | nil => simp [mul_assoc]
  | cons a w ih =>
    simp only [conv_cons, conv_nil, deriv_conv, conv_add_left, conv_smul_left,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, ih]
    ring

 theorem conv_neg_left (f g : Series α) : conv (-f) g = -conv f g := by
  simpa using conv_smul_left (-1) f g
 theorem conv_neg_right (f g : Series α) : conv f (-g) = -conv f g := by
  simpa using conv_smul_right (-1) f g
 theorem conv_sub_left (f g h : Series α) : conv (f-g) h = conv f h - conv g h := by
  simp [sub_eq_add_neg, conv_add_left, conv_neg_left]
 theorem conv_agree {n : ℕ} {f f' g g' : Series α} (hf : Agree n f f') (hg : Agree n g g') :
    Agree n (conv f g) (conv f' g') := by
  intro w hw
  simp only [conv_sum_splits]
  apply sum_congr rfl
  intro k hk
  rw [hf _ (by simp only [List.length_take]; omega),
    hg _ (by simp only [List.length_drop]; omega)]

theorem length_induction {P : List α → Prop} (w : List α)
    (h : ∀ w, (∀ v, v.length < w.length → P v) → P w) : P w :=
  (measure List.length).wf.induction w h

 theorem subst_cons (M f : Series α) (a : α) (w : List α) :
    subst M f (a::w) = conv M (subst M (deriv a f)) w := by
  rw [subst, conv_sum_splits]
 theorem deriv_subst (M f : Series α) (a : α) :
    deriv a (subst M f) = conv M (subst M (deriv a f)) := by
  funext w
  exact subst_cons M f a w

 theorem subst_add (M f g : Series α) : subst M (f+g) = subst M f + subst M g := by
  funext w
  induction w using length_induction generalizing f g with
  | h w ih =>
    cases w with
    | nil => simp
    | cons a w =>
      simp only [subst, Pi.add_apply]
      simp_rw [show deriv a (f+g) = deriv a f + deriv a g from rfl]
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro k hk
      rw [ih _ (by simp)]
      simp [mul_add]

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

 theorem subst_mul (M f g : Series α) : subst M (conv f g) = conv (subst M f) (subst M g) := by
  funext w
  induction w using length_induction generalizing f g with
  | h w ih =>
    cases w with
    | nil => simp
    | cons a w =>
      rw [subst_cons, deriv_conv, subst_add, subst_smul, conv_add_right, conv_smul_right]
      rw [conv_cons, subst_nil, subst_cons, deriv_subst, conv_assoc]
      change f [] * _ + _ = f [] * _ + _
      congr 1
      apply conv_agree (n := w.length) (fun _ _ => rfl) (fun v hv => ?_) w le_rfl
      exact ih v (by simp ; omega) _ _

 theorem subst_neg (M f : Series α) : subst M (-f) = -subst M f := by
  simpa using subst_smul M f (-1)
 theorem subst_sub (M f g : Series α) : subst M (f-g) = subst M f - subst M g := by
  simp [sub_eq_add_neg, subst_add, subst_neg]

 theorem subst_unit_left (f : Series α) : subst unit f = f := by
  funext w
  induction w generalizing f with
  | nil => simp
  | cons a w ih => rw [subst_cons, conv_unit_left, ih]; rfl

theorem subst_comp (L M f : Series α) :
    subst L (subst M f) = subst (conv L (subst L M)) f := by
  funext w
  induction w using length_induction generalizing f with
  | h w ih =>
    cases w with
    | nil => simp
    | cons a w =>
      rw [subst_cons, deriv_subst, subst_mul, ← conv_assoc, subst_cons]
      apply conv_agree (n := w.length) (fun _ _ => rfl) (fun v hv => ?_) w le_rfl
      exact ih v (by simp ; omega) _

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.CumulantSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type u1}

 theorem Agree.mono {n m : ℕ} {f g : Series α} (h : Agree n f g) (hmn : m ≤ n) :
    Agree m f g := fun w hw => h w (hw.trans hmn)
 theorem Agree.refl (n : ℕ) (f : Series α) : Agree n f f := fun _ _ => rfl
 theorem Agree.trans {n : ℕ} {f g h : Series α} (hfg : Agree n f g) (hgh : Agree n g h) :
    Agree n f h := fun w hw => (hfg w hw).trans (hgh w hw)
 theorem agree_add {n : ℕ} {f f' g g' : Series α} (hf : Agree n f f') (hg : Agree n g g') :
    Agree n (f+g) (f'+g') := fun w hw => by simp only [Pi.add_apply, hf w hw, hg w hw]
 theorem agree_deriv {n : ℕ} {f g : Series α} (h : Agree (n+1) f g) (a : α) :
    Agree n (deriv a f) (deriv a g) := fun w hw => h (a::w) (by simp; omega)

 theorem subst_agree {n : ℕ} {M M' f g : Series α} (hM : Agree n M M') (hf : Agree n f g) :
    Agree n (subst M f) (subst M' g) := by
  induction n generalizing M M' f g with
  | zero =>
    intro w hw
    have : w = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
    subst w
    simpa using hf [] (by simp)
  | succ n ih =>
    intro w hw
    cases w with
    | nil => simpa using hf [] (by simp)
    | cons a w =>
      simp only [subst_cons]
      exact conv_agree (hM.mono (by omega))
        (ih (hM.mono (by omega)) (agree_deriv hf a)) w (by simp at hw; omega)

 theorem subst_agree_left_step {n : ℕ} {M M' : Series α} (hM : Agree n M M') (f : Series α) :
    Agree (n+1) (subst M f) (subst M' f) := by
  intro w hw
  cases w with
  | nil => simp
  | cons a w =>
    simp only [subst_cons]
    exact conv_agree hM (subst_agree hM (Agree.refl _ _)) w (by simp at hw; omega)

 theorem conv_left_cancel {M f g : Series α} (hM : M [] = 1)
    (h : conv M f = conv M g) : f = g := by
  funext w
  induction w using length_induction with
  | h w ih =>
    cases w with
    | nil => simpa [hM] using congrFun h []
    | cons a w =>
      have ht := congrFun h (a::w)
      simp only [conv_cons, hM, one_mul] at ht
      have hsmall : conv (deriv a M) f w = conv (deriv a M) g w := by
        apply conv_agree (Agree.refl w.length _) (fun v hv => ih v (by simp; omega)) w le_rfl
      rw [hsmall] at ht
      exact add_right_cancel ht

 theorem subst_injective {M : Series α} (hM : M [] = 1) : Function.Injective (subst M) := by
  intro f g h
  funext w
  induction w generalizing f g with
  | nil => simpa using congrFun h []
  | cons a w ih =>
    apply ih
    apply conv_left_cancel hM
    change conv M (subst M (deriv a f)) = conv M (subst M (deriv a g))
    rw [← deriv_subst, ← deriv_subst, h]

 theorem inverse_cons (f : Series α) (a : α) (w : List α) :
    inverse f (a::w) = -conv (deriv a f) (inverse f) w := by
  rw [inverse, conv_sum_splits]
  rfl
 theorem conv_inverse {f : Series α} (hf : f [] = 1) : conv f (inverse f) = unit := by
  funext w
  cases w with
  | nil => simp [hf]
  | cons a w => simp [inverse_cons, hf]
 theorem inverse_conv {f : Series α} (hf : f [] = 1) : conv (inverse f) f = unit := by
  apply conv_left_cancel hf
  rw [← conv_assoc, conv_inverse hf, conv_unit_left, conv_unit_right]
 theorem inverse_unique {f g : Series α} (hf : f [] = 1) (hg : conv f g = unit) :
    g = inverse f := conv_left_cancel hf (hg.trans (conv_inverse hf).symm)
 theorem momentIter_step {R : Series α} (hR : R [] = 0) (n : ℕ) :
    Agree n (momentIter R (n+1)) (momentIter R n) := by
  induction n with
  | zero =>
    intro w hw
    have : w = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
    subst w
    simp [momentIter, hR]
  | succ n ih =>
    exact agree_add (Agree.refl _ _) (subst_agree_left_step ih R)
 theorem momentIter_stable {R : Series α} (hR : R [] = 0) {n m : ℕ} (hnm : n ≤ m) :
    Agree n (momentIter R m) (momentIter R n) := by
  induction m, hnm using Nat.le_induction with
  | base => exact Agree.refl _ _
  | succ m hnm ih => exact ((momentIter_step hR m).mono hnm).trans ih

 theorem moments_agree {R : Series α} (hR : R [] = 0) (n : ℕ) :
    Agree n (moments R) (momentIter R n) := by
  intro w hw
  exact ((momentIter_stable hR hw) w le_rfl).symm
 theorem moments_eq {R : Series α} (hR : R [] = 0) : moments R = unit + subst (moments R) R := by
  funext w
  have h := (moments_agree hR (w.length+1)) w (by omega)
  rw [h, momentIter]
  apply congrArg (fun z : ℂ => unit w + z)
  exact ((subst_agree_left_step (moments_agree hR w.length) R) w (by omega)).symm
 theorem moments_unique {R M : Series α} (hR : R [] = 0)
    (hM : M = unit + subst M R) : M = moments R := by
  have hn (n : ℕ) : Agree n M (momentIter R n) := by
    induction n with
    | zero =>
      intro w hw
      have : w = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
      subst w
      have h := congrFun hM []
      simpa [momentIter, hR] using h
    | succ n ih =>
      rw [hM]
      exact agree_add (Agree.refl _ _) (subst_agree_left_step ih R)
  funext w
  exact hn w.length w le_rfl

 theorem cumulants_equation {M : Series α} (hM : M [] = 1) :
    M = unit + subst M (cumulants M) := by
  let J := moments (-boolean M)
  have hB : (-boolean M) [] = 0 := by simp
  have hJ : J = unit - subst J (boolean M) := by
    simpa only [subst_neg, sub_eq_add_neg] using moments_eq hB
  have hJM : conv J (subst J M) = unit := by
    have hJI : J = subst J (inverse M) := by
      calc
        J = unit - subst J (boolean M) := hJ
        _ = subst J (inverse M) := by rw [boolean, subst_sub, subst_unit]; abel
    calc
      conv J (subst J M) = conv (subst J (inverse M)) (subst J M) :=
        congrArg (fun A => conv A (subst J M)) hJI
      _ = unit := by rw [← subst_mul, inverse_conv hM, subst_unit]
  have hsubst : subst J (subst M (cumulants M)) = inverse J - unit := by
    rw [subst_comp, hJM, subst_unit_left]
    rfl
  apply subst_injective (moments_nil _)
  rw [subst_add, subst_unit, hsubst]
  have hMI : subst J M = inverse J := inverse_unique (moments_nil _) hJM
  rw [hMI]
  abel

 theorem cumulants_unique {M R : Series α} (hM : M [] = 1)
    (h : M = unit + subst M R) : R = cumulants M := by
  apply subst_injective hM
  have he := cumulants_equation hM
  exact add_left_cancel (h.symm.trans he)

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

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.CyclicSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α : Type} [DecidableEq α] [Fintype α]

 theorem rightDeriv_conv {α : Type} [DecidableEq α] [Fintype α] (i : α) (f g : Series α) :
    rightDeriv i (conv f g) = conv f (rightDeriv i g) + g [] • rightDeriv i f := by
  funext w
  induction w generalizing f with
  | nil => simp [rightDeriv, deriv, conv]; ring
  | cons a w ih =>
    change f [] * g ((a::w)++[i]) + conv (deriv a f) g (w++[i]) =
      (f [] * g ((a::w)++[i]) + conv (deriv a f) (rightDeriv i g) w) +
      g [] * f ((a::w)++[i])
    have h := ih (deriv a f)
    change conv (deriv a f) g (w++[i]) = _ at h
    rw [h]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, rightDeriv_apply, deriv_apply, List.cons_append]
    ring
 theorem rightDeriv_sub {α : Type} [DecidableEq α] [Fintype α] (i : α) (f g : Series α) :
    rightDeriv i (f-g) = rightDeriv i f - rightDeriv i g := rfl
 theorem rightDeriv_smul {α : Type} [DecidableEq α] [Fintype α] (i : α) (c : ℂ) (f : Series α) :
    rightDeriv i (c • f) = c • rightDeriv i f := rfl
 theorem rightDeriv_sum {α : Type} [DecidableEq α] [Fintype α] {β : Type u1} (s : Finset β) (f : β → Series α) (i : α) :
    rightDeriv i (∑ b ∈ s, f b) = ∑ b ∈ s, rightDeriv i (f b) := by
  funext w
  simp [rightDeriv]
 theorem rightDeriv_letter {α : Type} [DecidableEq α] [Fintype α] (i j : α) : rightDeriv i (letter j) = if i=j then unit else 0 := by
  funext w
  cases w with
  | nil => by_cases h : i=j <;> simp [rightDeriv, letter, unit, h]
  | cons a w => cases w <;> by_cases h : i=j <;> simp [rightDeriv, letter, unit, h]
 theorem series_ext_right {α : Type} [DecidableEq α] [Fintype α] {f g : Series α} (hn : f [] = g [])
    (h : ∀ i, rightDeriv i f = rightDeriv i g) : f = g := by
  funext w
  induction w using List.reverseRecOn with
  | nil => exact hn
  | append_singleton w i _ => exact congrFun (h i) w

 theorem rightDeriv_assemble (f : α → Series α) (j : α) :
    rightDeriv j (rightAssemble f) = f j := by
  rw [rightAssemble, rightDeriv_sum]
  simp only [rightDeriv_conv, rightDeriv_letter, letter_nil, zero_smul, add_zero]
  have hh (i : α) : conv (f i) (if j=i then unit else 0) = if j=i then f i else 0 := by
    split_ifs <;> simp
  simp_rw [hh]
  simp
 theorem assemble_rightDeriv (f : Series α) :
    rightAssemble (fun i => rightDeriv i f) = f - f [] • unit := by
  apply series_ext_right
  · simp
  · intro i
    simp [rightDeriv_assemble, rightDeriv_sub, rightDeriv_smul]
 theorem Cyclic.assemble {f : Series α} (hf : Cyclic f) :
    rightAssemble (fun i => deriv i f) = f - f [] • unit := by
  have hh : (fun i => deriv i f) = (fun i => rightDeriv i f) := funext hf
  rw [hh, assemble_rightDeriv]
 theorem cyclic_of_assemble {f : Series α} (h : rightAssemble (fun i => deriv i f) = f - f [] • unit) :
    Cyclic f := by
  intro i
  have hh := congrArg (rightDeriv i) h
  simpa [rightDeriv_assemble, rightDeriv_sub, rightDeriv_smul] using hh

 theorem conv_sum_left {α : Type} [DecidableEq α] [Fintype α] {β : Type u2} (s : Finset β) (f : β → Series α) (g : Series α) :
    conv (∑ b ∈ s, f b) g = ∑ b ∈ s, conv (f b) g := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert b s hb ih => simp [sum_insert hb, conv_add_left, ih]
 theorem conv_sum_right {α : Type} [DecidableEq α] [Fintype α] {β : Type u3} (s : Finset β) (f : Series α) (g : β → Series α) :
    conv f (∑ b ∈ s, g b) = ∑ b ∈ s, conv f (g b) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert b s hb ih => simp [sum_insert hb, conv_add_right, ih]
 theorem subst_sum {α : Type} [DecidableEq α] [Fintype α] {β : Type u4} (s : Finset β) (M : Series α) (f : β → Series α) :
    subst M (∑ b ∈ s, f b) = ∑ b ∈ s, subst M (f b) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert b s hb ih => simp [sum_insert hb, subst_add, ih]
 theorem subst_letter {α : Type} [DecidableEq α] [Fintype α] (M : Series α) (i : α) : subst M (letter i) = conv (letter i) M := by
  funext w
  cases w with
  | nil => simp
  | cons j w => simp only [subst_letter_cons, conv_cons, letter_nil, zero_mul, zero_add,
      deriv_letter]; split_ifs <;> simp
 theorem subst_rightAssemble (M : Series α) (f : α → Series α) :
    subst M (rightAssemble f) = conv (rightAssemble (fun i => subst M (f i))) M := by
  simp only [rightAssemble, subst_sum, conv_sum_left, subst_mul, subst_letter, conv_assoc]

 theorem cyclic_cumulants {M : Series α} (hM : M [] = 1) (hc : Cyclic M) :
    Cyclic (cumulants M) := by
  let R := cumulants M
  have he : M = unit + subst M R := cumulants_equation hM
  have hd (i : α) : deriv i M = conv M (subst M (deriv i R)) := by
    funext w
    have h := congrFun he (i::w)
    simpa [subst_cons] using h
  have hi (i : α) : rightDeriv i (inverse M) = -subst M (deriv i R) := by
    have hh := congrArg (rightDeriv i) (inverse_conv hM)
    rw [rightDeriv_conv, rightDeriv_unit, hM, one_smul, ← hc i, hd i,
      ← conv_assoc, inverse_conv hM, conv_unit_left] at hh
    exact eq_neg_of_add_eq_zero_right hh
  have hinv : rightAssemble (fun i => subst M (deriv i R)) = unit - inverse M := by
    apply series_ext_right
    · simp
    · intro i
      simp [rightDeriv_assemble, rightDeriv_sub, hi]
  apply cyclic_of_assemble
  simp only [cumulants_nil, zero_smul, sub_zero]
  apply subst_injective hM
  rw [subst_rightAssemble, hinv, conv_sub_left, conv_unit_left, inverse_conv hM]
  exact (eq_sub_iff_add_eq.mpr (by simpa [add_comm] using he.symm)).symm

 theorem cyclic_moments {R : Series α} (hR : R [] = 0) (hc : Cyclic R) :
    Cyclic (moments R) := by
  let M := moments R
  have hM : M [] = 1 := moments_nil R
  have he : M = unit + subst M R := moments_eq hR
  let A := rightAssemble (fun i => subst M (deriv i R))
  have hr : subst M R = conv A M := by
    have h := hc.assemble
    rw [hR, zero_smul, sub_zero] at h
    rw [← h, subst_rightAssemble]
  have ha : unit - A = inverse M := by
    have hp : conv (unit - A) M = unit := by
      rw [conv_sub_left, conv_unit_left]
      rw [hr] at he
      exact sub_eq_iff_eq_add.mpr he
    calc
      unit - A = conv (unit - A) (conv M (inverse M)) := by rw [conv_inverse hM, conv_unit_right]
      _ = inverse M := by rw [← conv_assoc, hp, conv_unit_left]
  intro i
  have hi : rightDeriv i (inverse M) = -subst M (deriv i R) := by
    rw [← ha, rightDeriv_sub, rightDeriv_unit, sub_eq_add_neg, zero_add]
    change -rightDeriv i (rightAssemble _) = _
    rw [rightDeriv_assemble]
  have hh := congrArg (rightDeriv i) (conv_inverse hM)
  rw [rightDeriv_conv, rightDeriv_unit, inverse_nil, one_smul, hi, conv_neg_right] at hh
  have hh' : rightDeriv i M = conv M (subst M (deriv i R)) := by
    exact eq_of_sub_eq_zero (by rw [sub_eq_add_neg]; simpa [add_comm] using hh)
  rw [hh']
  funext w
  have h := congrFun he (i::w)
  simpa [subst_cons] using h

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.LinearSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α β γ : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β]

 theorem reparam_cons {α β : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] (c : α → β → ℂ) (f : Series α) (b : β) (w : List β) :
    reparam c f (b::w) = ∑ a, c a b * reparam c (deriv a f) w := rfl
 theorem deriv_reparam {α β : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] (c : α → β → ℂ) (f : Series α) (b : β) :
    deriv b (reparam c f) = ∑ a, c a b • reparam c (deriv a f) := by
  funext w; simp [deriv_apply, reparam_cons]
 theorem reparam_add {α β : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] (c : α → β → ℂ) (f g : Series α) :
    reparam c (f+g) = reparam c f + reparam c g := by
  funext w
  induction w generalizing f g with
  | nil => rfl
  | cons b w ih =>
    simp only [reparam_cons, Pi.add_apply,
      show ∀ a, deriv a (f+g) = deriv a f + deriv a g from fun _ => rfl, ih]
    simp [mul_add, sum_add_distrib]
 theorem reparam_smul {α β : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] (c : α → β → ℂ) (z : ℂ) (f : Series α) :
    reparam c (z • f) = z • reparam c f := by
  funext w
  induction w generalizing f with
  | nil => rfl
  | cons b w ih =>
    simp only [reparam_cons, Pi.smul_apply, smul_eq_mul,
      show ∀ a, deriv a (z • f) = z • deriv a f from fun _ => rfl, ih]
    simp [mul_left_comm, mul_sum]
@[simp] theorem reparam_zero (c : α → β → ℂ) : reparam c 0 = 0 := by
  simpa using reparam_smul c 0 0
 theorem reparam_sum {δ : Type u1} (s : Finset δ) (c : α → β → ℂ) (f : δ → Series α) :
    reparam c (∑ d ∈ s, f d) = ∑ d ∈ s, reparam c (f d) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert d s hd ih => simp [sum_insert hd, reparam_add, ih]
@[simp] theorem reparam_unit (c : α → β → ℂ) : reparam c unit = unit := by
  funext w
  cases w with
  | nil => rfl
  | cons b w =>
    have hh (a : α) : deriv a (unit : Series α) = 0 := rfl
    simp [reparam_cons, hh]
 theorem reparam_conv (c : α → β → ℂ) (f g : Series α) :
    reparam c (conv f g) = conv (reparam c f) (reparam c g) := by
  funext w
  induction w generalizing f g with
  | nil => rfl
  | cons b w ih =>
    simp only [reparam_cons, deriv_conv, reparam_add, reparam_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, ih, mul_add, sum_add_distrib]
    rw [conv_cons, reparam_nil, reparam_cons, deriv_reparam, conv_sum_left]
    simp only [conv_smul_left, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    simp [mul_left_comm, mul_sum]
 theorem rightDeriv_reparam {α β : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] (c : α → β → ℂ) (f : Series α) (b : β) :
    rightDeriv b (reparam c f) = ∑ a, c a b • reparam c (rightDeriv a f) := by
  funext w
  induction w generalizing f with
  | nil => simp [rightDeriv, reparam_cons]
  | cons d w ih =>
    simp only [rightDeriv_apply, List.cons_append, reparam_cons, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    have hh (a : α) : reparam c (deriv a f) (w++[b]) =
        ∑ j, c j b * reparam c (rightDeriv j (deriv a f)) w := by
      simpa only [rightDeriv_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using ih (deriv a f)
    simp_rw [hh, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro j _
    have he : rightDeriv a (deriv j f) = deriv j (rightDeriv a f) := rfl
    rw [he]
    ring
 theorem Cyclic.reparam {f : Series α} (hf : Cyclic f) (c : α → β → ℂ) :
    Cyclic (reparam c f) := by
  intro b
  rw [deriv_reparam, rightDeriv_reparam]
  apply sum_congr rfl
  intro a _
  rw [hf a]
 theorem reparam_subst (c : α → β → ℂ) (M f : Series α) :
    reparam c (subst M f) = subst (reparam c M) (reparam c f) := by
  funext w
  induction w using length_induction generalizing f with
  | h w ih =>
    cases w with
    | nil => simp
    | cons b w =>
      rw [reparam_cons, subst_cons, deriv_reparam, subst_sum, conv_sum_right]
      simp only [deriv_subst, reparam_conv, subst_smul, conv_smul_right,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply sum_congr rfl
      intro a _
      congr 1
      apply conv_agree (n := w.length) (Agree.refl _ _) (fun v hv => ?_) w le_rfl
      exact ih v (by simp; omega) (deriv a f)
 theorem reparam_moments (c : α → β → ℂ) {R : Series α} (hR : R [] = 0) :
    reparam c (moments R) = moments (reparam c R) := by
  apply moments_unique (by simpa using hR)
  have hh := congrArg (reparam c) (moments_eq hR)
  simpa only [reparam_add, reparam_unit, reparam_subst] using hh
 theorem restrict_conv {α β : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] (e : β → α) (f g : Series α) :
    restrict e (conv f g) = conv (restrict e f) (restrict e g) := by
  funext w
  simp only [restrict, conv_sum_splits, List.length_map, ← List.map_take, ← List.map_drop]
 theorem restrict_subst (e : β → α) (M f : Series α) :
    restrict e (subst M f) = subst (restrict e M) (restrict e f) := by
  funext w
  induction w using length_induction generalizing f with
  | h w ih =>
    cases w with
    | nil => simp [restrict]
    | cons b w =>
      change subst M f (e b :: w.map e) = _
      rw [subst_cons, subst_cons]
      change restrict e (conv M (subst M (deriv (e b) f))) w = _
      rw [restrict_conv]
      apply conv_agree (n := w.length) (Agree.refl _ _) (fun v hv => ?_) w le_rfl
      exact ih v (by simp; omega) (deriv (e b) f)
 theorem restrict_moments (e : β → α) {R : Series α} (hR : R [] = 0) :
    restrict e (moments R) = moments (restrict e R) := by
  apply moments_unique (show (restrict e R) [] = 0 from hR)
  funext w
  have hh := congrFun (moments_eq hR) (w.map e)
  simp only [Pi.add_apply] at hh
  change moments R (w.map e) = _
  rw [hh]
  congr 1
  · cases w <;> rfl
  · exact congrFun (restrict_subst e _ _) w
end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.EmbeddedSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation.FreeSeries
open Finset
variable {α β γ : Type} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β]

 theorem deriv_liftSeries (e : α → β) (f : Series α) (b : β) :
    deriv b (liftSeries e f) = ∑ a, (if e a=b then (1:ℂ) else 0) • liftSeries e (deriv a f) :=
  deriv_reparam _ _ _
 theorem deriv_liftSeries_image (e : α → β) (he : Function.Injective e) (f : Series α) (a : α) :
    deriv (e a) (liftSeries e f) = liftSeries e (deriv a f) := by
  rw [deriv_liftSeries]
  simp only [he.eq_iff, ite_smul, one_smul, zero_smul]
  simp
 theorem deriv_liftSeries_out (e : α → β) (f : Series α) (b : β)
    (hb : ∀ a, e a ≠ b) : deriv b (liftSeries e f) = 0 := by
  rw [deriv_liftSeries]
  simp [hb]
 theorem liftSeries_letter (e : α → β) (a : α) : liftSeries e (letter a) = letter (e a) := by
  funext w
  cases w with
  | nil => rfl
  | cons b w =>
    rw [liftSeries, reparam_cons]
    simp only [deriv_letter, apply_ite (reparam _), reparam_unit, reparam_zero]
    simp only [ite_apply, Pi.zero_apply, mul_ite, mul_zero]
    simp only [sum_ite_eq', mem_univ, ↓reduceIte]
    cases w with
    | nil => simp [letter, eq_comm]
    | cons d w => cases w <;> simp [letter]
 theorem restrict_liftSeries (e : α → β) (he : Function.Injective e) (f : Series α) :
    restrict e (liftSeries e f) = f := by
  funext w
  induction w generalizing f with
  | nil => rfl
  | cons a w ih =>
    change deriv (e a) (liftSeries e f) (w.map e) = f (a::w)
    rw [deriv_liftSeries_image e he]
    exact ih (deriv a f)
 theorem restrict_liftSeries_disjoint (e : α → β) (d : γ → β)
    (hd : ∀ i j, e i ≠ d j) (f : Series α) (hf : f [] = 0) :
    (fun w : List γ => liftSeries e f (w.map d)) = 0 := by
  funext w
  cases w with
  | nil => exact hf
  | cons a w =>
    change deriv (d a) (liftSeries e f) (w.map d) = 0
    rw [deriv_liftSeries_out e f (d a) (fun i => hd i a)]
    rfl

variable [DecidableEq γ] [Fintype γ]
 theorem reparam_liftSeries (e : α → β) (c : β → γ → ℂ) (f : Series α) :
    reparam c (liftSeries e f) = reparam (fun a d => c (e a) d) f := by
  funext w
  induction w generalizing f with
  | nil => rfl
  | cons d w ih =>
    rw [reparam_cons, reparam_cons]
    simp only [deriv_liftSeries, reparam_sum, reparam_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero]
    simp only [sum_ite_eq, mem_univ, ↓reduceIte]
    rw [ih]
 theorem reparam_identity (f : Series α) : reparam (fun a b : α => if a=b then 1 else 0) f = f := by
  funext w
  have h := congrFun (restrict_liftSeries (id : α → α) Function.injective_id f) w
  change reparam (fun a b : α => if a=b then 1 else 0) f (w.map id) = f w at h
  simpa only [List.map_id] using h
 theorem reparam_scalar (z : ℂ) (f : Series α) (w : List α) :
    reparam (fun a b : α => if a=b then z else 0) f w = z^w.length * f w := by
  induction w generalizing f with
  | nil => simp
  | cons a w ih =>
    rw [reparam_cons]
    simp only [ite_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]
    rw [ih]
    simp [deriv_apply, pow_succ, mul_assoc, mul_left_comm]
 theorem reparam_scalar_quadratic (z : ℂ) :
    reparam (fun a b : α => if a=b then z else 0) quadratic = z^2 • quadratic := by
  funext w
  rw [reparam_scalar]
  cases w with
  | nil => simp
  | cons a w =>
    cases w with
    | nil => simp [quadratic]
    | cons b w => cases w <;> simp [quadratic]

 theorem Cyclic.append {α : Type} [DecidableEq α] [Fintype α] {f : Series α} (hf : Cyclic f) (u v : List α) :
    f (u++v) = f (v++u) := by
  induction u generalizing v with
  | nil => simp
  | cons a u ih =>
    have hh := congrFun (hf a) (u++v)
    change f (a::(u++v)) = f ((u++v)++[a]) at hh
    simp only [List.cons_append, hh, List.append_assoc]
    rw [ih]
    simp
 theorem cyclic_quadratic {α : Type} [DecidableEq α] [Fintype α] : Cyclic (quadratic : Series α) := by
  intro a
  funext w
  cases w with
  | nil => rfl
  | cons b w =>
    cases w with
    | nil => simp [deriv, rightDeriv, quadratic, eq_comm]
    | cons d w => cases w <;> rfl
 theorem deriv_moments {α : Type} [DecidableEq α] [Fintype α] {R : Series α} (hR : R [] = 0) (i : α) :
    deriv i (moments R) = conv (moments R) (subst (moments R) (deriv i R)) := by
  funext w
  have hh := congrFun (moments_eq hR) (i::w)
  simpa [subst_cons] using hh

end FiniteEntropySeparation.FreeSeries

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.WordLinearLaw
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

 theorem wordEval_mem {M : VonNeumannAlgebra H} {n : ℕ}
    (X : Fin n → H →L[ℂ] H) (hX : ∀ i, X i ∈ M) (w : List (Fin n)) : wordEval X w ∈ M := by
  induction w with
  | nil => simp [wordEval]
  | cons i w ih => simpa [wordEval] using M.mul_mem (hX i) ih
 theorem wordMoment_cyclic {M : VonNeumannAlgebra H} (τ : TracialVector M) {n : ℕ}
    (X : Fin n → H →L[ℂ] H) (hX : ∀ i, X i ∈ M) : Cyclic (wordMoment τ X) := by
  intro i
  funext w
  change trace τ ((i::w).map X).prod = trace τ ((w++[i]).map X).prod
  simpa [trace, wordEval, List.map_cons, List.prod_cons, List.map_append, List.prod_append] using
    τ.tracial (X i) (hX i) (wordEval X w) (wordEval_mem X hX w)
 theorem wordMoment_restrict {M : VonNeumannAlgebra H} (τ : TracialVector M) {n m : ℕ}
    (X : Fin n → H →L[ℂ] H) (e : Fin m → Fin n) :
    restrict e (wordMoment τ X) = wordMoment τ (fun i => X (e i)) := by
  funext w
  simp [FreeSeries.restrict, wordMoment, wordEval, List.map_map, Function.comp_def]

 theorem reparam_wordMoment {M : VonNeumannAlgebra H} (τ : TracialVector M) {n m : ℕ}
    (X : Fin n → H →L[ℂ] H) (c : Fin n → Fin m → ℂ) :
    reparam c (wordMoment τ X) = wordMoment τ (fun b => ∑ a, c a b • X a) := by
  let Y := fun b => ∑ a, c a b • X a
  have hh (w : List (Fin m)) (A : H →L[ℂ] H) :
      reparam c (fun v => trace τ (A * wordEval X v)) w = trace τ (A * wordEval Y w) := by
    induction w generalizing A with
    | nil => simp [wordEval]
    | cons b w ih =>
      rw [reparam_cons]
      have hf (a : Fin n) : deriv a (fun v => trace τ (A * wordEval X v)) =
          (fun v => trace τ ((A * X a) * wordEval X v)) := by
        funext v; simp [FreeSeries.deriv, wordEval, mul_assoc]
      simp only [hf, ih]
      change _ = trace τ (A * (Y b * wordEval Y w))
      rw [← mul_assoc]
      dsimp only [Y]
      rw [Finset.mul_sum, Finset.sum_mul, trace_sum]
      apply sum_congr rfl
      intro a _
      simp only [mul_smul_comm, smul_mul_assoc, trace_smul]
  funext w
  change reparam c (fun v => trace τ (wordEval X v)) w = trace τ (wordEval Y w)
  simpa only [one_mul] using hh w 1

 theorem pairDerivative_eq {n : ℕ} (M : Series (Fin n)) (i : Fin n) (w : List (Fin n)) :
    conv M (subst M (letter i)) w = ∑ r : Fin w.length, if w[r.val] = i then
      M (w.take r.val) * M (w.drop (r.val+1)) else 0 := by
  rw [← deriv_quadratic i, ← subst_cons]
  exact quadratic_subst_derivative M i w
 theorem derivativeMoment_series {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (X : Fin n → H →L[ℂ] H) (i : Fin n) :
    (fun w => derivativeMoment τ X i w) =
      conv (wordMoment τ X) (subst (wordMoment τ X) (letter i)) := by
  funext w
  rw [pairDerivative_eq]
  rfl
 theorem pairDerivative_congr {α : Type} [DecidableEq α] [Fintype α]
    {M N : Series α} {k : ℕ} (h : Agree k M N) (i : α) :
    Agree k (conv M (subst M (letter i))) (conv N (subst N (letter i))) :=
  conv_agree h (subst_agree h (Agree.refl _ _))

end FiniteEntropySeparation

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

namespace FreeTensor

variable {B N A : Type} [DecidableEq B] [DecidableEq N] [AddCommGroup A]
  [Fintype A] [DecidableEq A]

 theorem spectralSignal_selfAdjoint (y : AddChar A ℂ → ℝ) :
    IsSelfAdjoint (spectralSignal (B := B) (N := N) y) := by
  show star _ = _
  simp [spectralSignal,
    star_sum (R := Space B N (Multiplicative A) →L[ℂ] Space B N (Multiplicative A))]

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

namespace FreeTensor
variable {B N : Type} [DecidableEq B] [DecidableEq N] (p : ℕ) [NeZero p]

 theorem equidiscreteSignal_selfAdjoint : IsSelfAdjoint (equidiscreteSignal (B := B) (N := N) p) :=
  spectralSignal_selfAdjoint _

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

 theorem backgroundAlgebra_le (J : Set N) :
    backgroundAlgebra (B := B) (G := G) J ≤ (algebra B N G).toStarSubalgebra.toSubalgebra := by
  apply Algebra.adjoin_le
  rintro _ ((⟨b,rfl⟩ | ⟨g,rfl⟩) | ⟨i,_,rfl⟩)
  · exact semicircularB_mem b
  · exact unitaryG_mem g
  · exact semicircularN_mem i

 theorem semicircularB_mem_background (J : Set N) (b : B) :
    semicircularB (N := N) (G := G) b ∈ backgroundAlgebra J :=
  Algebra.subset_adjoin (Or.inl (Or.inl ⟨b,rfl⟩))
 theorem semicircularN_mem_background (J : Set N) {i : N} (hi : i ∈ J) :
    semicircularN (B := B) (G := G) i ∈ backgroundAlgebra J :=
  Algebra.subset_adjoin (Or.inr ⟨i,hi,rfl⟩)

 theorem heatTuple_selfAdjoint {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {n : ℕ} (X S : Fin n → H →L[ℂ] H)
    (hX : ∀ i, IsSelfAdjoint (X i)) (hS : ∀ i, IsSelfAdjoint (S i)) (u : ℝ) (i : Fin n) :
    IsSelfAdjoint (heatTuple X S u i) := by
  change star (X i + (Real.sqrt u : ℂ) • S i) = _
  simp only [star_add, star_smul, Complex.star_def, Complex.conj_ofReal, (hX i).star_eq,
    (hS i).star_eq, heatTuple]

 theorem heatTuple_mem_background {n : ℕ} (J : Set N)
    (X S : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J) (hS : ∀ i, S i ∈ backgroundAlgebra J)
    (u : ℝ) (i : Fin n) : heatTuple X S u i ∈ backgroundAlgebra J :=
  (backgroundAlgebra J).add_mem (hX i) ((backgroundAlgebra J).smul_mem (hS i) _)

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

 theorem X_mem_background (h : ℝ) (i : Fin (p+1)) :
    X p h i ∈ backgroundAlgebra (oldNoise p) := by
  apply heatTuple_mem_background _ _ _ (C_mem_background p (oldNoise p))
  intro j
  exact semicircularN_mem_background _ ⟨j,rfl⟩

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
-- module Solutions.OAIQW_FiniteEntropySeparation.MixedGaussianSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation
open Finset FreeSeries
namespace FreeSeries
variable {n : ℕ}
 theorem leftIndex_injective : Function.Injective (leftIndex (n := n)) := Fin.castAdd_injective n n
 theorem rightIndex_injective : Function.Injective (rightIndex (n := n)) := Fin.natAdd_injective n n
 theorem leftIndex_ne_rightIndex (i j : Fin n) : leftIndex i ≠ rightIndex j := by
  intro h
  have hh := congrArg Fin.val h
  simp [leftIndex, rightIndex] at hh
  have hi := i.isLt
  omega
 theorem joint_cases (j : Fin (n+n)) : (∃i, j=leftIndex i) ∨ (∃i, j=rightIndex i) := by
  induction j using Fin.addCases with
  | left i => exact Or.inl ⟨i,rfl⟩
  | right i => exact Or.inr ⟨i,rfl⟩
 theorem gaussianJointR_noise_deriv (R : Series (Fin n)) (i : Fin n) :
    FreeSeries.deriv (rightIndex i) (gaussianJointR R) = letter (rightIndex i) := by
  change FreeSeries.deriv (rightIndex i) (liftSeries leftIndex R) +
    FreeSeries.deriv (rightIndex i) (liftSeries rightIndex quadratic) = _
  rw [deriv_liftSeries_out _ _ _ (fun j => leftIndex_ne_rightIndex j i),
    deriv_liftSeries_image _ rightIndex_injective, deriv_quadratic, liftSeries_letter, zero_add]
 theorem gaussianJointR_restrict (R : Series (Fin n)) : restrict leftIndex (gaussianJointR R) = R := by
  have hh := restrict_liftSeries_disjoint (rightIndex (n := n)) leftIndex
    (fun i j => (leftIndex_ne_rightIndex j i).symm) (quadratic : Series (Fin n)) quadratic_nil
  have hl := restrict_liftSeries (leftIndex (n := n)) leftIndex_injective R
  funext w
  exact (congrArg₂ (·+·) (congrFun hl w) (congrFun hh w)).trans (add_zero _)
 theorem gaussianJointR_cyclic {R : Series (Fin n)} (hR : Cyclic R) : Cyclic (gaussianJointR R) := by
  have hL := hR.reparam (fun a b => if leftIndex a=b then (1:ℂ) else 0)
  have hN := (cyclic_quadratic (α := Fin n)).reparam (fun a b => if rightIndex a=b then (1:ℂ) else 0)
  intro i
  change FreeSeries.deriv i (liftSeries leftIndex R) + FreeSeries.deriv i (liftSeries rightIndex quadratic) =
    rightDeriv i (liftSeries leftIndex R) + rightDeriv i (liftSeries rightIndex quadratic)
  exact congrArg₂ (·+·) (hL i) (hN i)
 theorem word_left_or_noise (w : List (Fin (n+n))) :
    (∃ v : List (Fin n), w=v.map leftIndex) ∨ (∃u i v, w=u++rightIndex i::v) := by
  induction w with
  | nil => exact Or.inl ⟨[],rfl⟩
  | cons a w ih =>
    rcases joint_cases a with ⟨i,rfl⟩ | ⟨i,rfl⟩
    · rcases ih with ⟨v,rfl⟩ | ⟨u,j,v,rfl⟩
      · exact Or.inl ⟨i::v,rfl⟩
      · exact Or.inr ⟨leftIndex i::u,j,v,rfl⟩
    · exact Or.inr ⟨[],i,w,rfl⟩

theorem mixed_gaussian_unique {M N : Series (Fin (n+n))}
    (hM : Cyclic M) (hN : Cyclic N) (hleft : restrict leftIndex M = restrict leftIndex N)
    (hm : ∀ i, FreeSeries.deriv (rightIndex i) M = conv M (subst M (letter (rightIndex i))))
    (hn : ∀ i, FreeSeries.deriv (rightIndex i) N = conv N (subst N (letter (rightIndex i)))) : M=N := by
  funext w
  induction w using length_induction with
  | h w ih =>
    rcases word_left_or_noise w with ⟨v,rfl⟩ | ⟨u,i,v,rfl⟩
    · exact congrFun hleft v
    · rw [hM.append u _, hN.append u _]
      change FreeSeries.deriv (rightIndex i) M (v++u) = FreeSeries.deriv (rightIndex i) N (v++u)
      rw [hm, hn]
      exact pairDerivative_congr (fun z hz => ih z (by simp at hz ⊢; omega)) _ (v++u) le_rfl
 theorem moments_cumulants {α : Type} [DecidableEq α] [Fintype α] {M : Series α} (hM : M [] = 1) :
    moments (cumulants M) = M := (moments_unique (cumulants_nil M) (cumulants_equation hM)).symm
end FreeSeries

namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
variable {n : ℕ}
 theorem jointTuple_mem (J : Set N) (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (hX : ∀ i, X i ∈ backgroundAlgebra J) (σ : Fin n → N) (j : Fin (n+n)) :
    jointTuple X σ j ∈ algebra B N G := by
  rcases joint_cases j with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · rw [jointTuple_left]; exact backgroundAlgebra_le J (hX i)
  · rw [jointTuple_right]; exact semicircularN_mem _
 theorem jointTuple_noise_deriv (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J) (i : Fin n) :
    FreeSeries.deriv (rightIndex i) (wordMoment (tracialVector B N G) (jointTuple X σ)) =
      conv (wordMoment (tracialVector B N G) (jointTuple X σ))
        (subst (wordMoment (tracialVector B N G) (jointTuple X σ)) (letter (rightIndex i))) := by
  let Z := jointTuple X σ
  let τ := tracialVector B N G
  have hc (j : Fin (n+n)) : star (rightCreationN (σ i)) * Z j =
      Z j * star (rightCreationN (σ i)) + if j=rightIndex i then (1:ℂ) • vacuumRankOne τ else 0 := by
    rcases joint_cases j with ⟨k,rfl⟩ | ⟨k,rfl⟩
    · simpa [Z, leftIndex_ne_rightIndex] using (rightAnnihilationN_background (hs i) (hX k)).eq
    · have he : σ i = σ k ↔ rightIndex k = rightIndex i := by
        rw [hσ.eq_iff, rightIndex_injective.eq_iff, eq_comm]
      simpa [Z, he] using rightAnnihilationN_semicircularN (B := B) (G := G) (σ i) (σ k)
  funext w
  rw [← derivativeMoment_series]
  have h := commutator_integration_by_parts τ Z (star (rightCreationN (σ i)))
    (rightIndex i) 1 hc (by simp [τ, tracialVector, basis, empty]) w
  simp only [star_star, one_mul] at h
  have hv : rightCreationN (σ i) τ.vacuum = semicircularN (σ i) τ.vacuum := by
    simp [τ, tracialVector, semicircularN, basis, rightCreationN_single, creationN_single,
      annihilationN_single, removeN, rightN_eq_append, empty, append, leftN, push]
  rw [hv, ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    (semicircularN_selfAdjoint (B := B) (G := G) (σ i)).star_eq] at h
  change trace τ (semicircularN (σ i) * wordEval Z w) = _ at h
  simpa [FreeSeries.deriv, wordMoment, wordEval, Z] using h

 theorem joint_moments_cumulants (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J) :
    wordMoment (tracialVector B N G) (jointTuple X σ) =
      moments (gaussianJointR (cumulants (wordMoment (tracialVector B N G) X))) := by
  let τ := tracialVector B N G
  let M := wordMoment τ X
  have hM : M [] = 1 := by simp [M]
  have hC : Cyclic M := wordMoment_cyclic τ X (fun i => backgroundAlgebra_le J (hX i))
  let R := gaussianJointR (cumulants M)
  have hR : R [] = 0 := gaussianJointR_nil _ (cumulants_nil M)
  apply mixed_gaussian_unique
  · exact wordMoment_cyclic τ _ (jointTuple_mem J X hX σ)
  · exact cyclic_moments hR (gaussianJointR_cyclic (cyclic_cumulants hM hC))
  · rw [restrict_moments leftIndex hR, gaussianJointR_restrict, moments_cumulants hM, wordMoment_restrict]
    congr 1
    funext i
    exact jointTuple_left X σ i
  · exact jointTuple_noise_deriv J X hX σ hσ hs
  · intro i
    rw [deriv_moments hR, gaussianJointR_noise_deriv]
end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.HeatCumulants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation
open Finset FreeSeries
namespace FreeSeries
variable {n : ℕ}

 theorem heatCoefficients_R (u : ℝ) (hu : 0 ≤ u) (R : Series (Fin n)) :
    reparam (heatCoefficients u) (gaussianJointR R) = R + (u : ℂ) • quadratic := by
  rw [gaussianJointR, reparam_add, reparam_liftSeries, reparam_liftSeries]
  simp only [heatCoefficients_left, heatCoefficients_right, reparam_identity, reparam_scalar_quadratic]
  congr 2
  exact_mod_cast Real.sq_sqrt hu
end FreeSeries

namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
variable {n : ℕ}
 theorem heat_linear_tuple (X : Fin n → Space B N G →L[ℂ] Space B N G)
    (σ : Fin n → N) (u : ℝ) :
    (fun i => ∑ j, heatCoefficients u j i • jointTuple X σ j) =
      heatTuple X (fun i => semicircularN (σ i)) u := by
  funext i
  rw [Fin.sum_univ_add]
  change (∑ j : Fin n, heatCoefficients u (leftIndex j) i • jointTuple X σ (leftIndex j)) +
    (∑ j : Fin n, heatCoefficients u (rightIndex j) i • jointTuple X σ (rightIndex j)) = _
  simp only [heatCoefficients_left, heatCoefficients_right, jointTuple_left,
    jointTuple_right, ite_smul, one_smul,
    zero_smul ℂ (A := Space B N G →L[ℂ] Space B N G), Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, heatTuple]

theorem heat_moments_cumulants (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J)
    (u : ℝ) (hu : 0 ≤ u) :
    wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u) =
      moments (cumulants (wordMoment (tracialVector B N G) X) + (u : ℂ) • quadratic) := by
  rw [← heat_linear_tuple X σ u, ← reparam_wordMoment,
    joint_moments_cumulants J X hX σ hσ hs,
    reparam_moments (heatCoefficients u) (gaussianJointR_nil _ (cumulants_nil _)),
    heatCoefficients_R u hu]
 theorem heat_cumulants (J : Set N)
    (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀ i, X i ∈ backgroundAlgebra J)
    (σ : Fin n → N) (hσ : Function.Injective σ) (hs : ∀ i, σ i ∉ J)
    (u : ℝ) (hu : 0 ≤ u) :
    cumulants (wordMoment (tracialVector B N G) (heatTuple X (fun i => semicircularN (σ i)) u)) =
      cumulants (wordMoment (tracialVector B N G) X) + (u : ℂ) • quadratic := by
  let R := cumulants (wordMoment (tracialVector B N G) X) + (u : ℂ) • quadratic
  have hR : R [] = 0 := by simp [R]
  rw [heat_moments_cumulants J X hX σ hσ hs u hu]
  exact (cumulants_unique (moments_nil _) (moments_eq hR)).symm
end FreeTensor
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

 theorem fisher_le_scaled_test {M : VonNeumannAlgebra H} (τ : TracialVector M)
    {n : ℕ} (Z : Fin n → H →L[ℂ] H) (η : Fin n → H) (v : ℝ) (hv : 0 < v)
    (ht : ∀ i w, inner ℂ (η i) (wordEval Z w τ.vacuum) =
      (v : ℂ) * derivativeMoment τ Z i w)
    (hn : ∀ i, ‖η i‖ ^ 2 ≤ v) : freeFisher τ Z ≤ ENNReal.ofReal ((n : ℝ)/v) := by
  have ht' (i : Fin n) (w : List (Fin n)) :
      inner ℂ ((v⁻¹ : ℂ) • η i) (wordEval Z w τ.vacuum) = derivativeMoment τ Z i w := by
    rw [inner_smul_left, ht i w]
    simp [hv.ne']
  apply (freeFisher_le_testVectors τ Z (fun i => ((v⁻¹ : ℂ) • η i)) ht').trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = ∑ i, v⁻¹ ^ 2 * ‖η i‖ ^ 2 := by
      simp only [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, mul_pow, inv_pow, sq_abs]
    _ ≤ ∑ _i : Fin n, v⁻¹ ^ 2 * v := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hn i) (sq_nonneg _))
    _ = _ := by simp [pow_two, hv.ne', div_eq_mul_inv]

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

end FreeTensor
namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]

 theorem initialIndex_fresh (i : Fin (p+1)) : initialIndex p i ∉ Set.range (auxiliaryIndex p) := by
  rintro ⟨j,h⟩
  exact auxiliaryIndex_fresh p j ⟨i,h.symm⟩

 theorem doublyNoised_comm (h s : ℝ) : doublyNoised p h s =
    heatTuple (heatTuple (C p) (auxiliaryNoise p) s) (initialNoise p) h := by
  funext i
  simp only [doublyNoised, X, heatTuple]
  abel

 theorem auxiliaryBackground_mem (s : ℝ) (i : Fin (p+1)) :
    heatTuple (C p) (auxiliaryNoise p) s i ∈ backgroundAlgebra (Set.range (auxiliaryIndex p)) := by
  apply heatTuple_mem_background _ _ _ (C_mem_background p _)
  intro j
  exact semicircularN_mem_background _ ⟨j,rfl⟩

 theorem noiseVector₀_test (h s : ℝ) (i : Fin (p+1)) (w : List (Fin (p+1))) :
    inner ℂ (noiseVector₀ p i) (wordEval (doublyNoised p h s) w (τ p).vacuum) =
      (Real.sqrt h : ℂ) * derivativeMoment (τ p) (doublyNoised p h s) i w := by
  rw [doublyNoised_comm]
  exact noise_basis_test _ _ (auxiliaryBackground_mem p s)
    (initialIndex p) (initialIndex_injective p) (initialIndex_fresh p) h i w

 theorem noiseVector₁_test (h s : ℝ) (i : Fin (p+1)) (w : List (Fin (p+1))) :
    inner ℂ (noiseVector₁ p i) (wordEval (doublyNoised p h s) w (τ p).vacuum) =
      (Real.sqrt s : ℂ) * derivativeMoment (τ p) (doublyNoised p h s) i w :=
  noise_basis_test _ _ (X_mem_background p h)
    (auxiliaryIndex p) (auxiliaryIndex_injective p) (auxiliaryIndex_fresh p) s i w

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

theorem doublyNoised_fisher_le (h s : ℝ) (hh : 0 ≤ h) (hs : 0 ≤ s) (hu : 0 < h+s) :
    freeFisher (τ p) (doublyNoised p h s) ≤ ENNReal.ofReal ((p+1 : ℕ)/(h+s)) := by
  let η : Fin (p+1) → H p := fun i => (Real.sqrt h : ℂ) • noiseVector₀ p i +
    (Real.sqrt s : ℂ) • noiseVector₁ p i
  apply fisher_le_scaled_test (τ p) _ η (h+s) hu
  · intro i w
    simp only [η, inner_add_left, inner_smul_left, Complex.conj_ofReal,
      noiseVector₀_test, noiseVector₁_test, ← mul_assoc, ← pow_two]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, Real.sq_sqrt hh, Real.sq_sqrt hs]
    push_cast
    ring
  · intro i
    exact (norm_sq_sqrt_pair (noiseVector₀_norm p i) (noiseVector₁_norm p i)
      (noiseVector_orthogonal p i i) h s hh hs).le

end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.NoiseRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteEntropySeparation
open FreeSeries
namespace FreeSeries
variable {α : Type}
 theorem cumulants_injective_normalized {M N : Series α} (hM : M [] = 1) (hN : N [] = 1)
    (h : cumulants M = cumulants N) : M = N := by
  have hm := moments_unique (cumulants_nil M) (cumulants_equation hM)
  have hn := moments_unique (cumulants_nil N) (cumulants_equation hN)
  rw [hm, hn, h]
end FreeSeries
namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]
 theorem X_cumulants (h : ℝ) (hh : 0 ≤ h) :
    cumulants (wordMoment (τ p) (X p h)) =
      cumulants (wordMoment (τ p) (C p)) + (h : ℂ) • quadratic :=
  heat_cumulants ∅ (C p) (C_mem_background p ∅) (initialIndex p)
    (initialIndex_injective p) (by simp) h hh
 theorem doublyNoised_cumulants (h s : ℝ) (hh : 0 ≤ h) (hs : 0 ≤ s) :
    cumulants (wordMoment (τ p) (doublyNoised p h s)) =
      cumulants (wordMoment (τ p) (C p)) + ((h+s : ℝ) : ℂ) • quadratic := by
  calc
    _ = cumulants (wordMoment (τ p) (X p h)) + (s : ℂ) • quadratic :=
      heat_cumulants (oldNoise p) (X p h) (X_mem_background p h)
        (auxiliaryIndex p) (auxiliaryIndex_injective p) (auxiliaryIndex_fresh p) s hs
    _ = _ := by rw [X_cumulants p h hh]; simp [add_smul, add_assoc]
 theorem doublyNoised_law (h s : ℝ) (hh : 0 ≤ h) (hs : 0 ≤ s) :
    wordMoment (τ p) (doublyNoised p h s) = wordMoment (τ p) (X p (h+s)) := by
  apply cumulants_injective_normalized (by simp) (by simp)
  rw [doublyNoised_cumulants p h s hh hs, X_cumulants p (h+s) (add_nonneg hh hs)]
 theorem doublyNoised_fisher_eq (h s : ℝ) (hh : 0 ≤ h) (hs : 0 ≤ s) (hu : 0 < h+s) :
    freeFisher (τ p) (doublyNoised p h s) = freeFisher (τ p) (X p (h+s)) := by
  apply freeFisher_eq_of_wordMoments (τ p) (τ p)
  · intro i
    exact heatTuple_selfAdjoint (X p h) (auxiliaryNoise p) (X_selfAdjoint p h)
      (auxiliaryNoise_selfAdjoint p) s i
  · exact X_selfAdjoint p (h+s)
  · exact congrFun (doublyNoised_law p h s hh hs)
  · exact exists_conjugate_of_fisher_le _ _ ((p+1 : ℕ)/(h+s))
      (doublyNoised_fisher_le p h s hh hs hu)
  · exact heat_conjugates_exist ∅ (C p) (C_mem_background p ∅) (initialIndex p)
      (initialIndex_injective p) (by simp) (h+s) hu
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
 theorem chosenP_ge_two : 2≤chosenP := by norm_num [chosenP]
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
 theorem normal_prefactor_bounded {a b : ℝ} (ha : 0<a) :
    ∃ D : ℝ,0 ≤ D ∧ ∀s∈Icc a b, |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)| ≤ D := by
  have hc : ContinuousOn (fun s : ℝ => -(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)) (Icc a b) := by
    apply continuousOn_const.mul
    apply ContinuousOn.log (by fun_prop)
    intro s hs; exact ne_of_gt (by have : 0<s := ha.trans_le hs.1; positivity)
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro s hs
  exact (show |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)| ≤ D by simpa only [Real.norm_eq_abs] using hD s hs).trans (le_max_left _ _)
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
 theorem integrable_of_normBound (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {K : ℝ} (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) {f : EuclideanSpace ℝ ι → ℝ} (hf : Continuous f) : Integrable f μ := by
  apply integrable_of_compact_ae μ (isCompact_closedBall (0 : EuclideanSpace ℝ ι) K) _ hf.aestronglyMeasurable hf.continuousOn
  simpa only [Metric.mem_closedBall,dist_zero_right] using hμ
 theorem smoothedGradient_bound (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {a s K : ℝ} (ha : 0<a) (hs : a ≤ s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K)
    (x : EuclideanSpace ℝ ι) (i : ι) :
    |smoothedGradient μ s x i| ≤ ((‖x‖+K)/a)*smoothedDensity μ s x := by
  have hs0 := ha.trans_le hs
  have hi : Integrable (fun y => normalGradient s (x-y) i) μ := integrable_of_normBound μ hμ ((normalGradient_continuous s i).comp (continuous_const.sub continuous_id))
  calc
    _  ≤  ∫y,|normalGradient s (x-y) i| ∂μ := by simpa only [smoothedGradient,Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => normalGradient s (x-y) i)
    _  ≤  ∫y,((‖x‖+K)/a)*normalKernel s (x-y) ∂μ := by
      apply integral_mono_ae hi.norm ((normalKernel_integrable_finite μ hs0 x).const_mul _)
      filter_upwards [hμ] with y hy
      unfold normalGradient
      rw [Real.norm_eq_abs,abs_mul,abs_div,abs_neg,abs_of_pos hs0,abs_of_pos (normalKernel_pos _ _)]
      apply mul_le_mul_of_nonneg_right _ (normalKernel_pos _ _).le
      have hn0 : |(x-y) i| ≤ ‖x-y‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (x-y) i
      have hn : |(x-y) i| ≤ ‖x‖+K := hn0.trans ((norm_sub_le x y).trans (add_le_add le_rfl hy))
      exact (div_le_div_of_nonneg_right hn hs0.le).trans (div_le_div_of_nonneg_left (by positivity) ha hs)
    _ = _ := integral_const_mul _ _
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
 theorem smoothedGradient_measurable (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    (s : ℝ) (i : ι) : StronglyMeasurable (fun x => smoothedGradient μ s x i) := by
  exact (((normalGradient_continuous s i).comp (continuous_fst.sub continuous_snd)).stronglyMeasurable).integral_prod_right'
 theorem smoothedSecond_measurable (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    (s : ℝ) (i : ι) : StronglyMeasurable (fun x => smoothedSecond μ s x i) := by
  exact (((normalSecond_continuous s i).comp (continuous_fst.sub continuous_snd)).stronglyMeasurable).integral_prod_right'
 theorem smoothedTime_measurable (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    (s : ℝ) : StronglyMeasurable (smoothedTimeDerivative μ s) := by
  have hc : Continuous (fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => normalTimeDerivative s (z.1-z.2)) := by
    unfold normalTimeDerivative normalKernel
    fun_prop
  exact hc.stronglyMeasurable.integral_prod_right'
 theorem smoothedSecond_bound (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {a s K : ℝ} (ha : 0<a) (hs : a ≤ s) (_hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K)
    (x : EuclideanSpace ℝ ι) (i : ι) :
    |smoothedSecond μ s x i| ≤ (((‖x‖+K)^2/a^2)+1/a)*smoothedDensity μ s x := by
  have hs0 := ha.trans_le hs
  have hi : Integrable (fun y => normalSecond s (x-y) i) μ := integrable_of_normBound μ hμ ((normalSecond_continuous s i).comp (continuous_const.sub continuous_id))
  calc
    _ ≤ ∫y,|normalSecond s (x-y) i| ∂μ := by simpa only [smoothedSecond,Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => normalSecond s (x-y) i)
    _ ≤ ∫y,(((‖x‖+K)^2/a^2)+1/a)*normalKernel s (x-y) ∂μ := by
      apply integral_mono_ae hi.norm ((normalKernel_integrable_finite μ hs0 x).const_mul _)
      filter_upwards [hμ] with y hy
      unfold normalSecond
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (normalKernel_pos _ _)]
      apply mul_le_mul_of_nonneg_right _ (normalKernel_pos _ _).le
      have hn0 : |(x-y) i| ≤ ‖x-y‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (x-y) i
      have hn : |(x-y) i| ≤ ‖x‖+K := hn0.trans ((norm_sub_le x y).trans (add_le_add le_rfl hy))
      have hn2 : ((x-y) i)^2 ≤ (‖x‖+K)^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hn 2
      calc
        _ ≤ |((x-y) i)^2/s^2|+|1/s| := abs_sub _ _
        _ = ((x-y) i)^2/s^2+1/s := by rw [abs_of_nonneg (by positivity),abs_of_pos (by positivity)]
        _ ≤ _ := add_le_add
          ((div_le_div_of_nonneg_right hn2 (sq_nonneg s)).trans (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (pow_le_pow_left₀ ha.le hs 2)))
          (one_div_le_one_div_of_le ha hs)
    _ = _ := integral_const_mul _ _
 theorem smoothedSecond_polynomial_bound (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {a s K : ℝ} (ha : 0<a) (hs : a ≤ s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K)
    (x : EuclideanSpace ℝ ι) (i : ι) :
    |smoothedSecond μ s x i| ≤ (2*(1+K^2)/a^2+1/a)*(1+‖x‖^2)*smoothedDensity μ s x := by
  apply (smoothedSecond_bound μ ha hs hK hμ x i).trans
  apply mul_le_mul_of_nonneg_right _ (smoothedDensity_pos μ (ha.trans_le hs) x).le
  have hq : 1 ≤ 1+‖x‖^2 := le_add_of_nonneg_right (sq_nonneg _)
  have hn : (‖x‖+K)^2 ≤ 2*(1+K^2)*(1+‖x‖^2) := by nlinarith [sq_nonneg (‖x‖-K),mul_nonneg (sq_nonneg K) (sq_nonneg ‖x‖)]
  have h := div_le_div_of_nonneg_right hn (sq_nonneg a)
  have h' := mul_le_mul_of_nonneg_left hq (show 0 ≤ 1/a by positivity)
  convert add_le_add h h' using 1 <;> ring
 theorem smoothedGradient_polynomial_bound (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {a s K : ℝ} (ha : 0<a) (hs : a ≤ s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K)
    (x : EuclideanSpace ℝ ι) (i : ι) :
    |smoothedGradient μ s x i| ≤ ((1+K)/a)*(1+‖x‖^2)*smoothedDensity μ s x := by
  apply (smoothedGradient_bound μ ha hs hK hμ x i).trans
  apply mul_le_mul_of_nonneg_right _ (smoothedDensity_pos μ (ha.trans_le hs) x).le
  have h : ‖x‖+K ≤ (1+K)*(1+‖x‖^2) := by nlinarith [sq_nonneg (‖x‖-1/2),mul_nonneg hK (sq_nonneg ‖x‖)]
  convert div_le_div_of_nonneg_right h ha.le using 1 ; ring
 theorem smoothedTime_polynomial_bound (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {a s K : ℝ} (ha : 0<a) (hs : a ≤ s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K)
    (x : EuclideanSpace ℝ ι) :
    |smoothedTimeDerivative μ s x| ≤ ((Fintype.card ι:ℝ)/2*(2*(1+K^2)/a^2+1/a))*(1+‖x‖^2)*smoothedDensity μ s x := by
  classical
  have hmem : ∀ᵐ y ∂μ,y∈Metric.closedBall 0 K := by simpa only [Metric.mem_closedBall,dist_zero_right] using hμ
  rw [smoothed_heatEquation μ (isCompact_closedBall _ _) hmem,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  calc
    _ ≤ (1/2:ℝ)*∑i,|smoothedSecond μ s x i| := mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ (1/2:ℝ)*∑_i : ι,(2*(1+K^2)/a^2+1/a)*(1+‖x‖^2)*smoothedDensity μ s x :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => smoothedSecond_polynomial_bound μ ha hs hK hμ x i)) (by norm_num)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
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
 theorem smoothedLog_constant (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s K : ℝ} (hs : 0<s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) :
    ∃ L : ℝ,0 ≤ L ∧ ∀x,|1+Real.log (smoothedDensity μ s x)| ≤ L*(1+‖x‖^2) := by
  let D := |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)|
  refine ⟨1+D+(1+K^2)/s,by dsimp [D]; positivity,?_⟩
  intro x
  have h := smoothedLog_polynomial_bound μ hs (show s∈Icc s s from ⟨le_rfl,le_rfl⟩) (abs_nonneg _) (show |-(Fintype.card ι:ℝ)/2*Real.log (2*Real.pi*s)| ≤ D from le_rfl) hK hμ x
  have h' := abs_add_le (1:ℝ) (Real.log (smoothedDensity μ s x))
  norm_num only [abs_one] at h'
  dsimp [D]
  nlinarith [sq_nonneg ‖x‖]
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
 theorem smoothedLog_mul_integrable (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s K : ℝ} (hs : 0<s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K)
    {g : EuclideanSpace ℝ ι → ℝ} (hg : StronglyMeasurable g) (C : ℝ) (_hC : 0 ≤ C)
    (hb : ∀x,|g x| ≤ C*(1+‖x‖^2)*smoothedDensity μ s x) :
    Integrable (fun x => (1+Real.log (smoothedDensity μ s x))*g x) := by
  obtain ⟨L,hL,hlog⟩ := smoothedLog_constant μ hs hK hμ
  apply smoothedIntegrable_of_bound μ hs hK hμ
    (((continuous_const.add (smoothedLog_continuous μ hs)).stronglyMeasurable.mul hg).aestronglyMeasurable) (L*C) 2
  intro x
  simp only [Pi.mul_apply,Pi.add_apply]
  rw [Real.norm_eq_abs,abs_mul]
  calc _ ≤ (L*(1+‖x‖^2))*(C*(1+‖x‖^2)*smoothedDensity μ s x) :=
          mul_le_mul (hlog x) (hb x) (abs_nonneg _) (by positivity)
       _ = _ := by ring
 theorem smoothedScore_integrable (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s K : ℝ} (hs : 0<s) (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) (i : ι) :
    Integrable (fun x => (smoothedGradient μ s x i)^2/smoothedDensity μ s x) := by
  let C := (1+K)/s
  apply smoothedIntegrable_of_bound μ hs hK hμ
    (((smoothedGradient_measurable μ s i).pow 2).div (smoothedDensity_continuous μ hs).stronglyMeasurable).aestronglyMeasurable (C^2) 2
  intro x
  simp only [Pi.pow_apply,Pi.div_apply]
  have hp := smoothedDensity_pos μ hs x
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ hp).mpr
  have hb := smoothedGradient_polynomial_bound μ hs le_rfl hK hμ x i
  have hh := pow_le_pow_left₀ (abs_nonneg _) hb 2
  simp only [sq_abs] at hh
  dsimp only [C]
  nlinarith
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.CoordinateIBP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
 theorem integral_coordinate_ibp (i : ι) (f f' g g' : EuclideanSpace ℝ ι → ℝ)
    (hf : ∀x r,HasDerivAt (fun t : ℝ => f (x+t • EuclideanSpace.single i 1)) (f' (x+r • EuclideanSpace.single i 1)) r)
    (hg : ∀x r,HasDerivAt (fun t : ℝ => g (x+t • EuclideanSpace.single i 1)) (g' (x+r • EuclideanSpace.single i 1)) r)
    (hfg' : Integrable (fun x => f x*g' x)) (hf'g : Integrable (fun x => f' x*g x))
    (hfg : Integrable (fun x => f x*g x)) :
    (∫x,f x*g' x) = -(∫x,f' x*g x) := by
  apply integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℝ) hf'g hfg' hfg
  · intro x hx
    simpa only [HasLineDerivAt,zero_smul,add_zero] using hf x 0
  · intro x hx
    simpa only [HasLineDerivAt,zero_smul,add_zero] using hg x 0
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianDeBruijn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory Filter Set Finset
open scoped Topology
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
 theorem smoothedEntropy_hasDeriv_time (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {K s : ℝ} (_hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) (hs : 0<s) (x : EuclideanSpace ℝ ι) :
    HasDerivAt (fun t => smoothedDensity μ t x*Real.log (smoothedDensity μ t x))
      ((1+Real.log (smoothedDensity μ s x))*smoothedTimeDerivative μ s x) s := by
  have hm : ∀ᵐ y ∂μ,y∈Metric.closedBall 0 K := by simpa only [Metric.mem_closedBall,dist_zero_right] using hμ
  have hd := smoothedDensity_hasDeriv_time μ (isCompact_closedBall _ _) hm hs x
  have hp := (smoothedDensity_pos μ hs x).ne'
  convert hd.mul (hd.log hp) using 1 <;> first | rfl | (field_simp [hp]; ring)
 theorem classicalEntropy_hasDeriv_integral (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {K s : ℝ} (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) (hs : 0<s) :
    HasDerivAt (classicalEntropy μ)
      (-(∫x,(1+Real.log (smoothedDensity μ s x))*smoothedTimeDerivative μ s x)) s := by
  let a := s/2
  let b := s+1
  have ha : 0<a := by dsimp [a]; linarith
  have hb : 0<b := by dsimp [b]; linarith
  obtain ⟨D,hD0,hD⟩ := normal_prefactor_bounded (ι := ι) (b := b) ha
  let L := 1+D+(1+K^2)/a
  let T := (Fintype.card ι:ℝ)/2*(2*(1+K^2)/a^2+1/a)
  let A := Real.exp (D+K^2/(2*b))
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hA : 0 ≤ A := (Real.exp_pos _).le
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x => smoothedDensity μ t x*Real.log (smoothedDensity μ t x))
    (F' := fun t x => (1+Real.log (smoothedDensity μ t x))*smoothedTimeDerivative μ t x)
    (μ := volume) (s := Icc a b) (bound := fun x => (L*T*A)*(1+‖x‖^2)^2*Real.exp (-(1/(4*b))*‖x‖^2))
    (x₀ := s) (Icc_mem_nhds (by dsimp [a]; linarith) (by dsimp [b]; linarith)) ?_ ?_ ?_ ?_ ?_ ?_
  · exact hd.2.neg
  · filter_upwards [Icc_mem_nhds (show a<s by dsimp [a]; linarith) (show s<b by dsimp [b]; linarith)] with t ht
    have ht0 := ha.trans_le ht.1
    exact ((smoothedDensity_continuous μ ht0).mul (smoothedLog_continuous μ ht0)).aestronglyMeasurable
  · exact smoothedEntropy_integrable μ hs hK hμ
  · exact ((continuous_const.add (smoothedLog_continuous μ hs)).stronglyMeasurable.mul (smoothedTime_measurable μ s)).aestronglyMeasurable
  · exact ae_of_all _ (fun x t ht => by
      have ht0 := ha.trans_le ht.1
      have hp := (smoothedDensity_pos μ ht0 x).le
      have hlog : |1+Real.log (smoothedDensity μ t x)| ≤ L*(1+‖x‖^2) := by
        have h := smoothedLog_polynomial_bound μ ha ht hD0 (hD t ht) hK hμ x
        have h' := abs_add_le (1:ℝ) (Real.log (smoothedDensity μ t x))
        norm_num only [abs_one] at h'
        dsimp [L]; nlinarith [sq_nonneg ‖x‖]
      have htime := smoothedTime_polynomial_bound μ ha ht.1 hK hμ x
      have hden := (smoothedDensity_bounds μ ha ht (hD t ht) hK hμ x).2
      have he : -‖x‖^2/(4*b)=-(1/(4*b))*‖x‖^2 := by ring
      rw [he] at hden
      rw [Real.norm_eq_abs,abs_mul]
      calc
        _ ≤ (L*(1+‖x‖^2))*(T*(1+‖x‖^2)*smoothedDensity μ t x) := mul_le_mul hlog htime (abs_nonneg _) (by positivity)
        _ = (L*T)*(1+‖x‖^2)^2*smoothedDensity μ t x := by ring
        _ ≤ (L*T)*(1+‖x‖^2)^2*(A*Real.exp (-(1/(4*b))*‖x‖^2)) := mul_le_mul_of_nonneg_left hden (by positivity)
        _ = _ := by ring)
  · convert (polynomial_gaussian_integrable (E := EuclideanSpace ℝ ι) (c := 1/(4*b)) (by positivity) 2).const_mul (L*T*A) using 1
    funext x; ring
  · exact ae_of_all _ (fun x t ht => smoothedEntropy_hasDeriv_time μ hK hμ (ha.trans_le ht.1) x)
 theorem smoothed_score_ibp [DecidableEq ι] (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {K s : ℝ} (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) (hs : 0<s) (i : ι) :
    (∫x,(1+Real.log (smoothedDensity μ s x))*smoothedSecond μ s x i) =
      -(∫x,(smoothedGradient μ s x i)^2/smoothedDensity μ s x) := by
  have hm : ∀ᵐ y ∂μ,y∈Metric.closedBall 0 K := by simpa only [Metric.mem_closedBall,dist_zero_right] using hμ
  have hiSecond := smoothedLog_mul_integrable μ hs hK hμ (smoothedSecond_measurable μ s i)
    (2*(1+K^2)/s^2+1/s) (by positivity) (fun x => smoothedSecond_polynomial_bound μ hs le_rfl hK hμ x i)
  have hiGradient := smoothedLog_mul_integrable μ hs hK hμ (smoothedGradient_measurable μ s i)
    ((1+K)/s) (by positivity) (fun x => smoothedGradient_polynomial_bound μ hs le_rfl hK hμ x i)
  have he : (fun x => (smoothedGradient μ s x i/smoothedDensity μ s x)*smoothedGradient μ s x i) =
      fun x => (smoothedGradient μ s x i)^2/smoothedDensity μ s x := by funext x; ring
  have hiScore : Integrable (fun x => (smoothedGradient μ s x i/smoothedDensity μ s x)*smoothedGradient μ s x i) := by
    rw [he]; exact smoothedScore_integrable μ hs hK hμ i
  have hibp := integral_coordinate_ibp i (fun x => 1+Real.log (smoothedDensity μ s x))
    (fun x => smoothedGradient μ s x i/smoothedDensity μ s x)
    (fun x => smoothedGradient μ s x i) (fun x => smoothedSecond μ s x i) ?_ ?_ hiSecond hiScore hiGradient
  · simpa only [he] using hibp
  · intro x r
    convert ((smoothedDensity_hasDeriv_coordinate μ (isCompact_closedBall _ _) hm s x i r).log (smoothedDensity_pos μ hs _).ne').const_add 1 using 1
  · intro x r
    exact smoothedGradient_hasDeriv_coordinate μ (isCompact_closedBall _ _) hm s x i r
 theorem classicalEntropy_hasDeriv (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {K s : ℝ} (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂μ,‖y‖ ≤ K) (hs : 0<s) :
    HasDerivAt (classicalEntropy μ) ((1/2:ℝ)*classicalFisher μ s) s := by
  classical
  have hm : ∀ᵐ y ∂μ,y∈Metric.closedBall 0 K := by simpa only [Metric.mem_closedBall,dist_zero_right] using hμ
  convert classicalEntropy_hasDeriv_integral μ hK hμ hs using 1 ; try rfl
  simp_rw [smoothed_heatEquation μ (isCompact_closedBall _ _) hm]
  simp_rw [mul_left_comm _ (1/2:ℝ)]
  rw [integral_const_mul]
  simp_rw [mul_sum]
  rw [integral_finsetSum]
  · simp_rw [smoothed_score_ibp μ hK hμ hs]
    simp only [sum_neg_distrib,classicalFisher]
    ring
  · intro i hi
    exact smoothedLog_mul_integrable μ hs hK hμ (smoothedSecond_measurable μ s i)
      (2*(1+K^2)/s^2+1/s) (by positivity) (fun x => smoothedSecond_polynomial_bound μ hs le_rfl hK hμ x i)
 theorem classicalFisher_nonneg (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0<s) : 0 ≤ classicalFisher μ s := by
  apply sum_nonneg
  intro i hi
  apply integral_nonneg
  intro x
  exact div_nonneg (sq_nonneg _) (smoothedDensity_pos μ hs x).le
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixFisherLiminf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Finset
open scoped Topology
namespace FiniteEntropySeparation
variable {n d : ℕ}
namespace FreeTensor
variable {B N G : Type} [Group G] [DecidableEq B] [DecidableEq N] [DecidableEq G]
variable {D : ℕ → ℕ} (hD0 : ∀k,0<D k) (hD : Tendsto D atTop atTop)
  (J : Set N) (X : Fin n → Space B N G →L[ℂ] Space B N G) (hX : ∀i,X i ∈ backgroundAlgebra J)
  (hself : ∀i,IsSelfAdjoint (X i))
  {R : ℝ} (hR : 0≤R) (hn : ∀k,(diagonalMicrostates (tracialVector B N G) X R k (D k)).Nonempty)
  (σ : Fin n → N) (hσ : Function.Injective σ) (hsigma : ∀i,σ i ∉ J)
  (μ : (k:ℕ) → Measure (MatrixCoordinates n (D k))) [∀k,IsProbabilityMeasure (μ k)]
  (hμ : ∀k,∀ᵐa ∂μ k,a ∈ diagonalMicrostates (tracialVector B N G) X R k (D k))
include hR hμ in

omit [∀ (k : ℕ), IsProbabilityMeasure (μ k)] in
theorem diagonalMicrostates_norm_ae [∀ (k : ℕ), IsProbabilityMeasure (μ k)] (k : ℕ) :
    ∀ᵐa ∂μ k,‖a‖≤Real.sqrt ((n:ℝ)*D k)*R := by
  filter_upwards [hμ k] with a ha
  have hb := microstates_subset_closedBall (tracialVector B N G) X R hR k (D k) ((k+1:ℝ)⁻¹) ha
  simpa only [Metric.mem_closedBall,dist_zero_right] using hb
end FreeTensor
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.GaussianFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
 theorem smoothedDensity_cond_le (S : Set (EuclideanSpace ℝ ι)) {s : ℝ} (hs : 0<s)
    (x : EuclideanSpace ℝ ι) : smoothedDensity (ProbabilityTheory.cond volume S) s x ≤ (volume S).toReal⁻¹ := by
  rw [smoothedDensity,ProbabilityTheory.cond,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul]
  have hi : Integrable (fun y : EuclideanSpace ℝ ι => normalKernel s (x-y)) volume := (normalKernel_integrable (ι := ι) hs).comp_sub_left x
  have hle := integral_mono_measure (Measure.restrict_le_self (μ := (volume : Measure (EuclideanSpace ℝ ι))) (s := S))
    (ae_of_all _ (fun y => (normalKernel_pos s (x-y)).le)) hi
  rw [integral_sub_left_eq_self (μ := (volume : Measure (EuclideanSpace ℝ ι))),normalKernel_integral hs] at hle
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr ENNReal.toReal_nonneg)
 theorem classicalEntropy_cond_lower (S : Set (EuclideanSpace ℝ ι))
    (hS0 : volume S ≠ 0) (hSt : volume S ≠ ⊤) {K s : ℝ}
    (hK : 0 ≤ K) (hμ : ∀ᵐ y ∂ProbabilityTheory.cond volume S,‖y‖ ≤ K) (hs : 0<s) :
    Real.log (volume S).toReal ≤ classicalEntropy (ProbabilityTheory.cond volume S) s := by
  let ν := ProbabilityTheory.cond (volume : Measure (EuclideanSpace ℝ ι)) S
  have : IsProbabilityMeasure ν := cond_isProbabilityMeasure_of_finite hS0 hSt
  have hl x : Real.log (smoothedDensity ν s x) ≤ -Real.log (volume S).toReal := by
    have hb : smoothedDensity ν s x ≤ (volume S).toReal⁻¹ := smoothedDensity_cond_le S hs x
    have hp := smoothedDensity_pos ν hs x
    simpa only [Real.log_inv] using Real.log_le_log hp hb
  have hint := smoothedEntropy_integrable ν hs hK hμ
  have hbound := (smoothedDensity_integrable ν hs).mul_const (-Real.log (volume S).toReal)
  have hh := integral_mono_ae hint hbound (ae_of_all _ (fun x =>
    mul_le_mul_of_nonneg_left (hl x) (smoothedDensity_pos ν hs x).le))
  rw [integral_mul_const,smoothedDensity_integral ν hs,one_mul] at hh
  change Real.log (volume S).toReal ≤ -(∫x,smoothedDensity ν s x*Real.log (smoothedDensity ν s x))
  linarith
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.MatrixFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace FiniteEntropySeparation
variable {n d : ℕ}
 theorem normalizedMatrixEntropy_hasDeriv (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsProbabilityMeasure μ]
    {K s : ℝ} (hK : 0≤K) (hμ : ∀ᵐy ∂μ,‖y‖≤K) (hs : 0<s) :
    HasDerivAt (normalizedMatrixEntropy μ) ((1/2:ℝ)*normalizedMatrixFisher μ s) s := by
  have hdR : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
  have hsD : 0 < s/(d:ℝ) := div_pos hs (by exact_mod_cast hd)
  have hf := (((classicalEntropy_hasDeriv μ hK hμ hsD).comp s
    ((hasDerivAt_id s).div_const (d:ℝ))).div_const ((d:ℝ)^2)).add_const ((n:ℝ)/2*Real.log d)
  have he : (1/2:ℝ)*classicalFisher μ (s/d)*(1/(d:ℝ))/(d:ℝ)^2 =
      (1/2:ℝ)*normalizedMatrixFisher μ s := by
    unfold normalizedMatrixFisher
    field_simp
  rw [he] at hf
  exact hf
 theorem normalizedMatrixFisher_nonneg (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0<s) : 0≤normalizedMatrixFisher μ s :=
  div_nonneg (classicalFisher_nonneg μ (div_pos hs (by exact_mod_cast hd))) (by positivity)
 theorem normalizedMatrixEntropy_continuousOn (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsProbabilityMeasure μ]
    {K : ℝ} (hK : 0≤K) (hμ : ∀ᵐy ∂μ,‖y‖≤K) :
    ContinuousOn (normalizedMatrixEntropy μ) (Ioi 0) :=
  fun _ hs => (normalizedMatrixEntropy_hasDeriv hd μ hK hμ hs).continuousAt.continuousWithinAt
 theorem normalizedMatrixFisher_intervalIntegrable (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsProbabilityMeasure μ]
    {K a b : ℝ} (hK : 0≤K) (hμ : ∀ᵐy ∂μ,‖y‖≤K) (ha : 0<a) (hb : 0<b) :
    IntervalIntegrable (normalizedMatrixFisher μ) volume a b := by
  have hmin : 0 < min a b := lt_min ha hb
  have hi : IntervalIntegrable (fun s => (1/2:ℝ)*normalizedMatrixFisher μ s) volume a b :=
    intervalIntegral.intervalIntegrable_deriv_of_nonneg
      ((normalizedMatrixEntropy_continuousOn hd μ hK hμ).mono (fun s hs => hmin.trans_le hs.1))
      (fun s hs => normalizedMatrixEntropy_hasDeriv hd μ hK hμ (hmin.trans hs.1))
      (fun s hs => mul_nonneg (by norm_num) (normalizedMatrixFisher_nonneg hd μ (hmin.trans hs.1)))
  simpa only [← mul_assoc,show (2:ℝ)*(1/2:ℝ)=1 by norm_num,one_mul] using hi.const_mul (2:ℝ)
 theorem normalizedMatrixEntropy_flow (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsProbabilityMeasure μ]
    {K a b : ℝ} (hK : 0≤K) (hμ : ∀ᵐy ∂μ,‖y‖≤K) (ha : 0<a) (hb : 0<b) :
    normalizedMatrixEntropy μ b-normalizedMatrixEntropy μ a = (1/2:ℝ)*∫s in a..b,normalizedMatrixFisher μ s := by
  have hmin : 0 < min a b := lt_min ha hb
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (hs : s∈uIcc a b) => normalizedMatrixEntropy_hasDeriv hd μ hK hμ (hmin.trans_le hs.1))
    ((normalizedMatrixFisher_intervalIntegrable hd μ hK hμ ha hb).const_mul (1/2:ℝ))
  simpa only [intervalIntegral.integral_const_mul] using hf.symm
 theorem normalizedMatrixEntropy_cond_lower (hd : 0<d) (S : Set (MatrixCoordinates n d))
    (hS0 : volume S≠0) (hSt : volume S≠⊤) {K s : ℝ} (hK : 0≤K)
    (hμ : ∀ᵐy ∂ProbabilityTheory.cond volume S,‖y‖≤K) (hs : 0<s) :
    (d:ℝ)^(-2:ℤ)*Real.log (volume S).toReal+(n:ℝ)/2*Real.log d ≤ normalizedMatrixEntropy (ProbabilityTheory.cond volume S) s := by
  have hi := classicalEntropy_cond_lower S hS0 hSt hK hμ (show 0 < s/(d:ℝ) from div_pos hs (by exact_mod_cast hd))
  simpa [normalizedMatrixEntropy,zpow_neg,div_eq_mul_inv,mul_comm] using
    add_le_add_right (div_le_div_of_nonneg_right hi (sq_nonneg (d:ℝ))) ((n:ℝ)/2*Real.log d)
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.HeatAnalysis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal NNReal Topology
open MeasureTheory Filter Set Finset
namespace FiniteEntropySeparation
namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]
 theorem heatFisher_ne_top (u : ℝ) (hu : 0 < u) : freeFisher (τ p) (X p u) ≠ ⊤ := by
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (heat_freeFisher_le ∅ (C p) (C_mem_background p ∅) (initialIndex p)
      (initialIndex_injective p) (by simp) u hu)
end Model
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.FatouFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace FiniteEntropySeparation
 theorem integral_le_of_liminf_tests {Ω : Type u1} [MeasurableSpace Ω] (ν : Measure Ω)
    (F : Ω → ℝ) (g : ℕ → Ω → ℝ) (hF : Integrable F ν) (hF0 : 0≤ᵐ[ν] F)
    (hg : ∀k,Integrable (g k) ν) (hg0 : ∀k,0≤ᵐ[ν] g k)
    (hl : ∀ᵐs ∂ν,ENNReal.ofReal (F s) ≤ liminf (fun k => ENNReal.ofReal (g k s)) atTop)
    {C : ℝ} (hC : ∀ᶠk in atTop,(∫s,g k s ∂ν) ≤ C) : (∫s,F s ∂ν) ≤ C := by
  have hc : 0≤C := by
    obtain ⟨k,hk⟩ := hC.exists
    exact (integral_nonneg_of_ae (hg0 k)).trans hk
  apply (ENNReal.ofReal_le_ofReal_iff hc).mp
  rw [ofReal_integral_eq_lintegral_ofReal hF hF0]
  apply (lintegral_mono_ae hl).trans
  apply (lintegral_liminf_le' (fun k => ENNReal.measurable_ofReal.comp_aemeasurable (hg k).aestronglyMeasurable.aemeasurable)).trans
  apply liminf_le_of_frequently_le'
  apply Eventually.frequently
  filter_upwards [hC] with k hk
  simp only [Function.comp_apply]
  rw [← ofReal_integral_eq_lintegral_ofReal (hg k) (hg0 k)]
  exact ENNReal.ofReal_le_ofReal hk
variable {n : ℕ} {D : ℕ → ℕ} (hD : ∀k,0<D k)
  (μ : (k:ℕ) → Measure (MatrixCoordinates n (D k))) [∀k,IsProbabilityMeasure (μ k)]
  (K : ℕ → ℝ) (hK : ∀k,0≤K k) (hμ : ∀k,∀ᵐa ∂μ k,‖a‖≤K k)
include hD hK hμ
 theorem matrixFlow_limit_bound (F : ℝ → ℝ) {a t β L : ℝ}
    (ha : 0<a) (hat : a≤t) (hF : IntervalIntegrable F volume a t)
    (hF0 : ∀s∈Ioc a t,0≤F s)
    (hl : ∀s∈Ioc a t,ENNReal.ofReal (F s) ≤ liminf (fun k => ENNReal.ofReal (normalizedMatrixFisher (μ k) s)) atTop)
    (hinit : ∀k,β≤normalizedMatrixEntropy (μ k) a)
    (hterm : ∀ε : ℝ,0<ε → ∀ᶠk in atTop,normalizedMatrixEntropy (μ k) t ≤ L+ε) :
    β+(1/2:ℝ)*(∫s in a..t,F s) ≤ L := by
  have ht : 0<t := ha.trans_le hat
  apply le_of_forall_pos_le_add
  intro ε hε
  have hg k := normalizedMatrixFisher_intervalIntegrable (hD k) (μ k) (hK k) (hμ k) ha ht
  have hbound : ∀ᶠk in atTop,(∫s in Ioc a t,normalizedMatrixFisher (μ k) s) ≤ 2*(L+ε-β) := by
    filter_upwards [hterm ε hε] with k hk
    have he := normalizedMatrixEntropy_flow (hD k) (μ k) (hK k) (hμ k) ha ht
    rw [intervalIntegral.integral_of_le hat] at he
    linarith [hinit k]
  have hf := integral_le_of_liminf_tests (volume.restrict (Ioc a t)) F
    (fun k => normalizedMatrixFisher (μ k)) hF.1
    ((ae_restrict_mem measurableSet_Ioc).mono (fun _ hs => hF0 _ hs))
    (fun k => (hg k).1)
    (fun k => (ae_restrict_mem measurableSet_Ioc).mono (fun s hs => normalizedMatrixFisher_nonneg (hD k) (μ k) (ha.trans hs.1)))
    ((ae_restrict_mem measurableSet_Ioc).mono (fun _ hs => hl _ hs)) hbound
  rw [intervalIntegral.integral_of_le hat]
  linarith
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.ModelFlowLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace FiniteEntropySeparation.Model
variable (p : ℕ) [NeZero p]
 theorem matrixFlow_limit (hp : 2≤p) {D : ℕ → ℕ} (hD0 : ∀k,0<D k) (hD : Tendsto D atTop atTop)
    {h R : ℝ} (hh : 0<h) (hR : 0≤R)
    (hn : ∀k,(diagonalMicrostates (τ p) (X p h) R k (D k)).Nonempty)
    (μ : (k:ℕ) → Measure (MatrixCoordinates (p+1) (D k))) [∀k,IsProbabilityMeasure (μ k)]
    (hμ : ∀k,∀ᵐa ∂μ k,a∈diagonalMicrostates (τ p) (X p h) R k (D k))
    {a t β L : ℝ} (ha : 0<a) (hat : a≤t)
    (hinit : ∀k,β≤normalizedMatrixEntropy (μ k) a)
    (hterm : ∀ᶠk in atTop,normalizedMatrixEntropy (μ k) t≤L) :
    β+(1/2:ℝ)*(∫u in (h+a)..(h+t),heatFisherReal p u)≤L := by
  have hnorm k : ∀ᵐy ∂μ k,‖y‖≤Real.sqrt (((p+1:ℕ):ℝ)*D k)*R :=
    FreeTensor.diagonalMicrostates_norm_ae (X p h) hR μ hμ k
  have hl s (hs : s∈Ioc a t) : ENNReal.ofReal (heatFisherReal p (h+s))≤
      liminf (fun k => ENNReal.ofReal (normalizedMatrixFisher (μ k) s)) atTop := by
    have hs0 : 0<s := ha.trans hs.1
    have hb := FreeTensor.freeFisher_le_liminf_matrixFisher hD0 hD (oldNoise p) (X p h)
      (X_mem_background p h) (X_selfAdjoint p h) hR hn (auxiliaryIndex p)
      (auxiliaryIndex_injective p) (auxiliaryIndex_fresh p) μ hμ hs0
    change freeFisher (τ p) (doublyNoised p h s)≤_ at hb
    rw [doublyNoised_fisher_eq p h s hh.le hs0.le (by linarith)] at hb
    simpa only [heatFisherReal,ENNReal.ofReal_toReal (heatFisher_ne_top p (h+s) (by linarith))] using hb
  have hb := matrixFlow_limit_bound hD0 μ (fun k => Real.sqrt (((p+1:ℕ):ℝ)*D k)*R)
    (fun k => by positivity) hnorm (fun s => heatFisherReal p (h+s)) ha hat
    (heatFisher_shift_intervalIntegrable p hp hh ha.le hat) (fun _ _ => ENNReal.toReal_nonneg) hl hinit
    (fun ε hε => hterm.mono (fun k hk => by linarith))
  rwa [intervalIntegral.integral_comp_add_left] at hb
end FiniteEntropySeparation.Model

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.FlowSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace FiniteEntropySeparation
 theorem chosenStart_pos {h : ℝ} (hh : 0<h) : 0<chosenStart h := by unfold chosenStart; positivity
 theorem chosenStart_le_time {h : ℝ} (hh : h<1) : chosenStart h≤chosenTime := by
  unfold chosenStart
  apply (div_le_iff₀ (by positivity : (0:ℝ)<4*((chosenP+1:ℕ):ℝ))).mpr
  norm_num [chosenP,chosenTime] at *
  linarith
end FiniteEntropySeparation

end

end OAI
end

section
-- module Solutions.OAIQW_FiniteEntropySeparation.CutoffSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace FiniteEntropySeparation
 theorem chosen_cutoff_real_bound {h R δ Δ β : ℝ} (hh0 : 0<h) (hh1 : h<1) (hR : 0≤R)
    (hδ : 0<δ) (hΔ : 0<Δ) (hδΔ : δ≤Δ/4)
    (hsep : ∀i j : Fin chosenP,i≠j → Δ≤|equidiscreteAtom chosenP i-equidiscreteAtom chosenP j|)
    (hq : ∀l : Fin chosenP,∀r : ℝ,|r-equidiscreteAtom chosenP l|≤δ → (3:ℝ)/4≤((spectralBasis chosenP l).eval r)^2)
    (hh : spectralGood chosenP δ Δ (wordMoment (Model.τ chosenP) (Model.X chosenP h)))
    (hβ : (β:EReal)<chiCutoff (Model.τ chosenP) (Model.X chosenP h) R) :
    (β:EReal)≤chiStar (Model.τ chosenP) (Model.X chosenP h) (Model.auxiliaryNoise chosenP)-(1/2:EReal) := by
  obtain ⟨D,hDm,hD0,hvol⟩ := exists_microstate_dimensions (Model.τ chosenP) (Model.X chosenP h) hβ
  let S := fun k => diagonalMicrostates (Model.τ chosenP) (Model.X chosenP h) R k (D k)
  have hs k : MeasurableSet (S k) := diagonalMicrostates_measurable _ _ _ _ _
  have hv0 k : volume (S k)≠0 := matrixVolumeEntropy_ne_bot_volume (hD0 k) _
    (ne_bot_of_gt ((EReal.bot_lt_coe β).trans (hvol k)))
  have hvt k : volume (S k)≠⊤ := ne_of_lt (microstates_volume_lt_top (Model.τ chosenP) (Model.X chosenP h) R hR k (D k) _)
  let μ := fun k => cond volume (S k)
  have hprob : ∀k,IsProbabilityMeasure (μ k) := fun k => cond_isProbabilityMeasure_of_finite (hv0 k) (hvt k)
  let : ∀k,IsProbabilityMeasure (μ k) := hprob
  have hμ k : ∀ᵐa ∂μ k,a∈S k := ae_cond_mem (hs k)
  have hn k : (S k).Nonempty := by
    apply Set.nonempty_iff_ne_empty.mpr
    intro he
    apply hv0 k
    rw [he,measure_empty]
  have hinit (k : ℕ) : β≤normalizedMatrixEntropy (μ k) (chosenStart h) := by
    have hnorm : ∀ᵐa ∂μ k,‖a‖≤Real.sqrt (((chosenP+1:ℕ):ℝ)*D k)*R :=
      FreeTensor.diagonalMicrostates_norm_ae (Model.X chosenP h) hR μ hμ k
    have hb := normalizedMatrixEntropy_cond_lower (hD0 k) (S k) (hv0 k) (hvt k)
      (show 0≤Real.sqrt (((chosenP+1:ℕ):ℝ)*D k)*R by positivity) hnorm (chosenStart_pos hh0)
    have he : β<((D k:ℝ)^2)⁻¹*Real.log (volume (S k)).toReal+((chosenP+1:ℕ):ℝ)/2*Real.log (D k) := by
      apply EReal.coe_lt_coe_iff.mp
      have hbvol : (β:EReal)< matrixVolumeEntropy (S k) := hvol k
      rwa [matrixVolumeEntropy_coe (S k) (hv0 k) (hvt k)] at hbvol
    exact he.le.trans (by simpa only [zpow_neg,zpow_ofNat] using hb)
  have hterm := chosen_terminal_gaussian hD0 hDm.tendsto_atTop hh0 hh1 hR hδ hΔ hδΔ hsep hq hh hn μ hμ
  have hflow := Model.matrixFlow_limit chosenP chosenP_ge_two hD0 hDm.tendsto_atTop hh0 hR hn μ hμ
    (chosenStart_pos hh0) (chosenStart_le_time hh1) hinit hterm
  exact flow_to_chiStar_gap hh0 hh1 hflow
 theorem chosen_cutoff_bound {h R δ Δ : ℝ} (hh0 : 0<h) (hh1 : h<1) (hR : 0≤R)
    (hδ : 0<δ) (hΔ : 0<Δ) (hδΔ : δ≤Δ/4)
    (hsep : ∀i j : Fin chosenP,i≠j → Δ≤|equidiscreteAtom chosenP i-equidiscreteAtom chosenP j|)
    (hq : ∀l : Fin chosenP,∀r : ℝ,|r-equidiscreteAtom chosenP l|≤δ → (3:ℝ)/4≤((spectralBasis chosenP l).eval r)^2)
    (hh : spectralGood chosenP δ Δ (wordMoment (Model.τ chosenP) (Model.X chosenP h))) :
    chiCutoff (Model.τ chosenP) (Model.X chosenP h) R≤
      chiStar (Model.τ chosenP) (Model.X chosenP h) (Model.auxiliaryNoise chosenP)-(1/2:EReal) := by
  by_contra he
  obtain ⟨β,hb,hb'⟩ := EReal.exists_between_coe_real (lt_of_not_ge he)
  exact (not_lt_of_ge (chosen_cutoff_real_bound hh0 hh1 hR hδ hΔ hδΔ hsep hq hh hb')) hb
 theorem chosen_chi_bound_oai {h δ Δ : ℝ} (hh0 : 0<h) (hh1 : h<1)
    (hδ : 0<δ) (hΔ : 0<Δ) (hδΔ : δ≤Δ/4)
    (hsep : ∀i j : Fin chosenP,i≠j → Δ≤|equidiscreteAtom chosenP i-equidiscreteAtom chosenP j|)
    (hq : ∀l : Fin chosenP,∀r : ℝ,|r-equidiscreteAtom chosenP l|≤δ → (3:ℝ)/4≤((spectralBasis chosenP l).eval r)^2)
    (hh : spectralGood chosenP δ Δ (wordMoment (Model.τ chosenP) (Model.X chosenP h))) :
    chi (Model.τ chosenP) (Model.X chosenP h)≤
      chiStar (Model.τ chosenP) (Model.X chosenP h) (Model.auxiliaryNoise chosenP)-(1/2:EReal) := by
  apply iSup_le
  intro R
  exact chosen_cutoff_bound hh0 hh1 R.property.le hδ hΔ hδΔ hsep hq hh
end FiniteEntropySeparation

end

end OAI
end

theorem solution : type_of% @OAI.FiniteEntropySeparation.chosen_chi_bound_oai := @OAI.FiniteEntropySeparation.chosen_chi_bound_oai
