-- Prove2me | solution 1 for OAI.DirectionalTransience.normalJointPast_product_identification
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:45:58.482274+00:00
-- url     : https://prove2.me/submissions/f954c938-e6e6-4cf9-a5c3-963c791a6c52

import Mathlib
import Definitions.Def_OAIQ242Bal000
import Definitions.Def_OAIQ242Bal001

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_IidListProcess
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma symmetricClip_apply (w : ℝ≥0) (z : ℝ) : symmetricClip w z = max (-(w:ℝ)) (min (w:ℝ) z) := rfl

lemma symmetricClip_bound (w : ℝ≥0) (z : ℝ) : |symmetricClip w z| ≤ w := by
  rw [symmetricClip_apply,abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith [w.coe_nonneg]) (min_le_left _ _)⟩

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma symmetricClip_eq_self (w : ℝ≥0) {z : ℝ} (hz : |z|≤w) : symmetricClip w z=z := by
  obtain ⟨hl,hr⟩ := abs_le.mp hz
  simp only [symmetricClip_apply,min_eq_right hr,max_eq_right hl]

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ConditionalLawTests
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma symmetricClip_abs_le_abs (w : ℝ≥0) (z : ℝ) : |symmetricClip w z| ≤ |z| := by
  by_cases hz : |z| ≤ w
  · rw [symmetricClip_eq_self w hz]
  · exact (symmetricClip_bound w z).trans (le_of_not_ge hz)

lemma unit_clip_product_error (x y : ℝ) :
    |x*y-symmetricClip 1 x*symmetricClip 1 y| ≤ 2*(|x|^3+|y|^3) := by
  by_cases hx : |x| ≤ 1
  · by_cases hy : |y| ≤ 1
    · rw [symmetricClip_eq_self 1 (by simpa using hx),symmetricClip_eq_self 1 (by simpa using hy),sub_self,abs_zero]
      positivity
    · have hh : |x| * |y| ≤ |y|^3 := by nlinarith [abs_nonneg x,abs_nonneg y,sq_nonneg (|y|-1)]
      have hb := abs_sub (x*y) (symmetricClip 1 x*symmetricClip 1 y)
      rw [abs_mul,abs_mul] at hb
      have hc := mul_le_mul (symmetricClip_abs_le_abs 1 x) (symmetricClip_abs_le_abs 1 y)
        (abs_nonneg _) (abs_nonneg _)
      nlinarith [pow_nonneg (abs_nonneg x) 3]
  · by_cases hy : |y| ≤ |x|
    · have hx1 : 1 ≤ |x| := le_of_not_ge hx
      have hh : |x| * |y| ≤ |x|^3 := by
        have h1 := mul_le_mul_of_nonneg_left hy (abs_nonneg x)
        have h2 := mul_le_mul_of_nonneg_right hx1 (sq_nonneg |x|)
        nlinarith
      have hb := abs_sub (x*y) (symmetricClip 1 x*symmetricClip 1 y)
      rw [abs_mul,abs_mul] at hb
      have hc := mul_le_mul (symmetricClip_abs_le_abs 1 x) (symmetricClip_abs_le_abs 1 y)
        (abs_nonneg _) (abs_nonneg _)
      nlinarith [pow_nonneg (abs_nonneg y) 3]
    · have hy1 : 1 ≤ |y| := (le_of_not_ge hx).trans (le_of_not_ge hy)
      have hh : |x| * |y| ≤ |y|^3 := by
        have h1 := mul_le_mul_of_nonneg_right (le_of_not_ge hy) (abs_nonneg y)
        have h2 := mul_le_mul_of_nonneg_right hy1 (sq_nonneg |y|)
        nlinarith
      have hb := abs_sub (x*y) (symmetricClip 1 x*symmetricClip 1 y)
      rw [abs_mul,abs_mul] at hb
      have hc := mul_le_mul (symmetricClip_abs_le_abs 1 x) (symmetricClip_abs_le_abs 1 y)
        (abs_nonneg _) (abs_nonneg _)
      nlinarith [pow_nonneg (abs_nonneg x) 3]

lemma gaussian_absolute_moment_integrable (v : ℝ≥0) (k : ℕ) :
    Integrable (fun z : ℝ => |z|^k) (gaussianReal 0 v) := by
  exact integrable_pow_abs_of_mem_interior_integrableExpSet (X := id) (by simp) k

lemma normalThirdMoment_nonneg : 0 ≤ normalThirdMoment := integral_nonneg (fun z => by positivity)

lemma gaussian_absolute_third_moment (v : ℝ≥0) :
    (∫ z : ℝ, |z|^3 ∂gaussianReal 0 v)= (Real.sqrt v)^3*normalThirdMoment := by
  have hm : (gaussianReal 0 1).map (fun z => Real.sqrt v*z)=gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul,mul_zero,mul_one]
    congr 1
    exact NNReal.eq (Real.sq_sqrt v.coe_nonneg)
  rw [← hm,integral_map (by fun_prop : Measurable (fun z => Real.sqrt v*z)).aemeasurable
    (by fun_prop : Measurable (fun z : ℝ => |z|^3)).aestronglyMeasurable]
  simp_rw [abs_mul,mul_pow,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact integral_const_mul _ _

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_JointPastMoments
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma product_law_integral_mul {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : Type*} [RCLike K] (μ : Measure Ω) [IsFiniteMeasure μ] (γ : Measure ℝ) [SFinite γ]
    (Z : Ω → E) (X : Ω → ℝ) (hZ : Measurable Z) (hX : Measurable X)
    (hlaw : μ.map (fun ω => (Z ω,X ω))=(μ.map Z).prod γ)
    (F : E → K) (G : ℝ → K) (hF : Measurable F) (hG : Measurable G) :
    (∫ ω, F (Z ω)*G (X ω) ∂μ)=(∫ ω, F (Z ω) ∂μ)*(∫ z, G z ∂γ) := by
  have hi := integral_map (μ := μ) (hZ.prodMk hX).aemeasurable
    ((hF.comp measurable_fst).mul (hG.comp measurable_snd)).aestronglyMeasurable
  change (∫ z : E × ℝ, F z.1*G z.2 ∂μ.map (fun ω => (Z ω,X ω)))=
    (∫ ω, F (Z ω)*G (X ω) ∂μ) at hi
  rw [← hi,hlaw,integral_prod_mul,integral_map hZ.aemeasurable hF.aestronglyMeasurable]

lemma normalJointPast_moment {q k : ℕ} (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) (v : Fin q → unitInterval) (s t : unitInterval)
    (hv : ∀ z, v z ≤ s) (hst : s < t) (ht : (t:ℝ) < 1) (b : Bool)
    (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) :
    (∫ P, F (pairPastCoordinates v P)*(pairPathIncrement b s t P)^k ∂μ)=
      (∫ P, F (pairPastCoordinates v P) ∂μ)*(∫ z : ℝ, z^k ∂gaussianReal 0 (c*Real.toNNReal ((t:ℝ)-s))) := by
  exact product_law_integral_mul μ _ _ _ (pairPastCoordinates v).continuous.measurable
    (pairPathIncrement b s t).continuous.measurable (h q v s t hv hst ht b) F (fun z => z^k)
    F.continuous.measurable (by fun_prop)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma gaussianReal_second_moment (v : ℝ≥0) :
    (∫ z : ℝ, z^2 ∂gaussianReal 0 v) = v := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h

lemma normalJointPast_hasLaw {q : ℕ} (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) (v : Fin q → unitInterval) (s t : unitInterval)
    (hv : ∀ z, v z ≤ s) (hst : s < t) (ht : (t:ℝ) < 1) (b : Bool) :
    HasLaw (pairPathIncrement b s t) (gaussianReal 0 (c*Real.toNNReal ((t:ℝ)-s))) μ := by
  have hp := h q v s t hv hst ht b
  have he := congrArg (fun ξ : Measure ((Fin q → ℝ × ℝ) × ℝ) => ξ.map Prod.snd) hp
  rw [Measure.map_map measurable_snd ((pairPastCoordinates v).continuous.measurable.prodMk
    (pairPathIncrement b s t).continuous.measurable)] at he
  refine ⟨(pairPathIncrement b s t).continuous.measurable.aemeasurable,?_⟩
  simpa [Measure.map_apply (pairPastCoordinates v).continuous.measurable,Function.comp_def] using he

lemma normalJointPast_integrable_abs_pow (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) (s t : unitInterval)
    (hst : s < t) (ht : (t:ℝ) < 1) (b : Bool) (k : ℕ) :
    Integrable (fun P => |pairPathIncrement b s t P|^k) μ := by
  have hl := normalJointPast_hasLaw μ c h (fun _ : Fin 0 => s) s t (by simp) hst ht b
  have hi := gaussian_absolute_moment_integrable (c*Real.toNNReal ((t:ℝ)-s)) k
  rw [← hl.map_eq] at hi
  exact (integrable_map_measure (by fun_prop : Measurable (fun z : ℝ => |z|^k)).aestronglyMeasurable
    hl.aemeasurable).mp hi

lemma normalJointPast_absolute_third_moment (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) (s t : unitInterval)
    (hst : s < t) (ht : (t:ℝ) < 1) (b : Bool) :
    (∫ P, |pairPathIncrement b s t P|^3 ∂μ)=
      (Real.sqrt ((c:ℝ)*((t:ℝ)-s)))^3*normalThirdMoment := by
  have hl := normalJointPast_hasLaw μ c h (fun _ : Fin 0 => s) s t (by simp) hst ht b
  have hi := hl.integral_comp (by fun_prop : Measurable (fun z : ℝ => |z|^3)).aestronglyMeasurable
  change (∫ P, |pairPathIncrement b s t P|^3 ∂μ) = _ at hi
  rw [hi,gaussian_absolute_third_moment]
  rw [NNReal.coe_mul,Real.toNNReal_of_nonneg (sub_nonneg.mpr (show (s:ℝ) ≤ t from hst.le))]
  rfl

lemma normalJointPast_second {q : ℕ} (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) (v : Fin q → unitInterval) (s t : unitInterval)
    (hv : ∀ z, v z ≤ s) (hst : s < t) (ht : (t:ℝ) < 1) (b : Bool)
    (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) :
    (∫ P, F (pairPastCoordinates v P)*(pairPathIncrement b s t P)^2 ∂μ)=
      (∫ P, F (pairPastCoordinates v P) ∂μ)*((c:ℝ)*((t:ℝ)-s)) := by
  rw [normalJointPast_moment μ c h v s t hv hst ht b F,gaussianReal_second_moment,
    NNReal.coe_mul,Real.toNNReal_of_nonneg (sub_nonneg.mpr (show (s:ℝ) ≤ t from hst.le))]
  rfl

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_PastCutoffs
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma nearDiagonalCutoff_one {ρ : ℝ} (hρ : 0 < ρ) {z : ℝ} (hz : |z| ≤ ρ) :
    nearDiagonalCutoff ρ z=1 := by
  change max 0 (min 1 (2-|z|/ρ))=1
  have h := (div_le_one hρ).mpr hz
  rw [min_eq_left (by linarith),max_eq_right (by norm_num)]

lemma nearDiagonalCutoff_zero {ρ : ℝ} (hρ : 0 < ρ) {z : ℝ} (hz : 2*ρ ≤ |z|) :
    nearDiagonalCutoff ρ z=0 := by
  change max 0 (min 1 (2-|z|/ρ))=0
  have h := (le_div_iff₀ hρ).mpr hz
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

lemma nearDiagonalCutoff_uc (ρ : ℝ) : UniformContinuous (nearDiagonalCutoff ρ) := by
  have hh := (LipschitzWith.const (0:ℝ)).max ((LipschitzWith.const (1:ℝ)).min
    ((LipschitzWith.const (2:ℝ)).sub ((lipschitzWith_smul (ρ⁻¹)).comp
      (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ)))))
  change UniformContinuous (fun z : ℝ => max 0 (min 1 (2-|z|/ρ)))
  simpa only [Function.comp_def,smul_eq_mul,Real.norm_eq_abs,mul_comm,div_eq_mul_inv] using hh.uniformContinuous

lemma farDiagonalCutoff_unit (ρ z : ℝ) : 0 ≤ farDiagonalCutoff ρ z ∧ farDiagonalCutoff ρ z ≤ 1 := by
  have h := nearDiagonalCutoff_unit ρ z
  change 0 ≤ 1-nearDiagonalCutoff ρ z ∧ 1-nearDiagonalCutoff ρ z ≤ 1
  constructor <;> linarith

lemma farDiagonalCutoff_uc (ρ : ℝ) : UniformContinuous (farDiagonalCutoff ρ) :=
  uniformContinuous_const.sub (nearDiagonalCutoff_uc ρ)

lemma farDiagonalCutoff_zero {ρ : ℝ} (hρ : 0 < ρ) {z : ℝ} (hz : |z| ≤ ρ) :
    farDiagonalCutoff ρ z=0 := by
  change 1-nearDiagonalCutoff ρ z=0
  rw [nearDiagonalCutoff_one hρ hz]; ring

lemma normalJointPast_gap_second (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) (s t : unitInterval)
    (hst : s < t) (ht : (t:ℝ) < 1) (b : Bool) (g : ℝ →ᵇ ℝ) :
    (∫ P, g (P.1 s-P.2 s)*(pairPathIncrement b s t P)^2 ∂μ)=
      (∫ P, g (P.1 s-P.2 s) ∂μ)*((c:ℝ)*((t:ℝ)-s)) := by
  simpa [currentGapTest,pairPastCoordinates] using
    normalJointPast_second μ c h (fun _ : Fin 1 => s) s t (fun _ => le_rfl) hst ht b (currentGapTest (q := 0) g)

lemma abs_mul_le_half_squares (x y : ℝ) : |x*y| ≤ (x^2+y^2)/2 := by
  rw [abs_mul]
  nlinarith [sq_abs x,sq_abs y,sq_nonneg (|x|-|y|)]

lemma normalJointPast_cross_integrable (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) (s t : unitInterval)
    (hst : s < t) (ht : (t:ℝ) < 1) :
    Integrable (fun P => pairPathIncrement false s t P*pairPathIncrement true s t P) μ := by
  have hx := normalJointPast_integrable_abs_pow μ c h s t hst ht false 2
  have hy := normalJointPast_integrable_abs_pow μ c h s t hst ht true 2
  simp only [sq_abs] at hx hy
  apply ((hx.add hy).div_const 2).mono (by fun_prop : Measurable
    (fun P => pairPathIncrement false s t P*pairPathIncrement true s t P)).aestronglyMeasurable
  filter_upwards [] with P
  change |pairPathIncrement false s t P*pairPathIncrement true s t P| ≤
    |((pairPathIncrement false s t P)^2+(pairPathIncrement true s t P)^2)/2|
  rw [abs_of_nonneg (by positivity : 0 ≤
    ((pairPathIncrement false s t P)^2+(pairPathIncrement true s t P)^2)/2)]
  exact abs_mul_le_half_squares _ _

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma normalJointPast_weighted_cross_integrable {q : ℕ} (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) (v : Fin q → unitInterval) (s t : unitInterval)
    (hst : s < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) (g : ℝ →ᵇ ℝ) :
    Integrable (fun P => F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*
      (pairPathIncrement false s t P*pairPathIncrement true s t P)) μ := by
  apply (normalJointPast_cross_integrable μ c h s t hst ht).bdd_mul (by fun_prop)
  filter_upwards [] with P
  exact (norm_mul_le _ _).trans (mul_le_mul (F.norm_coe_le_norm _) (g.norm_coe_le_norm _)
    (norm_nonneg _) (norm_nonneg _))

lemma normalJointPast_weighted_clip_integrable {q : ℕ} (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (v : Fin q → unitInterval) (s t : unitInterval)
    (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) (g : ℝ →ᵇ ℝ) :
    Integrable (fun P => F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*
      (symmetricClip 1 (pairPathIncrement false s t P)*symmetricClip 1 (pairPathIncrement true s t P))) μ := by
  apply Integrable.of_bound (by fun_prop) (‖F‖*‖g‖)
  filter_upwards [] with P
  rw [norm_mul,norm_mul,norm_mul]
  have hx : ‖symmetricClip 1 (pairPathIncrement false s t P)‖ ≤ 1 := symmetricClip_bound 1 _
  have hy : ‖symmetricClip 1 (pairPathIncrement true s t P)‖ ≤ 1 := symmetricClip_bound 1 _
  have hc : ‖symmetricClip 1 (pairPathIncrement false s t P)‖*
      ‖symmetricClip 1 (pairPathIncrement true s t P)‖ ≤ 1 := by
    simpa using mul_le_mul hx hy (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have hf := mul_le_mul (F.norm_coe_le_norm (pairPastCoordinates v P)) (g.norm_coe_le_norm (P.1 s-P.2 s))
    (norm_nonneg _) (norm_nonneg _)
  simpa using mul_le_mul hf hc (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

lemma normalJointPast_unclip_error {q : ℕ} (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) (v : Fin q → unitInterval) (s t : unitInterval)
    (hst : s < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) (g : ℝ →ᵇ ℝ)
    (hgb : ∀ z, |g z| ≤ 1) :
    |(∫ P, F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*
      (pairPathIncrement false s t P*pairPathIncrement true s t P) ∂μ)-
      (∫ P, F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*
      (symmetricClip 1 (pairPathIncrement false s t P)*symmetricClip 1 (pairPathIncrement true s t P)) ∂μ)| ≤
      4*‖F‖*(Real.sqrt ((c:ℝ)*((t:ℝ)-s)))^3*normalThirdMoment := by
  let X := pairPathIncrement false s t
  let Y := pairPathIncrement true s t
  have hi := normalJointPast_weighted_cross_integrable μ c h v s t hst ht F g
  have hj := normalJointPast_weighted_clip_integrable μ v s t F g
  have hx := normalJointPast_integrable_abs_pow μ c h s t hst ht false 3
  have hy := normalJointPast_integrable_abs_pow μ c h s t hst ht true 3
  rw [← integral_sub hi hj]
  calc
    _ ≤ ∫ P, |F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*(X P*Y P)-
        F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*(symmetricClip 1 (X P)*symmetricClip 1 (Y P))| ∂μ := by
      simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (μ := μ)
        (fun P => F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*(X P*Y P)-
        F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*(symmetricClip 1 (X P)*symmetricClip 1 (Y P))))
    _ ≤ ∫ P, 2*‖F‖*(|X P|^3+|Y P|^3) ∂μ := by
      apply integral_mono (hi.sub hj).norm ((hx.add hy).const_mul (2*‖F‖))
      intro P
      change |F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*(X P*Y P)-
        F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*(symmetricClip 1 (X P)*symmetricClip 1 (Y P))| ≤
          2*‖F‖*(|X P|^3+|Y P|^3)
      rw [← mul_sub,abs_mul,abs_mul]
      have hf : |F (pairPastCoordinates v P)| * |g (P.1 s-P.2 s)| ≤ ‖F‖ := by
        simpa using mul_le_mul (F.norm_coe_le_norm _) (hgb _) (abs_nonneg _) (norm_nonneg _)
      have hh := mul_le_mul hf (unit_clip_product_error (X P) (Y P)) (abs_nonneg _)
        (norm_nonneg F)
      nlinarith only [hh]
    _ = _ := by
      rw [integral_const_mul,integral_add hx hy,
        normalJointPast_absolute_third_moment μ c h s t hst ht false,
        normalJointPast_absolute_third_moment μ c h s t hst ht true]
      ring

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_UniformRiemannMesh
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory Filter
open scoped BigOperators Topology
namespace DirectionalTransience

lemma realMesh_zero (s t : ℝ) (n : ℕ) : realMesh s t n 0=s := by simp [realMesh]
lemma realMesh_last (s t : ℝ) {n : ℕ} (hn : 0 < n) : realMesh s t n n=t := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [realMesh,mul_div_cancel_left₀ _ hn0]
  ring
lemma realMesh_sub (s t : ℝ) (n j : ℕ) : realMesh s t n (j+1)-realMesh s t n j=(t-s)/n := by
  simp only [realMesh,Nat.cast_add,Nat.cast_one]
  ring
lemma realMesh_mono {s t : ℝ} (hst : s ≤ t) (n : ℕ) : Monotone (realMesh s t n) := by
  intro i j hij
  simpa only [realMesh, add_comm] using add_le_add_left (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr hij) (sub_nonneg.mpr hst)) (Nat.cast_nonneg n)) s

lemma riemann_error_le (f : ℝ → ℝ) (hf : Continuous f) {s t ε δ : ℝ}
    (hst : s ≤ t) (hε : 0 ≤ ε) (hmod : ∀ x y, dist x y < δ → dist (f x) (f y) ≤ ε)
    {n : ℕ} (hn : 0 < n) (hδ : (t-s)/n < δ) :
    |(∑ j ∈ Finset.range n, (t-s)/n*f (realMesh s t n j))-(∫ u in s..t, f u)| ≤ ε*(t-s) := by
  have hmono := realMesh_mono hst n
  have hi : ∀ k < n, IntervalIntegrable f volume (realMesh s t n k) (realMesh s t n (k+1)) :=
    fun _ _ => hf.intervalIntegrable _ _
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hi
  rw [realMesh_zero,realMesh_last s t hn] at hsum
  rw [← hsum,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range n, |(t-s)/n*f (realMesh s t n j)-
        (∫ u in realMesh s t n j..realMesh s t n (j+1), f u)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range n, ε*((t-s)/n) := by
      apply Finset.sum_le_sum
      intro j hj
      have he : (t-s)/n*f (realMesh s t n j) =
          ∫ _u in realMesh s t n j..realMesh s t n (j+1), f (realMesh s t n j) := by
        rw [intervalIntegral.integral_const,realMesh_sub,smul_eq_mul]
      rw [he,← intervalIntegral.integral_sub intervalIntegrable_const (hf.intervalIntegrable _ _)]
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := realMesh s t n j)
        (b := realMesh s t n (j+1)) (C := |ε|) (f := fun u => f (realMesh s t n j)-f u) (fun u hu => by
          rw [Set.uIoc_of_le (hmono (Nat.le_succ j))] at hu
          have hd : dist (realMesh s t n j) u < δ := by
            rw [Real.dist_eq,abs_of_nonpos (by linarith [hu.1] : realMesh s t n j-u ≤ 0)]
            have hw := realMesh_sub s t n j
            linarith [hu.2]
          simpa only [Real.norm_eq_abs,Real.dist_eq,abs_of_nonneg hε] using hmod _ _ hd)
      simpa only [Real.norm_eq_abs,realMesh_sub,abs_of_nonneg hε,abs_of_nonneg (div_nonneg (sub_nonneg.mpr hst) (Nat.cast_nonneg n))] using hb
    _ = ε*(t-s) := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp

lemma tendsto_riemann_mesh (f : ℝ → ℝ) (hf : UniformContinuous f) {s t : ℝ} (hst : s < t) :
    Tendsto (fun n => ∑ j ∈ Finset.range n, (t-s)/n*f (realMesh s t n j)) atTop
      (𝓝 (∫ u in s..t, f u)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he : 0 < ε/(2*(t-s)) := div_pos hε (mul_pos (by norm_num) (sub_pos.mpr hst))
  obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuous_iff.mp hf (ε/(2*(t-s))) he
  have hh : Tendsto (fun n : ℕ => (t-s)/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((hh.eventually_lt_const hδ).and (eventually_gt_atTop 0))
  refine ⟨N,fun n hn => ?_⟩
  have hb := riemann_error_le f hf.continuous hst.le he.le
    (fun x y hxy => (hmod hxy).le) (hN n hn).2 (hN n hn).1
  rw [Real.dist_eq]
  have heq : ε/(2*(t-s))*(t-s)=ε/2 := by field_simp [ne_of_gt (sub_pos.mpr hst)]
  rw [heq] at hb
  exact hb.trans_lt (by linarith)

end DirectionalTransience

end

section

open MeasureTheory Filter
open scoped BigOperators Topology
namespace DirectionalTransience

lemma realMesh_between {s t : ℝ} (hst : s ≤ t) {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    s ≤ realMesh s t n j ∧ realMesh s t n j ≤ t := by
  constructor
  · simpa only [realMesh_zero] using (realMesh_mono hst n (Nat.zero_le j))
  · simpa only [realMesh_last s t hn] using (realMesh_mono hst n hj)

lemma unitMesh_coe (s t : unitInterval) (hst : s ≤ t) {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    (unitMesh s t n j:ℝ)=realMesh s t n j := by
  have hb := realMesh_between hst hn hj
  have hm : realMesh (s:ℝ) t n j ∈ unitInterval := ⟨s.property.1.trans hb.1,hb.2.trans t.property.2⟩
  simp only [unitMesh,Set.projIcc_of_mem zero_le_one hm]

lemma unitMesh_between (s t : unitInterval) (hst : s ≤ t) {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    s ≤ unitMesh s t n j ∧ unitMesh s t n j ≤ t := by
  change (s:ℝ) ≤ (unitMesh s t n j:ℝ) ∧ (unitMesh s t n j:ℝ) ≤ t
  rw [unitMesh_coe s t hst hn hj]
  exact realMesh_between hst hn hj

lemma unitMesh_zero (s t : unitInterval) (n : ℕ) : unitMesh s t n 0=s := by
  simp only [unitMesh,realMesh_zero,Set.projIcc_of_mem zero_le_one s.property]

lemma unitMesh_last (s t : unitInterval) {n : ℕ} (hn : 0 < n) : unitMesh s t n n=t := by
  simp only [unitMesh,realMesh_last (s:ℝ) t hn,Set.projIcc_of_mem zero_le_one t.property]

lemma unitMesh_sub (s t : unitInterval) (hst : s ≤ t) {n j : ℕ} (hn : 0 < n) (hj : j < n) :
    (unitMesh s t n (j+1):ℝ)-(unitMesh s t n j:ℝ)=((t:ℝ)-s)/n := by
  rw [unitMesh_coe s t hst hn (Nat.succ_le_of_lt hj),unitMesh_coe s t hst hn hj.le,realMesh_sub]

lemma unitMesh_step_lt (s t : unitInterval) (hst : s < t) {n j : ℕ} (hn : 0 < n) (hj : j < n) :
    unitMesh s t n j < unitMesh s t n (j+1) := by
  have hh := unitMesh_sub s t hst.le hn hj
  have hp : 0 < ((t:ℝ)-s)/(n:ℝ) := div_pos (sub_pos.mpr (show (s:ℝ) < t from hst))
    (Nat.cast_pos.mpr hn)
  change (unitMesh s t n j:ℝ) < (unitMesh s t n (j+1):ℝ)
  linarith

end DirectionalTransience

end

section

open Filter
open scoped BigOperators Topology
namespace DirectionalTransience

lemma contraction_recurrence_error (z : ℕ → ℂ) (r : ℂ) (e : ℕ → ℝ) (n : ℕ)
    (hr : ‖r‖ ≤ 1) (he : ∀ j < n, ‖z (j+1)-r*z j‖ ≤ e j) :
    ‖z n-r^n*z 0‖ ≤ ∑ j ∈ Finset.range n, e j := by
  induction n with
  | zero => simp
  | succ n ihn =>
    have hn := ihn (fun j hj => he j (Nat.lt_succ_of_lt hj))
    have heq : z (n+1)-r^(n+1)*z 0=(z (n+1)-r*z n)+r*(z n-r^n*z 0) := by
      rw [pow_succ]; ring
    rw [heq,Finset.sum_range_succ]
    calc
      _ ≤ ‖z (n+1)-r*z n‖+‖r‖*‖z n-r^n*z 0‖ := by
        simpa only [norm_mul] using norm_add_le (z (n+1)-r*z n) (r*(z n-r^n*z 0))
      _ ≤ e n+‖z n-r^n*z 0‖ := add_le_add (he n (Nat.lt_succ_self n))
        ((mul_le_mul_of_nonneg_right hr (norm_nonneg _)).trans_eq (one_mul _))
      _ ≤ _ := by linarith

lemma realEulerCoefficient_norm {lam δ : ℝ} (hlam : 0 ≤ lam) (hδ : 0 ≤ δ) (h : lam*δ ≤ 1) :
    ‖(1-((lam*δ:ℝ):ℂ))‖ ≤ 1 := by
  rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr h)]
  nlinarith

lemma scaled_exp_tendsto_zero {A L : ℝ} (hA : 0 < A) (hL : 0 < L) :
    Tendsto (fun n : ℕ => (n:ℝ)*Real.exp (-A/(L/n))) atTop (𝓝 0) := by
  have hat : Tendsto (fun n : ℕ => (A/L)*(n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (div_pos hA hL)
  have hh := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hat).const_mul (L/A)
  simp only [pow_one,mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hid : -A/(L/(n:ℝ))= -(A/L*(n:ℝ)) := by field_simp
  rw [hid]
  simp only [Function.comp_apply]
  field_simp

lemma scaled_sqrt_cube_tendsto_zero {c L : ℝ} (hc : 0 ≤ c) (hL : 0 ≤ L) :
    Tendsto (fun n : ℕ => (n:ℝ)*(Real.sqrt (c*(L/n)))^3) atTop (𝓝 0) := by
  have hh : Tendsto (fun n : ℕ => c*(L/n)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => L/(n:ℝ)) atTop (𝓝 0)).const_mul c
  have hs := (Real.continuous_sqrt.tendsto 0).comp hh
  simp only [Real.sqrt_zero] at hs
  have hj := hs.const_mul (c*L)
  simp only [mul_zero] at hj
  apply hj.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hp : 0 ≤ c*(L/(n:ℝ)) := mul_nonneg hc (div_nonneg hL (Nat.cast_nonneg n))
  calc
    c*L*Real.sqrt (c*(L/(n:ℝ))) = (n:ℝ)*(c*(L/(n:ℝ)))*Real.sqrt (c*(L/(n:ℝ))) := by field_simp
    _ = _ := by
      have hcube : (Real.sqrt (c*(L/(n:ℝ))))^3=c*(L/(n:ℝ))*Real.sqrt (c*(L/(n:ℝ))) := by
        calc
          _ = (Real.sqrt (c*(L/(n:ℝ))))^2*Real.sqrt (c*(L/(n:ℝ))) := by ring
          _ = _ := by rw [Real.sq_sqrt hp]
      rw [hcube]
      ring

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_CutoffTimeAverages
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma cutoffMean_unit (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (ρ : ℝ) (s : unitInterval) :
    0 ≤ cutoffMean μ ρ s ∧ cutoffMean μ ρ s ≤ 1 := by
  constructor
  · exact integral_nonneg (fun P => (nearDiagonalCutoff_unit ρ _).1)
  · have hh := norm_integral_le_of_norm_le_const (μ := μ) (f := fun P : RealPathPair =>
        nearDiagonalCutoff ρ (P.1 s-P.2 s)) (C := 1) (by
        filter_upwards [] with P
        rw [Real.norm_eq_abs,abs_of_nonneg (nearDiagonalCutoff_unit ρ _).1]
        exact (nearDiagonalCutoff_unit ρ _).2)
    simp only [Measure.real,measure_univ,ENNReal.toReal_one,mul_one,Real.norm_eq_abs] at hh
    exact (le_abs_self _).trans hh

lemma cutoffMeanExtension_uniformContinuous (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (ρ : ℝ) :
    UniformContinuous (cutoffMeanExtension μ ρ) := by
  exact (CompactSpace.uniformContinuous_of_continuous (cutoffMean μ ρ).continuous).comp
    (LipschitzWith.projIcc zero_le_one).uniformContinuous

lemma cutoff_riemann_tendsto (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (ρ : ℝ)
    {s t : ℝ} (hst : s < t) :
    Tendsto (fun n => ∑ j ∈ Finset.range n, (t-s)/n*cutoffMeanExtension μ ρ (realMesh s t n j)) atTop
      (𝓝 (∫ u in s..t, cutoffMeanExtension μ ρ u)) :=
  tendsto_riemann_mesh _ (cutoffMeanExtension_uniformContinuous μ ρ) hst

lemma nearDiagonalCutoff_tendsto_zero {z : ℝ} (hz : z ≠ 0) :
    Tendsto (fun n : ℕ => nearDiagonalCutoff (1/((n:ℝ)+1)) z) atTop (𝓝 0) := by
  have hh : Tendsto (fun n : ℕ => 2*(1/((n:ℝ)+1))) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop) :
      Tendsto (fun n : ℕ => (2:ℝ)/((n:ℝ)+1)) atTop (𝓝 0))
  apply tendsto_const_nhds.congr'
  filter_upwards [hh.eventually_lt_const (abs_pos.mpr hz)] with n hn
  exact (nearDiagonalCutoff_zero (by positivity : 0 < 1/((n:ℝ)+1)) hn.le).symm

lemma diagonal_zero_cutoff_integral_tendsto (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (hz : (μ.prod volume) {z : RealPathPair × unitInterval | z.1.1 z.2-z.1.2 z.2=0}=0) :
    Tendsto (fun n : ℕ => ∫ z : RealPathPair × unitInterval,
      nearDiagonalCutoff (1/((n:ℝ)+1)) (z.1.1 z.2-z.1.2 z.2) ∂μ.prod volume) atTop (𝓝 0) := by
  have hae : ∀ᵐ z : RealPathPair × unitInterval ∂μ.prod volume, z.1.1 z.2-z.1.2 z.2 ≠ 0 := by
    rw [ae_iff]
    simpa using hz
  have hh := tendsto_integral_of_dominated_convergence (μ := μ.prod volume) (fun _ => (1:ℝ))
    (fun n => (by fun_prop : Measurable (fun z : RealPathPair × unitInterval =>
      nearDiagonalCutoff (1/((n:ℝ)+1)) (z.1.1 z.2-z.1.2 z.2))).aestronglyMeasurable)
    (integrable_const 1) (fun n => by
      filter_upwards [] with z
      rw [Real.norm_eq_abs,abs_of_nonneg (nearDiagonalCutoff_unit _ _).1]
      exact (nearDiagonalCutoff_unit _ _).2) (show ∀ᵐ z : RealPathPair × unitInterval ∂μ.prod volume,
      Tendsto (fun n : ℕ => nearDiagonalCutoff (1/((n:ℝ)+1)) (z.1.1 z.2-z.1.2 z.2)) atTop (𝓝 0) by
      filter_upwards [hae] with z hz
      exact nearDiagonalCutoff_tendsto_zero hz)
  simpa using hh

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma cutoffMean_integral_eq (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (ρ : ℝ) :
    (∫ u in (0:ℝ)..1, cutoffMeanExtension μ ρ u)=
      ∫ z : RealPathPair × unitInterval, nearDiagonalCutoff ρ (z.1.1 z.2-z.1.2 z.2) ∂μ.prod volume := by
  have hi : Integrable (fun z : RealPathPair × unitInterval =>
      nearDiagonalCutoff ρ (z.1.1 z.2-z.1.2 z.2)) (μ.prod volume) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with z
    rw [Real.norm_eq_abs,abs_of_nonneg (nearDiagonalCutoff_unit ρ _).1]
    exact (nearDiagonalCutoff_unit ρ _).2
  rw [integral_prod_symm _ hi]
  have hid : (fun u : unitInterval => (∫ P : RealPathPair, nearDiagonalCutoff ρ (P.1 u-P.2 u) ∂μ))=
      fun u : unitInterval => cutoffMeanExtension μ ρ (u:ℝ) := by
    funext u
    simp only [cutoffMeanExtension,Set.projIcc_of_mem zero_le_one u.property]
    rfl
  rw [hid,integral_subtype measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le zero_le_one]

lemma cutoffMean_subinterval_le (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (ρ : ℝ)
    (s t : unitInterval) (hst : s ≤ t) :
    (∫ u in (s:ℝ)..t, cutoffMeanExtension μ ρ u) ≤
      ∫ z : RealPathPair × unitInterval, nearDiagonalCutoff ρ (z.1.1 z.2-z.1.2 z.2) ∂μ.prod volume := by
  rw [← cutoffMean_integral_eq]
  exact intervalIntegral.integral_mono_interval s.property.1 hst t.property.2
    (ae_of_all _ (fun u => (cutoffMean_unit μ ρ _).1))
    ((cutoffMeanExtension_uniformContinuous μ ρ).continuous.intervalIntegrable 0 1)

lemma cutoffMean_subinterval_nonneg (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (ρ : ℝ)
    (s t : unitInterval) (hst : s ≤ t) :
    0 ≤ ∫ u in (s:ℝ)..t, cutoffMeanExtension μ ρ u := by
  exact intervalIntegral.integral_nonneg hst (fun u _ => (cutoffMean_unit μ ρ _).1)

lemma diagonal_zero_subinterval_cutoff_tendsto (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (hz : (μ.prod volume) {z : RealPathPair × unitInterval | z.1.1 z.2-z.1.2 z.2=0}=0)
    (s t : unitInterval) (hst : s ≤ t) :
    Tendsto (fun n : ℕ => ∫ u in (s:ℝ)..t, cutoffMeanExtension μ (1/((n:ℝ)+1)) u) atTop (𝓝 0) := by
  exact squeeze_zero (fun n => cutoffMean_subinterval_nonneg μ _ s t hst)
    (fun n => cutoffMean_subinterval_le μ _ s t hst) (diagonal_zero_cutoff_integral_tendsto μ hz)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Crossings_NearCrossEstimates
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma normalJointPast_weighted_square_integrable (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) (s t : unitInterval)
    (hst : s < t) (ht : (t:ℝ) < 1) (b : Bool) (g : ℝ →ᵇ ℝ) :
    Integrable (fun P => g (P.1 s-P.2 s)*(pairPathIncrement b s t P)^2) μ := by
  have hi := normalJointPast_integrable_abs_pow μ c h s t hst ht b 2
  simp only [sq_abs] at hi
  apply hi.bdd_mul (by fun_prop)
  filter_upwards [] with P
  exact g.norm_coe_le_norm _

lemma normalJointPast_near_cross {q : ℕ} (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) (v : Fin q → unitInterval) (s t : unitInterval)
    (hst : s < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) (g : ℝ →ᵇ ℝ)
    (hg : ∀ z, 0 ≤ g z) :
    |∫ P, F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*
      (pairPathIncrement false s t P*pairPathIncrement true s t P) ∂μ| ≤
      ‖F‖*((c:ℝ)*((t:ℝ)-s))*(∫ P, g (P.1 s-P.2 s) ∂μ) := by
  let X := pairPathIncrement false s t
  let Y := pairPathIncrement true s t
  have hi := normalJointPast_weighted_cross_integrable μ c h v s t hst ht F g
  have hx := normalJointPast_weighted_square_integrable μ c h s t hst ht false g
  have hy := normalJointPast_weighted_square_integrable μ c h s t hst ht true g
  calc
    _ ≤ ∫ P, |F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*(X P*Y P)| ∂μ := by
      simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm (μ := μ)
        (fun P => F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*(X P*Y P)))
    _ ≤ ∫ P, ‖F‖/2*(g (P.1 s-P.2 s)*(X P)^2+g (P.1 s-P.2 s)*(Y P)^2) ∂μ := by
      apply integral_mono hi.norm ((hx.add hy).const_mul (‖F‖/2))
      intro P
      change |F (pairPastCoordinates v P)*g (P.1 s-P.2 s)*(X P*Y P)| ≤ _
      rw [abs_mul,abs_mul,abs_of_nonneg (hg _)]
      have hb := mul_le_mul (mul_le_mul_of_nonneg_right (F.norm_coe_le_norm (pairPastCoordinates v P)) (hg (P.1 s-P.2 s)))
        (abs_mul_le_half_squares (X P) (Y P)) (abs_nonneg _) (mul_nonneg (norm_nonneg _) (hg (P.1 s-P.2 s)))
      simp only [Real.norm_eq_abs] at hb
      change |F (pairPastCoordinates v P)| *g (P.1 s-P.2 s)*|X P*Y P| ≤
        ‖F‖/2*(g (P.1 s-P.2 s)*(X P)^2+g (P.1 s-P.2 s)*(Y P)^2)
      nlinarith only [hb]
    _ = _ := by
      rw [integral_const_mul,integral_add hx hy,
        normalJointPast_gap_second μ c h s t hst ht false,
        normalJointPast_gap_second μ c h s t hst ht true]
      ring

lemma normalJointPast_cross_bound {q : ℕ} (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) {A K : ℝ} (hcross : SeparatedCrossBound μ A K)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    |∫ P, F (pairPastCoordinates v P)*
      (pairPathIncrement false s t P*pairPathIncrement true s t P) ∂μ| ≤
      ‖F‖*(K*Real.exp (-A*ρ^2/((t:ℝ)-s))+
        4*(Real.sqrt ((c:ℝ)*((t:ℝ)-s)))^3*normalThirdMoment+
        ((c:ℝ)*((t:ℝ)-s))*(∫ P, nearDiagonalCutoff ρ (P.1 s-P.2 s) ∂μ)) := by
  let X := pairPathIncrement false s t
  let Y := pairPathIncrement true s t
  let G := farDiagonalCutoff ρ
  let N := nearDiagonalCutoff ρ
  have hGb : ∀ z, |G z| ≤ 1 := fun z => by
    rw [abs_of_nonneg (farDiagonalCutoff_unit ρ z).1]
    exact (farDiagonalCutoff_unit ρ z).2
  have hfar := hcross q v s t hv hst ht F G (farDiagonalCutoff_uc ρ) hGb ρ hρ
    (fun _ hz => farDiagonalCutoff_zero hρ hz)
  have he := normalJointPast_unclip_error μ c h v s t hst ht F G hGb
  have hn := normalJointPast_near_cross μ c h v s t hst ht F N (fun z => (nearDiagonalCutoff_unit ρ z).1)
  have hI := normalJointPast_weighted_cross_integrable μ c h v s t hst ht F G
  have hJ := normalJointPast_weighted_cross_integrable μ c h v s t hst ht F N
  have hid : (∫ P, F (pairPastCoordinates v P)*(X P*Y P) ∂μ)=
      (∫ P, F (pairPastCoordinates v P)*G (P.1 s-P.2 s)*(X P*Y P) ∂μ)+
      (∫ P, F (pairPastCoordinates v P)*N (P.1 s-P.2 s)*(X P*Y P) ∂μ) := by
    rw [← integral_add hI hJ]
    congr 1
    funext P
    change _ = F (pairPastCoordinates v P)*(1-N (P.1 s-P.2 s))*(X P*Y P)+_
    ring
  change |∫ P, F (pairPastCoordinates v P)*(X P*Y P) ∂μ| ≤ _
  rw [hid]
  have hab := abs_add_le
    (∫ P, F (pairPastCoordinates v P)*G (P.1 s-P.2 s)*(X P*Y P) ∂μ)
    (∫ P, F (pairPastCoordinates v P)*N (P.1 s-P.2 s)*(X P*Y P) ∂μ)
  have hf : |∫ P, F (pairPastCoordinates v P)*G (P.1 s-P.2 s)*(X P*Y P) ∂μ| ≤
      4*‖F‖*(Real.sqrt ((c:ℝ)*((t:ℝ)-s)))^3*normalThirdMoment+
      ‖F‖*(K*Real.exp (-A*ρ^2/((t:ℝ)-s))) := by
    have hh := abs_add_le
      ((∫ P, F (pairPastCoordinates v P)*G (P.1 s-P.2 s)*(X P*Y P) ∂μ)-
      (∫ P, F (pairPastCoordinates v P)*G (P.1 s-P.2 s)*
        (symmetricClip 1 (X P)*symmetricClip 1 (Y P)) ∂μ))
      (∫ P, F (pairPastCoordinates v P)*G (P.1 s-P.2 s)*
        (symmetricClip 1 (X P)*symmetricClip 1 (Y P)) ∂μ)
    rw [sub_add_cancel] at hh
    exact hh.trans (add_le_add he hfar)
  nlinarith only [hab,hf,hn]

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CharacteristicTaylor
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma charPhase_add (x y : ℝ) : charPhase (x+y)=charPhase x*charPhase y := by
  simp only [charPhase,Complex.ofReal_add,add_mul,Complex.exp_add]

lemma charTaylorConstant_nonneg : 0 ≤ charTaylorConstant := by unfold charTaylorConstant; positivity

lemma charPhase_quadratic_error (x : ℝ) :
    ‖charPhase x-(1+(x:ℂ)*Complex.I-(x:ℂ)^2/2)‖ ≤ charTaylorConstant*|x|^3 := by
  have hx0 := abs_nonneg x
  have heq : (∑ m ∈ Finset.range 3, (((x:ℂ)*Complex.I)^m)/(m.factorial:ℂ)) =
      1+(x:ℂ)*Complex.I-(x:ℂ)^2/2 := by
    simp [Finset.sum_range_succ, pow_succ]
    ring_nf
    simp [Complex.I_sq]
    ring
  by_cases hx : |x| ≤ 1
  · have h := Complex.norm_exp_sub_sum_le_norm_mul_exp ((x:ℂ)*Complex.I) 3
    rw [heq] at h
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one] at h
    exact h.trans (by
      have he := Real.exp_le_exp.mpr hx
      have hp : 0 ≤ |x|^3 := by positivity
      unfold charTaylorConstant
      nlinarith)
  · have hx1 : 1 ≤ |x| := le_of_not_ge hx
    have hn : ‖charPhase x-(1+(x:ℂ)*Complex.I-(x:ℂ)^2/2)‖ ≤ 2+|x|+|x|^2/2 := by
      calc
        _ ≤ ‖charPhase x‖+‖1+(x:ℂ)*Complex.I-(x:ℂ)^2/2‖ := norm_sub_le _ _
        _ ≤ 1+(‖(1:ℂ)‖+‖(x:ℂ)*Complex.I‖+‖(x:ℂ)^2/2‖) := by
          rw [charPhase_norm]
          exact add_le_add (le_refl 1) ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _)))
        _ = 2+|x|+|x|^2/2 := by simp [norm_pow]; ring
    have h2 : |x| ≤ |x|^2 := by nlinarith
    have h3 : |x|^2 ≤ |x|^3 := by nlinarith [mul_le_mul_of_nonneg_right hx1 (sq_nonneg |x|)]
    have hp : 0 ≤ Real.exp 1*|x|^3 := by positivity
    unfold charTaylorConstant
    nlinarith

lemma abs_linear_cube_bound (a b x y : ℝ) :
    |a*x+b*y|^3 ≤ 4*(|a|+|b|)^3*(|x|^3+|y|^3) := by
  have hsum := abs_add_le (a*x) (b*y)
  rw [abs_mul,abs_mul] at hsum
  have ha := abs_nonneg a
  have hb := abs_nonneg b
  have hx := abs_nonneg x
  have hy := abs_nonneg y
  have hlin : |a*x+b*y| ≤ (|a|+|b|)*(|x|+|y|) := by nlinarith
  have hpow := pow_le_pow_left₀ (abs_nonneg _) hlin 3
  have hc : (|x|+|y|)^3 ≤ 4*(|x|^3+|y|^3) := by
    nlinarith [mul_nonneg (sq_nonneg (|x|-|y|)) (add_nonneg hx hy)]
  calc
    _ ≤ ((|a|+|b|)*(|x|+|y|))^3 := hpow
    _ = (|a|+|b|)^3*(|x|+|y|)^3 := mul_pow _ _ _
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hc (pow_nonneg (add_nonneg ha hb) 3)]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma normalJointPast_complex_weighted_moment_integrable {q k : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    (v : Fin q → unitInterval) (s t : unitInterval) (hst : s < t) (ht : (t:ℝ) < 1) (b : Bool)
    (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) :
    Integrable (fun P => F (pairPastCoordinates v P)*((pairPathIncrement b s t P:ℂ)^k)) μ := by
  have hi := normalJointPast_integrable_abs_pow μ c h s t hst ht b k
  have hj : Integrable (fun P => (pairPathIncrement b s t P)^k) μ :=
    (integrable_norm_iff (by fun_prop : Measurable (fun P => (pairPathIncrement b s t P)^k)).aestronglyMeasurable).mp
      (by simpa [Real.norm_eq_abs,abs_pow] using hi)
  have hc := hj.ofReal (𝕜 := ℂ)
  simp only [RCLike.ofReal_eq_complex_ofReal,Complex.ofReal_pow] at hc
  apply hc.bdd_mul (by fun_prop)
  filter_upwards [] with P
  exact F.norm_coe_le_norm _

lemma normalJointPast_complex_moment {q k : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s < t) (ht : (t:ℝ) < 1) (b : Bool) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) :
    (∫ P, F (pairPastCoordinates v P)*((pairPathIncrement b s t P:ℂ)^k) ∂μ)=
      (∫ P, F (pairPastCoordinates v P) ∂μ)*
        ((∫ z : ℝ, (z^k:ℝ) ∂gaussianReal 0 (c*Real.toNNReal ((t:ℝ)-s)) : ℝ):ℂ) := by
  have hh := product_law_integral_mul μ (gaussianReal 0 (c*Real.toNNReal ((t:ℝ)-s)))
    (pairPastCoordinates v) (pairPathIncrement b s t) (by fun_prop) (by fun_prop)
    (h q v s t hv hst ht b) F (fun z => (z:ℂ)^k) F.continuous.measurable (by fun_prop)
  simpa only [← Complex.ofReal_pow,integral_complex_ofReal] using hh

lemma normalJointPast_complex_mean {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s < t) (ht : (t:ℝ) < 1) (b : Bool) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) :
    (∫ P, F (pairPastCoordinates v P)*(pairPathIncrement b s t P:ℂ) ∂μ)=0 := by
  simpa using normalJointPast_complex_moment (k := 1) μ c h v s t hv hst ht b F

lemma normalJointPast_complex_second {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s < t) (ht : (t:ℝ) < 1) (b : Bool) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) :
    (∫ P, F (pairPastCoordinates v P)*(pairPathIncrement b s t P:ℂ)^2 ∂μ)=
      (∫ P, F (pairPastCoordinates v P) ∂μ)*(((c:ℝ)*((t:ℝ)-s)):ℂ) := by
  rw [normalJointPast_complex_moment μ c h v s t hv hst ht b F,gaussianReal_second_moment,
    NNReal.coe_mul,Real.toNNReal_of_nonneg (sub_nonneg.mpr (show (s:ℝ) ≤ t from hst.le))]
  push_cast
  rfl

lemma normalJointPast_complex_cross_integrable {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    (v : Fin q → unitInterval) (s t : unitInterval) (hst : s < t) (ht : (t:ℝ) < 1)
    (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) :
    Integrable (fun P => F (pairPastCoordinates v P)*
      ((pairPathIncrement false s t P*pairPathIncrement true s t P:ℝ):ℂ)) μ := by
  apply (normalJointPast_cross_integrable μ c h s t hst ht).ofReal.bdd_mul (by fun_prop)
  filter_upwards [] with P
  exact F.norm_coe_le_norm _

lemma normalJointPast_complex_cross_bound {q : ℕ} (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) {A K : ℝ} (hK : 0 ≤ K) (hcross : SeparatedCrossBound μ A K)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ‖∫ P, F (pairPastCoordinates v P)*
      ((pairPathIncrement false s t P*pairPathIncrement true s t P:ℝ):ℂ) ∂μ‖ ≤
      2*‖F‖*(K*Real.exp (-A*ρ^2/((t:ℝ)-s))+
        4*(Real.sqrt ((c:ℝ)*((t:ℝ)-s)))^3*normalThirdMoment+
        ((c:ℝ)*((t:ℝ)-s))*(∫ P, nearDiagonalCutoff ρ (P.1 s-P.2 s) ∂μ)) := by
  let Fr := F.comp Complex.reCLM Complex.reCLM.lipschitz
  let Fi := F.comp Complex.imCLM Complex.imCLM.lipschitz
  have hrn : ‖Fr‖ ≤ ‖F‖ := (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr
    (fun z => (Complex.abs_re_le_norm (F z)).trans (F.norm_coe_le_norm z))
  have hin : ‖Fi‖ ≤ ‖F‖ := (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr
    (fun z => (Complex.abs_im_le_norm (F z)).trans (F.norm_coe_le_norm z))
  have hr := normalJointPast_cross_bound μ c h hcross v s t hv hst ht Fr hρ
  have hi := normalJointPast_cross_bound μ c h hcross v s t hv hst ht Fi hρ
  have hI := normalJointPast_complex_cross_integrable μ c h v s t hst ht F
  have hre := integral_re hI
  have him := integral_im hI
  change (∫ P, (F (pairPastCoordinates v P)*
    ((pairPathIncrement false s t P*pairPathIncrement true s t P:ℝ):ℂ)).re ∂μ)=_ at hre
  change (∫ P, (F (pairPastCoordinates v P)*
    ((pairPathIncrement false s t P*pairPathIncrement true s t P:ℝ):ℂ)).im ∂μ)=_ at him
  simp only [RCLike.re_eq_complex_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] at hre
  simp only [RCLike.im_eq_complex_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_add] at him
  have hpos : 0 ≤ K*Real.exp (-A*ρ^2/((t:ℝ)-s))+
        4*(Real.sqrt ((c:ℝ)*((t:ℝ)-s)))^3*normalThirdMoment+
        ((c:ℝ)*((t:ℝ)-s))*(∫ P, nearDiagonalCutoff ρ (P.1 s-P.2 s) ∂μ) := by
    have hh : 0 ≤ ∫ P : RealPathPair, nearDiagonalCutoff ρ (P.1 s-P.2 s) ∂μ :=
      integral_nonneg (fun P => (nearDiagonalCutoff_unit ρ (P.1 s-P.2 s)).1)
    have hd : 0 ≤ (t:ℝ)-s := sub_nonneg.mpr (show (s:ℝ) ≤ t from hst.le)
    have hm := normalThirdMoment_nonneg
    positivity
  calc
    _ ≤ |(∫ P, F (pairPastCoordinates v P)*
      ((pairPathIncrement false s t P*pairPathIncrement true s t P:ℝ):ℂ) ∂μ).re|+
      |(∫ P, F (pairPastCoordinates v P)*
      ((pairPathIncrement false s t P*pairPathIncrement true s t P:ℝ):ℂ) ∂μ).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ _ := by
      rw [← hre,← him]
      have hr' := hr.trans (mul_le_mul_of_nonneg_right hrn hpos)
      have hi' := hi.trans (mul_le_mul_of_nonneg_right hin hpos)
      change |∫ P, Fr (pairPastCoordinates v P)*(pairPathIncrement false s t P*pairPathIncrement true s t P) ∂μ|+
        |∫ P, Fi (pairPastCoordinates v P)*(pairPathIncrement false s t P*pairPathIncrement true s t P) ∂μ| ≤ _
      nlinarith only [hr',hi']

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_NormalLinearPast
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma normalJointPast_linear_mean_integrable {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    (v : Fin q → unitInterval) (s t : unitInterval) (hst : s < t) (ht : (t:ℝ) < 1)
    (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ) :
    Integrable (fun P => F (pairPastCoordinates v P)*(pairLinearIncrement a b s t P:ℂ)) μ := by
  have hx := normalJointPast_complex_weighted_moment_integrable (k := 1) μ c h v s t hst ht false F
  have hy := normalJointPast_complex_weighted_moment_integrable (k := 1) μ c h v s t hst ht true F
  simp only [pow_one] at hx hy
  have hid : (fun P => F (pairPastCoordinates v P)*(pairLinearIncrement a b s t P:ℂ))=
      (fun P => (a:ℂ)*(F (pairPastCoordinates v P)*(pairPathIncrement false s t P:ℂ))+
        (b:ℂ)*(F (pairPastCoordinates v P)*(pairPathIncrement true s t P:ℂ))) := by
    funext P
    simp only [pairLinearIncrement,ContinuousMap.coe_mk,Complex.ofReal_add,Complex.ofReal_mul]
    ring
  rw [hid]
  exact (hx.const_mul (a:ℂ)).add (hy.const_mul (b:ℂ))

lemma normalJointPast_linear_mean {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ) :
    (∫ P, F (pairPastCoordinates v P)*(pairLinearIncrement a b s t P:ℂ) ∂μ)=0 := by
  have hx := normalJointPast_complex_weighted_moment_integrable (k := 1) μ c h v s t hst ht false F
  have hy := normalJointPast_complex_weighted_moment_integrable (k := 1) μ c h v s t hst ht true F
  simp only [pow_one] at hx hy
  have hid : (fun P => F (pairPastCoordinates v P)*(pairLinearIncrement a b s t P:ℂ))=
      (fun P => (a:ℂ)*(F (pairPastCoordinates v P)*(pairPathIncrement false s t P:ℂ))+
        (b:ℂ)*(F (pairPastCoordinates v P)*(pairPathIncrement true s t P:ℂ))) := by
    funext P
    simp only [pairLinearIncrement,ContinuousMap.coe_mk,Complex.ofReal_add,Complex.ofReal_mul]
    ring
  rw [hid,integral_add (hx.const_mul _) (hy.const_mul _),integral_const_mul,integral_const_mul,
    normalJointPast_complex_mean μ c h v s t hv hst ht false,
    normalJointPast_complex_mean μ c h v s t hv hst ht true]
  simp

lemma normalJointPast_linear_second_integrable {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    (v : Fin q → unitInterval) (s t : unitInterval) (hst : s < t) (ht : (t:ℝ) < 1)
    (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ) :
    Integrable (fun P => F (pairPastCoordinates v P)*(pairLinearIncrement a b s t P:ℂ)^2) μ := by
  have hx := normalJointPast_complex_weighted_moment_integrable (k := 2) μ c h v s t hst ht false F
  have hy := normalJointPast_complex_weighted_moment_integrable (k := 2) μ c h v s t hst ht true F
  have hxy := normalJointPast_complex_cross_integrable μ c h v s t hst ht F
  have hid : (fun P => F (pairPastCoordinates v P)*(pairLinearIncrement a b s t P:ℂ)^2)=
      (fun P => (a:ℂ)^2*(F (pairPastCoordinates v P)*(pairPathIncrement false s t P:ℂ)^2)+
        (b:ℂ)^2*(F (pairPastCoordinates v P)*(pairPathIncrement true s t P:ℂ)^2)+
        2*(a:ℂ)*b*(F (pairPastCoordinates v P)*
        ((pairPathIncrement false s t P*pairPathIncrement true s t P:ℝ):ℂ))) := by
    funext P
    simp only [pairLinearIncrement,ContinuousMap.coe_mk,Complex.ofReal_add,Complex.ofReal_mul]
    ring
  rw [hid]
  exact ((hx.const_mul ((a:ℂ)^2)).add (hy.const_mul ((b:ℂ)^2))).add
    (hxy.const_mul (2*(a:ℂ)*b))

lemma normalJointPast_linear_second {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ) :
    (∫ P, F (pairPastCoordinates v P)*(pairLinearIncrement a b s t P:ℂ)^2 ∂μ)=
      (((c:ℝ)*((t:ℝ)-s)*(a^2+b^2):ℝ):ℂ)*(∫ P, F (pairPastCoordinates v P) ∂μ)+
      2*(a:ℂ)*b*(∫ P, F (pairPastCoordinates v P)*
        ((pairPathIncrement false s t P*pairPathIncrement true s t P:ℝ):ℂ) ∂μ) := by
  have hx := normalJointPast_complex_weighted_moment_integrable (k := 2) μ c h v s t hst ht false F
  have hy := normalJointPast_complex_weighted_moment_integrable (k := 2) μ c h v s t hst ht true F
  have hxy := normalJointPast_complex_cross_integrable μ c h v s t hst ht F
  have hid : (fun P => F (pairPastCoordinates v P)*(pairLinearIncrement a b s t P:ℂ)^2)=
      (fun P => (a:ℂ)^2*(F (pairPastCoordinates v P)*(pairPathIncrement false s t P:ℂ)^2)+
        (b:ℂ)^2*(F (pairPastCoordinates v P)*(pairPathIncrement true s t P:ℂ)^2)+
        2*(a:ℂ)*b*(F (pairPastCoordinates v P)*
        ((pairPathIncrement false s t P*pairPathIncrement true s t P:ℝ):ℂ))) := by
    funext P
    simp only [pairLinearIncrement,ContinuousMap.coe_mk,Complex.ofReal_add,Complex.ofReal_mul]
    ring
  have hadd := integral_add ((hx.const_mul ((a:ℂ)^2)).add (hy.const_mul ((b:ℂ)^2)))
      (hxy.const_mul (2*(a:ℂ)*b))
  simp only [Pi.add_apply] at hadd
  rw [hid,hadd,
    integral_add (hx.const_mul ((a:ℂ)^2)) (hy.const_mul ((b:ℂ)^2)),integral_const_mul,integral_const_mul,integral_const_mul,
    normalJointPast_complex_second μ c h v s t hv hst ht false,
    normalJointPast_complex_second μ c h v s t hv hst ht true]
  push_cast
  ring

lemma normalJointPast_linear_absolute_third_bound
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    (s t : unitInterval) (hst : s < t) (ht : (t:ℝ) < 1) (a b : ℝ) :
    Integrable (fun P => |pairLinearIncrement a b s t P|^3) μ ∧
    (∫ P, |pairLinearIncrement a b s t P|^3 ∂μ) ≤
      8*(|a|+|b|)^3*(Real.sqrt ((c:ℝ)*((t:ℝ)-s)))^3*normalThirdMoment := by
  have hx := normalJointPast_integrable_abs_pow μ c h s t hst ht false 3
  have hy := normalJointPast_integrable_abs_pow μ c h s t hst ht true 3
  have hi := (hx.add hy).const_mul (4*(|a|+|b|)^3)
  have hb : ∀ P, |pairLinearIncrement a b s t P|^3 ≤
      4*(|a|+|b|)^3*(|pairPathIncrement false s t P|^3+|pairPathIncrement true s t P|^3) := by
    intro P
    exact abs_linear_cube_bound a b _ _
  have hI : Integrable (fun P => |pairLinearIncrement a b s t P|^3) μ := hi.mono (by fun_prop)
    (by filter_upwards [] with P
        change ‖|(pairLinearIncrement a b s t) P|^3‖ ≤
          ‖4*(|a|+|b|)^3*(|pairPathIncrement false s t P|^3+|pairPathIncrement true s t P|^3)‖
        simp only [norm_pow,Real.norm_eq_abs,abs_abs]
        exact (hb P).trans (le_abs_self _))
  refine ⟨hI,?_⟩
  calc
    _ ≤ ∫ P, 4*(|a|+|b|)^3*(|pairPathIncrement false s t P|^3+|pairPathIncrement true s t P|^3) ∂μ :=
      integral_mono hI hi hb
    _ = _ := by
      rw [integral_const_mul,integral_add hx hy,
        normalJointPast_absolute_third_moment μ c h s t hst ht false,
        normalJointPast_absolute_third_moment μ c h s t hst ht true]
      ring

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma pairPastTest_integrable {q : ℕ} (μ : Measure RealPathPair) [IsFiniteMeasure μ]
    (v : Fin q → unitInterval) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) :
    Integrable (fun P => F (pairPastCoordinates v P)) μ := by
  apply Integrable.of_bound (by fun_prop) ‖F‖
  filter_upwards [] with P
  exact F.norm_coe_le_norm _

lemma pairPastPhase_integrable {q : ℕ} (μ : Measure RealPathPair) [IsFiniteMeasure μ]
    (v : Fin q → unitInterval) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ) (s t : unitInterval) :
    Integrable (fun P => F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s t P)) μ := by
  apply Integrable.of_bound (by unfold charPhase; fun_prop) ‖F‖
  filter_upwards [] with P
  rw [norm_mul,charPhase_norm,mul_one]
  exact F.norm_coe_le_norm _

lemma normalJointPast_integral_quadratic {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ) :
    (∫ P, F (pairPastCoordinates v P)*(1+(pairLinearIncrement a b s t P:ℂ)*Complex.I-
      (pairLinearIncrement a b s t P:ℂ)^2/2) ∂μ)=
    (1-(((c:ℝ)*((t:ℝ)-s)*(a^2+b^2)/2:ℝ):ℂ))*(∫ P, F (pairPastCoordinates v P) ∂μ)-
    (a:ℂ)*b*(∫ P, F (pairPastCoordinates v P)*
        ((pairPathIncrement false s t P*pairPathIncrement true s t P:ℝ):ℂ) ∂μ) := by
  have h0 := pairPastTest_integrable μ v F
  have h1 := normalJointPast_linear_mean_integrable μ c h v s t hst ht F a b
  have h2 := normalJointPast_linear_second_integrable μ c h v s t hst ht F a b
  have hid : (fun P => F (pairPastCoordinates v P)*(1+(pairLinearIncrement a b s t P:ℂ)*Complex.I-
      (pairLinearIncrement a b s t P:ℂ)^2/2))=
      (fun P => F (pairPastCoordinates v P)+
        Complex.I*(F (pairPastCoordinates v P)*(pairLinearIncrement a b s t P:ℂ))-
        (1/2:ℂ)*(F (pairPastCoordinates v P)*(pairLinearIncrement a b s t P:ℂ)^2)) := by
    funext P; ring
  have hadd := integral_sub (h0.add (h1.const_mul Complex.I)) (h2.const_mul (1/2:ℂ))
  simp only [Pi.add_apply] at hadd
  rw [hid,hadd,integral_add h0 (h1.const_mul Complex.I),integral_const_mul,integral_const_mul,
    normalJointPast_linear_mean μ c h v s t hv hst ht F a b,
    normalJointPast_linear_second μ c h v s t hv hst ht F a b]
  push_cast
  ring

lemma normalJointPast_taylor_error {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ) :
    ‖(∫ P, F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s t P) ∂μ)-
      ((1-(((c:ℝ)*((t:ℝ)-s)*(a^2+b^2)/2:ℝ):ℂ))*(∫ P, F (pairPastCoordinates v P) ∂μ)-
      (a:ℂ)*b*(∫ P, F (pairPastCoordinates v P)*
        ((pairPathIncrement false s t P*pairPathIncrement true s t P:ℝ):ℂ) ∂μ))‖ ≤
      8*charTaylorConstant*‖F‖*(|a|+|b|)^3*
        (Real.sqrt ((c:ℝ)*((t:ℝ)-s)))^3*normalThirdMoment := by
  have h0 := pairPastTest_integrable μ v F
  have h1 := normalJointPast_linear_mean_integrable μ c h v s t hst ht F a b
  have h2 := normalJointPast_linear_second_integrable μ c h v s t hst ht F a b
  have hchar := pairPastPhase_integrable μ v F a b s t
  have hQ : Integrable (fun P => F (pairPastCoordinates v P)*(1+(pairLinearIncrement a b s t P:ℂ)*Complex.I-
      (pairLinearIncrement a b s t P:ℂ)^2/2)) μ := by
    have hid : (fun P => F (pairPastCoordinates v P)*(1+(pairLinearIncrement a b s t P:ℂ)*Complex.I-
      (pairLinearIncrement a b s t P:ℂ)^2/2))=
      (fun P => F (pairPastCoordinates v P)+
        Complex.I*(F (pairPastCoordinates v P)*(pairLinearIncrement a b s t P:ℂ))-
        (1/2:ℂ)*(F (pairPastCoordinates v P)*(pairLinearIncrement a b s t P:ℂ)^2)) := by
      funext P; ring
    rw [hid]
    exact (h0.add (h1.const_mul Complex.I)).sub (h2.const_mul (1/2:ℂ))
  rw [← normalJointPast_integral_quadratic μ c h v s t hv hst ht F a b,← integral_sub hchar hQ]
  have h3 := normalJointPast_linear_absolute_third_bound μ c h s t hst ht a b
  have hb : ∀ P, ‖F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s t P)-
      F (pairPastCoordinates v P)*(1+(pairLinearIncrement a b s t P:ℂ)*Complex.I-
      (pairLinearIncrement a b s t P:ℂ)^2/2)‖ ≤
      ‖F‖*charTaylorConstant*|pairLinearIncrement a b s t P|^3 := by
    intro P
    rw [← mul_sub,norm_mul]
    exact (mul_le_mul (F.norm_coe_le_norm _) (charPhase_quadratic_error _) (norm_nonneg _) (norm_nonneg F)).trans_eq (by ring)
  calc
    _ ≤ ∫ P, ‖F‖*charTaylorConstant*|pairLinearIncrement a b s t P|^3 ∂μ :=
      norm_integral_le_of_norm_le (h3.1.const_mul _) (ae_of_all _ hb)
    _ = ‖F‖*charTaylorConstant*(∫ P, |pairLinearIncrement a b s t P|^3 ∂μ) := integral_const_mul _ _
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left h3.2 (mul_nonneg (norm_nonneg F) charTaylorConstant_nonneg)
      nlinarith only [hh]

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_PastPhaseExtension
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma phaseAugmentedTest_norm {q : ℕ} (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ) :
    ‖phaseAugmentedTest F a b‖ ≤ ‖F‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr
  intro z
  change ‖F (fun i => z i.succ.succ)*charPhase _‖ ≤ ‖F‖
  rw [norm_mul,charPhase_norm,mul_one]
  exact F.norm_coe_le_norm _

lemma phaseAugmentedTest_eval {q : ℕ} (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ)
    (v : Fin q → unitInterval) (s u : unitInterval) (P : RealPathPair) :
    phaseAugmentedTest F a b (pairPastCoordinates (phaseAugmentedTimes v s u) P)=
      F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s u P) := by
  simp [phaseAugmentedTest,phaseAugmentedTimes,pairPastCoordinates,pairLinearIncrement,
    pairPathIncrement,Fin.cons_zero,Fin.cons_succ]

lemma phaseAugmentedTimes_le {q : ℕ} (v : Fin q → unitInterval) (s u : unitInterval)
    (hv : ∀ z,v z ≤ s) (hsu : s ≤ u) : ∀ z,phaseAugmentedTimes v s u z ≤ u := by
  intro z
  refine Fin.cases ?_ (fun z => ?_) z
  · exact le_rfl
  · refine Fin.cases ?_ (fun z => ?_) z
    · exact hsu
    · exact (hv z).trans hsu

lemma pairLinearIncrement_add (a b : ℝ) (s u t : unitInterval) (P : RealPathPair) :
    pairLinearIncrement a b s u P+pairLinearIncrement a b u t P=pairLinearIncrement a b s t P := by
  simp only [pairLinearIncrement,pairPathIncrement,ContinuousMap.coe_mk,Bool.false_eq_true,
    ↓reduceIte]
  ring

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma jointTaylorCoeff_nonneg (a b : ℝ) : 0 ≤ jointTaylorCoeff a b := by
  have hT := charTaylorConstant_nonneg
  have hM := normalThirdMoment_nonneg
  unfold jointTaylorCoeff
  positivity

lemma normalJointPast_phase_step {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    {A K : ℝ} (hK : 0 ≤ K) (hcross : SeparatedCrossBound μ A K)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ‖(∫ P, F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s t P) ∂μ)-
      (1-(((c:ℝ)*((t:ℝ)-s)*(a^2+b^2)/2:ℝ):ℂ))*(∫ P, F (pairPastCoordinates v P) ∂μ)‖ ≤
      ‖F‖*(2*|a*b| *K*Real.exp (-A*ρ^2/((t:ℝ)-s))+
        jointTaylorCoeff a b*(Real.sqrt ((c:ℝ)*((t:ℝ)-s)))^3+
        2*|a*b| *(c:ℝ)*((t:ℝ)-s)*(∫ P, nearDiagonalCutoff ρ (P.1 s-P.2 s) ∂μ)) := by
  have htay := normalJointPast_taylor_error μ c h v s t hv hst ht F a b
  have hcr := normalJointPast_complex_cross_bound μ c h hK hcross v s t hv hst ht F hρ
  let Z := ∫ P, F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s t P) ∂μ
  let W := (1-(((c:ℝ)*((t:ℝ)-s)*(a^2+b^2)/2:ℝ):ℂ))*(∫ P, F (pairPastCoordinates v P) ∂μ)
  let Q := ∫ P, F (pairPastCoordinates v P)*
        ((pairPathIncrement false s t P*pairPathIncrement true s t P:ℝ):ℂ) ∂μ
  have hid : Z-W=(Z-(W-(a:ℂ)*b*Q))-(a:ℂ)*b*Q := by ring
  change ‖Z-W‖ ≤ _
  rw [hid]
  have hn := norm_sub_le (Z-(W-(a:ℂ)*b*Q)) ((a:ℂ)*b*Q)
  have hm : ‖(a:ℂ)*b*Q‖=|a*b| *‖Q‖ := by
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul]
  rw [hm] at hn
  have hcr' := mul_le_mul_of_nonneg_left hcr (abs_nonneg (a*b))
  change ‖Z-(W-(a:ℂ)*b*Q)‖ ≤ _ at htay
  change |a*b| *‖Q‖ ≤ _ at hcr'
  unfold jointTaylorCoeff
  nlinarith only [hn,htay,hcr']

lemma normalJointPast_cumulative_phase_step {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    {A K : ℝ} (hK : 0 ≤ K) (hcross : SeparatedCrossBound μ A K)
    (v : Fin q → unitInterval) (s u t : unitInterval) (hv : ∀ z, v z ≤ s) (hsu : s ≤ u)
    (hut : u < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ‖(∫ P, F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s t P) ∂μ)-
      (1-(((c:ℝ)*((t:ℝ)-u)*(a^2+b^2)/2:ℝ):ℂ))*
      (∫ P, F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s u P) ∂μ)‖ ≤
      ‖F‖*(2*|a*b| *K*Real.exp (-A*ρ^2/((t:ℝ)-u))+
        jointTaylorCoeff a b*(Real.sqrt ((c:ℝ)*((t:ℝ)-u)))^3+
        2*|a*b| *(c:ℝ)*((t:ℝ)-u)*(∫ P, nearDiagonalCutoff ρ (P.1 u-P.2 u) ∂μ)) := by
  have hh := normalJointPast_phase_step μ c h hK hcross (phaseAugmentedTimes v s u) u t
    (phaseAugmentedTimes_le v s u hv hsu) hut ht (phaseAugmentedTest F a b) a b hρ
  simp only [phaseAugmentedTest_eval,mul_assoc,← charPhase_add,pairLinearIncrement_add] at hh
  have hpos : 0 ≤ 2*|a*b| *K*Real.exp (-A*ρ^2/((t:ℝ)-u))+
        jointTaylorCoeff a b*(Real.sqrt ((c:ℝ)*((t:ℝ)-u)))^3+
        2*|a*b| *(c:ℝ)*((t:ℝ)-u)*(∫ P : RealPathPair, nearDiagonalCutoff ρ (P.1 u-P.2 u) ∂μ) := by
    have hM := jointTaylorCoeff_nonneg a b
    have hd : 0 ≤ (t:ℝ)-u := sub_nonneg.mpr (show (u:ℝ) ≤ t from hut.le)
    have hi : 0 ≤ ∫ P : RealPathPair, nearDiagonalCutoff ρ (P.1 u-P.2 u) ∂μ :=
      integral_nonneg (fun P => (nearDiagonalCutoff_unit ρ _).1)
    positivity
  simpa only [mul_assoc] using hh.trans (by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (phaseAugmentedTest_norm F a b) hpos)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_JointMeshPhase
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma normalJointPast_mesh_phase_bound {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    {A K : ℝ} (hK : 0 ≤ K) (hcross : SeparatedCrossBound μ A K)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) {n : ℕ} (hn : 0 < n)
    (hnlarge : ((c:ℝ)*(a^2+b^2)/2)*(((t:ℝ)-s)/n) ≤ 1) :
    ‖(∫ P, F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s t P) ∂μ)-
      (1-((((c:ℝ)*(a^2+b^2)/2)*(((t:ℝ)-s)/n):ℝ):ℂ))^n*
        (∫ P, F (pairPastCoordinates v P) ∂μ)‖ ≤
      ‖F‖*(2*|a*b| *K*(n:ℝ)*Real.exp (-A*ρ^2/(((t:ℝ)-s)/n))+
        jointTaylorCoeff a b*(n:ℝ)*(Real.sqrt ((c:ℝ)*(((t:ℝ)-s)/n)))^3+
        2*|a*b| *(c:ℝ)*(∑ j ∈ Finset.range n, ((t:ℝ)-s)/n*
          cutoffMeanExtension μ ρ (realMesh s t n j))) := by
  let δ := ((t:ℝ)-s)/n
  let r : ℂ := 1-((((c:ℝ)*(a^2+b^2)/2)*δ:ℝ):ℂ)
  let z : ℕ → ℂ := fun j => ∫ P, F (pairPastCoordinates v P)*
      charPhase (pairLinearIncrement a b s (unitMesh s t n j) P) ∂μ
  let D := 2*|a*b| *K*Real.exp (-A*ρ^2/δ)+jointTaylorCoeff a b*(Real.sqrt ((c:ℝ)*δ))^3
  let C := 2*|a*b| *(c:ℝ)
  let e : ℕ → ℝ := fun j => ‖F‖*(D+C*δ*cutoffMeanExtension μ ρ (realMesh s t n j))
  have hz0 : z 0=∫ P, F (pairPastCoordinates v P) ∂μ := by
    dsimp [z]
    rw [unitMesh_zero]
    simp only [pairLinearIncrement,pairPathIncrement,ContinuousMap.coe_mk,Bool.false_eq_true,
      ↓reduceIte,sub_self,mul_zero,add_zero,charPhase,Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one]
  have hzn : z n=∫ P, F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s t P) ∂μ := by
    simp only [z,unitMesh_last s t hn]
  have hδ : 0 ≤ δ := div_nonneg (sub_nonneg.mpr (show (s:ℝ) ≤ t from hst.le)) (Nat.cast_nonneg n)
  have hc : 0 ≤ (c:ℝ)*(a^2+b^2)/2 := by positivity
  have hr : ‖r‖ ≤ 1 := realEulerCoefficient_norm hc hδ hnlarge
  have he : ∀ j < n, ‖z (j+1)-r*z j‖ ≤ e j := by
    intro j hj
    have hju := unitMesh_between s t hst.le hn hj.le
    have hjv := unitMesh_between s t hst.le hn (Nat.succ_le_of_lt hj)
    have hh := normalJointPast_cumulative_phase_step μ c h hK hcross v s
      (unitMesh s t n j) (unitMesh s t n (j+1)) hv hju.1
      (unitMesh_step_lt s t hst hn hj) (lt_of_le_of_lt hjv.2 ht) F a b hρ
    rw [unitMesh_sub s t hst.le hn hj] at hh
    have hcoef : 1-((((c:ℝ)*δ*(a^2+b^2)/2):ℝ):ℂ)=r := by
      dsimp [r]
      congr 1
      ring_nf
    change ‖z (j+1)-(1-((((c:ℝ)*δ*(a^2+b^2)/2):ℝ):ℂ))*z j‖ ≤ _ at hh
    rw [hcoef] at hh
    have hcut : (∫ P : RealPathPair, nearDiagonalCutoff ρ
      (P.1 (unitMesh s t n j)-P.2 (unitMesh s t n j)) ∂μ)=
      cutoffMeanExtension μ ρ (realMesh s t n j) := rfl
    rw [hcut] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
  have hh := contraction_recurrence_error z r e n hr he
  rw [hz0,hzn] at hh
  calc
    _ ≤ ∑ j ∈ Finset.range n, e j := hh
    _ = _ := by
      simp only [e,mul_add,Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
        Finset.card_range,nsmul_eq_mul]
      dsimp [D,C,δ]
      ring

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma complexEuler_tendsto (lam L : ℝ) :
    Tendsto (fun n : ℕ => (1-((lam*(L/n):ℝ):ℂ))^n) atTop
      (𝓝 (Complex.exp ((-lam*L:ℝ):ℂ))) := by
  convert Complex.tendsto_one_add_div_pow_exp (((-lam*L:ℝ):ℂ)) using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  congr 1
  push_cast
  ring

lemma normalJointPast_phase_bound {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    {A K : ℝ} (hA : 0 < A) (hK : 0 ≤ K) (hcross : SeparatedCrossBound μ A K)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ‖(∫ P, F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s t P) ∂μ)-
      Complex.exp ((-((c:ℝ)*(a^2+b^2)/2)*((t:ℝ)-s):ℝ):ℂ)*
        (∫ P, F (pairPastCoordinates v P) ∂μ)‖ ≤
      ‖F‖*(2*|a*b| *(c:ℝ)*(∫ u in (s:ℝ)..t, cutoffMeanExtension μ ρ u)) := by
  let lam := (c:ℝ)*(a^2+b^2)/2
  let L := (t:ℝ)-s
  have hL : 0 < L := sub_pos.mpr hst
  have hEu := complexEuler_tendsto lam L
  have hleft := ((tendsto_const_nhds.sub (hEu.mul_const
    (∫ P, F (pairPastCoordinates v P) ∂μ))).norm :
    Tendsto (fun n : ℕ => ‖(∫ P, F (pairPastCoordinates v P)*
      charPhase (pairLinearIncrement a b s t P) ∂μ)-
      (1-((lam*(L/n):ℝ):ℂ))^n*(∫ P, F (pairPastCoordinates v P) ∂μ)‖) atTop
      (𝓝 ‖(∫ P, F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s t P) ∂μ)-
      Complex.exp ((-lam*L:ℝ):ℂ)*(∫ P, F (pairPastCoordinates v P) ∂μ)‖))
  have hex := (scaled_exp_tendsto_zero (mul_pos hA (sq_pos_of_pos hρ)) hL).const_mul (2*|a*b| *K)
  have hcu := (scaled_sqrt_cube_tendsto_zero c.coe_nonneg hL.le).const_mul (jointTaylorCoeff a b)
  have hri := (cutoff_riemann_tendsto μ ρ hst).const_mul (2*|a*b| *(c:ℝ))
  have hr := ((hex.add hcu).add hri).const_mul ‖F‖
  simp only [mul_zero,zero_add] at hr
  have hnlarge : ∀ᶠ n : ℕ in atTop, lam*(L/n) ≤ 1 := by
    have hh : Tendsto (fun n : ℕ => lam*(L/n)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => L/(n:ℝ)) atTop (𝓝 0)).const_mul lam
    exact (hh.eventually_lt_const zero_lt_one).mono (fun n hn => hn.le)
  apply le_of_tendsto_of_tendsto hleft hr
  filter_upwards [eventually_gt_atTop 0,hnlarge] with n hn hnl
  have hh := normalJointPast_mesh_phase_bound μ c h hK hcross v s t hv hst ht F a b hρ hn hnl
  simpa only [lam,L,neg_mul,mul_assoc] using hh

lemma normalJointPast_joint_characteristic {q : ℕ}
    (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    {A K : ℝ} (hA : 0 < A) (hK : 0 ≤ K) (hcross : SeparatedCrossBound μ A K)
    (hz : (μ.prod volume) {z : RealPathPair × unitInterval | z.1.1 z.2-z.1.2 z.2=0}=0)
    (v : Fin q → unitInterval) (s t : unitInterval) (hv : ∀ z, v z ≤ s)
    (hst : s < t) (ht : (t:ℝ) < 1) (F : (Fin q → ℝ × ℝ) →ᵇ ℂ) (a b : ℝ) :
    (∫ P, F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s t P) ∂μ)=
      Complex.exp ((-((c:ℝ)*(a^2+b^2)/2)*((t:ℝ)-s):ℝ):ℂ)*
        (∫ P, F (pairPastCoordinates v P) ∂μ) := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  have hh := ((diagonal_zero_subinterval_cutoff_tendsto μ hz s t hst.le).const_mul
    (2*|a*b| *(c:ℝ))).const_mul ‖F‖
  simp only [mul_zero] at hh
  apply ge_of_tendsto hh
  filter_upwards [] with n
  exact normalJointPast_phase_bound μ c h hA hK hcross v s t hv hst ht F a b
    (by positivity : 0 < 1/((n:ℝ)+1))

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_CharacteristicProductLaw
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma real_linear_apply (L : ℝ →L[ℝ] ℝ) (x : ℝ) : L x=L 1*x := by
  have h := L.map_smul x (1:ℝ)
  simpa [smul_eq_mul,mul_comm] using h

lemma charFunDual_gaussianReal (v : ℝ≥0) (L : ℝ →L[ℝ] ℝ) :
    charFunDual (gaussianReal 0 v) L=Complex.exp ((-(v:ℝ)*(L 1)^2/2:ℝ):ℂ) := by
  have hid : charFunDual (gaussianReal 0 v) L=charFun (gaussianReal 0 v) (L 1) := by
    rw [charFunDual_apply,charFun_apply_real]
    congr 1
    funext x
    rw [real_linear_apply L x,Complex.ofReal_mul]
  rw [hid,charFun_gaussianReal]
  congr 1
  push_cast
  ring

lemma product_linear_split {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E × (ℝ × ℝ) →L[ℝ] ℝ) (z : E) (x y : ℝ) :
    L (z,(x,y))=L (z,0)+L (0,(1,0))*x+L (0,(0,1))*y := by
  have hid : (z,(x,y))=(z,0)+x • (0,(1,0))+y • (0,(0,1)) := by ext <;> simp
  rw [hid,map_add,map_add,map_smul,map_smul]
  simp only [smul_eq_mul]
  ring

lemma product_normal_law_of_characteristics {Ω E : Type*}
    [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (v : ℝ≥0)
    (Z : Ω → E) (X Y : Ω → ℝ) (hZ : Measurable Z) (hX : Measurable X) (hY : Measurable Y)
    (h : ∀ (F : E →ᵇ ℂ) (a b : ℝ),
       (∫ ω, F (Z ω)*charPhase (a*X ω+b*Y ω) ∂μ)=
       Complex.exp ((-(v:ℝ)*(a^2+b^2)/2:ℝ):ℂ)*(∫ ω, F (Z ω) ∂μ)) :
    μ.map (fun ω => (Z ω,(X ω,Y ω)))=(μ.map Z).prod ((gaussianReal 0 v).prod (gaussianReal 0 v)) := by
  have hm := hZ.prodMk (hX.prodMk hY)
  have : IsProbabilityMeasure (μ.map Z) :=
    (Measure.isProbabilityMeasure_map_iff hZ.aemeasurable).mpr inferInstance
  have : IsProbabilityMeasure (μ.map (fun ω => (Z ω,(X ω,Y ω)))) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_prod,charFunDual_prod,charFunDual_gaussianReal,charFunDual_gaussianReal]
  let L0 : E →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inl ℝ E (ℝ × ℝ))
  let a := L (0,(1,0))
  let b := L (0,(0,1))
  have hleft : charFunDual (μ.map (fun ω => (Z ω,(X ω,Y ω)))) L=
      ∫ ω, linearPhaseTest L0 (Z ω)*charPhase (a*X ω+b*Y ω) ∂μ := by
    rw [charFunDual_apply,integral_map hm.aemeasurable (by fun_prop)]
    congr 1
    funext ω
    rw [product_linear_split,show L (0,(1,0))=a from rfl,show L (0,(0,1))=b from rfl]
    change charPhase (L (Z ω,0)+a*X ω+b*Y ω)=charPhase (L (Z ω,0))*charPhase (a*X ω+b*Y ω)
    rw [add_assoc,charPhase_add]
  rw [hleft,h]
  have hi : charFunDual (μ.map Z) L0=∫ ω, linearPhaseTest L0 (Z ω) ∂μ := by
    rw [charFunDual_apply,integral_map hZ.aemeasurable (by fun_prop)]
    rfl
  change _=charFunDual (μ.map Z) L0*(Complex.exp ((-(v:ℝ)*a^2/2:ℝ):ℂ)*
    Complex.exp ((-(v:ℝ)*b^2/2:ℝ):ℂ))
  rw [hi,← Complex.exp_add]
  have hex : ((-(v:ℝ)*a^2/2:ℝ):ℂ)+((-(v:ℝ)*b^2/2:ℝ):ℂ)=
      ((-(v:ℝ)*(a^2+b^2)/2:ℝ):ℂ) := by push_cast <;> ring
  rw [hex,mul_comm]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma fullNormalJointPast_of_cross (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) {A K : ℝ} (hA : 0 < A) (hK : 0 ≤ K)
    (hcross : SeparatedCrossBound μ A K)
    (hz : (μ.prod volume) {z : RealPathPair × unitInterval | z.1.1 z.2-z.1.2 z.2=0}=0) :
    FullNormalJointPast μ c := by
  intro q v s t hv hst ht
  apply product_normal_law_of_characteristics μ _ (pairPastCoordinates v)
    (pairPathIncrement false s t) (pairPathIncrement true s t) (by fun_prop) (by fun_prop) (by fun_prop)
  intro F a b
  have hh := normalJointPast_joint_characteristic μ c h hA hK hcross hz v s t hv hst ht F a b
  change (∫ P, F (pairPastCoordinates v P)*charPhase (pairLinearIncrement a b s t P) ∂μ)=_
  rw [hh]
  congr 2
  rw [NNReal.coe_mul,Real.toNNReal_of_nonneg (sub_nonneg.mpr (show (s:ℝ) ≤ t from hst.le))]
  congr 1
  simp only [NNReal.coe_mk]
  ring

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DirectionalTransience

lemma measure_prod_shuffle {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology E] [SecondCountableTopology F]
    [SecondCountableTopology G] [SecondCountableTopology H]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure E) (ν : Measure F) (γ : Measure G) (δ : Measure H)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure γ] [IsFiniteMeasure δ] :
    ((μ.prod ν).prod (γ.prod δ)).map (fun z => ((z.1.1,z.2.1),(z.1.2,z.2.2)))=
      (μ.prod γ).prod (ν.prod δ) := by
  let S := (ContinuousLinearEquiv.prodProdProdComm ℝ E F G H).toContinuousLinearMap
  change (((μ.prod ν).prod (γ.prod δ)).map S)=(μ.prod γ).prod (ν.prod δ)
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map]
  simp only [charFunDual_prod]
  have hE : ((L.comp S).comp (ContinuousLinearMap.inl ℝ (E × F) (G × H))).comp
      (ContinuousLinearMap.inl ℝ E F)=
      (L.comp (ContinuousLinearMap.inl ℝ (E × G) (F × H))).comp (ContinuousLinearMap.inl ℝ E G) := by ext x; rfl
  have hF : ((L.comp S).comp (ContinuousLinearMap.inl ℝ (E × F) (G × H))).comp
      (ContinuousLinearMap.inr ℝ E F)=
      (L.comp (ContinuousLinearMap.inr ℝ (E × G) (F × H))).comp (ContinuousLinearMap.inl ℝ F H) := by ext x; rfl
  have hG : ((L.comp S).comp (ContinuousLinearMap.inr ℝ (E × F) (G × H))).comp
      (ContinuousLinearMap.inl ℝ G H)=
      (L.comp (ContinuousLinearMap.inl ℝ (E × G) (F × H))).comp (ContinuousLinearMap.inr ℝ E G) := by ext x; rfl
  have hH : ((L.comp S).comp (ContinuousLinearMap.inr ℝ (E × F) (G × H))).comp
      (ContinuousLinearMap.inr ℝ G H)=
      (L.comp (ContinuousLinearMap.inr ℝ (E × G) (F × H))).comp (ContinuousLinearMap.inr ℝ F H) := by ext x; rfl
  rw [hE,hF,hG,hH]
  ring

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_ProductNormalJointPast
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma normalJointPast_single (μ : Measure RealPathPair) [IsProbabilityMeasure μ] (c : ℝ≥0) (h : NormalJointPast μ c)
    (b : Bool) : NormalSinglePast (μ.map (fun P => if b then P.2 else P.1)) c := by
  intro q v s t hv hst ht
  let g := fun z : Fin q → ℝ × ℝ => fun j => if b then (z j).2 else (z j).1
  have hg : Measurable g := by cases b <;> simp [g] <;> fun_prop
  have hh := congrArg (fun M => M.map (Prod.map g id)) (h q v s t hv hst ht b)
  rw [Measure.map_map (hg.prodMap measurable_id) (by fun_prop),
    ← Measure.map_prod_map _ _ hg measurable_id,Measure.map_id,
    Measure.map_map hg (by fun_prop)] at hh
  rw [Measure.map_map (by fun_prop) (by cases b <;> simp <;> fun_prop),
    Measure.map_map (by fun_prop) (by cases b <;> simp <;> fun_prop)]
  cases b <;> exact hh

lemma normalSinglePast_prod (μ ν : Measure C(unitInterval,ℝ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (c : ℝ≥0)
    (hμ : NormalSinglePast μ c) (hν : NormalSinglePast ν c) : FullNormalJointPast (μ.prod ν) c := by
  intro q v s t hv hst ht
  let Z := fun P : C(unitInterval,ℝ) => (pathPastCoordinates v P,pathIncrement s t P)
  have hZ : Measurable Z := by fun_prop
  let γ := gaussianReal 0 (c*Real.toNNReal ((t:ℝ)-s))
  let Q := fun z : ((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ) => ((z.1.1,z.2.1),(z.1.2,z.2.2))
  have hQ : Measurable Q := by fun_prop
  let zip := fun z : (Fin q → ℝ) × (Fin q → ℝ) => fun j => (z.1 j,z.2 j)
  have hzip : Measurable zip := by fun_prop
  have hh : ((μ.prod ν).map (Prod.map Z Z)).map Q =
      ((μ.map (pathPastCoordinates v)).prod (ν.map (pathPastCoordinates v))).prod (γ.prod γ) := by
    rw [← Measure.map_prod_map _ _ hZ hZ,hμ q v s t hv hst ht,hν q v s t hv hst ht]
    exact measure_prod_shuffle _ _ _ _
  have he := congrArg (fun M => M.map (Prod.map zip id)) hh
  rw [Measure.map_map (hzip.prodMap measurable_id) hQ,
    Measure.map_map ((hzip.prodMap measurable_id).comp hQ) (hZ.prodMap hZ),
    ← Measure.map_prod_map _ _ hzip measurable_id,Measure.map_id,
    Measure.map_prod_map _ _ (pathPastCoordinates v).continuous.measurable (pathPastCoordinates v).continuous.measurable,
    Measure.map_map hzip (by fun_prop)] at he
  exact he

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma fullNormalJointPast_finset (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : FullNormalJointPast μ c) (I : Finset unitInterval)
    (s t : unitInterval) (hv : ∀ z ∈ I,z ≤ s) (hst : s < t) (ht : (t:ℝ) < 1) :
    μ.map (fun P => (pairRestricted I P,pairIncrement s t P))=
      (μ.map (pairRestricted I)).prod
        ((gaussianReal 0 (c*Real.toNNReal ((t:ℝ)-s))).prod
         (gaussianReal 0 (c*Real.toNNReal ((t:ℝ)-s)))) := by
  let e := Fintype.equivFin I
  let v := fun j : Fin (Fintype.card I) => ((e.symm j:I):unitInterval)
  let g := fun z : Fin (Fintype.card I) → ℝ × ℝ => fun j : I => z (e j)
  have hg : Measurable g := by fun_prop
  have hh := h (Fintype.card I) v s t (fun j => hv _ (e.symm j).property) hst ht
  have hh' := congrArg (fun M => M.map (Prod.map g id)) hh
  rw [Measure.map_map (hg.prodMap measurable_id) (by fun_prop),← Measure.map_prod_map _ _ hg measurable_id,
    Measure.map_id,Measure.map_map hg (by fun_prop)] at hh'
  convert hh' using 1
  · congr 1
    funext P
    apply Prod.ext
    · funext j
      simp [g,v,e,pairRestricted,pairPastCoordinates]
    · rfl
  · congr 2
    funext P j
    simp [g,v,e,pairRestricted,pairPastCoordinates]

lemma pairRestricted_empty_map (μ : Measure RealPathPair) [IsProbabilityMeasure μ] :
    μ.map (pairRestricted ∅)=Measure.dirac 0 := by
  have he : (pairRestricted ∅ : RealPathPair → (∅ : Finset unitInterval) → ℝ × ℝ)=fun _ => 0 := by
    funext P z
    exact False.elim (Finset.notMem_empty _ z.property)
  rw [he,Measure.map_const,measure_univ,one_smul]

lemma pairRestricted_singleton_zero_map (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (hzero : ∀ᵐ P ∂μ, P.1 0=0 ∧ P.2 0=0) :
    μ.map (pairRestricted {0})=Measure.dirac 0 := by
  have he : (pairRestricted {0} : RealPathPair → ({0} : Finset unitInterval) → ℝ × ℝ)=ᵐ[μ] fun _ => 0 := by
    filter_upwards [hzero] with P hP
    funext z
    have hz : z.val=0 := Finset.mem_singleton.mp z.property
    simp [pairRestricted,hz,hP.1,hP.2]
  rw [Measure.map_congr he,Measure.map_const,measure_univ,one_smul]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma pairRestricted_mono_eq (μ ν : Measure RealPathPair) {I J : Finset unitInterval}
    (hIJ : I ⊆ J) (h : μ.map (pairRestricted J)=ν.map (pairRestricted J)) :
    μ.map (pairRestricted I)=ν.map (pairRestricted I) := by
  let g := fun z : J → ℝ × ℝ => fun i : I => z ⟨i,hIJ i.property⟩
  have hg : Measurable g := by fun_prop
  have hh := congrArg (fun M => M.map g) h
  rw [Measure.map_map hg (pairRestricted J).continuous.measurable,
    Measure.map_map hg (pairRestricted J).continuous.measurable] at hh
  exact hh

lemma pairExtend_measurable (I : Finset unitInterval) (t s : unitInterval) (hs : s ∈ I) :
    Measurable (pairExtend I t s hs) := by
  apply Measurable.of_eval
  intro j
  by_cases h : j.val=t <;> simp [pairExtend,h] <;> fun_prop

lemma pairExtend_eval (I : Finset unitInterval) (t s : unitInterval) (hs : s ∈ I) (P : RealPathPair) :
    pairExtend I t s hs (pairRestricted I P,pairIncrement s t P)=pairRestricted (insert t I) P := by
  funext j
  by_cases h : j.val=t
  · simp [pairExtend,h,pairRestricted,pairIncrement]
  · simp [pairExtend,h,pairRestricted]

lemma pairRestricted_insert_eq (μ ν : Measure RealPathPair)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (c : ℝ≥0)
    (hμ : FullNormalJointPast μ c) (hν : FullNormalJointPast ν c)
    (I : Finset unitInterval) (t s : unitInterval) (hs : s ∈ I)
    (hIs : ∀ z ∈ I,z ≤ s) (hst : s < t) (ht : (t:ℝ) < 1)
    (hI : μ.map (pairRestricted I)=ν.map (pairRestricted I)) :
    μ.map (pairRestricted (insert t I))=ν.map (pairRestricted (insert t I)) := by
  have hm := fullNormalJointPast_finset μ c hμ I s t hIs hst ht
  have hn := fullNormalJointPast_finset ν c hν I s t hIs hst ht
  rw [hI] at hm
  have he := hm.trans hn.symm
  have he' := congrArg (fun M => M.map (pairExtend I t s hs)) he
  rw [Measure.map_map (pairExtend_measurable I t s hs) (by fun_prop),
    Measure.map_map (pairExtend_measurable I t s hs) (by fun_prop)] at he'
  simpa only [Function.comp_def,pairExtend_eval] using he'

lemma fullNormalJointPast_finite_uniqueness (μ ν : Measure RealPathPair)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (c : ℝ≥0)
    (hμ : FullNormalJointPast μ c) (hν : FullNormalJointPast ν c)
    (hμ0 : ∀ᵐ P ∂μ, P.1 0=0 ∧ P.2 0=0) (hν0 : ∀ᵐ P ∂ν, P.1 0=0 ∧ P.2 0=0)
    (I : Finset unitInterval) (hI : ∀ z ∈ I,(z:ℝ) < 1) :
    μ.map (pairRestricted I)=ν.map (pairRestricted I) := by
  have hz : μ.map (pairRestricted {0})=ν.map (pairRestricted {0}) := by
    rw [pairRestricted_singleton_zero_map μ hμ0,pairRestricted_singleton_zero_map ν hν0]
  induction I using Finset.induction_on_max with
  | empty => rw [pairRestricted_empty_map,pairRestricted_empty_map]
  | insert t I hlt ih =>
    have ht : (t:ℝ) < 1 := hI t (Finset.mem_insert_self _ _)
    have hIp : ∀ z ∈ I,(z:ℝ) < 1 := fun z hz => hI z (Finset.mem_insert_of_mem hz)
    rcases I.eq_empty_or_nonempty with he | he
    · subst I
      simp only [Finset.insert_empty]
      by_cases ht0 : t=0
      · subst t
        exact hz
      · have h0t : (0:unitInterval) < t := lt_of_le_of_ne (show (0:unitInterval) ≤ t from t.property.1) (Ne.symm ht0)
        have hh := pairRestricted_insert_eq μ ν c hμ hν {0} t 0 (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
          (by intro z hz; rw [Finset.mem_singleton.mp hz]) h0t ht hz
        apply pairRestricted_mono_eq μ ν (J := insert t {0}) (by intro z hz; simp_all)
        exact hh
    · apply pairRestricted_insert_eq μ ν c hμ hν I t (I.max' he) (Finset.max'_mem I he)
        (fun z hz => Finset.le_max' I z hz) (hlt _ (Finset.max'_mem I he)) ht
      exact ih hIp

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Estimates_InteriorPairMeasureExt
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma shrinkTime_lt_one (n : ℕ) (t : unitInterval) : (shrinkTime n t:ℝ) < 1 := by
  have hn : 0 ≤ ((n:ℝ)+1)/((n:ℝ)+2) := by positivity
  have hlt : ((n:ℝ)+1)/((n:ℝ)+2) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  exact (mul_le_mul_of_nonneg_left t.property.2 hn).trans_lt (by simpa using hlt)

lemma shrinkTime_tendsto (t : unitInterval) : Tendsto (fun n => shrinkTime n t) atTop (𝓝 t) := by
  have hh : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  apply tendsto_subtype_rng.mpr
  have hc := ((tendsto_const_nhds (x := (1:ℝ))).sub hh).mul_const (t:ℝ)
  simp only [sub_zero,one_mul] at hc
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  change ((n:ℝ)+1)/((n:ℝ)+2)*(t:ℝ)=(1-1/((n:ℝ)+2))*(t:ℝ)
  field_simp
  ring

lemma interior_pair_measure_ext (μ ν : Measure RealPathPair)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ I : Finset unitInterval, (∀ t ∈ I,(t:ℝ) < 1) →
      μ.map (pairRestricted I)=ν.map (pairRestricted I)) : μ=ν := by
  let e := TopologicalSpace.denseSeq unitInterval
  let f := fun j : ℕ × ℕ => shrinkTime j.2 (e j.1)
  let E := fun P : RealPathPair => fun j : ℕ × ℕ => (P.1 (f j),P.2 (f j))
  have hE : Continuous E := by fun_prop
  have hEinj : Function.Injective E := by
    intro P Q hPQ
    have hcoord (n : ℕ) : (P.1 (e n),P.2 (e n))=(Q.1 (e n),Q.2 (e n)) := by
      have hp : Tendsto (fun m => (P.1 (shrinkTime m (e n)),P.2 (shrinkTime m (e n)))) atTop
          (𝓝 (P.1 (e n),P.2 (e n))) :=
        ((P.1.continuous.prodMk P.2.continuous).tendsto (e n)).comp (shrinkTime_tendsto (e n))
      have hq : Tendsto (fun m => (Q.1 (shrinkTime m (e n)),Q.2 (shrinkTime m (e n)))) atTop
          (𝓝 (Q.1 (e n),Q.2 (e n))) :=
        ((Q.1.continuous.prodMk Q.2.continuous).tendsto (e n)).comp (shrinkTime_tendsto (e n))
      apply tendsto_nhds_unique hp
      apply hq.congr
      intro m
      exact (congrFun hPQ (n,m)).symm
    apply Prod.ext
    · apply ContinuousMap.coe_injective
      exact (TopologicalSpace.denseRange_denseSeq unitInterval).equalizer P.1.continuous Q.1.continuous
        (funext fun n => congrArg Prod.fst (hcoord n))
    · apply ContinuousMap.coe_injective
      exact (TopologicalSpace.denseRange_denseSeq unitInterval).equalizer P.2.continuous Q.2.continuous
        (funext fun n => congrArg Prod.snd (hcoord n))
  apply hE.measurableEmbedding hEinj |>.map_injective
  let P := fun J : Finset (ℕ × ℕ) => (μ.map E).map J.restrict
  have : ∀ J, IsFiniteMeasure (P J) := fun _ => inferInstance
  apply IsProjectiveLimit.unique (P := P) (fun _ => rfl)
  intro J
  let I := J.image f
  let g := fun z : I → ℝ × ℝ => fun j : J => z ⟨f j,Finset.mem_image_of_mem f j.property⟩
  have hg : Measurable g := by fun_prop
  have hm : Measurable (J.restrict : ((ℕ × ℕ) → ℝ × ℝ) → (J → ℝ × ℝ)) := by fun_prop
  change (ν.map E).map J.restrict=(μ.map E).map J.restrict
  rw [Measure.map_map hm hE.measurable,Measure.map_map hm hE.measurable]
  have he : J.restrict ∘ E=g ∘ pairRestricted I := rfl
  rw [he,← Measure.map_map hg (pairRestricted I).continuous.measurable,
    ← Measure.map_map hg (pairRestricted I).continuous.measurable,h I]
  intro t ht
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ht
  exact shrinkTime_lt_one j.2 (e j.1)

end DirectionalTransience

end

end

end OAI
end

section
-- module Solutions.OAIQ242_BAL.Ballisticity_Walk_JointPathIndependence
attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.row_compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma probability_prod_initial_zero (μ ν : Measure C(unitInterval,ℝ))
    (hμ : ∀ᵐ P ∂μ,P 0=0) (hν : ∀ᵐ P ∂ν,P 0=0) [SFinite ν] :
    ∀ᵐ P : RealPathPair ∂μ.prod ν,P.1 0=0 ∧ P.2 0=0 := by
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [hμ] with P hP
  filter_upwards [hν] with Q hQ
  exact ⟨hP,hQ⟩

lemma normalJointPast_product_identification_oai (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    (c : ℝ≥0) (h : NormalJointPast μ c) {A K : ℝ} (hA : 0 < A) (hK : 0 ≤ K)
    (hcross : SeparatedCrossBound μ A K)
    (hz : (μ.prod volume) {z : RealPathPair × unitInterval | z.1.1 z.2-z.1.2 z.2=0}=0)
    (hzero : ∀ᵐ P ∂μ,P.1 0=0 ∧ P.2 0=0) :
    μ=(μ.map Prod.fst).prod (μ.map Prod.snd) := by
  let : IsProbabilityMeasure (μ.map Prod.fst) := by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let : IsProbabilityMeasure (μ.map Prod.snd) := by first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hf : NormalSinglePast (μ.map Prod.fst) c := normalJointPast_single μ c h false
  have hg : NormalSinglePast (μ.map Prod.snd) c := normalJointPast_single μ c h true
  have h0f : ∀ᵐ P ∂μ.map Prod.fst,P 0=0 := by
    rw [ae_map_iff measurable_fst.aemeasurable ((isClosed_eq (continuous_eval_const 0) continuous_const).measurableSet)]
    exact hzero.mono fun P hP => hP.1
  have h0g : ∀ᵐ P ∂μ.map Prod.snd,P 0=0 := by
    rw [ae_map_iff measurable_snd.aemeasurable ((isClosed_eq (continuous_eval_const 0) continuous_const).measurableSet)]
    exact hzero.mono fun P hP => hP.2
  have hfull := fullNormalJointPast_of_cross μ c h hA hK hcross hz
  have hprod := normalSinglePast_prod (μ.map Prod.fst) (μ.map Prod.snd) c hf hg
  apply interior_pair_measure_ext
  intro I hI
  exact fullNormalJointPast_finite_uniqueness μ _ c hfull hprod hzero
    (probability_prod_initial_zero _ _ h0f h0g) I hI

end DirectionalTransience

end

end

end OAI
end

theorem solution : type_of% @OAI.DirectionalTransience.normalJointPast_product_identification_oai := @OAI.DirectionalTransience.normalJointPast_product_identification_oai
