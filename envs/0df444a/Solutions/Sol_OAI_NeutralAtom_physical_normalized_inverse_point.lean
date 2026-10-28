-- Prove2me | solution 1 for OAI.NeutralAtom.physical_normalized_inverse_point
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:34:53.087918+00:00
-- url     : https://prove2.me/submissions/ffd99d68-6e18-416b-b571-d4d43e3e13e4

import Mathlib
import Definitions.Def_CoulombRadii
import Definitions.Def_OAIQ062C008
import Theorems.Thm_OAI_NeutralAtom_arrayEvent_fresh_field_means
import Theorems.Thm_OAI_NeutralAtom_physical_retained_master_fresh_transfer

section
-- module Solutions.OAIQ062_CR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_ExplicitMultiplyGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

open scoped ENNReal Convolution

theorem observationNoiseDensity_contDiff : ContDiff ℝ ∞ observationNoiseDensity :=
  contDiff_const.mul observationNoiseBase_contDiff

theorem observationNoiseDensity_formula (u : ℝ) :
    observationNoiseDensity u = observationNoiseNormalizer*
      (if |u| < 1 then Real.exp (-(1-u^2)⁻¹) else 0) := by
  rw [observationNoiseDensity, observationNoiseBase_formula]

theorem observationNoiseDensity_even (u : ℝ) :
    observationNoiseDensity (-u) = observationNoiseDensity u := by
  simp [observationNoiseDensity, observationNoiseBase]

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_SignAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
open scoped ENNReal Convolution

open scoped BigOperators

instance observationNoiseLaw_negInvariant : observationNoiseLaw.IsNegInvariant := by
  constructor
  ext s hs
  change (Measure.map (fun u : ℝ => -u) observationNoiseLaw) s = observationNoiseLaw s
  rw [Measure.map_apply measurable_neg hs]
  unfold observationNoiseLaw
  rw [withDensity_apply _ (measurable_neg hs), withDensity_apply _ hs,
    ← lintegral_indicator (measurable_neg hs), ← lintegral_indicator hs]
  have h := lintegral_neg_eq_self (μ := (volume : Measure ℝ))
    (s.indicator (fun u => ENNReal.ofReal (observationNoiseDensity u)))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext u
  classical
  by_cases hu : -u ∈ s <;> simp [hu, observationNoiseDensity_even]

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservationProductDensity
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
open scoped ENNReal Convolution
open scoped BigOperators

open scoped Convolution

theorem observationProductDensity_nonneg {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    0 ≤ observationProductDensity u :=
  Finset.prod_nonneg (fun _i _ => observationNoiseDensity_nonneg _)

theorem observationProductDensity_contDiff {ι : Type*} [Fintype ι] :
    ContDiff ℝ ∞ (@observationProductDensity ι _) := by
  unfold observationProductDensity
  have h := observationNoiseDensity_contDiff
  fun_prop

theorem observationProductDensity_compact {ι : Type*} [Fintype ι] :
    HasCompactSupport (@observationProductDensity ι _) := by
  classical
  apply HasCompactSupport.intro
    (isCompact_pi_infinite (fun _ : ι => (isCompact_Icc : IsCompact (Set.Icc (-1:ℝ) 1))))
  intro u hu
  simp only [Set.mem_ofPred_eq, not_forall] at hu
  obtain ⟨i, hi⟩ := hu
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [observationNoiseDensity_formula, ite_eq_right, mul_zero]
  intro hh
  exact hi ⟨(abs_lt.mp hh).1.le, (abs_lt.mp hh).2.le⟩

theorem observationProductDensity_integrable {ι : Type*} [Fintype ι] :
    Integrable (@observationProductDensity ι _) :=
  Integrable.fintype_prod (fun _ => observationNoiseDensity_integrable)

theorem observationProductDensity_even {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    observationProductDensity (-u) = observationProductDensity u := by
  simp [observationProductDensity, observationNoiseDensity_even]

theorem observationNoiseLaw_pi_density {ι : Type*} [Fintype ι] :
    Measure.pi (fun _ : ι => observationNoiseLaw) =
      volume.withDensity (fun u : ι → ℝ => ENNReal.ofReal (observationProductDensity u)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal observationProductDensity_integrable.integrableOn
      (Filter.Eventually.of_forall observationProductDensity_nonneg)]
  change ENNReal.ofReal (∫ u : ι → ℝ in Set.univ.pi s,
    ∏ i, observationNoiseDensity (u i) ∂Measure.pi (fun _ => volume)) = _
  rw [Measure.restrict_pi_pi, integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg]
  · apply Finset.prod_congr rfl
    intro i _
    rw [observationNoiseLaw, withDensity_apply _ (hs i),
      ← ofReal_integral_eq_lintegral_ofReal observationNoiseDensity_integrable.integrableOn
        (Filter.Eventually.of_forall observationNoiseDensity_nonneg)]
  · intro i _
    exact integral_nonneg observationNoiseDensity_nonneg

theorem observationNoiseLaw_pi_integral {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) :
    (∫ u, f u ∂Measure.pi (fun _ : ι => observationNoiseLaw)) =
      ∫ u, observationProductDensity u * f u := by
  rw [observationNoiseLaw_pi_density, integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (observationProductDensity_nonneg _), smul_eq_mul]
  · exact observationProductDensity_contDiff.continuous.measurable.ennreal_ofReal
  · exact Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)

theorem observationEventLikelihood_contDiff {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) :
    ContDiff ℝ ∞ (observationEventLikelihood s) :=
  observationProductDensity_compact.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    ((locallyIntegrable_const 1).indicator hs) observationProductDensity_contDiff

theorem observationEventLikelihood_integral {ι : Type*} [Fintype ι]
    (s : Set (ι → ℝ)) (z : ι → ℝ) :
    observationEventLikelihood s z =
      ∫ u, s.indicator (fun _ => (1:ℝ)) (z+u)
        ∂Measure.pi (fun _ : ι => observationNoiseLaw) := by
  rw [observationEventLikelihood, convolution_def, observationNoiseLaw_pi_integral,
    ← integral_add_left_eq_self (fun y : ι → ℝ =>
      (ContinuousLinearMap.mul ℝ ℝ) (s.indicator (fun _ => (1:ℝ)) y)
        (observationProductDensity (z-y))) z]
  apply integral_congr_ae
  filter_upwards with u
  simp only [ContinuousLinearMap.mul_apply', show z-(z+u) = -u by abel,
    observationProductDensity_even]
  ring

theorem observationEventLikelihood_probability {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) (z : ι → ℝ) :
    observationEventLikelihood s z =
      (Measure.pi (fun _ : ι => observationNoiseLaw)).real ((fun u => z+u) ⁻¹' s) := by
  rw [observationEventLikelihood_integral]
  have he : (fun u => s.indicator (fun _ => (1:ℝ)) (z+u)) =
      ((fun u => z+u) ⁻¹' s).indicator (fun _ => (1:ℝ)) := by
    ext u
    exact (Set.indicator_comp_right (fun u : ι → ℝ => z+u)).symm
  rw [he]
  have ht : MeasurableSet ((fun u : ι → ℝ => z+u) ⁻¹' s) := hs.preimage (by fun_prop)
  rw [integral_indicator ht, setIntegral_const, smul_eq_mul, mul_one]

theorem observationEventLikelihood_nonneg {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) (z : ι → ℝ) :
    0 ≤ observationEventLikelihood s z := by
  rw [observationEventLikelihood_probability hs]
  exact measureReal_nonneg

theorem observationEventLikelihood_le_one {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) (z : ι → ℝ) :
    observationEventLikelihood s z ≤ 1 := by
  rw [observationEventLikelihood_probability hs]
  exact measureReal_le_one

theorem arrayEventLikelihood_contDiff {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) {s : Set ((H × (Fin n × Fin 3)) → ℝ)} (hs : MeasurableSet s) :
    ContDiff ℝ ∞ (arrayEventLikelihood ℓ s) :=
  (observationEventLikelihood_contDiff (hs.preimage (by
    unfold observationArrayRescale; fun_prop))).comp (observationArrayCenter ℓ).contDiff

theorem arrayEventLikelihood_nonneg {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) {s : Set ((H × (Fin n × Fin 3)) → ℝ)} (hs : MeasurableSet s)
    (x : Configuration n) : 0 ≤ arrayEventLikelihood ℓ s x :=
  observationEventLikelihood_nonneg (hs.preimage (by unfold observationArrayRescale; fun_prop)) _

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservationWidthSquareSum
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom
open scoped ENNReal Convolution
open scoped BigOperators
open scoped Convolution

theorem arrayEventLikelihood_le_one {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) {s : Set ((H × (Fin n × Fin 3)) → ℝ)} (hs : MeasurableSet s)
    (x : Configuration n) : arrayEventLikelihood ℓ s x ≤ 1 :=
  observationEventLikelihood_le_one (hs.preimage (by unfold observationArrayRescale; fun_prop)) _

theorem arrayEventLikelihood_integral {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) (hℓ : ∀ h, ℓ h ≠ 0)
    (s : Set ((H × (Fin n × Fin 3)) → ℝ)) (x : Configuration n) :
    arrayEventLikelihood ℓ s x =
      ∫ u, s.indicator (fun _ => (1:ℝ)) (fun hia => x hia.2.1 hia.2.2 + ℓ hia.1 * u hia)
        ∂Measure.pi (fun _ : H × (Fin n × Fin 3) => observationNoiseLaw) := by
  rw [arrayEventLikelihood, observationEventLikelihood_integral]
  apply integral_congr_ae
  filter_upwards with u
  have he : observationArrayRescale ℓ (observationArrayCenter ℓ x + u) =
      (fun hia => x hia.2.1 hia.2.2 + ℓ hia.1 * u hia) := by
    ext hia
    simp [observationArrayRescale, observationArrayCenter, mul_add, hℓ]
  change (observationArrayRescale ℓ ⁻¹' s).indicator
    ((fun _ => (1:ℝ)) ∘ observationArrayRescale ℓ) (observationArrayCenter ℓ x + u) = _
  rw [Set.indicator_comp_right, he]

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservationSmallScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

lemma tendsto_positive_rpow_zero {q : ℝ} (hq : 0<q) :
    Tendsto (fun r : ℝ => r^q) (𝓝[>] 0) (𝓝 0) := by
  simpa [Real.zero_rpow hq.ne'] using
    ((Real.continuous_rpow_const hq.le).tendsto 0).mono_left nhdsWithin_le_nhds

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_AtomicGapScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

lemma sqrt_rpow_monomial {a : ℝ} (ha : 0<a) {c : ℝ} (hc : 0 ≤ c) (x : ℝ) :
    Real.sqrt (c*a^x)=Real.sqrt c*a^(x/2) := by
  rw [Real.sqrt_mul hc]
  simp only [Real.sqrt_eq_rpow]
  rw [←Real.rpow_mul ha.le]
  congr 2
  ring

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_NewtonSubmean
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
namespace Coulomb

lemma volume_closedBall_three (y : Space) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (Metric.closedBall y r) = 4*Real.pi/3*r^3 := by
  rw [Measure.addHaar_real_closedBall_eq_addHaar_real_ball,
    Measure.addHaar_real_ball_center,volume_real_ball_three r hr]

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_WindowSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set
open scoped SchwartzMap
noncomputable section
namespace NeutralAtom
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem schwartz_square_bounded_lipschitz (g : 𝓢(E,ℝ)) :
    ∃ B L : ℝ, 0 ≤ B ∧ 0 ≤ L ∧ (∀ x, |g x^2| ≤ B) ∧
      (∀ x v, |g x^2-g v^2| ≤ L*‖x-v‖) := by
  let M := SchwartzMap.seminorm ℝ 0 0 g
  let D := SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.fderivCLM ℝ E ℝ g)
  have hM : 0 ≤ M := apply_nonneg _ _
  have hD : 0 ≤ D := apply_nonneg _ _
  have hm (x : E) : |g x| ≤ M := by simpa only [Real.norm_eq_abs] using g.norm_le_seminorm ℝ x
  have hd (x : E) : ‖fderiv ℝ g x‖ ≤ D :=
    (SchwartzMap.fderivCLM ℝ E ℝ g).norm_le_seminorm ℝ x
  have hl (x v : E) : |g x-g v| ≤ D*‖x-v‖ := by
    have hh := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := (g : E → ℝ)) (f' := fderiv ℝ g)
      (fun z (_ : z∈(univ : Set E)) => (g.hasFDerivAt z).hasFDerivWithinAt)
      (fun z _ => hd z) (convex_univ : Convex ℝ (univ : Set E)) (mem_univ v) (mem_univ x)
    simpa only [Real.norm_eq_abs] using hh
  refine ⟨M^2,2*M*D,sq_nonneg _,mul_nonneg (mul_nonneg (by norm_num) hM) hD,?_,?_⟩
  · intro x
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hm x) 2
  · intro x v
    have hsum : |g x+g v| ≤ 2*M := (abs_add_le _ _).trans (by linarith [hm x,hm v])
    rw [show g x^2-g v^2=(g x-g v)*(g x+g v) by ring,abs_mul]
    calc
      _ ≤ (D*‖x-v‖)*(2*M) := mul_le_mul (hl x v) hsum (abs_nonneg _) (mul_nonneg hD (norm_nonneg _))
      _ = _ := by ring
end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_KernelScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set
namespace NeutralAtom

lemma inv_upper_of_half_le {T a : ℝ} (hT : 0 < T) (ha : T/2 ≤ a) :
    a⁻¹ ≤ 2/T := by
  have ha0 : 0 < a := lt_of_lt_of_le (half_pos hT) ha
  calc
    a⁻¹ ≤ (T/2)⁻¹ := (inv_le_inv₀ ha0 (half_pos hT)).mpr ha
    _ = 2/T := by simp [div_eq_mul_inv]

lemma inv_sub_bound_of_half_le {T a b : ℝ}
    (hT : 0 < T) (ha : T/2 ≤ a) (hb : T/2 ≤ b) :
    |a⁻¹-b⁻¹| ≤ (4/T^2)*|a-b| := by
  have ha0 : 0 < a := lt_of_lt_of_le (half_pos hT) ha
  have hb0 : 0 < b := lt_of_lt_of_le (half_pos hT) hb
  rw [inv_sub_inv' ha0.ne' hb0.ne', abs_mul,abs_mul,
    abs_of_pos (inv_pos.mpr ha0),abs_of_pos (inv_pos.mpr hb0),abs_sub_comm b a]
  calc
    _ ≤ ((2/T)*|a-b|)*(2/T) := mul_le_mul
      (mul_le_mul_of_nonneg_right (inv_upper_of_half_le hT ha) (abs_nonneg _))
      (inv_upper_of_half_le hT hb) (inv_nonneg.mpr hb0.le)
      (mul_nonneg (by positivity) (abs_nonneg _))
    _ = _ := by ring

lemma inv_cube_sub_bound_of_half_le {T a b : ℝ}
    (hT : 0 < T) (ha : T/2 ≤ a) (hb : T/2 ≤ b) :
    |(a^3)⁻¹-(b^3)⁻¹| ≤ (48/T^4)*|a-b| := by
  have ha0 : 0 < a := lt_of_lt_of_le (half_pos hT) ha
  have hb0 : 0 < b := lt_of_lt_of_le (half_pos hT) hb
  have href : ∀ z ∈ Ici (T/2),
      HasDerivWithinAt (fun x : ℝ => x^(-3:ℝ)) (-3*z^(-4:ℝ)) (Ici (T/2)) z := by
    intro z hz
    have hd := (Real.hasDerivAt_rpow_const (x := z) (p := -3)
      (Or.inl (ne_of_gt (lt_of_lt_of_le (half_pos hT) hz)))).hasDerivWithinAt (s := Ici (T/2))
    norm_num only at hd
    exact hd
  have hbd : ∀ z ∈ Ici (T/2), ‖-3*z^(-4:ℝ)‖ ≤ 48/T^4 := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le (half_pos hT) hz
    rw [norm_mul,Real.norm_eq_abs,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<3),
      Real.norm_of_nonneg (Real.rpow_nonneg hz0.le _)]
    calc
      _ ≤ 3*(T/2)^(-4:ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (half_pos hT) hz (by norm_num)) (by norm_num)
      _ = 48/T^4 := by norm_num [Real.rpow_neg (le_of_lt (half_pos hT)),Real.rpow_natCast]; ring
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le href hbd (convex_Ici _)
    (show a ∈ Ici (T/2) from ha) (show b ∈ Ici (T/2) from hb)
  simpa only [Real.norm_eq_abs,show (-3:ℝ) = -(3:ℝ) by norm_num,
    Real.rpow_neg ha0.le,Real.rpow_neg hb0.le,Real.rpow_ofNat,abs_sub_comm] using hh

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma inverse_scaled_argument_bound {T a b : ℝ} (hT : 0 < T)
    (ha : T/2 ≤ a) (hb : T/2 ≤ b) (x v : E) (hv : ‖v‖ ≤ 2*T) :
    ‖a⁻¹ • x-b⁻¹ • v‖ ≤ (2/T)*‖x-v‖+(8/T)*|a-b| := by
  have ha0 : 0<a := lt_of_lt_of_le (half_pos hT) ha
  have he : a⁻¹ • x-b⁻¹ • v = a⁻¹ • (x-v)+(a⁻¹-b⁻¹) • v := by module
  rw [he]
  calc
    _ ≤ ‖a⁻¹ • (x-v)‖+‖(a⁻¹-b⁻¹) • v‖ := norm_add_le _ _
    _ = a⁻¹*‖x-v‖+|a⁻¹-b⁻¹| *‖v‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha0)]
    _ ≤ (2/T)*‖x-v‖+((4/T^2)*|a-b|)*(2*T) := add_le_add
      (mul_le_mul_of_nonneg_right (inv_upper_of_half_le hT ha) (norm_nonneg _))
      (mul_le_mul (inv_sub_bound_of_half_le hT ha hb) hv (norm_nonneg _)
        (mul_nonneg (by positivity) (abs_nonneg _)))
    _ = _ := by field_simp; ring

theorem scaled_kernel_local_bound {T a b B L : ℝ} (hT : 0 < T)
    (ha : T/2 ≤ a) (hb : T/2 ≤ b) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (φ : E → ℝ) (hφ : ∀ x, |φ x| ≤ B)
    (hφL : ∀ x v, |φ x-φ v| ≤ L*‖x-v‖)
    (x v : E) (hv : ‖v‖ ≤ 2*T) :
    |(a^3)⁻¹*φ (a⁻¹ • x)-(b^3)⁻¹*φ (b⁻¹ • v)| ≤
      ((48*B+64*L)/T^4)*|a-b|+(16*L/T^4)*‖x-v‖ := by
  have hb0 : 0<b := lt_of_lt_of_le (half_pos hT) hb
  have hb3 : (b^3)⁻¹ ≤ 8/T^3 := by
    have hh := pow_le_pow_left₀ (inv_nonneg.mpr hb0.le) (inv_upper_of_half_le hT hb) 3
    simpa only [inv_pow,div_pow,show (2:ℝ)^3=8 by norm_num] using hh
  have he : (a^3)⁻¹*φ (a⁻¹ • x)-(b^3)⁻¹*φ (b⁻¹ • v) =
      ((a^3)⁻¹-(b^3)⁻¹)*φ (a⁻¹ • x)+(b^3)⁻¹*(φ (a⁻¹ • x)-φ (b⁻¹ • v)) := by ring
  rw [he]
  calc
    _ ≤ |((a^3)⁻¹-(b^3)⁻¹)*φ (a⁻¹ • x)|+
        |(b^3)⁻¹*(φ (a⁻¹ • x)-φ (b⁻¹ • v))| := abs_add_le _ _
    _ = |(a^3)⁻¹-(b^3)⁻¹| *|φ (a⁻¹ • x)|+
        (b^3)⁻¹*|φ (a⁻¹ • x)-φ (b⁻¹ • v)| := by
      rw [abs_mul,abs_mul,abs_of_pos (inv_pos.mpr (pow_pos hb0 _))]
    _ ≤ ((48/T^4)*|a-b|)*B+(8/T^3)*
        (L*((2/T)*‖x-v‖+(8/T)*|a-b|)) := add_le_add
      ((mul_le_mul_of_nonneg_left (hφ _) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (inv_cube_sub_bound_of_half_le hT ha hb) hB))
      (mul_le_mul hb3 ((hφL _ _).trans (mul_le_mul_of_nonneg_left
        (inverse_scaled_argument_bound hT ha hb x v hv) hL))
        (abs_nonneg _) (by positivity))
    _ = _ := by field_simp; ring

end NeutralAtom

end
open Set
namespace NeutralAtom
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma scaledCenterKernel_support (φ : E → ℝ) (t : E → ℝ)
    (hs : ∀ x, 1 < ‖x‖ → φ x = 0) (ht : ∀ z, 0 < t z)
    (z y : E) (hK : scaledCenterKernel φ t z y ≠ 0) : ‖y-z‖ ≤ t z := by
  by_contra h
  have hu : 1 < ‖(t z)⁻¹ • (y-z)‖ := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (ht z).le),←div_eq_inv_mul]
    exact (lt_div_iff₀ (ht z)).mpr (by simpa using lt_of_not_ge h)
  exact hK (by simp [scaledCenterKernel,hs _ hu])

lemma scaledCenterKernel_support_width (φ : E → ℝ) (t : E → ℝ)
    (hs : ∀ x, 1 < ‖x‖ → φ x = 0) (ht : ∀ z, 0 < t z)
    (hLip : ∀ x v, |t x-t v| ≤ ‖x-v‖/4)
    (z y : E) (hK : scaledCenterKernel φ t z y ≠ 0) :
    t z ∈ Icc (4*t y/5) (4*t y/3) ∧ ‖y-z‖ ≤ 4*t y/3 := by
  have hc := scaledCenterKernel_support φ t hs ht z y hK
  have hl := hLip z y
  rw [norm_sub_rev z y] at hl
  have hh : |t z-t y| ≤ t z/4 := hl.trans (by linarith)
  have hab := abs_le.mp hh
  constructor
  · constructor <;> linarith
  · linarith

lemma scaledCenterKernel_uniform_bound (φ : E → ℝ) (t : E → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hs : ∀ x, 1 < ‖x‖ → φ x = 0)
    (hφ : ∀ x, |φ x| ≤ B) (ht : ∀ z, 0 < t z)
    (hLip : ∀ x v, |t x-t v| ≤ ‖x-v‖/4) (z y : E) :
    |scaledCenterKernel φ t z y| ≤ 8*B/(t y)^3 := by
  have hT := ht y
  by_cases hK : scaledCenterKernel φ t z y=0
  · rw [hK,abs_zero]; positivity
  have hc := (scaledCenterKernel_support_width φ t hs ht hLip z y hK).1.1
  have hi := inv_upper_of_half_le (ht y) (show t y/2 ≤ t z by linarith [ht y])
  have hh := pow_le_pow_left₀ (inv_nonneg.mpr (ht z).le) hi 3
  have hh' : ((t z)^3)⁻¹ ≤ 8/(t y)^3 := by
    simpa only [inv_pow,div_pow,show (2:ℝ)^3=8 by norm_num] using hh
  rw [scaledCenterKernel,abs_mul,abs_of_pos (inv_pos.mpr (pow_pos (ht z) _))]
  calc
    _ ≤ (8/(t y)^3)*B := mul_le_mul hh' (hφ _) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem scaledCenterKernel_center_lipschitz (φ : E → ℝ) (t : E → ℝ)
    {B L : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hs : ∀ x, 1 < ‖x‖ → φ x = 0) (hφ : ∀ x, |φ x| ≤ B)
    (hφL : ∀ x v, |φ x-φ v| ≤ L*‖x-v‖) (ht : ∀ z, 0 < t z)
    (hLip : ∀ x v, |t x-t v| ≤ ‖x-v‖/4) (z z' y : E) :
    |scaledCenterKernel φ t z y-scaledCenterKernel φ t z' y| ≤
      ((64*B+80*L)/(t y)^4)*‖z-z'‖ := by
  have hT := ht y
  have hordered (z z' : E) (hK : scaledCenterKernel φ t z y≠0) :
      |scaledCenterKernel φ t z y-scaledCenterKernel φ t z' y| ≤
        ((64*B+80*L)/(t y)^4)*‖z-z'‖ := by
    have hc := scaledCenterKernel_support_width φ t hs ht hLip z y hK
    by_cases hf : t y/4 ≤ ‖z-z'‖
    · calc
        _ ≤ |scaledCenterKernel φ t z y|+|scaledCenterKernel φ t z' y| := by simpa only [sub_zero,zero_sub,abs_neg] using (abs_sub_le (scaledCenterKernel φ t z y) 0 (scaledCenterKernel φ t z' y))
        _ ≤ 16*B/(t y)^3 := by
          have h₁ := scaledCenterKernel_uniform_bound φ t hB hs hφ ht hLip z y
          have h₂ := scaledCenterKernel_uniform_bound φ t hB hs hφ ht hLip z' y
          calc
            _ ≤ 8*B/(t y)^3+8*B/(t y)^3 := add_le_add h₁ h₂
            _ = _ := by ring
        _ = ((64*B)/(t y)^4)*(t y/4) := by field_simp; ring
        _ ≤ ((64*B+80*L)/(t y)^4)*‖z-z'‖ := mul_le_mul
          (div_le_div_of_nonneg_right (show 64*B ≤ 64*B+80*L by linarith) (pow_nonneg (ht y).le _)) hf
          (by positivity) (by positivity)
    · have hnear : ‖z-z'‖ < t y/4 := lt_of_not_ge hf
      have hab := abs_le.mp (hLip z z')
      have hb : t y/2 ≤ t z' := by linarith [hc.1.1]
      have ha : t y/2 ≤ t z := by linarith [hc.1.1,ht y]
      have hv : ‖y-z'‖ ≤ 2*t y := by
        have hh : ‖y-z'‖ ≤ ‖y-z‖+‖z-z'‖ := by
          simpa only [sub_add_sub_cancel] using (norm_add_le (y-z) (z-z'))
        linarith [hc.2]
      have hh := scaled_kernel_local_bound (ht y) ha hb hB hL φ hφ hφL (y-z) (y-z') hv
      have he : (y-z)-(y-z')=z'-z := by abel
      rw [he,norm_sub_rev z' z] at hh
      have had : |t z-t z'| ≤ ‖z-z'‖ := (hLip z z').trans (by linarith [norm_nonneg (z-z')])
      apply hh.trans
      calc
        _ ≤ ((48*B+64*L)/(t y)^4)*‖z-z'‖+(16*L/(t y)^4)*‖z-z'‖ :=
          add_le_add (mul_le_mul_of_nonneg_left had (by positivity)) le_rfl
        _ = ((48*B+80*L)/(t y)^4)*‖z-z'‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (show 48*B+80*L ≤ 64*B+80*L by linarith) (pow_nonneg (ht y).le _)) (norm_nonneg _)
  by_cases hz : scaledCenterKernel φ t z y=0
  · by_cases hz' : scaledCenterKernel φ t z' y=0
    · rw [hz,hz',sub_self,abs_zero]; positivity
    · simpa only [abs_sub_comm,norm_sub_rev] using hordered z' z hz'
  · exact hordered z z' hz

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_KernelCenterMass
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace NeutralAtom

lemma continuous_scaledCenterKernel {φ t : Coulomb.Space → ℝ}
    (hφ : Continuous φ) (htc : Continuous t) (ht : ∀ z, 0 < t z) (y : Coulomb.Space) :
    Continuous (fun z => scaledCenterKernel φ t z y) := by
  unfold scaledCenterKernel
  exact ((htc.pow 3).inv₀ (fun z => pow_ne_zero _ (ht z).ne')).mul
    (hφ.comp ((htc.inv₀ (fun z => (ht z).ne')).smul (continuous_const.sub continuous_id)))

lemma integrable_scaledCenterKernel {φ t : Coulomb.Space → ℝ}
    (hφ : Continuous φ) (htc : Continuous t) (ht : ∀ z, 0 < t z)
    (hs : ∀ x, 1 < ‖x‖ → φ x=0)
    (hLip : ∀ z z', |t z-t z'| ≤ ‖z-z'‖/4) (y : Coulomb.Space) :
    Integrable (fun z => scaledCenterKernel φ t z y) := by
  apply (continuous_scaledCenterKernel hφ htc ht y).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Metric.closedBall y (2*t y)) (isCompact_closedBall _ _)
  intro z hz
  by_contra hK
  have hh := (scaledCenterKernel_support_width φ t hs ht hLip z y hK).2
  apply hz
  rw [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev]
  linarith [ht y]

lemma integral_constant_scaledCenterKernel (φ : Coulomb.Space → ℝ)
    {T : ℝ} (hT : 0 < T) (y : Coulomb.Space) :
    (∫ z, scaledCenterKernel φ (fun _ => T) z y) = ∫ z, φ z := by
  unfold scaledCenterKernel
  rw [integral_const_mul, integral_sub_left_eq_self
    (fun z : Coulomb.Space => φ (T⁻¹ • z)),
    Measure.integral_comp_inv_smul_of_nonneg volume φ hT.le]
  simp only [Coulomb.Space,finrank_euclideanSpace_fin,smul_eq_mul]
  rw [←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ hT.ne'),one_mul]

theorem center_kernel_mass_defect {φ t : Coulomb.Space → ℝ} {B L q : ℝ}
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hq : 0 ≤ q) (hqs : q ≤ 1/4)
    (hφc : Continuous φ) (htc : Continuous t) (ht : ∀ z, 0 < t z)
    (hs : ∀ x, 1 < ‖x‖ → φ x=0) (hφ : ∀ x, |φ x| ≤ B)
    (hφL : ∀ x v, |φ x-φ v| ≤ L*‖x-v‖)
    (hLip : ∀ z z', |t z-t z'| ≤ q*‖z-z'‖)
    (y : Coulomb.Space) :
    |(∫ z, scaledCenterKernel φ t z y)-(∫ z, φ z)| ≤
      (64*Real.pi/3)*(48*B+64*L)*q := by
  have hT := ht y
  have hLip' : ∀ z z', |t z-t z'| ≤ ‖z-z'‖/4 := by
    intro z z'
    calc
      _ ≤ q*‖z-z'‖ := hLip z z'
      _ ≤ (1/4)*‖z-z'‖ := mul_le_mul_of_nonneg_right hqs (norm_nonneg _)
      _ = _ := by ring
  let F : Coulomb.Space → ℝ := fun z => scaledCenterKernel φ t z y
  let G : Coulomb.Space → ℝ := fun z => scaledCenterKernel φ (fun _ => t y) z y
  have hFi : Integrable F := integrable_scaledCenterKernel hφc htc ht hs hLip' y
  have hGi : Integrable G := integrable_scaledCenterKernel hφc continuous_const (fun _ => hT) hs
    (by intro z z'; simp only [sub_self,abs_zero]; positivity) y
  have hpt (z : Coulomb.Space) (hz : z∈Metric.closedBall y (2*t y)) :
      |F z-G z| ≤ 2*(48*B+64*L)*q/(t y)^3 := by
    have hz' : ‖y-z‖ ≤ 2*t y := by simpa only [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev] using hz
    have hwd : |t z-t y| ≤ 2*q*t y := by
      calc
        _ ≤ q*‖z-y‖ := hLip z y
        _ ≤ q*(2*t y) := mul_le_mul_of_nonneg_left (by simpa only [norm_sub_rev] using hz') hq
        _ = _ := by ring
    have ha : t y/2 ≤ t z := by
      have hab := abs_le.mp hwd
      have hqt := mul_le_mul_of_nonneg_right hqs hT.le
      nlinarith
    have hh := scaled_kernel_local_bound hT ha (show t y/2 ≤ t y by linarith) hB hL φ hφ hφL
      (y-z) (y-z) hz'
    simp only [sub_self,norm_zero,mul_zero,add_zero] at hh
    calc
      _ ≤ ((48*B+64*L)/(t y)^4)*|t z-t y| := hh
      _ ≤ ((48*B+64*L)/(t y)^4)*(2*q*t y) := mul_le_mul_of_nonneg_left hwd (by positivity)
      _ = _ := by field_simp
  have hout (z : Coulomb.Space) (hz : z∉Metric.closedBall y (2*t y)) : F z-G z=0 := by
    have hz' : 2*t y < ‖y-z‖ := by simpa only [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev,not_le] using hz
    have hF : F z=0 := by
      by_contra hh
      have hh' := (scaledCenterKernel_support_width φ t hs ht hLip' z y hh).2
      linarith
    have hG : G z=0 := by
      by_contra hh
      have hh' := scaledCenterKernel_support φ (fun _ => t y) hs (fun _ => hT) z y hh
      linarith
    rw [hF,hG,sub_self]
  rw [←integral_constant_scaledCenterKernel φ hT y,←integral_sub hFi hGi]
  change |∫ z, F z-G z| ≤ _
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero hout]
  have hh := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (isCompact_closedBall y (2*t y)).measure_lt_top
    (fun z hz => (show ‖F z-G z‖ ≤ 2*(48*B+64*L)*q/(t y)^3 by simpa only [Real.norm_eq_abs] using hpt z hz))
  rw [Real.norm_eq_abs,Coulomb.volume_closedBall_three y (by positivity : 0 ≤ 2*t y)] at hh
  apply hh.trans_eq
  field_simp
  ring

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_LimitTheory_UniformGroundStateCountControl
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

theorem rawCount_nonneg {n : ℕ} (S : Set Position) (x : Configuration n) :
    0 ≤ rawCount S x := by
  apply Finset.sum_nonneg
  intro i _
  by_cases hi : x i ∈ S <;> simp [hi]

theorem rawCount_le_number {n : ℕ} (S : Set Position) (x : Configuration n) :
    rawCount S x ≤ n := by
  calc
    rawCount S x ≤ ∑ _i : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : x i ∈ S <;> simp [hi]
    _ = n := by simp

theorem packetWidth_pos {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) (z : Position) : 0 < packetWidth c₁ r₀ s z := by
  unfold packetWidth
  have hmax : 0 < max ‖z‖ r₀ := lt_of_lt_of_le hr (le_max_right _ _)
  exact mul_pos (mul_pos hc hmax) (Real.rpow_pos_of_pos (lt_min hmax hs) _)

theorem packetKernel_eq_wavepacket_sq (g : Position → ℝ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z y : Position) :
    packetKernel g c₁ r₀ s z y =
      ((packetWidth c₁ r₀ s z) ^ (-(3 / 2 : ℝ)) *
        g ((packetWidth c₁ r₀ s z)⁻¹ • (y-z))) ^ 2 := by
  have ht := (packetWidth_pos hc hr hs z).le
  rw [mul_pow]
  unfold packetKernel
  congr 1
  rw [← Real.rpow_natCast (_ ^ (-(3 / 2 : ℝ))) 2, ← Real.rpow_mul ht]
  norm_num

theorem packetKernel_nonneg (g : Position → ℝ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z y : Position) :
    0 ≤ packetKernel g c₁ r₀ s z y := by
  rw [packetKernel_eq_wavepacket_sq g hc hr hs]
  positivity

theorem integral_packetKernel (g : Position → ℝ) (hg : (∫ y, g y ^ 2) = 1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z : Position) :
    (∫ y, packetKernel g c₁ r₀ s z y) = 1 := by
  have ht := packetWidth_pos hc hr hs z
  unfold packetKernel
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun y : Position => (g ((packetWidth c₁ r₀ s z)⁻¹ • y)) ^ 2)]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume (fun y : Position => g y ^ 2) ht.le]
  simp only [Position, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, hg, mul_one]
  exact inv_mul_cancel₀ (pow_ne_zero _ ht.ne')

theorem integrable_packetKernel (g : Position → ℝ) (hg : (∫ y, g y ^ 2) = 1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z : Position) :
    Integrable (packetKernel g c₁ r₀ s z) := by
  by_contra hnot
  have hzero := integral_undef hnot
  rw [integral_packetKernel g hg hc hr hs z] at hzero
  exact one_ne_zero hzero

theorem packetWidth_le (c₁ r₀ s : ℝ) (hc : 0 ≤ c₁) (_hr : 0 < r₀)
    (hs : 0 < s) (z : Position) :
    packetWidth c₁ r₀ s z ≤ (c₁ * s ^ packetExponent) * max ‖z‖ r₀ := by
  unfold packetWidth
  calc
    c₁ * max ‖z‖ r₀ * min (max ‖z‖ r₀) s ^ packetExponent
      ≤ c₁ * max ‖z‖ r₀ * s ^ packetExponent := by
        apply mul_le_mul_of_nonneg_left
        · exact Real.rpow_le_rpow (le_min (le_max_of_le_left (norm_nonneg _)) hs.le)
            (min_le_right _ _) (by norm_num [packetExponent])
        · exact mul_nonneg hc (le_max_of_le_left (norm_nonneg _))
    _ = (c₁ * s ^ packetExponent) * max ‖z‖ r₀ := by ring

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PacketWidthScalar
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set
namespace NeutralAtom

theorem clamped_width_scalar_lipschitz {w s u v : ℝ}
    (hw : 0  ≤  w) (hs : 0  <  s) (hu : 0  <  u) (hv : 0  <  v) :
    |u * (min u s)^w - v * (min v s)^w|  ≤
      (1+w)*s^w*|u-v| := by
  have hbelow {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ s) :
      |y*(min y s)^w-x*(min x s)^w|  ≤  (1+w)*s^w*(y-x) := by
    have href : ∀ z ∈ Icc x y,
        HasDerivWithinAt (fun z : ℝ => z^(w+1)) ((w+1)*z^w) (Icc x y) z := by
      intro z hz
      simpa only [add_sub_cancel_right] using (Real.hasDerivAt_rpow_const (p := w+1) (Or.inl (ne_of_gt (hx.trans_le hz.1)))).hasDerivWithinAt (s := Icc x y)
    have hbd : ∀ z ∈ Icc x y, ‖(w+1)*z^w‖  ≤  (1+w)*s^w := by
      intro z hz
      rw [Real.norm_of_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (hx.le.trans hz.1) _))]
      calc
        (w+1)*z^w  ≤  (w+1)*s^w := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (hx.le.trans hz.1) (hz.2.trans hy) hw) (by linarith)
        _ = (1+w)*s^w := by ring
    have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le href hbd
      (convex_Icc x y) (show x ∈ Icc x y from ⟨le_rfl,hxy⟩)
      (show y ∈ Icc x y from ⟨hxy,le_rfl⟩)
    rw [Real.rpow_add_one (ne_of_gt (hx.trans_le hxy)), Real.rpow_add_one hx.ne',
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy)] at hh
    simpa only [min_eq_left hy, min_eq_left (hxy.trans hy), mul_comm] using hh
  have hordered {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
      |y*(min y s)^w-x*(min x s)^w|  ≤  (1+w)*s^w*(y-x) := by
    by_cases hy : y ≤ s
    · exact hbelow hx hxy hy
    by_cases hxs : s ≤ x
    · rw [min_eq_right hxs, min_eq_right (hxs.trans hxy), ←sub_mul,
        abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hxy) (Real.rpow_nonneg hs.le _))]
      have hw0 := mul_nonneg hw (mul_nonneg (Real.rpow_nonneg hs.le w) (sub_nonneg.mpr hxy))
      nlinarith
    · have hxle : x  ≤  s := le_of_not_ge hxs
      have hsy : s  ≤  y := le_of_not_ge hy
      have hh := hbelow hx hxle le_rfl
      rw [min_self, min_eq_left hxle] at hh
      have he : y*s^w - x*x^w = (y-s)*s^w+(s*s^w-x*x^w) := by ring
      rw [min_eq_right hsy, min_eq_left hxle,he]
      calc
        |(y-s)*s^w+(s*s^w-x*x^w)|  ≤  |(y-s)*s^w|+|s*s^w-x*x^w| := abs_add_le _ _
        _  ≤  (y-s)*s^w+(1+w)*s^w*(s-x) := by
          rw [abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hsy) (Real.rpow_nonneg hs.le _))]
          exact add_le_add_right hh _
        _  ≤  (1+w)*s^w*(y-x) := by
          have hw0 := mul_nonneg hw (mul_nonneg (Real.rpow_nonneg hs.le w) (sub_nonneg.mpr hsy))
          nlinarith
  rcases le_total u v with huv | hvu
  · rw [abs_sub_comm,abs_of_nonpos (sub_nonpos.mpr huv)]
    simpa only [neg_sub] using hordered hu huv
  · rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
    exact hordered hv hvu
end NeutralAtom

end
open MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace NeutralAtom

theorem continuous_packetWidth (c₁ r₀ s : ℝ) : Continuous (packetWidth c₁ r₀ s) := by
  unfold packetWidth
  fun_prop (disch := norm_num [packetExponent])

theorem packetWidth_lipschitz {c r₀ s : ℝ} (hc : 0 ≤ c)
    (hr : 0 < r₀) (hs : 0 < s) (z z' : Position) :
    |packetWidth c r₀ s z-packetWidth c r₀ s z'| ≤
      (c*(1+packetExponent)*s^packetExponent)*‖z-z'‖ := by
  have h := clamped_width_scalar_lipschitz (w := packetExponent) (u := max ‖z‖ r₀) (v := max ‖z'‖ r₀) (by norm_num [packetExponent]) hs
    (hr.trans_le (le_max_right _ _)) (hr.trans_le (le_max_right _ _))
  have hm : |max ‖z‖ r₀-max ‖z'‖ r₀| ≤ ‖z-z'‖ := by
    calc
      _ ≤ max |‖z‖-‖z'‖| |r₀-r₀| := abs_max_sub_max_le_max _ _ _ _
      _ = |‖z‖-‖z'‖| := by simp
      _ ≤ ‖z-z'‖ := abs_norm_sub_norm_le _ _
  unfold packetWidth
  rw [show c*max ‖z‖ r₀*(min (max ‖z‖ r₀) s)^packetExponent-
      c*max ‖z'‖ r₀*(min (max ‖z'‖ r₀) s)^packetExponent =
      c*(max ‖z‖ r₀*(min (max ‖z‖ r₀) s)^packetExponent-
      max ‖z'‖ r₀*(min (max ‖z'‖ r₀) s)^packetExponent) by ring,
    abs_mul,abs_of_nonneg hc]
  calc
    _ ≤ c*((1+packetExponent)*s^packetExponent*|max ‖z‖ r₀-max ‖z'‖ r₀|) :=
      mul_le_mul_of_nonneg_left h hc
    _ ≤ (c*(1+packetExponent)*s^packetExponent)*‖z-z'‖ := by
      have hh := mul_le_mul_of_nonneg_left hm
        (show 0 ≤ c*(1+packetExponent)*s^packetExponent from
          mul_nonneg (mul_nonneg hc (by norm_num [packetExponent])) (Real.rpow_nonneg hs.le _))
      simpa only [mul_assoc] using hh

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_MasterKernel
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology SchwartzMap
noncomputable section
namespace NeutralAtom

theorem master_kernel_estimates (g : 𝓢(Position,ℝ))
    (hg : ∀ x, 1 < ‖x‖ → g x=0) (hm : (∫ x, g x^2)=1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {c r₀ s : ℝ}, 0 < c → 0 < r₀ → 0 < s →
    c*(1+packetExponent)*s^packetExponent ≤ 1/4 →
    ∀ y : Position,
      (∀ z, packetKernel g c r₀ s z y≠0 → ‖y-z‖ ≤ 2*packetWidth c r₀ s y) ∧
      (∀ z, |packetKernel g c r₀ s z y| ≤ C/(packetWidth c r₀ s y)^3) ∧
      (∀ z z', |packetKernel g c r₀ s z y-packetKernel g c r₀ s z' y| ≤
        (C/(packetWidth c r₀ s y)^4)*‖z-z'‖) ∧
      Integrable (fun z => packetKernel g c r₀ s z y) ∧
      |(∫ z, packetKernel g c r₀ s z y)-1| ≤
        C*(c*(1+packetExponent)*s^packetExponent) := by
  obtain ⟨B,L,hB,hL,hφ,hφL⟩ := schwartz_square_bounded_lipschitz g
  let A := 8*B
  let D := 64*B+80*L
  let M := (64*Real.pi/3)*(48*B+64*L)
  let C := 1+A+D+M
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hAC : A ≤ C := by dsimp [C]; linarith
  have hDC : D ≤ C := by dsimp [C]; linarith
  have hMC : M ≤ C := by dsimp [C]; linarith
  refine ⟨C,by dsimp [C]; linarith,?_⟩
  intro c r₀ s hc hr hs hsmall y
  let t := packetWidth c r₀ s
  let q := c*(1+packetExponent)*s^packetExponent
  have ht : ∀ z, 0 < t z := packetWidth_pos hc hr hs
  have hq : 0 ≤ q := by
    dsimp [q]
    exact mul_nonneg (mul_nonneg hc.le (by norm_num [packetExponent]))
      (Real.rpow_nonneg hs.le _)
  have hlip : ∀ z z', |t z-t z'| ≤ q*‖z-z'‖ := packetWidth_lipschitz hc.le hr hs
  have hlip' : ∀ z z', |t z-t z'| ≤ ‖z-z'‖/4 := by
    intro z z'
    calc
      _ ≤ q*‖z-z'‖ := hlip z z'
      _ ≤ (1/4)*‖z-z'‖ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
      _ = _ := by ring
  have hφs : ∀ x, 1 < ‖x‖ → (fun z => g z^2) x=0 := by
    intro x hx; simp only [hg x hx,zero_pow (by decide : (2:ℕ)≠0)]
  have he (z : Position) : packetKernel g c r₀ s z y=scaledCenterKernel (fun z => g z^2) t z y := rfl
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro z hK
    rw [he] at hK
    have hh := (scaledCenterKernel_support_width _ t hφs ht hlip' z y hK).2
    linarith [ht y]
  · intro z
    rw [he]
    exact (scaledCenterKernel_uniform_bound _ t hB hφs hφ ht hlip' z y).trans
      (div_le_div_of_nonneg_right hAC (pow_nonneg (ht y).le _))
  · intro z z'
    rw [he,he]
    exact (scaledCenterKernel_center_lipschitz _ t hB hL hφs hφ hφL ht hlip' z z' y).trans
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hDC (pow_nonneg (ht y).le _)) (norm_nonneg _))
  · exact integrable_scaledCenterKernel (g.continuous.pow 2) (continuous_packetWidth c r₀ s) ht hφs hlip' y
  · have hh := center_kernel_mass_defect hB hL hq hsmall (g.continuous.pow 2)
      (continuous_packetWidth c r₀ s) ht hφs hφ hφL hlip y
    change |(∫ z, packetKernel g c r₀ s z y)-(∫ z, g z^2)| ≤ M*q at hh
    rw [hm] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hMC hq)

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PatchKernelDuality
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap

namespace NeutralAtom

theorem kernel_sum_matching {n : ℕ} (K : Position → ℝ) (y : Position)
    {R A d : ℝ} (hA : 0 ≤ A) (hd : 0 ≤ d)
    (hs : ∀ z, R < ‖z-y‖ → K z=0)
    (hL : ∀ z v, |K z-K v| ≤ A*‖z-v‖)
    (x v : Configuration n) (hv : ∀ i, ‖x i-v i‖ ≤ d) :
    |(∑ i, K (x i))-(∑ i, K (v i))| ≤
      (A*d)*rawCount (Metric.closedBall y (R+d)) v := by
  rw [←Finset.sum_sub_distrib,rawCount,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : v i ∈ Metric.closedBall y (R+d)
  · rw [indicator_of_mem hi,mul_one]
    exact (hL _ _).trans (mul_le_mul_of_nonneg_left (hv i) hA)
  · rw [indicator_of_notMem hi,mul_zero]
    have hvi : R+d < ‖v i-y‖ := by
      simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hi
    have hxi : R < ‖x i-y‖ := by
      have htri := norm_sub_le_norm_sub_add_norm_sub (v i) (x i) y
      rw [norm_sub_rev (v i) (x i)] at htri
      linarith [hv i]
    rw [hs _ hxi,hs _ (by linarith),sub_self,abs_zero]

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ConditionalDensity
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace NeutralAtom

theorem continuous_packetKernel {g : Position → ℝ} (hg : Continuous g)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) :
    Continuous (fun zy : Position × Position => packetKernel g c₁ r₀ s zy.1 zy.2) := by
  have ht : Continuous (fun zy : Position × Position => packetWidth c₁ r₀ s zy.1) :=
    (continuous_packetWidth c₁ r₀ s).comp continuous_fst
  have htne : ∀ zy : Position × Position, packetWidth c₁ r₀ s zy.1 ≠ 0 :=
    fun zy => (packetWidth_pos hc hr hs zy.1).ne'
  unfold packetKernel
  exact ((ht.pow 3).inv₀ (fun zy => pow_ne_zero _ (htne zy))).mul
    ((hg.comp ((ht.inv₀ htne).smul (continuous_snd.sub continuous_fst))).pow 2)

theorem rawPacketDensity_nonneg {n : ℕ} (g : Position → ℝ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (x : Configuration n) (y : Position) :
    0 ≤ rawPacketDensity g c₁ r₀ s x y :=
  Finset.sum_nonneg (fun i _ => packetKernel_nonneg g hc hr hs (x i) y)

theorem rawPacketDensity_integrable {n : ℕ} (g : Position → ℝ) (hgnorm : (∫ y, g y^2)=1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (x : Configuration n) :
    Integrable (rawPacketDensity g c₁ r₀ s x) :=
  integrable_finsetSum _ (fun i _ => integrable_packetKernel g hgnorm hc hr hs (x i))

theorem rawPacketDensity_mass {n : ℕ} (g : Position → ℝ) (hgnorm : (∫ y, g y^2)=1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (x : Configuration n) :
    (∫ y, rawPacketDensity g c₁ r₀ s x y) = n := by
  unfold rawPacketDensity
  rw [integral_finsetSum _ (fun i _ => integrable_packetKernel g hgnorm hc hr hs (x i))]
  simp only [integral_packetKernel g hgnorm hc hr hs, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem continuous_rawPacketDensity {n : ℕ} {g : Position → ℝ} (hg : Continuous g)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) :
    Continuous (fun xy : Configuration n × Position => rawPacketDensity g c₁ r₀ s xy.1 xy.2) := by
  have hi : ∀ i : Fin n, Continuous (fun xy : Configuration n × Position =>
      packetKernel g c₁ r₀ s (xy.1 i) xy.2) := by
    intro i
    have hh : Continuous (fun xy : Configuration n × Position => xy.1 i) :=
      (continuous_apply i).comp continuous_fst
    have hhpair : Continuous (fun xy : Configuration n × Position => (xy.1 i,xy.2)) :=
      hh.prodMk continuous_snd
    change Continuous ((fun zy : Position × Position => packetKernel g c₁ r₀ s zy.1 zy.2) ∘
      (fun xy : Configuration n × Position => (xy.1 i,xy.2)))
    exact (continuous_packetKernel hg hc hr hs).comp hhpair
  exact continuous_finsetSum Finset.univ (fun i _ => hi i)

theorem packetWidth_lower {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z : Position) :
    c₁*r₀*(min r₀ s)^packetExponent ≤ packetWidth c₁ r₀ s z := by
  unfold packetWidth
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (le_max_right _ _) hc.le
  · exact Real.rpow_le_rpow (lt_min hr hs).le
      (min_le_min (le_max_right _ _) le_rfl) (by norm_num [packetExponent])
  · exact Real.rpow_nonneg (lt_min hr hs).le _
  · exact mul_nonneg hc.le (hr.le.trans (le_max_right _ _))

theorem compact_packet_function_bound {g : Position → ℝ} (hg : Continuous g)
    (hgs : HasCompactSupport g) : ∃ A : ℝ, 0 ≤ A ∧ ∀ x, g x^2 ≤ A := by
  obtain ⟨A,hA⟩ := ((hgs.isCompact_range hg).image (continuous_id.pow 2)).bddAbove
  refine ⟨A, (sq_nonneg (g 0)).trans (hA ⟨g 0, ⟨0,rfl⟩,rfl⟩), ?_⟩
  intro x
  exact hA ⟨g x,⟨x,rfl⟩,rfl⟩

theorem packetKernel_bound {g : Position → ℝ} {A c₁ r₀ s : ℝ}
    (_hA : 0 ≤ A) (hg : ∀ x, g x^2 ≤ A)
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (z y : Position) :
    packetKernel g c₁ r₀ s z y ≤ (c₁*r₀*(min r₀ s)^packetExponent)^(-3:ℤ)*A := by
  have hp : 0 < c₁*r₀*(min r₀ s)^packetExponent := by positivity
  have hh := packetWidth_lower hc hr hs z
  have hinv := inv_anti₀ (pow_pos hp 3) (pow_le_pow_left₀ hp.le hh 3)
  change (packetWidth c₁ r₀ s z^3)⁻¹*g _^2 ≤ _
  rw [zpow_neg]
  exact mul_le_mul hinv (hg _) (sq_nonneg _) (by positivity)

theorem rawPacketDensity_bound {n : ℕ} {g : Position → ℝ} {A c₁ r₀ s : ℝ}
    (hA : 0 ≤ A) (hg : ∀ x, g x^2 ≤ A)
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (x : Configuration n) (y : Position) :
    rawPacketDensity g c₁ r₀ s x y ≤
      n*((c₁*r₀*(min r₀ s)^packetExponent)^(-3:ℤ)*A) := by
  calc
    _ ≤ ∑ _i : Fin n, (c₁*r₀*(min r₀ s)^packetExponent)^(-3:ℤ)*A :=
      Finset.sum_le_sum (fun i _ => packetKernel_bound hA hg hc hr hs (x i) y)
    _ = _ := by simp

theorem rawPacketDensity_integrable_configuration {n : ℕ} {g : Position → ℝ}
    (hg : Continuous g) (hgs : HasCompactSupport g) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (ν : Measure (Configuration n)) [IsFiniteMeasure ν] (y : Position) :
    Integrable (fun x => rawPacketDensity g c₁ r₀ s x y) ν := by
  obtain ⟨A,hA,hAb⟩ := compact_packet_function_bound hg hgs
  have hm : AEStronglyMeasurable (fun x => rawPacketDensity g c₁ r₀ s x y) ν :=
    ((continuous_rawPacketDensity hg hc hr hs).comp
      (continuous_id.prodMk (continuous_const (y := y)))).aestronglyMeasurable
  apply (integrable_const (n*((c₁*r₀*(min r₀ s)^packetExponent)^(-3:ℤ)*A))).mono' hm
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (rawPacketDensity_nonneg g hc hr hs x y)]
    using rawPacketDensity_bound hA hAb hc hr hs x y

theorem conditionalPacketDensity_eq_condExp {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    {n : ℕ} (P : Measure Ω) [IsFiniteMeasure P]
    (ν : Measure (Configuration n)) [IsFiniteMeasure ν]
    {raw : Ω → Configuration n} {obs : Ω → B}
    (hraw : MeasurePreserving raw P ν) (hobs : Measurable obs)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) (y : Position) :
    (fun sample => conditionalPacketDensity P raw obs g c₁ r₀ s (obs sample) y) =ᵐ[P]
      P[fun sample => rawPacketDensity g c₁ r₀ s (raw sample) y |
        MeasurableSpace.comap obs inferInstance] := by
  have hf : StronglyMeasurable (fun x : Configuration n => rawPacketDensity g c₁ r₀ s x y) :=
    ((continuous_rawPacketDensity hg hc hr hs).comp
      (continuous_id.prodMk (continuous_const (y := y)))).stronglyMeasurable
  exact (ProbabilityTheory.condExp_ae_eq_integral_condDistrib hobs hraw.measurable.aemeasurable hf
    (hraw.integrable_comp_of_integrable (rawPacketDensity_integrable_configuration hg hgs hc hr hs ν y))).symm

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ConditionalMatching
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace NeutralAtom

theorem condExp_matching {α : Type*} [m₀ : MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {m : MeasurableSpace α}
    (hm : m ≤ m₀) {f g e : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (he : Integrable e μ)
    (hgm : StronglyMeasurable[m] g) (hem : StronglyMeasurable[m] e)
    (hfg : ∀ᵐ z ∂μ, |f z-g z|≤e z) :
    ∀ᵐ z ∂μ, |(μ[f|m]) z-g z|≤e z := by
  have hupper := condExp_mono hf (hg.add he) (hfg.mono (fun z hz => by
    have hh := (abs_le.mp hz).2
    change f z≤g z+e z
    linarith)) (m := m)
  have hlower := condExp_mono (hg.sub he) hf (hfg.mono (fun z hz => by
    have hh := (abs_le.mp hz).1
    change g z-e z≤f z
    linarith)) (m := m)
  rw [condExp_of_stronglyMeasurable hm (hgm.add hem) (hg.add he)] at hupper
  rw [condExp_of_stronglyMeasurable hm (hgm.sub hem) (hg.sub he)] at hlower
  filter_upwards [hupper,hlower] with z hu hl
  change _≤g z+e z at hu
  change g z-e z≤_ at hl
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end NeutralAtom

end
open MeasureTheory
open scoped ENNReal ContDiff
namespace NeutralAtom

theorem measurable_forgetOrder {n : ℕ} : Measurable (forgetOrder (n := n)) :=
  measurable_iff_le_map.mpr le_rfl

theorem observationLaw_rawProjection {n J : ℕ} (ν : Measure (Configuration n)) :
    MeasurePreserving Prod.fst (observationLaw J ν) ν := measurePreserving_fst

theorem observationNoiseVector_coordinate (v : Fin 3 → ℝ) (a : Fin 3) :
    observationNoiseVector v a = v a := by
  simp [observationNoiseVector, Pi.single_apply]

theorem continuous_observationNoiseVector : Continuous observationNoiseVector := by
  unfold observationNoiseVector
  exact continuous_finsetSum Finset.univ (fun a _ => (continuous_apply a).smul continuous_const)

theorem measurable_observedOrdered {n J : ℕ} (r : Fin J → ℝ) (j : Fin J) :
    Measurable (observedOrdered (n := n) r j) := by
  apply Measurable.of_eval
  intro i
  have hn : Measurable (fun sample : ObservationSample n J => sample.2 j i) :=
    (measurable_pi_apply i).comp ((measurable_pi_apply j).comp measurable_snd)
  exact ((measurable_pi_apply i).comp measurable_fst).add
    ((continuous_observationNoiseVector.measurable.comp hn).const_smul ((r j)^(101/100 : ℝ)))

theorem measurable_observedArray {n J : ℕ} (r : Fin J → ℝ) (j : Fin J) :
    Measurable (observedArray (n := n) r j) :=
  measurable_forgetOrder.comp (measurable_observedOrdered r j)

theorem measurable_tailObservation {n J : ℕ} (r : Fin J → ℝ) (j : ℕ) :
    Measurable (tailObservation (n := n) r j) := by
  apply Measurable.of_eval
  intro k
  by_cases hj : j ≤ k.val
  · simpa only [tailObservation, ite_eq_left hj] using measurable_observedArray r k
  · simpa only [tailObservation, ite_eq_right hj] using
      (measurable_const : Measurable (fun _ : ObservationSample n J => forgetOrder (0 : Configuration n)))

theorem observationSigma_le {n J : ℕ} (r : Fin J → ℝ) (j : ℕ) :
    observationSigma (n := n) r j ≤ (inferInstance : MeasurableSpace (ObservationSample n J)) :=
  measurable_iff_comap_le.mp (measurable_tailObservation r j)

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_OriginalPotentialTower
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace NeutralAtom

theorem rawPacketPotential_uniform {n : ℕ} {g : Position → ℝ}
    (hg : Continuous g) (hgs : HasCompactSupport g) (hm : (∫ z, g z^2)=1)
    {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s) :
    ∃ B : ℝ, 0≤B ∧ ∀ (x : Configuration n) (y : Position),
      Integrable (fun z => coulombKernel (y-z)*rawPacketDensity g c r₀ s x z) ∧
      0≤potentialOf (rawPacketDensity g c r₀ s x) y ∧
      potentialOf (rawPacketDensity g c r₀ s x) y≤B := by
  obtain ⟨A,hA,hAb⟩ := compact_packet_function_bound hg hgs
  let M : ℝ := n*((c*r₀*(min r₀ s)^packetExponent)^(-3:ℤ)*A)
  have hM : 0≤M := by dsimp [M]; positivity
  refine ⟨2*Real.pi*M+n,by positivity,?_⟩
  intro x y
  have hρ := rawPacketDensity_integrable g hm hc hr hs x
  have hρm : Measurable (rawPacketDensity g c r₀ s x) :=
    ((continuous_rawPacketDensity hg hc hr hs).comp
      ((continuous_const (y := x)).prodMk continuous_id)).measurable
  have hρ0 := rawPacketDensity_nonneg g hc hr hs x
  have hρM : ∀ z,rawPacketDensity g c r₀ s x z≤M :=
    rawPacketDensity_bound hA hAb hc hr hs x
  refine ⟨Coulomb.coulomb_convolution_integrable hρ hρm hρ0 hρM
    (by norm_num : (0:ℝ)<1) y,integral_nonneg (fun z =>
      mul_nonneg (coulombKernel_nonneg _) (hρ0 z)),?_⟩
  simpa [potentialOf,coulombKernel,Coulomb.coulombKernel,rawPacketDensity_mass g hm hc hr hs] using
    Coulomb.coulomb_convolution_bound hρ hρm hρ0 hρM (by norm_num : (0:ℝ)<1) y

lemma measurable_rawPacketPotential {n : ℕ} {g : Position → ℝ} (hg : Continuous g)
    {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s) (y : Position) :
    Measurable (fun x : Configuration n => potentialOf (rawPacketDensity g c r₀ s x) y) := by
  have hi : Measurable (fun xz : Configuration n × Position =>
      coulombKernel (y-xz.2)*rawPacketDensity g c r₀ s xz.1 xz.2) :=
    (measurable_coulombKernel.comp (measurable_const.sub measurable_snd)).mul
      (continuous_rawPacketDensity hg hc hr hs).measurable
  exact hi.stronglyMeasurable.integral_prod_right'.measurable

lemma integrable_rawPacketPotential {n : ℕ} {g : Position → ℝ}
    (hg : Continuous g) (hgs : HasCompactSupport g) (hm : (∫ z,g z^2)=1)
    {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    (ν : Measure (Configuration n)) [IsFiniteMeasure ν] (y : Position) :
    Integrable (fun x => potentialOf (rawPacketDensity g c r₀ s x) y) ν := by
  obtain ⟨B,hB,H⟩ := rawPacketPotential_uniform (n := n) hg hgs hm hc hr hs
  apply (integrable_const B).mono' (measurable_rawPacketPotential hg hc hr hs y).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by simpa [Real.norm_of_nonneg (H x y).2.1] using (H x y).2.2)

theorem mixturePacketPotential {n : ℕ} {g : Position → ℝ}
    (hg : Continuous g) (hgs : HasCompactSupport g) (hm : (∫ z,g z^2)=1)
    {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    (ν : Measure (Configuration n)) [IsFiniteMeasure ν] (y : Position) :
    potentialOf (mixturePacketDensity ν g c r₀ s) y =
      ∫ x, potentialOf (rawPacketDensity g c r₀ s x) y ∂ν := by
  obtain ⟨B,hB,H⟩ := rawPacketPotential_uniform (n := n) hg hgs hm hc hr hs
  have hmeas : Measurable (fun xz : Configuration n × Position =>
      coulombKernel (y-xz.2)*rawPacketDensity g c r₀ s xz.1 xz.2) :=
    (measurable_coulombKernel.comp (measurable_const.sub measurable_snd)).mul
      (continuous_rawPacketDensity hg hc hr hs).measurable
  have hi : Integrable (fun xz : Configuration n × Position =>
      coulombKernel (y-xz.2)*rawPacketDensity g c r₀ s xz.1 xz.2) (ν.prod volume) := by
    apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall (fun x => (H x y).1),?_⟩
    have he : (fun x : Configuration n => ∫ z, ‖coulombKernel (y-z)*rawPacketDensity g c r₀ s x z‖)=
        fun x => potentialOf (rawPacketDensity g c r₀ s x) y := by
      funext x
      simp only [potentialOf,Real.norm_of_nonneg (mul_nonneg (coulombKernel_nonneg _) (rawPacketDensity_nonneg g hc hr hs x _))]
    rw [he]
    exact integrable_rawPacketPotential hg hgs hm hc hr hs ν y
  change (∫ z, coulombKernel (y-z)*(∫ x,rawPacketDensity g c r₀ s x z ∂ν))=_
  simp_rw [←integral_const_mul]
  exact integral_integral_swap hi.swap

theorem conditionalPacketPotential_eq_condExp {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure (Configuration n)) [IsFiniteMeasure ν]
    {raw : Ω → Configuration n} {obs : Ω → B}
    (hraw : MeasurePreserving raw P ν) (hobs : Measurable obs)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hm : (∫ z,g z^2)=1) {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    (y : Position) :
    (fun sample => potentialOf (conditionalPacketDensity P raw obs g c r₀ s (obs sample)) y) =ᵐ[P]
      P[fun sample => potentialOf (rawPacketDensity g c r₀ s (raw sample)) y |
        MeasurableSpace.comap obs inferInstance] := by
  have he := ProbabilityTheory.condExp_ae_eq_integral_condDistrib hobs hraw.measurable.aemeasurable
    (measurable_rawPacketPotential hg hc hr hs y).stronglyMeasurable
    (hraw.integrable_comp_of_integrable (integrable_rawPacketPotential hg hgs hm hc hr hs ν y))
  exact (he.trans (Eventually.of_forall (fun sample =>
    (mixturePacketPotential hg hgs hm hc hr hs (ProbabilityTheory.condDistrib raw obs P (obs sample)) y).symm))).symm

theorem conditionalPacketPotential_event_tower {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure (Configuration n)) [IsFiniteMeasure ν]
    {raw : Ω → Configuration n} {obs : Ω → B}
    (hraw : MeasurePreserving raw P ν) (hobs : Measurable obs)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hm : (∫ z,g z^2)=1) {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    {A : Set Ω} (hA : MeasurableSet[MeasurableSpace.comap obs inferInstance] A)
    (y : Position) :
    (∫ sample in A, potentialOf (conditionalPacketDensity P raw obs g c r₀ s (obs sample)) y ∂P)=
      ∫ sample in A, potentialOf (rawPacketDensity g c r₀ s (raw sample)) y ∂P := by
  have hle := measurable_iff_comap_le.mp hobs
  have he := conditionalPacketPotential_eq_condExp P ν hraw hobs hg hgs hm hc hr hs y
  rw [setIntegral_congr_ae (hle _ hA) (he.mono (fun x hx _ => hx))]
  exact setIntegral_condExp hle
    (hraw.integrable_comp_of_integrable (integrable_rawPacketPotential hg hgs hm hc hr hs ν y)) hA

theorem physical_observation_potential_tower {n J : ℕ}
    (ν : Measure (Configuration n)) [IsProbabilityMeasure ν]
    (r : Fin J → ℝ) (j : ℕ) {g : Position → ℝ}
    (hg : Continuous g) (hgs : HasCompactSupport g) (hm : (∫ z,g z^2)=1)
    {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    {A : Set (ObservationSample n J)} (hA : MeasurableSet[observationSigma r j] A)
    (y : Position) :
    (∫ sample in A, potentialOf
      (conditionalPacketDensity (observationLaw J ν) Prod.fst (tailObservation r j)
        g c r₀ s (tailObservation r j sample)) y ∂observationLaw J ν)=
      ∫ sample in A, potentialOf (rawPacketDensity g c r₀ s sample.1) y ∂observationLaw J ν :=
  conditionalPacketPotential_event_tower (observationLaw J ν) ν (observationLaw_rawProjection ν)
    (measurable_tailObservation r j) hg hgs hm hc hr hs hA y

end NeutralAtom

end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_PhysicalBridge
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
noncomputable section
namespace NeutralAtom

lemma flattenConfiguration_measurePreserving (n : ℕ) :
    MeasurePreserving (flattenConfiguration n).toHomeomorph.toMeasurableEquiv :=
  (flattenConfiguration_symm_measurePreserving n).symm

lemma fromH1_mass {n : ℕ} (ψ : Coulomb.H1Vector n) :
    normSquared (fromH1Wave ψ) = Coulomb.mass ψ := by
  unfold normSquared Coulomb.mass fromH1Wave
  apply Finset.sum_congr rfl
  intro s _
  exact (flattenConfiguration_measurePreserving n).integral_comp' (fun x => ‖ψ.value s x‖^2)

end NeutralAtom

end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservationMatching
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
namespace NeutralAtom

lemma measurable_observationArrayPositions {H : Type*} {n : ℕ} (h : H) :
    Measurable (@observationArrayPositions H n h) := by
  unfold observationArrayPositions
  fun_prop

end NeutralAtom

end
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PhysicalLikelihoodBridge
attribute [-instance] _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
namespace NeutralAtom

lemma rawExpectation_eq_stateWeightedIntegral {n : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) {F : Configuration n → ℝ}
    (hF : Measurable F) {C : ℝ} (hC : ∀ x, ‖F x‖≤C) :
    rawExpectation ψ F=stateWeightedIntegral ψ F := by
  unfold rawExpectation configurationDensity stateWeightedIntegral
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum _ (fun σ _ =>
    (hψ σ).norm.integrable_sq.bdd_mul hF.aestronglyMeasurable
      (Eventually.of_forall hC))

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PhysicalRetainedLikelihood
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace NeutralAtom

lemma flattenIndexedNoise_preserving (n : ℕ) (H : Type*) [Fintype H] :
    MeasurePreserving (flattenIndexedNoise n H)
      (Measure.pi (fun _ : H => Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin 3 => observationNoiseLaw))))
      (Measure.pi (fun _ : H × (Fin n × Fin 3) => observationNoiseLaw)) := by
  refine ⟨(flattenIndexedNoise n H).measurable,?_⟩
  refine (Measure.pi_eq (fun v hv => ?_)).symm
  rw [MeasurableEquiv.map_apply]
  have he : (flattenIndexedNoise n H) ⁻¹' Set.univ.pi v=
      Set.univ.pi (fun j => Set.univ.pi (fun i => Set.univ.pi (fun a => v (j,i,a)))) := by
    ext u
    simp only [mem_preimage,Set.mem_pi,mem_univ,true_implies,flattenIndexedNoise,
      MeasurableEquiv.coe_mk,Equiv.coe_fn_mk]
    exact ⟨fun h j i a => h (j,i,a),fun h ⟨j,i,a⟩ => h j i a⟩
  rw [he]
  simp only [Measure.pi_pi,Fintype.prod_prod_type]

lemma retainedNoise_preserving (n J j : ℕ) :
    MeasurePreserving (@retainedNoise n J j) (allObservationNoiseLaw n J)
      (Measure.pi (fun _ : RetainedScales J j × (Fin n × Fin 3) => observationNoiseLaw)) := by
  have hp : MeasurePreserving
      (fun u : ObservationNoise n J => fun k : RetainedScales J j => u k.val)
      (allObservationNoiseLaw n J)
      (Measure.pi (fun _ : RetainedScales J j =>
        Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin 3 => observationNoiseLaw)))) :=
    measurePreserving_fst.comp (measurePreserving_piEquivPiSubtypeProd
      (fun _ : Fin J => Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin 3 => observationNoiseLaw)))
      (fun k : Fin J => j≤k.val))
  exact (flattenIndexedNoise_preserving n (RetainedScales J j)).comp hp

lemma measurable_retainedObservationData {n J : ℕ} (j : ℕ) (ℓ : RetainedScales J j → ℝ) :
    Measurable (@retainedObservationData n J j ℓ) := by
  unfold retainedObservationData
  fun_prop

lemma arrayEventLikelihood_retained_integral {n J : ℕ} (j : ℕ) (ℓ : RetainedScales J j → ℝ)
    (hℓ : ∀ h, ℓ h≠0) (B : Set ((RetainedScales J j × (Fin n × Fin 3)) → ℝ))
    (hB : MeasurableSet B) (x : Configuration n) :
    arrayEventLikelihood ℓ B x=
      ∫ u, B.indicator (fun _ => (1:ℝ)) (retainedObservationData j ℓ (x,u))
        ∂allObservationNoiseLaw n J := by
  have hm : Measurable (fun u : (RetainedScales J j × (Fin n × Fin 3)) → ℝ =>
      B.indicator (fun _ => (1:ℝ)) (fun ia => x ia.2.1 ia.2.2+ℓ ia.1*u ia)) :=
    (measurable_const.indicator hB).comp (by fun_prop)
  rw [arrayEventLikelihood_integral ℓ hℓ,←(retainedNoise_preserving n J j).map_eq]
  exact integral_map_of_stronglyMeasurable (retainedNoise_preserving n J j).measurable hm.stronglyMeasurable

theorem physical_retainedEvent_bayes_integral {n J : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ=1)
    (j : ℕ) (ℓ : RetainedScales J j → ℝ) (hℓ : ∀ k, ℓ k≠0)
    {B : Set ((RetainedScales J j × (Fin n × Fin 3)) → ℝ)} (hB : MeasurableSet B)
    {F : Configuration n → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ x, ‖F x‖≤C) :
    (∫ sample, (retainedObservationData j ℓ ⁻¹' B).indicator (fun z => F z.1) sample
      ∂observationLaw J (rawLaw ψ))=
    stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ B x*F x) := by
  let := rawLaw_isProbability hψ hn
  have hi : Integrable (fun z : ObservationSample n J => F z.1)
      (observationLaw J (rawLaw ψ)) :=
    (integrable_const C).mono' (hF.comp measurable_fst).aestronglyMeasurable
      (Eventually.of_forall (fun z => hC z.1))
  have hA := hB.preimage (measurable_retainedObservationData j ℓ)
  rw [observationLaw,integral_prod _ (hi.indicator hA)]
  have hi2 : (fun x : Configuration n => ∫ u,
      (retainedObservationData j ℓ ⁻¹' B).indicator (fun z => F z.1) (x,u)
        ∂allObservationNoiseLaw n J)=
      fun x => arrayEventLikelihood ℓ B x*F x := by
    funext x
    rw [arrayEventLikelihood_retained_integral j ℓ hℓ B hB x,←integral_mul_const]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by
      by_cases h : retainedObservationData j ℓ (x,u)∈B <;> simp [h]
  rw [hi2,integral_rawLaw hψ]
  apply rawExpectation_eq_stateWeightedIntegral (C:=C) hψ
    (((arrayEventLikelihood_contDiff ℓ hB).continuous.measurable).mul hF)
  intro x
  change ‖arrayEventLikelihood ℓ B x*F x‖≤C
  rw [norm_mul,Real.norm_of_nonneg (arrayEventLikelihood_nonneg ℓ hB x)]
  exact (mul_le_mul_of_nonneg_right (arrayEventLikelihood_le_one ℓ hB x)
    (norm_nonneg _)).trans (by simpa using hC x)
end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace NeutralAtom

lemma measurable_retainedTailObservation {n J : ℕ} (j : ℕ) :
    Measurable (@retainedTailObservation n J j) := by
  apply Measurable.of_eval
  intro k
  by_cases hk : j≤k.val
  · simpa only [retainedTailObservation,dite_eq_left hk,Function.comp_def] using
      measurable_forgetOrder.comp (measurable_observationArrayPositions (⟨k,hk⟩ : RetainedScales J j))
  · simpa only [retainedTailObservation,dite_eq_right hk] using
      (measurable_const : Measurable (fun _ : (RetainedScales J j × (Fin n × Fin 3)) → ℝ =>
        forgetOrder (0 : Configuration n)))

lemma retainedTailObservation_physical {n J : ℕ} (r : Fin J → ℝ)
    (j : ℕ) (sample : ObservationSample n J) :
    retainedTailObservation j (retainedObservationData j (fun k => (r k.val)^(101/100:ℝ)) sample)=
      tailObservation r j sample := by
  funext k
  by_cases hk : j≤k.val
  · simp only [retainedTailObservation,tailObservation,dite_eq_left hk,ite_eq_left hk,observedArray]
    congr 1
    funext i
    ext a
    simp [observationArrayPositions,retainedObservationData,observedOrdered,
      observationNoiseVector_coordinate]
  · simp only [retainedTailObservation,tailObservation,dite_eq_right hk,ite_eq_right hk]

lemma physical_retainedTailEvent_bayes_integral {n J : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ=1)
    (r : Fin J → ℝ) (hr : ∀ k, 0 < r k) (j : ℕ)
    {B : Set (Fin J → UnorderedArray n)} (hB : MeasurableSet B)
    {F : Configuration n → ℝ} (hF : Measurable F) {C : ℝ}
    (hC : ∀ x, ‖F x‖≤C) :
    (∫ sample, (tailObservation r j ⁻¹' B).indicator (fun z => F z.1) sample
      ∂observationLaw J (rawLaw ψ))=
    stateWeightedIntegral ψ (fun x =>
      arrayEventLikelihood (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ))
        (retainedTailObservation j ⁻¹' B) x*F x) := by
  have he : retainedObservationData j (fun k => (r k.val)^(101/100:ℝ)) ⁻¹'
      (retainedTailObservation j ⁻¹' B)=tailObservation r j ⁻¹' B := by
    ext sample
    simp only [mem_preimage,retainedTailObservation_physical]
  rw [←he]
  exact physical_retainedEvent_bayes_integral hψ hn j _
    (fun k => (Real.rpow_pos_of_pos (hr k.val) _).ne')
    (hB.preimage (measurable_retainedTailObservation j)) hF hC

lemma physical_retainedTailEvent_probability {n J : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ=1)
    (r : Fin J → ℝ) (hr : ∀ k, 0 < r k) (j : ℕ)
    {B : Set (Fin J → UnorderedArray n)} (hB : MeasurableSet B) :
    (observationLaw J (rawLaw ψ)).real (tailObservation r j ⁻¹' B)=
    stateWeightedIntegral ψ (arrayEventLikelihood (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ))
      (retainedTailObservation j ⁻¹' B)) := by
  have H := physical_retainedTailEvent_bayes_integral hψ hn r hr j hB
    (measurable_const : Measurable (fun _ : Configuration n => (1:ℝ)))
    (C:=1) (fun _ => by simp)
  simpa only [integral_indicator_const _ (hB.preimage (measurable_tailObservation r j)),
    smul_eq_mul,mul_one] using H

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_RetainedPotentialMean
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace NeutralAtom

lemma fromH1_raw_bounded_integral {n : ℕ} (u : Coulomb.H1Vector n)
    {F : Configuration n → ℝ} (hF : Measurable F) {C : ℝ} (hC : ∀ x, ‖F x‖≤C) :
    (∫ x,F x ∂rawLaw (fromH1Wave u))=
      Coulomb.potentialForm (fun x => F ((flattenConfiguration n).symm x)) u := by
  have hu (σ : Spins n) : MemLp (fromH1Wave u σ) 2 volume :=
    (u.value_L2 σ).comp_measurePreserving (flattenConfiguration_measurePreserving n)
  rw [integral_rawLaw hu,rawExpectation_eq_stateWeightedIntegral hu hF hC]
  unfold stateWeightedIntegral Coulomb.potentialForm
  apply Finset.sum_congr rfl
  intro σ _
  have H := (flattenConfiguration_measurePreserving n).integral_comp'
    (fun x => F ((flattenConfiguration n).symm x)*‖u.value σ x‖^2)
  change (∫ x : Configuration n, F ((flattenConfiguration n).symm (flattenConfiguration n x))*
    ‖fromH1Wave u σ x‖^2)=_ at H
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using H

theorem retainedEvent_potential_mean {n J : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ=1)
    (r : Fin J → ℝ) (hr : ∀ k, 0 < r k) (j : ℕ)
    {B : Set (Fin J → UnorderedArray n)} (hB : MeasurableSet B)
    (u : Coulomb.H1Vector n) (hum : Coulomb.mass u=1)
    (hlaw : ∀ F : Coulomb.Configuration n → ℝ, Coulomb.potentialForm F u=
      (stateWeightedIntegral ψ (arrayEventLikelihood
        (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ)) (retainedTailObservation j ⁻¹' B)))⁻¹*
      stateWeightedIntegral ψ (fun x => arrayEventLikelihood
        (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ)) (retainedTailObservation j ⁻¹' B) x*
        F (flattenConfiguration n x)))
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) (hm : (∫ z,g z^2)=1)
    {c r₀ s : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s) (y : Position) :
    letI := rawLaw_isProbability hψ hn
    potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y=
      ((observationLaw J (rawLaw ψ)).real (tailObservation r j ⁻¹' B))⁻¹*
        ∫ z in tailObservation r j ⁻¹' B,
          potentialOf (conditionalPacketDensity (observationLaw J (rawLaw ψ)) Prod.fst
            (tailObservation r j) g c r₀ s (tailObservation r j z)) y ∂observationLaw J (rawLaw ψ) := by
  let := rawLaw_isProbability hψ hn
  have hu (σ : Spins n) : MemLp (fromH1Wave u σ) 2 volume :=
    (u.value_L2 σ).comp_measurePreserving (flattenConfiguration_measurePreserving n)
  have := rawLaw_isProbability hu ((fromH1_mass u).trans hum)
  obtain ⟨C,hC,H⟩ := rawPacketPotential_uniform (n:=n) hg hgs hm hc hr₀ hs
  have hF := measurable_rawPacketPotential (n:=n) hg hc hr₀ hs y
  have hbound (x : Configuration n) : ‖potentialOf (rawPacketDensity g c r₀ s x) y‖≤C := by
    rw [Real.norm_of_nonneg (H x y).2.1]
    exact (H x y).2.2
  rw [mixturePacketPotential hg hgs hm hc hr₀ hs,fromH1_raw_bounded_integral u hF hbound,hlaw]
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  rw [←physical_retainedTailEvent_probability hψ hn r hr j hB,
    ←physical_retainedTailEvent_bayes_integral hψ hn r hr j hB hF hbound,
    integral_indicator (hB.preimage (measurable_tailObservation r j))]
  congr 1
  exact (physical_observation_potential_tower (rawLaw ψ) r j hg hgs hm hc hr₀ hs
    (show MeasurableSet[observationSigma r j] (tailObservation r j ⁻¹' B) from ⟨B,hB,rfl⟩) y).symm

lemma conditionalPacketPotential_integrable {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure (Configuration n)) [IsFiniteMeasure ν]
    {raw : Ω → Configuration n} {obs : Ω → B}
    (hraw : MeasurePreserving raw P ν) (hobs : Measurable obs)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hm : (∫ z,g z^2)=1) {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s)
    (y : Position) :
    Integrable (fun sample => potentialOf (conditionalPacketDensity P raw obs g c r₀ s (obs sample)) y) P :=
  (integrable_condExp (f:=fun sample => potentialOf (rawPacketDensity g c r₀ s (raw sample)) y)).congr
    (conditionalPacketPotential_eq_condExp P ν hraw hobs hg hgs hm hc hr hs y).symm

lemma normalized_event_const_sub {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {A : Set Ω} {f : Ω → ℝ} (hi : Integrable f P)
    (hp : 0<P.real A) (C : ℝ) :
    (P.real A)⁻¹*(∫ x in A,C-f x ∂P)=C-(P.real A)⁻¹*(∫ x in A,f x ∂P) := by
  rw [integral_sub (integrable_const C) hi.integrableOn,integral_const]
  simp only [smul_eq_mul,measureReal_restrict_apply_univ]
  rw [mul_sub,←mul_assoc,inv_mul_cancel₀ hp.ne',one_mul]

lemma normalized_event_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {A : Set Ω} (hA : MeasurableSet A) {f : Ω → ℝ}
    (hi : Integrable f P) (hp : 0<P.real A) {v : ℝ}
    (hb : ∀ᵐ x ∂P, x∈A → f x≤v) :
    (P.real A)⁻¹*(∫ x in A,f x ∂P)≤v := by
  have h := setIntegral_mono_ae_restrict hi.integrableOn (integrable_const v)
    ((ae_restrict_iff' hA).mpr hb)
  rw [integral_const] at h
  simp only [smul_eq_mul,measureReal_restrict_apply_univ] at h
  have hh := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hp.le)
  simpa only [←mul_assoc,inv_mul_cancel₀ hp.ne',one_mul] using hh

lemma le_normalized_event {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {A : Set Ω} (hA : MeasurableSet A) {f : Ω → ℝ}
    (hi : Integrable f P) (hp : 0<P.real A) {v : ℝ}
    (hb : ∀ᵐ x ∂P, x∈A → v≤f x) :
    v≤(P.real A)⁻¹*(∫ x in A,f x ∂P) := by
  have h := setIntegral_mono_ae_restrict (integrable_const v) hi.integrableOn
    ((ae_restrict_iff' hA).mpr hb)
  rw [integral_const] at h
  simp only [smul_eq_mul,measureReal_restrict_apply_univ] at h
  have hh := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hp.le)
  simpa only [←mul_assoc,inv_mul_cancel₀ hp.ne',one_mul] using hh

theorem retainedEvent_field_mean {n J : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hn : normSquared ψ=1)
    (r : Fin J → ℝ) (hr : ∀ k, 0 < r k) (j : ℕ)
    {B : Set (Fin J → UnorderedArray n)} (hB : MeasurableSet B)
    (u : Coulomb.H1Vector n) (hum : Coulomb.mass u=1)
    (hlaw : ∀ F : Coulomb.Configuration n → ℝ, Coulomb.potentialForm F u=
      (stateWeightedIntegral ψ (arrayEventLikelihood
        (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ)) (retainedTailObservation j ⁻¹' B)))⁻¹*
      stateWeightedIntegral ψ (fun x => arrayEventLikelihood
        (fun k : RetainedScales J j => (r k.val)^(101/100:ℝ)) (retainedTailObservation j ⁻¹' B) x*
        F (flattenConfiguration n x)))
    (hp : 0<(observationLaw J (rawLaw ψ)).real (tailObservation r j ⁻¹' B))
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) (hm : (∫ z,g z^2)=1)
    {c r₀ s : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s) (y : Position) (V : ℝ) :
    letI := rawLaw_isProbability hψ hn
    V-potentialOf (mixturePacketDensity (rawLaw (fromH1Wave u)) g c r₀ s) y=
      ((observationLaw J (rawLaw ψ)).real (tailObservation r j ⁻¹' B))⁻¹*
        ∫ z in tailObservation r j ⁻¹' B,
          V-potentialOf (conditionalPacketDensity (observationLaw J (rawLaw ψ)) Prod.fst
            (tailObservation r j) g c r₀ s (tailObservation r j z)) y ∂observationLaw J (rawLaw ψ) := by
  let := rawLaw_isProbability hψ hn
  rw [normalized_event_const_sub
    (conditionalPacketPotential_integrable (observationLaw J (rawLaw ψ)) (rawLaw ψ)
      (observationLaw_rawProjection _) (measurable_tailObservation r j) hg hgs hm hc hr₀ hs y) hp]
  rw [retainedEvent_potential_mean hψ hn r hr j hB u hum hlaw hg hgs hm hc hr₀ hs y]

end NeutralAtom

end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_InverseErrorScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace NeutralAtom

lemma exists_uniform_inner_scale {f : ℝ → ℝ} (hf : Tendsto f (𝓝[>] 0) (𝓝 0))
    {A ε : ℝ} (hA : 0<A) (hε : 0<ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ {s a : ℝ}, 0 < s → s < s₀ → 0<a → a≤A*s → f a<ε := by
  obtain ⟨d,hd,Hd⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (hf.eventually (gt_mem_nhds hε))
  refine ⟨d/A,div_pos hd hA,?_⟩
  intro s a _ hss ha has
  apply Hd
  refine ⟨ha,has.trans_lt ?_⟩
  have h := (lt_div_iff₀ hA).mp hss
  simpa only [mul_comm] using h

lemma inverseResponseError_majorizes {D F K κ L M a v ell m : ℝ}
    (hD : 0≤D) (hF : 0≤F) (hK : 0≤K) (hκ : 0<κ) (hL : 0≤L) (_ : 0≤M)
    (ha : 0<a) (hv : κ*a^(1+packetExponent)≤v) (hell : ell≤L*a^(101/100:ℝ))
    (hm : m≤M*a^(-3:ℝ)) (hell0 : 0≤ell) (hm0 : 0 ≤ m) :
    Real.sqrt (D/v^5*a^(-699/100:ℝ))+
      (F/v^4*(2*a^(6/5:ℝ))+K/v^4*(Real.sqrt 3*ell))*m≤
        inverseResponseError D F K κ L M a := by
  have hv0 : 0<κ*a^(1+packetExponent) := by positivity
  unfold inverseResponseError
  gcongr

lemma inverseResponseError_expansion {D F K κ L M a : ℝ}
    (hD : 0≤D) (hκ : 0<κ) (ha : 0<a) :
    inverseResponseError D F K κ L M a*a^6=
      Real.sqrt (D/κ^5)*a^(1/200-5*packetExponent/2)+
      (2*F*M/κ^4)*a^(1/5-4*packetExponent)+
      (K*Real.sqrt 3*L*M/κ^4)*a^(1/100-4*packetExponent) := by
  have hpow (n : ℕ) : (κ*a^(1+packetExponent))^n=κ^n*a^((1+packetExponent)*n) := by
    rw [mul_pow,Real.rpow_mul_natCast ha.le]
  have hfirst : D/(κ*a^(1+packetExponent))^5*a^(-699/100:ℝ)=
      (D/κ^5)*a^(-(1+packetExponent)*5-699/100) := by
    rw [hpow]
    calc
      _ = (D/κ^5)*(a^(-699/100:ℝ)/a^((1+packetExponent)*5)) := by ring_nf
      _ = _ := by rw [←Real.rpow_sub ha]; congr 2; ring
  have hfrac : (κ*a^(1+packetExponent))^4=κ^4*a^((1+packetExponent)*4) := hpow 4
  unfold inverseResponseError
  rw [hfirst,Coulomb.sqrt_rpow_monomial ha (div_nonneg hD (pow_nonneg hκ.le _)),hfrac]
  have hterm₁ : (Real.sqrt (D/κ^5)*a^((-(1+packetExponent)*5-699/100)/2))*a^6=
      Real.sqrt (D/κ^5)*a^(1/200-5*packetExponent/2) := by
    rw [←Real.rpow_natCast a 6,mul_assoc,←Real.rpow_add ha]
    congr 2; ring
  have hterm₂ : (F/(κ^4*a^((1+packetExponent)*4))*(2*a^(6/5:ℝ)))*(M*a^(-3:ℝ))*a^6=
      (2*F*M/κ^4)*a^(1/5-4*packetExponent) := by
    calc
      _ = (2*F*M/κ^4)*((a^(6/5:ℝ)*a^(-3:ℝ)*a^6)/a^((1+packetExponent)*4)) := by ring
      _ = _ := by
        rw [←Real.rpow_natCast a 6,←Real.rpow_add ha,←Real.rpow_add ha,←Real.rpow_sub ha]
        congr 2; ring
  have hterm₃ : (K/(κ^4*a^((1+packetExponent)*4))*(Real.sqrt 3*(L*a^(101/100:ℝ))))*(M*a^(-3:ℝ))*a^6=
      (K*Real.sqrt 3*L*M/κ^4)*a^(1/100-4*packetExponent) := by
    calc
      _ = (K*Real.sqrt 3*L*M/κ^4)*((a^(101/100:ℝ)*a^(-3:ℝ)*a^6)/a^((1+packetExponent)*4)) := by ring
      _ = _ := by
        rw [←Real.rpow_natCast a 6,←Real.rpow_add ha,←Real.rpow_add ha,←Real.rpow_sub ha]
        congr 2; ring
  rw [add_mul,add_mul,add_mul,hterm₁,hterm₂,hterm₃]
  ring

lemma inverseResponseError_scaled_tendsto {D κ : ℝ} (hD : 0≤D) (hκ : 0<κ)
    (F K L M : ℝ) :
    Tendsto (fun a => inverseResponseError D F K κ L M a*a^6) (𝓝[>] 0) (𝓝 0) := by
  have H := (((tendsto_positive_rpow_zero (by norm_num [packetExponent] :
      (0:ℝ)<1/200-5*packetExponent/2)).const_mul (Real.sqrt (D/κ^5))).add
    ((tendsto_positive_rpow_zero (by norm_num [packetExponent] :
      (0:ℝ)<1/5-4*packetExponent)).const_mul (2*F*M/κ^4))).add
    ((tendsto_positive_rpow_zero (by norm_num [packetExponent] :
      (0:ℝ)<1/100-4*packetExponent)).const_mul (K*Real.sqrt 3*L*M/κ^4))
  simp only [mul_zero,add_zero] at H
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (inverseResponseError_expansion hD hκ ha).symm

lemma lower_width_div_pow {a v κ : ℝ} (ha : 0<a) (hκ : 0<κ)
    (hv : κ*a^(1+packetExponent)≤v) (p : ℝ) (n : ℕ) :
    a^p/v^n≤(1/κ^n)*a^(p-(1+packetExponent)*n) := by
  have hbase : 0<κ*a^(1+packetExponent) := by positivity
  calc
    _ ≤ a^p/(κ*a^(1+packetExponent))^n := div_le_div_of_nonneg_left
      (Real.rpow_nonneg ha.le _) (pow_pos hbase _) (pow_le_pow_left₀ hbase.le hv n)
    _ = _ := by
      rw [mul_pow,←Real.rpow_mul_natCast ha.le,Real.rpow_sub ha]
      ring

lemma inverseHighMeanError_bound {H B γ κ N a v L G : ℝ}
    (hH : 0≤H) (hB : 0≤B) (hγ : 0<γ) (hκ : 0<κ) (_ : 0≤N)
    (ha : 0<a) (hv : κ*a^(1+packetExponent)≤v) (hL : 0≤L) (hLH : L≤H/a^4)
    (hG : G≤2*a^(-349/50:ℝ)) :
    ((L/a^(-699/100:ℝ)+2*(B/v^3)/(γ/a^6))*G+
        2*(N*(2*v/a))*(a^4)⁻¹)*a^4 ≤ inverseHighMeanError H B γ κ N a v := by
  have hv0 : 0<v := (by positivity : 0<κ*a^(1+packetExponent)).trans_le hv
  have he : 0≤L/a^(-699/100:ℝ)+2*(B/v^3)/(γ/a^6) := by positivity
  have hcap := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG he) (pow_nonneg ha.le 4)
  have hLcap : (L/a^(-699/100:ℝ))*(2*a^(-349/50:ℝ))*a^4≤
      2*H*a^(1/100:ℝ) := by
    calc
      _ ≤ ((H/a^4)/a^(-699/100:ℝ))*(2*a^(-349/50:ℝ))*a^4 := by gcongr
      _ = _ := by
        have hrat : a^(-349/50:ℝ)/a^(-699/100:ℝ)=a^(1/100:ℝ) := by
          rw [←Real.rpow_sub ha]; norm_num
        field_simp [ha.ne'] at hrat ⊢
        nlinarith
  have hBcap : (2*(B/v^3)/(γ/a^6))*(2*a^(-349/50:ℝ))*a^4≤
      (4*B/(γ*κ^3))*a^(1/50-3*packetExponent) := by
    have hp : (a^6*a^(-349/50:ℝ)*a^4)=a^(151/50:ℝ) := by
      rw [←Real.rpow_natCast a 6,←Real.rpow_natCast a 4,←Real.rpow_add ha,←Real.rpow_add ha]
      norm_num
    calc
      _ = (4*B/γ)*(a^(151/50:ℝ)/v^3) := by rw [←hp]; field_simp; ring
      _ ≤ (4*B/γ)*((1/κ^3)*a^(151/50-(1+packetExponent)*3)) :=
        mul_le_mul_of_nonneg_left (lower_width_div_pow ha hκ hv _ _) (by positivity)
      _ = _ := by
        rw [show (151/50:ℝ)-(1+packetExponent)*3=1/50-3*packetExponent by ring]
        ring
  have hlast : (2*(N*(2*v/a))*(a^4)⁻¹)*a^4=4*N*(v/a) := by field_simp; ring
  unfold inverseHighMeanError
  rw [add_mul,hlast]
  have hh : (L/a^(-699/100:ℝ)+2*(B/v^3)/(γ/a^6))*G*a^4≤
      2*H*a^(1/100:ℝ)+(4*B/(γ*κ^3))*a^(1/50-3*packetExponent) := by
    apply hcap.trans
    rw [add_mul,add_mul]
    exact add_le_add hLcap hBcap
  exact add_le_add hh le_rfl

lemma inverseHighMeanError_uniform {H B γ κ N A V ε : ℝ}
    (hA : 0<A) (hN : 0≤N) (hε : 0<ε) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ {s a v : ℝ}, 0 < s → s < s₀ → 0<a → a≤A*s →
      v/a≤V*s^packetExponent → inverseHighMeanError H B γ κ N a v<ε := by
  have ht := ((tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<1/100)).const_mul (2*H)).add
    ((tendsto_positive_rpow_zero (by norm_num [packetExponent] : (0:ℝ)<1/50-3*packetExponent)).const_mul (4*B/(γ*κ^3)))
  simp only [mul_zero,add_zero] at ht
  obtain ⟨s₁,hs₁,Hs₁⟩ := exists_uniform_inner_scale ht hA (by linarith : 0<ε/2)
  have ht' := (tendsto_positive_rpow_zero (by norm_num [packetExponent] : 0<packetExponent)).const_mul (4*N*V)
  simp only [mul_zero] at ht'
  obtain ⟨s₂,hs₂,Hs₂⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (ht'.eventually (gt_mem_nhds (by linarith : 0<ε/2)))
  refine ⟨min s₁ s₂,lt_min hs₁ hs₂,?_⟩
  intro s a v hs hss ha has hv
  have h1 := Hs₁ hs (hss.trans_le (min_le_left _ _)) ha has
  have h2 := Hs₂ ⟨hs,hss.trans_le (min_le_right _ _)⟩
  change 4*N*V*s^packetExponent < ε/2 at h2
  have h3 := mul_le_mul_of_nonneg_left hv (show 0≤4*N by positivity)
  unfold inverseHighMeanError
  nlinarith

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_InverseGeometry
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

lemma physical_inverse_width_geometry {c r₀ r s A : ℝ} {y : Position}
    (hc : 0 < c) (hr₀ : 0 < r₀) (hr : 0 < r) (hs : 0 < s) (hA : 0 < A)
    (hr₀y : r₀ ≤ ‖y‖) (hry : r ≤ ‖y‖) (hya : Coulomb.atomicCellScale y ≤ A*r) (hrs : r ≤ s) :
    (c*100000/(max 1 A)^packetExponent)*(Coulomb.atomicCellScale y)^(1+packetExponent) ≤
      packetWidth c r₀ s y ∧
    packetWidth c r₀ s y/Coulomb.atomicCellScale y ≤ (100000*c)*s^packetExponent ∧
    r^(101/100:ℝ) ≤ 100000^(101/100:ℝ)*(Coulomb.atomicCellScale y)^(101/100:ℝ) := by
  let a := Coulomb.atomicCellScale y
  have hd : 0 < ‖y‖ := hr.trans_le hry
  have ha : 0 < a := by dsimp [a,Coulomb.atomicCellScale]; positivity
  have he : ‖y‖=100000*a := by dsimp [a,Coulomb.atomicCellScale]; ring
  have hmax : 0 < max 1 A := lt_max_of_lt_left (by norm_num)
  have hma : a/(max 1 A) ≤ min ‖y‖ s := by
    apply le_min
    · rw [div_le_iff₀ hmax,he]
      nlinarith [le_max_left (1:ℝ) A]
    · rw [div_le_iff₀ hmax]
      have H := hya.trans (mul_le_mul_of_nonneg_left hrs hA.le)
      exact H.trans (by nlinarith [le_max_right (1:ℝ) A])
  have hwEq : packetWidth c r₀ s y=c*‖y‖*(min ‖y‖ s)^packetExponent := by
    simp only [packetWidth,max_eq_left hr₀y]
  constructor
  · have H := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (div_nonneg ha.le hmax.le) hma (by norm_num [packetExponent] : 0 ≤ packetExponent))
      (show 0 ≤ c*‖y‖ by positivity)
    rw [←hwEq,Real.div_rpow ha.le hmax.le] at H
    apply le_trans _ H
    rw [he,Real.rpow_add ha,Real.rpow_one]
    ring_nf
    exact le_rfl
  constructor
  · have H := packetWidth_le c r₀ s hc.le hr₀ hs y
    rw [max_eq_left hr₀y,he] at H
    apply (div_le_iff₀ ha).mpr
    exact H.trans_eq (by ring)
  · have H := Real.rpow_le_rpow hr.le hry (by norm_num : (0:ℝ) ≤ 101/100)
    rw [he,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 100000) ha.le] at H
    exact H

lemma physical_inverse_count_rescale {K A r a : ℝ} (hK : 0 ≤ K) (hA : 0 < A)
    (hr : 0 < r) (ha : 0 < a) (h : a ≤ A*r) : K/r^3 ≤ (K*A^3)*a^(-3:ℝ) := by
  rw [show a^(-3:ℝ)=(a^3)⁻¹ by rw [Real.rpow_neg ha.le]; norm_num]
  rw [←div_eq_mul_inv,div_le_div_iff₀ (pow_pos hr 3) (pow_pos ha 3)]
  have H : a^3 ≤ (A*r)^3 :=
    (pow_le_pow_iff_left₀ ha.le (mul_nonneg hA.le hr.le) (by norm_num : (3 : ℕ) ≠ 0)).mpr h
  rw [mul_pow] at H
  nlinarith [mul_le_mul_of_nonneg_left H hK]
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_NormalizedBandModulus
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace NeutralAtom

lemma inverse_count_ball_subset {c r₀ s r L : ℝ} {y : Position}
    (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s) (hr : 0 < r) (hL : 1 ≤ L)
    (hr₀r : r₀ ≤ r) (hy0 : r ≤ ‖y‖) (hy1 : ‖y‖ ≤ 4*L*r)
    (hw : c*s^packetExponent ≤ 1/100) (ha : (Coulomb.atomicCellScale y)^(6/5:ℝ) ≤ Coulomb.atomicCellScale y)
    (he : Real.sqrt 3*r^(101/100:ℝ) ≤ r/12) :
    Metric.closedBall y (2*packetWidth c r₀ s y+2*(Coulomb.atomicCellScale y)^(6/5:ℝ)+
      2*(Real.sqrt 3*r^(101/100:ℝ))) ⊆
        {z : Position | r/4 ≤ ‖z‖ ∧ ‖z‖ ≤ 12*L*r} := by
  have hwidth : packetWidth c r₀ s y ≤ ‖y‖/100 := by
    have H := packetWidth_le c r₀ s hc.le hr₀ hs y
    rw [max_eq_left (hr₀r.trans hy0)] at H
    exact H.trans ((mul_le_mul_of_nonneg_right hw (norm_nonneg y)).trans_eq (by ring))
  have ha' : 2*(Coulomb.atomicCellScale y)^(6/5:ℝ) ≤ ‖y‖/100 := by
    dsimp [Coulomb.atomicCellScale] at ha ⊢
    linarith
  intro z hz
  have hdist : ‖z-y‖ ≤ 3*‖y‖/100+r/6 := by
    have H : ‖z-y‖ ≤ 2*packetWidth c r₀ s y+2*(Coulomb.atomicCellScale y)^(6/5:ℝ)+
        2*(Real.sqrt 3*r^(101/100:ℝ)) := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
    linarith
  have hz' := norm_le_norm_add_norm_sub y z
  have hy' := norm_le_norm_add_norm_sub z y
  rw [norm_sub_rev y z] at hz'
  have hLr := mul_le_mul_of_nonneg_right hL hr.le
  constructor <;> nlinarith
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_PatchResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
noncomputable section
namespace Coulomb

lemma tfScalarDensity_nonneg (v : ℝ) : 0≤tfScalarDensity v := by
  unfold tfScalarDensity
  have hc := thomasFermiKineticConstant_pos
  positivity

lemma tfScalarDensity_mono : Monotone tfScalarDensity := by
  intro v w hvw
  have hc := thomasFermiKineticConstant_pos
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  apply div_le_div_of_nonneg_right (max_le_max_right 0 hvw)
  exact mul_nonneg thomasFermiKineticConstant_pos.le (by norm_num)

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_ThomasFermi_TFResponseMargins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

lemma tfScalarDensity_continuous : Continuous tfScalarDensity := by
  unfold tfScalarDensity
  exact (Real.continuous_rpow_const (by norm_num : (0:ℝ)≤3/2)).comp
    ((continuous_id.max continuous_const).div_const _)

lemma tfScalarDensity_strict {v w : ℝ} (hv : 0≤v) (hvw : v<w) :
    tfScalarDensity v<tfScalarDensity w := by
  unfold tfScalarDensity
  rw [max_eq_left hv,max_eq_left (hv.trans hvw.le)]
  apply Real.rpow_lt_rpow (div_nonneg hv (mul_nonneg thomasFermiKineticConstant_pos.le (by norm_num))) _ (by norm_num)
  exact (div_lt_div_iff_of_pos_right (mul_pos thomasFermiKineticConstant_pos (by norm_num))).mpr hvw

theorem exists_tf_response_margins {hl hh η : ℝ} (hη : 0<η) (hηl : η<hl)
    (hlh : hl≤hh) : ∃ ε : ℝ, 0<ε ∧ ε≤1 ∧
    ∀ {h θ δ e : ℝ}, h∈Icc hl hh → 0≤θ → θ≤ε → 0≤δ → δ≤ε → 0≤e → e≤ε →
      tfScalarDensity (h-η+θ)*(1+δ)+e<tfScalarDensity h ∧
      tfScalarDensity h<tfScalarDensity (h+η-θ)*(1-δ)-e := by
  have hlo : 0<hl := hη.trans hηl
  have hcontL : Continuous (fun h => tfScalarDensity h-tfScalarDensity (h-η/2)) :=
    tfScalarDensity_continuous.sub (tfScalarDensity_continuous.comp (continuous_id.sub continuous_const))
  have hcontU : Continuous (fun h => tfScalarDensity (h+η/2)-tfScalarDensity h) :=
    (tfScalarDensity_continuous.comp (continuous_id.add continuous_const)).sub tfScalarDensity_continuous
  obtain ⟨minPoint,hminPoint,Hd₁⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hlh) hcontL.continuousOn
  let d₁ := tfScalarDensity minPoint-tfScalarDensity (minPoint-η/2)
  have hd₁ : 0<d₁ :=
    sub_pos.mpr (tfScalarDensity_strict (by linarith [hminPoint.1]) (by linarith))
  obtain ⟨d₂,hd₂,Hd₂⟩ := isCompact_Icc.exists_forall_le' hcontU.continuousOn
    (a:=0) (s:=Icc hl hh) (fun h hh' => sub_pos.mpr (tfScalarDensity_strict (by linarith [hh'.1]) (by linarith)))
  let A := tfScalarDensity (hh+η)
  have hA : 0≤A := tfScalarDensity_nonneg _
  let ε := min 1 (min (η/2) (min (d₁/(2*(A+1))) (d₂/(2*(A+1)))))
  have hε : 0<ε := by dsimp [ε]; positivity
  refine ⟨ε,hε,min_le_left _ _,?_⟩
  intro h θ δ e hh' hθ hθε hδ hδε he heε
  have hεη : ε≤η/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hεd₁ : ε≤d₁/(2*(A+1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεd₂ : ε≤d₂/(2*(A+1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hd₁' := (le_div_iff₀ (show 0<2*(A+1) by positivity)).mp hεd₁
  have hd₂' := (le_div_iff₀ (show 0<2*(A+1) by positivity)).mp hεd₂
  have hb₁ : tfScalarDensity (h-η+θ)≤tfScalarDensity (h-η/2) := tfScalarDensity_mono (by linarith)
  have hb₂ : tfScalarDensity (h+η/2)≤tfScalarDensity (h+η-θ) := tfScalarDensity_mono (by linarith)
  have hc₁ : tfScalarDensity (h-η+θ)≤A := tfScalarDensity_mono (by linarith [hh'.2])
  have hc₂ : tfScalarDensity (h+η-θ)≤A := tfScalarDensity_mono (by linarith [hh'.2])
  have herr₁ := mul_le_mul hc₁ hδε hδ hA
  have herr₂ := mul_le_mul hc₂ hδε hδ hA
  have hg₁ : d₁≤tfScalarDensity h-tfScalarDensity (h-η/2) := Hd₁ hh'
  have hg₂ := Hd₂ h hh'
  constructor <;> nlinarith
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_PhysicalRetainedMean
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
namespace NeutralAtom

theorem physical_retained_inverse_means (g₀ : 𝓢(Position,ℝ))
    (hg : ∀ z, 1<‖z‖ → g₀ z=0) (hm : (∫ z,g₀ z^2)=1)
    (hrad : ∀ z,g₀ z=g₀ (EuclideanSpace.single 0 ‖z‖)) :
    ∃ C D₁ E₁ F K N₁ B₀ : ℝ,
      0<C ∧ 0<D₁ ∧ 0<E₁ ∧ 0<F ∧ 0<K ∧ 0<N₁ ∧ 0<B₀ ∧
    ∀ {D c A ε : ℝ}, 0 ≤ D → 0 < c → 0<A → 0<ε →
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧
    ∀ {N J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)), FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h) →
    ∀ {E : ℝ}, (E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D → ∀ {r₀ s : ℝ}, 0 < r₀ → 0 < s → s < s₀ →
    c*(1+packetExponent)*s^packetExponent ≤ 1/4 →
    ∀ (j : ℕ), r₀*2^j ≤ s →
    ∀ {B : Set (Fin J → UnorderedArray (N+1))}, MeasurableSet B →
    (r₀*2^j)^42 ≤ (observationLaw J (rawLaw ψ)).real
      (tailObservation (fun k : Fin J => r₀*2^k.val) j ⁻¹' B) →
    ∀ (k : RetainedScales J j) (y : Position) (_ : y≠0), r₀ ≤ ‖y‖ →
    Coulomb.atomicCellScale y ≤ A*(r₀*2^j) →
    letI := rawLaw_isProbability hd.2.2.1 hn
    let a := Coulomb.atomicCellScale y
    let b := a^(6/5:ℝ)
    let w := packetWidth c r₀ s y
    let ell := (r₀*2^k.val.val)^(101/100:ℝ)
    let θ := C*(2*w/a)
    let δ := E₁*(c*(1+packetExponent)*s^packetExponent)
    let field := fun z : ObservationSample (N+1) J => (Z:ℝ)*coulombKernel y-
      potentialOf (conditionalPacketDensity (observationLaw J (rawLaw ψ)) Prod.fst
        (tailObservation (fun l : Fin J => r₀*2^l.val) j) g₀ c r₀ s
        (tailObservation (fun l : Fin J => r₀*2^l.val) j z)) y
    let event := tailObservation (fun l : Fin J => r₀*2^l.val) j ⁻¹' B
    let fieldMean := ((observationLaw J (rawLaw ψ)).real event)⁻¹*
      ∫ z in event, field z ∂observationLaw J (rawLaw ψ)
    ∀ {M Qlo Qhi q L U : ℝ}, 18*b ≤ a → 2*w ≤ a →
    (∀ z∈retainedTailObservation j ⁻¹' B,
      Qlo ≤ ∑ i,packetKernel g₀ c r₀ s (observationArrayPositions k z i) y) →
    (∀ z∈retainedTailObservation j ⁻¹' B,
      (∑ i,packetKernel g₀ c r₀ s (observationArrayPositions k z i) y) ≤ Qhi) →
    (∀ z∈retainedTailObservation j ⁻¹' B,
      rawCount (Metric.closedBall y (2*w+2*b+2*(Real.sqrt 3*ell)))
        (observationArrayPositions k z) ≤ M) →
    0 ≤ L → 0 ≤ U → 0<q → θ ≤ 1 →
    let e := Real.sqrt ((D₁/w^5)*q)+(F/w^4*(2*b)+K/w^4*(Real.sqrt 3*ell))*M
    (∀ {P : ℝ}, 0<P → N₁*(2*w/a) ≤ 1/2 →
      P ≤ Qlo-(B₀/w^4)*(Real.sqrt 3*ell+2*b)*M →
      Coulomb.tfScalarDensity (L+θ*(a^4)⁻¹)*(1+δ)+e<Qlo →
      L-(L/q+2*(B₀/w^3)/P)*(2*a^(-349/50:ℝ))-
        2*(N₁*(2*w/a))*(a^4)⁻¹-ε*a^(-4:ℝ) ≤ fieldMean) ∧
    (Qhi<Coulomb.tfScalarDensity (U-θ*(a^4)⁻¹)*(1-δ)-e →
      fieldMean ≤ U+((Coulomb.tfInteriorConstant Coulomb.thomasFermiKineticConstant/a^4)/q)*
        (2*a^(-349/50:ℝ))+ε*a^(-4:ℝ)) := by
  obtain ⟨C,D₁,E₁,F,K,N₁,B₀,hC,hD₁,hE₁,hF,hK,hN₁,hB₀,Hmean⟩ :=
    arrayEvent_fresh_field_means g₀ hg hm
  refine ⟨C,D₁,E₁,F,K,N₁,B₀,hC,hD₁,hE₁,hF,hK,hN₁,hB₀,?_⟩
  intro D c A ε hD hc hA hε
  obtain ⟨s₀,hs₀,hs₀1,Htransfer⟩ := physical_retained_master_fresh_transfer hD hc hA hε
  refine ⟨s₀,hs₀,hs₀1,?_⟩
  intro N J Z hZ ψ g hd hn hmin E hE hbase r₀ s hr₀ hs hss hscale j hrs B hB hp k y hy hry hya
  dsimp only
  intro M Qlo Qhi q L U hsmall hw hlo hhi hcount hL hU hq hθ
  let a := Coulomb.atomicCellScale y
  let b := a^(6/5:ℝ)
  let w := packetWidth c r₀ s y
  have ha : 0<a := Coulomb.atomicCellScale_pos hy
  have hb : 0<b := Real.rpow_pos_of_pos ha _
  have := rawLaw_isProbability hd.2.2.1 hn
  obtain ⟨u,hu,hum,hue,hlaw,t,ht,T,hT,ho,hcs,hos,hG,hdel,hFtransfer⟩ :=
    Htransfer Z hZ hd hn hmin hE hbase hr₀ hs hss j hrs hB hp y hy hry hya
  have hTM : T.ensemble.totalMass=1 := by rw [T.mass_eq,hum]
  have hnu : ∀ l,20*a ≤ ‖(Coulomb.atom Z hZ).position l-y‖ :=
    Coulomb.atomic_patch_nucleus_distance (Coulomb.atom Z hZ) (fun _ => rfl) y
  have Hmeans := Hmean hc hr₀ hs hscale
    (fun l : RetainedScales J j => (r₀*2^l.val.val)^(101/100:ℝ))
    (fun _ => Real.rpow_pos_of_pos (by positivity) _) k
    (hB.preimage (measurable_retainedTailObservation j)) ψ u hlaw
    (Coulomb.atom Z hZ) T.ensemble T.law hTM ha hb hsmall ht y hnu hcs hw
    hlo hhi hcount hL hU hq hθ
  have hgs : HasCompactSupport (g₀ : Position → ℝ) := by
    apply HasCompactSupport.intro (K := Metric.closedBall 0 1) (isCompact_closedBall _ _)
    intro z hz
    exact hg z (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz)
  have hp0 := (pow_pos (show 0 < r₀*2^j by positivity) 42).trans_le hp
  have Htower := retainedEvent_field_mean hd.2.2.1 hn
    (fun l : Fin J => r₀*2^l.val) (fun _ => by positivity) j hB u hum hlaw hp0
    g₀.continuous hgs hm hc hr₀ hs y ((Z:ℝ)*coulombKernel y)
  have HT := hFtransfer g₀ hm hrad hg
  rw [Htower] at HT
  have hgap : (∑ p,Coulomb.sliceExpectation (T.ensemble.vector p)
      (Coulomb.patchSliceTFGap (Coulomb.atom Z hZ) (T.ensemble.vector p) ha hb ht.2 y hnu)) ≤
      2*a^(-349/50:ℝ) := by
    exact hG
  have hfield : (∑ p,Coulomb.sliceExpectation (T.ensemble.vector p) (fun spin x =>
      Coulomb.patchTFScreenedField (Coulomb.atom Z hZ)
        ((T.ensemble.vector p).coreSlice spin x).normalized ha hb ht.2 y hnu y))=
      Coulomb.atomicPatchMeanField (Coulomb.atom Z hZ) (fun _ => rfl) T.ensemble y hy b hb t ht.2 := rfl
  rw [hfield] at Hmeans
  constructor
  · intro P hP hNw hPm hmargin
    have HI := Hmeans.1 hP hNw hPm hmargin
    have hcoef : 0 ≤ L/q+2*(B₀/w^3)/P := by positivity [packetWidth_pos hc hr₀ hs y]
    have HH := mul_le_mul_of_nonneg_left hgap hcoef
    have HT' := (abs_le.mp HT).1
    dsimp only [a,b,w] at HH HI HT' ⊢
    linarith
  · intro hmargin
    have HI := Hmeans.2 hmargin
    have hcoef : 0 ≤ (Coulomb.tfInteriorConstant Coulomb.thomasFermiKineticConstant/a^4)/q := by
      positivity [Coulomb.tfInteriorConstant_nonneg Coulomb.thomasFermiKineticConstant]
    have HH := mul_le_mul_of_nonneg_left hgap hcoef
    have HT' := (abs_le.mp HT).2
    dsimp only [a,b,w] at HH HI HT' ⊢
    linarith
end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
namespace NeutralAtom

lemma inverse_all_errors_majorized {D F K K₀ B κ Λ M a v ell m : ℝ}
    (hD : 0 ≤ D) (hF : 0 ≤ F) (hK : 0 ≤ K) (hK₀ : 0 ≤ K₀) (hB : 0 ≤ B)
    (hκ : 0<κ) (hΛ : 0 ≤ Λ) (hM : 0 ≤ M) (ha : 0<a)
    (hv : κ*a^(1+packetExponent) ≤ v) (hell : ell ≤ Λ*a^(101/100:ℝ))
    (hm : m ≤ M*a^(-3:ℝ)) (hell0 : 0 ≤ ell) (hm0 : 0 ≤ m) :
    (Real.sqrt (D/v^5*a^(-699/100:ℝ))+
      (F/v^4*(2*a^(6/5:ℝ))+K/v^4*(Real.sqrt 3*ell))*m)+
      (K₀/v^4*(Real.sqrt 3*ell))*m+
      (B/v^4*(Real.sqrt 3*ell+2*a^(6/5:ℝ)))*m ≤
    inverseResponseError D (F+B) (K+K₀+B) κ Λ M a := by
  have H := inverseResponseError_majorizes hD (add_nonneg hF hB)
    (add_nonneg (add_nonneg hK hK₀) hB) hκ hΛ hM ha hv hell hm hell0 hm0
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma tf_response_margins_scaled {hl hh η : ℝ} (hη : 0<η) (hηl : η<hl)
    (hlh : hl ≤ hh) : ∃ ε : ℝ, 0<ε ∧ ε ≤ 1 ∧
    ∀ {h a θ δ e e₀ : ℝ}, h∈Icc hl hh → 0<a → 0 ≤ θ → θ ≤ ε →
    0 ≤ δ → δ ≤ ε → 0 ≤ e → 0 ≤ e₀ → (e+e₀)*a^6 ≤ ε →
    Coulomb.tfScalarDensity ((h-η)/a^4+θ*(a^4)⁻¹)*(1+δ)+e <
      Coulomb.tfScalarDensity h/a^6-e₀ ∧
    Coulomb.tfScalarDensity h/a^6+e₀ <
      Coulomb.tfScalarDensity ((h+η)/a^4-θ*(a^4)⁻¹)*(1-δ)-e := by
  obtain ⟨ε,hε,hε1,H⟩ := Coulomb.exists_tf_response_margins hη hηl hlh
  refine ⟨ε,hε,hε1,?_⟩
  intro h a θ δ e e₀ hh' ha hθ hθε hδ hδε he he₀ hsum
  obtain ⟨Hlo,Hhi⟩ := H hh' hθ hθε hδ hδε (by positivity) hsum
  have hEq₁ : (h-η)/a^4+θ*(a^4)⁻¹=(h-η+θ)/a^4 := by ring
  have hEq₂ : (h+η)/a^4-θ*(a^4)⁻¹=(h+η-θ)/a^4 := by ring
  rw [hEq₁,hEq₂,Coulomb.tfScalarDensity_scale _ ha,Coulomb.tfScalarDensity_scale _ ha]
  constructor
  · apply (mul_lt_mul_iff_left₀ (pow_pos ha 6)).mp
    field_simp [ha.ne'] at Hlo ⊢
    nlinarith
  · apply (mul_lt_mul_iff_left₀ (pow_pos ha 6)).mp
    field_simp [ha.ne'] at Hhi ⊢
    nlinarith

lemma inverse_low_mean_scaled {H a : ℝ} (ha : 0<a) :
    (((H/a^4)/a^(-699/100:ℝ))*(2*a^(-349/50:ℝ)))*a^4=
      2*H*a^(1/100:ℝ) := by
  have hrat : a^(-349/50:ℝ)/a^(-699/100:ℝ)=a^(1/100:ℝ) := by
    rw [←Real.rpow_sub ha]; norm_num
  field_simp [ha.ne'] at hrat ⊢
  rw [hrat]

theorem inverse_errors_uniform {D F K K₀ B κ Λ M A V C E₁ c N H hl hh η : ℝ}
    (hD : 0 ≤ D) (hF : 0 ≤ F) (hK : 0 ≤ K) (hK₀ : 0 ≤ K₀) (hB : 0 ≤ B)
    (hκ : 0<κ) (hΛ : 0 ≤ Λ) (hM : 0 ≤ M) (hA : 0<A)
    (hV : 0 ≤ V) (hC : 0 ≤ C) (hE₁ : 0 ≤ E₁) (hc : 0 ≤ c) (hN : 0 ≤ N)
    (hη : 0<η) (hηl : η<hl) (hlh : hl ≤ hh) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ {s a v ell m h : ℝ},
    0 < s → s < s₀ → 0<a → a ≤ A*s → κ*a^(1+packetExponent) ≤ v →
    v/a ≤ V*s^packetExponent → 0 ≤ ell → ell ≤ Λ*a^(101/100:ℝ) →
    0 ≤ m → m ≤ M*a^(-3:ℝ) → h∈Icc hl hh →
    let θ := C*(2*v/a)
    let δ := E₁*(c*(1+packetExponent)*s^packetExponent)
    let e := Real.sqrt (D/v^5*a^(-699/100:ℝ))+
      (F/v^4*(2*a^(6/5:ℝ))+K/v^4*(Real.sqrt 3*ell))*m
    let e₀ := K₀/v^4*(Real.sqrt 3*ell)*m
    let matchError := (B/v^4*(Real.sqrt 3*ell+2*a^(6/5:ℝ)))*m
    18*a^(6/5:ℝ) ≤ a ∧ 2*v ≤ a ∧ θ ≤ 1 ∧ N*(2*v/a) ≤ 1/2 ∧
    Coulomb.tfScalarDensity hl/(2*a^6) ≤ Coulomb.tfScalarDensity h/a^6-e₀-matchError ∧
    Coulomb.tfScalarDensity ((h-η)/a^4+θ*(a^4)⁻¹)*(1+δ)+e <
      Coulomb.tfScalarDensity h/a^6-e₀ ∧
    Coulomb.tfScalarDensity h/a^6+e₀ <
      Coulomb.tfScalarDensity ((h+η)/a^4-θ*(a^4)⁻¹)*(1-δ)-e ∧
    inverseHighMeanError hh B (Coulomb.tfScalarDensity hl/2) κ N a v < η/4 ∧
    2*H*a^(1/100:ℝ) < η/4 := by
  obtain ⟨ε,hε,hε1,Hmargin⟩ := tf_response_margins_scaled hη hηl hlh
  have hhl : 0<hl := hη.trans hηl
  have htf : 0<Coulomb.tfScalarDensity hl := by
    have h := Coulomb.tfScalarDensity_strict (show (0:ℝ) ≤ 0 by rfl) hhl
    simpa [Coulomb.tfScalarDensity] using h
  have hR := inverseResponseError_scaled_tendsto hD hκ (F+B) (K+K₀+B) Λ M
  obtain ⟨s₁,hs₁,Hs₁⟩ := exists_uniform_inner_scale hR hA
    (lt_min hε (by positivity : 0<Coulomb.tfScalarDensity hl/2))
  have ht := (tendsto_positive_rpow_zero (by norm_num [packetExponent] : 0<packetExponent))
  have hlim : Tendsto (fun s =>
      (2*V+2*C*V+4*N*V+E₁*c*(1+packetExponent))*s^packetExponent) (𝓝[>] 0) (𝓝 0) := by
    simpa using ht.const_mul (2*V+2*C*V+4*N*V+E₁*c*(1+packetExponent))
  obtain ⟨s₂,hs₂,Hs₂⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (hlim.eventually (gt_mem_nhds hε))
  change 0 < s₂ at hs₂
  obtain ⟨s₃,hs₃,Hs₃⟩ := inverseHighMeanError_uniform
    (H:=hh) (B:=B) (γ:=Coulomb.tfScalarDensity hl/2) (κ:=κ) (N:=N) (V:=V)
    hA hN (by positivity : 0<η/4)
  obtain ⟨s₄,hs₄,Hs₄⟩ := exists_uniform_inner_scale
    (by simpa using (tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<1/100)).const_mul (2*H))
    hA (by positivity : 0<η/4)
  obtain ⟨s₅,hs₅,Hs₅⟩ := exists_uniform_inner_scale
    (by simpa using (tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<1/5)).const_mul (18:ℝ))
    hA (by norm_num : (0:ℝ)<1)
  refine ⟨min s₁ (min s₂ (min s₃ (min s₄ s₅))),by positivity,?_⟩
  intro s a v ell m h hs hss ha has hv hva hell0 hell hm0 hm hh'
  have hs1 := hss.trans_le (min_le_left _ _)
  have hs2 := hss.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hs3 := hss.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hs4 := hss.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hs5 := hss.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hRsmall := Hs₁ hs hs1 ha has
  have hp := Hs₂ ⟨hs,hs2⟩
  change (2*V+2*C*V+4*N*V+E₁*c*(1+packetExponent))*s^packetExponent<ε at hp
  have hsPow : 0 ≤ s^packetExponent := Real.rpow_nonneg hs.le _
  have hpw : 0<1+packetExponent := by norm_num [packetExponent]
  have hv0 : 0<v := (by positivity : 0<κ*a^(1+packetExponent)).trans_le hv
  have hθ0 : 0 ≤ C*(2*v/a) := by positivity
  have hδ0 : 0 ≤ E₁*(c*(1+packetExponent)*s^packetExponent) := by positivity
  have hθ : C*(2*v/a) ≤ ε := by
    have HH := mul_le_mul_of_nonneg_left hva (show 0 ≤ 2*C by positivity)
    have Hne : 0 ≤ (2*V+4*N*V+E₁*c*(1+packetExponent))*s^packetExponent := by positivity
    have Heq : C*(2*v/a)=2*C*(v/a) := by ring
    rw [Heq]
    linarith only [HH,hp,Hne]
  have hδ : E₁*(c*(1+packetExponent)*s^packetExponent) ≤ ε := by
    have Hne : 0 ≤ (2*V+2*C*V+4*N*V)*s^packetExponent := by positivity
    linarith only [hp,Hne]
  have hvsmall : 2*v ≤ a := by
    have HH := mul_le_mul_of_nonneg_left hva (show (0:ℝ) ≤ 2 by norm_num)
    have Hne : 0 ≤ (2*C*V+4*N*V+E₁*c*(1+packetExponent))*s^packetExponent := by positivity
    have hdiv : 2*(v/a) ≤ 1 := by linarith only [HH,hp,Hne,hε1]
    have Hdiv : (2*v)/a ≤ 1 := by simpa only [mul_div_assoc] using hdiv
    simpa only [one_mul] using (div_le_iff₀ ha).mp Hdiv
  have hNsmall : N*(2*v/a) ≤ 1/2 := by
    have HH := mul_le_mul_of_nonneg_left hva (show 0 ≤ 4*N by positivity)
    have Hne : 0 ≤ (2*V+2*C*V+E₁*c*(1+packetExponent))*s^packetExponent := by positivity
    have Heq : N*(2*v/a)=2*N*(v/a) := by ring
    rw [Heq]
    linarith only [HH,hp,Hne,hε1]
  have hthin : 18*a^(6/5:ℝ) ≤ a := by
    have Hthin := (Hs₅ hs hs5 ha has).le
    have heq : a^(6/5:ℝ)=a^(1/5:ℝ)*a := by
      calc
        _ = a^((1/5:ℝ)+1) := by norm_num
        _ = _ := by rw [Real.rpow_add ha,Real.rpow_one]
    rw [heq]
    nlinarith only [Hthin,ha]
  let e := Real.sqrt (D/v^5*a^(-699/100:ℝ))+
      (F/v^4*(2*a^(6/5:ℝ))+K/v^4*(Real.sqrt 3*ell))*m
  let e₀ := K₀/v^4*(Real.sqrt 3*ell)*m
  let em := (B/v^4*(Real.sqrt 3*ell+2*a^(6/5:ℝ)))*m
  have he : 0 ≤ e := by dsimp [e]; positivity
  have he₀ : 0 ≤ e₀ := by dsimp [e₀]; positivity
  have hem : 0 ≤ em := by dsimp [em]; positivity
  have hbound := inverse_all_errors_majorized hD hF hK hK₀ hB hκ hΛ hM ha hv hell hm hell0 hm0
  change e+e₀+em ≤ inverseResponseError D (F+B) (K+K₀+B) κ Λ M a at hbound
  have hmul := mul_le_mul_of_nonneg_right hbound (pow_nonneg ha.le 6)
  have hsum : (e+e₀)*a^6 ≤ ε := by
    have := hRsmall.trans_le (min_le_left _ _)
    nlinarith only [hmul,this,mul_nonneg hem (pow_nonneg ha.le 6)]
  have hmarg := Hmargin hh' ha hθ0 hθ hδ0 hδ he he₀ hsum
  have hP : Coulomb.tfScalarDensity hl/(2*a^6) ≤ Coulomb.tfScalarDensity h/a^6-e₀-em := by
    have htfl := Coulomb.tfScalarDensity_mono hh'.1
    have hhalf := hRsmall.trans_le (min_le_right _ _)
    apply (mul_le_mul_iff_left₀ (pow_pos ha 6)).mp
    field_simp [ha.ne']
    nlinarith only [hmul,hhalf,htfl,mul_nonneg he (pow_nonneg ha.le 6)]
  exact ⟨hthin,hvsmall,hθ.trans hε1,hNsmall,hP,hmarg.1,hmarg.2,
    Hs₃ hs hs3 ha has hva,by simpa only [one_div] using Hs₄ hs hs4 ha has⟩
end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_InverseEventContradiction
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

lemma inverse_high_mean_contradiction {η h hh B γ κ N a v mean : ℝ}
    (hη : 0 < η) (hηh : η < h) (hhh : h ≤ hh) (hB : 0 ≤ B) (hγ : 0 < γ)
    (hκ : 0 < κ) (hN : 0 ≤ N) (ha : 0 < a) (hv : κ*a^(1+packetExponent) ≤ v)
    (herr : inverseHighMeanError hh B γ κ N a v  <  η/4)
    (hmean : (h-η)/a^4-(((h-η)/a^4)/a^(-699/100:ℝ)+2*(B/v^3)/(γ/a^6))*
      (2*a^(-349/50:ℝ))-2*(N*(2*v/a))*(a^4)⁻¹-(η/4)*a^(-4:ℝ) ≤ mean)
    (hbad : mean ≤ (h-2*η)/a^4) : False := by
  have he := inverseHighMeanError_bound (hη.le.trans ((hηh.le).trans hhh)) hB hγ hκ hN
    ha hv (show 0 ≤ (h-η)/a^4 by positivity)
    (show (h-η)/a^4 ≤ hh/a^4 by gcongr; linarith) (le_refl (2*a^(-349/50:ℝ)))
  have he' := he.trans_lt herr
  have hpow : a^(-4:ℝ)=(a^4)⁻¹ := by rw [Real.rpow_neg ha.le]; norm_num
  rw [hpow] at hmean
  have HH := mul_le_mul_of_nonneg_right (hmean.trans hbad) (pow_nonneg ha.le 4)
  have h4 : a^4≠0 := pow_ne_zero _ ha.ne'
  simp only [sub_mul,div_mul_cancel₀ _ h4,mul_assoc,inv_mul_cancel₀ h4,mul_one] at HH
  simp only [add_mul,mul_assoc,inv_mul_cancel₀ h4,mul_one] at he'
  nlinarith only [HH,he',hη]

lemma inverse_low_mean_contradiction {η h H a mean : ℝ} (hη : 0 < η) (ha : 0 < a)
    (herr : 2*H*a^(1/100:ℝ) < η/4)
    (hmean : mean ≤ (h+η)/a^4+((H/a^4)/a^(-699/100:ℝ))*(2*a^(-349/50:ℝ))+
      (η/4)*a^(-4:ℝ)) (hbad : (h+2*η)/a^4 ≤ mean) : False := by
  have HH := mul_le_mul_of_nonneg_right (hbad.trans hmean) (pow_nonneg ha.le 4)
  have hpow : a^(-4:ℝ)=(a^4)⁻¹ := by rw [Real.rpow_neg ha.le]; norm_num
  rw [hpow] at HH
  have he := inverse_low_mean_scaled (H:=H) ha
  have h4 : a^4≠0 := pow_ne_zero _ ha.ne'
  simp only [add_mul,div_mul_cancel₀ _ h4,mul_assoc,inv_mul_cancel₀ h4,mul_one] at HH
  nlinarith only [HH,he,herr,hη]

theorem physical_retained_inverse_event (g₀ : 𝓢(Position,ℝ))
    (hg : ∀ z, 1 < ‖z‖  →  g₀ z=0) (hm : (∫ z,g₀ z^2)=1)
    (hrad : ∀ z,g₀ z=g₀ (EuclideanSpace.single 0 ‖z‖))
    {D c A κ Λ M V K₀ hl hh η : ℝ}
    (hD : 0 ≤ D) (hc : 0 < c) (hA : 0 < A) (hκ : 0 < κ) (hΛ : 0 ≤ Λ)
    (hM : 0 ≤ M) (hV : 0 ≤ V) (hK₀ : 0 ≤ K₀) (hη : 0 < η) (hηl : η < hl) (hlh : hl ≤ hh) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧
    ∀ {N J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)), FormDomain χ h  →  normSquared χ=1  →
      energy Z ψ g  ≤  energy Z χ h)  →
    ∀ {E : ℝ}, (E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ)  →
    energy Z ψ g ≤ E+D  →  ∀ {r₀ s : ℝ}, 0 < r₀  →  0 < s  →  s < s₀  →
    c*(1+packetExponent)*s^packetExponent ≤ 1/4  →
    ∀ (j : ℕ), r₀*2^j ≤ s  →  ∀ (k : RetainedScales J j) (y : Position) (_ : y≠0),
    r₀ ≤ ‖y‖  →  Coulomb.atomicCellScale y ≤ A*(r₀*2^j)  →
    letI := rawLaw_isProbability hd.2.2.1 hn
    let a := Coulomb.atomicCellScale y
    let w := packetWidth c r₀ s y
    let ell := (r₀*2^k.val.val)^(101/100:ℝ)
    let m := M*a^(-3:ℝ)
    let e₀ := K₀/w^4*(Real.sqrt 3*ell)*m
    let field := fun z : ObservationSample (N+1) J => (Z:ℝ)*coulombKernel y-
      potentialOf (conditionalPacketDensity (observationLaw J (rawLaw ψ)) Prod.fst
        (tailObservation (fun l : Fin J => r₀*2^l.val) j) g₀ c r₀ s
        (tailObservation (fun l : Fin J => r₀*2^l.val) j z)) y
    κ*a^(1+packetExponent) ≤ w  →  w/a ≤ V*s^packetExponent  →
    ell ≤ Λ*a^(101/100:ℝ)  →  ∀ {h : ℝ}, h∈Icc hl hh  →
    ∀ {B : Set (Fin J  →  UnorderedArray (N+1))}, MeasurableSet B  →
    (∀ z∈retainedTailObservation j ⁻¹' B,
      rawCount (Metric.closedBall y (2*w+2*a^(6/5:ℝ)+2*(Real.sqrt 3*ell)))
        (observationArrayPositions k z) ≤ m)  →
    ((∀ z∈retainedTailObservation j ⁻¹' B,
       Coulomb.tfScalarDensity h/a^6-e₀ ≤ ∑ i,packetKernel g₀ c r₀ s (observationArrayPositions k z i) y) ∧
      (∀ᵐ z ∂observationLaw J (rawLaw ψ),
        z∈tailObservation (fun l : Fin J => r₀*2^l.val) j ⁻¹' B  →  field z ≤ (h-2*η)/a^4) ∨
     (∀ z∈retainedTailObservation j ⁻¹' B,
       (∑ i,packetKernel g₀ c r₀ s (observationArrayPositions k z i) y) ≤ Coulomb.tfScalarDensity h/a^6+e₀) ∧
      (∀ᵐ z ∂observationLaw J (rawLaw ψ),
        z∈tailObservation (fun l : Fin J => r₀*2^l.val) j ⁻¹' B  →  (h+2*η)/a^4 ≤ field z))  →
    (observationLaw J (rawLaw ψ)).real
      (tailObservation (fun l : Fin J => r₀*2^l.val) j ⁻¹' B) < (r₀*2^j)^42 := by
  obtain ⟨C,D₁,E₁,F,K,N₁,B₀,hC,hD₁,hE₁,hF,hK,hN₁,hB₀,Hmean⟩ :=
    physical_retained_inverse_means g₀ hg hm hrad
  obtain ⟨s₁,hs₁,hs₁1,Hs₁⟩ := Hmean hD hc hA (show 0 < η/4 by positivity)
  obtain ⟨s₂,hs₂,Hs₂⟩ := inverse_errors_uniform (H:=Coulomb.tfInteriorConstant Coulomb.thomasFermiKineticConstant)
    hD₁.le hF.le hK.le hK₀ hB₀.le hκ hΛ hM hA hV hC.le hE₁.le hc.le hN₁.le hη hηl hlh
  obtain ⟨Kcap,hKcap,Hcap⟩ := master_kernel_estimates g₀ hg hm
  refine ⟨min s₁ s₂,lt_min hs₁ hs₂,(min_le_left _ _).trans hs₁1,?_⟩
  intro N J Z hZ ψ g hd hn hmin E hE hbase r₀ s hr₀ hs hss hscale j hrj k y hy hry hya
  dsimp only
  intro hw hwa hell h hh' B hB hcount hbad
  by_contra hp
  have hp' := le_of_not_gt hp
  have ha := Coulomb.atomicCellScale_pos hy
  let a := Coulomb.atomicCellScale y
  let w := packetWidth c r₀ s y
  let ell := (r₀*2^k.val.val)^(101/100:ℝ)
  let m := M*a^(-3:ℝ)
  let e₀ := K₀/w^4*(Real.sqrt 3*ell)*m
  have hhη : η < h := hηl.trans_le hh'.1
  have hs1 := hss.trans_le (min_le_left _ _)
  have hs2 := hss.trans_le (min_le_right _ _)
  have has : a ≤ A*s := hya.trans (mul_le_mul_of_nonneg_left hrj hA.le)
  have hm0 : 0 ≤ m := by dsimp [m]; positivity
  have he0 : 0 ≤ ell := by dsimp [ell]; positivity
  have Hnum := Hs₂ hs hs2 ha has hw hwa he0 hell hm0 (le_refl m) hh'
  obtain ⟨hthin,hww,hθ,hNw,hP,hhi,hlo,hErr,hErr'⟩ := Hnum
  have hl0 : 0 ≤ (h-η)/a^4 := div_nonneg (sub_nonneg.mpr hhη.le) (pow_nonneg ha.le _)
  have hh0 : 0 < h := hη.trans hhη
  have hu0 : 0 ≤ (h+η)/a^4 := by positivity
  have hq : 0 < a^(-699/100:ℝ) := Real.rpow_pos_of_pos ha _
  have := rawLaw_isProbability hd.2.2.1 hn
  have hgs : HasCompactSupport (g₀ : Position  →  ℝ) := by
    apply HasCompactSupport.intro (K:=Metric.closedBall 0 1) (isCompact_closedBall _ _)
    intro z hz
    exact hg z (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz)
  have hf := (integrable_const ((Z:ℝ)*coulombKernel y)).sub
    (conditionalPacketPotential_integrable (observationLaw J (rawLaw ψ)) (rawLaw ψ)
      (observationLaw_rawProjection _) (measurable_tailObservation (fun l : Fin J =>r₀*2^l.val) j)
      g₀.continuous hgs hm hc hr₀ hs y)
  have hp0 : 0 < (observationLaw J (rawLaw ψ)).real
      (tailObservation (fun l : Fin J =>r₀*2^l.val) j ⁻¹' B) :=
    (pow_pos (show 0 < r₀*2^j by positivity) 42).trans_le hp'
  have hγ : 0 < Coulomb.tfScalarDensity hl/2 := by
    have H := Coulomb.tfScalarDensity_strict (show (0:ℝ) ≤ 0 by rfl) (hη.trans hηl)
    have : 0 < Coulomb.tfScalarDensity hl := by simpa [Coulomb.tfScalarDensity] using H
    positivity
  have htfl : 0 < Coulomb.tfScalarDensity hl := by linarith only [hγ]
  rcases hbad with ⟨hgate,hbad⟩ | ⟨hgate,hbad⟩
  · have hupper (z) (_hz : z∈retainedTailObservation j ⁻¹' B) :
        (∑ i,packetKernel g₀ c r₀ s (observationArrayPositions k z i) y) ≤
          (N+1:ℕ)*(Kcap/w^3) := by
      calc
        _  ≤  ∑ i : Fin (N+1), Kcap/w^3 := Finset.sum_le_sum (fun i _ =>
          (le_abs_self _).trans ((Hcap hc hr₀ hs hscale y).2.1 _))
        _ = _ := by simp
    have Hmeans := Hs₁ Z hZ hd hn hmin hE hbase hr₀ hs hs1 hscale j hrj hB hp' k y hy hry hya
      hthin hww hgate hupper hcount hl0 hu0 hq hθ
    have H := Hmeans.1 (P:=Coulomb.tfScalarDensity hl/(2*a^6)) (by positivity)
      hNw hP hhi
    have Hb := normalized_event_le (hB.preimage (measurable_tailObservation _ j)) hf hp0 hbad
    have HP : Coulomb.tfScalarDensity hl/(2*a^6)=(Coulomb.tfScalarDensity hl/2)/a^6 := by ring
    rw [HP] at H
    exact inverse_high_mean_contradiction hη hhη hh'.2 hB₀.le hγ hκ hN₁.le ha hw hErr H Hb
  · have hlower (z) (_hz : z∈retainedTailObservation j ⁻¹' B) :
        0 ≤ ∑ i,packetKernel g₀ c r₀ s (observationArrayPositions k z i) y :=
      Finset.sum_nonneg (fun i _ => packetKernel_nonneg g₀ hc hr₀ hs _ _)
    have Hmeans := Hs₁ Z hZ hd hn hmin hE hbase hr₀ hs hs1 hscale j hrj hB hp' k y hy hry hya
      hthin hww hlower hgate hcount hl0 hu0 hq hθ
    have H := Hmeans.2 hlo
    have Hb := le_normalized_event (hB.preimage (measurable_tailObservation _ j)) hf hp0 hbad
    exact inverse_low_mean_contradiction hη ha hErr' H Hb
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_ObservedUnordered
attribute [-instance] _root_.OAI.NeutralAtom.observationNoiseLaw_negInvariant _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace NeutralAtom

lemma measurable_unorderedSum {n : ℕ} {f : Position → ℝ} (hf : Measurable f) :
    Measurable (unorderedSum (n := n) f) := by
  intro s hs
  change MeasurableSet ((fun x : Configuration n => ∑ i, f (x i)) ⁻¹' s)
  exact (Finset.measurable_sum _ (fun i _ => hf.comp (measurable_pi_apply i))) hs

lemma observationNoiseLaw_ae_support : ∀ᵐ u ∂observationNoiseLaw, |u|<1 := by
  rw [observationNoiseLaw,ae_withDensity_iff observationNoiseDensity_contDiff.continuous.measurable.ennreal_ofReal]
  filter_upwards [] with u hu
  by_contra hn
  apply hu
  simp [observationNoiseDensity_formula,hn]

lemma allObservationNoiseLaw_ae_support (n J : ℕ) :
    ∀ᵐ u ∂allObservationNoiseLaw n J, ∀ j i a, |u j i a|<1 := by
  simp only [ae_all_iff]
  intro j i a
  exact ((measurePreserving_eval (fun _ : Fin 3 => observationNoiseLaw) a).comp
    ((measurePreserving_eval (fun _ : Fin n => Measure.pi (fun _ : Fin 3 => observationNoiseLaw)) i).comp
      (measurePreserving_eval (fun _ : Fin J => Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin 3 => observationNoiseLaw))) j))).quasiMeasurePreserving.ae observationNoiseLaw_ae_support

lemma observationNoiseVector_norm_le {v : Fin 3 → ℝ} (hv : ∀ a, |v a|≤1) :
    ‖observationNoiseVector v‖≤Real.sqrt 3 := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq,Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  calc
    _≤∑ _a : Fin 3, (1:ℝ) := Finset.sum_le_sum (fun a _ => by
      rw [observationNoiseVector_coordinate]
      nlinarith [(abs_le.mp (hv a)).1,(abs_le.mp (hv a)).2])
    _=_ := by norm_num

lemma observationLaw_ae_displacement {n J : ℕ} (ν : Measure (Configuration n))
    [IsProbabilityMeasure ν] (r : Fin J → ℝ) (hR : ∀ k, 0 ≤ r k) :
    ∀ᵐ z ∂observationLaw J ν, ∀ j i,
      ‖z.1 i-observedOrdered r j z i‖≤Real.sqrt 3*(r j)^(101/100:ℝ) := by
  have hh : ∀ᵐ z ∂observationLaw J ν, ∀ j i a, |z.2 j i a|<1 :=
    measurePreserving_snd.quasiMeasurePreserving.ae (allObservationNoiseLaw_ae_support n J)
  filter_upwards [hh] with z hz j i
  have hn := observationNoiseVector_norm_le (fun a => (hz j i a).le)
  rw [observedOrdered,sub_add_cancel_left,norm_neg,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (hR j) _)]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg (hR j) _)

lemma unorderedSum_tail_stronglyMeasurable {n J : ℕ} (r : Fin J → ℝ) (j : ℕ)
    (k : Fin J) {f : Position → ℝ} (hf : Measurable f) :
    StronglyMeasurable[observationSigma (n := n) r j]
      (fun z => unorderedSum f (tailObservation r j z k)) :=
  ((measurable_unorderedSum hf).comp ((measurable_pi_apply k).comp
    (comap_measurable (tailObservation r j)))).stronglyMeasurable

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
namespace NeutralAtom

theorem physical_posterior_kernel_matching (g : 𝓢(Position,ℝ))
    (hg : ∀ z, 1<‖z‖ → g z=0) (hgn : (∫ z, g z^2)=1) :
    ∃ C : ℝ, 0<C ∧ ∀ {c r₀ s : ℝ}, 0 < c → 0 < r₀ → 0 < s →
    c*(1+packetExponent)*s^packetExponent≤1/4 →
    ∀ {n J : ℕ} (ν : Measure (Configuration n)) [IsProbabilityMeasure ν]
      (r : Fin J → ℝ), (∀ k, 0 ≤ r k) → ∀ {j : ℕ} (k : Fin J), j≤k.val → ∀ y : Position,
    ∀ᵐ z ∂observationLaw J ν,
      |conditionalPacketDensity (observationLaw J ν) Prod.fst (tailObservation r j)
          g c r₀ s (tailObservation r j z) y-
        rawPacketDensity g c r₀ s (observedOrdered r k z) y|≤
      (C/(packetWidth c r₀ s y)^4*(Real.sqrt 3*(r k)^(101/100:ℝ)))*
        rawCount (Metric.closedBall y (2*packetWidth c r₀ s y+Real.sqrt 3*(r k)^(101/100:ℝ)))
          (observedOrdered r k z) := by
  obtain ⟨C,hC,H⟩ := master_kernel_estimates g hg hgn
  refine ⟨C,hC,?_⟩
  intro c r₀ s hc hr hs hq n J ν _ r hR j k hj y
  obtain ⟨hsp,hamp,hL,_,_⟩ := H hc hr hs hq y
  let P := observationLaw J ν
  let t := packetWidth c r₀ s y
  let d := Real.sqrt 3*(r k)^(101/100:ℝ)
  let A := C/t^4
  have hd : 0≤d := mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (hR k) _)
  have ht : 0<t := packetWidth_pos hc hr hs y
  have hA : 0≤A := by dsimp [A]; positivity
  let v := fun z : ObservationSample n J => rawPacketDensity g c r₀ s (observedOrdered r k z) y
  let e := fun z : ObservationSample n J => (A*d)*rawCount (Metric.closedBall y (2*t+d)) (observedOrdered r k z)
  have hvmeas : StronglyMeasurable[observationSigma r j] v := by
    have HH := unorderedSum_tail_stronglyMeasurable (n := n) r j k
      (((continuous_packetKernel g.continuous hc hr hs).comp
        (continuous_id.prodMk (continuous_const (y := y)))).measurable)
    simpa only [v,tailObservation,ite_eq_left hj,observedArray,unorderedSum_forgetOrder,rawPacketDensity,Function.comp_apply,id_eq] using HH
  have hemeas : StronglyMeasurable[observationSigma r j] e := by
    have HH := unorderedSum_tail_stronglyMeasurable (n := n) r j k
      (measurable_const.indicator (s := Metric.closedBall y (2*t+d)) measurableSet_closedBall :
        Measurable ((Metric.closedBall y (2*t+d)).indicator (fun _ => (1:ℝ))))
    have HHH := HH.const_mul (A*d)
    simpa only [e,tailObservation,ite_eq_left hj,observedArray,unorderedSum_forgetOrder,rawCount] using HHH
  have hgs : HasCompactSupport (g : Position → ℝ) := by
    apply HasCompactSupport.intro (K := Metric.closedBall 0 1) (isCompact_closedBall _ _)
    intro z hz
    apply hg
    simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz
  have hf : Integrable (fun z : ObservationSample n J => rawPacketDensity g c r₀ s z.1 y) P :=
    (observationLaw_rawProjection ν).integrable_comp_of_integrable
      (rawPacketDensity_integrable_configuration g.continuous hgs hc hr hs ν y)
  have hv : Integrable v P := by
    apply Integrable.of_bound (hvmeas.mono (observationSigma_le _ _)).aestronglyMeasurable ((n:ℝ)*(C/t^3))
    filter_upwards [] with z
    rw [Real.norm_eq_abs]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum (fun i _ => hamp (observedOrdered r k z i))).trans_eq (by simp [t]))
  have he : Integrable e P := by
    apply Integrable.of_bound (hemeas.mono (observationSigma_le _ _)).aestronglyMeasurable ((A*d)*(n:ℝ))
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hA hd) (rawCount_nonneg _ _))]
    exact mul_le_mul_of_nonneg_left (rawCount_le_number _ _) (mul_nonneg hA hd)
  have hcomp : ∀ᵐ z ∂P, |rawPacketDensity g c r₀ s z.1 y-v z|≤e z := by
    filter_upwards [observationLaw_ae_displacement ν r hR] with z hz
    apply kernel_sum_matching _ y hA hd ?_ hL z.1 (observedOrdered r k z) (hz k)
    intro u hu
    by_contra hn
    have hh := hsp u hn
    rw [norm_sub_rev] at hh
    linarith
  have HH := condExp_matching (observationSigma_le r j) hf hv he hvmeas hemeas hcomp
  have He := conditionalPacketDensity_eq_condExp (observationLaw J ν) ν
    (observationLaw_rawProjection ν) (measurable_tailObservation r j) g.continuous hgs hc hr hs y
  filter_upwards [HH,He] with z hz he
  rw [he]
  exact hz

end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PosteriorDataMeasurable
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
namespace NeutralAtom

lemma measurable_conditionalPacketPotential_data {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] {n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P] (raw : Ω → Configuration n) (obs : Ω → B)
    {g : Position → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hm : (∫ z,g z^2)=1) {c r₀ s : ℝ}
    (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s) (y : Position) :
    Measurable (fun datum => potentialOf (conditionalPacketDensity P raw obs g c r₀ s datum) y) := by
  have H := ((measurable_rawPacketPotential (n:=n) hg hc hr hs y).stronglyMeasurable.integral_kernel
      (κ:=ProbabilityTheory.condDistrib raw obs P)).measurable
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext datum
  exact mixturePacketPotential hg hgs hm hc hr hs _ y

lemma measurable_packetKernel_center {g : Position → ℝ} (hg : Continuous g)
    {c r₀ s : ℝ} (hc : 0 < c) (hr : 0 < r₀) (hs : 0 < s) (y : Position) :
    Measurable (fun x => packetKernel g c r₀ s x y) := by
  exact ((continuous_packetKernel hg hc hr hs).comp
    (continuous_id.prodMk continuous_const)).measurable
end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
namespace NeutralAtom

lemma posterior_inverse_failure_transfer {Ω B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace B] (P : Measure Ω) [IsFiniteMeasure P]
    {obs : Ω → B} (hobs : Measurable obs) {μ H S C : B → ℝ}
    (hH : Measurable H) (hS : Measurable S) (hC : Measurable C)
    {m q e L U p : ℝ}
    (hmatch : ∀ᵐ z ∂P, C (obs z) ≤ m → |μ (obs z)-S (obs z)| ≤ e)
    (hhi : ∀ {A : Set B}, MeasurableSet A →
      (∀ d∈A, C d ≤ m) → (∀ d∈A, q-e ≤ S d) → (∀ d∈A,H d ≤ L) → P.real (obs ⁻¹' A) ≤ p)
    (hlo : ∀ {A : Set B}, MeasurableSet A →
      (∀ d∈A, C d ≤ m) → (∀ d∈A, S d ≤ q+e) → (∀ d∈A,U ≤ H d) → P.real (obs ⁻¹' A) ≤ p) :
    P.real {z | C (obs z) ≤ m ∧ q ≤ μ (obs z) ∧ H (obs z) ≤ L} ≤ p ∧
    P.real {z | C (obs z) ≤ m ∧ μ (obs z) ≤ q ∧ U ≤ H (obs z)} ≤ p := by
  have transfer {event : Set Ω} {dataEvent : Set B} (hmeas : MeasurableSet dataEvent)
      (hsub : event ≤ᵐ[P] obs ⁻¹' dataEvent) : P.real event ≤ P.real (obs ⁻¹' dataEvent) := by
    have hnull : P.real (event \ obs ⁻¹' dataEvent) = 0 := by
      simp only [measureReal_def, ae_le_set.mp hsub, ENNReal.toReal_zero]
    rw [← measureReal_inter_add_sdiff (hmeas.preimage hobs), hnull, add_zero]
    exact measureReal_mono Set.inter_subset_right
  have hmeasHi : MeasurableSet {datum | C datum ≤ m ∧ q-e ≤ S datum ∧ H datum ≤ L} :=
    (measurableSet_le hC measurable_const).inter
      ((measurableSet_le measurable_const hS).inter (measurableSet_le hH measurable_const))
  have hmeasLo : MeasurableSet {datum | C datum ≤ m ∧ S datum ≤ q+e ∧ U ≤ H datum} :=
    (measurableSet_le hC measurable_const).inter
      ((measurableSet_le hS measurable_const).inter (measurableSet_le measurable_const hH))
  have Hhi := hhi (A:={d | C d ≤ m ∧ q-e ≤ S d ∧ H d ≤ L}) hmeasHi
    (fun _ hd =>hd.1) (fun _ hd =>hd.2.1) (fun _ hd =>hd.2.2)
  have Hlo := hlo (A:={d | C d ≤ m ∧ S d ≤ q+e ∧ U ≤ H d}) hmeasLo
    (fun _ hd =>hd.1) (fun _ hd =>hd.2.1) (fun _ hd =>hd.2.2)
  constructor
  · exact (transfer hmeasHi (by
      filter_upwards [hmatch] with z hz
      intro hd
      exact ⟨hd.1,by linarith [(abs_le.mp (hz hd.1)).2,hd.2.1],hd.2.2⟩)).trans Hhi
  · exact (transfer hmeasLo (by
      filter_upwards [hmatch] with z hz
      intro hd
      exact ⟨hd.1,by linarith [(abs_le.mp (hz hd.1)).1,hd.2.1],hd.2.2⟩)).trans Hlo

lemma retained_inverse_gate_transfer {n J : ℕ} (ν : Measure (Configuration n))
    [IsProbabilityMeasure ν] (r : Fin J → ℝ) {j : ℕ} (k : RetainedScales J j)
    {ball : Set Position} (hb : MeasurableSet ball) {f : Position → ℝ} (hf : Measurable f)
    {μ H : (Fin J → UnorderedArray n) → ℝ} (hH : Measurable H) {m e q L U p : ℝ}
    (hmatch : ∀ᵐ z ∂observationLaw J ν, rawCount ball (observedOrdered r k.val z) ≤ m →
      |μ (tailObservation r j z)-(∑ i,f (observedOrdered r k.val z i))| ≤ e)
    (hhi : ∀ {B : Set (Fin J → UnorderedArray n)}, MeasurableSet B →
      (∀ z∈retainedTailObservation j ⁻¹' B,rawCount ball (observationArrayPositions k z) ≤ m) →
      (∀ z∈retainedTailObservation j ⁻¹' B,q-e ≤ ∑ i,f (observationArrayPositions k z i)) →
      (∀ᵐ z ∂observationLaw J ν,z∈tailObservation r j ⁻¹' B → H (tailObservation r j z) ≤ L) →
      (observationLaw J ν).real (tailObservation r j ⁻¹' B) ≤ p)
    (hlo : ∀ {B : Set (Fin J → UnorderedArray n)}, MeasurableSet B →
      (∀ z∈retainedTailObservation j ⁻¹' B,rawCount ball (observationArrayPositions k z) ≤ m) →
      (∀ z∈retainedTailObservation j ⁻¹' B,(∑ i,f (observationArrayPositions k z i)) ≤ q+e) →
      (∀ᵐ z ∂observationLaw J ν,z∈tailObservation r j ⁻¹' B → U ≤ H (tailObservation r j z)) →
      (observationLaw J ν).real (tailObservation r j ⁻¹' B) ≤ p) :
    (observationLaw J ν).real {z | rawCount ball (observedOrdered r k.val z) ≤ m ∧
      q ≤ μ (tailObservation r j z) ∧ H (tailObservation r j z) ≤ L} ≤ p ∧
    (observationLaw J ν).real {z | rawCount ball (observedOrdered r k.val z) ≤ m ∧
      μ (tailObservation r j z) ≤ q ∧ U ≤ H (tailObservation r j z)} ≤ p := by
  let C := fun datum : Fin J → UnorderedArray n =>
    unorderedSum (ball.indicator (fun _ => (1:ℝ))) (datum k.val)
  let S := fun datum : Fin J → UnorderedArray n => unorderedSum f (datum k.val)
  have hS : Measurable S := (measurable_unorderedSum hf).comp (measurable_pi_apply k.val)
  have hC : Measurable C := (measurable_unorderedSum
    (measurable_const.indicator hb)).comp (measurable_pi_apply k.val)
  have hcount (z : ObservationSample n J) :
      C (tailObservation r j z)=rawCount ball (observedOrdered r k.val z) := by
    simp only [C,unorderedSum_tailObservation r k.val k.property,rawCount]
  have hsum (z : ObservationSample n J) :
      S (tailObservation r j z)=∑ i,f (observedOrdered r k.val z i) := by
    simp only [S,unorderedSum_tailObservation r k.val k.property]
  have hcRet (z : (RetainedScales J j × (Fin n × Fin 3)) → ℝ) :
      C (retainedTailObservation j z)=rawCount ball (observationArrayPositions k z) := by
    simp only [C,unorderedSum_retainedTailObservation,rawCount]
  have hsRet (z : (RetainedScales J j × (Fin n × Fin 3)) → ℝ) :
      S (retainedTailObservation j z)=∑ i,f (observationArrayPositions k z i) := by
    simp only [S,unorderedSum_retainedTailObservation]
  have HH := posterior_inverse_failure_transfer (observationLaw J ν)
    (measurable_tailObservation r j) hH hS hC (by simpa only [hcount,hsum] using hmatch)
    (q:=q) (L:=L) (U:=U) (p:=p)
    (by
      intro B hB hcnt hgate hfld
      apply hhi hB
      · intro z hz; rw [←hcRet]; exact hcnt _ hz
      · intro z hz; rw [←hsRet]; exact hgate _ hz
      · exact Eventually.of_forall (fun z hz => hfld _ hz))
    (by
      intro B hB hcnt hgate hfld
      apply hlo hB
      · intro z hz; rw [←hcRet]; exact hcnt _ hz
      · intro z hz; rw [←hsRet]; exact hgate _ hz
      · exact Eventually.of_forall (fun z hz => hfld _ hz))
  simpa only [hcount] using HH
end NeutralAtom

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_RandomFields_PhysicalPosteriorInverse
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
namespace NeutralAtom

lemma rawCount_mono {n : ℕ} {S T : Set Position} (x : Configuration n)
    (h : S ⊆ T) : rawCount S x ≤ rawCount T x := by
  apply Finset.sum_le_sum
  intro i hi
  by_cases hS : x i ∈ S
  · simp only [Set.indicator_of_mem hS, Set.indicator_of_mem (h hS)]
    exact le_rfl
  · simp only [Set.indicator_of_notMem hS]
    exact Set.indicator_nonneg (fun _ _ => by norm_num) _

theorem physical_posterior_matching_count (g₀ : 𝓢(Position,ℝ))
    (hg : ∀ z, 1 < ‖z‖ → g₀ z=0) (hm : (∫ z,g₀ z^2)=1) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ {c r₀ s : ℝ}, 0 < c → 0 < r₀ → 0 < s →
    c*(1+packetExponent)*s^packetExponent ≤ 1/4 →
    ∀ {n J : ℕ} (ν : Measure (Configuration n)) [IsProbabilityMeasure ν]
    (r : Fin J → ℝ), (∀ k, 0 ≤ r k) → ∀ {j : ℕ} (k : Fin J), j ≤ k.val →
    ∀ (y : Position) (a m : ℝ), 0 ≤ a →
    ∀ᵐ z ∂observationLaw J ν,
      rawCount (Metric.closedBall y (2*packetWidth c r₀ s y+2*a^(6/5:ℝ)+2*(Real.sqrt 3*(r k)^(101/100:ℝ))))
        (observedOrdered r k z) ≤ m →
      |conditionalPacketDensity (observationLaw J ν) Prod.fst (tailObservation r j) g₀ c r₀ s
        (tailObservation r j z) y-rawPacketDensity g₀ c r₀ s (observedOrdered r k z) y| ≤
        (K₀/(packetWidth c r₀ s y)^4*(Real.sqrt 3*(r k)^(101/100:ℝ)))*m := by
  obtain ⟨K₀,hK₀,H⟩ := physical_posterior_kernel_matching g₀ hg hm
  refine ⟨K₀,hK₀,?_⟩
  intro c r₀ s hc hr₀ hs hscale n J ν inst r hr j k hk y a m ha
  have hrk := hr k
  filter_upwards [H hc hr₀ hs hscale ν r hr k hk y] with z hz hcz
  apply hz.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (rawCount_mono (observedOrdered r k z) ?_).trans hcz
  apply Metric.closedBall_subset_closedBall
  have hb : 0 ≤ a^(6/5:ℝ) := Real.rpow_nonneg ha _
  have he : 0 ≤ Real.sqrt 3*(r k)^(101/100:ℝ) := by positivity
  linarith

theorem physical_posterior_inverse_point (g₀ : 𝓢(Position,ℝ))
    (hg : ∀ z, 1<‖z‖ → g₀ z=0) (hm : (∫ z,g₀ z^2)=1)
    (hrad : ∀ z,g₀ z=g₀ (EuclideanSpace.single 0 ‖z‖))
    {D c A κ Λ M V hl hh η : ℝ}
    (hD : 0 ≤ D) (hc : 0 < c) (hA : 0<A) (hκ : 0<κ) (hΛ : 0 ≤ Λ)
    (hM : 0 ≤ M) (hV : 0 ≤ V) (hη : 0<η) (hηl : η<hl) (hlh : hl ≤ hh) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧
    ∀ {N J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)), FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h) →
    ∀ {E : ℝ}, (E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D → ∀ {r₀ s : ℝ}, 0 < r₀ → 0 < s → s < s₀ →
    c*(1+packetExponent)*s^packetExponent ≤ 1/4 →
    ∀ (j : ℕ), r₀*2^j ≤ s → ∀ (k : RetainedScales J j) (y : Position), y≠0 →
    r₀ ≤ ‖y‖ → Coulomb.atomicCellScale y ≤ A*(r₀*2^j) →
    letI := rawLaw_isProbability hd.2.2.1 hn
    let a := Coulomb.atomicCellScale y
    let w := packetWidth c r₀ s y
    let ell := (r₀*2^k.val.val)^(101/100:ℝ)
    let count := fun z : ObservationSample (N+1) J =>
      rawCount (Metric.closedBall y (2*w+2*a^(6/5:ℝ)+2*(Real.sqrt 3*ell)))
        (observedOrdered (fun l : Fin J => r₀*2^l.val) k.val z)
    let μ := fun z : ObservationSample (N+1) J =>
      conditionalPacketDensity (observationLaw J (rawLaw ψ)) Prod.fst
        (tailObservation (fun l : Fin J => r₀*2^l.val) j) g₀ c r₀ s
        (tailObservation (fun l : Fin J => r₀*2^l.val) j z)
    let field := fun z : ObservationSample (N+1) J => (Z:ℝ)*coulombKernel y-potentialOf (μ z) y
    κ*a^(1+packetExponent) ≤ w → w/a ≤ V*s^packetExponent →
    ell ≤ Λ*a^(101/100:ℝ) → ∀ {h : ℝ}, h∈Icc hl hh →
    (observationLaw J (rawLaw ψ)).real
      {z | count z ≤ M*a^(-3:ℝ) ∧ Coulomb.tfScalarDensity h/a^6 ≤ μ z y ∧ field z ≤ (h-2*η)/a^4}
        ≤ (r₀*2^j)^42 ∧
    (observationLaw J (rawLaw ψ)).real
      {z | count z ≤ M*a^(-3:ℝ) ∧ μ z y ≤ Coulomb.tfScalarDensity h/a^6 ∧ (h+2*η)/a^4 ≤ field z}
        ≤ (r₀*2^j)^42 := by
  obtain ⟨K₀,hK₀,Hmatch⟩  := physical_posterior_matching_count g₀ hg hm
  obtain ⟨s₀,hs₀,hs₀1,Hfail⟩ := physical_retained_inverse_event g₀ hg hm hrad
    hD hc hA hκ hΛ hM hV hK₀.le hη hηl hlh
  refine ⟨s₀,hs₀,hs₀1,?_⟩
  intro N J Z hZ ψ g hd hn hmin E hE hbase r₀ s hr₀ hs hss hscale j hrj k y hy hry hya
  dsimp only
  intro hw hwa hell h hh'
  have := rawLaw_isProbability hd.2.2.1 hn
  let P := observationLaw J (rawLaw ψ)
  let r : Fin J → ℝ := fun l => r₀*2^l.val
  let obs : ObservationSample (N+1) J → (Fin J → UnorderedArray (N+1)) := tailObservation r j
  let a := Coulomb.atomicCellScale y
  let w := packetWidth c r₀ s y
  let ell := (r k.val)^(101/100:ℝ)
  let m := M*a^(-3:ℝ)
  let ball := Metric.closedBall y (2*w+2*a^(6/5:ℝ)+2*(Real.sqrt 3*ell))
  have hgs : HasCompactSupport (g₀ : Position → ℝ) := by
    apply HasCompactSupport.intro (K:=Metric.closedBall 0 1) (isCompact_closedBall _ _)
    intro z hz
    exact hg z (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz)
  let μ := conditionalPacketDensity P Prod.fst obs g₀ c r₀ s
  let H := fun datum => (Z:ℝ)*coulombKernel y-potentialOf (μ datum) y
  have hH : Measurable H := measurable_const.sub
    (measurable_conditionalPacketPotential_data P Prod.fst obs g₀.continuous hgs hm hc hr₀ hs y)
  have ha : 0 < a := Coulomb.atomicCellScale_pos hy
  have hmatch := Hmatch hc hr₀ hs hscale (rawLaw ψ) r
    (fun _ => by dsimp [r]; positivity) k.val k.property y a m ha.le
  have Hfail' (B : Set (Fin J → UnorderedArray (N+1))) :=
    Hfail Z hZ hd hn hmin hE hbase hr₀ hs hss hscale j hrj k y hy hry hya hw hwa hell hh' (B:=B)
  exact retained_inverse_gate_transfer (rawLaw ψ) r k measurableSet_closedBall
    (measurable_packetKernel_center g₀.continuous hc hr₀ hs y) (μ:=fun datum => μ datum y) hH
    (by simpa only [rawPacketDensity] using hmatch)
    (fun hB hcnt hgate hfld => (Hfail' _ hB hcnt (Or.inl ⟨hgate,hfld⟩)).le)
    (fun hB hcnt hgate hfld => (Hfail' _ hB hcnt (Or.inr ⟨hgate,hfld⟩)).le)
end NeutralAtom

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Packets_NormalizedInversePoint
attribute [-instance] _root_.OAI.NeutralAtom.observationNoise_standardBorel _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

lemma atomic_response_normalization (h : ℝ) {y : Position} (hy : y≠0) :
    Coulomb.tfScalarDensity (h/100000^4)/(Coulomb.atomicCellScale y)^6 =
      Coulomb.tfScalarDensity h/‖y‖^6 := by
  rw [Coulomb.tfScalarDensity_scale _ (by norm_num : (0:ℝ) < 100000)]
  dsimp [Coulomb.atomicCellScale]
  field_simp [norm_ne_zero_iff.mpr hy]

lemma atomic_field_normalization (h η : ℝ) {y : Position} :
    (h/100000^4-2*(η/(8*100000^4)))/(Coulomb.atomicCellScale y)^4=(h-η/4)/‖y‖^4 ∧
    (h/100000^4+2*(η/(8*100000^4)))/(Coulomb.atomicCellScale y)^4=(h+η/4)/‖y‖^4 := by
  dsimp [Coulomb.atomicCellScale]
  constructor <;> ring

theorem physical_normalized_inverse_point_oai (g₀ : 𝓢(Position,ℝ))
    (hg : ∀ z,1 < ‖z‖ → g₀ z=0) (hm : (∫ z,g₀ z^2)=1)
    (hrad : ∀ z,g₀ z=g₀ (EuclideanSpace.single 0 ‖z‖))
    {D c L K hl hh ξ : ℝ} (hD : 0 ≤ D) (hc : 0 < c) (hL : 1 ≤ L)
    (hK : 0 ≤ K) (hξ : 0 < ξ) (hξl : ξ < hl) (hlh : hl ≤ hh) :
    ∃ s₀ : ℝ,0 < s₀ ∧ s₀ ≤ 1 ∧
    ∀ {N J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)),FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h) →
    ∀ {E : ℝ},(E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D → ∀ {r₀ s : ℝ},0 < r₀ → 0 < s → s < s₀ →
    c*(1+packetExponent)*s^packetExponent ≤ 1/4 → c*s^packetExponent ≤ 1/100 →
    (4*L/100000)*s ≤ 1 → ∀ (j : Fin J),r₀*2^j.val ≤ s →
    Real.sqrt 3*(r₀*2^j.val)^(101/100:ℝ) ≤ (r₀*2^j.val)/12 →
    ∀ (y : Position),r₀*2^j.val ≤ ‖y‖ → ‖y‖ ≤ 4*L*(r₀*2^j.val) →
    ∀ h∈Icc hl hh,
    letI := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    let r := fun l : Fin J => r₀*2^l.val
    let μ := fun z => conditionalPacketDensity P Prod.fst (tailObservation r j.val) g₀ c r₀ s
      (tailObservation r j.val z)
    let cnt := fun z => rawCount {x : Position | (r j)/4 ≤ ‖x‖ ∧ ‖x‖ ≤ 12*L*(r j)} (observedOrdered r j z)
    let f := fun z => (Z:ℝ)*coulombKernel y-potentialOf (μ z) y
    P.real {z | cnt z ≤ K/(r j)^3 ∧ Coulomb.tfScalarDensity h ≤ ‖y‖^6*μ z y ∧ ‖y‖^4*f z ≤ h-ξ/4}
        ≤ (r j)^42 ∧
    P.real {z | cnt z ≤ K/(r j)^3 ∧ ‖y‖^6*μ z y ≤ Coulomb.tfScalarDensity h ∧ h+ξ/4 ≤ ‖y‖^4*f z}
        ≤ (r j)^42 := by
  let A := 4*L/100000
  let κ := c*100000/(max 1 A)^packetExponent
  let Λ := (100000:ℝ)^(101/100:ℝ)
  have hA : 0 < A := by dsimp [A]; positivity
  have hκ : 0 < κ := by dsimp [κ]; positivity
  obtain ⟨s₀,hs₀,hs₀1,H⟩ := physical_posterior_inverse_point g₀ hg hm hrad hD hc hA hκ
    (show 0 ≤ Λ by dsimp [Λ]; positivity) (by positivity : 0 ≤ K*A^3)
    (by positivity : 0 ≤ 100000*c) (by positivity : 0 < ξ/(8*100000^4))
    (show ξ/(8*100000^4) < hl/100000^4 by linarith)
    (show hl/100000^4 ≤ hh/100000^4 by gcongr)
  refine ⟨s₀,hs₀,hs₀1,?_⟩
  intro N J Z hZ ψ g hd hn hmin E hE hbase r₀ s hr₀ hs hss hscale hwidth hsA j hrj hnoise y hy0 hy1 h hh'
  have := rawLaw_isProbability hd.2.2.1 hn
  dsimp only
  let P := observationLaw J (rawLaw ψ)
  let r : Fin J → ℝ := fun l => r₀*2^l.val
  have hr : 0 < r j := by dsimp [r]; positivity
  have hr₀r : r₀ ≤ r j := le_mul_of_one_le_right hr₀.le (one_le_pow₀ (by norm_num))
  have hy : y≠0 := norm_pos_iff.mp (hr.trans_le hy0)
  have ha : 0 < Coulomb.atomicCellScale y := Coulomb.atomicCellScale_pos hy
  have hya : Coulomb.atomicCellScale y ≤ A*(r j) := by dsimp [A,Coulomb.atomicCellScale]; linarith
  obtain ⟨hw,hwa,hell⟩ := physical_inverse_width_geometry hc hr₀ hr hs hA
    (hr₀r.trans hy0) hy0 hya hrj
  have ha1 : Coulomb.atomicCellScale y ≤ 1 :=
    (hya.trans (mul_le_mul_of_nonneg_left hrj hA.le)).trans hsA
  have hball := inverse_count_ball_subset hc hr₀ hs hr hL hr₀r hy0 hy1 hwidth
    (Real.rpow_le_self_of_le_one ha.le ha1 (by norm_num : (1:ℝ) ≤ 6/5)) hnoise
  have H' := H Z hZ hd hn hmin hE hbase hr₀ hs hss hscale j.val hrj
    ⟨j,le_rfl⟩ y hy (hr₀r.trans hy0) hya hw hwa hell
    (show h/100000^4∈Icc (hl/100000^4) (hh/100000^4) by
      constructor
      · exact div_le_div_of_nonneg_right hh'.1 (by norm_num)
      · exact div_le_div_of_nonneg_right hh'.2 (by norm_num))
  dsimp only at H'
  rw [atomic_response_normalization h hy,(atomic_field_normalization h ξ).1,
    (atomic_field_normalization h ξ).2] at H'
  have h6 := pow_pos (hr.trans_le hy0) 6
  have h4 := pow_pos (hr.trans_le hy0) 4
  constructor
  · apply le_trans (measureReal_mono (μ:=P) ?_) H'.1
    intro z hz
    refine ⟨(rawCount_mono (observedOrdered r j z) hball).trans
      (hz.1.trans (physical_inverse_count_rescale hK hA hr ha hya)),?_,?_⟩
    · exact (div_le_iff₀ h6).mpr (by simpa only [mul_comm] using hz.2.1)
    · exact (le_div_iff₀ h4).mpr (by simpa only [mul_comm] using hz.2.2)
  · apply le_trans (measureReal_mono (μ:=P) ?_) H'.2
    intro z hz
    refine ⟨(rawCount_mono (observedOrdered r j z) hball).trans
      (hz.1.trans (physical_inverse_count_rescale hK hA hr ha hya)),?_,?_⟩
    · exact (le_div_iff₀ h6).mpr (by simpa only [mul_comm] using hz.2.1)
    · exact (div_le_iff₀ h4).mpr (by simpa only [mul_comm] using hz.2.2)
end NeutralAtom
end

end

end OAI
end

theorem solution : type_of% @OAI.NeutralAtom.physical_normalized_inverse_point_oai := @OAI.NeutralAtom.physical_normalized_inverse_point_oai
