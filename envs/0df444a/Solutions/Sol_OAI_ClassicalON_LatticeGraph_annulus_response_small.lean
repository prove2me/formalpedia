-- Prove2me | solution 1 for OAI.ClassicalON.LatticeGraph.annulus_response_small
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T02:55:35.131119+00:00
-- url     : https://prove2.me/submissions/2af01e5e-fdb0-41ca-80c6-b5408c0638d4

import Mathlib
import Definitions.Def_ClassicalON
import Definitions.Def_OAIQWCO002
import Theorems.Thm_OAI_ClassicalON_SpinSystem_complexMixedResponse_paired

section
-- module Solutions.OAIQW_ClassicalON.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

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

theorem spinRotation_preserves_surface {n : ℕ}
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (spinRotation R)
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere := by
  open scoped Pointwise in
  refine ⟨(spinRotation R).measurable, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply (spinRotation R).measurable hs,
    Measure.toSphere_apply' _ ((spinRotation R).measurable hs),
    Measure.toSphere_apply' _ hs]
  congr 1
  have hcone : Set.Ioo (0 : ℝ) 1 • (Subtype.val '' ((spinRotation R) ⁻¹' s)) =
      R ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
    ext v
    constructor
    · rintro ⟨r, hr, w, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨r, hr, R t.val, ⟨spinRotation R t, ht, rfl⟩, (R.map_smul r t.val).symm⟩
    · rintro ⟨r, hr, w, ⟨t, ht, rfl⟩, hv⟩
      refine ⟨r, hr, R.symm t.val, ⟨(spinRotation R).symm t, ?_, rfl⟩, ?_⟩
      · simpa only [Set.mem_preimage, Homeomorph.apply_symm_apply] using ht
      · apply R.injective
        simpa only [map_smul, LinearIsometryEquiv.apply_symm_apply] using hv
  rw [hcone]
  have hm := R.toHomeomorph.measurableEmbedding.map_apply
    (volume : Measure (EuclideanSpace ℝ (Fin n)))
    (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s))
  change (Measure.map R volume) _ = volume (R ⁻¹' _) at hm
  rw [R.measurePreserving.map_eq] at hm
  exact hm.symm

theorem spinRotation_preserves_probability {n : ℕ}
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (spinRotation R) (sphereProbability n) (sphereProbability n) :=
  (spinRotation_preserves_surface R).smul_measure _

namespace SpinSystem
variable {n : ℕ} {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem integrable_weight [NeZero n] (S : SpinSystem n V E) (K : E → SpinOperator n) :
    Integrable (fun σ => Real.exp (S.energy K σ)) S.reference :=
  (S.continuous_energy K).rexp.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem Z_pos [NeZero n] (S : SpinSystem n V E) (K : E → SpinOperator n) :
    0 < S.Z K := by
  unfold Z
  apply (integral_pos_iff_support_of_nonneg
    (fun σ => (Real.exp_pos _).le) (S.integrable_weight K)).mpr
  have hs : Function.support (fun σ => Real.exp (S.energy K σ)) = Set.univ := by
    ext σ
    simp [Function.mem_support, Real.exp_ne_zero]
  rw [hs, measure_univ]
  exact zero_lt_one

omit [Fintype E] in
theorem rotateConfiguration_preserves_reference [NeZero n] (S : SpinSystem n V E)
    (U : V → EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (rotateConfiguration U) S.reference (S.rotatePins U).reference := by
  change MeasurePreserving (fun σ x => spinRotation (U x) (σ x))
    (Measure.pi (fun x => siteReference n (S.pin x)))
    (Measure.pi (fun x => siteReference n ((S.pin x).map (spinRotation (U x)))))
  apply measurePreserving_pi
  intro x
  cases S.pin x with
  | none => exact spinRotation_preserves_probability (U x)
  | some s =>
    exact ⟨(spinRotation (U x)).measurable, Measure.map_dirac s⟩

omit [Fintype V] in
theorem energy_gauge (S : SpinSystem n V E) (K : E → SpinOperator n)
    (U : V → EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (σ : V → Spin n) :
    S.energy (S.gauge K U) σ = (S.rotatePins U).energy K (rotateConfiguration U σ) := by
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  change ⟪(σ (S.left e)).val,
      (U (S.left e)).symm (K e (U (S.right e) (σ (S.right e)).val))⟫_ℝ =
    ⟪U (S.left e) (σ (S.left e)).val, K e (U (S.right e) (σ (S.right e)).val)⟫_ℝ
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    ((U (S.left e)).inner_map_map (σ (S.left e)).val
      ((U (S.left e)).symm (K e (U (S.right e) (σ (S.right e)).val)))).symm

theorem Z_gauge [NeZero n] (S : SpinSystem n V E) (K : E → SpinOperator n)
    (U : V → EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    S.Z (S.gauge K U) = (S.rotatePins U).Z K := by
  unfold Z
  simp_rw [energy_gauge]
  exact (S.rotateConfiguration_preserves_reference U).integral_comp
    (rotateConfiguration U).measurableEmbedding
    (fun σ => Real.exp ((S.rotatePins U).energy K σ))

omit [Fintype V] [Fintype E] in

theorem rotatePins_eq_self (S : SpinSystem n V E)
    (U : V → EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (hU : ∀ x s, S.pin x = some s → spinRotation (U x) s = s) :
    S.rotatePins U = S := by
  suffices hp : (fun x => (S.pin x).map (spinRotation (U x))) = S.pin by
    unfold rotatePins
    rw [hp]
  funext x
  cases h : S.pin x with
  | none => rfl
  | some s => simp only [Option.map_some, hU x s h]

theorem Z_gauge_of_fixes_pins [NeZero n] (S : SpinSystem n V E)
    (K : E → SpinOperator n)
    (U : V → EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (hU : ∀ x s, S.pin x = some s → spinRotation (U x) s = s) :
    S.Z (S.gauge K U) = S.Z K := by
  rw [S.Z_gauge K U, S.rotatePins_eq_self U hU]

@[simp] theorem W_zero [NeZero n] (S : SpinSystem n V E) : S.W 0 = 1 := by
  simp only [W, Pi.zero_apply, NormedSpace.exp_zero]
  exact div_self (S.Z_pos _).ne'

omit [Fintype V] in
theorem continuous_twistEnergy (S : SpinSystem n V E) (A : E → SpinOperator n)
    (k : ℕ) : Continuous (Function.uncurry (S.twistEnergy A k)) := by
  unfold twistEnergy energy Function.uncurry
  fun_prop

omit [Fintype V] in
theorem hasDerivAt_twistEnergy (S : SpinSystem n V E) (A : E → SpinOperator n)
    (k : ℕ) (t : ℝ) (σ : V → Spin n) :
    HasDerivAt (fun u => S.twistEnergy A k u σ) (S.twistEnergy A (k+1) t σ) t := by
  unfold twistEnergy energy
  have he (e : E) : HasDerivAt
      (fun u => NormedSpace.exp (u • A e) * A e ^ k)
      (NormedSpace.exp (t • A e) * A e ^ (k+1)) t := by
    exact ((hasDerivAt_exp_smul_const (A e) t).mul_const (A e ^ k)).congr_deriv
      (by rw [pow_succ', mul_assoc])
  apply HasDerivAt.fun_sum
  intro e _
  exact (((hasDerivAt_const t (σ (S.left e)).val).inner ℝ
    ((he e).clm_apply (hasDerivAt_const t (σ (S.right e)).val))).const_mul
      (S.strength e)).congr_deriv (by simp)

omit [Fintype V] in
theorem continuous_firstWeight (S : SpinSystem n V E) (A : E → SpinOperator n) :
    Continuous (Function.uncurry (S.firstWeight A)) := by
  exact (S.continuous_twistEnergy A 0).rexp.mul (S.continuous_twistEnergy A 1)

omit [Fintype V] in
theorem continuous_secondWeight (S : SpinSystem n V E) (A : E → SpinOperator n) :
    Continuous (Function.uncurry (S.secondWeight A)) := by
  exact (S.continuous_twistEnergy A 0).rexp.mul
    ((S.continuous_twistEnergy A 2).add ((S.continuous_twistEnergy A 1).pow 2))

omit [Fintype V] in
theorem hasDerivAt_weight (S : SpinSystem n V E) (A : E → SpinOperator n)
    (t : ℝ) (σ : V → Spin n) :
    HasDerivAt (fun u => Real.exp (S.twistEnergy A 0 u σ)) (S.firstWeight A t σ) t := by
  exact (S.hasDerivAt_twistEnergy A 0 t σ).exp

omit [Fintype V] in
theorem hasDerivAt_firstWeight (S : SpinSystem n V E) (A : E → SpinOperator n)
    (t : ℝ) (σ : V → Spin n) :
    HasDerivAt (fun u => S.firstWeight A u σ) (S.secondWeight A t σ) t := by
  exact ((S.hasDerivAt_weight A t σ).mul (S.hasDerivAt_twistEnergy A 1 t σ)).congr_deriv
    (by unfold firstWeight secondWeight; ring)

theorem hasDerivAt_twistZ [NeZero n] (S : SpinSystem n V E)
    (A : E → SpinOperator n) (t : ℝ) :
    HasDerivAt (fun u => S.Z (fun e => NormedSpace.exp (u • A e)))
      (∫ σ, S.firstWeight A t σ ∂S.reference) t := by
  simpa only [twistEnergy, pow_zero, mul_one, Z] using
    hasDerivAt_integral_compact S.reference
      (fun u σ => Real.exp (S.twistEnergy A 0 u σ)) (S.firstWeight A)
      (S.continuous_twistEnergy A 0).rexp (S.continuous_firstWeight A)
      (S.hasDerivAt_weight A) t

theorem hasDerivAt_firstVariation [NeZero n] (S : SpinSystem n V E)
    (A : E → SpinOperator n) (t : ℝ) :
    HasDerivAt (fun u => ∫ σ, S.firstWeight A u σ ∂S.reference)
      (∫ σ, S.secondWeight A t σ ∂S.reference) t :=
  hasDerivAt_integral_compact S.reference (S.firstWeight A) (S.secondWeight A)
    (S.continuous_firstWeight A) (S.continuous_secondWeight A)
    (S.hasDerivAt_firstWeight A) t

omit [Fintype V] [Fintype E] in

theorem exp_smul_add (g : SpinOperator n) (r s : ℝ) :
    NormedSpace.exp ((r+s) • g) = NormedSpace.exp (r • g) * NormedSpace.exp (s • g) := by
  rw [add_smul r s g]
  apply NormedSpace.exp_add_of_commute
  change (r • g) * (s • g) = (s • g) * (r • g)
  rw [Algebra.smul_mul_assoc r g (s • g), Algebra.mul_smul_comm s g g,
    smul_smul r s (g*g), Algebra.smul_mul_assoc s g (r • g),
    Algebra.mul_smul_comm r g g, smul_smul s r (g*g), mul_comm r s]

theorem W_add_gradient [NeZero n] (S : SpinSystem n V E) (g : SpinOperator n)
    (hg : g ∈ skewAdjoint (SpinOperator n)) (h : E → ℝ) (f : V → ℝ)
    (hP : ∀ x s, S.pin x = some s → f x = 0) :
    S.W (fun e => (h e + f (S.right e) - f (S.left e)) • g) =
      S.W (fun e => h e • g) := by
  let U := fun x => rotationExp (-(f x • g)) ((skewAdjoint _).neg_mem (skewAdjoint.smul_mem _ hg))
  have hfix : ∀ x s, S.pin x = some s → spinRotation (U x) s = s := by
    intro x s hs
    apply Subtype.ext
    change NormedSpace.exp (-(f x • g)) s.val = s.val
    rw [hP x s hs, zero_smul ℝ g, neg_zero, NormedSpace.exp_zero]
    rfl
  have hK : S.gauge
      (fun e => NormedSpace.exp ((h e + f (S.right e) - f (S.left e)) • g)) U =
      (fun e => NormedSpace.exp (h e • g)) := by
    funext e
    apply ContinuousLinearMap.ext
    intro v
    change (U (S.left e)).symm
      (NormedSpace.exp ((h e + f (S.right e) - f (S.left e)) • g)
        (U (S.right e) v)) = _
    simp only [U, rotationExp_symm_apply, rotationExp_apply, neg_neg]
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← neg_smul (f (S.right e)) g,
      ← exp_smul_add,
      ← exp_smul_add]
    have hc : f (S.left e) + (h e + f (S.right e) - f (S.left e)) + -f (S.right e) =
        h e := by ring
    rw [hc]
  unfold W
  congr 1
  rw [← hK]
  exact (S.Z_gauge_of_fixes_pins _ U hfix).symm

theorem W_gradient [NeZero n] (S : SpinSystem n V E) (g : SpinOperator n)
    (hg : g ∈ skewAdjoint (SpinOperator n)) (f : V → ℝ)
    (hP : ∀ x s, S.pin x = some s → f x = 0) :
    S.W (fun e => (f (S.right e) - f (S.left e)) • g) = 1 := by
  have h := S.W_add_gradient g hg 0 f hP
  simp only [Pi.zero_apply, zero_add, zero_smul ℝ g] at h
  exact h.trans (S.W_zero)

@[simp] theorem average_const [NeZero n] (S : SpinSystem n V E) (c : ℝ) :
    S.average (fun _ => c) = c := by
  unfold average
  rw [integral_const_mul]
  change c * S.Z (fun _ => 1) / S.Z (fun _ => 1) = c
  exact mul_div_cancel_right₀ c (S.Z_pos _).ne'

theorem average_mono [NeZero n] (S : SpinSystem n V E)
    {f g : (V → Spin n) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ σ, f σ ≤ g σ) : S.average f ≤ S.average g := by
  apply div_le_div_of_nonneg_right _ (S.Z_pos _).le
  apply integral_mono (S.integrable_average_integrand hf) (S.integrable_average_integrand hg)
  intro σ
  exact mul_le_mul_of_nonneg_right (hfg σ) (Real.exp_pos _).le

theorem average_nonneg [NeZero n] (S : SpinSystem n V E)
    {f : (V → Spin n) → ℝ} (hf : ∀ σ, 0 ≤ f σ) : 0 ≤ S.average f :=
  div_nonneg (integral_nonneg fun σ => mul_nonneg (hf σ) (Real.exp_pos _).le) (S.Z_pos _).le

theorem Z_gradient_line [NeZero n] (S : SpinSystem n V E) (g : SpinOperator n)
    (hg : g ∈ skewAdjoint (SpinOperator n)) (f : V → ℝ)
    (hP : ∀ x s, S.pin x = some s → f x = 0) (t : ℝ) :
    S.Z (fun e => NormedSpace.exp (t • S.axisGradient f g e)) = S.Z (fun _ => 1) := by
  have hp : ∀ x s, S.pin x = some s → t * f x = 0 := by
    intro x s hs
    rw [hP x s hs, mul_zero]
  have h := S.W_gradient g hg (fun x => t * f x) hp
  unfold W at h
  have ha : (fun e => (t * f (S.right e) - t * f (S.left e)) • g) =
      (fun e => t • S.axisGradient f g e) := by
    funext e
    simp only [axisGradient, smul_smul, mul_sub]
  rw [ha] at h
  exact (div_eq_one_iff_eq (S.Z_pos _).ne').mp h

theorem second_gradient_identity [NeZero n] (S : SpinSystem n V E) (g : SpinOperator n)
    (hg : g ∈ skewAdjoint (SpinOperator n)) (f : V → ℝ)
    (hP : ∀ x s, S.pin x = some s → f x = 0) :
    S.average (fun σ => S.energy (fun e => S.axisGradient f g e ^ 2) σ +
      (S.energy (S.axisGradient f g) σ)^2) = 0 := by
  let A := S.axisGradient f g
  have hZ : (fun t => S.Z (fun e => NormedSpace.exp (t • A e))) =
      (fun _ : ℝ => S.Z (fun _ => 1)) := funext (S.Z_gradient_line g hg f hP)
  have hfirst : (fun t => ∫ σ, S.firstWeight A t σ ∂S.reference) = (fun _ : ℝ => 0) := by
    funext t
    have h := S.hasDerivAt_twistZ A t
    rw [hZ] at h
    exact h.unique (hasDerivAt_const t _)
  have hsecond : (∫ σ, S.secondWeight A 0 σ ∂S.reference) = 0 := by
    have h := S.hasDerivAt_firstVariation A 0
    rw [hfirst] at h
    exact h.unique (hasDerivAt_const 0 0)
  unfold average
  have hfun : (fun σ => (S.energy (fun e => A e ^ 2) σ + (S.energy A σ)^2) *
      Real.exp (S.energy (fun _ => 1) σ)) = (fun σ => S.secondWeight A 0 σ) := by
    funext σ
    have hz (e : E) : (0:ℝ) • A e = 0 := zero_smul ℝ (A e)
    simp only [secondWeight, twistEnergy, hz, NormedSpace.exp_zero, one_mul,
      pow_zero, pow_one]
    exact mul_comm _ _
  change (∫ σ, (S.energy (fun e => A e ^ 2) σ + (S.energy A σ)^2) *
    Real.exp (S.energy (fun _ => 1) σ) ∂S.reference) / S.Z (fun _ => 1) = 0
  rw [hfun, hsecond, zero_div]

omit [Fintype V] in

theorem abs_energy_le (S : SpinSystem n V E) (K : E → SpinOperator n)
    (σ : V → Spin n) : |S.energy K σ| ≤ ∑ e, |S.strength e| * ‖K e‖ := by
  unfold energy
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro e _
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc
    |⟪(σ (S.left e)).val, K e (σ (S.right e)).val⟫_ℝ| ≤
        ‖(σ (S.left e)).val‖ * ‖K e (σ (S.right e)).val‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖(σ (S.left e)).val‖ * (‖K e‖ * ‖(σ (S.right e)).val‖) :=
      mul_le_mul_of_nonneg_left ((K e).le_opNorm _) (norm_nonneg _)
    _ = ‖K e‖ := by simp

omit [Fintype V] in

theorem abs_axis_secondEnergy_le (S : SpinSystem n V E) (β : ℝ)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (h : E → ℝ) (g : SpinOperator n) (hg : ‖g‖ ≤ 1) (σ : V → Spin n) :
    |S.energy (fun e => (h e • g)^2) σ| ≤ β * ∑ e, (h e)^2 := by
  apply (S.abs_energy_le _ σ).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  rw [abs_of_nonneg (hb e).1]
  have hA : ‖h e • g‖ ≤ |h e| := by
    rw [norm_smul (h e) g, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) hg
  have hp : ‖(h e • g)^2‖ ≤ (h e)^2 := by
    calc
      ‖(h e • g)^2‖ ≤ ‖h e • g‖^2 := by simpa only [pow_two] using norm_mul_le (h e • g) (h e • g)
      _ ≤ |h e|^2 := pow_le_pow_left₀ (norm_nonneg _) hA 2
      _ = (h e)^2 := sq_abs _
  exact mul_le_mul (hb e).2 hp (norm_nonneg _) ((hb e).1.trans (hb e).2)

theorem gradient_current_bound [NeZero n] (S : SpinSystem n V E) (β : ℝ)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (g : SpinOperator n) (hg : g ∈ skewAdjoint (SpinOperator n)) (hgn : ‖g‖ ≤ 1)
    (f : V → ℝ) (hP : ∀ x s, S.pin x = some s → f x = 0) :
    S.average (fun σ => (S.energy (S.axisGradient f g) σ)^2) ≤
      β * ∑ e, (f (S.right e) - f (S.left e))^2 := by
  let A := S.axisGradient f g
  let C := β * ∑ e, (f (S.right e) - f (S.left e))^2
  have hc1 := (S.continuous_energy A).pow 2
  have hc2 := (S.continuous_energy (fun e => A e^2)).add hc1
  have hbound (σ : V → Spin n) : (S.energy A σ)^2 ≤
      (S.energy (fun e => A e^2) σ + (S.energy A σ)^2) + C := by
    have hh := (abs_le.mp (S.abs_axis_secondEnergy_le β hb
      (fun e => f (S.right e) - f (S.left e)) g hgn σ)).1
    change -C ≤ S.energy (fun e => A e^2) σ at hh
    linarith
  have h := S.average_mono hc1 (hc2.add continuous_const) hbound
  rw [S.average_add hc2 continuous_const, S.average_const] at h
  have hi := S.second_gradient_identity g hg f hP
  change S.average (fun σ => S.energy (fun e => A e^2) σ + (S.energy A σ)^2) = 0 at hi
  change S.average (fun σ => (S.energy A σ)^2) ≤
    S.average (fun σ => S.energy (fun e => A e^2) σ + (S.energy A σ)^2) + C at h
  rw [hi, zero_add] at h
  exact h

end SpinSystem

open scoped Matrix

theorem axisA_apply (v : EuclideanSpace ℝ (Fin 3)) :
    axisA v = WithLp.toLp 2 ![0, -v 2, v 1] := by
  rw [axisA, matrixOperator_apply]
  congr 1
  ext i
  fin_cases i <;> simp [axisMatrixA, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem axisA_skew : axisA ∈ skewAdjoint (SpinOperator 3) := by
  rw [skewAdjoint.mem_iff, axisA, matrixOperator_star, ← map_neg]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [axisMatrixA]

theorem axisA_norm_le : ‖axisA‖ ≤ 1 := by
  apply axisA.opNorm_le_bound zero_le_one
  intro v
  rw [one_mul]
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  simp only [← pow_two]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, axisA_apply]
  simp [Fin.sum_univ_three, Matrix.cons_val_two]
  nlinarith [sq_nonneg ‖v.ofLp 0‖]

theorem axisB_skew : axisB ∈ skewAdjoint (SpinOperator 3) := by
  rw [skewAdjoint.mem_iff, axisB, matrixOperator_star, ← map_neg]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [axisMatrixB]

theorem axisB_apply (v : EuclideanSpace ℝ (Fin 3)) :
    axisB v = WithLp.toLp 2 ![v 2, 0, -v 0] := by
  rw [axisB, matrixOperator_apply]
  congr 1
  ext i
  fin_cases i <;> simp [axisMatrixB, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem axisC_apply (v : EuclideanSpace ℝ (Fin 3)) :
    axisC v = WithLp.toLp 2 ![-v 1, v 0, 0] := by
  rw [axisC, matrixOperator_apply]
  congr 1
  ext i
  fin_cases i <;> simp [axisMatrixC, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem axisB_norm_le : ‖axisB‖ ≤ 1 := by
  apply axisB.opNorm_le_bound zero_le_one
  intro v
  rw [one_mul]
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  simp only [← pow_two]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, axisB_apply]
  simp [Fin.sum_univ_three, Matrix.cons_val_two]
  nlinarith [sq_nonneg ‖v.ofLp 1‖]

theorem axisC_norm_le : ‖axisC‖ ≤ 1 := by
  apply axisC.opNorm_le_bound zero_le_one
  intro v
  rw [one_mul]
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  simp only [← pow_two]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, axisC_apply]
  simp [Fin.sum_univ_three, Matrix.cons_val_two]
  nlinarith [sq_nonneg ‖v.ofLp 2‖]

theorem mixedMatrixAB_sym : mixedMatrixAB = (1/2 : ℝ) • (axisMatrixA*axisMatrixB+axisMatrixB*axisMatrixA) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [axisMatrixA, axisMatrixB, mixedMatrixAB, Matrix.cons_val_two]

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.TorusFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP

noncomputable section
open scoped BigOperators ComplexConjugate

namespace ClassicalON

variable {L : ℕ} [NeZero L]

theorem torusWave_mul_conj (p q x : DiscreteTorus L) :
    torusWave p x*conj (torusWave q x) = torusWave (p-q) x := by
  rw [torusWave_conj]
  unfold torusWave
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg]
  ring

theorem sum_stdAddChar_mul (t : ZMod L) :
    (∑ i : ZMod L, ZMod.stdAddChar (t*i)) = if t=0 then (L:ℂ) else 0 := by
  classical
  split_ifs with h
  · simp [h]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar L h)

theorem sum_torusWave (p : DiscreteTorus L) :
    (∑ x : DiscreteTorus L, torusWave p x) = if p=0 then (L:ℂ)^2 else 0 := by
  classical
  simp only [torusWave, Fintype.sum_prod_type, AddChar.map_add_eq_mul]
  rw [← Finset.sum_mul_sum, sum_stdAddChar_mul, sum_stdAddChar_mul]
  by_cases h1 : p.1=0 <;> by_cases h2 : p.2=0 <;>
    simp [h1, h2, Prod.ext_iff, pow_two]

theorem torusWave_orthogonal (p q : DiscreteTorus L) :
    (∑ x : DiscreteTorus L, torusWave p x*conj (torusWave q x)) =
      if p=q then ((L:ℝ)^2 : ℂ) else 0 := by
  simp only [torusWave_mul_conj, sum_torusWave, sub_eq_zero,
    Complex.ofReal_natCast]

theorem torusWave_orthogonal_subfamily {P : Type uP} [DecidableEq P]
    (p : P → DiscreteTorus L) (hp : Function.Injective p) (i j : P) :
    (∑ x : DiscreteTorus L, torusWave (p i) x*conj (torusWave (p j) x)) =
      if i=j then ((L:ℝ)^2 : ℂ) else 0 := by
  simp only [torusWave_orthogonal, hp.eq_iff]

theorem norm_stdAddChar_intCast_sub_one (p : ℤ) :
    ‖ZMod.stdAddChar (p : ZMod L)-1‖ ≤ (2*Real.pi/(L:ℝ))*|(p:ℝ)| := by
  rw [ZMod.stdAddChar_coe]
  have he : (2*Real.pi*Complex.I*(p:ℂ)/(L:ℂ)) =
      Complex.I*((2*Real.pi/(L:ℝ)*(p:ℝ):ℝ):ℂ) := by push_cast; ring
  rw [he]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi/(L:ℝ)*(p:ℝ))).trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg]
  positivity

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.DyadicFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace ClassicalON

theorem dyadicRadius_pos {k : ℕ} (p : DyadicFreq k) : 0 < dyadicRadius p := by
  unfold dyadicRadius
  positivity

theorem dyadicRadius_le {k : ℕ} (p : DyadicFreq k) : dyadicRadius p ≤ 2^k := by
  exact Nat.pow_le_pow_right (by decide) p.1.isLt.le

theorem dyadicPoint_bounds {k : ℕ} (p : DyadicFreq k) :
    (dyadicRadius p:ℤ) ≤ (dyadicPoint p).1 ∧ (dyadicPoint p).1 < 2*dyadicRadius p ∧
      -(dyadicRadius p:ℤ) ≤ (dyadicPoint p).2 ∧ (dyadicPoint p).2 ≤ dyadicRadius p := by
  have h1 := p.2.1.isLt
  have h2 := p.2.2.isLt
  simp only [dyadicPoint, dyadicRadius]
  omega

theorem dyadicPoint_injective {k : ℕ} : Function.Injective (dyadicPoint (k := k)) := by
  intro p q he
  have hf := congrArg Prod.fst he
  have hs := congrArg Prod.snd he
  have hp := dyadicPoint_bounds p
  have hq := dyadicPoint_bounds q
  have hj : p.1 = q.1 := by
    apply Fin.ext
    by_contra h
    rcases lt_or_gt_of_ne h with hlt | hgt
    · have hr : 2*dyadicRadius p ≤ dyadicRadius q := by
        have hh := Nat.pow_le_pow_right (n := 2) (by decide : 1 ≤ 2) (Nat.succ_le_of_lt hlt)
        simpa only [dyadicRadius, pow_succ, Nat.mul_comm] using hh
      have hr' : (2*dyadicRadius p:ℤ) ≤ dyadicRadius q := by exact_mod_cast hr
      omega
    · have hr : 2*dyadicRadius q ≤ dyadicRadius p := by
        have hh := Nat.pow_le_pow_right (n := 2) (by decide : 1 ≤ 2) (Nat.succ_le_of_lt hgt)
        simpa only [dyadicRadius, pow_succ, Nat.mul_comm] using hh
      have hr' : (2*dyadicRadius q:ℤ) ≤ dyadicRadius p := by exact_mod_cast hr
      omega
  rcases p with ⟨j,a,b⟩
  rcases q with ⟨j',a',b'⟩
  dsimp only at hj
  subst j'
  have ha : a = a' := by apply Fin.ext; simp only [dyadicPoint, dyadicRadius] at hf; omega
  have hb : b = b' := by apply Fin.ext; simp only [dyadicPoint, dyadicRadius] at hs; omega
  subst a'; subst b'; rfl

theorem zmod_cast_inj_interval (L : ℕ) (c a b : ℤ)
    (ha : c ≤ a ∧ a < c+L) (hb : c ≤ b ∧ b < c+L)
    (he : (a:ZMod L) = (b:ZMod L)) : a=b := by
  have hh : ((a-c:ℤ):ZMod L) = ((b-c:ℤ):ZMod L) := by simpa only [Int.cast_sub] using congrArg (fun z : ZMod L => z-(c:ZMod L)) he
  have ha' : a-c ∈ Set.Ico (0:ℤ) L := by constructor <;> omega
  have hb' : b-c ∈ Set.Ico (0:ℤ) L := by constructor <;> omega
  have hz := CharP.intCast_injOn_Ico (R := ZMod L) L ha' hb' hh
  omega

theorem dyadicTorusPoint_injective {k : ℕ} : Function.Injective (dyadicTorusPoint (k := k)) := by
  intro p q he
  apply dyadicPoint_injective
  apply Prod.ext
  · apply zmod_cast_inj_interval (16*2^k) 0 _ _
    · have hp := dyadicPoint_bounds p; have hr := dyadicRadius_le p; have hn : 0 < 2^k := by positivity
      constructor <;> omega
    · have hq := dyadicPoint_bounds q; have hr := dyadicRadius_le q; have hn : 0 < 2^k := by positivity
      constructor <;> omega
    · exact congrArg Prod.fst he
  · apply zmod_cast_inj_interval (16*2^k) (-(2^k:ℕ):ℤ) _ _
    · have hp := dyadicPoint_bounds p; have hr := dyadicRadius_le p; have hn : 0 < 2^k := by positivity
      constructor <;> omega
    · have hq := dyadicPoint_bounds q; have hr := dyadicRadius_le q; have hn : 0 < 2^k := by positivity
      constructor <;> omega
    · exact congrArg Prod.snd he

theorem dyadic_shell_card_bounds (j : ℕ) :
    2*(2^j)^2 ≤ Fintype.card (Fin (2^j) × Fin (2*2^j+1)) ∧
      Fintype.card (Fin (2^j) × Fin (2*2^j+1)) ≤ 3*(2^j)^2 := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  have h : 1 ≤ 2^j := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
  constructor <;> nlinarith

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.SmoothProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function
open scoped Topology ContDiff

namespace ClassicalON

theorem thetaBump_one {x : ℝ} (hx : |x| ≤ 4/3) : thetaBump x = 1 := by
  apply thetaBump.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, Real.dist_eq, thetaBump] using hx

theorem thetaBump_zero {x : ℝ} (hx : 5/3 ≤ |x|) : thetaBump x = 0 := by
  apply thetaBump.zero_of_le_dist
  simpa [Real.dist_eq, thetaBump] using hx

theorem thetaBump_deriv_zero_inner {x : ℝ} (hx : |x| ≤ 4/3) : deriv thetaBump x = 0 := by
  apply IsLocalMax.deriv_eq_zero
  apply Filter.Eventually.of_forall
  intro y
  rw [thetaBump_one hx]
  exact thetaBump.le_one

theorem thetaBump_deriv_zero_outer {x : ℝ} (hx : 5/3 ≤ |x|) : deriv thetaBump x = 0 := by
  apply IsLocalMin.deriv_eq_zero
  apply Filter.Eventually.of_forall
  intro y
  rw [thetaBump_zero hx]
  exact thetaBump.nonneg

theorem outerBump_one {x : ℝ} (hx : |x| ≤ 7/4) : outerBump x = 1 := by
  apply outerBump.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, Real.dist_eq, outerBump] using hx

theorem outerBump_zero {x : ℝ} (hx : 15/8 ≤ |x|) : outerBump x = 0 := by
  apply outerBump.zero_of_le_dist
  simpa [Real.dist_eq, outerBump] using hx

theorem innerBump_one {x : ℝ} (hx : |x| ≤ 9/8) : innerBump x = 1 := by
  apply innerBump.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, Real.dist_eq, innerBump] using hx

theorem innerBump_zero {x : ℝ} (hx : 5/4 ≤ |x|) : innerBump x = 0 := by
  apply innerBump.zero_of_le_dist
  simpa [Real.dist_eq, innerBump] using hx

theorem squareTheta_zero (z : ℝ × ℝ) (h : 2 ≤ |z.1| ∨ 2 ≤ |z.2|) :
    squareTheta z = 0 := by
  rcases h with hx | hy
  · simp [squareTheta, thetaBump_zero (by linarith : 5/3 ≤ |z.1|)]
  · simp [squareTheta, thetaBump_zero (by linarith : 5/3 ≤ |z.2|)]

theorem squareProfile_zero_inner (m s : Bool) (z : ℝ × ℝ)
    (hx : |z.1| ≤ 1) (hy : |z.2| ≤ 1) : squareProfile m s z = 0 := by
  have hc : squareCutoff z = 0 := by
    simp [squareCutoff, innerBump_one (by linarith : |z.1| ≤ 9/8),
      innerBump_one (by linarith : |z.2| ≤ 9/8)]
  have hg : squareGradient m z = 0 := by
    cases m <;> simp [squareGradient,
      thetaBump_deriv_zero_inner (by linarith : |z.1| ≤ 4/3),
      thetaBump_deriv_zero_inner (by linarith : |z.2| ≤ 4/3)]
  cases s <;> simp [squareProfile, hc, hg]

theorem squareProfile_zero_outer (m s : Bool) (z : ℝ × ℝ)
    (h : 2 ≤ |z.1| ∨ 2 ≤ |z.2|) : squareProfile m s z = 0 := by
  have hc : squareCutoff z = 0 := by
    rcases h with hx | hy
    · simp [squareCutoff, outerBump_zero (by linarith : 15/8 ≤ |z.1|)]
    · simp [squareCutoff, outerBump_zero (by linarith : 15/8 ≤ |z.2|)]
  have hg : squareGradient m z = 0 := by
    rcases h with hx | hy
    · cases m <;> simp [squareGradient,
        thetaBump_zero (by linarith : 5/3 ≤ |z.1|),
        thetaBump_deriv_zero_outer (by linarith : 5/3 ≤ |z.1|)]
    · cases m <;> simp [squareGradient,
        thetaBump_zero (by linarith : 5/3 ≤ |z.2|),
        thetaBump_deriv_zero_outer (by linarith : 5/3 ≤ |z.2|)]
  cases s <;> simp [squareProfile, hc, hg]

theorem squareTheta_contDiff : ContDiff ℝ ∞ squareTheta := by
  exact (thetaBump.contDiff.comp contDiff_fst).mul (thetaBump.contDiff.comp contDiff_snd)

theorem squareCutoff_contDiff : ContDiff ℝ ∞ squareCutoff := by
  apply ((outerBump.contDiff.comp contDiff_fst).mul (outerBump.contDiff.comp contDiff_snd)).mul
  exact contDiff_const.sub ((innerBump.contDiff.comp contDiff_fst).mul (innerBump.contDiff.comp contDiff_snd))

theorem squareGradient_contDiff (m : Bool) : ContDiff ℝ ∞ (squareGradient m) := by
  have hd : ContDiff ℝ ∞ (deriv thetaBump) := (contDiff_infty_iff_deriv.mp (thetaBump.contDiff : ContDiff ℝ ∞ thetaBump)).2
  cases m
  · exact (hd.comp contDiff_fst).mul (thetaBump.contDiff.comp contDiff_snd)
  · exact (thetaBump.contDiff.comp contDiff_fst).mul (hd.comp contDiff_snd)

theorem squareProfile_contDiff (m s : Bool) : ContDiff ℝ ∞ (squareProfile m s) := by
  cases s
  · exact (squareCutoff_contDiff.add (squareGradient_contDiff m)).div_const 2
  · exact (squareCutoff_contDiff.sub (squareGradient_contDiff m)).div_const 2

theorem squareProfile_compact (m s : Bool) : HasCompactSupport (squareProfile m s) := by
  apply HasCompactSupport.intro (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Icc (-2:ℝ) 2 ×ˢ Icc (-2:ℝ) 2))
  intro z hz
  apply squareProfile_zero_outer
  by_contra h
  push Not at h
  apply hz
  constructor <;> constructor <;> nlinarith [abs_le.mp h.1.le, abs_le.mp h.2.le]

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.SmoothBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uF

noncomputable section
open Set Function
open scoped ContDiff
namespace ClassicalON

variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem compact_continuous_norm_bound {f : E → F} (hc : HasCompactSupport f) (hf : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C,hC⟩ := (hc.isCompact_range hf).isBounded.exists_norm_le
  exact ⟨max C 0, le_max_right _ _, fun x => (hC _ ⟨x,rfl⟩).trans (le_max_left _ _)⟩

theorem smooth_compact_lipschitz_bound {f : E → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ ∞ f) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x, ‖f x‖ ≤ C) ∧
      (∀ x y, ‖f y-f x‖ ≤ C*‖y-x‖) := by
  obtain ⟨A,hA,hfA⟩ := compact_continuous_norm_bound hc hf.continuous
  obtain ⟨B,hB,hfB⟩ := compact_continuous_norm_bound (hc.fderiv ℝ)
    (hf.fderiv_right (m := ∞) (by simp)).continuous
  refine ⟨A+B, add_nonneg hA hB, fun x => (hfA x).trans (le_add_of_nonneg_right hB), ?_⟩
  intro x y
  calc ‖f y-f x‖ ≤ B*‖y-x‖ :=
        Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hf.differentiable (by simp) z)
          (fun z _ => hfB z) convex_univ (mem_univ x) (mem_univ y)
       _ ≤ (A+B)*‖y-x‖ := by gcongr; exact le_add_of_nonneg_left hA

theorem abs_sub_left_le_of_uIcc {x y z : ℝ} (hz : z ∈ uIcc x y) :
    |z-x| ≤ |y-x| := by
  rcases le_total x y with h | h
  · rw [uIcc_of_le h] at hz
    rw [abs_of_nonneg (sub_nonneg.mpr hz.1), abs_of_nonneg (sub_nonneg.mpr h)]
    linarith [hz.2]
  · rw [uIcc_of_ge h] at hz
    rw [abs_of_nonpos (sub_nonpos.mpr hz.2), abs_of_nonpos (sub_nonpos.mpr h)]
    linarith [hz.1]

theorem first_remainder_bound (f f' : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hL : ∀ x y, |f' y-f' x| ≤ C*|y-x|) (x y : ℝ) :
    |f y-f x-f' x*(y-x)| ≤ C*|y-x|^2 := by
  let g := fun z => f z-f' x*z
  have hg (z : ℝ) : HasDerivAt g (f' z-f' x) z := by
    convert (hf z).sub ((hasDerivAt_id z).const_mul (f' x)) using 1 <;> first | rfl | ring
  have hb (z : ℝ) (hz : z ∈ uIcc x y) : |f' z-f' x| ≤ C*|y-x| :=
    (hL x z).trans (mul_le_mul_of_nonneg_left (abs_sub_left_le_of_uIcc hz) hC)
  have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ uIcc x y) => (hg z).hasDerivWithinAt)
    (fun z hz => hb z hz) (convex_uIcc x y) (left_mem_uIcc) (right_mem_uIcc)
  change |g y-g x| ≤ _ at H
  convert H using 1
  · congr 1; ring
  · rw [Real.norm_eq_abs]; ring

theorem second_remainder_bound (f f' f'' : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hL : ∀ x y, |f'' y-f'' x| ≤ C*|y-x|) (x y : ℝ) :
    |f y-f x-f' x*(y-x)-f'' x/2*(y-x)^2| ≤ C*|y-x|^3 := by
  let g := fun z => f z-f' x*(z-x)-f'' x/2*(z-x)^2
  have hg (z : ℝ) : HasDerivAt g (f' z-f' x-f'' x*(z-x)) z := by
    have ht : HasDerivAt (fun t : ℝ => t-x) 1 z := (hasDerivAt_id z).sub_const x
    have hq : HasDerivAt g _ z :=
      ((hf z).sub (ht.const_mul (f' x))).sub ((ht.pow 2).const_mul (f'' x/2))
    exact hq.congr_deriv (by push_cast; ring)
  have hb (z : ℝ) (hz : z ∈ uIcc x y) : |f' z-f' x-f'' x*(z-x)| ≤ C*|y-x|^2 := by
    exact (first_remainder_bound f' f'' C hC hf' hL x z).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (abs_sub_left_le_of_uIcc hz) 2) hC)
  have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ uIcc x y) => (hg z).hasDerivWithinAt)
    (fun z hz => hb z hz) (convex_uIcc x y) (left_mem_uIcc) (right_mem_uIcc)
  change |g y-g x| ≤ _ at H
  convert H using 1
  · congr 1; ring
  · rw [Real.norm_eq_abs]; ring

theorem trapezoid_error_bound (f f' f'' : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hL : ∀ x y, |f'' y-f'' x| ≤ C*|y-x|) (x y : ℝ) :
    |f y-f x-(y-x)/2*(f' x+f' y)| ≤ 2*C*|y-x|^3 := by
  have h1 := second_remainder_bound f f' f'' C hC hf hf' hL x y
  have h2 := first_remainder_bound f' f'' C hC hf' hL x y
  have he : f y-f x-(y-x)/2*(f' x+f' y) =
      (f y-f x-f' x*(y-x)-f'' x/2*(y-x)^2) -
        (y-x)/2*(f' y-f' x-f'' x*(y-x)) := by ring
  rw [he]
  calc _ ≤ |f y-f x-f' x*(y-x)-f'' x/2*(y-x)^2| +
        |(y-x)/2*(f' y-f' x-f'' x*(y-x))| := abs_sub _ _
       _ ≤ C*|y-x|^3+|y-x|/2*(C*|y-x|^2) := by
          rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
          gcongr
       _ ≤ _ := by nlinarith [mul_nonneg hC (pow_nonneg (abs_nonneg (y-x)) 3)]

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.ProfileEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff BigOperators
namespace ClassicalON

theorem profiles_uniform_bound : ∃ C : ℝ, 1 ≤ C ∧
    (∀ m s z, |squareProfile m s z| ≤ C) ∧
    (∀ m s z w, |squareProfile m s w-squareProfile m s z| ≤ C*‖w-z‖) := by
  have he (m s : Bool) := smooth_compact_lipschitz_bound
    (squareProfile_compact m s) (squareProfile_contDiff m s)
  choose C hC hval hLip using he
  let M : ℝ := 1+∑ m, ∑ s, C m s
  have hsum : 0 ≤ ∑ m : Bool, ∑ s : Bool, C m s :=
    Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun s _ => hC m s
  have hCM (m s : Bool) : C m s ≤ M := by
    have hs := Finset.single_le_sum (fun t _ => hC m t) (Finset.mem_univ s)
    have hm : (∑ t : Bool, C m t) ≤ ∑ u : Bool, ∑ t : Bool, C u t := Finset.single_le_sum (fun t _ => Finset.sum_nonneg fun t' _ => hC t t') (Finset.mem_univ m)
    dsimp only [M]
    linarith
  refine ⟨M, by dsimp only [M]; linarith, fun m s z => (hval m s z).trans (hCM m s), ?_⟩
  intro m s z w
  exact (hLip m s z w).trans (mul_le_mul_of_nonneg_right (hCM m s) (norm_nonneg _))

theorem theta_trapezoid_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ,
    |thetaBump y-thetaBump x-(y-x)/2*(deriv thetaBump x+deriv thetaBump y)| ≤
      C*|y-x|^3 := by
  have hd : ContDiff ℝ ∞ (deriv thetaBump) :=
    (contDiff_infty_iff_deriv.mp (thetaBump.contDiff : ContDiff ℝ ∞ thetaBump)).2
  have hdd : ContDiff ℝ ∞ (deriv (deriv thetaBump)) := (contDiff_infty_iff_deriv.mp hd).2
  obtain ⟨C,hC,_hval,hL⟩ := smooth_compact_lipschitz_bound
    (thetaBump.hasCompactSupport.deriv.deriv) hdd
  refine ⟨2*C, by positivity, fun x y => ?_⟩
  exact trapezoid_error_bound thetaBump (deriv thetaBump) (deriv (deriv thetaBump)) C hC
    (fun t => ((thetaBump.contDiff : ContDiff ℝ ∞ thetaBump).differentiable (by simp) t).hasDerivAt)
    (fun t => (hd.differentiable (by simp) t).hasDerivAt) hL x y

theorem squareCutoff_near_gradient (m : Bool) (z w : ℝ × ℝ)
    (h1 : |w.1-z.1| ≤ 1/16) (h2 : |w.2-z.2| ≤ 1/16)
    (hg : squareGradient m z ≠ 0) : squareCutoff w = 1 := by
  have ha1 : |w.1| ≤ |w.1-z.1|+|z.1| := by simpa only [sub_add_cancel] using (abs_add_le (w.1-z.1) z.1)
  have ha2 : |w.2| ≤ |w.2-z.2|+|z.2| := by simpa only [sub_add_cancel] using (abs_add_le (w.2-z.2) z.2)
  have hb1 : |z.1| ≤ |w.1-z.1|+|w.1| := by
    simpa only [sub_add_cancel, abs_sub_comm] using (abs_add_le (z.1-w.1) w.1)
  have hb2 : |z.2| ≤ |w.2-z.2|+|w.2| := by
    simpa only [sub_add_cancel, abs_sub_comm] using (abs_add_le (z.2-w.2) w.2)
  cases m
  · have hd : deriv thetaBump z.1 ≠ 0 := by intro h; apply hg; simp [squareGradient, h]
    have ht : thetaBump z.2 ≠ 0 := by intro h; apply hg; simp [squareGradient, h]
    have hx : 4/3 < |z.1| ∧ |z.1| < 5/3 := ⟨
      lt_of_not_ge (fun h => hd (thetaBump_deriv_zero_inner h)),
      lt_of_not_ge (fun h => hd (thetaBump_deriv_zero_outer h))⟩
    have hy : |z.2| < 5/3 := lt_of_not_ge (fun h => ht (thetaBump_zero h))
    simp [squareCutoff, outerBump_one (by linarith : |w.1| ≤ 7/4),
      outerBump_one (by linarith : |w.2| ≤ 7/4), innerBump_zero (by linarith : 5/4 ≤ |w.1|)]
  · have hd : deriv thetaBump z.2 ≠ 0 := by intro h; apply hg; simp [squareGradient, h]
    have ht : thetaBump z.1 ≠ 0 := by intro h; apply hg; simp [squareGradient, h]
    have hy : 4/3 < |z.2| ∧ |z.2| < 5/3 := ⟨
      lt_of_not_ge (fun h => hd (thetaBump_deriv_zero_inner h)),
      lt_of_not_ge (fun h => hd (thetaBump_deriv_zero_outer h))⟩
    have hx : |z.1| < 5/3 := lt_of_not_ge (fun h => ht (thetaBump_zero h))
    simp [squareCutoff, outerBump_one (by linarith : |w.1| ≤ 7/4),
      outerBump_one (by linarith : |w.2| ≤ 7/4), innerBump_zero (by linarith : 5/4 ≤ |w.2|)]

theorem squareProfile_product_difference (m : Bool) (z w : ℝ × ℝ)
    (h1 : |w.1-z.1| ≤ 1/16) (h2 : |w.2-z.2| ≤ 1/16) :
    squareProfile m false z*squareProfile m false w-
      squareProfile m true z*squareProfile m true w =
      (squareGradient m z+squareGradient m w)/2 := by
  have hzw : squareGradient m z*squareCutoff w = squareGradient m z := by
    by_cases hg : squareGradient m z=0
    · simp [hg]
    · rw [squareCutoff_near_gradient m z w h1 h2 hg, mul_one]
  have hwz : squareCutoff z*squareGradient m w = squareGradient m w := by
    by_cases hg : squareGradient m w=0
    · simp [hg]
    · rw [squareCutoff_near_gradient m w z (by simpa only [abs_sub_comm] using h1)
        (by simpa only [abs_sub_comm] using h2) hg, one_mul]
  simp only [squareProfile, Bool.false_eq_true, ↓reduceIte]
  nlinarith

theorem squareTheta_step_error : ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : Bool) (z : ℝ × ℝ) (ε : ℝ),
    |ε| ≤ 1/16 →
    |squareTheta (squareStep m ε z)-squareTheta z-
      ε*(squareProfile m false z*squareProfile m false (squareStep m ε z)-
           squareProfile m true z*squareProfile m true (squareStep m ε z))| ≤ C*|ε|^3 := by
  obtain ⟨C,hC,hT⟩ := theta_trapezoid_bound
  refine ⟨C,hC,?_⟩
  intro m z ε hε
  have hp := squareProfile_product_difference m z (squareStep m ε z)
    (by cases m
        · simpa only [squareStep, Bool.false_eq_true, ↓reduceIte, add_sub_cancel_left] using hε
        · simp [squareStep])
    (by cases m
        · simp [squareStep]
        · simpa only [squareStep, ↓reduceIte, add_sub_cancel_left] using hε)
  rw [hp]
  have hb (x : ℝ) : |thetaBump x| ≤ 1 := by rw [abs_of_nonneg thetaBump.nonneg]; exact thetaBump.le_one
  cases m
  · have h := hT z.1 (z.1+ε)
    simp only [add_sub_cancel_left] at h
    have he : squareTheta (squareStep false ε z)-squareTheta z-
        ε*((squareGradient false z+squareGradient false (squareStep false ε z))/2) =
        thetaBump z.2*(thetaBump (z.1+ε)-thetaBump z.1-ε/2*(deriv thetaBump z.1+deriv thetaBump (z.1+ε))) := by
      simp only [squareTheta, squareStep, squareGradient, Bool.false_eq_true, ↓reduceIte]
      ring
    rw [he, abs_mul]
    calc _ ≤ 1*(C*|ε|^3) := mul_le_mul (hb z.2) h (abs_nonneg _) (by norm_num)
         _ = _ := one_mul _
  · have h := hT z.2 (z.2+ε)
    simp only [add_sub_cancel_left] at h
    have he : squareTheta (squareStep true ε z)-squareTheta z-
        ε*((squareGradient true z+squareGradient true (squareStep true ε z))/2) =
        thetaBump z.1*(thetaBump (z.2+ε)-thetaBump z.2-ε/2*(deriv thetaBump z.2+deriv thetaBump (z.2+ε))) := by
      simp only [squareTheta, squareStep, squareGradient, ↓reduceIte]
      ring
    rw [he, abs_mul]
    calc _ ≤ 1*(C*|ε|^3) := mul_le_mul (hb z.1) h (abs_nonneg _) (by norm_num)
         _ = _ := one_mul _

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.LatticeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace ClassicalON

namespace LatticeGraph

theorem edge_step (G : LatticeGraph) (e : G.edges) :
    e.val.2.val = e.val.1.val+latticeAxis (G.edgeDirection e) := by
  rcases G.nearest e.val e.property with h | h
  · have hn : e.val.2.val.1 ≠ e.val.1.val.1 := by omega
    simp only [edgeDirection, decide_eq_false hn, latticeAxis, Bool.false_eq_true, ↓reduceIte]
    exact Prod.ext h.1 (by simpa using h.2)
  · simp only [edgeDirection, h.1, decide_true, latticeAxis, ↓reduceIte]
    exact Prod.ext (by simpa using h.1) h.2

theorem directional_origin_injective (G : LatticeGraph) (m : Bool) :
    Function.Injective (fun e : G.DirectionalEdges m => e.val.val.1) := by
  intro e f h
  change e.val.val.1 = f.val.val.1 at h
  have he := G.edge_step e.val
  have hf := G.edge_step f.val
  rw [e.property] at he
  rw [f.property] at hf
  have hy : e.val.val.2 = f.val.val.2 := by
    apply Subtype.ext
    rw [he, hf, h]
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext h hy

theorem torus_site_injective (G : LatticeGraph) (k : ℕ) (hG : G.WithinDyadicBox k) :
    Function.Injective (fun x : G.vertices => latticeTorus (16*2^k) x.val) := by
  intro x y h
  apply Subtype.ext
  apply Prod.ext
  · apply zmod_cast_inj_interval (16*2^k) (-(2*(2^k:ℕ)):ℤ) _ _
    · have hx := abs_le.mp (hG x).1; have hN : 0<2^k := by positivity
      constructor <;> omega
    · have hy := abs_le.mp (hG y).1; have hN : 0<2^k := by positivity
      constructor <;> omega
    · exact congrArg Prod.fst h
  · apply zmod_cast_inj_interval (16*2^k) (-(2*(2^k:ℕ)):ℤ) _ _
    · have hx := abs_le.mp (hG x).2; have hN : 0<2^k := by positivity
      constructor <;> omega
    · have hy := abs_le.mp (hG y).2; have hN : 0<2^k := by positivity
      constructor <;> omega
    · exact congrArg Prod.snd h

theorem directional_torus_injective (G : LatticeGraph) (k : ℕ) (hG : G.WithinDyadicBox k) (m : Bool) :
    Function.Injective (fun e : G.DirectionalEdges m => latticeTorus (16*2^k) e.val.val.1.val) :=
  (G.torus_site_injective k hG).comp (G.directional_origin_injective m)

theorem edge_card_bound (G : LatticeGraph) (k : ℕ) (hG : G.WithinDyadicBox k) :
    (Fintype.card G.edges:ℝ) ≤ 512*((2:ℝ)^k)^2 := by
  let i := fun e : G.edges => (G.edgeDirection e, latticeTorus (16*2^k) e.val.1.val)
  have hi : Function.Injective i := by
    intro e f h
    have hm : G.edgeDirection e = G.edgeDirection f := congrArg Prod.fst h
    have hx := (G.torus_site_injective k hG) (congrArg Prod.snd h)
    have he := G.edge_step e
    have hf := G.edge_step f
    have hy : e.val.2 = f.val.2 := by
      apply Subtype.ext
      rw [he,hf,hm,hx]
    apply Subtype.ext
    exact Prod.ext hx hy
  have hc := Fintype.card_le_of_injective i hi
  simp only [Fintype.card_prod, Fintype.card_bool, ZMod.card] at hc
  have hh : (Fintype.card G.edges:ℝ) ≤ 2*((16*(2:ℝ)^k)*(16*(2:ℝ)^k)) := by exact_mod_cast hc
  nlinarith

theorem scaled_edge_distance (G : LatticeGraph) (k : ℕ) (e : G.edges) :
    ‖scaledSite k e.val.2.val-scaledSite k e.val.1.val‖ = 1/(2:ℝ)^k := by
  rw [G.edge_step e, scaledSite_add_axis, squareStep_distance, abs_of_pos (by positivity)]

end LatticeGraph
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.DyadicSine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace ClassicalON

theorem dyadic_sin_lower (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (hN : t ≤ (2:ℝ)^k) :
    t/(4*(2:ℝ)^k) ≤ Real.sin (dyadicAngle k t) := by
  have hpow : (0:ℝ) < 2^k := by positivity
  have ha : 0 ≤ dyadicAngle k t := by unfold dyadicAngle; positivity
  have hb : dyadicAngle k t ≤ Real.pi/2 := by
    unfold dyadicAngle
    rw [div_le_iff₀ (by positivity : (0:ℝ)<16*2^k)]
    nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left hN Real.pi_pos.le]
  have h := Real.mul_le_sin ha hb
  convert h using 1
  unfold dyadicAngle
  field_simp
  ring

theorem dyadicPoint_fst_le_N {k : ℕ} (p : DyadicFreq k) :
    ((dyadicPoint p).1:ℝ) ≤ (2:ℝ)^k := by
  have hr : 2*dyadicRadius p ≤ 2^k := by
    have hh := Nat.pow_le_pow_right (n := 2) (by decide : 1 ≤ 2) p.1.isLt
    simpa only [dyadicRadius, pow_succ, Nat.mul_comm] using hh
  have hp := (dyadicPoint_bounds p).2.1
  have hz : (dyadicPoint p).1 ≤ (2^k:ℕ) := by omega
  exact_mod_cast hz

theorem dyadicLambda_lower (k : ℕ) : (k:ℝ)/2 ≤ dyadicLambda k := by
  have hN : (0:ℝ)<2^k := by positivity
  have hp (p : DyadicFreq k) :
      (1/(dyadicRadius p:ℝ))^2/4 ≤
        (2:ℝ)^k*((1/(dyadicRadius p:ℝ))^3*Real.sin (dyadicAngle k (dyadicPoint p).1)) := by
    have hr : (0:ℝ)<dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
    have hpr : (dyadicRadius p:ℝ) ≤ ((dyadicPoint p).1:ℝ) := by exact_mod_cast (dyadicPoint_bounds p).1
    have hs := dyadic_sin_lower k ((dyadicPoint p).1:ℝ) (by linarith) (dyadicPoint_fst_le_N p)
    calc _ = (2:ℝ)^k*((1/(dyadicRadius p:ℝ))^3*((dyadicRadius p:ℝ)/(4*(2:ℝ)^k))) := by field_simp
         _ ≤ _ := by gcongr; exact (div_le_div_of_nonneg_right hpr (by positivity)).trans hs
  unfold dyadicLambda
  rw [Finset.mul_sum]
  calc _ ≤ ∑ p : DyadicFreq k, (1/(dyadicRadius p:ℝ))^2/4 := by
          rw [Fintype.sum_sigma]
          calc _ = ∑ _j : Fin k, (1/2:ℝ) := by simp; ring
               _ ≤ _ := by
                 apply Finset.sum_le_sum
                 intro j _
                 simp only [dyadicRadius, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
                 have hr : (0:ℝ)<(2^j.val:ℕ) := by positivity
                 have hc : 2*((2^j.val:ℕ):ℝ)^2 ≤ (Fintype.card (Fin (2^j.val) × Fin (2*2^j.val+1)):ℝ) := by
                   exact_mod_cast (dyadic_shell_card_bounds j.val).1
                 calc (1/2:ℝ) = (2*((2^j.val:ℕ):ℝ)^2)*((1/((2^j.val:ℕ):ℝ))^2/4) := by field_simp; norm_num
                      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
       _ ≤ _ := Finset.sum_le_sum fun p _ => hp p

theorem dyadic_sin_cancel (k : ℕ) :
    (∑ p : DyadicFreq k, (1/(dyadicRadius p:ℝ))^3 *
      Real.sin (dyadicAngle k (dyadicPoint p).2)) = 0 := by
  let e : DyadicFreq k ≃ DyadicFreq k := ⟨dyadicReflect, dyadicReflect, dyadicReflect_involution, dyadicReflect_involution⟩
  have he := Equiv.sum_comp e
    (fun p : DyadicFreq k => (1/(dyadicRadius p:ℝ))^3 * Real.sin (dyadicAngle k (dyadicPoint p).2))
  change (∑ p : DyadicFreq k, (1/(dyadicRadius (dyadicReflect p):ℝ))^3 * Real.sin (dyadicAngle k (dyadicPoint (dyadicReflect p)).2)) = _ at he
  simp only [dyadicReflect_radius, dyadicReflect_point,
    Int.cast_neg, dyadicAngle_neg, Real.sin_neg, mul_neg, Finset.sum_neg_distrib] at he
  linarith

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.DyadicModes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace ClassicalON

variable {k : ℕ}

theorem groupedTorusPoint_injective (m s : Bool) :
    Function.Injective (groupedTorusPoint (k := k) m s) := by
  have hs := dyadicTorusPoint_injective (k := k)
  cases m <;> cases s <;> intro p q h <;> apply hs
  · exact h
  · simpa [groupedTorusPoint, groupedPoint, dyadicTorusPoint, Prod.ext_iff] using h
  · exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  · have h' : (dyadicTorusPoint p).swap = (dyadicTorusPoint q).swap := by
      simpa [groupedTorusPoint, groupedPoint, dyadicTorusPoint, Prod.ext_iff] using h
    exact Prod.swap_injective h'

theorem dyadicWeight_pos (p : DyadicFreq k) : 0 < dyadicWeight p := by
  have h : (0:ℝ)<dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
  unfold dyadicWeight
  positivity

@[simp] theorem dyadicWeight_sq (p : DyadicFreq k) :
    dyadicWeight p^2 = (1/(dyadicRadius p:ℝ))^3 := by
  have hr : (0:ℝ)<dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
  unfold dyadicWeight
  rw [div_pow, mul_pow, Real.sq_sqrt hr.le]
  field_simp

@[simp] theorem dyadicWeight_mul_sqrt (p : DyadicFreq k) :
    dyadicWeight p*Real.sqrt (dyadicRadius p:ℝ) = 1/(dyadicRadius p:ℝ) := by
  have hr : (0:ℝ)<dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
  have hs : Real.sqrt (dyadicRadius p:ℝ) ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  unfold dyadicWeight
  field_simp

theorem wave_commutator (a b c θ : ℝ) (w : ℂ) (hw : ‖w‖=1) :
    ((a*b:ℝ):ℂ)*w * conj (((a*c:ℝ):ℂ)*w*Complex.exp (Complex.I*(θ:ℂ))) / 2 -
      conj (((a*b:ℝ):ℂ)*w) * (((a*c:ℝ):ℂ)*w*Complex.exp (Complex.I*(θ:ℂ))) / 2 =
        -Complex.I * ((a^2*b*c*Real.sin θ:ℝ):ℂ) := by
  have hww : w*conj w=1 := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]; norm_num
  rw [mul_comm Complex.I (θ:ℂ), Complex.exp_ofReal_mul_I]
  simp only [map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  linear_combination -Complex.I*(a:ℂ)^2*(b:ℂ)*(c:ℂ)*(Complex.sin (θ:ℂ)) * hww

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.MatrixSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP uX

noncomputable section
open scoped BigOperators ComplexConjugate

namespace ClassicalON

variable {X : Type uX} {P : Type uP} [Fintype X] [Fintype P]

theorem SquareBound.column {U : X → P → ℂ} {a : ℝ} (h : SquareBound U a) (p : P) :
    ∑ x, ‖U x p‖^2 ≤ a^2 := by
  classical
  have hs : (∑ q : P, ‖((Pi.single p (1:ℂ)) : P → ℂ) q‖^2) = 1 := by
    simp only [Pi.single_apply, apply_ite, norm_one, norm_zero, ite_pow, one_pow,
      zero_pow (by decide : 2 ≠ 0), Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have he := h (Pi.single p 1)
  rw [hs, mul_one] at he
  simpa only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] using he

theorem SquareBound.gram_weighted {U : X → P → ℂ} {a : ℝ}
    (h : SquareBound U a) (d : P → ℂ) :
    (∑ x, ∑ y, ‖∑ p, U x p*d p*conj (U y p)‖^2) ≤ a^4*∑ p, ‖d p‖^2 := by
  calc _ = ∑ y, ∑ x, ‖∑ p, U x p*(d p*conj (U y p))‖^2 := by
          simp only [mul_assoc]
          exact Finset.sum_comm
       _ ≤ ∑ y, a^2*∑ p, ‖d p*conj (U y p)‖^2 :=
          Finset.sum_le_sum fun y _ => h (fun p => d p*conj (U y p))
       _ = a^2*∑ p, ‖d p‖^2*(∑ y, ‖U y p‖^2) := by
          simp only [norm_mul, Complex.norm_conj, mul_pow, Finset.mul_sum]
          rw [Finset.sum_comm]
       _ ≤ a^2*∑ p, ‖d p‖^2*a^2 := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (h.column p) (sq_nonneg _)
       _ = _ := by rw [← Finset.sum_mul]; ring

theorem sum_norm_add_sq_le (f g : X → ℂ) :
    (∑ x, ‖f x+g x‖^2) ≤ 2*(∑ x, ‖f x‖^2)+2*(∑ x, ‖g x‖^2) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  have hv := norm_add_le (f x) (g x)
  have hsq := sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr hv
  nlinarith [sq_nonneg (‖f x‖-‖g x‖)]

theorem parseval_of_orthogonal [DecidableEq P] (W : X → P → ℂ) (M : ℝ)
    (ho : ∀ p q, (∑ x, W x p*conj (W x q)) = if p=q then (M:ℂ) else 0)
    (v : P → ℂ) :
    (∑ x, ‖∑ p, W x p*v p‖^2) = M*∑ p, ‖v p‖^2 := by
  classical
  have he : (∑ x, (∑ p, W x p*v p)*conj (∑ q, W x q*v q)) =
      (M:ℂ)*∑ p, v p*conj (v p) := by
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    calc
      (∑ x, ∑ q, ∑ p, W x p*v p*(conj (W x q)*conj (v q))) =
          ∑ q, ∑ p, ∑ x, W x p*v p*(conj (W x q)*conj (v q)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun q _ => Finset.sum_comm)
      _ = ∑ p, ∑ q, (∑ x, W x p*conj (W x q))*(v p*conj (v q)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro q _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by simp [ho]
  have hr := congrArg Complex.re he
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.ofReal_re, ← Complex.ofReal_sum, ← Complex.ofReal_mul] at hr
  exact hr

theorem parseval_diagonal_bound [DecidableEq P] (W : X → P → ℂ) (M c : ℝ) (hM : 0 ≤ M)
    (ho : ∀ p q, (∑ x, W x p*conj (W x q)) = if p=q then (M:ℂ) else 0)
    (d v : P → ℂ) (hd : ∀ p, ‖d p‖ ≤ c) :
    (∑ x, ‖∑ p, W x p*(d p*v p)‖^2) ≤ (M*c^2)*∑ p, ‖v p‖^2 := by
  rw [parseval_of_orthogonal W M ho, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hM
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hd p) 2) (sq_nonneg _)

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.FourierOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP uX uY

noncomputable section
open scoped BigOperators ComplexConjugate
namespace ClassicalON

variable {X : Type uX} {P : Type uP} {Y : Type uY} [Fintype X] [Fintype P] [Fintype Y]

theorem sum_norm_pointwise_mul_sq_le (d v : X → ℂ) (c : ℝ) (hd : ∀ x, ‖d x‖ ≤ c) :
    (∑ x, ‖d x*v x‖^2) ≤ c^2*∑ x, ‖v x‖^2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun x _ => by
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hd x) 2) (sq_nonneg _)

theorem sum_norm_sq_restrict (i : Y → X) (hi : Function.Injective i) (v : X → ℂ) :
    (∑ y, ‖v (i y)‖^2) ≤ ∑ x, ‖v x‖^2 := by
  classical
  calc _ = ∑ x ∈ Finset.univ.image i, ‖v x‖^2 := (Finset.sum_image (fun a _ b _ h => hi h)).symm
       _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg fun x => sq_nonneg _

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.EdgeOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP uX uY

noncomputable section
open scoped BigOperators ComplexConjugate
namespace ClassicalON

theorem restricted_modulated_fourier_bound {X : Type uX} {P : Type uP} {Y : Type uY}
    [Fintype X] [Fintype P] [Fintype Y] [DecidableEq P]
    (W : X → P → ℂ) (M C A : ℝ) (hM : 0 ≤ M)
    (hW : ∀ p q, (∑ x, W x p*conj (W x q)) = if p=q then (M:ℂ) else 0)
    (i : Y → X) (hi : Function.Injective i) (d : Y → ℂ) (a v : P → ℂ)
    (hd : ∀ y, ‖d y‖ ≤ C) (ha : ∀ p, ‖a p‖ ≤ A) :
    (∑ y, ‖d y*(∑ p, W (i y) p*(a p*v p))‖^2) ≤ (C^2*M*A^2)*∑ p, ‖v p‖^2 := by
  calc _ ≤ C^2*∑ y, ‖∑ p, W (i y) p*(a p*v p)‖^2 := sum_norm_pointwise_mul_sq_le _ _ C hd
       _ ≤ C^2*∑ x, ‖∑ p, W x p*(a p*v p)‖^2 :=
          mul_le_mul_of_nonneg_left (sum_norm_sq_restrict i hi (fun x => ∑ p, W x p*(a p*v p))) (sq_nonneg _)
       _ ≤ C^2*((M*A^2)*∑ p, ‖v p‖^2) := mul_le_mul_of_nonneg_left
          (parseval_diagonal_bound W M A hM hW a v ha) (sq_nonneg _)
       _ = _ := by ring

theorem edge_cutoff_squareBound {P : Type uP} {Y : Type uY} [Fintype P] [Fintype Y] [DecidableEq P]
    {L : ℕ} [NeZero L] (p : P → DiscreteTorus L) (hp : Function.Injective p)
    (i : Y → DiscreteTorus L) (hi : Function.Injective i) (h : DiscreteTorus L)
    (φ₀ φ₁ : Y → ℂ) (a : P → ℂ)
    (D C A B : ℝ) (hD : ∀ y, ‖φ₁ y-φ₀ y‖ ≤ D) (hC : ∀ y, ‖φ₁ y‖ ≤ C)
    (hA : ∀ q, ‖a q‖ ≤ A) (hB : ∀ q, ‖a q*(torusWave (p q) h-1)‖ ≤ B) :
    SquareBound (fun y q => a q*(φ₁ y*torusWave (p q) (i y+h)-φ₀ y*torusWave (p q) (i y)))
      (Real.sqrt (2*(L:ℝ)^2*(D^2*A^2+C^2*B^2))) := by
  intro v
  rw [Real.sq_sqrt (by positivity)]
  let f := fun y => (φ₁ y-φ₀ y)*(∑ q, torusWave (p q) (i y)*(a q*v q))
  let g := fun y => φ₁ y*(∑ q, torusWave (p q) (i y)*((a q*(torusWave (p q) h-1))*v q))
  have he (y : Y) :
      (∑ q, a q*(φ₁ y*torusWave (p q) (i y+h)-φ₀ y*torusWave (p q) (i y))*v q) = f y+g y := by
    simp only [f, g, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    rw [torusWave_add]
    ring
  simp_rw [he]
  have hf := restricted_modulated_fourier_bound (fun x q => torusWave (p q) x) ((L:ℝ)^2) D A
    (sq_nonneg _) (fun q r => by simpa only [Complex.ofReal_pow] using torusWave_orthogonal_subfamily p hp q r)
    i hi (fun y => φ₁ y-φ₀ y) a v hD hA
  have hg := restricted_modulated_fourier_bound (fun x q => torusWave (p q) x) ((L:ℝ)^2) C B
    (sq_nonneg _) (fun q r => by simpa only [Complex.ofReal_pow] using torusWave_orthogonal_subfamily p hp q r)
    i hi φ₁ (fun q => a q*(torusWave (p q) h-1)) v hC hB
  have ht := sum_norm_add_sq_le f g
  dsimp only [f, g] at ht ⊢
  linarith

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.SquareEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uP uX

noncomputable section
open scoped BigOperators ComplexConjugate
namespace ClassicalON

variable {X : Type uX} {P : Type uP} {I : Type uI} [Fintype X] [Fintype P] [Fintype I]

theorem norm_sum_sq_le_card (f : I → ℂ) :
    ‖∑ i, f i‖^2 ≤ (Fintype.card I:ℝ)*∑ i, ‖f i‖^2 := by
  calc _ ≤ (∑ i, ‖f i‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
       _ ≤ _ := by
          have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (R := ℝ)
            (s := Finset.univ) (r := fun i => ‖f i‖) (f := fun _ => 1)
            (g := fun i => ‖f i‖^2) (fun _ _ => by norm_num) (fun i _ => sq_nonneg _)
            (fun i _ => le_of_eq (one_mul _).symm)
          simpa using h

theorem sum_by_fibers [DecidableEq I] (d : X → I) (f : X → ℝ) :
    (∑ x, f x) = ∑ i, ∑ x : {x // d x=i}, f x := by
  classical
  simpa only [Fintype.sum_sigma, Equiv.sigmaFiberEquiv_apply] using
    (Equiv.sum_comp (Equiv.sigmaFiberEquiv d) f).symm

theorem SquareBound.combine_directions (U : X → P → ℂ) (d : X → Bool) (a : ℝ)
    (h : ∀ m : Bool, SquareBound (fun (x : {x // d x=m}) p => U x p) a) :
    SquareBound U (2*a) := by
  intro v
  rw [sum_by_fibers d]
  calc _ ≤ ∑ _m : Bool, a^2*∑ p, ‖v p‖^2 :=
          Finset.sum_le_sum fun m _ => h m v
       _ ≤ (2*a)^2*∑ p, ‖v p‖^2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul, Nat.cast_ofNat]
          have hs : 0 ≤ ∑ p : P, ‖v p‖^2 := Finset.sum_nonneg fun p _ => sq_nonneg ‖v p‖
          nlinarith [mul_nonneg (sq_nonneg a) hs]

theorem gram_groups_bound (T : I → X → X → ℂ) (C : ℝ)
    (h : ∀ i, (∑ x, ∑ y, ‖T i x y‖^2) ≤ C) :
    (∑ x, ∑ y, ‖∑ i, T i x y‖^2) ≤ (Fintype.card I:ℝ)^2*C := by
  calc _ ≤ ∑ x, ∑ y, (Fintype.card I:ℝ)*∑ i, ‖T i x y‖^2 :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => norm_sum_sq_le_card _
       _ = (Fintype.card I:ℝ)*∑ i, ∑ x, ∑ y, ‖T i x y‖^2 := by
          simp only [← Finset.mul_sum]
          congr 1
          calc (∑ x, ∑ y, ∑ i, ‖T i x y‖^2) = ∑ x, ∑ i, ∑ y, ‖T i x y‖^2 :=
                Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
               _ = _ := Finset.sum_comm
       _ ≤ (Fintype.card I:ℝ)*∑ _i : I, C := by gcongr with i; exact h i
       _ = _ := by simp; ring

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.LatticeModes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace ClassicalON

variable {k : ℕ}

theorem groupedPoint_abs_bound (m s : Bool) (p : DyadicFreq k) :
    |(groupedPoint m s p).1| ≤ 2*(dyadicRadius p:ℤ) ∧
    |(groupedPoint m s p).2| ≤ 2*(dyadicRadius p:ℤ) := by
  have hp := dyadicPoint_bounds p
  have hr : (0:ℤ)<dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
  have h1 : |(dyadicPoint p).1| ≤ 2*(dyadicRadius p:ℤ) := abs_le.mpr (by constructor <;> omega)
  have h2 : |(dyadicPoint p).2| ≤ 2*(dyadicRadius p:ℤ) := abs_le.mpr (by constructor <;> omega)
  cases m <;> cases s
  · simpa [groupedPoint] using And.intro h1 h2
  · simpa [groupedPoint] using And.intro h1 h2
  · simpa [groupedPoint] using And.intro h2 h1
  · simpa [groupedPoint] using And.intro h2 h1

theorem groupedWave_axis (m s j : Bool) (p : DyadicFreq k) :
    torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) (latticeAxis j)) =
      ZMod.stdAddChar ((if j then (groupedPoint m s p).2 else (groupedPoint m s p).1):ZMod (16*2^k)) := by
  cases j <;> simp [torusWave, groupedTorusPoint, latticeTorus, latticeAxis]

theorem groupedWave_axis_sine (m s j : Bool) (p : DyadicFreq k) :
    torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) (latticeAxis j)) =
      Complex.exp (Complex.I*((dyadicAngle k ((if j then (groupedPoint m s p).2 else (groupedPoint m s p).1):ℤ):ℝ):ℂ)) := by
  rw [groupedWave_axis]
  cases j <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals
    rw [ZMod.stdAddChar_coe]
    congr 1
    unfold dyadicAngle
    push_cast
    ring

theorem groupedWave_multiplier_bound (m s j : Bool) (p : DyadicFreq k) :
    ‖((1/(dyadicRadius p:ℝ)):ℂ) *
      (torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) (latticeAxis j))-1)‖ ≤
        Real.pi/(4*(2:ℝ)^k) := by
  have hr : (0:ℝ)<dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
  have hp : |((if j then (groupedPoint m s p).2 else (groupedPoint m s p).1):ℤ)| ≤
      2*(dyadicRadius p:ℤ) := by
    cases j
    · exact (groupedPoint_abs_bound m s p).1
    · exact (groupedPoint_abs_bound m s p).2
  have hp' : |(((if j then (groupedPoint m s p).2 else (groupedPoint m s p).1):ℤ):ℝ)| ≤ 2*(dyadicRadius p:ℝ) := by exact_mod_cast hp
  simp only [norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  rw [groupedWave_axis]
  have hchar : ‖ZMod.stdAddChar (if j then ((groupedPoint m s p).2:ZMod (16*2^k)) else ((groupedPoint m s p).1:ZMod (16*2^k)))-1‖ ≤
      (2*Real.pi/(16*2^k:ℕ))*|(((if j then (groupedPoint m s p).2 else (groupedPoint m s p).1):ℤ):ℝ)| := by
    cases j <;> exact norm_stdAddChar_intCast_sub_one (L := 16*2^k) _
  calc _ ≤ (1/(dyadicRadius p:ℝ))*((2*Real.pi/(16*2^k:ℕ))*|(((if j then (groupedPoint m s p).2 else (groupedPoint m s p).1):ℤ):ℝ)|) :=
          mul_le_mul_of_nonneg_left hchar (by positivity)
       _ ≤ (1/(dyadicRadius p:ℝ))*((2*Real.pi/(16*2^k:ℕ))*(2*(dyadicRadius p:ℝ))) := by gcongr
       _ = Real.pi/(4*(2:ℝ)^k) := by push_cast; field_simp [ne_of_gt hr]; ring

theorem latticeMode_norm_bound (m s : Bool) (p : DyadicFreq k) (x : Site) (C : ℝ)
    (hC : |squareProfile m s (scaledSite k x)| ≤ C) : ‖latticeMode m s p x‖ ≤ dyadicWeight p*C := by
  simp only [latticeMode, norm_mul, torusWave_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (dyadicWeight_pos p)]
  exact mul_le_mul_of_nonneg_left hC (dyadicWeight_pos p).le

namespace LatticeGraph

theorem scaledModeGradient_formula (G : LatticeGraph) (m s : Bool) (p : DyadicFreq k) (e : G.edges) :
    G.scaledModeGradient m s p e =
      ((1/(dyadicRadius p:ℝ)):ℂ) *
      ((squareProfile m s (scaledSite k e.val.2.val):ℂ)*torusWave (groupedTorusPoint m s p)
        (latticeTorus (16*2^k) e.val.1.val+latticeTorus (16*2^k) (latticeAxis (G.edgeDirection e))) -
       (squareProfile m s (scaledSite k e.val.1.val):ℂ)*torusWave (groupedTorusPoint m s p)
        (latticeTorus (16*2^k) e.val.1.val)) := by
  have h := congrArg Complex.ofReal (dyadicWeight_mul_sqrt p)
  push_cast at h
  simp only [scaledModeGradient, modeGradient, latticeMode]
  rw [G.edge_step e, latticeTorus_add]
  linear_combination ( ((squareProfile m s (scaledSite k (e.val.1.val+latticeAxis (G.edgeDirection e))):ℂ)*
    torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) e.val.1.val+latticeTorus (16*2^k) (latticeAxis (G.edgeDirection e)))) -
    ((squareProfile m s (scaledSite k e.val.1.val):ℂ)*torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) e.val.1.val)) ) * h

end LatticeGraph
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.DyadicSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace ClassicalON

theorem dyadic_inverse_square_sum (k : ℕ) :
    (∑ p : DyadicFreq k, (1/(dyadicRadius p:ℝ))^2) ≤ 3*(k:ℝ) := by
  rw [Fintype.sum_sigma]
  calc _ ≤ ∑ j : Fin k, (3:ℝ) := by
          apply Finset.sum_le_sum
          intro j _
          simp only [dyadicRadius, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          have hr : (0:ℝ) < (2^j.val:ℕ) := by positivity
          have hc : (Fintype.card (Fin (2^j.val) × Fin (2*2^j.val+1)):ℝ) ≤ 3*((2^j.val:ℕ):ℝ)^2 := by
            exact_mod_cast (dyadic_shell_card_bounds j.val).2
          calc _ ≤ (3*((2^j.val:ℕ):ℝ)^2)*(1/((2^j.val:ℕ):ℝ))^2 :=
                mul_le_mul_of_nonneg_right hc (sq_nonneg _)
               _ = 3 := by field_simp
       _ = _ := by simp; ring

theorem sum_dyadic_ratio_lower (k i : ℕ) :
    (∑ j ∈ Finset.range k, if j ≤ i then (2:ℝ)^j/2^i else 0) ≤ 2 := by
  classical
  rw [← Finset.sum_filter]
  have hs : (Finset.range k).filter (fun j => j ≤ i) ⊆ Finset.range (i+1) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    omega
  calc _ ≤ ∑ j ∈ Finset.range (i+1), (2:ℝ)^j/2^i :=
          Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)
       _ ≤ 2 := by
          rw [← Finset.sum_div]
          have hh := geom_sum_mul (2:ℝ) (i+1)
          have hp : (0:ℝ) < 2^i := by positivity
          rw [div_le_iff₀ hp]
          simp only [show (2:ℝ)-1=1 by norm_num, mul_one,
            pow_succ] at hh
          linarith

theorem dyadic_min_ratio_sum (k : ℕ) :
    (∑ i : Fin k, ∑ j : Fin k, min ((2:ℝ)^i.val/2^j.val) (2^j.val/2^i.val)) ≤ 4*(k:ℝ) := by
  classical
  have point (i j : Fin k) : min ((2:ℝ)^i.val/2^j.val) (2^j.val/2^i.val) ≤
      (if j.val ≤ i.val then (2:ℝ)^j.val/2^i.val else 0)+
      (if i.val ≤ j.val then (2:ℝ)^i.val/2^j.val else 0) := by
    by_cases h : j.val ≤ i.val
    · rw [ite_eq_left h]
      exact (min_le_right _ _).trans (le_add_of_nonneg_right (by split_ifs <;> positivity))
    · have hh : i.val ≤ j.val := by omega
      rw [ite_eq_right h, ite_eq_left hh, zero_add]
      exact min_le_left _ _
  have hs : (∑ i : Fin k, ∑ j : Fin k, if j.val ≤ i.val then (2:ℝ)^j.val/2^i.val else 0) ≤ 2*(k:ℝ) := by
    calc _ ≤ ∑ _i : Fin k, (2:ℝ) := by
            apply Finset.sum_le_sum
            intro i _
            rw [← Finset.sum_range (fun j => if j ≤ i.val then (2:ℝ)^j/2^i.val else 0)]
            exact sum_dyadic_ratio_lower k i.val
         _ = _ := by simp; ring
  calc _ ≤ ∑ i : Fin k, ∑ j : Fin k,
          ((if j.val ≤ i.val then (2:ℝ)^j.val/2^i.val else 0)+
           (if i.val ≤ j.val then (2:ℝ)^i.val/2^j.val else 0)) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => point i j
       _ = 2*∑ i : Fin k, ∑ j : Fin k, if j.val ≤ i.val then (2:ℝ)^j.val/2^i.val else 0 := by
          simp only [Finset.sum_add_distrib]
          rw [Finset.sum_comm (f := fun i j : Fin k => if i.val ≤ j.val then (2:ℝ)^i.val/2^j.val else 0)]
          ring
       _ ≤ _ := by linarith

theorem weighted_dyadic_min_pair (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    a^2*b^2*min ((1/a)^3*(1/b)) ((1/b)^3*(1/a)) = min (b/a) (a/b) := by
  rw [mul_min_of_nonneg _ _ (by positivity : (0:ℝ) ≤ a^2*b^2)]
  congr 1 <;> field_simp

theorem dyadic_min_cost_sum (k : ℕ) :
    (∑ p : DyadicFreq k, ∑ q : DyadicFreq k,
      min ((1/(dyadicRadius p:ℝ))^3*(1/(dyadicRadius q:ℝ)))
          ((1/(dyadicRadius q:ℝ))^3*(1/(dyadicRadius p:ℝ)))) ≤ 36*(k:ℝ) := by
  simp only [Fintype.sum_sigma]
  have he : (∑ i : Fin k, ∑ a : Fin (2^i.val) × Fin (2*2^i.val+1),
      ∑ j : Fin k, ∑ b : Fin (2^j.val) × Fin (2*2^j.val+1),
      min ((1/(dyadicRadius ⟨i,a⟩:ℝ))^3*(1/(dyadicRadius ⟨j,b⟩:ℝ)))
          ((1/(dyadicRadius ⟨j,b⟩:ℝ))^3*(1/(dyadicRadius ⟨i,a⟩:ℝ)))) =
      ∑ i : Fin k, ∑ j : Fin k,
      (Fintype.card (Fin (2^i.val) × Fin (2*2^i.val+1)):ℝ)*
      (Fintype.card (Fin (2^j.val) × Fin (2*2^j.val+1)):ℝ)*
      min ((1/(2:ℝ)^i.val)^3*(1/(2:ℝ)^j.val))
          ((1/(2:ℝ)^j.val)^3*(1/(2:ℝ)^i.val)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp only [dyadicRadius, Nat.cast_pow, Nat.cast_ofNat, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [he]
  calc _ ≤ ∑ i : Fin k, ∑ j : Fin k, 9*min ((2:ℝ)^i.val/2^j.val) (2^j.val/2^i.val) := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          have hi : (Fintype.card (Fin (2^i.val) × Fin (2*2^i.val+1)):ℝ) ≤ 3*((2:ℝ)^i.val)^2 := by
            exact_mod_cast (dyadic_shell_card_bounds i.val).2
          have hj : (Fintype.card (Fin (2^j.val) × Fin (2*2^j.val+1)):ℝ) ≤ 3*((2:ℝ)^j.val)^2 := by
            exact_mod_cast (dyadic_shell_card_bounds j.val).2
          calc _ ≤ (3*((2:ℝ)^i.val)^2)*(3*((2:ℝ)^j.val)^2)*
                min ((1/(2:ℝ)^i.val)^3*(1/(2:ℝ)^j.val)) ((1/(2:ℝ)^j.val)^3*(1/(2:ℝ)^i.val)) := by
                  gcongr
               _ = _ := by
                  rw [show (3*((2:ℝ)^i.val)^2)*(3*((2:ℝ)^j.val)^2) = 9*(((2:ℝ)^i.val)^2*((2:ℝ)^j.val)^2) by ring,
                    mul_assoc, weighted_dyadic_min_pair _ _ (by positivity) (by positivity), min_comm]
       _ ≤ _ := by
          simp only [← Finset.mul_sum]
          have hs := dyadic_min_ratio_sum k
          linarith

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.ModeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace ClassicalON
namespace LatticeGraph
variable {k : ℕ}

theorem scaledModes_direction_bound (G : LatticeGraph) (hG : G.WithinDyadicBox k)
    (C : ℝ)
    (hval : ∀ m s z, |squareProfile m s z| ≤ C)
    (hLip : ∀ m s z w, |squareProfile m s w-squareProfile m s z| ≤ C*‖w-z‖)
    (m s j : Bool) :
    SquareBound (fun (e : G.DirectionalEdges j) (p : DyadicFreq k) => G.scaledModeGradient m s p e.val)
      (modeBlockConstant C) := by
  classical
  have hN : (2:ℝ)^k ≠ 0 := by positivity
  have hd (e : G.DirectionalEdges j) :
      ‖(squareProfile m s (scaledSite k e.val.val.2.val):ℂ)-
        (squareProfile m s (scaledSite k e.val.val.1.val):ℂ)‖ ≤ C/(2:ℝ)^k := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simpa only [G.scaled_edge_distance, div_eq_mul_inv, one_mul] using
      hLip m s (scaledSite k e.val.val.1.val) (scaledSite k e.val.val.2.val)
  have hv (e : G.DirectionalEdges j) :
      ‖(squareProfile m s (scaledSite k e.val.val.2.val):ℂ)‖ ≤ C := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hval m s (scaledSite k e.val.val.2.val)
  have ha (p : DyadicFreq k) : ‖((1/(dyadicRadius p:ℝ)):ℂ)‖ ≤ 1 := by
    have hp : (1:ℝ) ≤ dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
    simp only [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ dyadicRadius p)]
    exact (div_le_one (by positivity)).mpr hp
  have hh := edge_cutoff_squareBound (groupedTorusPoint m s) (groupedTorusPoint_injective m s)
    (fun e : G.DirectionalEdges j => latticeTorus (16*2^k) e.val.val.1.val)
    (G.directional_torus_injective k hG j) (latticeTorus (16*2^k) (latticeAxis j))
    (fun e => (squareProfile m s (scaledSite k e.val.val.1.val):ℂ))
    (fun e => (squareProfile m s (scaledSite k e.val.val.2.val):ℂ))
    (fun p => ((1/(dyadicRadius p:ℝ)):ℂ)) (C/(2:ℝ)^k) C 1 (Real.pi/(4*(2:ℝ)^k))
    hd hv ha (groupedWave_multiplier_bound m s j)
  have hc : Real.sqrt (2*((16*2^k:ℕ):ℝ)^2*((C/(2:ℝ)^k)^2*1^2+C^2*(Real.pi/(4*(2:ℝ)^k))^2)) = modeBlockConstant C := by
    congr 1
    push_cast
    field_simp [hN]
    ring
  rw [hc] at hh
  have hdir (e : G.DirectionalEdges j) : G.edgeDirection e.val=j := e.property
  exact fun v => by simpa only [G.scaledModeGradient_formula, hdir] using hh v

theorem scaledModes_squareBound (G : LatticeGraph) (hG : G.WithinDyadicBox k)
    (C : ℝ)
    (hval : ∀ m s z, |squareProfile m s z| ≤ C)
    (hLip : ∀ m s z w, |squareProfile m s w-squareProfile m s z| ≤ C*‖w-z‖)
    (m s : Bool) :
    SquareBound (fun e (p : DyadicFreq k) => G.scaledModeGradient m s p e) (2*modeBlockConstant C) := by
  apply SquareBound.combine_directions _ G.edgeDirection
  exact fun j => G.scaledModes_direction_bound hG C hval hLip m s j

end LatticeGraph
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.MixedWard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uK uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

variable {n : ℕ}

omit [Fintype V] [Fintype E] in
theorem operator_smul_pow (r : ℝ) (M : SpinOperator n) (k : ℕ) :
    (r • M)^k = r^k • M^k := by
  induction k with
  | zero => simp only [pow_zero, one_smul]
  | succ k ih =>
    rw [pow_succ, ih, Algebra.smul_mul_assoc (r^k) (M^k) (r • M),
      Algebra.mul_smul_comm r (M^k) M, smul_smul (r^k) r (M^k*M),
      ← pow_succ, ← pow_succ]

attribute [local fun_prop] continuous_energy

omit [Fintype V] in
theorem secondObservable_add_left (S : SpinSystem 3 V E) (u v w : E → ℝ) :
    S.secondObservable (u+v) w = S.secondObservable u w + S.secondObservable v w := by
  ext σ
  change S.energy (fun e => (((u+v) e)*w e) • axisC^2) σ +
    S.energy (fun e => (u+v) e • axisC) σ * S.energy (fun e => w e • axisC) σ =
    (S.energy (fun e => (u e*w e) • axisC^2) σ +
      S.energy (fun e => u e • axisC) σ * S.energy (fun e => w e • axisC) σ) +
    (S.energy (fun e => (v e*w e) • axisC^2) σ +
      S.energy (fun e => v e • axisC) σ * S.energy (fun e => w e • axisC) σ)
  simp only [energy_weighted]
  change MixedAlgebra.weighted (S.localCoefficient (axisC^2) σ) ((u+v)*w) +
      MixedAlgebra.weighted (S.localCoefficient axisC σ) (u+v) *
        MixedAlgebra.weighted (S.localCoefficient axisC σ) w = _
  rw [add_mul, MixedAlgebra.weighted_add, MixedAlgebra.weighted_add]
  simp only [MixedAlgebra.weighted, Pi.mul_apply]
  ring

omit [Fintype V] in
theorem secondObservable_symm (S : SpinSystem 3 V E) (u v : E → ℝ) :
    S.secondObservable u v = S.secondObservable v u := by
  ext σ
  change S.energy (fun e => (u e*v e) • axisC^2) σ +
    S.energy (fun e => u e • axisC) σ * S.energy (fun e => v e • axisC) σ = _
  simp only [mul_comm, secondObservable, ContinuousMap.coe_mk]

theorem secondAxisResponse_add_left (S : SpinSystem 3 V E) (u v w : E → ℝ) :
    S.secondAxisResponse (u+v) w = S.secondAxisResponse u w + S.secondAxisResponse v w := by
  have h := congrArg S.averageLinear (S.secondObservable_add_left u v w)
  simpa only [map_add, secondObservable_average] using h

theorem secondAxisResponse_symm (S : SpinSystem 3 V E) (u v : E → ℝ) :
    S.secondAxisResponse u v = S.secondAxisResponse v u := by
  exact congrArg S.averageLinear (S.secondObservable_symm u v)

theorem secondAxisResponse_add_right (S : SpinSystem 3 V E) (u v w : E → ℝ) :
    S.secondAxisResponse u (v+w) = S.secondAxisResponse u v + S.secondAxisResponse u w := by
  rw [S.secondAxisResponse_symm, S.secondAxisResponse_add_left,
    S.secondAxisResponse_symm v, S.secondAxisResponse_symm w]

end ClassicalON.SpinSystem

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.ComplexWard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uE uK uL uV uΩ

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

theorem complex_linear_zero_of_real {V : Type uV} (P : V → Prop)
    (L : (V → ℂ) → ℂ)
    (ha : ∀ u v, L (u+v) = L u + L v)
    (hs : ∀ r u, L (r • u) = r * L u)
    (hr : ∀ u : V → ℝ, (∀ x, P x → u x = 0) → L (fun x => (u x : ℂ)) = 0)
    (u : V → ℂ) (hu : ∀ x, P x → u x = 0) : L u = 0 := by
  have hre : ∀ x, P x → (u x).re = 0 := by
    intro x hx
    rw [hu x hx, Complex.zero_re]
  have him : ∀ x, P x → (u x).im = 0 := by
    intro x hx
    rw [hu x hx, Complex.zero_im]
  have hd : u = (fun x => ((u x).re : ℂ)) + Complex.I • (fun x => ((u x).im : ℂ)) := by
    ext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm]
    exact (Complex.re_add_im (u x)).symm
  rw [hd, ha, hs, hr _ hre, hr _ him]
  simp only [mul_zero, add_zero]

namespace MixedAlgebra
variable {E : Type uE} {K : Type uK} {L : Type uL} [Fintype E] [CommRing K] [CommRing L]

theorem weighted_map (φ : K →+* L) (J u : E → K) :
    weighted (φ ∘ J) (φ ∘ u) = φ (weighted J u) := by
  simp [weighted]

end MixedAlgebra

namespace ClassicalON.SpinSystem
variable {n : ℕ} {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] in
theorem complexEnergy_ofReal (S : SpinSystem n V E) (M : SpinOperator n)
    (u : E → ℝ) (σ : V → Spin n) :
    S.complexEnergy M (fun e => (u e : ℂ)) σ =
      (S.energy (fun e => u e • M) σ : ℂ) := by
  rw [S.energy_weighted]
  exact MixedAlgebra.weighted_map Complex.ofRealHom (S.localCoefficient M σ) u

theorem complexSecondResponse_ofReal (S : SpinSystem 3 V E) (u v : E → ℝ) :
    S.complexSecondResponse (fun e => (u e : ℂ)) (fun e => (v e : ℂ)) =
      (S.secondAxisResponse u v : ℂ) := by
  have hp : S.complexSecondObservable (fun e => (u e : ℂ)) (fun e => (v e : ℂ)) =
      ofRealObservable (S.secondObservable u v) := by
    ext σ
    change S.complexEnergy (axisC^2) ((fun e => (u e : ℂ)) * (fun e => (v e : ℂ))) σ +
      S.complexEnergy axisC (fun e => (u e : ℂ)) σ *
        S.complexEnergy axisC (fun e => (v e : ℂ)) σ = _
    rw [show ((fun e => (u e : ℂ)) * (fun e => (v e : ℂ))) =
      (fun e => ((u e*v e : ℝ) : ℂ)) from by ext; simp]
    simp only [complexEnergy_ofReal, ← Complex.ofReal_add, ← Complex.ofReal_mul]
    rfl
  unfold complexSecondResponse
  rw [hp, S.averageComplex_ofReal, S.secondObservable_average]

omit [Fintype V] [Fintype E] in
theorem differential_ofReal (S : SpinSystem n V E) (f : V → ℝ) :
    S.differential (fun x => (f x : ℂ)) = fun e => (S.differential (K := ℝ) f e : ℂ) := by
  ext e
  simp [differential]

end ClassicalON.SpinSystem

end
end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.FamilyAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uJ uK

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MixedAlgebra
variable {I : Type uI} {J : Type uJ} {E : Type uE} {K : Type uK} [Fintype I] [Fintype J] [Fintype E] [CommRing K]

lemma sum_three_rotate (F : I → J → E → K) :
    (∑ i, ∑ j, ∑ e, F i j e) = ∑ e, ∑ i, ∑ j, F i j e := by
  calc _ = ∑ i, ∑ e, ∑ j, F i j e := by
         apply Finset.sum_congr rfl
         intro i _
         exact Finset.sum_comm
       _ = _ := Finset.sum_comm

lemma sum_weighted_separated (A : E → K) (p : I → E → K) (q : J → E → K)
    (a : I → K) (b : J → K) :
    (∑ i, ∑ j, weighted A (p i * q j) * a i * b j) =
      ∑ e, A e * (∑ i, p i e * a i) * (∑ j, q j e * b j) := by
  simp only [weighted, Finset.sum_mul, Pi.mul_apply]
  rw [sum_three_rotate]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma sum_current (B : E → K) (p : I → E → K) (a : I → K) :
    (∑ i, a i * weighted B (p i)) = weighted B (fun e => ∑ i, a i * p i e) := by
  simp only [weighted, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma contract_two_current (A B C : E → K) (p q : I → E → K) (r s : J → E → K) :
    (∑ i, ∑ j, weighted A (p i * r j) * weighted B (q i) * weighted C (s j)) =
      ∑ e, A e * weighted B (fun l => ∑ i, p i e * q i l) *
        weighted C (fun l => ∑ j, r j e * s j l) := by
  rw [sum_weighted_separated]
  simp only [sum_current]

lemma contract_two_two (A B : E → K) (p q : I → E → K) (r s : J → E → K) :
    (∑ i, ∑ j, weighted A (p i * r j) * weighted B (q i * s j)) =
      ∑ e, ∑ l, A e * B l * (∑ i, p i e * q i l) * (∑ j, r j e * s j l) := by
  have h (i : I) (j : J) : weighted A (p i * r j) * weighted B (q i * s j) =
      ∑ l, B l * (weighted A (p i*r j) * q i l * s j l) := by
    simp only [weighted, Finset.mul_sum, Pi.mul_apply]
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [h]
  rw [sum_three_rotate]
  simp_rw [← Finset.mul_sum]
  simp_rw [sum_weighted_separated]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma contract_three_current (A B : E → K) (p q : I → E → K) (r s : J → E → K) :
    (∑ i, ∑ j, weighted A (p i*q i*r j) * weighted B (s j)) =
      ∑ e, A e * (∑ i, p i e*q i e) * weighted B (fun l => ∑ j, r j e*s j l) := by
  have h := sum_weighted_separated A (fun i => p i*q i) r (fun _ => 1)
    (fun j => weighted B (s j))
  simpa only [mul_one, Pi.mul_apply, sum_current] using h

lemma contract_four (A : E → K) (p q : I → E → K) (r s : J → E → K) :
    (∑ i, ∑ j, weighted A (p i*q i*r j*s j)) =
      ∑ e, A e * (∑ i, p i e*q i e) * (∑ j, r j e*s j e) := by
  have h := sum_weighted_separated A (fun i => p i*q i) (fun j => r j*s j)
    (fun _ => 1) (fun _ => 1)
  simpa only [mul_one, Pi.mul_apply, mul_assoc] using h

lemma four_grouped (C : Coeffs E K) (u v w z : E → K) :
    four C u v w z =
    (weighted C.a u * weighted C.b v + weighted C.ab (u*v)) *
      (weighted C.a w * weighted C.b z + weighted C.ab (w*z)) +
    (weighted C.aa (u*w) * weighted C.b v * weighted C.b z +
      weighted C.ab (u*z) * weighted C.b v * weighted C.a w +
      weighted C.ab (v*w) * weighted C.a u * weighted C.b z +
      weighted C.bb (v*z) * weighted C.a u * weighted C.a w +
      weighted C.aa (u*w) * weighted C.bb (v*z) +
      weighted C.ab (u*z) * weighted C.ab (v*w) +
      weighted C.aab (u*v*w) * weighted C.b z +
      weighted C.abb (u*v*z) * weighted C.a w +
      weighted C.aab (u*w*z) * weighted C.b v +
      weighted C.abb (v*w*z) * weighted C.a u +
      weighted C.aabb (u*v*w*z)) := by
  unfold four
  ring

lemma contract_current_three (A B : E → K) (p q : I → E → K) (r s : J → E → K) :
    (∑ i, ∑ j, weighted A (p i*r j*s j) * weighted B (q i)) =
      ∑ e, A e * (∑ j, r j e*s j e) * weighted B (fun l => ∑ i, p i e*q i l) := by
  rw [Finset.sum_comm]
  simpa only [mul_comm, mul_left_comm, mul_assoc] using contract_three_current A B r s p q

lemma four_family_contraction (C : Coeffs E K) (p q : I → E → K) (r s : J → E → K) :
    (∑ i, ∑ j, four C (p i) (q i) (r j) (s j)) =
      paired C p q * paired C r s +
    ((∑ e, C.aa e * weighted C.b (kernel p q e) * weighted C.b (kernel r s e)) +
      (∑ e, C.ab e * weighted C.b (kernel p q e) * weighted C.a (kernel s r e)) +
      (∑ e, C.ab e * weighted C.a (kernel q p e) * weighted C.b (kernel r s e)) +
      (∑ e, C.bb e * weighted C.a (kernel q p e) * weighted C.a (kernel s r e)) +
      (∑ e, ∑ l, C.aa e*C.bb l * kernel p q e l * kernel r s e l) +
      (∑ e, ∑ l, C.ab e*C.ab l * kernel p q e l * kernel s r e l) +
      (∑ e, C.aab e * kernel p q e e * weighted C.b (kernel r s e)) +
      (∑ e, C.abb e * kernel p q e e * weighted C.a (kernel s r e)) +
      (∑ e, C.aab e * kernel r s e e * weighted C.b (kernel p q e)) +
      (∑ e, C.abb e * kernel r s e e * weighted C.a (kernel q p e)) +
      (∑ e, C.aabb e * kernel p q e e * kernel r s e e)) := by
  simp only [four_grouped, Finset.sum_add_distrib]
  have hp : (∑ i, ∑ j,
      (weighted C.a (p i)*weighted C.b (q i) + weighted C.ab (p i*q i)) *
      (weighted C.a (r j)*weighted C.b (s j) + weighted C.ab (r j*s j))) =
      paired C p q * paired C r s := by
    simp only [paired, Finset.sum_mul_sum]
  rw [hp, contract_two_current, contract_two_current, contract_two_current,
    contract_two_current, contract_two_two, contract_two_two,
    contract_three_current, contract_three_current, contract_current_three,
    contract_current_three, contract_four]
  rfl

end MixedAlgebra

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.GradientComplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV uΩ

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON.SpinSystem
variable {n : ℕ} {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem averageLinear_nonneg [NeZero n] (S : SpinSystem n V E)
    (f : C((V → Spin n), ℝ)) (hf : ∀ σ, 0 ≤ f σ) : 0 ≤ S.averageLinear f :=
  S.average_nonneg hf

theorem averageLinear_mono [NeZero n] (S : SpinSystem n V E)
    (f g : C((V → Spin n), ℝ)) (hfg : ∀ σ, f σ ≤ g σ) :
    S.averageLinear f ≤ S.averageLinear g := S.average_mono f.continuous g.continuous hfg

theorem averageLinear_mul_self_nonneg [NeZero n] (S : SpinSystem n V E)
    (f : C((V → Spin n), ℝ)) : 0 ≤ S.averageLinear (f*f) :=
  S.averageLinear_nonneg _ (fun σ => mul_self_nonneg (f σ))

theorem averageLinear_cauchySchwarz [NeZero n] (S : SpinSystem n V E)
    (f g : C((V → Spin n), ℝ)) :
    (S.averageLinear (f*g))^2 ≤ S.averageLinear (f*f) * S.averageLinear (g*g) := by
  have hp (t : ℝ) : 0 ≤ S.averageLinear (f*f) * (t*t) +
      (2*S.averageLinear (f*g))*t + S.averageLinear (g*g) := by
    have h := S.averageLinear_mul_self_nonneg (t • f + g)
    have he : (t • f + g)*(t • f + g) =
        (t*t) • (f*f) + (2*t) • (f*g) + g*g := by
      ext σ
      simp only [ContinuousMap.mul_apply, ContinuousMap.add_apply,
        ContinuousMap.smul_apply, smul_eq_mul]
      ring
    rw [he, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
    nlinarith
  have h := discrim_le_zero hp
  unfold discrim at h
  nlinarith

theorem averageLinear_mul_le_sqrt [NeZero n] (S : SpinSystem n V E)
    (f g : C((V → Spin n), ℝ)) :
    S.averageLinear (f*g) ≤
      Real.sqrt (S.averageLinear (f*f)) * Real.sqrt (S.averageLinear (g*g)) := by
  rw [← Real.sqrt_mul (S.averageLinear_mul_self_nonneg f)]
  exact Real.le_sqrt_of_sq_le (S.averageLinear_cauchySchwarz f g)

theorem norm_averageComplex_le [NeZero n] (S : SpinSystem n V E)
    (f : C((V → Spin n), ℂ)) :
    ‖S.averageComplexLinear f‖ ≤ S.averageLinear (normObservable f) := by
  change ‖(∫ σ, f σ * (Real.exp (S.energy (fun _ => 1) σ) : ℂ) ∂S.reference) /
    (S.Z (fun _ => 1) : ℂ)‖ ≤ _
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (S.Z_pos _)]
  calc _ ≤ (∫ σ, ‖f σ * (Real.exp (S.energy (fun _ => 1) σ) : ℂ)‖ ∂S.reference) /
      S.Z (fun _ => 1) :=
      div_le_div_of_nonneg_right (norm_integral_le_integral_norm _) (S.Z_pos _).le
    _ = S.averageLinear (normObservable f) := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      rfl

theorem complex_gradient_current_bound [NeZero n] (S : SpinSystem n V E) (β : ℝ)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (M : SpinOperator n) (hM : M ∈ skewAdjoint (SpinOperator n)) (hMn : ‖M‖ ≤ 1)
    (f : V → ℂ) (hP : ∀ x s, S.pin x = some s → f x = 0) :
    S.average (fun σ => ‖S.complexEnergy M (S.differential f) σ‖^2) ≤
      β * ∑ e, ‖S.differential f e‖^2 := by
  have hr := S.gradient_current_bound β hb M hM hMn (fun x => (f x).re)
    (fun x s hs => by rw [hP x s hs, Complex.zero_re])
  have hi := S.gradient_current_bound β hb M hM hMn (fun x => (f x).im)
    (fun x s hs => by rw [hP x s hs, Complex.zero_im])
  have he (σ : V → Spin n) : ‖S.complexEnergy M (S.differential f) σ‖^2 =
      (S.energy (S.axisGradient (fun x => (f x).re) M) σ)^2 +
      (S.energy (S.axisGradient (fun x => (f x).im) M) σ)^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, complexEnergy_re, complexEnergy_im]
    simp only [differential, Complex.sub_re, Complex.sub_im, pow_two]
    rfl
  have he' : (fun σ => ‖S.complexEnergy M (S.differential f) σ‖^2) =
      (fun σ => (S.energy (S.axisGradient (fun x => (f x).re) M) σ)^2) +
      (fun σ => (S.energy (S.axisGradient (fun x => (f x).im) M) σ)^2) := funext he
  rw [he', S.average_add
    (f := fun σ => (S.energy (S.axisGradient (fun x => (f x).re) M) σ)^2)
    (g := fun σ => (S.energy (S.axisGradient (fun x => (f x).im) M) σ)^2)
    ((S.continuous_energy _).pow 2) ((S.continuous_energy _).pow 2)]
  have hn : (∑ e, ‖S.differential f e‖^2) =
      (∑ e, ((f (S.right e)).re - (f (S.left e)).re)^2) +
      (∑ e, ((f (S.right e)).im - (f (S.left e)).im)^2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, differential, pow_two]
  rw [hn, mul_add]
  exact add_le_add hr hi

theorem averageComplex_re [NeZero n] (S : SpinSystem n V E)
    (f : C((V → Spin n), ℂ)) :
    (S.averageComplexLinear f).re = S.averageLinear (reObservable f) := by
  change ((∫ σ, f σ * (Real.exp (S.energy (fun _ => 1) σ) : ℂ) ∂S.reference) /
    (S.Z (fun _ => 1) : ℂ)).re = _
  rw [Complex.div_ofReal_re]
  have h := integral_re (S.integrable_complex_integrand f.continuous)
  simp only [RCLike.re_to_complex] at h
  rw [← h]
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  rfl

omit [Fintype V] [Fintype E] in
theorem abs_localCoefficient_le (S : SpinSystem n V E) (β : ℝ)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (M : SpinOperator n) (hM : ‖M‖ ≤ 1) (σ : V → Spin n) (e : E) :
    |S.localCoefficient M σ e| ≤ β := by
  have hi : |⟪(σ (S.left e)).val, M (σ (S.right e)).val⟫_ℝ| ≤ 1 := by
    calc _ ≤ ‖(σ (S.left e)).val‖ * ‖M (σ (S.right e)).val‖ := abs_real_inner_le_norm _ _
         _ ≤ ‖(σ (S.left e)).val‖ * (‖M‖ * ‖(σ (S.right e)).val‖) :=
           mul_le_mul_of_nonneg_left (M.le_opNorm _) (norm_nonneg _)
         _ = ‖M‖ := by simp
         _ ≤ 1 := hM
  rw [localCoefficient, abs_mul, abs_of_nonneg (hb e).1]
  exact (mul_le_of_le_one_right (hb e).1 hi).trans (hb e).2

end ClassicalON.SpinSystem

namespace ClassicalON

theorem norm_square_le_one {n : ℕ} (M : SpinOperator n) (hM : ‖M‖ ≤ 1) : ‖M^2‖ ≤ 1 := by
  calc ‖M^2‖ ≤ ‖M‖ * ‖M‖ := by simpa only [pow_two] using norm_mul_le M M
       _ ≤ 1 * 1 := mul_le_mul hM hM (norm_nonneg _) zero_le_one
       _ = 1 := one_mul _

theorem mixedAB_norm_le : ‖mixedAB‖ ≤ 1 := by
  have he : mixedAB = (1/2 : ℝ) • (axisA*axisB+axisB*axisA) := by
    have h := congrArg matrixOperator mixedMatrixAB_sym
    simpa only [map_smul, map_add, map_mul, mixedAB, axisA, axisB] using h
  rw [he, norm_smul]
  have hab := (norm_mul_le axisA axisB).trans
    (mul_le_mul axisA_norm_le axisB_norm_le (norm_nonneg _) zero_le_one)
  have hba := (norm_mul_le axisB axisA).trans
    (mul_le_mul axisB_norm_le axisA_norm_le (norm_nonneg _) zero_le_one)
  have hsum := norm_add_le (axisA*axisB) (axisB*axisA)
  norm_num at hab hba ⊢
  linarith

theorem mixedAAB_norm_le : ‖mixedAAB‖ ≤ 1 := by
  have he : mixedAAB = (-1/3 : ℝ) • axisB := by
    simp only [mixedAAB, mixedMatrixAAB, map_smul, axisB]
  rw [he, norm_smul]
  norm_num
  linarith [axisB_norm_le]

theorem mixedABB_norm_le : ‖mixedABB‖ ≤ 1 := by
  have he : mixedABB = (-1/3 : ℝ) • axisA := by
    simp only [mixedABB, mixedMatrixABB, map_smul, axisA]
  rw [he, norm_smul]
  norm_num
  linarith [axisA_norm_le]

theorem mixedAABB_norm_le : ‖mixedAABB‖ ≤ 1 := by
  have he : mixedAABB = (-1/6 : ℝ) • (axisA^2+axisB^2) := by
    simp only [mixedAABB, mixedMatrixAABB, map_smul, map_add, map_pow, axisA, axisB]
  rw [he, norm_smul]
  have hsum := norm_add_le (axisA^2) (axisB^2)
  have ha := norm_square_le_one axisA axisA_norm_le
  have hb := norm_square_le_one axisB axisB_norm_le
  norm_num
  linarith

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.ObservableBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV uΩ

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON.SpinSystem
variable {n : ℕ} {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [NeZero n]

@[simp] theorem averageLinear_const (S : SpinSystem n V E) (c : ℝ) :
    S.averageLinear (ContinuousMap.const _ c) = c := S.average_const c

@[simp] theorem averageLinear_one (S : SpinSystem n V E) : S.averageLinear 1 = 1 :=
  S.average_const 1

theorem norm_averageComplex_le_const (S : SpinSystem n V E)
    (f : C((V → Spin n), ℂ)) (c : ℝ) (h : ∀ σ, ‖f σ‖ ≤ c) :
    ‖S.averageComplexLinear f‖ ≤ c := by
  calc _ ≤ S.averageLinear (normObservable f) := S.norm_averageComplex_le f
       _ ≤ S.averageLinear (ContinuousMap.const _ c) := S.averageLinear_mono _ _ h
       _ = c := S.averageLinear_const c

theorem averageLinear_norm_le_sqrt (S : SpinSystem n V E)
    (f : C((V → Spin n), ℂ)) :
    S.averageLinear (normObservable f) ≤
      Real.sqrt (S.averageLinear (normObservable f * normObservable f)) := by
  simpa only [mul_one, one_mul, S.averageLinear_one, Real.sqrt_one] using
    S.averageLinear_mul_le_sqrt (normObservable f) 1

theorem norm_averageComplex_mul_mul_le (S : SpinSystem n V E)
    (a f g : C((V → Spin n), ℂ)) (c : ℝ) (hc : 0 ≤ c)
    (ha : ∀ σ, ‖a σ‖ ≤ c) :
    ‖S.averageComplexLinear (a*f*g)‖ ≤ c *
      (Real.sqrt (S.averageLinear (normObservable f * normObservable f)) *
       Real.sqrt (S.averageLinear (normObservable g * normObservable g))) := by
  have hpt : ∀ σ, normObservable (a*f*g) σ ≤
      (c • (normObservable f * normObservable g)) σ := by
    intro σ
    change ‖a σ*f σ*g σ‖ ≤ c * (‖f σ‖*‖g σ‖)
    rw [norm_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_right (ha σ) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  calc _ ≤ S.averageLinear (normObservable (a*f*g)) := S.norm_averageComplex_le _
       _ ≤ S.averageLinear (c • (normObservable f * normObservable g)) :=
          S.averageLinear_mono _ _ hpt
       _ = c * S.averageLinear (normObservable f * normObservable g) := by
          rw [map_smul, smul_eq_mul]
       _ ≤ _ := mul_le_mul_of_nonneg_left (S.averageLinear_mul_le_sqrt _ _) hc

theorem norm_averageComplex_mul_mul_le_of_moments (S : SpinSystem n V E)
    (a f g : C((V → Spin n), ℂ)) (c v : ℝ) (hc : 0 ≤ c)
    (ha : ∀ σ, ‖a σ‖ ≤ c)
    (hf : S.averageLinear (normObservable f * normObservable f) ≤ v)
    (hg : S.averageLinear (normObservable g * normObservable g) ≤ v) :
    ‖S.averageComplexLinear (a*f*g)‖ ≤ c*v := by
  have hv : 0 ≤ v := (S.averageLinear_mul_self_nonneg (normObservable f)).trans hf
  calc _ ≤ c * (Real.sqrt (S.averageLinear (normObservable f * normObservable f)) *
      Real.sqrt (S.averageLinear (normObservable g * normObservable g))) :=
      S.norm_averageComplex_mul_mul_le a f g c hc ha
       _ ≤ c * (Real.sqrt v * Real.sqrt v) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (Real.sqrt_le_sqrt hf) (Real.sqrt_le_sqrt hg)
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hc
       _ = c*v := by rw [Real.mul_self_sqrt hv]

theorem norm_averageComplex_mul_le_of_moment (S : SpinSystem n V E)
    (a f : C((V → Spin n), ℂ)) (c v : ℝ) (hc : 0 ≤ c)
    (ha : ∀ σ, ‖a σ‖ ≤ c)
    (hf : S.averageLinear (normObservable f * normObservable f) ≤ v) :
    ‖S.averageComplexLinear (a*f)‖ ≤ c*Real.sqrt v := by
  have h := S.norm_averageComplex_mul_mul_le a f 1 c hc ha
  simp only [mul_one] at h
  have h1 : normObservable (1 : C((V → Spin n), ℂ)) = 1 := by
    ext σ
    change ‖(1 : ℂ)‖ = (1 : ℝ)
    exact norm_one
  rw [h1, mul_one, S.averageLinear_one, Real.sqrt_one, mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hf) hc)

end ClassicalON.SpinSystem

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.FamilyKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uV uΩ

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON
variable {I : Type uI} {E : Type uE} [Fintype I] [Fintype E]

theorem rowSquare_nonneg (u : I → E → ℂ) (e : E) : 0 ≤ rowSquare u e :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem kernel_diag_sq_le_row (u : I → E → ℂ) (e : E) :
    ‖familyKernel u e e‖^2 ≤ rowSquare u e :=
  Finset.single_le_sum (fun l _ => sq_nonneg ‖familyKernel u e l‖) (Finset.mem_univ e)

theorem kernel_diag_norm_le_sqrt (u : I → E → ℂ) (e : E) :
    ‖familyKernel u e e‖ ≤ Real.sqrt (rowSquare u e) :=
  Real.le_sqrt_of_sq_le (kernel_diag_sq_le_row u e)

namespace SpinSystem
variable {n : ℕ} {V : Type uV} [Fintype V]

omit [Fintype V] [Fintype E] in
theorem familyKernel_differential (S : SpinSystem n V E) (f : I → V → ℂ) (e : E) :
    familyKernel (fun i => S.differential (f i)) e =
      S.differential (fun x => ∑ i, S.differential (f i) e * conj (f i x)) := by
  funext l
  simp only [familyKernel, differential, map_sub, mul_sub, Finset.sum_sub_distrib]

theorem row_current_moment [NeZero n] (S : SpinSystem n V E) (β : ℝ)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (M : SpinOperator n) (hM : M ∈ skewAdjoint (SpinOperator n)) (hMn : ‖M‖ ≤ 1)
    (f : I → V → ℂ) (hP : ∀ i x s, S.pin x = some s → f i x = 0) (e : E) :
    S.averageLinear (normObservable (S.currentObservable M
      (familyKernel (fun i => S.differential (f i)) e)) *
      normObservable (S.currentObservable M
      (familyKernel (fun i => S.differential (f i)) e))) ≤
        β * rowSquare (fun i => S.differential (f i)) e := by
  have hp : ∀ x s, S.pin x = some s →
      (∑ i, S.differential (f i) e * conj (f i x)) = 0 := by
    intro x s hs
    simp [hP _ x s hs]
  have h := S.complex_gradient_current_bound β hb M hM hMn
    (fun x => ∑ i, S.differential (f i) e * conj (f i x)) hp
  rw [← S.familyKernel_differential f e] at h
  change S.average (fun σ =>
    ‖S.complexEnergy M (familyKernel (fun i => S.differential (f i)) e) σ‖ *
    ‖S.complexEnergy M (familyKernel (fun i => S.differential (f i)) e) σ‖) ≤ _
  simpa only [rowSquare, pow_two] using h

end SpinSystem
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.ModeCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace ClassicalON
namespace LatticeGraph
variable {k : ℕ}

theorem mode_gradient_square_sum_le (G : LatticeGraph) (m s : Bool) (a : ℝ)
    (h : SquareBound (fun e (p : DyadicFreq k) => G.scaledModeGradient m s p e) a) (p : DyadicFreq k) :
    (∑ e, ‖G.modeGradient m s p e‖^2) ≤ a^2/(dyadicRadius p:ℝ) := by
  have hr : (0:ℝ)<dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
  have hh := h.column p
  simp only [scaledModeGradient, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hr.le] at hh
  rw [← Finset.mul_sum] at hh
  exact (le_div_iff₀ hr).mpr (by simpa only [mul_comm] using hh)

theorem mode_sup_square_le (G : LatticeGraph) (m s : Bool) (p : DyadicFreq k)
    (C : ℝ) (hC : 0 ≤ C) (hv : ∀ z, |squareProfile m s z| ≤ C) :
    ‖(fun x : G.vertices => latticeMode m s p x.val)‖^2 ≤ C^2*(1/(dyadicRadius p:ℝ))^3 := by
  have hnorm : ‖(fun x : G.vertices => latticeMode m s p x.val)‖ ≤ dyadicWeight p*C := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (dyadicWeight_pos p).le hC)).mpr
    exact fun x => latticeMode_norm_bound m s p x.val C (hv _)
  calc _ ≤ (dyadicWeight p*C)^2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
       _ = _ := by rw [mul_pow, dyadicWeight_sq]; ring

theorem mode_gram_reweight (G : LatticeGraph) (m s : Bool) (e l : G.edges) :
    (∑ p : DyadicFreq k, G.scaledModeGradient m s p e*((1/(dyadicRadius p:ℝ)):ℂ)*
      conj (G.scaledModeGradient m s p l)) = ∑ p : DyadicFreq k,
        G.modeGradient m s p e*conj (G.modeGradient m s p l) := by
  apply Finset.sum_congr rfl
  intro p _
  have hr : (0:ℝ)<dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
  have hs : ((Real.sqrt (dyadicRadius p:ℝ):ℂ)*((1/(dyadicRadius p:ℝ)):ℂ)*
      (Real.sqrt (dyadicRadius p:ℝ):ℂ)) = 1 := by
    have hsreal : Real.sqrt (dyadicRadius p:ℝ)*(1/(dyadicRadius p:ℝ))*Real.sqrt (dyadicRadius p:ℝ) = 1 := by
      rw [show Real.sqrt (dyadicRadius p:ℝ)*(1/(dyadicRadius p:ℝ))*Real.sqrt (dyadicRadius p:ℝ) =
      (Real.sqrt (dyadicRadius p:ℝ))^2/(dyadicRadius p:ℝ) by ring, Real.sq_sqrt hr.le, div_self hr.ne']
    exact_mod_cast hsreal
  simp only [scaledModeGradient, map_mul, Complex.conj_ofReal]
  linear_combination G.modeGradient m s p e*conj (G.modeGradient m s p l)*hs

theorem mode_group_gram_bound (G : LatticeGraph) (m s : Bool) (a : ℝ)
    (h : SquareBound (fun e (p : DyadicFreq k) => G.scaledModeGradient m s p e) a) :
    (∑ e, ∑ l, ‖∑ p : DyadicFreq k, G.modeGradient m s p e*conj (G.modeGradient m s p l)‖^2)
      ≤ 3*a^4*(k:ℝ) := by
  have hh := h.gram_weighted (fun p => ((1/(dyadicRadius p:ℝ)):ℂ))
  simp_rw [G.mode_gram_reweight] at hh
  have he (p : DyadicFreq k) : ‖((1/(dyadicRadius p:ℝ)):ℂ)‖^2 = (1/(dyadicRadius p:ℝ))^2 := by
    have hr : (0:ℝ) ≤ dyadicRadius p := by positivity
    simp only [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  simp_rw [he] at hh
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left (dyadic_inverse_square_sum k) (by positivity : 0≤a^4)])

theorem modes_HS_bound (G : LatticeGraph) (a : ℝ)
    (h : ∀ m s, SquareBound (fun e (p : DyadicFreq k) => G.scaledModeGradient m s p e) a) :
    familyHSSquare (G.modeDifferences (k := k)) ≤ 48*a^4*(k:ℝ) := by
  unfold familyHSSquare rowSquare familyKernel modeDifferences
  simp only [Fintype.sum_prod_type]
  have hh := gram_groups_bound
    (fun (i : Bool × Bool) e l => ∑ p : DyadicFreq k,
      G.modeGradient i.1 i.2 p e*conj (G.modeGradient i.1 i.2 p l))
    (3*a^4*(k:ℝ)) (fun i => G.mode_group_gram_bound i.1 i.2 a (h i.1 i.2))
  simpa only [Fintype.sum_prod_type, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat,
    show ((2:ℝ)*2)^2*(3*a^4*(k:ℝ)) = 48*a^4*(k:ℝ) by ring] using hh

theorem modes_min_bound (G : LatticeGraph) (a C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ m s z, |squareProfile m s z| ≤ C)
    (h : ∀ m s, SquareBound (fun e (p : DyadicFreq k) => G.scaledModeGradient m s p e) a) :
    (∑ i : ModeIndex k, ∑ j : ModeIndex k,
      min (‖G.modes i‖^2*∑ e, ‖G.modeDifferences j e‖^2)
          (‖G.modes j‖^2*∑ e, ‖G.modeDifferences i e‖^2)) ≤ 576*C^2*a^2*(k:ℝ) := by
  have hv' (i : ModeIndex k) : ‖G.modes i‖^2 ≤ C^2*(1/(dyadicRadius i.2:ℝ))^3 :=
    G.mode_sup_square_le i.1.1 i.1.2 i.2 C hC (hv i.1.1 i.1.2)
  have hd' (i : ModeIndex k) : (∑ e, ‖G.modeDifferences i e‖^2) ≤ a^2/(dyadicRadius i.2:ℝ) :=
    G.mode_gradient_square_sum_le i.1.1 i.1.2 a (h i.1.1 i.1.2) i.2
  have hm (i j : ModeIndex k) :
      min (‖G.modes i‖^2*∑ e, ‖G.modeDifferences j e‖^2)
          (‖G.modes j‖^2*∑ e, ‖G.modeDifferences i e‖^2) ≤
      C^2*a^2*min ((1/(dyadicRadius i.2:ℝ))^3*(1/(dyadicRadius j.2:ℝ)))
                 ((1/(dyadicRadius j.2:ℝ))^3*(1/(dyadicRadius i.2:ℝ))) := by
    rw [mul_min_of_nonneg _ _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    apply min_le_min
    · calc _ ≤ (C^2*(1/(dyadicRadius i.2:ℝ))^3)*(a^2/(dyadicRadius j.2:ℝ)) :=
            mul_le_mul (hv' i) (hd' j) (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
           _ = _ := by ring
    · calc _ ≤ (C^2*(1/(dyadicRadius j.2:ℝ))^3)*(a^2/(dyadicRadius i.2:ℝ)) :=
            mul_le_mul (hv' j) (hd' i) (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
           _ = _ := by ring
  calc _ ≤ ∑ i : ModeIndex k, ∑ j : ModeIndex k,
        C^2*a^2*min ((1/(dyadicRadius i.2:ℝ))^3*(1/(dyadicRadius j.2:ℝ)))
                   ((1/(dyadicRadius j.2:ℝ))^3*(1/(dyadicRadius i.2:ℝ))) :=
           Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hm i j
       _ = 16*C^2*a^2*∑ p : DyadicFreq k, ∑ q : DyadicFreq k,
           min ((1/(dyadicRadius p:ℝ))^3*(1/(dyadicRadius q:ℝ)))
               ((1/(dyadicRadius q:ℝ))^3*(1/(dyadicRadius p:ℝ))) := by
          simp only [ModeIndex, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
            Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, nsmul_eq_mul, Nat.cast_ofNat, ← Finset.mul_sum]
          ring
       _ ≤ _ := by
          have hd := mul_le_mul_of_nonneg_left (dyadic_min_cost_sum k)
            (by positivity : 0 ≤ 16*C^2*a^2)
          nlinarith

end LatticeGraph
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.ModeCommutator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace ClassicalON
variable {k : ℕ}

theorem dyadic_sine_main_sum (k : ℕ) :
    (∑ p : DyadicFreq k, (dyadicWeight p)^2*Real.sin (dyadicAngle k (dyadicPoint p).1)) =
      dyadicLambda k/(2:ℝ)^k := by
  simp only [dyadicWeight_sq, dyadicLambda]
  rw [mul_div_cancel_left₀ _ (by positivity : (2:ℝ)^k ≠ 0)]

theorem grouped_sine_sum (m s j : Bool) :
    (∑ p : DyadicFreq k, (dyadicWeight p)^2*
      Real.sin (dyadicAngle k (if j then (groupedPoint m s p).2 else (groupedPoint m s p).1))) =
      if m=j then (if s then -(dyadicLambda k/(2:ℝ)^k) else dyadicLambda k/(2:ℝ)^k) else 0 := by
  have h1 := dyadic_sine_main_sum k
  have h2 := dyadic_sin_cancel k
  cases m <;> cases s <;> cases j <;>
    simp_all [groupedPoint]

namespace LatticeGraph

theorem modeCommutator_formula (G : LatticeGraph) (m s : Bool) (p : DyadicFreq k) (e : G.edges) :
    G.modeCommutator m s p e = -Complex.I *
      ((squareProfile m s (scaledSite k e.val.1.val)*squareProfile m s (scaledSite k e.val.2.val)*
        ((dyadicWeight p)^2*Real.sin (dyadicAngle k
          (if G.edgeDirection e then (groupedPoint m s p).2 else (groupedPoint m s p).1))):ℝ):ℂ) := by
  have hy : latticeMode m s p e.val.2.val =
      (((dyadicWeight p*squareProfile m s (scaledSite k e.val.2.val)):ℝ):ℂ)*
        torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) e.val.1.val)*
        Complex.exp (Complex.I*((dyadicAngle k
          (if G.edgeDirection e then (groupedPoint m s p).2 else (groupedPoint m s p).1):ℝ):ℂ)) := by
    unfold latticeMode
    rw [show latticeTorus (16*2^k) e.val.2.val = latticeTorus (16*2^k) e.val.1.val+
      latticeTorus (16*2^k) (latticeAxis (G.edgeDirection e)) by rw [G.edge_step e,latticeTorus_add],
      torusWave_add, groupedWave_axis_sine]
    push_cast
    ring
  have hh := wave_commutator (dyadicWeight p)
    (squareProfile m s (scaledSite k e.val.1.val)) (squareProfile m s (scaledSite k e.val.2.val))
    (dyadicAngle k (if G.edgeDirection e then (groupedPoint m s p).2 else (groupedPoint m s p).1))
    (torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) e.val.1.val))
    (torusWave_norm _ _)
  unfold modeCommutator
  rw [hy]
  simp only [latticeMode, Complex.ofReal_mul] at hh ⊢
  linear_combination hh

theorem mode_group_commutator (G : LatticeGraph) (m s : Bool) (e : G.edges) :
    (∑ p : DyadicFreq k, G.modeCommutator m s p e) = -Complex.I*
      ((squareProfile m s (scaledSite k e.val.1.val)*squareProfile m s (scaledSite k e.val.2.val)*
        (if m=G.edgeDirection e then (if s then -(dyadicLambda k/(2:ℝ)^k) else dyadicLambda k/(2:ℝ)^k) else 0):ℝ):ℂ) := by
  simp only [G.modeCommutator_formula, ← Finset.mul_sum, ← Complex.ofReal_sum]
  rw [grouped_sine_sum]

theorem modes_commutator (G : LatticeGraph) (e : G.edges) :
    (∑ i : ModeIndex k, G.modeCommutator i.1.1 i.1.2 i.2 e) =
      -Complex.I*((dyadicLambda k*G.profileEdge k e:ℝ):ℂ) := by
  simp only [Fintype.sum_prod_type, G.mode_group_commutator, Fintype.sum_bool]
  cases h : G.edgeDirection e <;>
    simp [profileEdge, h]
  all_goals ring

end LatticeGraph
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.SecondGauge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem secondAxisResponse_integral (S : SpinSystem 3 V E) (u : E → ℝ) :
    S.secondAxisResponse u u =
      (∫ σ, S.secondWeight (fun e => u e • axisC) 0 σ ∂S.reference) / S.Z (fun _ => 1) := by
  unfold secondAxisResponse average
  congr 1
  apply integral_congr_ae (Filter.Eventually.of_forall _)
  intro σ
  have hz (e : E) : (0 : ℝ) • (u e • axisC) = 0 := zero_smul ℝ (u e • axisC)
  simp only [secondWeight, twistEnergy, hz, NormedSpace.exp_zero, one_mul,
    pow_zero, pow_one]
  have hp (e : E) : (u e • axisC)^2 = (u e*u e) • axisC^2 := by
    rw [operator_smul_pow, sq]
  simp only [hp, pow_two]
  ring

theorem Z_axis_add_gradient (S : SpinSystem 3 V E) (u : E → ℝ) (f : V → ℝ)
    (hP : ∀ x s, S.pin x = some s → f x = 0) (t : ℝ) :
    S.Z (fun e => NormedSpace.exp (t • ((u+S.differential f) e • axisC))) =
      S.Z (fun e => NormedSpace.exp (t • (u e • axisC))) := by
  have hp (x) (s) (hs : S.pin x = some s) : t*f x = 0 := by rw [hP x s hs, mul_zero]
  have h := S.W_add_gradient axisC axisC_skew (fun e => t*u e) (fun x => t*f x) hp
  unfold W at h
  have ha : (fun e => (t*u e + t*f (S.right e) - t*f (S.left e)) • axisC) =
      (fun e => t • ((u+S.differential f) e • axisC)) := by
    funext e
    simp only [Pi.add_apply, differential, smul_smul]
    congr 1
    ring
  rw [ha] at h
  simpa only [← smul_smul] using (div_left_inj' (S.Z_pos _).ne').mp h

theorem secondAxisResponse_gradient_diag (S : SpinSystem 3 V E) (u : E → ℝ)
    (f : V → ℝ) (hP : ∀ x s, S.pin x = some s → f x = 0) :
    S.secondAxisResponse (u+S.differential f) (u+S.differential f) =
      S.secondAxisResponse u u := by
  let A : E → SpinOperator 3 := fun e => (u+S.differential f) e • axisC
  let B : E → SpinOperator 3 := fun e => u e • axisC
  have hZ : (fun t => S.Z (fun e => NormedSpace.exp (t • A e))) =
      (fun t => S.Z (fun e => NormedSpace.exp (t • B e))) :=
    funext (S.Z_axis_add_gradient u f hP)
  have hfirst : (fun t => ∫ σ, S.firstWeight A t σ ∂S.reference) =
      (fun t => ∫ σ, S.firstWeight B t σ ∂S.reference) := by
    funext t
    have h := S.hasDerivAt_twistZ A t
    rw [hZ] at h
    exact h.unique (S.hasDerivAt_twistZ B t)
  have hsecond : (∫ σ, S.secondWeight A 0 σ ∂S.reference) =
      (∫ σ, S.secondWeight B 0 σ ∂S.reference) := by
    have h := S.hasDerivAt_firstVariation A 0
    rw [hfirst] at h
    exact h.unique (S.hasDerivAt_firstVariation B 0)
  rw [S.secondAxisResponse_integral, S.secondAxisResponse_integral]
  exact congrArg (fun q => q / S.Z (fun _ => 1)) hsecond

theorem secondAxisResponse_gradient_right (S : SpinSystem 3 V E) (u : E → ℝ)
    (f : V → ℝ) (hP : ∀ x s, S.pin x = some s → f x = 0) :
    S.secondAxisResponse u (S.differential f) = 0 := by
  have h := S.secondAxisResponse_gradient_diag u f hP
  have hz := S.secondAxisResponse_gradient_diag 0 f hP
  have he (v : E → ℝ) : S.secondAxisResponse 0 v = 0 := by
    unfold secondAxisResponse
    have h0 (σ : V → Spin 3) : S.energy (fun _ => (0 : SpinOperator 3)) σ = 0 :=
      S.energy_zero σ
    simp only [Pi.zero_apply, zero_mul, zero_smul ℝ (axisC^2), zero_smul ℝ axisC, h0, zero_add]
    exact S.average_const 0
  simp only [zero_add, he] at hz
  rw [S.secondAxisResponse_add_left, S.secondAxisResponse_add_right,
    S.secondAxisResponse_add_right, S.secondAxisResponse_symm (S.differential f), hz] at h
  linarith

omit [Fintype V] [Fintype E] in
theorem differential_add_complex (S : SpinSystem 3 V E) (f g : V → ℂ) :
    S.differential (f+g) = S.differential f + S.differential g := by
  ext e
  simp only [differential, Pi.add_apply]
  ring

omit [Fintype V] [Fintype E] in
theorem differential_smul_complex (S : SpinSystem 3 V E) (r : ℂ) (f : V → ℂ) :
    S.differential (r • f) = r • S.differential f := by
  ext e
  simp only [differential, Pi.smul_apply, smul_eq_mul, mul_sub]

theorem complexSecondResponse_gradient_right (S : SpinSystem 3 V E) (u : E → ℂ)
    (f : V → ℂ) (hP : ∀ x s, S.pin x = some s → f x = 0) :
    S.complexSecondResponse u (S.differential f) = 0 := by
  apply complex_linear_zero_of_real (fun _ : E => False)
    (fun u => S.complexSecondResponse u (S.differential f))
    (fun u v => S.complexSecondResponse_add_left u v _)
    (fun r u => S.complexSecondResponse_smul_left u _ r) ?_ u (fun _ h => h.elim)
  intro a _
  apply complex_linear_zero_of_real (fun x => ∃ s, S.pin x = some s)
    (fun f => S.complexSecondResponse (fun e => (a e : ℂ)) (S.differential f)) ?_ ?_ ?_ f ?_
  · intro f g
    rw [S.differential_add_complex, S.complexSecondResponse_add_right]
  · intro r f
    rw [S.differential_smul_complex, S.complexSecondResponse_smul_right]
  · intro b hb
    rw [S.differential_ofReal, S.complexSecondResponse_ofReal,
      S.secondAxisResponse_gradient_right a b (fun x s hs => hb x ⟨s,hs⟩),
      Complex.ofReal_zero]
  · intro x hx
    obtain ⟨s, hs⟩ := hx
    exact hP x s hs

theorem complexSecondResponse_add_gradient_right (S : SpinSystem 3 V E) (u v : E → ℂ)
    (f : V → ℂ) (hP : ∀ x s, S.pin x = some s → f x = 0) :
    S.complexSecondResponse u (v+S.differential f) = S.complexSecondResponse u v := by
  rw [S.complexSecondResponse_add_right, S.complexSecondResponse_gradient_right u f hP, add_zero]

theorem complexSecondResponse_add_gradients (S : SpinSystem 3 V E) (u v : E → ℂ)
    (f g : V → ℂ) (hP : ∀ x s, S.pin x = some s → f x = 0)
    (hQ : ∀ x s, S.pin x = some s → g x = 0) :
    S.complexSecondResponse (u+S.differential f) (v+S.differential g) =
      S.complexSecondResponse u v := by
  rw [S.complexSecondResponse_add_gradient_right _ v g hQ,
    S.complexSecondResponse_symm, S.complexSecondResponse_add_gradient_right _ u f hP,
    S.complexSecondResponse_symm]

end ClassicalON.SpinSystem

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.SecondBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] in
theorem complexEnergy_normSq_re (S : SpinSystem 3 V E) (M : SpinOperator 3)
    (u : E → ℂ) (σ : V → Spin 3) :
    (S.complexEnergy M (fun e => u e * conj (u e)) σ).re =
      ∑ e, S.localCoefficient M σ e * ‖u e‖^2 := by
  simp [complexEnergy, MixedAlgebra.weighted, Complex.mul_conj, Complex.normSq_eq_norm_sq, -Complex.ofReal_pow]

theorem complexSecondResponse_upper (S : SpinSystem 3 V E) (β : ℝ)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β) (u : E → ℂ) :
    -(S.complexSecondResponse u (fun e => conj (u e))).re ≤ β*∑ e, ‖u e‖^2 := by
  unfold complexSecondResponse
  rw [S.averageComplex_re]
  have h (σ : V → Spin 3) :
      -(β*∑ e, ‖u e‖^2) ≤
        reObservable (S.complexSecondObservable u (fun e => conj (u e))) σ := by
    change _ ≤ (S.complexEnergy (axisC^2) (u*(fun e => conj (u e))) σ +
      S.complexEnergy axisC u σ * S.complexEnergy axisC (fun e => conj (u e)) σ).re
    rw [complexEnergy_conj, Complex.mul_conj, Complex.add_re, Complex.ofReal_re]
    have hc := S.complexEnergy_normSq_re (axisC^2) u σ
    change (S.complexEnergy (axisC^2) (u*(fun e => conj (u e))) σ).re = _ at hc
    rw [hc]
    have he : -(β*∑ e, ‖u e‖^2) ≤ ∑ e, S.localCoefficient (axisC^2) σ e*‖u e‖^2 := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro e _
      have hb' := (abs_le.mp (S.abs_localCoefficient_le β hb (axisC^2)
        (norm_square_le_one axisC axisC_norm_le) σ e)).1
      nlinarith [sq_nonneg ‖u e‖]
    exact he.trans (le_add_of_nonneg_right (Complex.normSq_nonneg _))
  have hm := S.averageLinear_mono (ContinuousMap.const _ (-(β*∑ e, ‖u e‖^2)))
    (reObservable (S.complexSecondObservable u (fun e => conj (u e)))) h
  rw [S.averageLinear_const] at hm
  linarith

omit [Fintype V] [Fintype E] in
theorem commutatorForm_adjust (S : SpinSystem 3 V E) (f g : V → ℂ) :
    S.commutatorForm f g + S.differential ((1/2 : ℂ) • (f*g)) =
      fun e => ((f (S.left e)+f (S.right e))/2) * S.differential g e := by
  ext e
  simp only [commutatorForm, complexCross, differential, Pi.add_apply, Pi.mul_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype E] in
theorem commutatorForm_adjust_norm (S : SpinSystem 3 V E) (f g : V → ℂ) (e : E) :
    ‖((f (S.left e)+f (S.right e))/2) * S.differential g e‖ ≤
      ‖f‖ * ‖S.differential g e‖ := by
  rw [norm_mul, norm_div]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  norm_num
  have h := norm_add_le (f (S.left e)) (f (S.right e))
  have hx := norm_le_pi_norm f (S.left e)
  have hy := norm_le_pi_norm f (S.right e)
  linarith

theorem commutatorForm_bound_left (S : SpinSystem 3 V E) (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (f g : V → ℂ) (hP : ∀ x s, S.pin x = some s → f x = 0) :
    -(S.complexSecondResponse (S.commutatorForm f g)
      (fun e => conj (S.commutatorForm f g e))).re ≤
        β*(‖f‖^2*∑ e, ‖S.differential g e‖^2) := by
  let F : V → ℂ := (1/2 : ℂ) • (f*g)
  have hp (x) (s) (hs : S.pin x = some s) : F x = 0 := by
    simp only [F, Pi.smul_apply, Pi.mul_apply, hP x s hs, zero_mul, smul_zero]
  have hq (x) (s) (hs : S.pin x = some s) : conj (F x) = 0 := by rw [hp x s hs, map_zero]
  have hd : S.differential (fun x => conj (F x)) = fun e => conj (S.differential F e) := by
    ext e
    simp only [differential, map_sub]
  have hid := S.complexSecondResponse_add_gradients (S.commutatorForm f g)
    (fun e => conj (S.commutatorForm f g e)) F (fun x => conj (F x)) hp hq
  rw [hd] at hid
  have hc : ((fun e => conj (S.commutatorForm f g e)) + (fun e => conj (S.differential F e))) =
      (fun e => conj ((S.commutatorForm f g + S.differential F) e)) := by
    ext e
    simp only [Pi.add_apply, map_add]
  rw [hc] at hid
  rw [← hid]
  apply (S.complexSecondResponse_upper β hb _).trans
  apply mul_le_mul_of_nonneg_left _ hβ
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  change ‖(S.commutatorForm f g + S.differential ((1/2 : ℂ) • (f*g))) e‖^2 ≤ _
  rw [S.commutatorForm_adjust]
  have h := S.commutatorForm_adjust_norm f g e
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq (mul_pow _ _ _)

end ClassicalON.SpinSystem

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.ResponseTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] in
theorem complexEnergy_norm_le (S : SpinSystem 3 V E) (β : ℝ)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (M : SpinOperator 3) (hM : ‖M‖ ≤ 1) (u : E → ℂ) (σ : V → Spin 3) :
    ‖S.complexEnergy M u σ‖ ≤ β*∑ e, ‖u e‖ := by
  unfold complexEnergy MixedAlgebra.weighted
  calc _ ≤ ∑ e, ‖(S.localCoefficient M σ e : ℂ)*u e‖ := norm_sum_le _ _
       _ ≤ ∑ e, β*‖u e‖ := by
         apply Finset.sum_le_sum
         intro e _
         rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
         exact mul_le_mul_of_nonneg_right (S.abs_localCoefficient_le β hb M hM σ e) (norm_nonneg _)
       _ = _ := (Finset.mul_sum _ _ _).symm

omit [Fintype V] in
@[simp] theorem quadraticObservable_apply (S : SpinSystem 3 V E) (u : E → ℂ) (σ) :
    S.quadraticObservable u σ = ∑ e, S.localCoefficient (axisC^2) σ e*‖u e‖^2 :=
  S.complexEnergy_normSq_re (axisC^2) u σ

omit [Fintype V] in
theorem quadraticObservable_lower (S : SpinSystem 3 V E) (β : ℝ)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β) (u : E → ℂ) (σ) :
    -(β*∑ e, ‖u e‖^2) ≤ S.quadraticObservable u σ := by
  rw [quadraticObservable_apply, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro e _
  have h := (abs_le.mp (S.abs_localCoefficient_le β hb (axisC^2)
    (norm_square_le_one axisC axisC_norm_le) σ e)).1
  nlinarith [sq_nonneg ‖u e‖]

theorem complexSecondResponse_re_decomposition (S : SpinSystem 3 V E) (u : E → ℂ) :
    (S.complexSecondResponse u (fun e => conj (u e))).re =
      S.averageLinear (S.quadraticObservable u) +
        S.averageLinear (normObservable (S.currentObservable axisC u) *
          normObservable (S.currentObservable axisC u)) := by
  unfold complexSecondResponse
  rw [S.averageComplex_re, ← map_add]
  congr 1
  ext σ
  change (S.complexEnergy (axisC^2) (u*(fun e => conj (u e))) σ +
    S.complexEnergy axisC u σ*S.complexEnergy axisC (fun e => conj (u e)) σ).re = _
  rw [complexEnergy_conj, Complex.add_re, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]
  change _ + ‖S.complexEnergy axisC u σ‖^2 = _ + ‖S.complexEnergy axisC u σ‖*‖S.complexEnergy axisC u σ‖
  exact congrArg ((S.complexEnergy (axisC^2) (u*(fun e => conj (u e))) σ).re + ·) (pow_two _)

theorem current_moment_of_response_nonpos (S : SpinSystem 3 V E) (β : ℝ)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β) (u : E → ℂ)
    (hR : (S.complexSecondResponse u (fun e => conj (u e))).re ≤ 0) :
    S.averageLinear (normObservable (S.currentObservable axisC u) *
      normObservable (S.currentObservable axisC u)) ≤ β*∑ e, ‖u e‖^2 := by
  rw [S.complexSecondResponse_re_decomposition] at hR
  have h := S.averageLinear_mono (ContinuousMap.const _ (-(β*∑ e, ‖u e‖^2)))
    (S.quadraticObservable u) (S.quadraticObservable_lower β hb u)
  rw [S.averageLinear_const] at h
  linarith

theorem current_moment_difference (S : SpinSystem 3 V E)
    (F G : C((V → Spin 3), ℂ)) (b v : ℝ) (hb : 0 ≤ b)
    (hFG : ∀ σ, ‖F σ-G σ‖ ≤ b)
    (hF : S.averageLinear (normObservable F * normObservable F) ≤ v) :
    S.averageLinear (normObservable G * normObservable G) -
      S.averageLinear (normObservable F * normObservable F) ≤ 2*b*Real.sqrt v+b^2 := by
  have hpt (σ : V → Spin 3) : (normObservable G * normObservable G) σ ≤
      (normObservable F * normObservable F + (2*b) • normObservable F + ContinuousMap.const (V → Spin 3) (b^2)) σ := by
    change ‖G σ‖*‖G σ‖ ≤ ‖F σ‖*‖F σ‖+2*b*‖F σ‖+b^2
    have hn : ‖G σ‖ ≤ ‖F σ‖+b := by
      calc _ ≤ ‖F σ‖+‖G σ-F σ‖ := norm_le_insert' _ _
           _ ≤ _ := by rw [norm_sub_rev]; exact add_le_add le_rfl (hFG σ)
    nlinarith [norm_nonneg (F σ), norm_nonneg (G σ)]
  have hm := S.averageLinear_mono _ _ hpt
  simp only [map_add, map_smul, smul_eq_mul, S.averageLinear_const] at hm
  have hav := (S.averageLinear_norm_le_sqrt F).trans (Real.sqrt_le_sqrt hF)
  have hmul := mul_le_mul_of_nonneg_left hav (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hb)
  linarith

theorem abs_norm_sq_sub_norm_sq (z w : ℂ) :
    |‖z‖^2-‖w‖^2| ≤ ‖z-w‖*(‖z‖+‖w‖) := by
  calc _ = |‖z‖-‖w‖| * (‖z‖+‖w‖) := by
          rw [← abs_of_nonneg (add_nonneg (norm_nonneg z) (norm_nonneg w)), ← abs_mul]
          congr 1
          ring
       _ ≤ _ := mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le z w)
          (add_nonneg (norm_nonneg z) (norm_nonneg w))

omit [Fintype V] in
theorem quadraticObservable_difference (S : SpinSystem 3 V E) (β : ℝ)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β) (u v : E → ℂ) (σ) :
    S.quadraticObservable v σ - S.quadraticObservable u σ ≤
      β*∑ e, ‖u e-v e‖*(‖u e‖+‖v e‖) := by
  simp only [quadraticObservable_apply, ← Finset.sum_sub_distrib, Finset.mul_sum, ← mul_sub]
  apply Finset.sum_le_sum
  intro e _
  calc _ ≤ |S.localCoefficient (axisC^2) σ e*(‖v e‖^2-‖u e‖^2)| := le_abs_self _
       _ = |S.localCoefficient (axisC^2) σ e| * |‖v e‖^2-‖u e‖^2| := abs_mul _ _
       _ ≤ β*(‖u e-v e‖*(‖u e‖+‖v e‖)) := by
         apply mul_le_mul (S.abs_localCoefficient_le β hb (axisC^2)
           (norm_square_le_one axisC axisC_norm_le) σ e) _ (abs_nonneg _)
           (abs_nonneg _ |>.trans (S.abs_localCoefficient_le β hb (axisC^2)
             (norm_square_le_one axisC axisC_norm_le) σ e))
         simpa only [abs_sub_comm] using abs_norm_sq_sub_norm_sq (u e) (v e)

theorem response_transfer (S : SpinSystem 3 V E) (β a : ℝ) (hβ : 0 ≤ β) (ha : 0 ≤ a)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β) (u v : E → ℂ)
    (hr : -(S.complexSecondResponse v (fun e => conj (v e))).re ≤ a) :
    -(S.complexSecondResponse u (fun e => conj (u e))).re ≤ a +
      β*∑ e, ‖u e-v e‖*(‖u e‖+‖v e‖) +
      2*(β*∑ e, ‖u e-v e‖)*Real.sqrt (β*∑ e, ‖u e‖^2) +
      (β*∑ e, ‖u e-v e‖)^2 := by
  have hb' : 0 ≤ β*∑ e, ‖u e-v e‖ := mul_nonneg hβ (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hl : 0 ≤ β*∑ e, ‖u e-v e‖*(‖u e‖+‖v e‖) := mul_nonneg hβ
    (Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _)))
  by_cases hR : (S.complexSecondResponse u (fun e => conj (u e))).re ≤ 0
  · have hm := S.current_moment_difference (S.currentObservable axisC u) (S.currentObservable axisC v)
      (β*∑ e, ‖u e-v e‖) (β*∑ e, ‖u e‖^2) hb'
      (fun σ => by
        change ‖S.complexEnergy axisC u σ-S.complexEnergy axisC v σ‖ ≤ _
        rw [← S.complexEnergy_sub]
        exact S.complexEnergy_norm_le β hb axisC axisC_norm_le (u-v) σ)
      (S.current_moment_of_response_nonpos β hb u hR)
    have hq := S.averageLinear_mono (S.quadraticObservable v-S.quadraticObservable u)
      (ContinuousMap.const _ (β*∑ e, ‖u e-v e‖*(‖u e‖+‖v e‖)))
      (S.quadraticObservable_difference β hb u v)
    rw [map_sub, S.averageLinear_const] at hq
    rw [S.complexSecondResponse_re_decomposition] at hr ⊢
    linarith
  · have he : 0 ≤ 2*(β*∑ e, ‖u e-v e‖)*Real.sqrt (β*∑ e, ‖u e‖^2) :=
      mul_nonneg (mul_nonneg (by norm_num) hb') (Real.sqrt_nonneg _)
    linarith [sq_nonneg (β*∑ e, ‖u e-v e‖)]

end ClassicalON.SpinSystem

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.ThetaEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped BigOperators ComplexConjugate
namespace ClassicalON

theorem squareTheta_compact : HasCompactSupport squareTheta := by
  apply HasCompactSupport.intro (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Icc (-2:ℝ) 2 ×ˢ Icc (-2:ℝ) 2))
  intro z hz
  apply squareTheta_zero
  by_contra h
  push Not at h
  apply hz
  constructor <;> constructor <;> nlinarith [abs_le.mp h.1.le, abs_le.mp h.2.le]

theorem theta_lipschitz_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ z w,
    |squareTheta w-squareTheta z| ≤ C*‖w-z‖ := by
  obtain ⟨C,hC,_,hL⟩ := smooth_compact_lipschitz_bound squareTheta_compact squareTheta_contDiff
  exact ⟨C,hC,by simpa only [Real.norm_eq_abs] using hL⟩

namespace LatticeGraph

theorem theta_edge_bounds : ∃ L D : ℝ, 0 ≤ L ∧ 0 ≤ D ∧
    ∀ (G : LatticeGraph) (k : ℕ), 4 ≤ k → ∀ e : G.edges,
      |G.thetaEdge k e| ≤ L/(2:ℝ)^k ∧
      |G.thetaEdge k e-G.profileEdge k e| ≤ D/((2:ℝ)^k)^3 := by
  obtain ⟨L,hL,hLip⟩ := theta_lipschitz_bound
  obtain ⟨D,hD,hR⟩ := squareTheta_step_error
  refine ⟨L,D,hL,hD,?_⟩
  intro G k hk e
  constructor
  · have h := hLip (scaledSite k e.val.1.val) (scaledSite k e.val.2.val)
    rw [G.scaled_edge_distance] at h
    exact h.trans_eq (by ring)
  · have hN : (16:ℝ) ≤ (2:ℝ)^k := by
      calc (16:ℝ) = (2:ℝ)^4 := by norm_num
           _ ≤ _ := pow_le_pow_right₀ (by norm_num) hk
    have hmesh : |1/(2:ℝ)^k| ≤ 1/16 := by
      rw [abs_of_pos (by positivity)]
      exact one_div_le_one_div_of_le (by norm_num) hN
    have h := hR (G.edgeDirection e) (scaledSite k e.val.1.val) (1/(2:ℝ)^k) hmesh
    rw [← scaledSite_add_axis, ← G.edge_step e,abs_of_pos (by positivity : 0 < 1/(2:ℝ)^k)] at h
    simpa only [thetaEdge,profileEdge,div_pow,one_pow,mul_one_div] using h

theorem theta_sum_bounds (G : LatticeGraph) (k : ℕ) (hG : G.WithinDyadicBox k)
    (L D : ℝ) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (he : ∀ e : G.edges, |G.thetaEdge k e| ≤ L/(2:ℝ)^k ∧
      |G.thetaEdge k e-G.profileEdge k e| ≤ D/((2:ℝ)^k)^3) :
    (∑ e, |G.thetaEdge k e-G.profileEdge k e|) ≤ 512*D/(2:ℝ)^k ∧
    (∑ e, |G.thetaEdge k e|^2) ≤ 512*L^2 ∧
    (∑ e, |G.thetaEdge k e-G.profileEdge k e| *
      (|G.thetaEdge k e| + |G.profileEdge k e|)) ≤ 512*D*(2*L+D)/((2:ℝ)^k)^2 := by
  let N : ℝ := (2:ℝ)^k
  have hN : 0 < N := by dsimp [N]; positivity
  have hN1 : 1 ≤ N := one_le_pow₀ (by norm_num)
  have hcount := G.edge_card_bound k hG
  change (Fintype.card G.edges:ℝ) ≤ 512*N^2 at hcount
  have hv (e : G.edges) : |G.profileEdge k e| ≤ (L+D)/N := by
    have htri : |G.profileEdge k e| ≤ |G.thetaEdge k e| + |G.thetaEdge k e-G.profileEdge k e| := by
      simpa only [add_sub_cancel, abs_sub_comm] using abs_add_le (G.thetaEdge k e) (G.profileEdge k e-G.thetaEdge k e)
    have hpow : N ≤ N^3 := by nlinarith [sq_nonneg (N-1)]
    calc _ ≤ L/N+D/N^3 := htri.trans (add_le_add (he e).1 (he e).2)
         _ ≤ L/N+D/N := add_le_add_right (div_le_div_of_nonneg_left hD hN hpow) _
         _ = _ := by ring
  have hs1 : (∑ e, |G.thetaEdge k e-G.profileEdge k e|) ≤ (Fintype.card G.edges:ℝ)*(D/N^3) := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ) (fun e _ => (he e).2)
  have hs2 : (∑ e, |G.thetaEdge k e|^2) ≤ (Fintype.card G.edges:ℝ)*(L/N)^2 := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ)
      (fun e _ => pow_le_pow_left₀ (abs_nonneg _) (he e).1 2)
  have hs3 : (∑ e, |G.thetaEdge k e-G.profileEdge k e| *(|G.thetaEdge k e| + |G.profileEdge k e|)) ≤
      (Fintype.card G.edges:ℝ)*(D/N^3*((2*L+D)/N)) := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ)
      (fun e _ => mul_le_mul (he e).2 (show |G.thetaEdge k e| + |G.profileEdge k e| ≤ (2*L+D)/N from
        (add_le_add (he e).1 (hv e)).trans_eq (by ring)) (by positivity) (by positivity))
  refine ⟨hs1.trans ?_,hs2.trans ?_,hs3.trans ?_⟩
  all_goals
    calc _ ≤ 512*N^2*_ := mul_le_mul_of_nonneg_right hcount (by positivity)
         _ = _ := by dsimp only [N]; field_simp

end LatticeGraph
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.FamilyBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uJ uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} {I : Type uI} [Fintype V] [Fintype E] [Fintype I]

omit [Fintype V] [Fintype E] [Fintype I] in
theorem coefficientObservable_norm_le (S : SpinSystem 3 V E) (β : ℝ)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (M : SpinOperator 3) (hM : ‖M‖ ≤ 1) (e : E) (σ : V → Spin 3) :
    ‖S.coefficientObservable M e σ‖ ≤ β := by
  change ‖(S.localCoefficient M σ e : ℂ)‖ ≤ β
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact S.abs_localCoefficient_le β hb M hM σ e

omit [Fintype I] in
theorem averageComplex_pos_square (S : SpinSystem 3 V E) (F : C((V → Spin 3), ℂ)) :
    0 ≤ (S.averageComplexLinear (F * conjugateObservable F)).re := by
  rw [S.averageComplex_re]
  apply S.averageLinear_nonneg
  intro σ
  change 0 ≤ (F σ * conj (F σ)).re
  rw [Complex.mul_conj, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

omit [Fintype I] in
theorem norm_averageComplex_sum_le {J : Type uJ} [Fintype J]
    (S : SpinSystem 3 V E) (F : J → C((V → Spin 3), ℂ)) (bound : J → ℝ)
    (hF : ∀ j, ‖S.averageComplexLinear (F j)‖ ≤ bound j) :
    ‖S.averageComplexLinear (∑ j, F j)‖ ≤ ∑ j, bound j := by
  rw [map_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hF j)

omit [Fintype V] in

theorem familyObservable_contraction (S : SpinSystem 3 V E) (u : I → E → ℂ) :
    (∑ i, ∑ j, S.complexMixedObservable (u i) (fun e => conj (u i e))
      (fun e => conj (u j e)) (u j)) =
        S.familyPaired u * conjugateObservable (S.familyPaired u) + S.familyRemainder u := by
  ext σ
  have h := MixedAlgebra.four_family_contraction (S.complexCoefficients σ) u
    (fun i e => conj (u i e)) (fun i e => conj (u i e)) u
  simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply, ContinuousMap.add_apply,
    complexMixedObservable, ContinuousMap.coe_mk]
  rw [h]
  simp only [familyPaired, familyRemainder, ContinuousMap.sum_apply,
    ContinuousMap.add_apply, ContinuousMap.mul_apply, conjugateObservable_apply,
    ContinuousMap.const_apply, currentObservable, coefficientObservable,
    ContinuousMap.coe_mk, MixedAlgebra.paired, MixedAlgebra.kernel,
    familyKernel, complexCoefficients, MixedAlgebra.Coeffs.map,
    mixedCoefficients, Function.comp_def, Complex.ofRealHom_eq_coe,
    complexEnergy, map_sum, map_add, map_mul,
    starRingEnd_self_apply, pow_two]
  congr 1
  all_goals simp only [MixedAlgebra.weighted, MixedAlgebra.kernel, familyKernel,
    map_sum, map_mul, Complex.conj_ofReal, starRingEnd_self_apply, Pi.mul_apply, mul_assoc]

end ClassicalON.SpinSystem

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.FamilyEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} {I : Type uI} [Fintype V] [Fintype E] [Fintype I]

omit [Fintype I] in
theorem norm_avg_coeff_two (S : SpinSystem 3 V E) (β v : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (M : SpinOperator 3) (hM : ‖M‖ ≤ 1) (e : E)
    (F G : C((V → Spin 3), ℂ))
    (hF : S.averageLinear (normObservable F * normObservable F) ≤ v)
    (hG : S.averageLinear (normObservable G * normObservable G) ≤ v) :
    ‖S.averageComplexLinear (S.coefficientObservable M e * F * G)‖ ≤ β*v :=
  S.norm_averageComplex_mul_mul_le_of_moments _ F G β v hβ
    (S.coefficientObservable_norm_le β hb M hM e) hF hG

omit [Fintype I] in
theorem norm_avg_coeff_coeff_const (S : SpinSystem 3 V E) (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (M N : SpinOperator 3) (hM : ‖M‖ ≤ 1) (hN : ‖N‖ ≤ 1) (e l : E) (z : ℂ) :
    ‖S.averageComplexLinear (S.coefficientObservable M e * S.coefficientObservable N l *
      ContinuousMap.const _ z)‖ ≤ β^2*‖z‖ := by
  apply S.norm_averageComplex_le_const
  intro σ
  simp only [ContinuousMap.mul_apply, ContinuousMap.const_apply, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
  rw [pow_two]
  exact mul_le_mul (S.coefficientObservable_norm_le β hb M hM e σ)
    (S.coefficientObservable_norm_le β hb N hN l σ) (norm_nonneg _) hβ

omit [Fintype I] in
theorem norm_avg_coeff_const_current (S : SpinSystem 3 V E) (β q : ℝ)
    (hβ : 0 ≤ β) (hq : 0 ≤ q)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (M : SpinOperator 3) (hM : ‖M‖ ≤ 1) (e : E) (z : ℂ)
    (hz : ‖z‖ ≤ Real.sqrt q) (F : C((V → Spin 3), ℂ))
    (hF : S.averageLinear (normObservable F * normObservable F) ≤ β*q) :
    ‖S.averageComplexLinear (S.coefficientObservable M e * ContinuousMap.const _ z * F)‖ ≤
      β*Real.sqrt β*q := by
  have hcoeff (σ : V → Spin 3) :
      ‖(S.coefficientObservable M e * ContinuousMap.const (V → Spin 3) z) σ‖ ≤ β*‖z‖ := by
    simp only [ContinuousMap.mul_apply, ContinuousMap.const_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right (S.coefficientObservable_norm_le β hb M hM e σ)
      (norm_nonneg z)
  calc _ ≤ (β*‖z‖)*Real.sqrt (β*q) :=
        S.norm_averageComplex_mul_le_of_moment _ F (β*‖z‖) (β*q)
          (mul_nonneg hβ (norm_nonneg z)) hcoeff hF
       _ ≤ (β*Real.sqrt q)*Real.sqrt (β*q) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz hβ) (Real.sqrt_nonneg _)
       _ = β*Real.sqrt β*q := by
          rw [Real.sqrt_mul hβ]
          calc _ = β*Real.sqrt β*(Real.sqrt q*Real.sqrt q) := by ring
               _ = _ := by rw [Real.mul_self_sqrt hq]

omit [Fintype I] in
theorem norm_avg_coeff_const (S : SpinSystem 3 V E) (β : ℝ)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (M : SpinOperator 3) (hM : ‖M‖ ≤ 1) (e : E) (z : ℂ) :
    ‖S.averageComplexLinear (S.coefficientObservable M e * ContinuousMap.const _ z)‖ ≤ β*‖z‖ := by
  apply S.norm_averageComplex_le_const
  intro σ
  simp only [ContinuousMap.mul_apply, ContinuousMap.const_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (S.coefficientObservable_norm_le β hb M hM e σ) (norm_nonneg z)

end ClassicalON.SpinSystem

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.FamilyLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} {I : Type uI} [Fintype V] [Fintype E] [Fintype I]

theorem norm_avg_row_sum (S : SpinSystem 3 V E) (u : I → E → ℂ)
    (F : E → C((V → Spin 3), ℂ)) (c : ℝ)
    (hF : ∀ e, ‖S.averageComplexLinear (F e)‖ ≤ c * rowSquare u e) :
    ‖S.averageComplexLinear (∑ e, F e)‖ ≤ c * familyHSSquare u := by
  simpa only [familyHSSquare, Finset.mul_sum] using
    S.norm_averageComplex_sum_le F (fun e => c * rowSquare u e) hF

omit [Fintype I] in
theorem norm_avg_add_le (S : SpinSystem 3 V E) (F G : C((V → Spin 3), ℂ))
    (a b : ℝ) (hF : ‖S.averageComplexLinear F‖ ≤ a)
    (hG : ‖S.averageComplexLinear G‖ ≤ b) :
    ‖S.averageComplexLinear (F+G)‖ ≤ a+b := by
  rw [map_add]
  exact (norm_add_le _ _).trans (add_le_add hF hG)

theorem norm_familyRemainder_le (S : SpinSystem 3 V E) (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (f : I → V → ℂ) (hP : ∀ i x s, S.pin x = some s → f i x = 0) :
    ‖S.averageComplexLinear (S.familyRemainder (fun i => S.differential (f i)))‖ ≤
      (6*β^2+4*β*Real.sqrt β+β) * familyHSSquare (fun i => S.differential (f i)) := by
  let u := fun i => S.differential (f i)
  let T := familyKernel u
  let X := fun M e => S.currentObservable M (T e)
  let C := S.coefficientObservable
  let bar := conjugateObservable (Ω := V → Spin 3)
  let k : ℂ → C((V → Spin 3), ℂ) := ContinuousMap.const (V → Spin 3)
  let H := familyHSSquare u
  have ha (e : E) : S.averageLinear (normObservable (X axisA e) * normObservable (X axisA e)) ≤
      β * rowSquare u e := S.row_current_moment β hb axisA axisA_skew axisA_norm_le f hP e
  have hb' (e : E) : S.averageLinear (normObservable (X axisB e) * normObservable (X axisB e)) ≤
      β * rowSquare u e := S.row_current_moment β hb axisB axisB_skew axisB_norm_le f hP e
  have hac (e : E) : S.averageLinear (normObservable (bar (X axisA e)) *
      normObservable (bar (X axisA e))) ≤ β * rowSquare u e := by
    simpa only [bar, normObservable_conjugate] using ha e
  have hbc (e : E) : S.averageLinear (normObservable (bar (X axisB e)) *
      normObservable (bar (X axisB e))) ≤ β * rowSquare u e := by
    simpa only [bar, normObservable_conjugate] using hb' e
  have row (M : SpinOperator 3) (hM : ‖M‖ ≤ 1)
      (F G : E → C((V → Spin 3), ℂ))
      (hF : ∀ e, S.averageLinear (normObservable (F e)*normObservable (F e)) ≤ β*rowSquare u e)
      (hG : ∀ e, S.averageLinear (normObservable (G e)*normObservable (G e)) ≤ β*rowSquare u e) :
      ‖S.averageComplexLinear (∑ e, C M e * F e * G e)‖ ≤ β^2*H := by
    apply S.norm_avg_row_sum u _ (β^2)
    intro e
    exact (S.norm_avg_coeff_two β (β*rowSquare u e) hβ hb M hM e (F e) (G e)
      (hF e) (hG e)).trans_eq (by ring)
  have b1 := row (axisA^2) (norm_square_le_one axisA axisA_norm_le)
    (X axisB) (fun e => bar (X axisB e)) hb' hbc
  have b2 := row mixedAB mixedAB_norm_le (X axisB) (X axisA) hb' ha
  have b3 := row mixedAB mixedAB_norm_le (fun e => bar (X axisA e))
    (fun e => bar (X axisB e)) hac hbc
  have b4 := row (axisB^2) (norm_square_le_one axisB axisB_norm_le)
    (fun e => bar (X axisA e)) (X axisA) hac ha
  have pair (M N : SpinOperator 3) (hM : ‖M‖ ≤ 1) (hN : ‖N‖ ≤ 1)
      (z : E → E → ℂ) (hz : ∀ e l, ‖z e l‖ = ‖T e l‖^2) :
      ‖S.averageComplexLinear (∑ e, ∑ l, C M e * C N l * k (z e l))‖ ≤ β^2*H := by
    apply S.norm_avg_row_sum u _ (β^2)
    intro e
    calc _ ≤ ∑ l, β^2*‖T e l‖^2 := by
          apply S.norm_averageComplex_sum_le
          intro l
          exact (S.norm_avg_coeff_coeff_const β hβ hb M N hM hN e l (z e l)).trans_eq
            (by rw [hz e l])
         _ = _ := by rw [← Finset.mul_sum]; rfl
  have b5 := pair (axisA^2) (axisB^2) (norm_square_le_one axisA axisA_norm_le)
    (norm_square_le_one axisB axisB_norm_le) (fun e l => T e l*conj (T e l))
    (by intro e l; simp only [norm_mul, Complex.norm_conj, pow_two])
  have b6 := pair mixedAB mixedAB mixedAB_norm_le mixedAB_norm_le (fun e l => T e l^2)
    (by intro e l; exact norm_pow _ _)
  have triple (M : SpinOperator 3) (hM : ‖M‖ ≤ 1)
      (z : E → ℂ) (hz : ∀ e, ‖z e‖ ≤ Real.sqrt (rowSquare u e))
      (F : E → C((V → Spin 3), ℂ))
      (hF : ∀ e, S.averageLinear (normObservable (F e)*normObservable (F e)) ≤ β*rowSquare u e) :
      ‖S.averageComplexLinear (∑ e, C M e * k (z e) * F e)‖ ≤ β*Real.sqrt β*H := by
    apply S.norm_avg_row_sum u _ (β*Real.sqrt β)
    intro e
    exact S.norm_avg_coeff_const_current β (rowSquare u e) hβ (rowSquare_nonneg u e)
      hb M hM e (z e) (hz e) (F e) (hF e)
  have hz (e : E) : ‖T e e‖ ≤ Real.sqrt (rowSquare u e) := kernel_diag_norm_le_sqrt u e
  have hzc (e : E) : ‖conj (T e e)‖ ≤ Real.sqrt (rowSquare u e) := by
    rw [Complex.norm_conj]; exact hz e
  have b7 := triple mixedAAB mixedAAB_norm_le (fun e => T e e) hz
    (fun e => bar (X axisB e)) hbc
  have b8 := triple mixedABB mixedABB_norm_le (fun e => T e e) hz (X axisA) ha
  have b9 := triple mixedAAB mixedAAB_norm_le (fun e => conj (T e e)) hzc (X axisB) hb'
  have b10 := triple mixedABB mixedABB_norm_le (fun e => conj (T e e)) hzc
    (fun e => bar (X axisA e)) hac
  have b11 : ‖S.averageComplexLinear (∑ e, C mixedAABB e * k (T e e*conj (T e e)))‖ ≤ β*H := by
    apply S.norm_avg_row_sum u _ β
    intro e
    calc _ ≤ β*‖T e e*conj (T e e)‖ := S.norm_avg_coeff_const β hb mixedAABB mixedAABB_norm_le e _
         _ = β*‖T e e‖^2 := by rw [norm_mul, Complex.norm_conj, pow_two]
         _ ≤ β*rowSquare u e := mul_le_mul_of_nonneg_left (kernel_diag_sq_le_row u e) hβ
  have hadd := S.norm_avg_add_le
  have h := hadd _ _ _ _ (hadd _ _ _ _ (hadd _ _ _ _ (hadd _ _ _ _ (hadd _ _ _ _
    (hadd _ _ _ _ (hadd _ _ _ _ (hadd _ _ _ _ (hadd _ _ _ _ (hadd _ _ _ _ b1 b2)
      b3) b4) b5) b6) b7) b8) b9) b10) b11
  change ‖S.averageComplexLinear (S.familyRemainder u)‖ ≤ _ at h ⊢
  exact h.trans_eq (by dsimp only [H]; ring)

theorem fourth_family_lower (S : SpinSystem 3 V E) (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (f : I → V → ℂ) (hP : ∀ i x s, S.pin x = some s → f i x = 0) :
    -((6*β^2+4*β*Real.sqrt β+β)*familyHSSquare (fun i => S.differential (f i))) ≤
      (S.averageComplexLinear (∑ i, ∑ j,
        S.complexMixedObservable (S.differential (f i)) (fun e => conj (S.differential (f i) e))
          (fun e => conj (S.differential (f j) e)) (S.differential (f j)))).re := by
  rw [S.familyObservable_contraction, map_add, Complex.add_re]
  have hp := S.averageComplex_pos_square (S.familyPaired (fun i => S.differential (f i)))
  have hr := S.norm_familyRemainder_le β hβ hb f hP
  have hre := (abs_le.mp (Complex.abs_re_le_norm (S.averageComplexLinear
    (S.familyRemainder (fun i => S.differential (f i)))))).1
  linarith

end ClassicalON.SpinSystem

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.RotationInequality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} {I : Type uI} [Fintype V] [Fintype E] [Fintype I]

omit [Fintype V] [Fintype E] [Fintype I] in
theorem commutatorForm_antisymm (S : SpinSystem 3 V E) (f g : V → ℂ) :
    S.commutatorForm g f = -S.commutatorForm f g := by
  ext e
  simp only [commutatorForm, complexCross, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype I] in
theorem commutatorForm_bound_right (S : SpinSystem 3 V E) (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (f g : V → ℂ) (hP : ∀ x s, S.pin x = some s → g x = 0) :
    -(S.complexSecondResponse (S.commutatorForm f g)
      (fun e => conj (S.commutatorForm f g e))).re ≤
        β*(‖g‖^2*∑ e, ‖S.differential f e‖^2) := by
  have h := S.commutatorForm_bound_left β hβ hb g f hP
  rw [S.commutatorForm_antisymm] at h
  have hc : (fun e => conj ((-S.commutatorForm f g) e)) =
      -(fun e => conj (S.commutatorForm f g e)) := by
    ext e; simp only [Pi.neg_apply, map_neg]
  rw [hc, S.complexSecondResponse_neg_neg] at h
  exact h

omit [Fintype I] in
theorem commutatorForm_bound (S : SpinSystem 3 V E) (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (f g : V → ℂ) (hP : ∀ x s, S.pin x = some s → f x = 0)
    (hQ : ∀ x s, S.pin x = some s → g x = 0) :
    -(S.complexSecondResponse (S.commutatorForm f g)
      (fun e => conj (S.commutatorForm f g e))).re ≤
        β*min (‖f‖^2*∑ e, ‖S.differential g e‖^2) (‖g‖^2*∑ e, ‖S.differential f e‖^2) := by
  rw [mul_min_of_nonneg _ _ hβ]
  exact le_min (S.commutatorForm_bound_left β hβ hb f g hP)
    (S.commutatorForm_bound_right β hβ hb f g hQ)

theorem rotation_family_bound (S : SpinSystem 3 V E) (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (f : I → V → ℂ) (hP : ∀ i x s, S.pin x = some s → f i x = 0) :
    -(S.complexSecondResponse (∑ i, S.commutatorForm (f i) (fun x => conj (f i x)))
      (fun e => conj ((∑ i, S.commutatorForm (f i) (fun x => conj (f i x))) e))).re ≤
      (6*β^2+4*β*Real.sqrt β+β) * familyHSSquare (fun i => S.differential (f i)) +
        β*∑ i, ∑ j, min (‖f i‖^2*∑ e, ‖S.differential (f j) e‖^2)
          (‖f j‖^2*∑ e, ‖S.differential (f i) e‖^2) := by
  let Q := ∑ i, S.commutatorForm (f i) (fun x => conj (f i x))
  have hsum : S.complexSecondResponse Q (fun e => conj (Q e)) =
      ∑ i, ∑ j, S.complexSecondResponse (S.commutatorForm (f i) (fun x => conj (f i x)))
        (fun e => conj (S.commutatorForm (f j) (fun x => conj (f j x)) e)) := by
    have hq : (fun e => conj (Q e)) = ∑ i, (fun e => conj (S.commutatorForm (f i) (fun x => conj (f i x)) e)) := by
      ext e; simp only [Q, Finset.sum_apply, map_sum]
    rw [hq]
    change S.complexSecondBilin (∑ i, _) (∑ j, _) = _
    simp only [map_sum, LinearMap.sum_apply]
    rw [Finset.sum_comm]
    rfl
  have hid : (∑ i, ∑ j, S.complexMixedResponse (S.differential (f i))
      (fun e => conj (S.differential (f i) e)) (fun e => conj (S.differential (f j) e))
        (S.differential (f j))) = S.complexSecondResponse Q (fun e => conj (Q e)) -
      ∑ i, ∑ j, S.complexSecondResponse (S.commutatorForm (f i) (f j))
        (fun e => conj (S.commutatorForm (f i) (f j) e)) := by
    simp only [S.complexMixedResponse_paired _ _ (hP _) (hP _),
      Finset.sum_sub_distrib, hsum]
  have hl := S.fourth_family_lower β hβ hb f hP
  simp only [map_sum] at hl
  have hu : ∑ i, ∑ j, -(S.complexSecondResponse (S.commutatorForm (f i) (f j))
        (fun e => conj (S.commutatorForm (f i) (f j) e))).re ≤
      β*∑ i, ∑ j, min (‖f i‖^2*∑ e, ‖S.differential (f j) e‖^2)
        (‖f j‖^2*∑ e, ‖S.differential (f i) e‖^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ =>
      S.commutatorForm_bound β hβ hb (f i) (f j) (hP i) (hP j)
  have hir := congrArg Complex.re hid
  simp only [Complex.sub_re, complexMixedResponse] at hir
  simp only [Complex.re_sum, Finset.sum_neg_distrib] at hir hl hu
  change -(S.complexSecondResponse Q (fun e => conj (Q e))).re ≤ _
  linarith

end ClassicalON.SpinSystem

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AnnulusResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open scoped BigOperators ComplexConjugate
namespace ClassicalON

namespace SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem response_imaginary_multiple (S : SpinSystem 3 V E) (u : E → ℝ) (r : ℝ) :
    (S.complexSecondResponse (fun e => -Complex.I*((r*u e:ℝ):ℂ))
      (fun e => conj (-Complex.I*((r*u e:ℝ):ℂ)))).re = r^2*S.secondAxisResponse u u := by
  have hf : (fun e => -Complex.I*((r*u e:ℝ):ℂ)) = (-Complex.I*(r:ℂ)) • (fun e => (u e:ℂ)) := by
    ext e; simp only [Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul]; ring
  have hg : (fun e => conj (-Complex.I*((r*u e:ℝ):ℂ))) = (Complex.I*(r:ℂ)) • (fun e => (u e:ℂ)) := by
    ext e; simp only [map_mul,map_neg,Complex.conj_I,neg_neg,Complex.conj_ofReal,Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul]; ring
  rw [hf,hg,S.complexSecondResponse_smul_left,S.complexSecondResponse_smul_right,S.complexSecondResponse_ofReal]
  simp only [Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

end SpinSystem

namespace LatticeGraph

theorem modes_zero_pins (G : LatticeGraph) (k n : ℕ) (P : G.vertices → Option (Spin n))
    (hP : G.BoundaryPins k n P) (i : ModeIndex k) (x : G.vertices) (s : Spin n) (hs : P x=some s) :
    G.modes i x=0 := by
  have hp : squareProfile i.1.1 i.1.2 (scaledSite k x.val)=0 := by
    rcases hP x s hs with h | h
    · exact squareProfile_zero_inner _ _ _ h.1 h.2
    · exact squareProfile_zero_outer _ _ _ h
  simp [modes,latticeMode,hp]

theorem system_modes_commutator (G : LatticeGraph) (k : ℕ) (b : G.edges → ℝ) (P : G.vertices → Option (Spin 3)) :
    (∑ i : ModeIndex k, (G.spinSystem 3 b P).commutatorForm (G.modes i) (fun x => conj (G.modes i x))) =
      (fun e => -Complex.I*((dyadicLambda k*G.profileEdge k e:ℝ):ℂ)) := by
  ext e
  rw [Finset.sum_apply]
  convert G.modes_commutator e using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [SpinSystem.commutatorForm,SpinSystem.complexCross,Pi.smul_apply,smul_eq_mul,
    spinSystem,modes,modeCommutator]
  ring

theorem profile_response_bound (G : LatticeGraph) (k : ℕ) (hk : 0 < k) (hG : G.WithinDyadicBox k)
    (β : ℝ) (hβ : 0 ≤ β) (b : G.edges → ℝ) (hb : ∀ e, 0 ≤ b e ∧ b e ≤ β)
    (P : G.vertices → Option (Spin 3)) (hP : G.BoundaryPins k 3 P)
    (C : ℝ) (hC : 0 ≤ C) (hv : ∀ m s z, |squareProfile m s z| ≤ C)
    (hLip : ∀ m s z w, |squareProfile m s w-squareProfile m s z| ≤ C*‖w-z‖) :
    -(G.spinSystem 3 b P).secondAxisResponse (G.profileEdge k) (G.profileEdge k) ≤
      4*((6*β^2+4*β*Real.sqrt β+β)*(48*(2*modeBlockConstant C)^4)+
        β*(576*C^2*(2*modeBlockConstant C)^2))/(k:ℝ) := by
  let a := 2*modeBlockConstant C
  let M := (6*β^2+4*β*Real.sqrt β+β)*(48*a^4)+β*(576*C^2*a^2)
  have ha (m s : Bool) := G.scaledModes_squareBound hG C hv hLip m s
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hLam : (k:ℝ)/2 ≤ dyadicLambda k := dyadicLambda_lower k
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  have hLp : 0 < dyadicLambda k := by linarith
  have h := (G.spinSystem 3 b P).rotation_family_bound β hβ hb (G.modes (k := k))
    (fun i x s hs => G.modes_zero_pins k 3 P hP i x s hs)
  have hd : (fun i : ModeIndex k => (G.spinSystem 3 b P).differential (G.modes i)) = G.modeDifferences := rfl
  rw [G.system_modes_commutator k b P, (G.spinSystem 3 b P).response_imaginary_multiple,hd] at h
  have hHS := G.modes_HS_bound a ha
  have hmin := G.modes_min_bound a C hC hv ha
  have hK : 0 ≤ 6*β^2+4*β*Real.sqrt β+β := by positivity
  have hcost : (6*β^2+4*β*Real.sqrt β+β)*familyHSSquare (G.modeDifferences (k := k))+
      β*(∑ i : ModeIndex k, ∑ j : ModeIndex k,
      min (‖G.modes i‖^2*∑ e, ‖G.modeDifferences j e‖^2)
          (‖G.modes j‖^2*∑ e, ‖G.modeDifferences i e‖^2)) ≤ M*(k:ℝ) := by
    calc _ ≤ (6*β^2+4*β*Real.sqrt β+β)*(48*a^4*(k:ℝ))+β*(576*C^2*a^2*(k:ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left hHS hK) (mul_le_mul_of_nonneg_left hmin hβ)
         _ = _ := by dsimp only [M]; ring
  have hfinal : -(G.spinSystem 3 b P).secondAxisResponse (G.profileEdge k) (G.profileEdge k) ≤ 4*M/(k:ℝ) := by
    by_cases hr : (G.spinSystem 3 b P).secondAxisResponse (G.profileEdge k) (G.profileEdge k) ≤ 0
    · apply (le_div_iff₀ hkR).mpr
      have hsq : (k:ℝ)^2/4 ≤ (dyadicLambda k)^2 := by nlinarith
      have hh := mul_le_mul_of_nonneg_right hsq (neg_nonneg.mpr hr)
      have ht := h.trans hcost
      nlinarith
    · have hh : 0 ≤ 4*M/(k:ℝ) := by positivity
      linarith
  exact hfinal

end LatticeGraph
end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.AnnulusSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter
namespace ClassicalON
namespace LatticeGraph

theorem theta_response_bound (G : LatticeGraph) (k : ℕ) (hk : 0<k) (hG : G.WithinDyadicBox k)
    (β : ℝ) (hβ : 0 ≤ β) (b : G.edges → ℝ) (hb : ∀ e,0 ≤ b e ∧ b e ≤ β)
    (P : G.vertices → Option (Spin 3)) (hP : G.BoundaryPins k 3 P)
    (C L D : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hv : ∀ m s z, |squareProfile m s z| ≤ C)
    (hLip : ∀ m s z w, |squareProfile m s w-squareProfile m s z| ≤ C*‖w-z‖)
    (he : ∀ e : G.edges, |G.thetaEdge k e| ≤ L/(2:ℝ)^k ∧
      |G.thetaEdge k e-G.profileEdge k e| ≤ D/((2:ℝ)^k)^3) :
    -(G.spinSystem 3 b P).secondAxisResponse (G.thetaEdge k) (G.thetaEdge k) ≤
      rotationCostConstant β C/(k:ℝ)+transferCostConstant β L D/(2:ℝ)^k := by
  let S := G.spinSystem 3 b P
  let a := rotationCostConstant β C/(k:ℝ)
  let N : ℝ := (2:ℝ)^k
  have hN : 0<N := by dsimp [N]; positivity
  have hN1 : 1≤N := one_le_pow₀ (by norm_num)
  have ha : 0≤a := by dsimp [a,rotationCostConstant]; positivity
  have hr : -(S.complexSecondResponse (fun e => (G.profileEdge k e:ℂ))
      (fun e => conj (G.profileEdge k e:ℂ))).re ≤ a := by
    simp only [Complex.conj_ofReal,S.complexSecondResponse_ofReal,Complex.ofReal_re]
    exact G.profile_response_bound k hk hG β hβ b hb P hP C hC hv hLip
  have ht := S.response_transfer β a hβ ha hb
    (fun e => (G.thetaEdge k e:ℂ)) (fun e => (G.profileEdge k e:ℂ)) hr
  simp only [Complex.conj_ofReal,S.complexSecondResponse_ofReal,Complex.ofReal_re,
    ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at ht
  obtain ⟨hs1,hs2,hs3⟩ := G.theta_sum_bounds k hG L D hL hD he
  have hsq : Real.sqrt (β*∑ e, |G.thetaEdge k e|^2) ≤ Real.sqrt (β*(512*L^2)) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hs2 hβ)
  have h1n : 0 ≤ β*∑ e, |G.thetaEdge k e-G.profileEdge k e| := by positivity
  have hh : -(S.secondAxisResponse (G.thetaEdge k) (G.thetaEdge k)) ≤ a+
      β*(512*D*(2*L+D)/N^2)+2*(β*(512*D/N))*Real.sqrt (β*(512*L^2))+(β*(512*D/N))^2 := by
    exact ht.trans (add_le_add (add_le_add (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hs3 hβ))
      (mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs1 hβ) (by norm_num))
        hsq (Real.sqrt_nonneg _) (by positivity)))
      (pow_le_pow_left₀ h1n (mul_le_mul_of_nonneg_left hs1 hβ) 2))
  apply hh.trans
  change a+β*(512*D*(2*L+D)/N^2)+2*(β*(512*D/N))*Real.sqrt (β*(512*L^2))+(β*(512*D/N))^2 ≤ a+transferCostConstant β L D/N
  rw [add_assoc a,add_assoc a]
  apply add_le_add le_rfl
  have hN2 : N ≤ N^2 := by nlinarith
  have hQ : 0 ≤ β*(512*D*(2*L+D))+(β*512*D)^2 := by positivity
  calc _ = (β*(512*D*(2*L+D))+(β*512*D)^2)/N^2+
        (2*(β*512*D)*Real.sqrt (β*(512*L^2)))/N := by ring
       _ ≤ (β*(512*D*(2*L+D))+(β*512*D)^2)/N+
        (2*(β*512*D)*Real.sqrt (β*(512*L^2)))/N :=
        add_le_add (div_le_div_of_nonneg_left hQ hN hN2) le_rfl
       _ = _ := by unfold transferCostConstant; ring

theorem annulus_response_small_oai (β : ℝ) (hβ : 0 ≤ β) (ε : ℝ) (hε : 0<ε) :
    ∃ k : ℕ, 4 ≤ k ∧ ∀ (G : LatticeGraph), G.WithinDyadicBox k →
      ∀ (b : G.edges → ℝ), (∀ e,0 ≤ b e ∧ b e ≤ β) →
      ∀ (P : G.vertices → Option (Spin 3)), G.BoundaryPins k 3 P →
      -(G.spinSystem 3 b P).secondAxisResponse (G.thetaEdge k) (G.thetaEdge k) ≤ ε := by
  obtain ⟨C,hC,hv,hLip⟩ := profiles_uniform_bound
  obtain ⟨L,D,hL,hD,he⟩ := theta_edge_bounds
  have ht1 : Tendsto (fun k : ℕ => rotationCostConstant β C/(k:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have ht2 : Tendsto (fun k : ℕ => transferCostConstant β L D/(2:ℝ)^k) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have ht : Tendsto (fun k : ℕ => rotationCostConstant β C/(k:ℝ)+transferCostConstant β L D/(2:ℝ)^k) atTop (𝓝 0) := by
    simpa only [add_zero] using ht1.add ht2
  obtain ⟨k,hk,hkε⟩ := ((eventually_ge_atTop 4).and (ht.eventually_lt_const hε)).exists
  refine ⟨k,hk,?_⟩
  intro G hG b hb P hP
  exact (G.theta_response_bound k (by omega) hG β hβ b hb P hP C L D (by linarith) hL hD hv hLip
    (he G k hk)).trans hkε.le

end LatticeGraph
end ClassicalON

end

end OAI
end

theorem solution : type_of% @OAI.ClassicalON.LatticeGraph.annulus_response_small_oai := @OAI.ClassicalON.LatticeGraph.annulus_response_small_oai
