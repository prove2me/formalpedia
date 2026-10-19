-- Prove2me | solution 1 for OAI.ClassicalON.SpinSystem.complexMixedResponse_paired
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T02:58:05.486487+00:00
-- url     : https://prove2.me/submissions/8a16bdc0-fe9d-42a4-8550-9908709db148

import Mathlib
import Definitions.Def_ClassicalON
import Definitions.Def_OAIQWCO002

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

theorem noncommuting_gauge [NeZero n] (S : SpinSystem n V E)
    (F : V → SpinOperator n) (hF : ∀ x, F x ∈ skewAdjoint (SpinOperator n))
    (hP : ∀ x s, S.pin x = some s → F x = 0) :
    S.Z (fun e => NormedSpace.exp (F (S.right e) - F (S.left e))) =
      S.Z (S.gaugeProduct F) := by
  let U := fun x => rotationExp (-F x) ((skewAdjoint _).neg_mem (hF x))
  have hfix : ∀ x s, S.pin x = some s → spinRotation (U x) s = s := by
    intro x s hs
    apply Subtype.ext
    change NormedSpace.exp (-F x) s.val = s.val
    rw [hP x s hs, neg_zero, NormedSpace.exp_zero]
    rfl
  have hg : S.gauge (fun e => NormedSpace.exp (F (S.right e) - F (S.left e))) U =
      S.gaugeProduct F := by
    funext e
    apply ContinuousLinearMap.ext
    intro v
    change (U (S.left e)).symm
      (NormedSpace.exp (F (S.right e) - F (S.left e)) (U (S.right e) v)) = _
    simp only [U, rotationExp_symm_apply, rotationExp_apply, neg_neg,
      gaugeProduct, mul_apply_eq_comp]
  rw [← hg]
  exact (S.Z_gauge_of_fixes_pins _ U hfix).symm

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

omit [Fintype V] in
theorem continuous_thirdWeight (S : SpinSystem n V E) (A : E → SpinOperator n) :
    Continuous (Function.uncurry (S.thirdWeight A)) := by
  exact (S.continuous_twistEnergy A 0).rexp.mul
    (((S.continuous_twistEnergy A 3).add
      (((S.continuous_twistEnergy A 1).const_mul 3).mul
        (S.continuous_twistEnergy A 2))).add ((S.continuous_twistEnergy A 1).pow 3))

omit [Fintype V] in
theorem continuous_fourthWeight (S : SpinSystem n V E) (A : E → SpinOperator n) :
    Continuous (Function.uncurry (S.fourthWeight A)) := by
  exact (S.continuous_twistEnergy A 0).rexp.mul
    (((((S.continuous_twistEnergy A 4).add
      (((S.continuous_twistEnergy A 1).const_mul 4).mul
        (S.continuous_twistEnergy A 3))).add
      (((S.continuous_twistEnergy A 2).pow 2).const_mul 3)).add
      ((((S.continuous_twistEnergy A 1).pow 2).const_mul 6).mul
        (S.continuous_twistEnergy A 2))).add ((S.continuous_twistEnergy A 1).pow 4))

omit [Fintype V] in
theorem hasDerivAt_secondWeight (S : SpinSystem n V E) (A : E → SpinOperator n)
    (t : ℝ) (σ : V → Spin n) :
    HasDerivAt (fun u => S.secondWeight A u σ) (S.thirdWeight A t σ) t := by
  exact ((S.hasDerivAt_weight A t σ).mul
    ((S.hasDerivAt_twistEnergy A 2 t σ).add
      ((S.hasDerivAt_twistEnergy A 1 t σ).pow 2))).congr_deriv
    (by dsimp [firstWeight, thirdWeight]; ring)

omit [Fintype V] in
theorem hasDerivAt_thirdWeight (S : SpinSystem n V E) (A : E → SpinOperator n)
    (t : ℝ) (σ : V → Spin n) :
    HasDerivAt (fun u => S.thirdWeight A u σ) (S.fourthWeight A t σ) t := by
  exact ((S.hasDerivAt_weight A t σ).mul
    (((S.hasDerivAt_twistEnergy A 3 t σ).add
      (((S.hasDerivAt_twistEnergy A 1 t σ).const_mul 3).mul
        (S.hasDerivAt_twistEnergy A 2 t σ))).add
      ((S.hasDerivAt_twistEnergy A 1 t σ).pow 3))).congr_deriv
    (by dsimp [firstWeight, fourthWeight]; ring)

theorem hasDerivAt_secondVariation [NeZero n] (S : SpinSystem n V E)
    (A : E → SpinOperator n) (t : ℝ) :
    HasDerivAt (fun u => ∫ σ, S.secondWeight A u σ ∂S.reference)
      (∫ σ, S.thirdWeight A t σ ∂S.reference) t :=
  hasDerivAt_integral_compact S.reference (S.secondWeight A) (S.thirdWeight A)
    (S.continuous_secondWeight A) (S.continuous_thirdWeight A)
    (S.hasDerivAt_secondWeight A) t

theorem hasDerivAt_thirdVariation [NeZero n] (S : SpinSystem n V E)
    (A : E → SpinOperator n) (t : ℝ) :
    HasDerivAt (fun u => ∫ σ, S.thirdWeight A u σ ∂S.reference)
      (∫ σ, S.fourthWeight A t σ ∂S.reference) t :=
  hasDerivAt_integral_compact S.reference (S.thirdWeight A) (S.fourthWeight A)
    (S.continuous_thirdWeight A) (S.continuous_fourthWeight A)
    (S.hasDerivAt_thirdWeight A) t

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

end SpinSystem

theorem iteratedDeriv_four_integral_exp
    {Ω : Type uΩ} [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : ℕ → ℝ → Ω → ℝ)
    (hC : ∀ k, Continuous (Function.uncurry (F k)))
    (hD : ∀ k t ω, HasDerivAt (fun u => F k u ω) (F (k+1) t ω) t) (t : ℝ) :
    iteratedDeriv 4 (fun u => ∫ ω, Real.exp (F 0 u ω) ∂μ) t =
      ∫ ω, fourthBell F t ω ∂μ := by
  let w0 := fun u ω => Real.exp (F 0 u ω)
  let w1 := fun u ω => Real.exp (F 0 u ω) * F 1 u ω
  let w2 := fun u ω => Real.exp (F 0 u ω) * (F 2 u ω + (F 1 u ω)^2)
  let w3 := fun u ω => Real.exp (F 0 u ω) *
    (F 3 u ω + 3 * F 1 u ω * F 2 u ω + (F 1 u ω)^3)
  let w4 := fourthBell F
  have c0 : Continuous (Function.uncurry w0) := (hC 0).rexp
  have c1 : Continuous (Function.uncurry w1) := (hC 0).rexp.mul (hC 1)
  have c2 : Continuous (Function.uncurry w2) :=
    (hC 0).rexp.mul ((hC 2).add ((hC 1).pow 2))
  have c3 : Continuous (Function.uncurry w3) := (hC 0).rexp.mul
    (((hC 3).add (((hC 1).const_mul 3).mul (hC 2))).add ((hC 1).pow 3))
  have c4 : Continuous (Function.uncurry w4) := (hC 0).rexp.mul
    (((((hC 4).add (((hC 1).const_mul 4).mul (hC 3))).add
      (((hC 2).pow 2).const_mul 3)).add ((((hC 1).pow 2).const_mul 6).mul
        (hC 2))).add ((hC 1).pow 4))
  have d0 (u : ℝ) (ω : Ω) : HasDerivAt (fun v => w0 v ω) (w1 u ω) u := (hD 0 u ω).exp
  have d1 (u : ℝ) (ω : Ω) : HasDerivAt (fun v => w1 v ω) (w2 u ω) u :=
    ((d0 u ω).mul (hD 1 u ω)).congr_deriv (by dsimp [w0, w1, w2]; ring)
  have d2 (u : ℝ) (ω : Ω) : HasDerivAt (fun v => w2 v ω) (w3 u ω) u :=
    ((d0 u ω).mul ((hD 2 u ω).add ((hD 1 u ω).pow 2))).congr_deriv
      (by dsimp [w0, w1, w3]; ring)
  have d3 (u : ℝ) (ω : Ω) : HasDerivAt (fun v => w3 v ω) (w4 u ω) u :=
    ((d0 u ω).mul (((hD 3 u ω).add (((hD 1 u ω).const_mul 3).mul
      (hD 2 u ω))).add ((hD 1 u ω).pow 3))).congr_deriv
      (by dsimp [w0, w1, w4, fourthBell]; ring)
  have e0 : deriv (fun u => ∫ ω, w0 u ω ∂μ) = (fun u => ∫ ω, w1 u ω ∂μ) :=
    funext fun u => (hasDerivAt_integral_compact μ w0 w1 c0 c1 d0 u).deriv
  have e1 : deriv (fun u => ∫ ω, w1 u ω ∂μ) = (fun u => ∫ ω, w2 u ω ∂μ) :=
    funext fun u => (hasDerivAt_integral_compact μ w1 w2 c1 c2 d1 u).deriv
  have e2 : deriv (fun u => ∫ ω, w2 u ω ∂μ) = (fun u => ∫ ω, w3 u ω ∂μ) :=
    funext fun u => (hasDerivAt_integral_compact μ w2 w3 c2 c3 d2 u).deriv
  have e3 : deriv (fun u => ∫ ω, w3 u ω ∂μ) = (fun u => ∫ ω, w4 u ω ∂μ) :=
    funext fun u => (hasDerivAt_integral_compact μ w3 w4 c3 c4 d3 u).deriv
  change iteratedDeriv 4 (fun u => ∫ ω, w0 u ω ∂μ) t = ∫ ω, w4 t ω ∂μ
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, e0, e1, e2, e3]

theorem hasDerivAt_expPower {n : ℕ} (X : SpinOperator n) (a : ℕ) (t : ℝ) :
    HasDerivAt (expPower X a) (expPower X (a+1) t) t := by
  exact ((hasDerivAt_exp_smul_const X t).mul_const (X^a)).congr_deriv
    (by simp only [expPower, pow_succ', mul_assoc])

theorem continuous_expPower {n : ℕ} (X : SpinOperator n) (a : ℕ) :
    Continuous (expPower X a) := by
  unfold expPower
  fun_prop

theorem continuous_tripleJet {n : ℕ} (X Y Z : SpinOperator n)
    (k a b c : ℕ) : Continuous (tripleJet X Y Z k a b c) := by
  induction k generalizing a b c with
  | zero => exact ((continuous_expPower X a).mul (continuous_expPower Y b)).mul (continuous_expPower Z c)
  | succ k ih => exact ((ih (a+1) b c).add (ih a (b+1) c)).add (ih a b (c+1))

theorem hasDerivAt_tripleJet {n : ℕ} (X Y Z : SpinOperator n)
    (k a b c : ℕ) (t : ℝ) :
    HasDerivAt (tripleJet X Y Z k a b c) (tripleJet X Y Z (k+1) a b c t) t := by
  induction k generalizing a b c with
  | zero =>
    exact (((hasDerivAt_expPower X a t).mul (hasDerivAt_expPower Y b t)).mul
      (hasDerivAt_expPower Z c t)).congr_deriv (by dsimp [tripleJet]; rw [add_mul, add_assoc])
  | succ k ih => exact ((ih (a+1) b c).add (ih a (b+1) c)).add (ih a b (c+1))

theorem gaugeJets_zero_one {n : ℕ} (X Y : SpinOperator n) :
    tripleJet X (Y-X) (-Y) 0 0 0 0 0 = 1 ∧
    tripleJet X (Y-X) (-Y) 1 0 0 0 0 = 0 := by
  simp [tripleJet]

theorem gaugeJet_two {n : ℕ} (X Y : SpinOperator n) :
    tripleJet X (Y-X) (-Y) 2 0 0 0 0 = X*Y-Y*X := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [tripleJet, expPower_zero, Nat.reduceAdd, pow_zero, pow_one, one_mul, mul_one, pow_two,
    add_apply, sub_apply, neg_apply, mul_apply_eq_comp, map_sub, map_neg]
  abel

namespace SpinSystem
variable {n : ℕ} {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] in
theorem continuous_gaugeEnergy (S : SpinSystem n V E) (F : V → SpinOperator n) (k : ℕ) :
    Continuous (Function.uncurry (S.gaugeEnergy F k)) := by
  unfold gaugeEnergy energy
  apply continuous_finsetSum
  intro e _
  exact continuous_const.mul
    (((continuous_apply (S.left e)).comp continuous_snd).subtype_val.inner
      (((continuous_tripleJet _ _ _ k 0 0 0).comp continuous_fst).clm_apply
        (((continuous_apply (S.right e)).comp continuous_snd).subtype_val)))

omit [Fintype V] in
theorem hasDerivAt_gaugeEnergy (S : SpinSystem n V E) (F : V → SpinOperator n)
    (k : ℕ) (t : ℝ) (σ : V → Spin n) :
    HasDerivAt (fun u => S.gaugeEnergy F k u σ) (S.gaugeEnergy F (k+1) t σ) t := by
  unfold gaugeEnergy energy
  apply HasDerivAt.fun_sum
  intro e _
  exact (((hasDerivAt_const t (σ (S.left e)).val).inner ℝ
    ((hasDerivAt_tripleJet _ _ _ k 0 0 0 t).clm_apply
      (hasDerivAt_const t (σ (S.right e)).val))).const_mul
        (S.strength e)).congr_deriv (by simp)

omit [Fintype V] in
theorem gaugeEnergy_at_zero (S : SpinSystem n V E) (F : V → SpinOperator n)
    (σ : V → Spin n) :
    S.gaugeEnergy F 0 0 σ = S.energy (fun _ => 1) σ ∧
    S.gaugeEnergy F 1 0 σ = 0 ∧
    S.gaugeEnergy F 2 0 σ = S.energy
      (fun e => F (S.left e)*F (S.right e)-F (S.right e)*F (S.left e)) σ := by
  have h0 := fun e => (gaugeJets_zero_one (F (S.left e)) (F (S.right e))).1
  have h1 := fun e => (gaugeJets_zero_one (F (S.left e)) (F (S.right e))).2
  simp only [gaugeEnergy, h0, h1, gaugeJet_two]
  exact ⟨True.intro, S.energy_zero σ, True.intro⟩

theorem fourth_noncommuting_identity [NeZero n] (S : SpinSystem n V E)
    (F : V → SpinOperator n) (hF : ∀ x, F x ∈ skewAdjoint (SpinOperator n))
    (hP : ∀ x s, S.pin x = some s → F x = 0) :
    (∫ σ, S.fourthWeight (fun e => F (S.right e)-F (S.left e)) 0 σ ∂S.reference) =
      ∫ σ, Real.exp (S.energy (fun _ => 1) σ) *
        (S.gaugeEnergy F 4 0 σ + 3 * (S.energy
          (fun e => F (S.left e)*F (S.right e)-F (S.right e)*F (S.left e)) σ)^2)
        ∂S.reference := by
  let A : E → SpinOperator n := fun e => F (S.right e)-F (S.left e)
  have heq : (fun t => ∫ σ, Real.exp (S.twistEnergy A 0 t σ) ∂S.reference) =
      (fun t => ∫ σ, Real.exp (S.gaugeEnergy F 0 t σ) ∂S.reference) := by
    funext t
    have htP : ∀ x s, S.pin x = some s → t • F x = 0 := by
      intro x s hs
      rw [hP x s hs]
      exact smul_zero (M := ℝ) (A := SpinOperator n) t
    have h := S.noncommuting_gauge (fun x => t • F x)
      (fun x => skewAdjoint.smul_mem t (hF x)) htP
    have hd (e : E) : t • F (S.right e) - t • F (S.left e) = t • A e :=
      (smul_sub t (F (S.right e)) (F (S.left e))).symm
    have hGP : S.gaugeProduct (fun x => t • F x) =
        (fun e => tripleJet (F (S.left e)) (F (S.right e)-F (S.left e))
          (-F (S.right e)) 0 0 0 0 t) := by
      funext e
      change NormedSpace.exp (t • F (S.left e)) *
        NormedSpace.exp (t • F (S.right e) - t • F (S.left e)) *
        NormedSpace.exp (-(t • F (S.right e))) = _
      rw [hd]
      simp only [tripleJet, expPower, pow_zero, mul_one]
      rw [smul_neg t (F (S.right e))]
    rw [hGP] at h
    simpa only [Z, twistEnergy, pow_zero, mul_one, gaugeEnergy, hd] using h
  have hl := iteratedDeriv_four_integral_exp S.reference (S.twistEnergy A)
    (S.continuous_twistEnergy A) (S.hasDerivAt_twistEnergy A) 0
  have hr := iteratedDeriv_four_integral_exp S.reference (S.gaugeEnergy F)
    (S.continuous_gaugeEnergy F) (S.hasDerivAt_gaugeEnergy F) 0
  rw [heq, hr] at hl
  refine hl.symm.trans (integral_congr_ae (Filter.Eventually.of_forall ?_))
  intro σ
  have hz := S.gaugeEnergy_at_zero F σ
  simp [fourthBell, hz.1, hz.2.1, hz.2.2]

end SpinSystem

open scoped Matrix

theorem axisA_skew : axisA ∈ skewAdjoint (SpinOperator 3) := by
  rw [skewAdjoint.mem_iff, axisA, matrixOperator_star, ← map_neg]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [axisMatrixA]

theorem axisB_skew : axisB ∈ skewAdjoint (SpinOperator 3) := by
  rw [skewAdjoint.mem_iff, axisB, matrixOperator_star, ← map_neg]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [axisMatrixB]

theorem tripleMoment_four {R : Type uR} [Ring R] (X Y Z : R) :
    tripleMoment X Y Z 4 0 0 0 = X^4+Y^4+Z^4 +
      4 • (X^3*Y+X^3*Z+X*Y^3+Y^3*Z+X*Z^3+Y*Z^3) +
      6 • (X^2*Y^2+X^2*Z^2+Y^2*Z^2) +
      12 • (X^2*Y*Z+X*Y^2*Z+X*Y*Z^2) := by
  simp only [tripleMoment, Nat.reduceAdd, pow_zero, pow_one, one_mul, mul_one]
  noncomm_ring

lemma plane_sub (f g h k : ℝ) : plane f g - plane h k = plane (f-h) (g-k) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [plane] <;> ring
lemma plane_neg (f g : ℝ) : -plane f g = plane (-f) (-g) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [plane]

lemma plane_mul_plane (a b c d : ℝ) :
    plane a b * plane c d = blkM (-(b*d)) (b*c) (a*d) (-(a*c)) (-(a*c+b*d)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [plane, blkM, Matrix.mul_apply, Fin.sum_univ_three]

lemma blkM_mul_blkM (p q r s t p' q' r' s' t' : ℝ) :
    blkM p q r s t * blkM p' q' r' s' t' =
      blkM (p*p'+q*r') (p*q'+q*s') (r*p'+s*r') (r*q'+s*s') (t*t') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blkM, Matrix.mul_apply, Fin.sum_univ_three]

lemma blkM_add_blkM (p q r s t p' q' r' s' t' : ℝ) :
    blkM p q r s t + blkM p' q' r' s' t' = blkM (p+p') (q+q') (r+r') (s+s') (t+t') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkM]

lemma nsmul_blkM (n : ℕ) (p q r s t : ℝ) :
    n • blkM p q r s t = blkM (n*p) (n*q) (n*r) (n*s) (n*t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkM, nsmul_eq_mul]

lemma smul_blkM (c p q r s t : ℝ) :
    c • blkM p q r s t = blkM (c*p) (c*q) (c*r) (c*s) (c*t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkM]

lemma third_sq_blkM : third ^ 2 = blkM (-1) 0 0 (-1) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [third, blkM, pow_two, Matrix.mul_apply, Fin.sum_univ_three]

lemma blkM_congr {p q r s t p' q' r' s' t' : ℝ} (hp : p = p') (hq : q = q') (hr : r = r')
    (hs : s = s') (ht : t = t') : blkM p q r s t = blkM p' q' r' s' t' := by
  subst hp hq hr hs ht; rfl

theorem tripleMoment_four_paired {R : Type uR} [Ring R] (X Y Z : R) :
    tripleMoment X Y Z 4 0 0 0 = X*X*(X*X)+Y*Y*(Y*Y)+Z*Z*(Z*Z) +
      4 • (X*X*(X*Y)+X*X*(X*Z)+X*Y*(Y*Y)+Y*Y*(Y*Z)+X*Z*(Z*Z)+Y*Z*(Z*Z)) +
      6 • (X*X*(Y*Y)+X*X*(Z*Z)+Y*Y*(Z*Z)) +
      12 • (X*X*(Y*Z)+X*Y*(Y*Z)+X*Y*(Z*Z)) := by
  rw [tripleMoment_four]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

lemma moment4_plane_even (f g h k : ℝ) :
    moment4Plane f g h k + moment4Plane f (-g) h (-k) =
      (6 * (f*k-g*h)^2) • third^2 := by
  unfold moment4Plane
  rw [plane_sub, plane_neg, plane_sub, plane_neg]
  simp only [tripleMoment_four_paired, plane_mul_plane, blkM_mul_blkM, blkM_add_blkM,
    nsmul_blkM, third_sq_blkM, smul_blkM]
  refine blkM_congr ?_ ?_ ?_ ?_ ?_ <;> push_cast <;> ring

theorem tripleJet_at_zero {n : ℕ} (X Y Z : SpinOperator n) (k a b c : ℕ) :
    tripleJet X Y Z k a b c 0 = tripleMoment X Y Z k a b c := by
  induction k generalizing a b c with
  | zero =>
      simp only [tripleJet, expPower, tripleMoment,
        zero_smul ℝ X, zero_smul ℝ Y, zero_smul ℝ Z, NormedSpace.exp_zero, one_mul]
  | succ k ih => simp only [tripleJet, tripleMoment, ih]

theorem map_tripleMoment {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (φ : R →+* S) (X Y Z : R) (k a b c : ℕ) :
    φ (tripleMoment X Y Z k a b c) =
      tripleMoment (φ X) (φ Y) (φ Z) k a b c := by
  induction k generalizing a b c with
  | zero => simp [tripleMoment]
  | succ k ih => simp [tripleMoment, ih]

theorem planeOperator_eq (f g : ℝ) : planeOperator f g = f • axisA + g • axisB := by
  rw [planeOperator, axisA, axisB, ← map_smul, ← map_smul, ← map_add]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [plane, axisMatrixA, axisMatrixB]

theorem plane_commutator (f g h k : ℝ) :
    plane f g * plane h k - plane h k * plane f g = (f*k-g*h) • third := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [plane, third, Matrix.cons_val_two] <;> ring

theorem planeOperator_commutator (f g h k : ℝ) :
    planeOperator f g * planeOperator h k - planeOperator h k * planeOperator f g =
      (f*k-g*h) • axisC := by
  rw [planeOperator, planeOperator, ← map_mul, ← map_mul, ← map_sub, plane_commutator,
    map_smul]
  rfl

theorem gaugeJet_plane_four_even (f g h k : ℝ) :
    tripleJet (planeOperator f g) (planeOperator h k-planeOperator f g)
      (-planeOperator h k) 4 0 0 0 0 +
    tripleJet (planeOperator f (-g)) (planeOperator h (-k)-planeOperator f (-g))
      (-planeOperator h (-k)) 4 0 0 0 0 = (6*(f*k-g*h)^2) • axisC^2 := by
  simp only [tripleJet_at_zero, planeOperator]
  have hm (f g h k : ℝ) := map_tripleMoment matrixOperator.toRingHom
    (plane f g) (plane h k-plane f g) (-plane h k) 4 0 0 0
  change ∀ f g h k, matrixOperator (tripleMoment (plane f g)
    (plane h k-plane f g) (-plane h k) 4 0 0 0) =
      tripleMoment (matrixOperator (plane f g)) (matrixOperator (plane h k-plane f g))
        (matrixOperator (-plane h k)) 4 0 0 0 at hm
  simp only [map_sub, map_neg] at hm
  rw [← hm, ← hm, ← map_add]
  change matrixOperator (moment4Plane f g h k + moment4Plane f (-g) h (-k)) = _
  rw [moment4_plane_even, map_smul, map_pow]
  rfl

theorem plane_matrix_square (f g : ℝ) :
    plane f g ^ 2 = f^2 • axisMatrixA^2 + (2*f*g) • mixedMatrixAB + g^2 • axisMatrixB^2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [plane, axisMatrixA, axisMatrixB, mixedMatrixAB, pow_succ, Matrix.cons_val_two] <;> ring

theorem plane_matrix_cube (f g : ℝ) :
    plane f g ^ 3 = f^3 • axisMatrixA^3 + (3*f^2*g) • mixedMatrixAAB + (3*f*g^2) • mixedMatrixABB + g^3 • axisMatrixB^3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [plane, axisMatrixA, axisMatrixB, mixedMatrixAAB, mixedMatrixABB, pow_succ, Matrix.cons_val_two] <;> ring

theorem plane_matrix_four_even (f g : ℝ) :
    plane f g ^ 4 + plane f (-g) ^ 4 = (2*f^4) • axisMatrixA^4 +
      (12*f^2*g^2) • mixedMatrixAABB + (2*g^4) • axisMatrixB^4 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [plane, axisMatrixA, axisMatrixB, mixedMatrixAABB, pow_succ, Matrix.cons_val_two] <;> ring

theorem planeOperator_square (f g : ℝ) :
    planeOperator f g ^ 2 = f^2 • axisA^2 + (2*f*g) • mixedAB + g^2 • axisB^2 := by
  have h := congrArg matrixOperator (plane_matrix_square f g)
  simpa only [map_add, map_smul, map_pow, planeOperator, axisA, axisB, mixedAB, mixedAAB, mixedABB, mixedAABB] using h

theorem planeOperator_cube (f g : ℝ) :
    planeOperator f g ^ 3 = f^3 • axisA^3 + (3*f^2*g) • mixedAAB +
      (3*f*g^2) • mixedABB + g^3 • axisB^3 := by
  have h := congrArg matrixOperator (plane_matrix_cube f g)
  simpa only [map_add, map_smul, map_pow, planeOperator, axisA, axisB, mixedAB, mixedAAB, mixedABB, mixedAABB] using h

theorem planeOperator_four_even (f g : ℝ) :
    planeOperator f g ^ 4 + planeOperator f (-g) ^ 4 = (2*f^4) • axisA^4 +
      (12*f^2*g^2) • mixedAABB + (2*g^4) • axisB^4 := by
  have h := congrArg matrixOperator (plane_matrix_four_even f g)
  simpa only [map_add, map_smul, map_pow, planeOperator, axisA, axisB, mixedAB, mixedAAB, mixedABB, mixedAABB] using h

namespace SpinSystem
variable {n : ℕ} {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] in
theorem energy_add (S : SpinSystem n V E) (K L : E → SpinOperator n) (σ : V → Spin n) :
    S.energy (K+L) σ = S.energy K σ + S.energy L σ := by
  simp [energy, inner_add_right, mul_add, Finset.sum_add_distrib]

omit [Fintype V] in
theorem energy_smul (S : SpinSystem n V E) (r : ℝ) (K : E → SpinOperator n)
    (σ : V → Spin n) : S.energy (r • K) σ = r * S.energy K σ := by
  simp only [energy, Pi.smul_apply, smul_apply, real_inner_smul_right,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Fintype V] in
theorem energy_neg (S : SpinSystem n V E) (K : E → SpinOperator n) (σ : V → Spin n) :
    S.energy (-K) σ = -S.energy K σ := by
  simp [energy]

theorem fourthResponse_integral [NeZero n] (S : SpinSystem n V E)
    (A : E → SpinOperator n) :
    S.fourthResponse A = (∫ σ, S.fourthWeight A 0 σ ∂S.reference) / S.Z (fun _ => 1) := by
  unfold fourthResponse average
  congr 1
  apply integral_congr_ae (Filter.Eventually.of_forall _)
  intro σ
  have hz (e : E) : (0:ℝ) • A e = 0 := zero_smul ℝ (A e)
  simp only [fourthWeight, twistEnergy, hz, NormedSpace.exp_zero, one_mul, pow_zero,
    fourthPolynomial]
  ring

theorem fourthResponse_gauge [NeZero n] (S : SpinSystem n V E)
    (F : V → SpinOperator n) (hF : ∀ x, F x ∈ skewAdjoint (SpinOperator n))
    (hP : ∀ x s, S.pin x = some s → F x = 0) :
    S.fourthResponse (fun e => F (S.right e)-F (S.left e)) =
      S.average (fun σ => S.gaugeEnergy F 4 0 σ + 3 * (S.energy
        (fun e => F (S.left e)*F (S.right e)-F (S.right e)*F (S.left e)) σ)^2) := by
  rw [S.fourthResponse_integral, S.fourth_noncommuting_identity F hF hP]
  unfold average
  congr 1
  apply integral_congr_ae (Filter.Eventually.of_forall _)
  intro σ
  exact mul_comm _ _

end SpinSystem

end ClassicalON

end

end OAI
end

section
-- module Solutions.OAIQW_ClassicalON.RotationWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uK uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
noncomputable section
open scoped BigOperators

namespace MixedAlgebra
variable {E : Type uE} {K : Type uK} [Fintype E] [CommRing K]

theorem four_polarize_a (J : Coeffs E K) (u w v : E → K) :
    four J (u+w) v (u+w) v = four J u v u v + 2 * four J u v w v + four J w v w v := by
  rw [four_add_first, four_add_third, four_add_third, four_swap_first_third J w v u]
  ring

theorem four_polarize_b (J : Coeffs E K) (u w v z : E → K) :
    four J u (v+z) w (v+z) = four J u v w v + 2 * four J u v w z + four J u z w z := by
  rw [four_add_second, four_add_fourth, four_add_fourth, four_swap_second_fourth J u z w v]
  ring

end MixedAlgebra

namespace MixedAlgebra
variable {E : Type uE} {K : Type uK} [Fintype E] [CommRing K]

theorem four_diagonal (J : Coeffs E K) (u v : E → K) :
    four J u v u v =
      (weighted J.a u)^2 * (weighted J.b v)^2 +
      weighted J.aa (u*u) * (weighted J.b v)^2 +
      weighted J.bb (v*v) * (weighted J.a u)^2 +
      4 * weighted J.ab (u*v) * weighted J.a u * weighted J.b v +
      weighted J.aa (u*u) * weighted J.bb (v*v) +
      2 * (weighted J.ab (u*v))^2 +
      2 * weighted J.aab (u*u*v) * weighted J.b v +
      2 * weighted J.abb (u*v*v) * weighted J.a u +
      weighted J.aabb (u*u*v*v) := by
  simp only [four, mul_comm, mul_left_comm]
  ring

end MixedAlgebra

theorem bell4_even (a b aa ab bb aaa aab abb bbb p q aaaa aabb bbbb : ℝ)
    (h : p+q = 2*aaaa+12*aabb+2*bbbb) :
    bell4 (a+b) (aa+2*ab+bb) (aaa+3*aab+3*abb+bbb) p +
      bell4 (a-b) (aa-2*ab+bb) (aaa-3*aab+3*abb-bbb) q -
      2*bell4 a aa aaa aaaa - 2*bell4 b bb bbb bbbb =
      12*(a^2*b^2+aa*b^2+bb*a^2+4*ab*a*b+aa*bb+2*ab^2+
        2*aab*b+2*abb*a+aabb) := by
  unfold bell4
  nlinarith only [h]

namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem fourthResponse_plane_even (S : SpinSystem 3 V E) (f g : V → ℝ)
    (hf : ∀ x s, S.pin x = some s → f x = 0)
    (hg : ∀ x s, S.pin x = some s → g x = 0) :
    S.fourthResponse (S.planarGradient f g) +
      S.fourthResponse (S.planarGradient f (-g)) =
        6 * S.secondAxisResponse (S.crossForm f g) (S.crossForm f g) := by
  have hsk (f g : V → ℝ) (x : V) :
      planeOperator (f x) (g x) ∈ skewAdjoint (SpinOperator 3) := by
    rw [planeOperator_eq]
    exact (skewAdjoint _).add_mem (skewAdjoint.smul_mem _ axisA_skew)
      (skewAdjoint.smul_mem _ axisB_skew)
  have hp : ∀ x s, S.pin x = some s → planeOperator (f x) (g x) = 0 := by
    intro x s hs
    rw [hf x s hs, hg x s hs, planeOperator_eq]
    simp only [zero_smul ℝ axisA, zero_smul ℝ axisB, add_zero]
  have hm : ∀ x s, S.pin x = some s → planeOperator (f x) ((-g) x) = 0 := by
    intro x s hs
    rw [Pi.neg_apply, hg x s hs, neg_zero, hf x s hs, planeOperator_eq]
    simp only [zero_smul ℝ axisA, zero_smul ℝ axisB, add_zero]
  change S.fourthResponse (fun e => planeOperator (f (S.right e)) (g (S.right e)) -
    planeOperator (f (S.left e)) (g (S.left e))) + S.fourthResponse (fun e =>
      planeOperator (f (S.right e)) ((-g) (S.right e)) -
      planeOperator (f (S.left e)) ((-g) (S.left e))) = _
  rw [S.fourthResponse_gauge _ (hsk f g) hp,
    S.fourthResponse_gauge _ (hsk f (-g)) hm]
  let w := S.crossForm f g
  have he (σ : V → Spin 3) :
      S.gaugeEnergy (fun x => planeOperator (f x) (g x)) 4 0 σ +
      S.gaugeEnergy (fun x => planeOperator (f x) ((-g) x)) 4 0 σ =
        S.energy (fun e => (6*(w e)^2) • axisC^2) σ := by
    rw [gaugeEnergy, gaugeEnergy, ← S.energy_add]
    apply congrArg (fun K => S.energy K σ)
    funext e
    have ht := gaugeJet_plane_four_even (f (S.left e)) (g (S.left e))
      (f (S.right e)) (g (S.right e))
    dsimp only [Pi.add_apply, Pi.neg_apply, w, crossForm]
    with_reducible exact ht
  have hcm : (fun e =>
      planeOperator (f (S.left e)) ((-g) (S.left e)) *
        planeOperator (f (S.right e)) ((-g) (S.right e)) -
      planeOperator (f (S.right e)) ((-g) (S.right e)) *
        planeOperator (f (S.left e)) ((-g) (S.left e))) = -(fun e => w e • axisC) := by
    funext e
    rw [planeOperator_commutator]
    change (f (S.left e) * (-g) (S.right e) - (-g) (S.left e) * f (S.right e)) • axisC = -(w e • axisC)
    rw [← neg_smul (w e) axisC]
    congr 1
    dsimp only [w, crossForm, Pi.neg_apply]
    ring
  have hcp : (fun e =>
      planeOperator (f (S.left e)) (g (S.left e)) *
        planeOperator (f (S.right e)) (g (S.right e)) -
      planeOperator (f (S.right e)) (g (S.right e)) *
        planeOperator (f (S.left e)) (g (S.left e))) = (fun e => w e • axisC) := by
    funext e
    exact planeOperator_commutator _ _ _ _
  rw [hcp, hcm]
  simp only [S.energy_neg, neg_sq]
  have hc (F : V → SpinOperator 3) : Continuous (fun σ =>
      S.gaugeEnergy F 4 0 σ + 3 * (S.energy (fun e => w e • axisC) σ)^2) :=
    ((S.continuous_gaugeEnergy F 4).comp (continuous_const.prodMk continuous_id)).add
      (continuous_const.mul ((S.continuous_energy _).pow 2))
  rw [← S.average_add (hc _) (hc _)]
  have hpoint : (fun σ =>
      (S.gaugeEnergy (fun x => planeOperator (f x) (g x)) 4 0 σ +
        3 * (S.energy (fun e => w e • axisC) σ)^2) +
      (S.gaugeEnergy (fun x => planeOperator (f x) ((-g) x)) 4 0 σ +
        3 * (S.energy (fun e => w e • axisC) σ)^2)) =
      (fun σ => 6 * (S.energy (fun e => (w e*w e) • axisC^2) σ +
        S.energy (fun e => w e • axisC) σ * S.energy (fun e => w e • axisC) σ)) := by
    funext σ
    have ht := he σ
    have hsc : (fun e => (6*(w e)^2) • axisC^2) =
        (6 : ℝ) • (fun e => (w e*w e) • axisC^2) := by
      funext e
      simp only [Pi.smul_apply, smul_smul, pow_two]
    rw [hsc, S.energy_smul] at ht
    nlinarith
  change S.average (fun σ =>
      (S.gaugeEnergy (fun x => planeOperator (f x) (g x)) 4 0 σ +
        3 * (S.energy (fun e => w e • axisC) σ)^2) +
      (S.gaugeEnergy (fun x => planeOperator (f x) ((-g) x)) 4 0 σ +
        3 * (S.energy (fun e => w e • axisC) σ)^2)) = _
  rw [hpoint, S.average_mul_const]
  rfl

variable {n : ℕ}

theorem fourthResponse_axisGradient [NeZero n] (S : SpinSystem n V E)
    (g : SpinOperator n) (hg : g ∈ skewAdjoint (SpinOperator n)) (f : V → ℝ)
    (hP : ∀ x s, S.pin x = some s → f x = 0) :
    S.fourthResponse (S.axisGradient f g) = 0 := by
  let A := S.axisGradient f g
  have hZ : (fun t => S.Z (fun e => NormedSpace.exp (t • A e))) =
      (fun _ : ℝ => S.Z (fun _ => 1)) := funext (S.Z_gradient_line g hg f hP)
  have hfirst : (fun t => ∫ σ, S.firstWeight A t σ ∂S.reference) = (fun _ : ℝ => 0) := by
    funext t
    have h := S.hasDerivAt_twistZ A t
    rw [hZ] at h
    exact h.unique (hasDerivAt_const t _)
  have hsecond : (fun t => ∫ σ, S.secondWeight A t σ ∂S.reference) = (fun _ : ℝ => 0) := by
    funext t
    have h := S.hasDerivAt_firstVariation A t
    rw [hfirst] at h
    exact h.unique (hasDerivAt_const t 0)
  have hthird : (fun t => ∫ σ, S.thirdWeight A t σ ∂S.reference) = (fun _ : ℝ => 0) := by
    funext t
    have h := S.hasDerivAt_secondVariation A t
    rw [hsecond] at h
    exact h.unique (hasDerivAt_const t 0)
  have hfourth : (∫ σ, S.fourthWeight A 0 σ ∂S.reference) = 0 := by
    have h := S.hasDerivAt_thirdVariation A 0
    rw [hthird] at h
    exact h.unique (hasDerivAt_const 0 0)
  rw [S.fourthResponse_integral, hfourth, zero_div]

omit [Fintype V] [Fintype E] in
theorem planarGradient_eq (S : SpinSystem 3 V E) (f g : V → ℝ) :
    S.planarGradient f g = fun e => planeOperator (S.differential f e) (S.differential g e) := by
  funext e
  simp only [planarGradient, planeOperator_eq, differential]
  module

omit [Fintype V] in
theorem planeEnergy_one (S : SpinSystem 3 V E) (u v : E → ℝ) (σ : V → Spin 3) :
    S.energy (fun e => planeOperator (u e) (v e)) σ =
      MixedAlgebra.weighted (S.mixedCoefficients σ).a u +
      MixedAlgebra.weighted (S.mixedCoefficients σ).b v := by
  simp only [planeOperator_eq]
  change S.energy ((fun e => u e • axisA) + (fun e => v e • axisB)) σ = _
  rw [S.energy_add, S.energy_weighted, S.energy_weighted]
  rfl

end ClassicalON.SpinSystem

end
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

omit [Fintype V] in
theorem planeEnergy_two (S : SpinSystem 3 V E) (u v : E → ℝ) (σ : V → Spin 3) :
    S.energy (fun e => planeOperator (u e) (v e)^2) σ =
      MixedAlgebra.weighted (S.mixedCoefficients σ).aa (u*u) +
      2 * MixedAlgebra.weighted (S.mixedCoefficients σ).ab (u*v) +
      MixedAlgebra.weighted (S.mixedCoefficients σ).bb (v*v) := by
  simp only [planeOperator_square]
  change S.energy (((fun e => u e^2 • axisA^2) +
    (fun e => (2*u e*v e) • mixedAB)) + (fun e => v e^2 • axisB^2)) σ = _
  rw [S.energy_add, S.energy_add, S.energy_weighted, S.energy_weighted, S.energy_weighted]
  simp only [mixedCoefficients, pow_two, mul_assoc]
  rw [MixedAlgebra.weighted_const_mul]
  rfl

omit [Fintype V] in
theorem planeEnergy_three (S : SpinSystem 3 V E) (u v : E → ℝ) (σ : V → Spin 3) :
    S.energy (fun e => planeOperator (u e) (v e)^3) σ =
      MixedAlgebra.weighted (S.localCoefficient (axisA^3) σ) (u^3) +
      3 * MixedAlgebra.weighted (S.mixedCoefficients σ).aab (u*u*v) +
      3 * MixedAlgebra.weighted (S.mixedCoefficients σ).abb (u*v*v) +
      MixedAlgebra.weighted (S.localCoefficient (axisB^3) σ) (v^3) := by
  simp only [planeOperator_cube]
  change S.energy ((((fun e => u e^3 • axisA^3) +
    (fun e => (3*u e^2*v e) • mixedAAB)) +
    (fun e => (3*u e*v e^2) • mixedABB)) + (fun e => v e^3 • axisB^3)) σ = _
  rw [S.energy_add, S.energy_add, S.energy_add,
    S.energy_weighted, S.energy_weighted, S.energy_weighted, S.energy_weighted]
  simp only [mixedCoefficients, pow_two, mul_assoc]
  rw [MixedAlgebra.weighted_const_mul, MixedAlgebra.weighted_const_mul]
  rfl

omit [Fintype V] in
theorem planeEnergy_four_even (S : SpinSystem 3 V E) (u v : E → ℝ) (σ : V → Spin 3) :
    S.energy (fun e => planeOperator (u e) (v e)^4) σ +
      S.energy (fun e => planeOperator (u e) (-v e)^4) σ =
      2 * MixedAlgebra.weighted (S.localCoefficient (axisA^4) σ) (u^4) +
      12 * MixedAlgebra.weighted (S.mixedCoefficients σ).aabb (u*u*v*v) +
      2 * MixedAlgebra.weighted (S.localCoefficient (axisB^4) σ) (v^4) := by
  rw [← S.energy_add]
  have hp : (fun e => planeOperator (u e) (v e)^4) +
      (fun e => planeOperator (u e) (-v e)^4) =
      ((fun e => (2*u e^4) • axisA^4) +
        (fun e => (12*u e^2*v e^2) • mixedAABB)) +
        (fun e => (2*v e^4) • axisB^4) := by
    funext e
    exact planeOperator_four_even (u e) (v e)
  rw [hp, S.energy_add, S.energy_add, S.energy_weighted, S.energy_weighted, S.energy_weighted]
  simp only [mixedCoefficients, pow_two, mul_assoc]
  rw [MixedAlgebra.weighted_const_mul, MixedAlgebra.weighted_const_mul,
    MixedAlgebra.weighted_const_mul]
  rfl

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

omit [Fintype V] in
theorem energy_scaled_power (S : SpinSystem n V E) (M : SpinOperator n)
    (u : E → ℝ) (k : ℕ) (σ : V → Spin n) :
    S.energy (fun e => (u e • M)^k) σ =
      MixedAlgebra.weighted (S.localCoefficient (M^k) σ) (u^k) := by
  have hp : (fun e => (u e • M)^k) = (fun e => (u e)^k • M^k) :=
    funext (fun e => operator_smul_pow (u e) M k)
  rw [hp]
  exact S.energy_weighted (M^k) (u^k) σ

attribute [local fun_prop] continuous_energy

omit [Fintype V] in
theorem fourthObservable_even (S : SpinSystem 3 V E) (u v : E → ℝ) :
    S.fourthObservable (fun e => planeOperator (u e) (v e)) +
      S.fourthObservable (fun e => planeOperator (u e) (-v e)) -
      (2:ℝ) • S.fourthObservable (fun e => u e • axisA) -
      (2:ℝ) • S.fourthObservable (fun e => v e • axisB) =
      (12:ℝ) • S.mixedObservable u v u v := by
  ext σ
  change fourthPolynomial (fun k => S.energy (fun e => planeOperator (u e) (v e)^k) σ) +
    fourthPolynomial (fun k => S.energy (fun e => planeOperator (u e) (-v e)^k) σ) -
    2 * fourthPolynomial (fun k => S.energy (fun e => (u e • axisA)^k) σ) -
    2 * fourthPolynomial (fun k => S.energy (fun e => (v e • axisB)^k) σ) =
    12 * MixedAlgebra.four (S.mixedCoefficients σ) u v u v
  simp only [fourthPolynomial, pow_one, planeEnergy_one, planeEnergy_two,
    planeEnergy_three, energy_scaled_power, energy_weighted]
  have hn : (fun e => -v e) = -v := rfl
  have hv3 : (-v)^3 = -(v^3) := by ring
  simp only [hn, hv3, neg_mul, mul_neg, neg_neg, MixedAlgebra.weighted_neg]
  have hp := S.planeEnergy_four_even u v σ
  have hb := bell4_even
    (MixedAlgebra.weighted (S.mixedCoefficients σ).a u)
    (MixedAlgebra.weighted (S.mixedCoefficients σ).b v)
    (MixedAlgebra.weighted (S.mixedCoefficients σ).aa (u*u))
    (MixedAlgebra.weighted (S.mixedCoefficients σ).ab (u*v))
    (MixedAlgebra.weighted (S.mixedCoefficients σ).bb (v*v))
    (MixedAlgebra.weighted (S.localCoefficient (axisA^3) σ) (u^3))
    (MixedAlgebra.weighted (S.mixedCoefficients σ).aab (u*u*v))
    (MixedAlgebra.weighted (S.mixedCoefficients σ).abb (u*v*v))
    (MixedAlgebra.weighted (S.localCoefficient (axisB^3) σ) (v^3))
    (S.energy (fun e => planeOperator (u e) (v e)^4) σ)
    (S.energy (fun e => planeOperator (u e) (-v e)^4) σ)
    (MixedAlgebra.weighted (S.localCoefficient (axisA^4) σ) (u^4))
    (MixedAlgebra.weighted (S.mixedCoefficients σ).aabb (u*u*v*v))
    (MixedAlgebra.weighted (S.localCoefficient (axisB^4) σ) (v^4)) hp
  rw [MixedAlgebra.four_diagonal]
  simp only [bell4, mixedCoefficients] at hb ⊢
  convert hb using 1
  ring_nf

theorem mixedResponse_diagonal (S : SpinSystem 3 V E) (f g : V → ℝ)
    (hf : ∀ x s, S.pin x = some s → f x = 0)
    (hg : ∀ x s, S.pin x = some s → g x = 0) :
    2 * S.mixedResponse (S.differential f) (S.differential g)
      (S.differential f) (S.differential g) =
      S.secondAxisResponse (S.crossForm f g) (S.crossForm f g) := by
  have h := congrArg S.averageLinear
    (S.fourthObservable_even (S.differential f) (S.differential g))
  simp only [map_sub, map_add, map_smul, smul_eq_mul,
    average_fourthObservable] at h
  have hp := S.fourthResponse_plane_even f g hf hg
  have ha := S.fourthResponse_axisGradient axisA axisA_skew f hf
  have hb := S.fourthResponse_axisGradient axisB axisB_skew g hg
  rw [S.planarGradient_eq, S.planarGradient_eq] at hp
  have hm : S.differential (-g) = fun e => -S.differential g e := by
    funext e
    simp only [differential, Pi.neg_apply]
    ring
  rw [hm] at hp
  change S.fourthResponse (fun e => S.differential f e • axisA) = 0 at ha
  change S.fourthResponse (fun e => S.differential g e • axisB) = 0 at hb
  rw [ha, hb] at h
  unfold mixedResponse
  linarith

theorem mixedResponse_polarize_a (S : SpinSystem 3 V E) (u w v : E → ℝ) :
    S.mixedResponse (u+w) v (u+w) v = S.mixedResponse u v u v +
      2 * S.mixedResponse u v w v + S.mixedResponse w v w v := by
  have hp : S.mixedObservable (u+w) v (u+w) v = S.mixedObservable u v u v +
      (2:ℝ) • S.mixedObservable u v w v + S.mixedObservable w v w v := by
    ext σ
    exact MixedAlgebra.four_polarize_a (S.mixedCoefficients σ) u w v
  unfold mixedResponse
  rw [hp, map_add, map_add, map_smul, smul_eq_mul]

theorem mixedResponse_polarize_b (S : SpinSystem 3 V E) (u w v z : E → ℝ) :
    S.mixedResponse u (v+z) w (v+z) = S.mixedResponse u v w v +
      2 * S.mixedResponse u v w z + S.mixedResponse u z w z := by
  have hp : S.mixedObservable u (v+z) w (v+z) = S.mixedObservable u v w v +
      (2:ℝ) • S.mixedObservable u v w z + S.mixedObservable u z w z := by
    ext σ
    exact MixedAlgebra.four_polarize_b (S.mixedCoefficients σ) u w v z
  unfold mixedResponse
  rw [hp, map_add, map_add, map_smul, smul_eq_mul]

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

omit [Fintype V] [Fintype E] in
theorem differential_add (S : SpinSystem n V E) (f g : V → ℝ) :
    S.differential (f+g) = S.differential f + S.differential g := by
  funext e
  simp only [differential, Pi.add_apply]
  ring

omit [Fintype V] [Fintype E] in
theorem crossForm_add_left (S : SpinSystem 3 V E) (f g h : V → ℝ) :
    S.crossForm (f+g) h = S.crossForm f h + S.crossForm g h := by
  funext e
  simp only [crossForm, Pi.add_apply]
  ring

omit [Fintype V] [Fintype E] in
theorem crossForm_add_right (S : SpinSystem 3 V E) (f g h : V → ℝ) :
    S.crossForm f (g+h) = S.crossForm f g + S.crossForm f h := by
  funext e
  simp only [crossForm, Pi.add_apply]
  ring

theorem mixedResponse_a_polarized (S : SpinSystem 3 V E) (f h g : V → ℝ)
    (hf : ∀ x s, S.pin x = some s → f x = 0)
    (hh : ∀ x s, S.pin x = some s → h x = 0)
    (hg : ∀ x s, S.pin x = some s → g x = 0) :
    2 * S.mixedResponse (S.differential f) (S.differential g)
      (S.differential h) (S.differential g) =
      S.secondAxisResponse (S.crossForm f g) (S.crossForm h g) := by
  have hfh : ∀ x s, S.pin x = some s → (f+h) x = 0 := by
    intro x s hs
    simp only [Pi.add_apply, hf x s hs, hh x s hs, add_zero]
  have hp := S.mixedResponse_diagonal (f+h) g hfh hg
  rw [S.differential_add, S.mixedResponse_polarize_a, S.crossForm_add_left,
    S.secondAxisResponse_add_left, S.secondAxisResponse_add_right,
    S.secondAxisResponse_add_right, S.secondAxisResponse_symm (S.crossForm h g)] at hp
  have hdiagf := S.mixedResponse_diagonal f g hf hg
  have hdiagh := S.mixedResponse_diagonal h g hh hg
  linarith

theorem mixedResponse_ward (S : SpinSystem 3 V E) (f g h k : V → ℝ)
    (hf : ∀ x s, S.pin x = some s → f x = 0)
    (hg : ∀ x s, S.pin x = some s → g x = 0)
    (hh : ∀ x s, S.pin x = some s → h x = 0)
    (hk : ∀ x s, S.pin x = some s → k x = 0) :
    4 * S.mixedResponse (S.differential f) (S.differential g)
      (S.differential h) (S.differential k) =
      S.secondAxisResponse (S.crossForm f g) (S.crossForm h k) +
        S.secondAxisResponse (S.crossForm f k) (S.crossForm h g) := by
  have hgk : ∀ x s, S.pin x = some s → (g+k) x = 0 := by
    intro x s hs
    simp only [Pi.add_apply, hg x s hs, hk x s hs, add_zero]
  have hp := S.mixedResponse_a_polarized f h (g+k) hf hh hgk
  rw [S.differential_add, S.mixedResponse_polarize_b, S.crossForm_add_right,
    S.crossForm_add_right, S.secondAxisResponse_add_left,
    S.secondAxisResponse_add_right, S.secondAxisResponse_add_right] at hp
  have hdiagg := S.mixedResponse_a_polarized f h g hf hh hg
  have hdiagk := S.mixedResponse_a_polarized f h k hf hh hk
  linarith

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

theorem ComplexFourForm.zero_of_real {V : Type uV} (F : ComplexFourForm (V → ℂ))
    (P : V → Prop)
    (hr : ∀ u v w z : V → ℝ,
      (∀ x, P x → u x = 0) → (∀ x, P x → v x = 0) →
      (∀ x, P x → w x = 0) → (∀ x, P x → z x = 0) →
      F (fun x => (u x : ℂ)) (fun x => (v x : ℂ))
        (fun x => (w x : ℂ)) (fun x => (z x : ℂ)) = 0)
    (u v w z : V → ℂ)
    (hu : ∀ x, P x → u x = 0) (hv : ∀ x, P x → v x = 0)
    (hw : ∀ x, P x → w x = 0) (hz : ∀ x, P x → z x = 0) :
    F u v w z = 0 := by
  apply complex_linear_zero_of_real P (fun u => F u v w z)
    (fun u u' => F.add_first u u' v w z) (fun r u => F.smul_first r u v w z) ?_ u hu
  intro a ha
  apply complex_linear_zero_of_real P (fun v => F (fun x => (a x : ℂ)) v w z)
    (fun v v' => F.add_second (fun x => (a x : ℂ)) v v' w z)
    (fun r v => F.smul_second r (fun x => (a x : ℂ)) v w z) ?_ v hv
  intro b hb
  apply complex_linear_zero_of_real P
    (fun w => F (fun x => (a x : ℂ)) (fun x => (b x : ℂ)) w z)
    (fun w w' => F.add_third (fun x => (a x : ℂ)) (fun x => (b x : ℂ)) w w' z)
    (fun r w => F.smul_third r (fun x => (a x : ℂ)) (fun x => (b x : ℂ)) w z) ?_ w hw
  intro c hc
  apply complex_linear_zero_of_real P
    (fun z => F (fun x => (a x : ℂ)) (fun x => (b x : ℂ)) (fun x => (c x : ℂ)) z)
    (fun z z' => F.add_fourth (fun x => (a x : ℂ)) (fun x => (b x : ℂ)) (fun x => (c x : ℂ)) z z')
    (fun r z => F.smul_fourth r (fun x => (a x : ℂ)) (fun x => (b x : ℂ)) (fun x => (c x : ℂ)) z)
    ?_ z hz
  intro d hd
  exact hr a b c d ha hb hc hd

namespace MixedAlgebra
variable {E : Type uE} {K : Type uK} {L : Type uL} [Fintype E] [CommRing K] [CommRing L]

theorem weighted_map (φ : K →+* L) (J u : E → K) :
    weighted (φ ∘ J) (φ ∘ u) = φ (weighted J u) := by
  simp [weighted]

theorem four_map (φ : K →+* L) (J : Coeffs E K) (u v w z : E → K) :
    four (J.map φ) (φ ∘ u) (φ ∘ v) (φ ∘ w) (φ ∘ z) = φ (four J u v w z) := by
  simp only [four, Coeffs.map, weighted, Function.comp_apply, Pi.mul_apply,
    map_add, map_mul, map_sum]

end MixedAlgebra

namespace ClassicalON.SpinSystem
variable {n : ℕ} {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem complexMixedResponse_ofReal (S : SpinSystem 3 V E) (u v w z : E → ℝ) :
    S.complexMixedResponse (fun e => (u e : ℂ)) (fun e => (v e : ℂ))
      (fun e => (w e : ℂ)) (fun e => (z e : ℂ)) = (S.mixedResponse u v w z : ℂ) := by
  have hc : S.complexMixedObservable (fun e => (u e : ℂ)) (fun e => (v e : ℂ))
      (fun e => (w e : ℂ)) (fun e => (z e : ℂ)) = ofRealObservable (S.mixedObservable u v w z) := by
    ext σ
    exact MixedAlgebra.four_map Complex.ofRealHom (S.mixedCoefficients σ) u v w z
  unfold complexMixedResponse
  rw [hc, S.averageComplex_ofReal]
  rfl

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
theorem complexCross_ofReal (S : SpinSystem 3 V E) (f g : V → ℝ) :
    S.complexCross (fun x => (f x : ℂ)) (fun x => (g x : ℂ)) =
      fun e => (S.crossForm f g e : ℂ) := by
  ext e
  simp [complexCross, crossForm]

omit [Fintype V] [Fintype E] in
theorem differential_ofReal (S : SpinSystem n V E) (f : V → ℝ) :
    S.differential (fun x => (f x : ℂ)) = fun e => (S.differential (K := ℝ) f e : ℂ) := by
  ext e
  simp [differential]

theorem complexWardDefect_real (S : SpinSystem 3 V E) (f g h k : V → ℝ)
    (hf : ∀ x s, S.pin x = some s → f x = 0)
    (hg : ∀ x s, S.pin x = some s → g x = 0)
    (hh : ∀ x s, S.pin x = some s → h x = 0)
    (hk : ∀ x s, S.pin x = some s → k x = 0) :
    S.complexWardDefect (fun x => (f x : ℂ)) (fun x => (g x : ℂ))
      (fun x => (h x : ℂ)) (fun x => (k x : ℂ)) = 0 := by
  change _ - _ = 0
  apply sub_eq_zero.mpr
  simp only [differential_ofReal, complexCross_ofReal, complexMixedResponse_ofReal,
    complexSecondResponse_ofReal]
  exact_mod_cast S.mixedResponse_ward f g h k hf hg hh hk

theorem complexMixedResponse_ward (S : SpinSystem 3 V E) (f g h k : V → ℂ)
    (hf : ∀ x s, S.pin x = some s → f x = 0)
    (hg : ∀ x s, S.pin x = some s → g x = 0)
    (hh : ∀ x s, S.pin x = some s → h x = 0)
    (hk : ∀ x s, S.pin x = some s → k x = 0) :
    4 * S.complexMixedResponse (S.differential f) (S.differential g)
      (S.differential h) (S.differential k) =
      S.complexSecondResponse (S.complexCross f g) (S.complexCross h k) +
        S.complexSecondResponse (S.complexCross f k) (S.complexCross h g) := by
  apply sub_eq_zero.mp
  change S.complexWardDefect f g h k = 0
  refine S.complexWardDefect.zero_of_real (fun x => ∃ s, S.pin x = some s) ?_ f g h k ?_ ?_ ?_ ?_
  · intro a b c d ha hb hc hd
    exact S.complexWardDefect_real a b c d
      (fun x s hs => ha x ⟨s, hs⟩) (fun x s hs => hb x ⟨s, hs⟩)
      (fun x s hs => hc x ⟨s, hs⟩) (fun x s hs => hd x ⟨s, hs⟩)
  · rintro x ⟨s, hs⟩; exact hf x s hs
  · rintro x ⟨s, hs⟩; exact hg x s hs
  · rintro x ⟨s, hs⟩; exact hh x s hs
  · rintro x ⟨s, hs⟩; exact hk x s hs

end ClassicalON.SpinSystem

end
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

omit [Fintype V] [Fintype E] [Fintype I] in
theorem commutatorForm_conj (S : SpinSystem 3 V E) (f g : V → ℂ) :
    S.commutatorForm (fun x => conj (f x)) (fun x => conj (g x)) =
      (fun e => conj (S.commutatorForm f g e)) := by
  ext e
  simp only [commutatorForm, complexCross, Pi.smul_apply, smul_eq_mul,
    map_mul, map_sub, map_div₀, map_one, map_ofNat]

omit [Fintype I] in
theorem complexMixedResponse_commutator (S : SpinSystem 3 V E) (f g h k : V → ℂ)
    (hf : ∀ x s, S.pin x = some s → f x = 0)
    (hg : ∀ x s, S.pin x = some s → g x = 0)
    (hh : ∀ x s, S.pin x = some s → h x = 0)
    (hk : ∀ x s, S.pin x = some s → k x = 0) :
    S.complexMixedResponse (S.differential f) (S.differential g)
      (S.differential h) (S.differential k) =
      S.complexSecondResponse (S.commutatorForm f g) (S.commutatorForm h k) +
        S.complexSecondResponse (S.commutatorForm f k) (S.commutatorForm h g) := by
  have hw := S.complexMixedResponse_ward f g h k hf hg hh hk
  simp only [commutatorForm, S.complexSecondResponse_smul_left, S.complexSecondResponse_smul_right]
  linear_combination (1/4 : ℂ) * hw

omit [Fintype I] in
theorem complexMixedResponse_paired_oai (S : SpinSystem 3 V E) (f g : V → ℂ)
    (hf : ∀ x s, S.pin x = some s → f x = 0)
    (hg : ∀ x s, S.pin x = some s → g x = 0) :
    S.complexMixedResponse (S.differential f) (fun e => conj (S.differential f e))
      (fun e => conj (S.differential g e)) (S.differential g) =
      S.complexSecondResponse (S.commutatorForm f (fun x => conj (f x)))
        (fun e => conj (S.commutatorForm g (fun x => conj (g x)) e)) -
      S.complexSecondResponse (S.commutatorForm f g) (fun e => conj (S.commutatorForm f g e)) := by
  have hfc : ∀ x s, S.pin x = some s → conj (f x) = 0 := by
    intro x s hs; rw [hf x s hs, map_zero]
  have hgc : ∀ x s, S.pin x = some s → conj (g x) = 0 := by
    intro x s hs; rw [hg x s hs, map_zero]
  have h := S.complexMixedResponse_commutator f (fun x => conj (f x))
    (fun x => conj (g x)) g hf hfc hgc hg
  have df (a : V → ℂ) : S.differential (fun x => conj (a x)) =
      fun e => conj (S.differential a e) := by ext e; simp only [differential, map_sub]
  have cc : S.commutatorForm (fun x => conj (g x)) g =
      (fun e => conj (S.commutatorForm g (fun x => conj (g x)) e)) := by
    simpa only [starRingEnd_self_apply] using S.commutatorForm_conj g (fun x => conj (g x))
  have cd : S.commutatorForm (fun x => conj (g x)) (fun x => conj (f x)) =
      -(fun e => conj (S.commutatorForm f g e)) := by
    rw [S.commutatorForm_antisymm, S.commutatorForm_conj]
  rw [df f, df g, cc, cd] at h
  change S.complexMixedResponse _ _ _ _ = S.complexSecondBilin _ _ + S.complexSecondBilin _ (-_) at h
  simpa only [map_neg, sub_eq_add_neg, complexSecondBilin, LinearMap.coe_mk, AddHom.coe_mk] using h

end ClassicalON.SpinSystem

end

end OAI
end

theorem solution.{uE, uV} : type_of% @OAI.ClassicalON.SpinSystem.complexMixedResponse_paired_oai.{uE, uV} := @OAI.ClassicalON.SpinSystem.complexMixedResponse_paired_oai.{uE, uV}
