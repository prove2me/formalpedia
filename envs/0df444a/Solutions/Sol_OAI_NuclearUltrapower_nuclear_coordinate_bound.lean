-- Prove2me | solution 1 for OAI.NuclearUltrapower.nuclear_coordinate_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T14:37:41.466235+00:00
-- url     : https://prove2.me/submissions/99e17088-af0b-434e-b876-f1f687a46476

import Mathlib
import Definitions.Def_NuclearUltrapower
import Definitions.Def_OAIQ019N043
import Theorems.Thm_OAI_NuclearUltrapower_VariableUltra_quotientRepresentation_weakly_mixing
import Theorems.Thm_OAI_NuclearUltrapower_unitary_complement_norm_of_energy

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_HilbertSchmidt
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instCompleteSpaceAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNontrivialAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.tensorHilbertNontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End

namespace NuclearUltrapower

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- All Hilbert--Schmidt operators are compact, without a separability assumption. -/
theorem hsOperator_compact (z : HilbertSchmidt K) : IsCompactOperator (hsOperator z) := by
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_setOfPred_isCompactOperator.preimage hsOperator.continuous
  | ih z =>
      rw [hsOperator_coe]
      induction z using OAI.tensorInductionOn with
      | tmul x f =>
          change IsCompactOperator (f.smulRight x)
          exact (isCompactOperator_of_locallyCompactSpace_dom f).clm_comp
            (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) x)
      | add z w hz hw =>
          rw [map_add]
          change IsCompactOperator (fun x => tensorOperator z x + tensorOperator w x)
          exact hz.add hw

variable {Γ : Type*} [Group Γ]

/-- The compact-operator obstruction used in the tensor-norm formulation.
This is the selfadjoint case; no dimension bound and no separability are used. -/
theorem compact_selfadjoint_commuting_eq_zero
    (σ : Γ →* (K ≃ₗᵢ[ℂ] K)) (hσ : HasNoFiniteDimensionalSubrep σ)
    (T : K →L[ℂ] K) (hT : IsCompactOperator T) (hsym : T.IsSymmetric)
    (hcomm : ∀ g x, T (σ g x) = σ g (T x)) : T = 0 := by
  apply (ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hT hsym).mp
  intro μ hμ
  by_contra hμ0
  have hfd := ContinuousLinearMap.finite_dimensional_eigenspace hT μ hμ0
  apply hσ (eigenspace T.toLinearMap μ) hμ ?_ hfd
  intro g x hx
  rw [mem_eigenspace_iff] at hx ⊢
  change T (σ g x) = μ • σ g x
  rw [hcomm, show T x = μ • x from hx, map_smul]

/-- Every compact operator in the commutant vanishes, not just selfadjoint ones.
This discharges the compact-operator part of lem:weak-mixing-bound. -/
theorem compact_commuting_eq_zero
    (σ : Γ →* (K ≃ₗᵢ[ℂ] K)) (hσ : HasNoFiniteDimensionalSubrep σ)
    (T : K →L[ℂ] K) (hT : IsCompactOperator T)
    (hcomm : ∀ g x, T (σ g x) = σ g (T x)) : T = 0 := by
  have hc (g : Γ) : Commute T (σ g : K →L[ℂ] K) := by
    ext x
    exact hcomm g x
  have hcs (g : Γ) : Commute (star T) (σ g : K →L[ℂ] K) := by
    have h := (hc g⁻¹).star_star
    have he : (σ g⁻¹ : K →L[ℂ] K) = star (σ g : K →L[ℂ] K) := by
      simp only [map_inv, LinearIsometryEquiv.star_eq_symm, LinearIsometryEquiv.inv_def]
    simpa only [he, star_star] using h
  have hz : star T * T = 0 := by
    apply compact_selfadjoint_commuting_eq_zero σ hσ (star T * T)
      (hT.clm_comp (star T)) (IsSelfAdjoint.star_mul_self T).isSymmetric
    intro g x
    exact congrArg (fun f : K →L[ℂ] K => f x) ((hcs g).mul_left (hc g)).eq
  apply norm_eq_zero.mp
  have hn : ‖T‖ * ‖T‖ = 0 := by
    rw [← CStarRing.norm_star_mul_self, hz, norm_zero]
  exact mul_self_eq_zero.mp hn

/-- Weak mixing excludes every invariant Hilbert--Schmidt vector, with no
separability assumption. This is the invariant-vector step of the source bound. -/
theorem hsRepresentation_no_invariants (σ : Γ →* (K ≃ₗᵢ[ℂ] K))
    (hσ : HasNoFiniteDimensionalSubrep σ) (z : HilbertSchmidt K)
    (hz : ∀ g, hsRepresentation σ g z = z) : z = 0 := by
  apply hsOperator_injective
  rw [map_zero]
  apply compact_commuting_eq_zero σ hσ _ (hsOperator_compact z)
  intro g x
  have hc := congrArg (fun z : HilbertSchmidt K => hsOperator z (σ g x)) (hz g)
  change hsOperator (hsConjugation (σ g) z) (σ g x) = hsOperator z (σ g x) at hc
  rw [hsOperator_conjugation] at hc
  simpa using hc.symm

end NuclearUltrapower

noncomputable section
open scoped CStarAlgebra

namespace NuclearUltrapower

variable {A : Type*} [CStarAlgebra A] [PartialOrder A]

namespace PositiveTrace

variable [StarOrderedRing A]

/-- Positivity of the trace pairing does not require the factors to commute. -/
theorem mul_nonneg (τ : PositiveTrace A) {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ τ (a * b) := by
  have hs : IsSelfAdjoint (CFC.sqrt a) := (CFC.sqrt_nonneg a).isSelfAdjoint
  have hp : 0 ≤ CFC.sqrt a * b * CFC.sqrt a := by
    exact hs.conjugate_nonneg hb
  have he : τ (a * b) = τ (CFC.sqrt a * b * CFC.sqrt a) := by
    calc
      τ (a * b) = τ ((CFC.sqrt a * CFC.sqrt a) * b) := by
        rw [CFC.sqrt_mul_sqrt_self a ha]
      _ = τ (CFC.sqrt a * (CFC.sqrt a * b)) := by rw [mul_assoc]
      _ = τ ((CFC.sqrt a * b) * CFC.sqrt a) := τ.cyclic _ _
  rw [he]
  exact τ.nonneg _ hp

/-- Pairing a selfadjoint contraction with an element is bounded by its trace
absolute value. This is the elementary dual trace-norm estimate needed below. -/
theorem contraction_pair_le_abs (τ : PositiveTrace A) {j d : A}
    (hjlo : -1 ≤ j) (hjhi : j ≤ 1) (hd : IsSelfAdjoint d) :
    τ (j * d) ≤ τ (CFC.abs d) := by
  have h₁ := τ.mul_nonneg (sub_nonneg.mpr hjhi) (CFC.posPart_nonneg d)
  have h₂ := τ.mul_nonneg (neg_le_iff_add_nonneg.mp hjlo) (CFC.negPart_nonneg d)
  rw [sub_mul, one_mul, map_sub] at h₁
  rw [add_mul, one_mul, map_add] at h₂
  calc
    τ (j * d) = τ (j * (posPart d - negPart d)) := by
      rw [CFC.posPart_sub_negPart d hd]
    _ = τ (j * posPart d) - τ (j * negPart d) := by rw [mul_sub, map_sub]
    _ ≤ τ (posPart d) + τ (negPart d) := by linarith
    _ = τ (CFC.abs d) := by rw [← map_add, CFC.posPart_add_negPart d hd]

/-- The lower estimate in the Powers--Størmer argument. -/
theorem square_sub_le_abs_pair (τ : PositiveTrace A) {x y : A}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    τ ((x - y) * (x - y)) ≤ τ (CFC.abs (x - y) * (x + y)) := by
  let f := x - y
  have hf : IsSelfAdjoint f := hx.isSelfAdjoint.sub hy.isSelfAdjoint
  have h₁ := τ.mul_nonneg (CFC.posPart_nonneg f)
    (show 0 ≤ x + y - f by dsimp [f]; convert add_nonneg hy hy using 1; abel)
  have h₂ := τ.mul_nonneg (CFC.negPart_nonneg f)
    (show 0 ≤ x + y + f by dsimp [f]; convert add_nonneg hx hx using 1; abel)
  rw [mul_sub, map_sub] at h₁
  rw [mul_add, map_add] at h₂
  calc
    τ (f * f) = τ ((posPart f - negPart f) * f) := by
      rw [CFC.posPart_sub_negPart f hf]
    _ = τ (posPart f * f) - τ (negPart f * f) := by rw [sub_mul, map_sub]
    _ ≤ τ (posPart f * (x + y)) + τ (negPart f * (x + y)) := by linarith
    _ = τ (CFC.abs f * (x + y)) := by
      rw [← map_add, ← add_mul, CFC.posPart_add_negPart f hf]

/-- The finite-spectrum sign of a selfadjoint element. -/
theorem exists_sign_of_finite_spectrum {f : A} (hf : IsSelfAdjoint f)
    (hs : (spectrum ℝ f).Finite) :
    ∃ j : A, -1 ≤ j ∧ j ≤ 1 ∧ j * f = CFC.abs f ∧ f * j = CFC.abs f ∧ ‖j‖ ≤ 1 := by
  have hc : ContinuousOn Real.sign (spectrum ℝ f) := hs.continuousOn _
  refine ⟨cfc Real.sign f, ?_, ?_, ?_, ?_, ?_⟩
  · have h : cfc (fun _ : ℝ => -1) f ≤ cfc Real.sign f := by
      apply (cfc_le_iff _ _ _ continuous_const.continuousOn hc hf).mpr
      intro r hr
      rcases Real.sign_apply_eq r with h | h | h <;> rw [h] <;> norm_num
    simpa [cfc_const _ _ hf] using h
  · have h : cfc Real.sign f ≤ cfc (fun _ : ℝ => 1) f := by
      apply (cfc_le_iff _ _ _ hc continuous_const.continuousOn hf).mpr
      intro r hr
      rcases Real.sign_apply_eq r with h | h | h <;> rw [h] <;> norm_num
    simpa [cfc_const _ _ hf] using h
  · conv_lhs => arg 2; rw [← cfc_id ℝ f hf]
    rw [← cfc_mul Real.sign id f hc continuous_id.continuousOn,
      CFC.abs_eq_cfc_norm f hf]
    apply cfc_congr
    intro r hr
    obtain hn | rfl | hp := lt_trichotomy r 0
    · simp [Real.sign_of_neg hn, Real.norm_eq_abs, abs_of_neg hn]
    · simp
    · simp [Real.sign_of_pos hp, Real.norm_eq_abs, abs_of_pos hp]
  · conv_lhs => arg 1; rw [← cfc_id ℝ f hf]
    rw [← cfc_mul id Real.sign f continuous_id.continuousOn hc,
      CFC.abs_eq_cfc_norm f hf]
    apply cfc_congr
    intro r hr
    obtain hn | rfl | hp := lt_trichotomy r 0
    · simp [Real.sign_of_neg hn, Real.norm_eq_abs, abs_of_neg hn]
    · simp
    · simp [Real.sign_of_pos hp, Real.norm_eq_abs, abs_of_pos hp]

  · apply norm_cfc_le zero_le_one
    intro r hr
    rcases Real.sign_apply_eq r with h | h | h <;> rw [h] <;> norm_num

/-- Powers--Størmer for a finite positive trace and a finite-spectrum difference.
This is the finite-rank analytic core, not yet the Hilbert--Schmidt theorem. -/
theorem powers_stormer_finite_spectrum (τ : PositiveTrace A) {x y : A}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hfinite : (spectrum ℝ (x - y)).Finite) :
    τ ((x - y) * (x - y)) ≤ τ (CFC.abs (x * x - y * y)) := by
  have hf : IsSelfAdjoint (x - y) := hx.isSelfAdjoint.sub hy.isSelfAdjoint
  obtain ⟨j, hjlo, hjhi, hjf, hfj, _hnj⟩ := exists_sign_of_finite_spectrum hf hfinite
  have hd : IsSelfAdjoint (x * x - y * y) := by
    change star (x * x - y * y) = x * x - y * y
    simp only [star_sub, star_mul, hx.isSelfAdjoint.star_eq, hy.isSelfAdjoint.star_eq]
  have he : τ (j * (x * x - y * y)) = τ (CFC.abs (x - y) * (x + y)) := by
    have hd' : x * x - y * y = (x - y) * x + y * (x - y) := by noncomm_ring
    rw [hd', mul_add, map_add]
    have hcy : τ (j * (y * (x - y))) = τ (CFC.abs (x - y) * y) := by
      rw [← mul_assoc, τ.cyclic (j * y) (x - y), ← mul_assoc, hfj]
    rw [hcy, ← mul_assoc j (x - y) x, hjf, ← map_add, ← mul_add]
  exact (τ.square_sub_le_abs_pair hx hy).trans
    (he ▸ τ.contraction_pair_le_abs hjlo hjhi hd)

end PositiveTrace
end NuclearUltrapower

namespace NuclearUltrapower
open scoped TensorProduct InnerProductSpace ComplexOrder
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- Finite-dimensional operator spectra are finite also as real spectra. -/
theorem operator_finite_real_spectrum [FiniteDimensional ℂ K] (T : K →L[ℂ] K) :
    (spectrum ℝ T).Finite := by
  let e : (K →ₗ[ℂ] K) ≃ₐ[ℂ] (K →L[ℂ] K) :=
    { LinearMap.toContinuousLinearMap with
      map_mul' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  rw [← spectrum.preimage_algebraMap ℂ, ← AlgEquiv.spectrum_eq e.symm T]
  exact (Module.End.finite_spectrum T.toLinearMap).preimage
    (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Elementary vector-state estimate, valid without separability or completeness. -/
theorem vectorState_difference_le (A : H →L[ℂ] H) (hA : ‖A‖ ≤ 1) (x y : H) :
    (⟪x, A x⟫_ℂ - ⟪y, A y⟫_ℂ).re ≤ (‖x‖ + ‖y‖) * ‖x - y‖ := by
  have he : ⟪x, A x⟫_ℂ - ⟪y, A y⟫_ℂ =
      ⟪x - y, A x⟫_ℂ + ⟪y, A (x - y)⟫_ℂ := by
    simp only [map_sub, inner_sub_left, inner_sub_right]
    ring
  have hx : ‖A x‖ ≤ ‖x‖ := by
    exact (A.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) hA)
  have hy : ‖A (x - y)‖ ≤ ‖x - y‖ := by
    exact (A.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hA)
  rw [he, Complex.add_re]
  calc
    (⟪x - y, A x⟫_ℂ).re + (⟪y, A (x - y)⟫_ℂ).re ≤
        ‖⟪x - y, A x⟫_ℂ‖ + ‖⟪y, A (x - y)⟫_ℂ‖ :=
      add_le_add (Complex.re_le_norm _) (Complex.re_le_norm _)
    _ ≤ ‖x - y‖ * ‖A x‖ + ‖y‖ * ‖A (x - y)‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖x - y‖ * ‖x‖ + ‖y‖ * ‖x - y‖ :=
      add_le_add (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hy (norm_nonneg _))
    _ = (‖x‖ + ‖y‖) * ‖x - y‖ := by ring

/-- The trace-norm estimate for reduced density matrices. -/
theorem trace_abs_reducedDensity_sub_le [FiniteDimensional ℂ K] (z w : E ⊗[ℂ] K) :
    (LinearMap.trace ℂ K (CFC.abs (reducedDensity z - reducedDensity w)).toLinearMap).re ≤
      (‖z‖ + ‖w‖) * ‖z - w‖ := by
  obtain ⟨j, _hlo, _hhi, hj, _hj', hnj⟩ := PositiveTrace.exists_sign_of_finite_spectrum
    ((reducedDensity_nonneg z).isSelfAdjoint.sub (reducedDensity_nonneg w).isSelfAdjoint)
    (operator_finite_real_spectrum _)
  rw [← hj, mul_sub, ContinuousLinearMap.toLinearMap_sub, map_sub,
    trace_reducedDensity, trace_reducedDensity]
  apply vectorState_difference_le
  calc
    ‖TensorProduct.mapL (ContinuousLinearMap.id ℂ E) j‖ ≤
        ‖ContinuousLinearMap.id ℂ E‖ * ‖j‖ := TensorProduct.norm_mapL_le _ _
    _ ≤ 1 * 1 := mul_le_mul ContinuousLinearMap.norm_id_le hnj (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

/-- Finite-dimensional Powers--Størmer in the Hilbert tensor norm. -/
theorem finite_density_root_difference [FiniteDimensional ℂ K] (z w : E ⊗[ℂ] K) :
    ‖finiteOperatorTensor (CFC.sqrt (reducedDensity z)) -
      finiteOperatorTensor (CFC.sqrt (reducedDensity w))‖ ^ 2 ≤
      (‖z‖ + ‖w‖) * ‖z - w‖ := by
  rw [← finiteOperatorTensor_sub, finiteOperatorTensor_norm_sq]
  have hs : star (CFC.sqrt (reducedDensity z) - CFC.sqrt (reducedDensity w)) =
      CFC.sqrt (reducedDensity z) - CFC.sqrt (reducedDensity w) :=
    ((CFC.sqrt_nonneg _).isSelfAdjoint.sub (CFC.sqrt_nonneg _).isSelfAdjoint).star_eq
  rw [hs]
  have h := (operatorPositiveTrace (K := K)).powers_stormer_finite_spectrum
    (CFC.sqrt_nonneg (reducedDensity z)) (CFC.sqrt_nonneg (reducedDensity w))
    (operator_finite_real_spectrum _)
  rw [CFC.sqrt_mul_sqrt_self _ (reducedDensity_nonneg z),
    CFC.sqrt_mul_sqrt_self _ (reducedDensity_nonneg w)] at h
  exact h.trans (trace_abs_reducedDensity_sub_le z w)

/-- Uniqueness makes the finite-support construction independent of all choices. -/
theorem densityRoot_mapIsometry [FiniteDimensional ℂ F]
    (g : E →ₗᵢ[ℂ] E') (f : F →ₗᵢ[ℂ] K) (z : E ⊗[ℂ] F) :
    densityRoot (TensorProduct.mapIsometry g f z) =
      (liftOperatorTensor f (CFC.sqrt (reducedDensity z)) : HilbertSchmidt K) := by
  apply hsOperator_injective
  rw [hsOperator_densityRoot, hsOperator_coe, tensorOperator_liftOperatorTensor,
    reducedDensity_mapIsometry]
  exact (operatorLift_sqrt f (reducedDensity_nonneg z)).symm

/-- The reduced-root estimate holds in arbitrary ambient Hilbert spaces.
Both vectors are compared inside one finite-dimensional support, not separately. -/
theorem densityRoot_difference (z w : E ⊗[ℂ] K) :
    ‖densityRoot z - densityRoot w‖ ^ 2 ≤ (‖z‖ + ‖w‖) * ‖z - w‖ := by
  obtain ⟨F, hF, hFzw⟩ := TensorProduct.exists_finite_submodule_right_of_setFinite
    ({z, w} : Set (E ⊗[ℂ] K)) (Set.toFinite _)
  let : FiniteDimensional ℂ F := hF
  obtain ⟨z', hz⟩ := hFzw (by simp : z ∈ ({z, w} : Set (E ⊗[ℂ] K)))
  obtain ⟨w', hw⟩ := hFzw (by simp : w ∈ ({z, w} : Set (E ⊗[ℂ] K)))
  let f := TensorProduct.mapIsometry (LinearIsometry.id : E →ₗᵢ[ℂ] E) F.subtypeₗᵢ
  have hz' : f z' = z := hz
  have hw' : f w' = w := hw
  rw [← hz', ← hw', densityRoot_mapIsometry, densityRoot_mapIsometry,
    ← UniformSpace.Completion.coe_sub, UniformSpace.Completion.norm_coe,
    ← liftOperatorTensor_sub, liftOperatorTensor_norm, finiteOperatorTensor_sub,
    ← map_sub, f.norm_map, f.norm_map, f.norm_map]
  exact finite_density_root_difference z' w'

/-- Unitary covariance of reduced densities, realized in actual HS space. -/
theorem densityRoot_unitary (u : E ≃ₗᵢ[ℂ] E) (v : K ≃ₗᵢ[ℂ] K) (z : E ⊗[ℂ] K) :
    densityRoot (TensorProduct.congrIsometry u v z) = hsConjugation v (densityRoot z) := by
  apply hsOperator_injective
  rw [hsOperator_densityRoot, hsOperator_conjugation, hsOperator_densityRoot]
  change CFC.sqrt (reducedDensity (TensorProduct.mapIsometry u.toLinearIsometry
    v.toLinearIsometry z)) = _
  rw [reducedDensity_mapIsometry, ← operatorLift_sqrt _ (reducedDensity_nonneg z)]
  change ((v : K →L[ℂ] K) ∘L CFC.sqrt (reducedDensity z)) ∘L
    (v : K →L[ℂ] K).adjoint = _
  rw [v.adjoint_eq_symm]
  rfl

/-- The exact factor two in the Powers--Størmer inequality. -/
theorem densityRoot_unitary_difference (u : E ≃ₗᵢ[ℂ] E) (v : K ≃ₗᵢ[ℂ] K)
    (z : E ⊗[ℂ] K) :
    ‖hsConjugation v (densityRoot z) - densityRoot z‖ ^ 2 ≤
      (2 * ‖z‖) * ‖TensorProduct.congrIsometry u v z - z‖ := by
  rw [← densityRoot_unitary u v z]
  simpa only [(TensorProduct.congrIsometry u v).norm_map, ← two_mul] using
    densityRoot_difference (TensorProduct.congrIsometry u v z) z

/-- The full weak-mixing estimate on the dense algebraic tensor product. -/
theorem weak_mixing_bound_algebraic {Γ : Type u} [Group Γ]
    (S : Finset Γ) (κ : ℝ) (hS : S.Nonempty) (hκ : 0 < κ)
    (hgap : HasKazhdanGap.{u, v} S κ)
    {K : Type v} {E : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (σ : Γ →* (K ≃ₗᵢ[ℂ] K)) (hσ : HasNoFiniteDimensionalSubrep σ)
    (U : Γ → (E ≃ₗᵢ[ℂ] E)) (z : E ⊗[ℂ] K) :
    κ ^ 2 / (4 * (S.card : ℝ)) * ‖z‖ ^ 2 ≤
      ∑ s ∈ S, ‖TensorProduct.congrIsometry (U s) (σ s) z - z‖ ^ 2 := by
  classical
  let δ : Γ → ℝ := fun s => ‖TensorProduct.congrIsometry (U s) (σ s) z - z‖
  have hδ s : 0 ≤ δ s := norm_nonneg _
  have hs : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hS.card_pos
  have hh := hgap (HilbertSchmidt K) (hsRepresentation σ)
    (hsRepresentation_no_invariants σ hσ) (densityRoot z)
  rw [densityRoot_norm] at hh
  have he : κ * ‖z‖ ^ 2 ≤ (2 * ‖z‖) * ∑ s ∈ S, δ s := by
    refine hh.trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    exact densityRoot_unitary_difference (U s) (σ s) z
  by_cases hz : z = 0
  · subst z
    simp
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hκn : κ * ‖z‖ ≤ 2 * ∑ s ∈ S, δ s := by
    apply (mul_le_mul_iff_right₀ hn).mp
    nlinarith [he]
  have hsq : (κ * ‖z‖) ^ 2 ≤ (2 * ∑ s ∈ S, δ s) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hκ.le hn.le) hκn 2
  have hcs := sq_sum_le_card_mul_sum_sq (s := S) (f := δ)
  change κ ^ 2 / (4 * (S.card : ℝ)) * ‖z‖ ^ 2 ≤ ∑ s ∈ S, δ s ^ 2
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (mul_pos (by norm_num) hs)).mpr
  nlinarith [hsq, hcs]

/-- Source lem:weak-mixing-bound, for arbitrary (possibly nonseparable)
Hilbert spaces and arbitrary unitaries U_s with no relations imposed. -/
theorem weak_mixing_bound {Γ : Type u} [Group Γ]
    (S : Finset Γ) (κ : ℝ) (hS : S.Nonempty) (hκ : 0 < κ)
    (hgap : HasKazhdanGap.{u, v} S κ)
    {K : Type v} {E : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (σ : Γ →* (K ≃ₗᵢ[ℂ] K)) (hσ : HasNoFiniteDimensionalSubrep σ)
    (U : Γ → (E ≃ₗᵢ[ℂ] E)) (ξ : HilbertTensor E K) :
    κ ^ 2 / (4 * (S.card : ℝ)) * ‖ξ‖ ^ 2 ≤
      ∑ s ∈ S, ‖tensorUnitaryAction (U s) (σ s) ξ - ξ‖ ^ 2 := by
  induction ξ using UniformSpace.Completion.induction_on with
  | hp =>
      apply isClosed_le
      · exact continuous_const.mul (continuous_norm.pow 2)
      · exact continuous_finsetSum S (fun s _ =>
          (((tensorUnitaryAction (U s) (σ s)).continuous.sub continuous_id).norm.pow 2))
  | ih z =>
      simp only [tensorUnitaryAction_coe, ← UniformSpace.Completion.coe_sub,
        UniformSpace.Completion.norm_coe]
      exact weak_mixing_bound_algebraic S κ hS hκ hgap σ hσ U z

end NuclearUltrapower

end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_HilbertTensor
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner _root_.OAI.NuclearUltrapower.tensorHilbertNontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End
noncomputable section
open scoped CStarAlgebra
noncomputable section
open Filter
open scoped Topology ENNReal
noncomputable section
open scoped InnerProductSpace
noncomputable section
open scoped TensorProduct InnerProductSpace
namespace NuclearUltrapower

section TensorOperators
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable [CompleteSpace E] [CompleteSpace F]

theorem tensorLeftRight_commute (U : E →L[ℂ] E) (V : F →L[ℂ] F) :
    Commute (tensorLeftHom U) (tensorRightHom V) := by
  change completedTensorMap U 1 * completedTensorMap 1 V = completedTensorMap 1 V * completedTensorMap U 1
  simp only [← completedTensorMap_mul, mul_one, one_mul]
end TensorOperators
end NuclearUltrapower

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_TensorNorms
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instCompleteSpaceAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End
noncomputable section
open scoped CStarAlgebra
noncomputable section
open Filter
open scoped Topology ENNReal
noncomputable section
open scoped InnerProductSpace
noncomputable section
open scoped TensorProduct InnerProductSpace
noncomputable section
open scoped TensorProduct
namespace NuclearUltrapower

section NormTransfer

variable {B : Type u} {C : Type v} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

local instance spatialTensorBoundedSMul_rdd0ec1_1 (H K : ComplexHilbert.{w}) :
    IsBoundedSMul ℂ (H ⊗[ℂ] K) := NormedSpace.toIsBoundedSMul
/-- Uniform finite projective bound on all spatial and commuting evaluations.
In particular the real suprema defining the tensor norms are genuine bounds. -/
theorem evals_bounded (x : B ⊗[ℂ] C) :
    ∃ M : ℝ, (∀ (H K : ComplexHilbert.{w})
      (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (σ : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)),
      ‖spatialEval H K ρ σ x‖ ≤ M) ∧
      (∀ (H : ComplexHilbert.{w}) (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H))
      (σ : C →⋆ₙₐ[ℂ] (H →L[ℂ] H)), ‖commutingEval H ρ σ x‖ ≤ M) := by
  induction x using OAI.tensorInductionOn with
  | tmul b c =>
    refine ⟨‖b‖ * ‖c‖, ?_, ?_⟩
    · intro H K ρ σ
      exact (TensorProduct.norm_mapL_le _ _).trans
        (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le ρ b)
          (NonUnitalStarAlgHom.norm_apply_le σ c) (norm_nonneg _) (norm_nonneg _))
    · intro H ρ σ
      exact (norm_mul_le _ _).trans
        (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le ρ b)
          (NonUnitalStarAlgHom.norm_apply_le σ c) (norm_nonneg _) (norm_nonneg _))
  | add x y hx hy =>
    obtain ⟨M, hM, hM'⟩ := hx
    obtain ⟨N, hN, hN'⟩ := hy
    refine ⟨M + N, ?_, ?_⟩
    · intro H K ρ σ
      rw [map_add]
      exact (norm_add_le (spatialEval H K ρ σ x) (spatialEval H K ρ σ y)).trans
        (add_le_add (hM H K ρ σ) (hN H K ρ σ))
    · intro H ρ σ
      rw [map_add]
      exact (norm_add_le _ _).trans (add_le_add (hM' H ρ σ) (hN' H ρ σ))

theorem norm_commutingEval_le (x : B ⊗[ℂ] C) (H : ComplexHilbert.{w})
    (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (σ : C →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hcomm : ∀ b c, Commute (ρ b) (σ c)) :
    ‖commutingEval H ρ σ x‖ ≤ maxTensorNorm.{u,v,w} x := by
  obtain ⟨M, _, hM⟩ := evals_bounded.{u,v,w} x
  unfold maxTensorNorm
  apply le_csSup
  · refine ⟨M, ?_⟩
    rintro _ ⟨H, ρ, σ, _, rfl⟩
    exact hM H ρ σ
  · exact ⟨H, ρ, σ, hcomm, rfl⟩

/-- Nuclearity precisely transfers a bound in every spatial realization to
every commuting realization. This is the sole tensor-norm step in the source
nuclear-finiteness proof, with no identification with coordinate quotients. -/
theorem nuclear_transfer_norm (hB : IsNuclear.{u,v} B) (x : B ⊗[ℂ] C) (M : ℝ)
    (hM : ∀ (H K : ComplexHilbert.{max u v})
      (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (σ : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)),
        ‖spatialEval H K ρ σ x‖ ≤ M)
    (H : ComplexHilbert.{max u v}) (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (σ : C →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hcomm : ∀ b c, Commute (ρ b) (σ c)) :
    ‖commutingEval H ρ σ x‖ ≤ M := by
  apply (norm_commutingEval_le x H ρ σ hcomm).trans
  rw [← hB C x]
  apply csSup_le
  · exact ⟨‖spatialEval H H ρ σ x‖, H, H, ρ, σ, rfl⟩
  · rintro _ ⟨H, K, ρ, σ, rfl⟩
    exact hM H K ρ σ

end NormTransfer
end NuclearUltrapower

noncomputable section
open scoped InnerProductSpace TensorProduct
namespace NuclearUltrapower

section Support
variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The original representation is its unital support plus a zero representation. -/
theorem representation_support_factor (φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    φ a = (representationSupport φ).subtypeL.comp ((supportRepresentation φ a).comp
      (supportProjection φ)) := by
  ext x
  change φ a x = (φ a * φ 1) x
  rw [← map_mul, mul_one]

/-- Orthogonal projection has norm at most one, including the zero support. -/
theorem supportProjection_norm_le (φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    ‖supportProjection φ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖φ 1 x‖ ≤ 1 * ‖x‖
  have h1 : ‖(1 : A)‖ ≤ 1 := by
    nontriviality A
    simp
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right ((NonUnitalStarAlgHom.norm_apply_le φ (1 : A)).trans h1) (norm_nonneg x))

end Support
end NuclearUltrapower

namespace NuclearUltrapower
open scoped TensorProduct

section SpatialSupport
variable {B : Type u} {C : Type v} [CStarAlgebra B] [CStarAlgebra C]

local instance tensorSupportBoundedSMul_rdd0ec1_1 (H K : ComplexHilbert.{w}) :
    IsBoundedSMul ℂ (H ⊗[ℂ] K) := NormedSpace.toIsBoundedSMul
/-- Degenerate spatial representations factor through their two unital supports. -/
theorem spatialEval_support_factor (x : B ⊗[ℂ] C) (H K : ComplexHilbert.{w})
    (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (σ : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    spatialEval H K ρ σ x =
      (TensorProduct.mapL (representationSupport ρ).subtypeL (representationSupport σ).subtypeL).comp
        ((spatialEval (supportHilbert H ρ) (supportHilbert K σ)
          (supportRepresentation ρ).toNonUnitalStarAlgHom
          (supportRepresentation σ).toNonUnitalStarAlgHom x).comp
            (TensorProduct.mapL (supportProjection ρ) (supportProjection σ))) := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, ContinuousLinearMap.add_comp,
      ContinuousLinearMap.comp_add]
  | tmul b c =>
      change TensorProduct.mapL (ρ b) (σ c) =
        (TensorProduct.mapL (representationSupport ρ).subtypeL (representationSupport σ).subtypeL).comp
          ((TensorProduct.mapL (supportRepresentation ρ b) (supportRepresentation σ c)).comp
            (TensorProduct.mapL (supportProjection ρ) (supportProjection σ)))
      rw [← TensorProduct.mapL_comp, ← TensorProduct.mapL_comp]
      rw [← representation_support_factor, ← representation_support_factor]

/-- No unitality was hidden in the minimal tensor norm quantifier. -/
theorem spatialEval_norm_le_support (x : B ⊗[ℂ] C) (H K : ComplexHilbert.{w})
    (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (σ : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    ‖spatialEval H K ρ σ x‖ ≤
      ‖spatialEval (supportHilbert H ρ) (supportHilbert K σ)
        (supportRepresentation ρ).toNonUnitalStarAlgHom
        (supportRepresentation σ).toNonUnitalStarAlgHom x‖ := by
  have hI : ‖TensorProduct.mapL (representationSupport ρ).subtypeL
      (representationSupport σ).subtypeL‖ ≤ 1 := by
    apply (TensorProduct.norm_mapL_le _ _).trans
    have hρ := (representationSupport ρ).subtypeₗᵢ.norm_toContinuousLinearMap_le
    have hσ := (representationSupport σ).subtypeₗᵢ.norm_toContinuousLinearMap_le
    simpa only [Submodule.subtypeₗᵢ_toContinuousLinearMap, one_mul] using
      mul_le_mul hρ hσ (norm_nonneg _) zero_le_one
  have hP : ‖TensorProduct.mapL (supportProjection ρ) (supportProjection σ)‖ ≤ 1 := by
    apply (TensorProduct.norm_mapL_le _ _).trans
    simpa only [one_mul] using mul_le_mul (supportProjection_norm_le ρ)
      (supportProjection_norm_le σ) (norm_nonneg (supportProjection σ)) zero_le_one
  rw [spatialEval_support_factor]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply (mul_le_mul hI (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) zero_le_one).trans
  simpa only [one_mul, mul_one] using
    mul_le_mul_of_nonneg_left hP (norm_nonneg
      (spatialEval (supportHilbert H ρ) (supportHilbert K σ)
        (supportRepresentation ρ).toNonUnitalStarAlgHom
        (supportRepresentation σ).toNonUnitalStarAlgHom x))

/-- It suffices to bound all unital spatial realizations, not to assume away the others. -/
theorem spatial_bound_of_unital (x : B ⊗[ℂ] C) (M : ℝ)
    (h : ∀ (H K : ComplexHilbert.{w}) (ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
      (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)),
      ‖spatialEval H K ρ.toNonUnitalStarAlgHom σ.toNonUnitalStarAlgHom x‖ ≤ M)
    (H K : ComplexHilbert.{w}) (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (σ : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) : ‖spatialEval H K ρ σ x‖ ≤ M := by
  apply le_trans (spatialEval_norm_le_support x H K ρ σ)
  exact h (supportHilbert H ρ) (supportHilbert K σ)
    (supportRepresentation ρ) (supportRepresentation σ)

end SpatialSupport
end NuclearUltrapower

end
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
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SpatialGap
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instCompleteSpaceAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNontrivialAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.tensorHilbertNontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End
noncomputable section
open scoped CStarAlgebra
noncomputable section
open Filter
open scoped Topology ENNReal
noncomputable section
open scoped InnerProductSpace
noncomputable section
open scoped TensorProduct InnerProductSpace
noncomputable section
open scoped TensorProduct
noncomputable section
open scoped InnerProductSpace TensorProduct
namespace NuclearUltrapower
open scoped TensorProduct InnerProductSpace ComplexOrder

section ComplementPolynomial
variable {Γ A : Type*} [CStarAlgebra A]

/-- Polynomial form of the complemented Laplacian, retaining arbitrary unitary tuples. -/
theorem laplacian_complement_expand (S : Finset Γ) (u : Γ → unitary A) :
    (4 * (S.card : ℝ)) • (1 : A) - laplacian S (fun s => (u s : A)) =
      (2 * (S.card : ℝ)) • (1 : A) + ∑ s ∈ S, ((u s : A) + star (u s : A)) := by
  have hs (s : Γ) : star ((u s : A) - 1) * ((u s : A) - 1) =
      (2 : ℝ) • (1 : A) - ((u s : A) + star (u s : A)) := by
    simp only [star_sub, star_one, sub_mul, mul_sub, one_mul, mul_one,
      Unitary.coe_star_mul_self]
    module
  simp only [laplacian, hs, Finset.sum_sub_distrib, Finset.sum_const,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  module
private theorem laplacian_complement_expand_complex (indices : Finset Γ)
    (unitaries : Γ → unitary A) :
    (4 * (indices.card : ℂ)) • (1 : A) - laplacian indices (fun index => (unitaries index : A)) =
      (2 * (indices.card : ℂ)) • (1 : A) +
        ∑ index ∈ indices, ((unitaries index : A) + star (unitaries index : A)) := by
  have expansion := laplacian_complement_expand indices unitaries
  have real_smul (scalar : ℝ) (value : A) : (scalar : ℂ) • value = scalar • value :=
    IsScalarTower.algebraMap_smul ℂ scalar value
  rw [← real_smul (4 * indices.card) 1, ← real_smul (2 * indices.card) 1] at expansion
  push_cast at expansion
  exact expansion

end ComplementPolynomial

section TensorComplement
variable {Γ B C : Type*} [CStarAlgebra B] [CStarAlgebra C]

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Spatial evaluation followed by completion is the complemented unitary Laplacian. -/
theorem spatial_complement (S : Finset Γ) (u : Γ → unitary B) (q : Γ → unitary C)
    (H K : ComplexHilbert) (ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    (spatialEval H K ρ.toNonUnitalStarAlgHom σ.toNonUnitalStarAlgHom (tensorComplement S u q)).completion =
      (4 * (S.card : ℂ)) • (1 : TensorHilbert H K →L[ℂ] TensorHilbert H K) -
        laplacian S (fun s => completedTensorMap (ρ (u s)) (σ (q s))) := by
  classical
  let U : Γ → unitary (TensorHilbert H K →L[ℂ] TensorHilbert H K) :=
    spatialUnitaryTuple (B := B) (C := C) H K ρ σ u q
  have he := laplacian_complement_expand_complex
    (A := TensorHilbert H K →L[ℂ] TensorHilbert H K) S U
  change (4 * (S.card : ℂ)) • (1 : TensorHilbert H K →L[ℂ] TensorHilbert H K) -
      laplacian S (fun s => completedTensorMap (ρ (u s)) (σ (q s))) = _ at he
  rw [he]
  simp only [tensorComplement, map_add, map_smul, map_sum, spatialEval_tmul,
    StarAlgHom.coe_toNonUnitalStarAlgHom, map_one, map_star, completed_add, completed_smul]
  rw [tensorMap_one, completed_one]
  have hsum (f : Γ → (H ⊗[ℂ] K →L[ℂ] H ⊗[ℂ] K)) :
      (∑ s ∈ S, f s).completion = ∑ s ∈ S, (f s).completion := by
    clear he
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih => simp only [Finset.sum_insert ha, completed_add, ih]
  rw [hsum]
  simp only [completed_add, U, spatialUnitaryTuple, pairedTensorUnitary_coe]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  change completedTensorMap (ρ (u s)) (σ (q s)) +
      completedTensorMap (star (ρ (u s))) (star (σ (q s))) = _
  rw [completedTensorMap_star]
  rfl
end TensorComplement

section SpatialGap
variable {Γ : Type u} [Group Γ] {B C : Type v} [CStarAlgebra B] [CStarAlgebra C]

/-- The spatial estimate is abstracted from the quotient to keep inference local. -/
theorem spatial_complement_bound_unital (q : Γ →* unitary C)
    (S : Finset Γ) (κ : ℝ) (hS : S.Nonempty) (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
    (hgap : HasKazhdanGap.{u,v} S κ)
    (hwm : ∀ (K : ComplexHilbert.{v}) (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)),
      HasNoFiniteDimensionalSubrep (tupleRepresentation q K σ))
    (u : Γ → unitary B)
    (H K : ComplexHilbert.{v}) (ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    ‖spatialEval H K ρ.toNonUnitalStarAlgHom σ.toNonUnitalStarAlgHom (tensorComplement S u q)‖ ≤
      4 * (S.card : ℝ) - κ ^ 2 / (4 * (S.card : ℝ)) := by
  let σg := tupleRepresentation q K σ
  have hσg := hwm K σ
  let Ut : Γ → unitary (TensorHilbert H K →L[ℂ] TensorHilbert H K) := fun g =>
    pairedTensorUnitary (Unitary.map (StarMonoidHom.ofClass ρ) (u g))
      (Unitary.map (StarMonoidHom.ofClass σ) (q g))
  have hb : κ ^ 2 / (4 * (S.card : ℝ)) ≤ 4 * (S.card : ℝ) := by
    have hcard : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
    apply (div_le_iff₀ (by positivity : 0 < 4 * (S.card : ℝ))).mpr
    nlinarith
  have he (ξ : TensorHilbert H K) : κ ^ 2 / (4 * (S.card : ℝ)) * ‖ξ‖ ^ 2 ≤
      ∑ s ∈ S, ‖(Ut s : TensorHilbert H K →L[ℂ] TensorHilbert H K) ξ - ξ‖ ^ 2 := by
    have hx := weak_mixing_bound S κ hS hκ0 hgap σg hσg
      (fun g => Unitary.linearIsometryEquiv (Unitary.map (StarMonoidHom.ofClass ρ) (u g))) ξ
    simpa only [Ut, pairedTensorUnitary_action, σg, tupleRepresentation_apply] using hx
  rw [← completed_norm, spatial_complement]
  exact unitary_complement_norm_of_energy S Ut _ hb he
theorem spatial_complement_bound (q : Γ →* unitary C)
    (S : Finset Γ) (κ : ℝ) (hS : S.Nonempty) (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
    (hgap : HasKazhdanGap.{u,v} S κ)
    (hwm : ∀ (K : ComplexHilbert.{v}) (σ : C →⋆ₐ[ℂ] (K →L[ℂ] K)),
      HasNoFiniteDimensionalSubrep (tupleRepresentation q K σ))
    (u : Γ → unitary B)
    (H K : ComplexHilbert.{v}) (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (σ : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    ‖spatialEval H K ρ σ (tensorComplement S u q)‖ ≤
      4 * (S.card : ℝ) - κ ^ 2 / (4 * (S.card : ℝ)) := by
  exact spatial_bound_of_unital _ _
    (fun H K ρ σ => spatial_complement_bound_unital q S κ hS hκ0 hκ hgap hwm u H K ρ σ) H K ρ σ
end SpatialGap
end NuclearUltrapower

end
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
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_NuclearFiniteness
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
universe u v w
open Filter
open scoped Topology InnerProductSpace ENNReal TensorProduct
namespace NuclearUltrapower

namespace VariableUltra

section QuotientHilbert
variable {ι : Type u} {A : ι → Type v} {E : ι → Type w}
  [∀ i, CStarAlgebra (A i)] [∀ i, Nontrivial (A i)]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, CompleteSpace (E i)] [∀ i, Nontrivial (E i)]
  (ω : Ultrafilter ι) (f : ∀ i, A i →⋆ₐ[ℂ] (E i →L[ℂ] E i))

/-- Coordinatewise commutation survives the quotient and its Hilbert action. -/
theorem quotientHilbertRep_commute_left
    (x : Seq (fun i => E i →L[ℂ] E i)) (q : Algebra A ω)
    (h : ∀ i a, Commute (x i) (f i a)) :
    Commute (HilbertUltraproduct.unitalOperatorRep (E := E) ω x)
      (quotientHilbertRep ω f q) := by
  induction q using Quotient.inductionOn with | h q =>
    change Commute (HilbertUltraproduct.unitalOperatorRep (E := E) ω x)
      (HilbertUltraproduct.unitalOperatorRep (E := E) ω (sequenceHom f q))
    have hc : Commute x (sequenceHom f q) := by
      apply Subtype.ext
      funext i
      exact h i (q i)
    exact hc.map (HilbertUltraproduct.unitalOperatorRep (E := E) ω)
end QuotientHilbert
end VariableUltra

section TensorCoordinateMaps
variable {ι : Type u} {E : Type v} {F : ι → Type w}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]
  [∀ i, CompleteSpace (F i)] [∀ i, Nontrivial (F i)]
  {B : Type*} [CStarAlgebra B] (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E))
  (ω : Ultrafilter ι)

/-- The two factor representations commute after taking the Hilbert ultraproduct. -/
theorem tensorAlphaBeta_commute (b : B)
    (q : VariableUltra.Algebra (fun i => F i →L[ℂ] F i) ω) :
    Commute (tensorAlpha (F := F) ρ ω b) (tensorBeta (E := E) ω q) := by
  exact VariableUltra.quotientHilbertRep_commute_left ω
    (fun i => tensorRightHom (E := E) (F := F i)) (tensorLeftSequence ρ b) q
    (fun i a => tensorLeftRight_commute (ρ b) a)

end TensorCoordinateMaps
end NuclearUltrapower
end
end

section
noncomputable section
universe u v
open Filter
open scoped InnerProductSpace TensorProduct Topology ENNReal ComplexOrder
namespace NuclearUltrapower
section ComplementEvaluation
variable {Γ B C D A : Type*} [CStarAlgebra B] [CStarAlgebra C] [CStarAlgebra D]
  [CStarAlgebra A]

theorem complementEval_poly (H : ComplexHilbert) (α : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (β : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : Finset Γ) (u : Γ → unitary B)
    (v : Γ → unitary C) :
    commutingEval H α.toNonUnitalStarAlgHom β.toNonUnitalStarAlgHom (tensorComplement S u v) =
      complementPoly S (fun g => α (u g)) (fun g => β (v g)) := by
  simp only [tensorComplement, complementPoly, map_add, map_smul, map_sum,
    commutingEval_tmul, StarAlgHom.coe_toNonUnitalStarAlgHom, map_one, one_mul, map_star]
end ComplementEvaluation
section NuclearFiniteness
variable {Γ : Type u} [Group Γ] {B : Type v} [CStarAlgebra B]
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (π : ℕ → FiniteUnitaryRep.{u,v} Γ) (ω : Ultrafilter ℕ)

theorem map_coordinateComplement (S : Finset Γ) (u : Γ → unitary B) :
    finiteTensorAction (E := E) π ω (coordinateComplement ρ π S u) =
      complementPoly S (fun g => finiteTensorAlpha ρ π ω (u g))
        (fun g => finiteTensorBeta (E := E) π ω (finiteQuotientTuple π ω g)) := by
  exact map_complementPoly (finiteTensorAction (E := E) π ω) S
    (fun g => tensorLeftSequence (F := fun i => π i) ρ (u g)) (rightRepSequence (E := E) π)

/-- Commuting evaluation is the image of the actual bounded coordinate sequence. -/
theorem commuting_coordinateComplement (S : Finset Γ) (u : Γ → unitary B) :
    commutingEval (finiteTensorHilbert (E := E) π ω)
      (finiteTensorAlpha ρ π ω).toNonUnitalStarAlgHom
      (finiteTensorBeta (E := E) π ω).toNonUnitalStarAlgHom
      (tensorComplement S u (finiteQuotientTuple π ω)) =
        finiteTensorAction (E := E) π ω (coordinateComplement ρ π S u) := by
  rw [map_coordinateComplement]
  exact complementEval_poly (finiteTensorHilbert (E := E) π ω)
    (finiteTensorAlpha ρ π ω) (finiteTensorBeta (E := E) π ω) S u (finiteQuotientTuple π ω)

theorem nuclear_coordinate_bound_oai
    (hB : IsNuclear.{v,v} B) (S : Finset Γ) (κ : ℝ)
    (hS : S.Nonempty) (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
    (hgap : HasKazhdanGap.{u,v} S κ)
    (hω : ∀ i : ℕ, ({i} : Set ℕ) ∉ (ω : Filter ℕ))
    (hirr : ∀ i, (π i).Irreducible)
    (hne : Pairwise (fun i j => ¬ (π i).Equivalent (π j)))
    (u : Γ → unitary B) :
    ‖finiteTensorAction (E := E) π ω (coordinateComplement ρ π S u)‖ ≤
      4 * (S.card : ℝ) - κ ^ 2 / (4 * (S.card : ℝ)) := by
  let q := finiteQuotientTuple π ω
  have hwm (K : ComplexHilbert.{v})
      (σ : VariableUltra.operatorQuotient (fun i => π i) ω →⋆ₐ[ℂ] (K →L[ℂ] K)) :
      HasNoFiniteDimensionalSubrep (tupleRepresentation q K σ) := by
    exact VariableUltra.quotientRepresentation_weakly_mixing π ω hω hirr hne S κ hκ0 hκ hgap σ
  let H := finiteTensorHilbert (E := E) π ω
  have hb := nuclear_transfer_norm hB (tensorComplement S u q)
    (4 * (S.card : ℝ) - κ ^ 2 / (4 * (S.card : ℝ)))
    (fun H K a b => spatial_complement_bound q S κ hS hκ0 hκ hgap hwm u H K a b)
    H (finiteTensorAlpha ρ π ω).toNonUnitalStarAlgHom
      (finiteTensorBeta (E := E) π ω).toNonUnitalStarAlgHom
    (fun b c => tensorAlphaBeta_commute ρ ω b c)
  rw [commuting_coordinateComplement] at hb
  exact hb

end NuclearFiniteness
end NuclearUltrapower
end
end

end OAI
end

theorem solution.{u, v} : type_of% @OAI.NuclearUltrapower.nuclear_coordinate_bound_oai.{u, v} := @OAI.NuclearUltrapower.nuclear_coordinate_bound_oai.{u, v}
