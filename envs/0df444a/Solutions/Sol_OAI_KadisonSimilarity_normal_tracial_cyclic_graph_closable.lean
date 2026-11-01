-- Prove2me | solution 1 for OAI.KadisonSimilarity.normal_tracial_cyclic_graph_closable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T14:42:14.05492+00:00
-- url     : https://prove2.me/submissions/c1f3855d-e754-40b8-ad9b-d45f238b54ef

import Mathlib
import Definitions.Def_OAIQ075A018
import Definitions.Def_OAIQ075A023
import Theorems.Thm_OAI_KadisonSimilarity_exists_countable_projection_join_of_equiv

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_CyclicGraphSequences
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Points of the closed cyclic graph are limits of actual algebra orbits. -/

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped Topology

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem exists_cyclicGraph_sequence
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (Ω : H) (ξ : K) (x : cyclicGraph σ ρ Ω ξ) :
    ∃ a : ℕ → A, Tendsto
      (fun n => pairRepresentation σ ρ (a n) (WithLp.toLp 2 (Ω, ξ))) atTop
      (𝓝 (x : RectangularSum H K)) := by
  classical
  have hx := x.property
  change (x : RectangularSum H K) ∈ closure
    (Set.range (orbitLinearMap (pairRepresentation σ ρ).range (WithLp.toLp 2 (Ω, ξ)))) at hx
  obtain ⟨y, hy, hlim⟩ := mem_closure_iff_seq_limit.mp hx
  choose b hb using hy
  choose a ha using fun n => (b n).property
  refine ⟨a, hlim.congr fun n => ?_⟩
  rw [← hb n]
  change (b n : RectangularSum H K →L[ℂ] RectangularSum H K) (WithLp.toLp 2 (Ω, ξ)) = _
  rw [← ha n]
  rfl

/-- Both coordinates of a graph point are limits of the same algebra orbit. -/
theorem exists_cyclicGraph_coordinate_limits
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (Ω : H) (ξ : K) (x : cyclicGraph σ ρ Ω ξ) :
    ∃ a : ℕ → A,
      Tendsto (fun n => σ (a n) Ω) atTop (𝓝 (x : RectangularSum H K).fst) ∧
      Tendsto (fun n => ρ (a n) ξ) atTop (𝓝 (x : RectangularSum H K).snd) := by
  obtain ⟨a, ha⟩ := exists_cyclicGraph_sequence σ ρ Ω ξ x
  refine ⟨a, ?_, ?_⟩
  · have h := ((WithLp.fstL 2 ℂ H K).continuous.tendsto
      (x : RectangularSum H K)).comp ha
    change Tendsto (fun n => (pairRepresentation σ ρ (a n)
      (WithLp.toLp 2 (Ω, ξ))).fst) atTop (𝓝 (x : RectangularSum H K).fst) at h
    simpa only [pairRepresentation_fst, WithLp.toLp_fst] using h
  · have h := ((WithLp.sndL 2 ℂ H K).continuous.tendsto
      (x : RectangularSum H K)).comp ha
    change Tendsto (fun n => (pairRepresentation σ ρ (a n)
      (WithLp.toLp 2 (Ω, ξ))).snd) atTop (𝓝 (x : RectangularSum H K).snd) at h
    simpa only [pairRepresentation_snd, WithLp.toLp_snd] using h

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralStepDischarge
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete spectral cut projections

We construct the spectral cuts from the closed range of the positive part.
The construction takes place in the represented Hilbert space; bicommutant
closure proves membership in the given von Neumann algebra.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem rangeSupport_isStarProjection (B : H →L[ℂ] H) :
    IsStarProjection (rangeSupport B) :=
  ⟨Submodule.isIdempotentElem_starProjection _, isSelfAdjoint_starProjection _⟩

theorem rangeSupport_mul (B : H →L[ℂ] H) : rangeSupport B * B = B := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr
    (Submodule.le_topologicalClosure _ ⟨x, rfl⟩)

theorem mul_rangeSupport (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) :
    B * rangeSupport B = B := by
  have h := congrArg star (rangeSupport_mul B)
  simpa only [star_mul, hB.star_eq, (rangeSupport_isStarProjection B).isSelfAdjoint.star_eq]
    using h

/-- Annihilating the range also annihilates its orthogonal support. -/
theorem mul_rangeSupport_eq_zero (B C : H →L[ℂ] H) (h : C * B = 0) :
    C * rangeSupport B = 0 := by
  have hh : operatorRangeClosure B ≤ C.ker := by
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨x, rfl⟩
      exact congrArg (fun S : H →L[ℂ] H => S x) h
    · exact C.isClosed_ker
  ext x
  exact hh ((operatorRangeClosure B).starProjection_apply_mem x)

theorem upperSpectralCut_isStarProjection (A : H →L[ℂ] H) (t : ℝ) :
    IsStarProjection (upperSpectralCut A t) := rangeSupport_isStarProjection _

/-- Multiplication by a cut removes the negative part of the shifted operator. -/
theorem shifted_mul_upperSpectralCut (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    (A - t • 1) * upperSpectralCut A t = (A - t • 1)⁺ := by
  let B := A - t • (1 : H →L[ℂ] H)
  have hB : IsSelfAdjoint B := by
    dsimp [B]
    exact hA.sub ((IsSelfAdjoint.all t).smul (IsSelfAdjoint.one (H →L[ℂ] H)))
  change B * rangeSupport B⁺ = B⁺
  nth_rw 1 [← CFC.posPart_sub_negPart B hB]
  rw [sub_mul]
  rw [mul_rangeSupport B⁺ (CFC.posPart_nonneg B).isSelfAdjoint,
    mul_rangeSupport_eq_zero B⁺ B⁻ (CFC.negPart_mul_posPart B), sub_zero]

theorem shifted_mul_complement_upperSpectralCut (A : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) (t : ℝ) :
    (A - t • 1) * (1 - upperSpectralCut A t) = -(A - t • 1)⁻ := by
  rw [mul_sub, mul_one, shifted_mul_upperSpectralCut A hA t]
  have hB : IsSelfAdjoint (A - t • (1 : H →L[ℂ] H)) :=
    hA.sub ((IsSelfAdjoint.all t).smul (IsSelfAdjoint.one (H →L[ℂ] H)))
  nth_rw 1 [← CFC.posPart_sub_negPart _ hB]
  abel


end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_SpectralCutBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.KadisonSimilarity.generatedGNSInclusion_vector _root_.OAI.KadisonSimilarity.matrixGNSArrayLinear_apply _root_.OAI.KadisonSimilarity.matrixGNSIsometry_vector _root_.OAI.KadisonSimilarity.matrixGNSUnitary_vector _root_.OAI.KadisonSimilarity.matrixGNSVector_apply _root_.OAI.KadisonSimilarity.restrictedTracialGNSInclusion_vector _root_.OAI.KadisonSimilarity.tracialRangeIsometry_vector _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative high spectral cuts. The discarded part has small operator
norm, and positivity bounds the trace of the retained projection. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem upperSpectralCut_commutes_self (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    Commute (upperSpectralCut A t) A := by
  have h : Commute (A - t • 1) A := by
    change (A - t • 1) * A = A * (A - t • 1)
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have hp : Commute (A - t • 1)⁺ A := by
    rw [CFC.posPart_def]
    exact h.cfcₙ_real _
  exact rangeSupport_commutes _ A hp (by simpa only [hA.star_eq] using hp)

/-- The high cut of a positive operator is bounded in order by that operator. -/
theorem smul_upperSpectralCut_le (A : H →L[ℂ] H) (hA : 0 ≤ A) (t : ℝ) :
    t • upperSpectralCut A t ≤ A := by
  let p := upperSpectralCut A t
  have hp : IsStarProjection p := upperSpectralCut_isStarProjection A t
  have hpa : Commute p A := upperSpectralCut_commutes_self A hA.isSelfAdjoint t
  have hc : Commute A (1 - p) := by
    change A * (1 - p) = (1 - p) * A
    rw [mul_sub, sub_mul, mul_one, one_mul, hpa.eq]
  have hfirst : 0 ≤ A * (1 - p) := Commute.mul_nonneg hA hp.one_sub.nonneg hc
  have hsecond : 0 ≤ (A - t • 1) * p := by
    rw [shifted_mul_upperSpectralCut A hA.isSelfAdjoint t]
    exact CFC.posPart_nonneg _
  apply sub_nonneg.mp
  have heq : A - t • p = A * (1 - p) + (A - t • 1) * p := by
    simp only [mul_sub, sub_mul, mul_one, smul_mul_assoc, one_mul]
    abel
  rw [heq]
  exact add_nonneg hfirst hsecond

/-- Removing the high cut of `x x*` leaves operator norm at most `ε`. -/
theorem norm_complement_upperSpectralCut_mul_le (x : H →L[ℂ] H)
    (ε : ℝ) (hε : 0 ≤ ε) :
    ‖(1 - upperSpectralCut (x * star x) (ε ^ 2)) * x‖ ≤ ε := by
  let A := x * star x
  let p := upperSpectralCut A (ε ^ 2)
  let q := 1 - p
  let B := q * x
  have hA : 0 ≤ A := mul_star_self_nonneg x
  have hp : IsStarProjection p := upperSpectralCut_isStarProjection A _
  have hq : IsStarProjection q := hp.one_sub
  have hpa : Commute p A := upperSpectralCut_commutes_self A hA.isSelfAdjoint _
  have hqa : q * A = A * q := by
    dsimp [q]
    rw [sub_mul, mul_sub, one_mul, mul_one, hpa.eq]
  have hu : A * q ≤ ε ^ 2 • q := by
    apply sub_nonpos.mp
    have heq : A * q - ε ^ 2 • q = (A - ε ^ 2 • 1) * q := by
      simp only [sub_mul, smul_mul_assoc, one_mul]
    rw [heq, shifted_mul_complement_upperSpectralCut A hA.isSelfAdjoint _]
    exact neg_nonpos.mpr (CFC.negPart_nonneg _)
  have hBB : B * star B = A * q := by
    change (q * x) * star (q * x) = A * q
    rw [star_mul, hq.isSelfAdjoint.star_eq]
    calc
      (q * x) * (star x * q) = (q * A) * q := by dsimp [A]; noncomm_ring
      _ = A * q := by rw [hqa, mul_assoc, hq.isIdempotentElem.eq]
  have hle : B * star B ≤ ε ^ 2 • (1 : H →L[ℂ] H) := by
    rw [hBB]
    exact hu.trans (smul_le_smul_of_nonneg_left
      (show q ≤ 1 from sub_le_self _ hp.nonneg) (sq_nonneg ε))
  have hn : ‖B‖ * ‖B‖ ≤ ε ^ 2 := by
    rw [← CStarRing.norm_self_mul_star]
    apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (sq_nonneg ε)
      (mul_star_self_nonneg B)).mpr
    simpa only [Algebra.algebraMap_eq_smul_one] using hle
  change ‖B‖ ≤ ε
  nlinarith [norm_nonneg B]

section Trace
open Filter
open scoped Topology

theorem leftSpectralCut_isStarProjection (M : VonNeumannAlgebra H)
    (x : M.toStarSubalgebra) (ε : ℝ) : IsStarProjection (leftSpectralCut M x ε) := by
  constructor
  · apply Subtype.ext
    exact (upperSpectralCut_isStarProjection _ _).isIdempotentElem.eq
  · apply Subtype.ext
    exact (upperSpectralCut_isStarProjection _ _).isSelfAdjoint.star_eq

theorem norm_complement_leftSpectralCut_mul_le (M : VonNeumannAlgebra H)
    (x : M.toStarSubalgebra) (ε : ℝ) (hε : 0 ≤ ε) :
    ‖(1 - leftSpectralCut M x ε) * x‖ ≤ ε :=
  norm_complement_upperSpectralCut_mul_le (x : H →L[ℂ] H) ε hε

attribute [local instance] OAI.KadisonSimilarity.spectralCut_closed
/-- Chebyshev's trace bound for the left spectral cut. -/
theorem leftSpectralCut_trace_bound (M : VonNeumannAlgebra H)
    (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (htr : ∀ a b, τ (a * b) = τ (b * a))
    (x : M.toStarSubalgebra) (ε : ℝ) :
    ε ^ 2 * (τ (leftSpectralCut M x ε)).re ≤ ‖gnsTracialVector τ x‖ ^ 2 := by
  have horder : (ε ^ 2 : ℝ) • leftSpectralCut M x ε ≤ x * star x := by
    change (ε ^ 2 : ℝ) • upperSpectralCut
      ((x : H →L[ℂ] H) * star (x : H →L[ℂ] H)) (ε ^ 2) ≤
      (x : H →L[ℂ] H) * star (x : H →L[ℂ] H)
    exact smul_upperSpectralCut_le ((x : H →L[ℂ] H) * star (x : H →L[ℂ] H))
      (mul_star_self_nonneg _) (ε ^ 2)
  have ht := (τ.monotone horder).1
  change (τ ((ε ^ 2 : ℝ) • leftSpectralCut M x ε)).re ≤
    (τ (x * star x)).re at ht
  have hmap : τ ((ε ^ 2 : ℝ) • leftSpectralCut M x ε) =
      (ε ^ 2 : ℝ) • τ (leftSpectralCut M x ε) :=
    τ.toLinearMap.map_smul_of_tower _ _
  rw [hmap] at ht
  have hreal : ε ^ 2 * (τ (leftSpectralCut M x ε)).re ≤ (τ (x * star x)).re := by
    simpa only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using ht
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), gnsTracialVector_inner, ← htr x (star x)]
  exact hreal

/-- Algebra vectors tending to zero have high spectral cuts of vanishing
trace at every fixed positive threshold. -/
theorem leftSpectralCut_trace_tendsto_zero (M : VonNeumannAlgebra H)
    (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (htr : ∀ a b, τ (a * b) = τ (b * a))
    (x : ℕ → M.toStarSubalgebra)
    (hx : Tendsto (fun n => gnsTracialVector τ (x n)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (τ (leftSpectralCut M (x n) ε)).re) atTop (𝓝 0) := by
  have hsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  apply squeeze_zero (g := fun n => ‖gnsTracialVector τ (x n)‖ ^ 2 / ε ^ 2)
    (fun n => (τ.map_nonneg (leftSpectralCut_isStarProjection M (x n) ε).nonneg).1)
    (fun n => (le_div_iff₀ hsq).mpr (by
      nlinarith [leftSpectralCut_trace_bound M τ htr (x n) ε]))
  simpa only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div]
    using (hx.norm.pow 2).div_const (ε ^ 2)

end Trace
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_StrongApplyLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniformly bounded strong convergence can be applied to converging
vectors. Only the contractive case needed for spectral projections is used. -/

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem contractive_strong_zero_apply
    (T : ℕ → H →L[ℂ] H) (hT : ∀ n, ‖T n‖ ≤ 1)
    (hzero : ∀ x : H, Tendsto (fun n => T n x) atTop (𝓝 0))
    (v : ℕ → H) (x : H) (hv : Tendsto v atTop (𝓝 x)) :
    Tendsto (fun n => T n (v n)) atTop (𝓝 0) := by
  have hb (n : ℕ) : ‖T n (v n)‖ ≤ ‖v n - x‖ + ‖T n x‖ := by
    calc
      _ = ‖T n (v n - x) + T n x‖ := by rw [map_sub, sub_add_cancel]
      _ ≤ ‖T n (v n - x)‖ + ‖T n x‖ := norm_add_le _ _
      _ ≤ ‖v n - x‖ + ‖T n x‖ := by
        have h := ((T n).le_opNorm (v n - x)).trans
          (mul_le_mul_of_nonneg_right (hT n) (norm_nonneg _))
        linarith
  apply squeeze_zero_norm hb
  have hc : Tendsto (fun _ : ℕ => x) atTop (𝓝 x) := tendsto_const_nhds
  simpa only [sub_self, norm_zero, zero_add] using
    ((hv.sub hc).norm.add (hzero x).norm)

theorem contractive_complement_apply
    (T : ℕ → H →L[ℂ] H) (hT : ∀ n, ‖T n‖ ≤ 1)
    (hzero : ∀ x : H, Tendsto (fun n => T n x) atTop (𝓝 0))
    (v : ℕ → H) (x : H) (hv : Tendsto v atTop (𝓝 x)) :
    Tendsto (fun n => (1 - T n) (v n)) atTop (𝓝 x) := by
  have h := hv.sub (contractive_strong_zero_apply T hT hzero v x hv)
  simpa only [_root_.sub_apply, one_apply_eq_self, sub_zero] using h

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_NormalSupportTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Range supports are preserved by star isomorphisms between concrete von
Neumann algebras. The proof uses their algebraic least-support property, so
no continuity in the weak operator topology is assumed. -/

noncomputable section
namespace KadisonSimilarity

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Any left identity on an operator is a left identity on its range support. -/
theorem rangeSupport_least_left (B p : H →L[ℂ] H) (h : p * B = B) :
    p * rangeSupport B = rangeSupport B := by
  have hz : (1 - p) * B = 0 := by rw [sub_mul, one_mul, h, sub_self]
  have hs := mul_rangeSupport_eq_zero B (1 - p) hz
  rw [sub_mul, one_mul, sub_eq_zero] at hs
  exact hs.symm

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ProjectionJoinTrace
attribute [-instance] _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite joins of projections and their trace bound. These elementary
support identities are used to control countable unions of small spectral
projections in the normal representation argument. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A positive trace is monotone in the algebraic projection order. -/
theorem trace_projection_le {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (τ : A →ₚ[ℂ] ℂ)
    (p q : A) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : q * p = p) : (τ p).re ≤ (τ q).re := by
  have ht := τ.map_nonneg (hp.sub_of_mul_eq_right hq h).nonneg
  rw [map_sub] at ht
  exact sub_nonneg.mp ht.1

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_MonotoneProjectionLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strong limits of increasing projections agree with their algebraic
least upper bound. This permits transport between faithful normal models
without assuming continuity of the intervening star isomorphism. -/

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem rangeSupport_of_isStarProjection (p : H →L[ℂ] H) (hp : IsStarProjection p) :
    rangeSupport p = p := by
  have h₁ := rangeSupport_least_left p p hp.isIdempotentElem.eq
  have h₂ := rangeSupport_mul p
  have h₃ := congrArg star h₂
  rw [star_mul, hp.isSelfAdjoint.star_eq,
    (rangeSupport_isStarProjection p).isSelfAdjoint.star_eq] at h₃
  exact h₁.symm.trans h₃

/-- A monotone sequence of projections has a strong limit which is its
least upper bound inside the concrete von Neumann algebra. -/
theorem exists_monotone_projection_limit (M : VonNeumannAlgebra H)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n))
    (hmono : ∀ i j, i ≤ j → p j * p i = p i) :
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧
      (∀ x : H, Tendsto (fun n => (p n : H →L[ℂ] H) x) atTop (𝓝 ((q : H →L[ℂ] H) x))) ∧
      (∀ n, q * p n = p n) ∧
      ∀ r : M.toStarSubalgebra, IsStarProjection r → (∀ n, r * p n = p n) → r * q = q := by
  let U : ℕ → Submodule ℂ H := fun n => operatorRangeClosure (p n : H →L[ℂ] H)
  have hU : Monotone U := by
    intro i j hij
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨x, rfl⟩
      apply Submodule.le_topologicalClosure
      refine ⟨(p i : H →L[ℂ] H) x, ?_⟩
      exact congrArg (fun a : M.toStarSubalgebra => (a : H →L[ℂ] H) x) (hmono i j hij)
    · exact Submodule.isClosed_topologicalClosure _
  let W := (⨆ n, U n).topologicalClosure
  let Q : H →L[ℂ] H := W.starProjection
  have hproj (n : ℕ) : (U n).starProjection = (p n : H →L[ℂ] H) :=
    rangeSupport_of_isStarProjection _ ((hp n).map M.toStarSubalgebra.subtype)
  have hlim (x : H) : Tendsto (fun n => (p n : H →L[ℂ] H) x) atTop (𝓝 (Q x)) := by
    simpa only [hproj] using Submodule.starProjection_tendsto_closure_iSup U hU x
  have hQM : Q ∈ M :=
    Generator.Tracial.weak_operator_limit_mem M p Q (fun x y =>
      (continuous_const.inner continuous_id).continuousAt.tendsto.comp (hlim x))
  let q : M.toStarSubalgebra := ⟨Q, hQM⟩
  have hq : IsStarProjection q := by
    constructor
    · apply Subtype.ext
      exact Submodule.isIdempotentElem_starProjection W
    · apply Subtype.ext
      exact isSelfAdjoint_starProjection W
  have hupper (n : ℕ) : q * p n = p n := by
    apply Subtype.ext
    ext x
    apply Submodule.starProjection_eq_self_iff.mpr
    exact (le_iSup U n).trans (Submodule.le_topologicalClosure _)
      (Submodule.le_topologicalClosure _ ⟨x, rfl⟩)
  refine ⟨q, hq, hlim, hupper, ?_⟩
  intro r hr hru
  apply Subtype.ext
  ext x
  have he : W ≤ operatorRangeClosure (r : H →L[ℂ] H) := by
    apply Submodule.topologicalClosure_minimal
    · apply iSup_le
      intro n
      apply Submodule.topologicalClosure_minimal
      · rintro _ ⟨y, rfl⟩
        apply Submodule.le_topologicalClosure
        exact ⟨(p n : H →L[ℂ] H) y,
          congrArg (fun a : M.toStarSubalgebra => (a : H →L[ℂ] H) y) (hru n)⟩
      · exact Submodule.isClosed_topologicalClosure _
    · exact Submodule.isClosed_topologicalClosure _
  have hfix := Submodule.starProjection_eq_self_iff.mpr
    (he (W.starProjection_apply_mem x))
  rw [show (operatorRangeClosure (r : H →L[ℂ] H)).starProjection = (r : H →L[ℂ] H) from
    rangeSupport_of_isStarProjection _ (hr.map M.toStarSubalgebra.subtype)] at hfix
  exact hfix

/-- Decreasing projections have a strong limit below every member. -/
theorem exists_antitone_projection_limit (M : VonNeumannAlgebra H)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n))
    (hanti : ∀ i j, i ≤ j → p i * p j = p j) :
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧
      (∀ x : H, Tendsto (fun n => (p n : H →L[ℂ] H) x) atTop (𝓝 ((q : H →L[ℂ] H) x))) ∧
      ∀ n, p n * q = q := by
  let a : ℕ → M.toStarSubalgebra := fun n => 1 - p n
  have ha (n : ℕ) : IsStarProjection (a n) := (hp n).one_sub
  have hmono (i j : ℕ) (hij : i ≤ j) : a j * a i = a i := by
    have hji : p j * p i = p j := by
      simpa only [star_mul, (hp i).isSelfAdjoint.star_eq, (hp j).isSelfAdjoint.star_eq]
        using congrArg star (hanti i j hij)
    change (1 - p j) * (1 - p i) = 1 - p i
    simp only [sub_mul, mul_sub, one_mul, mul_one, hji]
    abel
  obtain ⟨r, hr, hlim, hupper, -⟩ := exists_monotone_projection_limit M a ha hmono
  refine ⟨1 - r, hr.one_sub, ?_, ?_⟩
  · intro x
    have h := (tendsto_const_nhds (x := x)).sub (hlim x)
    change Tendsto (fun n => x - (x - (p n : H →L[ℂ] H) x)) atTop
      (𝓝 (x - (r : H →L[ℂ] H) x)) at h
    change Tendsto (fun n => (p n : H →L[ℂ] H) x) atTop
      (𝓝 (x - (r : H →L[ℂ] H) x))
    simpa only [sub_sub_cancel] using h
  · intro n
    have hu := hupper n
    change r * (1 - p n) = 1 - p n at hu
    rw [mul_sub, mul_one] at hu
    have hqp : (1 - r) * p n = 1 - r := by
      rw [sub_mul, one_mul]
      apply (sub_eq_sub_iff_add_eq_add).mpr
      simpa only [add_comm] using (sub_eq_sub_iff_add_eq_add).mp hu
    simpa only [star_mul, (hp n).isSelfAdjoint.star_eq, hr.one_sub.isSelfAdjoint.star_eq]
      using congrArg star hqp

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_ProjectionTraceContinuity
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
attribute [-simp] _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.Generator.Tracial.restrictedTrace_norm₂ _root_.OAI.Generator.Tracial.restrictedTrace_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalTracialRepresentation_vector _root_.OAI.KadisonSimilarity.concreteTraceLinear_apply _root_.OAI.KadisonSimilarity.concreteTraceLinear_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small trace projections act strongly as zero. The argument uses
countable joins and geometric trace tails, rather than assuming normality
of a star isomorphism between concrete von Neumann algebras. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge Filter
open scoped ComplexOrder Topology

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

attribute [local instance] OAI.KadisonSimilarity.projectionContinuity_closed
/-- Decreasing projections with vanishing faithful trace converge strongly
to zero in the original concrete representation. -/
theorem antitone_projection_tendsto_zero
    (M : VonNeumannAlgebra H) (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hf : ∀ q, IsStarProjection q → (τ q).re = 0 → q = 0)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n))
    (hanti : ∀ i j, i ≤ j → p i * p j = p j)
    (ht : Tendsto (fun n => (τ (p n)).re) atTop (𝓝 0)) (x : H) :
    Tendsto (fun n => (p n : H →L[ℂ] H) x) atTop (𝓝 0) := by
  obtain ⟨q, hq, hlim, hbelow⟩ := exists_antitone_projection_limit M p hp hanti
  have hqle : (τ q).re ≤ 0 := ge_of_tendsto ht
    (Eventually.of_forall fun n => trace_projection_le τ q (p n) hq (hp n) (hbelow n))
  have hqge : 0 ≤ (τ q).re := (τ.map_nonneg hq.nonneg).1
  have hzero := hf q hq (le_antisymm hqle hqge)
  simpa only [hzero, ZeroMemClass.coe_zero, zero_apply] using hlim x

/-- A sequence of projections with a geometric trace bound acts strongly
as zero, even in a different faithful concrete normal model. -/
theorem geometric_projection_tendsto_zero
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    [IsClosed (N.toStarSubalgebra : Set (K →L[ℂ] K))]
    (e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra)
    (υ : TracialRepresentation N)
    (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (σ : N.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hσ : ∀ b, σ b = υ.trace b) (he : ∀ a, σ (e a) = τ a)
    (hf : ∀ q, IsStarProjection q → (τ q).re = 0 → q = 0)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n))
    (hpt : ∀ n, (τ (p n)).re ≤ (1 / 2 : ℝ) ^ n) (x : H) :
    Tendsto (fun n => (p n : H →L[ℂ] H) x) atTop (𝓝 0) := by
  classical
  have htail (m n : ℕ) :
      ∑ i ∈ Finset.range n, (τ (p (m + i))).re ≤ 2 * (1 / 2 : ℝ) ^ m := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ (m + i) :=
        Finset.sum_le_sum (fun i _ => hpt (m + i))
      _ = (1 / 2 : ℝ) ^ m * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i := by
        simp only [pow_add, Finset.mul_sum]
      _ ≤ (1 / 2 : ℝ) ^ m * 2 :=
        mul_le_mul_of_nonneg_left (sum_geometric_two_le n) (by positivity)
      _ = 2 * (1 / 2 : ℝ) ^ m := mul_comm _ _
  have hex (m : ℕ) := exists_countable_projection_join_of_equiv M N e υ τ σ hσ he
    (fun i => p (m + i)) (fun i => hp (m + i)) (2 * (1 / 2 : ℝ) ^ m) (htail m)
  choose q hq hqt hqp hleast using hex
  have hanti (m n : ℕ) (hmn : m ≤ n) : q m * q n = q n := by
    apply hleast n (q m) (hq m)
    intro i
    have hidx : m + (n - m + i) = n + i := by omega
    simpa only [hidx] using hqp m (n - m + i)
  have htrace : Tendsto (fun n => (τ (q n)).re) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (τ.map_nonneg (hq n).nonneg).1) hqt
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 2
  have hqzero := antitone_projection_tendsto_zero M τ hf q hq hanti htrace x
  have hnorm (n : ℕ) : ‖(p n : H →L[ℂ] H) x‖ ≤ ‖(q n : H →L[ℂ] H) x‖ := by
    have hqp' : q n * p n = p n := by simpa only [Nat.add_zero] using hqp n 0
    have hpq : p n * q n = p n := by
      simpa only [star_mul, (hp n).isSelfAdjoint.star_eq, (hq n).isSelfAdjoint.star_eq]
        using congrArg star hqp'
    calc
      _ = ‖(p n : H →L[ℂ] H) ((q n : H →L[ℂ] H) x)‖ :=
        congrArg norm (congrArg (fun a : M.toStarSubalgebra => (a : H →L[ℂ] H) x) hpq).symm
      _ ≤ ‖(p n : H →L[ℂ] H)‖ * ‖(q n : H →L[ℂ] H) x‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖(q n : H →L[ℂ] H) x‖ :=
        mul_le_mul_of_nonneg_right ((hp n).map M.toStarSubalgebra.subtype).norm_le (norm_nonneg _)
      _ = ‖(q n : H →L[ℂ] H) x‖ := one_mul _
  exact squeeze_zero_norm hnorm (by simpa using hqzero.norm)

/-- Vanishing trace of arbitrary projections forces strong convergence to
zero. A hypothetical fixed violation supplies a geometric-trace sequence,
which contradicts the preceding countable-join argument. -/
theorem projection_tendsto_zero_of_trace_tendsto_zero
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    [IsClosed (N.toStarSubalgebra : Set (K →L[ℂ] K))]
    (e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra)
    (υ : TracialRepresentation N)
    (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (σ : N.toStarSubalgebra →ₚ[ℂ] ℂ)
    (hσ : ∀ b, σ b = υ.trace b) (he : ∀ a, σ (e a) = τ a)
    (hf : ∀ q, IsStarProjection q → (τ q).re = 0 → q = 0)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n))
    (ht : Tendsto (fun n => (τ (p n)).re) atTop (𝓝 0)) (x : H) :
    Tendsto (fun n => (p n : H →L[ℂ] H) x) atTop (𝓝 0) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  simp only [dist_zero_right]
  by_contra! hbad
  have hex (i : ℕ) : ∃ n, (τ (p n)).re ≤ (1 / 2 : ℝ) ^ i ∧
      ε ≤ ‖(p n : H →L[ℂ] H) x‖ := by
    have hevent : ∀ᶠ n in atTop, (τ (p n)).re < (1 / 2 : ℝ) ^ i :=
      ht (Iio_mem_nhds (by positivity))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
    obtain ⟨n, hn, hnx⟩ := hbad N
    exact ⟨n, (hN n hn).le, hnx⟩
  choose f hft hfx using hex
  have hz := geometric_projection_tendsto_zero M N e υ τ σ hσ he hf
    (fun i => p (f i)) (fun i => hp (f i)) hft x
  obtain ⟨n, hn⟩ := Metric.tendsto_atTop.mp hz ε hε
  have hsmall := hn n le_rfl
  rw [dist_zero_right] at hsmall
  exact (not_lt_of_ge (hfx n)) hsmall

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_GNSProjectionContinuity
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Projection continuity in the original representation follows from
faithfulness and normality of the chosen trace's native GNS range. -/

noncomputable section
namespace KadisonSimilarity
open Generator.Tracial UltrapowerBridge Filter
open scoped ComplexOrder Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonSimilarity.gnsProjection_closed
/-- Projection continuity for a faithful normal tracial geometry. -/
theorem projection_tendsto_zero_of_normal_geometry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (M : VonNeumannAlgebra H) (G : TracialCornerGeometry M.toStarSubalgebra E)
    (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hτ : ∀ a, τ a = G.trace a)
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (N : VonNeumannAlgebra E) (hN : G.left.range = N.toStarSubalgebra)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n))
    (ht : Tendsto (fun n => (τ (p n)).re) atTop (𝓝 0)) (x : H) :
    Tendsto (fun n => (p n : H →L[ℂ] H) x) atTop (𝓝 0) := by
  let e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra :=
    equivalenceOfConcreteRange N G.left (G.left_injective hf) hN
  let υ : TracialRepresentation N := G.normalTracialRepresentation h1 hf N hN
  let σ : N.toStarSubalgebra →ₚ[ℂ] ℂ := transportedPositiveTrace τ e
  have hσ (b : N.toStarSubalgebra) : σ b = υ.trace b := by
    have h := G.normalTracialRepresentation_trace h1 hf N hN (e.symm b)
    change υ.trace (e (e.symm b)) = G.trace (e.symm b) at h
    rw [e.apply_symm_apply] at h
    change τ (e.symm b) = υ.trace b
    exact (hτ _).trans h.symm
  have he (a : M.toStarSubalgebra) : σ (e a) = τ a :=
    transportedPositiveTrace_map τ e a
  have hfaith (q : M.toStarSubalgebra) (hq : IsStarProjection q)
      (hqt : (τ q).re = 0) : q = 0 := by
    have hn : ‖G.vector q‖ ^ 2 = 0 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), G.inner_vector,
        hq.isSelfAdjoint.star_eq, hq.isIdempotentElem.eq, ← hτ]
      exact hqt
    have hz : G.vector q = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
    exact hf (hz.trans (map_zero G.vector).symm)
  exact projection_tendsto_zero_of_trace_tendsto_zero M N e υ τ σ hσ he hfaith p hp ht x

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_NormalSpectralTruncation
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vanishing normal trace norm forces any convergent fixed-vector orbit
to have zero limit, by cutting off its high left spectrum. -/

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonSimilarity.normalTruncation_closed
theorem norm_limit_le_of_spectral_truncation
    (M : VonNeumannAlgebra H) (a : ℕ → M.toStarSubalgebra)
    (ξ y : H) (hv : Tendsto (fun n => (a n : H →L[ℂ] H) ξ) atTop (𝓝 y))
    (ε : ℝ) (hε : 0 < ε)
    (hz : ∀ z : H, Tendsto
      (fun n => (leftSpectralCut M (a n) ε : H →L[ℂ] H) z) atTop (𝓝 0)) :
    ‖y‖ ≤ ε * ‖ξ‖ := by
  let p (n : ℕ) := leftSpectralCut M (a n) ε
  let T (n : ℕ) : H →L[ℂ] H := p n
  have hp (n : ℕ) : IsStarProjection (p n) := leftSpectralCut_isStarProjection M (a n) ε
  have hT (n : ℕ) : ‖T n‖ ≤ 1 := (hp n).norm_le
  have hc := contractive_complement_apply T hT hz
    (fun n => (a n : H →L[ℂ] H) ξ) y hv
  apply le_of_tendsto hc.norm
  filter_upwards [] with n
  calc
    ‖(1 - T n) ((a n : H →L[ℂ] H) ξ)‖ =
        ‖(((1 - p n) * a n : M.toStarSubalgebra) : H →L[ℂ] H) ξ‖ := rfl
    _ ≤ ‖(1 - p n) * a n‖ * ‖ξ‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ε * ‖ξ‖ := mul_le_mul_of_nonneg_right
      (norm_complement_leftSpectralCut_mul_le M (a n) ε hε.le) (norm_nonneg _)

theorem limit_eq_zero_of_spectral_truncation
    (M : VonNeumannAlgebra H) (a : ℕ → M.toStarSubalgebra)
    (ξ y : H) (hv : Tendsto (fun n => (a n : H →L[ℂ] H) ξ) atTop (𝓝 y))
    (hz : ∀ ε : ℝ, 0 < ε → ∀ z : H, Tendsto
      (fun n => (leftSpectralCut M (a n) ε : H →L[ℂ] H) z) atTop (𝓝 0)) :
    y = 0 := by
  have hbound (ε : ℝ) (hε : 0 < ε) : ‖y‖ ≤ ε * ‖ξ‖ :=
    norm_limit_le_of_spectral_truncation M a ξ y hv ε hε (hz ε hε)
  have hsmall : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n * ‖ξ‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_const ‖ξ‖
  exact norm_eq_zero.mp (le_antisymm
    (ge_of_tendsto hsmall (Eventually.of_forall fun n =>
      hbound ((1 / 2 : ℝ) ^ n) (pow_pos (by norm_num) n))) (norm_nonneg _))

/-- Equal trace inner products identify the orbit norms in any tracial
geometry with the native GNS orbit norms. -/
theorem tracialGeometry_gns_norm_eq
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (G : TracialCornerGeometry A E)
    (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a, τ a = G.trace a)
    (a : A) : ‖gnsTracialVector τ a‖ = ‖G.vector a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    gnsTracialVector_inner, G.inner_vector, hτ]

theorem normal_geometry_orbit_limit_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (M : VonNeumannAlgebra H) (G : TracialCornerGeometry M.toStarSubalgebra E)
    (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hτ : ∀ a, τ a = G.trace a)
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (N : VonNeumannAlgebra E) (hN : G.left.range = N.toStarSubalgebra)
    (a : ℕ → M.toStarSubalgebra) (ha : Tendsto (fun n => G.vector (a n)) atTop (𝓝 0))
    (ξ y : H) (hv : Tendsto (fun n => (a n : H →L[ℂ] H) ξ) atTop (𝓝 y)) :
    y = 0 := by
  have hg : Tendsto (fun n => gnsTracialVector τ (a n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [tracialGeometry_gns_norm_eq G τ hτ, norm_zero] using ha.norm
  have htr (a b : M.toStarSubalgebra) : τ (a * b) = τ (b * a) := by
    rw [hτ, hτ, G.tracial]
  apply limit_eq_zero_of_spectral_truncation M a ξ y hv
  intro ε hε z
  exact projection_tendsto_zero_of_normal_geometry M G τ hτ h1 hf N hN
    (fun n => leftSpectralCut M (a n) ε)
    (fun n => leftSpectralCut_isStarProjection M (a n) ε)
    (leftSpectralCut_trace_tendsto_zero M τ htr a hg ε hε) z

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_NormalCyclicGraph
attribute [-instance] _root_.OAI.KadisonSimilarity.finiteMatrixTestAlgebra_closed _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftCStarAlgebra _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftInnerProductSpace _root_.OAI.KadisonSimilarity.SimilarityUniverseTransfer.uliftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A faithful normal finite trace makes the cyclic orbit map closable.
The proof removes a high spectral projection of vanishing trace, leaving
an arbitrarily small operator applied to the fixed cyclic vector. -/

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped Topology ComplexOrder

variable {H K E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

attribute [local instance] OAI.KadisonSimilarity.normalCyclic_closed
theorem normal_tracial_cyclic_graph_closable_oai
    (M : VonNeumannAlgebra H) (G : TracialCornerGeometry M.toStarSubalgebra E)
    (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hτ : ∀ a, τ a = G.trace a)
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (N : VonNeumannAlgebra E) (hN : G.left.range = N.toStarSubalgebra)
    (ρ : M.toStarSubalgebra →⋆ₐ[ℂ] (K →L[ℂ] K)) (J : K →ₗᵢ[ℂ] H)
    (hJ : ∀ a, J.toContinuousLinearMap.comp (ρ a) =
      (a : H →L[ℂ] H).comp J.toContinuousLinearMap) (ξ : K)
    (x : cyclicGraph G.left ρ (G.vector 1) ξ)
    (hx : (x : RectangularSum E K).fst = 0) :
    (x : RectangularSum E K).snd = 0 := by
  obtain ⟨a, hs, ht⟩ := exists_cyclicGraph_coordinate_limits G.left ρ (G.vector 1) ξ x
  have hsource : Tendsto (fun n => G.vector (a n)) atTop (𝓝 0) := by
    simpa only [G.left_vector, mul_one, hx] using hs
  have htarget : Tendsto (fun n => (a n : H →L[ℂ] H) (J ξ)) atTop
      (𝓝 (J (x : RectangularSum E K).snd)) := by
    have h := (J.continuous.tendsto (x : RectangularSum E K).snd).comp ht
    have he (n : ℕ) : J (ρ (a n) ξ) = (a n : H →L[ℂ] H) (J ξ) :=
      congrArg (fun T : K →L[ℂ] H => T ξ) (hJ (a n))
    exact h.congr (fun n => he n)
  have hy := normal_geometry_orbit_limit_eq_zero M G τ hτ h1 hf N hN a hsource
    (J ξ) (J (x : RectangularSum E K).snd) htarget
  exact J.injective (hy.trans (map_zero J).symm)

end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.KadisonSimilarity.normal_tracial_cyclic_graph_closable_oai.{u_1, u_2, u_3} := @OAI.KadisonSimilarity.normal_tracial_cyclic_graph_closable_oai.{u_1, u_2, u_3}
