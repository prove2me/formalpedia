-- Prove2me | solution 1 for OAI.KervaireMatrix.phase_scalar_le_codim
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:38:23.170824+00:00
-- url     : https://prove2.me/submissions/a0d0e81c-9c45-4c6e-95d7-e9d5aa654ca5

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/FixedSpaces.lean:L198-L225
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireMatrix.phase_scalar_le_codim. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceTangent
import Definitions.Def_OAI_GroupTheory_Kervaire_UnitaryHomotopy
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceDegree
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentExistence
import Definitions.Def_OAI_GroupTheory_Kervaire_SignedIncidence
import Definitions.Def_OAI_GroupTheory_Kervaire_FixedSpaces
import Theorems.Thm_OAI_KervaireSpectral_hasSum_spectralLog
import Theorems.Thm_OAI_KervaireSpectral_sumPhase_le_half_codim
import Theorems.Thm_OAI_KervaireSpectral_tendsto_smoothTrace_vectorCLM

-- ---- from OAI.GroupTheory.Kervaire.ScalarPhase ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology

namespace KervaireScalarPhase

theorem norm_cutApproach_lt_one {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1) :
    ‖cutApproach ε‖ < 1 := by
  apply (sq_lt_sq₀ (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 1)).mp
  rw [← Complex.normSq_eq_norm_sq]
  have hsq : ε ^ 2 < 1 := by nlinarith [mul_pos hε (sub_pos.mpr hε')]
  simp only [cutApproach, Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add, one_pow]
  nlinarith [mul_pos (sq_pos_of_pos hε) (sub_pos.mpr hsq)]

theorem cutTime_pos (n : ℕ) : 0 < cutTime n := by
  unfold cutTime
  positivity

theorem cutTime_lt_one (n : ℕ) : cutTime n < 1 := by
  unfold cutTime
  apply (div_lt_one (by positivity)).mpr
  have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem norm_cutApproach_cutTime_lt_one (n : ℕ) : ‖cutApproach (cutTime n)‖ < 1 :=
  norm_cutApproach_lt_one (cutTime_pos n) (cutTime_lt_one n)

end KervaireScalarPhase

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.SpectralApproximation ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology

namespace KervaireSpectral
open KervaireTraceCalculus KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Applying any continuous functional to the convergent spectral logarithm
 commutes with its Mercator expansion. -/
theorem traceLog_eq_calculus (U : Operator H) (hU : U ∈ unitary (Operator H))
    (τ : Operator H →L[ℂ] ℂ) {a : ℂ} (ha : ‖a‖ < 1) :
    let hN := isStarNormal_of_mem_unitary hU
    traceLog τ a U = τ (cfcHom hN (spectralLog U hU a ha)) := by
  let hN := isStarNormal_of_mem_unitary hU
  have hc := (hasSum_spectralLog U hU ha).map (cfcHom hN) (cfcHom_continuous hN)
  have ht := hc.map τ τ.continuous
  apply HasSum.tsum_eq
  convert ht using 1
  ext n
  simp [map_smul, map_pow, cfcHom_id]

end KervaireSpectral

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.PhaseSubadditivity ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder

namespace KervaireCentralizer
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
attribute [local instance] OAI.KervaireCentralizer.instContinuousFunctionalCalculusRealOperatorIsSelfAdjoint
end KervaireCentralizer

namespace KervaireSpectral
open KervaireTraceCalculus KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

/-- Regularized tracial phases distribute over a finite vector family. -/
theorem smoothTrace_vectorSum (U : Operator H) (hU : U ∈ unitary (Operator H))
    (ξ : ι → H) {a : ℂ} (ha : ‖a‖ < 1) :
    smoothTrace (vectorSum ξ) a U = ∑ j, smoothTrace (vectorCLM (ξ j)) a U := by
  let hN := isStarNormal_of_mem_unitary hU
  simp_rw [smoothTrace, traceLog_eq_calculus U hU _ ha, vectorSum_apply]
  simp only [Complex.re_sum, Complex.im_sum, Finset.sum_div, Finset.sum_sub_distrib]

/-- Bounded convergence for the precise matrix-trace phase. -/
theorem tendsto_smoothTrace_vectorSum (U : Operator H) (hU : U ∈ unitary (Operator H))
    (ξ : ι → H) :
    let _ := isStarNormal_of_mem_unitary hU
    Tendsto (fun n => smoothTrace (vectorSum ξ) (cutApproach (cutTime n)) U)
      atTop (𝓝 (sumPhase U ξ)) := by
  let hN := isStarNormal_of_mem_unitary hU
  simp_rw [smoothTrace_vectorSum U hU ξ (norm_cutApproach_cutTime_lt_one _)]
  exact tendsto_finsetSum _ (fun j _ => tendsto_smoothTrace_vectorCLM U hU (ξ j))

end KervaireSpectral

namespace KervaireCentralizer
open KervaireTraceCalculus KervaireSpectral KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

end KervaireCentralizer

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.PhaseGrids ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder

namespace KervaireSpectral

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end

open KervaireTraceCalculus KervaireScalarPhase
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Positive integral moments, including mass, determine the cut-sensitive phase.
This avoids assuming any Borel functional calculus naturality theorem. -/
theorem sumPhase_eq_of_moments
    (U : Operator H) (V : Operator K)
    (hU : U ∈ unitary (Operator H)) (hV : V ∈ unitary (Operator K))
    (ξ : ι → H) (η : κ → K)
    (hm : ∀ n : ℕ, vectorSum ξ (U ^ n) = vectorSum η (V ^ n)) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary hV
    sumPhase U ξ = sumPhase V η := by
  let _ := isStarNormal_of_mem_unitary hU
  let _ := isStarNormal_of_mem_unitary hV
  have hs (a : ℂ) : smoothTrace (vectorSum ξ) a U = smoothTrace (vectorSum η) a V := by
    have hmass := hm 0
    simp only [pow_zero] at hmass
    unfold smoothTrace traceLog
    rw [hmass]
    simp_rw [hm]
  exact tendsto_nhds_unique (tendsto_smoothTrace_vectorSum U hU ξ)
    (by simpa only [hs] using tendsto_smoothTrace_vectorSum V hV η)

end KervaireSpectral

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.MatrixTrace ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate

namespace KervaireMatrix

section
open KervaireRegular
variable {D A : Type*} [Group A]
variable [Fintype D]

end

section
open KervaireRegular
variable {D A : Type*} [Fintype D] [Group A]

end

section
open KervaireRegular KervaireSpectral
variable {D A : Type*} [Group A]

variable [Fintype D]

/-- The vector family agrees exactly with the unnormalized matrix trace. -/
theorem trace_eq_vectorSum : (trace : Operator D A →L[ℂ] ℂ) =
    vectorSum (fun i : D => (delta (i,(1 : A)))) := rfl

end

open KervaireRegular KervaireSpectral
variable {D A : Type*} [Fintype D] [Group A]

end KervaireMatrix

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.PhaseDimension ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder

namespace KervaireSpectral

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

end

section
open KervaireTraceCalculus
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [FiniteDimensional ℂ H] in
/-- The sum of vector functionals over an ONB is precisely algebraic trace. -/
theorem vectorSum_onb (b : OrthonormalBasis ι ℂ H) (T : Operator H) :
    vectorSum b T = LinearMap.trace ℂ H T.toLinearMap := by
  rw [LinearMap.trace_eq_sum_inner _ b, vectorSum_apply]
  rfl

end

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]
variable {ι : Type*} [Fintype ι]

end KervaireSpectral

namespace KervaireMatrix
open KervaireRegular KervaireSpectral KervaireTraceCalculus
open scoped Classical
variable {D A : Type*} [Fintype D] [Group A]

omit [Group A] in
/-- The ordinary finite-dimensional operator trace has the matrix entries used
by the amplification trace; no normalization is introduced here. -/
theorem vectorSum_toEuclideanCLM (M : Matrix D D ℂ) :
    vectorSum (EuclideanSpace.basisFun D ℂ) ((Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)) M) = Matrix.trace M := by
  classical
  rw [vectorSum_onb]
  change LinearMap.trace ℂ (EuclideanSpace ℂ D) (Matrix.toEuclideanLin M) = _
  rw [LinearMap.trace_eq_matrix_trace _ (EuclideanSpace.basisFun D ℂ).toBasis]
  simp only [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]

/-- The cut-sensitive phase of a scalar amplification is the ordinary
finite-dimensional phase, proved through every nonnegative power moment. -/
theorem phase_scalarTensor (M : Matrix D D ℂ) (hM : M ∈ Matrix.unitaryGroup D ℂ) :
    let _ := isStarNormal_of_mem_unitary (scalarTensor_mem_unitary (A := A) hM)
    let _ := isStarNormal_of_mem_unitary (Unitary.map_mem (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)) hM)
    KervaireMatrix.phase (scalarTensor (A := A) M) =
      sumPhase ((Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)) M) (EuclideanSpace.basisFun D ℂ) := by
  classical
  apply sumPhase_eq_of_moments _ _ (scalarTensor_mem_unitary (A := A) hM)
    (Unitary.map_mem (Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)) hM)
    (fun i : D => delta (i,(1 : A))) (EuclideanSpace.basisFun D ℂ)
  intro n
  rw [← trace_eq_vectorSum, ← scalarTensor_pow, trace_scalarTensor,
    ← map_pow, vectorSum_toEuclideanCLM]

end KervaireMatrix

namespace KervaireSpectral
open KervaireTraceCalculus KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]

end KervaireSpectral

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.FixedSpaces ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff
open Matrix

namespace KervaireFixed

section
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
end

section
open Matrix
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
end

section
open KervaireIncidenceCurrent KervaireSignPairing KervaireUnitaryHomotopy
open scoped Matrix.Norms.L2Operator
variable {I K : Type*} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]

end

open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]
end KervaireFixed

namespace KervaireMatrix
open KervaireFixed KervaireSpectral KervaireRegular
open scoped Classical
variable {D A : Type*} [Fintype D] [Group A]

/-- Scalar phase bound from the literal complex fixed-space dimension. -/
lemma phase_scalar_le_codim (M Q : Matrix D D ℂ)
    (hM : M ∈ unitary (Matrix D D ℂ)) (hQ : Q ∈ unitary (Matrix D D ℂ))
    (hc : Q * M * star Q = star M) :
    let _ := isStarNormal_of_mem_unitary (scalarTensor_mem_unitary (A := A) hM)
    KervaireMatrix.phase (scalarTensor (A := A) M) ≤
      ((Fintype.card D : ℝ) - fixedDim M) / 2 := by
  let L := Matrix.toEuclideanCLM (n := D) (𝕜 := ℂ)
  let e := (WithLp.linearEquiv 2 ℂ (D → ℂ)).symm
  let E := (fixedSpace M).map (e : (D → ℂ) →ₗ[ℂ] EuclideanSpace ℂ D)
  have hE (v : E) : L M (v : EuclideanSpace ℂ D) = v := by
    obtain ⟨w,hw,he⟩ := v.property
    rw [← he]
    change WithLp.toLp 2 (M.mulVec w) = WithLp.toLp 2 w
    rw [(mem_fixedSpace M w).mp hw]
  have hML := Unitary.map_mem L hM
  have hQL := Unitary.map_mem L hQ
  have hcL : L Q * L M * star (L Q) = star (L M) := by
    rw [← map_star, ← map_mul, ← map_mul,hc,map_star]
  let _ := isStarNormal_of_mem_unitary hML
  let _ := isStarNormal_of_mem_unitary (scalarTensor_mem_unitary (A := A) hM)
  change KervaireMatrix.phase (scalarTensor (A := A) M) ≤ _
  rw [phase_scalarTensor M hM]
  have h := sumPhase_le_half_codim (L M) (L Q) hML hQL hcL
    (EuclideanSpace.basisFun D ℂ) E hE
  have hd : Module.finrank ℂ E = fixedDim M := e.finrank_map_eq (fixedSpace M)
  rw [hd] at h
  simpa only [finrank_euclideanSpace] using h
end KervaireMatrix

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireMatrix
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff
open Matrix
open KervaireFixed KervaireSpectral KervaireRegular
open scoped Classical


theorem solution : type_of% @_root_.OAI.KervaireMatrix.phase_scalar_le_codim := @_root_.OAI.KervaireMatrix.phase_scalar_le_codim
