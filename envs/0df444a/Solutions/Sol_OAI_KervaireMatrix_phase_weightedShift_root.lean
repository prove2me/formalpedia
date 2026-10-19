-- Prove2me | solution 1 for OAI.KervaireMatrix.phase_weightedShift_root
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:24:24.492014+00:00
-- url     : https://prove2.me/submissions/fa697703-5934-43f1-b785-86dcfbded903

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/WeightedCycles.lean:L46-L70
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireMatrix.phase_weightedShift_root. The node keeps its source
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
import Theorems.Thm_OAI_KervaireMatrix_trace_mul_comm
import Theorems.Thm_OAI_KervaireSpectral_hasSum_spectralLog
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

theorem mem_algebra (T : Operator D A) : T ∈ algebra ↔ InCommutant T := by
  rw [algebra, KervaireCentralizer.algebra, StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h a
    exact ((h (right (D := D) a) ⟨a,rfl⟩).1).symm
  · intro h R hR
    obtain ⟨a,rfl⟩ := hR
    rw [right_star]
    exact ⟨(h a).symm, (h a⁻¹).symm⟩

variable [Fintype D]

/-- The vector family agrees exactly with the unnormalized matrix trace. -/
theorem trace_eq_vectorSum : (trace : Operator D A →L[ℂ] ℂ) =
    vectorSum (fun i : D => (delta (i,(1 : A)))) := rfl

end

open KervaireRegular KervaireSpectral
variable {D A : Type*} [Fintype D] [Group A]

omit [Fintype D] in
theorem InCommutant.mul {S T : Operator D A} (hS : InCommutant S) (hT : InCommutant T) :
    InCommutant (S*T) := fun a => (hS a).mul_left (hT a)

omit [Fintype D] in
theorem InCommutant.pow {S : Operator D A} (hS : InCommutant S) (n : ℕ) :
    InCommutant (S^n) := fun a => (hS a).pow_left n

omit [Fintype D] in
theorem InCommutant.star {S : Operator D A} (hS : InCommutant S) :
    InCommutant (star S) :=
  (mem_algebra _).mp (star_mem ((mem_algebra S).mpr hS))

omit [Fintype D] [Group A] in
/-- Telescope powers without a finite-dimensional restriction on the Hilbert space. -/
theorem conjugate_pow (U Q : Operator D A) (hQ : Q ∈ unitary (Operator D A)) (n : ℕ) :
    (Q*U*star Q)^n = Q*U^n*star Q := by
  induction n with
  | zero => simpa using (Unitary.mem_iff.mp hQ).2.symm
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    calc (Q * U^n * star Q) * (Q * U * star Q) =
        Q * U^n * (star Q * Q) * U * star Q := by noncomm_ring
         _ = Q * (U^n * U) * star Q := by rw [(Unitary.mem_iff.mp hQ).1]; noncomm_ring

/-- Conjugation invariance of the exact phase in the arbitrary-group regular algebra. -/
theorem phase_conjugate (U Q : Operator D A)
    (hU : U ∈ unitary (Operator D A)) (hQ : Q ∈ unitary (Operator D A))
    (hUc : InCommutant U) (hQc : InCommutant Q) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary (mul_mem (mul_mem hQ hU) (Unitary.star_mem hQ))
    KervaireMatrix.phase (Q*U*star Q) = KervaireMatrix.phase U := by
  apply sumPhase_eq_of_moments _ _
    (mul_mem (mul_mem hQ hU) (Unitary.star_mem hQ)) hU
    (fun i : D => delta (i,(1 : A))) (fun i : D => delta (i,(1 : A)))
  intro n
  rw [← trace_eq_vectorSum, conjugate_pow U Q hQ n,
    trace_mul_comm (hQc.mul (hUc.pow n)) hQc.star, ← mul_assoc,
    (Unitary.mem_iff.mp hQ).1, one_mul]

end KervaireMatrix

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.MatrixShifts ----
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
open scoped Classical
variable {D A : Type*}

variable [Fintype D]

variable [Group A]

/-- Scalar matrices lie in exactly the commutant required by the phase theorem. -/
theorem scalarTensor_mem_commutant (M : Matrix D D ℂ) :
    InCommutant (scalarTensor (A := A) M) := by
  intro a
  change scalarTensor M * (right (D := D) a).toContinuousLinearEquiv.toContinuousLinearMap = _
  ext f ⟨d,x⟩
  simp [mul_apply_eq_comp]

end

open KervaireRegular
open scoped Classical
variable {D A : Type*} [Group A]

/-- The commutant contains every group-labelled shift. -/
theorem labelledShift_mem_commutant (σ : Equiv.Perm D) (a : D → A) :
    InCommutant (labelledShift σ a) := by
  intro x
  change labelledShift σ a * (right (D := D) x : Operator D A) = _
  ext f ⟨d,y⟩
  simp [mul_apply_eq_comp, mul_assoc]

variable [Fintype D]

theorem weightedShift_mem_commutant (σ : Equiv.Perm D) (u : D → ℂ) (a : D → A) :
    InCommutant (weightedShift σ u a) := by
  intro x
  exact (labelledShift_mem_commutant σ a x).mul_left
    (scalarTensor_mem_commutant (Matrix.diagonal u) x)

end KervaireMatrix
namespace KervaireSpectral
end KervaireSpectral

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.WeightedCycles ----
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
open KervaireRegular KervaireSpectral
variable {A : Type*} [Group A]

/-- The finite clock advances by a root of unity, including at the cut. -/
theorem clock_rotate {n : ℕ} (z : ℂ) (hz : z^(n+1) = 1) (i : Fin (n+1)) :
    z^((finRotate (n+1) i).val) = z * z^i.val := by
  by_cases hi : i = Fin.last n
  · subst i
    simp only [finRotate_last, Fin.val_zero, pow_zero, Fin.val_last]
    rw [← pow_succ']
    exact hz.symm
  · rw [coe_finRotate_of_ne_last hi, pow_succ']

/-- Rephasing a labelled weighted cycle implements scalar rotation exactly. -/
theorem clock_weightedShift (n : ℕ) (z : ℂ) (hz : z^(n+1) = 1)
    (u : Fin (n+1) → ℂ) (a : Fin (n+1) → A) :
    scalarDiagonal (A := A) (fun i : Fin (n+1) => z^i.val) *
        weightedShift (finRotate (n+1)) u a =
      z • (weightedShift (finRotate (n+1)) u a *
        scalarDiagonal (fun i : Fin (n+1) => z^i.val)) := by
  apply ext_delta
  rintro ⟨i,x⟩
  simp only [mul_apply_eq_comp, weightedShift_delta, map_smul,
    scalarDiagonal_delta, smul_apply, smul_smul]
  rw [clock_rotate z hz i]
  congr 1
  ring

/-- Spectral phase of a finite weighted cycle is invariant under every clock rotation. -/
theorem phase_weightedShift_root (n : ℕ) (z : ℂ) (hz : z^(n+1) = 1)
    (hzu : z ∈ unitary ℂ) (u : Fin (n+1) → ℂ) (a : Fin (n+1) → A)
    (hu : ∀ i, u i ∈ unitary ℂ) :
    let _ := isStarNormal_of_mem_unitary (weightedShift_unitary (finRotate (n+1)) u a hu)
    let _ := isStarNormal_of_mem_unitary
      (Unitary.smul_mem ⟨z,hzu⟩ (weightedShift_unitary (finRotate (n+1)) u a hu))
    KervaireMatrix.phase (z • weightedShift (finRotate (n+1)) u a) =
      KervaireMatrix.phase (weightedShift (finRotate (n+1)) u a) := by
  classical
  let : DecidableEq (Fin (n+1)) := Classical.decEq _
  let T := weightedShift (finRotate (n+1)) u a
  let Q := scalarDiagonal (A := A) (fun i : Fin (n+1) => z^i.val)
  have hT : T ∈ unitary (Operator (Fin (n+1)) A) := weightedShift_unitary (finRotate (n+1)) u a hu
  have hQ : Q ∈ unitary (Operator (Fin (n+1)) A) :=
    scalarDiagonal_unitary _ (fun i => pow_mem hzu i.val)
  have hc : Q*T*star Q = z • T := by
    rw [show Q*T = z • (T*Q) from clock_weightedShift n z hz u a,
      smul_mul_assoc, mul_assoc, (Unitary.mem_iff.mp hQ).2, mul_one]
  let _ := isStarNormal_of_mem_unitary hT
  let _ := isStarNormal_of_mem_unitary (Unitary.smul_mem ⟨z,hzu⟩ hT)
  simpa only [hc] using phase_conjugate T Q hT hQ
    (weightedShift_mem_commutant _ u a)
    (by simpa only [Q, scalarDiagonal] using
      scalarTensor_mem_commutant (A := A) (Matrix.diagonal (fun i : Fin (n+1) => z^i.val)))

end KervaireMatrix
namespace KervaireSpectral
open KervaireTraceCalculus
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

end KervaireSpectral

namespace KervaireRegular
open KervaireSpectral
open scoped Classical
variable {A : Type*} [Group A]

end KervaireRegular

namespace KervaireMatrix
open KervaireRegular KervaireSpectral
variable {D A : Type*} [Fintype D] [Group A]

end KervaireMatrix
namespace KervaireCycle
open Fin.NatCast
variable {D B : Type*} [Monoid B]

end KervaireCycle

namespace KervaireMatrix
open KervaireRegular KervaireCycle
variable {D A : Type*} [Fintype D] [Group A]

end KervaireMatrix
namespace KervaireCycle
variable {D B : Type*} [Monoid B]

end KervaireCycle

namespace KervaireMatrix
open KervaireRegular KervaireSpectral KervaireCycle
open Fin.NatCast
variable {A : Type*} [Group A]

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
open KervaireRegular KervaireSpectral


theorem solution : type_of% @_root_.OAI.KervaireMatrix.phase_weightedShift_root := @_root_.OAI.KervaireMatrix.phase_weightedShift_root
