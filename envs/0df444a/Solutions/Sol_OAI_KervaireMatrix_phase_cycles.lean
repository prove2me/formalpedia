-- Prove2me | solution 1 for OAI.KervaireMatrix.phase_cycles
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:51:43.698251+00:00
-- url     : https://prove2.me/submissions/3d8d5592-3538-44d8-8a20-642fcdaaf596

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/MixingOperators.lean:L204-L230
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireMatrix.phase_cycles. The node keeps its source
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
import Theorems.Thm_OAI_KervaireMatrix_phase_weightedCycle
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

end

open KervaireRegular
open scoped Classical
variable {D A : Type*} [Group A]

variable [Fintype D]

/-- Multiplication proves the exact order of coefficient inverses on every boundary step. -/
theorem weightedShift_mul (σ τ : Equiv.Perm D) (u v : D → ℂ) (a b : D → A) :
    weightedShift σ u a * weightedShift τ v b =
      weightedShift (σ*τ) (fun d => u (τ d)*v d) (fun d => a (τ d)*b d) := by
  apply ext_delta
  rintro ⟨d,x⟩
  simp [mul_apply_eq_comp, smul_smul, mul_assoc, mul_comm (v d)]

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

end KervaireMatrix
namespace KervaireSpectral
open KervaireTraceCalculus
variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem vectorPhase_eq_of_moments (U : Operator H) (V : Operator K)
    (hU : U ∈ unitary (Operator H)) (hV : V ∈ unitary (Operator K))
    (ξ : H) (η : K)
    (hm : ∀ n : ℕ, inner ℂ ξ ((U^n) ξ) = inner ℂ η ((V^n) η)) :
    let _ := isStarNormal_of_mem_unitary hU
    let _ := isStarNormal_of_mem_unitary hV
    vectorPhase U ξ = vectorPhase V η := by
  simpa only [sumPhase, vectorSum_apply, Fintype.sum_unique] using
    sumPhase_eq_of_moments U V hU hV (fun _ : Unit => ξ) (fun _ : Unit => η)
      (fun n => by simpa only [vectorSum_apply, Fintype.sum_unique, vectorCLM_apply] using hm n)
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

/-- Exact powers of the scalar/group-labelled shift. -/
theorem weightedShift_pow (σ : Equiv.Perm D) (u : D → ℂ) (a : D → A) (n : ℕ) :
    weightedShift σ u a ^ n = weightedShift (σ^n)
      (orbitWeight σ u n) (orbitWeight σ a n) := by
  induction n with
  | zero =>
    change 1 = labelledShift (Equiv.refl D) (fun _ => 1) * scalarDiagonal (fun _ => 1)
    rw [labelledShift_one, scalarDiagonal_one, mul_one]
  | succ n ih => rw [pow_succ', ih, weightedShift_mul, pow_succ']; rfl

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

-- ---- from OAI.GroupTheory.Kervaire.MixingOperators ----
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

namespace KervaireMixing

section
open Matrix KervaireMatrix KervaireRegular
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A]

end
open Matrix KervaireMatrix KervaireRegular KervaireSpectral
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A]

end KervaireMixing
namespace KervaireCycle
variable {D E B : Type*} [Monoid B]
lemma perm_pow_embedding (σ : Equiv.Perm D) (τ : Equiv.Perm E) (e : E → D)
    (he : ∀ i, σ (e i) = e (τ i)) (n : ℕ) (i : E) :
    (σ^n) (e i) = e ((τ^n) i) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ',Equiv.Perm.mul_apply,ih,he]
lemma orbitWeight_embedding (σ : Equiv.Perm D) (τ : Equiv.Perm E) (e : E → D)
    (he : ∀ i, σ (e i) = e (τ i)) (b : D → B) (n : ℕ) (i : E) :
    orbitWeight σ b n (e i) = orbitWeight τ (b ∘ e) n i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [orbitWeight_succ,orbitWeight_succ,perm_pow_embedding σ τ e he,ih]; rfl
end KervaireCycle
namespace KervaireMatrix
open KervaireRegular KervaireSpectral KervaireTraceCalculus KervaireCycle
open scoped Classical
variable {D E A : Type*} [Fintype D] [Fintype E] [Group A]
omit [Fintype E] in
lemma weightedShift_moment (σ : Equiv.Perm D) (u : D → ℂ) (a : D → A) (n : ℕ) (i : D) :
    inner ℂ (delta (i,(1 : A))) ((weightedShift σ u a ^ n) (delta (i,1))) =
      if (σ^n) i = i ∧ orbitWeight σ a n i = 1 then orbitWeight σ u n i else 0 := by
  rw [weightedShift_pow,weightedShift_delta,inner_smul_right,inner_delta_left]
  simp [delta,Pi.single_apply,Prod.mk.injEq,eq_comm]

lemma vectorPhase_cycle_embedding (σ : Equiv.Perm D) (τ : Equiv.Perm E)
    (e : E ↪ D) (he : ∀ i, σ (e i) = e (τ i))
    (u : D → ℂ) (a : D → A) (hu : ∀ i, u i ∈ unitary ℂ) (i : E) :
    let _ := isStarNormal_of_mem_unitary (weightedShift_unitary σ u a hu)
    let _ := isStarNormal_of_mem_unitary (weightedShift_unitary τ (u ∘ e) (a ∘ e) (fun j ↦ hu (e j)))
    vectorPhase (weightedShift σ u a) (delta (e i,(1 : A))) =
      vectorPhase (weightedShift τ (u ∘ e) (a ∘ e)) (delta (i,(1 : A))) := by
  apply vectorPhase_eq_of_moments _ _ (weightedShift_unitary σ u a hu)
    (weightedShift_unitary τ (u ∘ e) (a ∘ e) (fun j ↦ hu (e j))) _ _
  intro n
  rw [weightedShift_moment,weightedShift_moment,perm_pow_embedding σ τ e he,
    orbitWeight_embedding σ τ e he,orbitWeight_embedding σ τ e he]
  simp only [EmbeddingLike.apply_eq_iff_eq]

/-- Exact cyclewise decomposition of boundary phase; all circuit words are in A. -/
lemma phase_cycles {Z : Type*} [Fintype Z] (n : Z → ℕ)
    (e : (Σ z, Fin (n z+1)) ≃ D) (σ : Equiv.Perm D)
    (he : ∀ z i, σ (e ⟨z,i⟩) = e ⟨z,finRotate (n z+1) i⟩)
    (u : D → ℂ) (a : D → A) (hu : ∀ i, u i ∈ unitary ℂ) :
    let _ := isStarNormal_of_mem_unitary (weightedShift_unitary σ u a hu)
    KervaireMatrix.phase (weightedShift σ u a) =
      ∑ z, ((n z : ℝ)/2 + groupPhase
        (orbitWeight (finRotate (n z+1)) (fun i ↦ u (e ⟨z,i⟩)) (n z+1) 0)
        (orbitWeight_mem (unitary ℂ) _ _ (fun i ↦ hu (e ⟨z,i⟩)) _ _)
        (orbitWeight (finRotate (n z+1)) (fun i ↦ a (e ⟨z,i⟩)) (n z+1) 0)) := by
  let _ := isStarNormal_of_mem_unitary (weightedShift_unitary σ u a hu)
  change (∑ i : D, vectorPhase (weightedShift σ u a) (delta (i,(1 : A)))) = _
  rw [← e.sum_comp,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro z _
  let ez : Fin (n z+1) ↪ D := ⟨fun i ↦ e ⟨z,i⟩, fun i j h ↦ by
    exact eq_of_heq (Sigma.mk.inj_iff.mp (e.injective h)).2⟩
  have hz (i : Fin (n z+1)) := vectorPhase_cycle_embedding σ (finRotate (n z+1)) ez
    (he z) u a hu i
  let _ := isStarNormal_of_mem_unitary
    (weightedShift_unitary (finRotate (n z+1)) (u ∘ ez) (a ∘ ez) (fun i ↦ hu (ez i)))
  trans KervaireMatrix.phase (weightedShift (finRotate (n z+1)) (u ∘ ez) (a ∘ ez))
  · apply Finset.sum_congr rfl
    intro i _
    exact hz i
  · exact phase_weightedCycle (n z) (u ∘ ez) (a ∘ ez) (fun i ↦ hu (ez i))
end KervaireMatrix

namespace KervaireRegular
open KervaireSpectral KervaireTraceCalculus MeasureTheory
variable {A : Type*} [Group A]

end KervaireRegular

namespace KervaireCycle
open KervaireSpectral
variable {D B : Type*} [CommMonoid B]
end KervaireCycle

namespace KervaireBoundary
open KervaireCycle KervaireSpectral KervaireMatrix KervaireRegular
open scoped Classical
variable {D Z A : Type*} [Fintype D] [Fintype Z] [Group A]

end KervaireBoundary

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
open KervaireRegular KervaireSpectral KervaireTraceCalculus KervaireCycle
open scoped Classical


theorem solution : type_of% @_root_.OAI.KervaireMatrix.phase_cycles := @_root_.OAI.KervaireMatrix.phase_cycles
