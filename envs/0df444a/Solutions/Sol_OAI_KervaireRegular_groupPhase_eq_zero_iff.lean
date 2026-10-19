-- Prove2me | solution 1 for OAI.KervaireRegular.groupPhase_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:36:23.613179+00:00
-- url     : https://prove2.me/submissions/bd7f0449-efde-4c87-b363-fa07de5f774c

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/PhaseFaithfulness.lean:L34-L75
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRegular.groupPhase_eq_zero_iff. The node keeps its source
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
import Theorems.Thm_OAI_KervaireRegular_eq_zero_of_delta_one
import Theorems.Thm_OAI_KervaireSpectral_exists_phaseOperator

-- ---- from OAI.GroupTheory.Kervaire.RegularOperators ----
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

namespace KervaireRegular

variable {α β γ : Type*}

variable {A : Type*} [Group A]

/-- The commuting left and right regular actions. -/
theorem left_right (a b : A) (f : ℓ²(A, ℂ)) :
    left a (right b f) = right b (left a f) := by ext x; simp [mul_assoc]

/-- Faithfulness in positive-square form, the part needed for positive operators. -/
theorem trace_star_mul_self_eq_zero_iff {T : Operator A} (hT : InCommutant T) :
    trace (star T * T) = 0 ↔ T = 0 := by
  constructor
  · intro h
    apply eq_zero_of_delta_one hT
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [trace_apply] at h
    change inner ℂ (delta 1) (star T (T (delta 1))) = 0 at h
    rwa [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right] at h
  · rintro rfl
    simp

attribute [local instance] OAI.KervaireRegular.instContinuousFunctionalCalculusRealOperatorIsSelfAdjoint
/-- The commutant is closed under the nonnegative continuous square root. -/
theorem InCommutant.sqrt {T : Operator A} (hT : InCommutant T) :
    InCommutant (CFC.sqrt T) := by
  intro a
  exact (hT a).cfcₙ_nnreal NNReal.sqrt

/-- Faithfulness for every nonnegative operator in the commutant. -/
theorem trace_eq_zero_iff_of_nonneg {T : Operator A} (hT : InCommutant T)
    (hpos : 0 ≤ T) : trace T = 0 ↔ T = 0 := by
  have hs : star (CFC.sqrt T) = CFC.sqrt T :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg T)).star_eq
  constructor
  · intro ht
    have hz : trace (star (CFC.sqrt T) * CFC.sqrt T) = 0 := by
      rwa [hs, CFC.sqrt_mul_sqrt_self T hpos]
    have hz' := (trace_star_mul_self_eq_zero_iff hT.sqrt).mp hz
    exact (CFC.sqrt_eq_zero_iff T hpos).mp hz'
  · rintro rfl
    simp

end KervaireRegular

end

end OAI

-- ---- from OAI.GroupTheory.Kervaire.PhaseFaithfulness ----
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

namespace KervaireRegular
open KervaireSpectral
open scoped ComplexOrder
variable {A : Type*} [Group A]

theorem leftOperator_mem (a : A) : InCommutant (leftOperator a) := by
  intro b
  apply ContinuousLinearMap.ext
  intro f
  exact left_right a b f

/-- The endpoint `τ(phase(L(a)))=0 → a=1`, on the full arbitrary group.
The positive trace faithfulness is proved above, not assumed. -/
theorem groupPhase_eq_zero_iff (a : A) : groupPhase 1 (one_mem _) a = 0 ↔ a = 1 := by
  let _ : Nontrivial ℓ²(A, ℂ) := by
    classical
    refine ⟨⟨delta (1 : A), 0, ?_⟩⟩
    intro h
    have hh := congrArg (fun f : ℓ²(A, ℂ) => f 1) h
    simp [delta] at hh
  let _ := isStarNormal_of_mem_unitary (leftOperator_unitary a)
  have hp : groupPhase 1 (one_mem _) a = vectorPhase (leftOperator a) (delta 1) := by
    simp only [groupPhase, one_smul]
  obtain ⟨B,hB,_,_,hexp,hvec,hcomm⟩ := exists_phaseOperator (leftOperator a) (leftOperator_unitary a)
  have hBm : InCommutant B := by
    intro b
    apply hcomm _ (leftOperator_mem a b)
    rw [star_leftOperator]
    exact leftOperator_mem a⁻¹ b
  constructor
  · intro hz
    have hre : (trace B).re = 0 := by rw [trace_apply, hvec, ← hp, hz]
    have him : (trace B).im = 0 := by
      exact (Complex.nonneg_iff.mp (((ContinuousLinearMap.nonneg_iff_isPositive _).mp hB).inner_nonneg_right _)).2.symm
    have hzB : B = 0 := (trace_eq_zero_iff_of_nonneg hBm hB).mp (Complex.ext hre him)
    rw [hzB, smul_zero, NormedSpace.exp_zero] at hexp
    have he : delta (1 : A) = delta a := by
      simpa only [one_apply_eq_self, leftOperator_delta, mul_one] using
        congrArg (fun T : Operator A => T (delta 1)) hexp
    have hv := congrArg (fun f : ℓ²(A, ℂ) => f a) he
    classical
    by_contra ha
    simp [delta, ha] at hv
  · intro ha
    subst a
    simp only [groupPhase, vectorPhase]
    apply MeasureTheory.integral_eq_zero_of_ae
    filter_upwards [] with z
    have hspec : (z : ℂ) ∈ spectrum ℂ (1 : Operator A) := by
      simpa only [one_smul, leftOperator_one] using z.property
    have hz : (z : ℂ) = 1 := by
      simpa only [spectrum.one_eq, Set.mem_singleton_iff] using hspec
    simp [hz]

end KervaireRegular

namespace KervaireSpectral
open KervaireTraceCalculus
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end KervaireSpectral

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireRegular
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open KervaireSpectral
open scoped ComplexOrder


theorem solution : type_of% @_root_.OAI.KervaireRegular.groupPhase_eq_zero_iff := @_root_.OAI.KervaireRegular.groupPhase_eq_zero_iff
