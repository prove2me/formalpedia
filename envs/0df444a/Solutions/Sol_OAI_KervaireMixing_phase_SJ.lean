-- Prove2me | solution 1 for OAI.KervaireMixing.phase_SJ
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:49:54.211994+00:00
-- url     : https://prove2.me/submissions/b002a2c0-f2b2-4abf-93fb-9acddb2d3524

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/MixingOperators.lean:L144-L161
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireMixing.phase_SJ. The node keeps its source
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
import Theorems.Thm_OAI_KervaireMixing_star_SJ
import Theorems.Thm_OAI_KervaireSpectral_vectorPhase_involution

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

end

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]
variable {ι : Type*} [Fintype ι]

end KervaireSpectral

namespace KervaireMatrix
open KervaireRegular KervaireSpectral KervaireTraceCalculus
open scoped Classical
variable {D A : Type*} [Fintype D] [Group A]

end KervaireMatrix

namespace KervaireSpectral
open KervaireTraceCalculus KervaireScalarPhase
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]

/-- The unnormalized matrix version used for the involution SJ. -/
theorem sumPhase_involution {ι : Type*} [Fintype ι]
    (U : Operator H) (hU : U ∈ unitary (Operator H)) (hUU : U ^ 2 = 1) (ξ : ι → H) :
    let _ := isStarNormal_of_mem_unitary hU
    sumPhase U ξ = ((vectorSum ξ 1).re - (vectorSum ξ U).re) / 4 := by
  let _ := isStarNormal_of_mem_unitary hU
  unfold sumPhase
  simp only [vectorPhase_involution U hU hUU, vectorSum_apply, Complex.re_sum,
    ]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]

end KervaireSpectral

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

/-- The mixed shift exchanges disk kinds, so its unnormalized trace is zero. -/
theorem trace_SJ (ρ : Equiv.Perm I) (a : I → A) (X : Matrix K K ℂ) :
    KervaireMatrix.trace (S ρ a * J (I := I) X) = 0 := by
  rw [KervaireMatrix.trace_apply]
  simp only [inner_delta_left]
  apply Finset.sum_eq_zero
  rintro ⟨k|k,i⟩ _ <;>
    simp only [S, J, mul_apply_eq_comp, labelledShift_apply, scalarTensor_delta]
    <;> simp [successor, mixingMatrix, blockDiagonal_apply, fromBlocks]

end
open Matrix KervaireMatrix KervaireRegular KervaireSpectral
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A]

/-- The exact phase identity at arbitrary group coefficients. -/
theorem phase_SJ [Nonempty I] [Nonempty K]
    (ρ : Equiv.Perm I) (a : I → A) (X : Matrix.unitaryGroup K ℂ) :
    let _ := isStarNormal_of_mem_unitary
      ((unitary _).mul_mem (S_unitary (K := K) ρ a) (J_unitary (I := I) X))
    KervaireMatrix.phase (S ρ a * J (I := I) (X : Matrix K K ℂ)) =
      (Fintype.card I : ℝ) * Fintype.card K / 2 := by
  have hU := (unitary _).mul_mem (S_unitary (K := K) ρ a) (J_unitary (I := I) X)
  let _ := isStarNormal_of_mem_unitary hU
  have hsq : (S ρ a * J (I := I) (X : Matrix K K ℂ)) ^ 2 = 1 := by
    simpa only [pow_two, star_SJ] using hU.1
  rw [KervaireMatrix.phase, sumPhase_involution _ hU hsq,
    ← trace_eq_vectorSum, KervaireMatrix.trace_one, trace_SJ]
  simp only [Complex.zero_re, sub_zero,
    Slot, Fintype.card_prod, Fintype.card_sum, Nat.cast_mul, Nat.cast_add]
  simp only [Complex.mul_re, Complex.add_re, Complex.natCast_re,
    Complex.natCast_im, mul_zero, sub_zero]
  ring

end KervaireMixing
namespace KervaireCycle
variable {D E B : Type*} [Monoid B]
end KervaireCycle
namespace KervaireMatrix
open KervaireRegular KervaireSpectral KervaireTraceCalculus KervaireCycle
open scoped Classical
variable {D E A : Type*} [Fintype D] [Fintype E] [Group A]
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
open OAI OAI.KervaireMixing
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
open Matrix KervaireMatrix KervaireRegular KervaireSpectral
open scoped Classical


theorem solution : type_of% @_root_.OAI.KervaireMixing.phase_SJ := @_root_.OAI.KervaireMixing.phase_SJ
