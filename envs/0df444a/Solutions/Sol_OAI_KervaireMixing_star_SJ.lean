-- Prove2me | solution 1 for OAI.KervaireMixing.star_SJ
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:47:26.926107+00:00
-- url     : https://prove2.me/submissions/c34f613f-4af0-4775-ba10-c0e20bcab1a3

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/MixingOperators.lean:L119-L137
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireMixing.star_SJ. The node keeps its source
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

/-- The exact corner reversal makes SJ self-adjoint for every mixer X. -/
theorem star_SJ (ρ : Equiv.Perm I) (a : I → A) (X : Matrix K K ℂ) :
    star (S ρ a * J (I := I) X) = S ρ a * J (I := I) X := by
  apply star_eq_of_coefficients
  rintro ⟨⟨k|k,i⟩,x⟩ ⟨⟨l|l,j⟩,y⟩ <;>
    simp only [S, J, mul_apply_eq_comp, labelledShift_apply, scalarTensor_delta]
    <;> simp [labels, successor, mixingMatrix, blockDiagonal_apply, fromBlocks]
  · by_cases h : ρ j = i
    · subst i
      simp only [Equiv.symm_apply_apply, ↓reduceIte, eq_inv_mul_iff_mul_eq]
      split_ifs <;> simp_all
    · have h' : ρ.symm i ≠ j := by intro hh; apply h; rw [← hh, ρ.apply_symm_apply]
      simp [h,h']
  · by_cases h : ρ i = j
    · subst j
      simp only [Equiv.symm_apply_apply, ↓reduceIte, eq_inv_mul_iff_mul_eq]
      split_ifs <;> simp_all
    · have h' : ρ.symm j ≠ i := by intro hh; apply h; rw [← hh, ρ.apply_symm_apply]
      simp [h,h']

end
open Matrix KervaireMatrix KervaireRegular KervaireSpectral
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A]

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
open Matrix KervaireMatrix KervaireRegular
open scoped Classical


theorem solution : type_of% @_root_.OAI.KervaireMixing.star_SJ := @_root_.OAI.KervaireMixing.star_SJ
