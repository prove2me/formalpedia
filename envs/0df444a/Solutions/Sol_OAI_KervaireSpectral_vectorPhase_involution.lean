-- Prove2me | solution 1 for OAI.KervaireSpectral.vectorPhase_involution
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:45:32.948735+00:00
-- url     : https://prove2.me/submissions/c632912e-2e14-412e-9e00-910f61e2a40a

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/PhaseDimension.lean:L250-L274
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireSpectral.vectorPhase_involution. The node keeps its source
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

-- ---- from OAI.GroupTheory.Kervaire.SpectralMeasures ----
namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology

namespace KervaireSpectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- The defining integration identity for the scalar spectral measure. -/
theorem integral_vectorMeasure (U : Operator H) [hU : IsStarNormal U] (ξ : H)
    (f : C(spectrum ℂ U, ℝ)) :
    ∫ z, f z ∂vectorMeasure U ξ = (inner ℂ ξ (cfcHom hU (complexify f) ξ)).re := by
  let fc : C_c(spectrum ℂ U, ℝ) := ⟨f, HasCompactSupport.of_compactSpace f⟩
  exact RealRMK.integral_rieszMeasure (vectorFunctional U ξ) fc

end KervaireSpectral

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

/-- A scalar point of the spectrum of an involution is exactly a sign. -/
theorem spectrum_involution {U : Operator H} (hU : U ^ 2 = 1) (z : spectrum ℂ U) :
    (z : ℂ) = 1 ∨ (z : ℂ) = -1 := by
  have hz : (z : ℂ)^2 ∈ spectrum ℂ (U^2) := by
    rw [spectrum.map_pow]
    exact ⟨z,z.property,rfl⟩
  rw [hU] at hz
  exact sq_eq_one_iff.mp (by simpa using hz)

/-- Spectral phase on a self-adjoint unitary is one half of its negative projection. -/
theorem vectorPhase_involution (U : Operator H) (hU : U ∈ unitary (Operator H))
    (hUU : U ^ 2 = 1) (ξ : H) :
    let _ := isStarNormal_of_mem_unitary hU
    vectorPhase U ξ = ((vectorCLM ξ 1).re - (vectorCLM ξ U).re) / 4 := by
  let hN := isStarNormal_of_mem_unitary hU
  let f : C(spectrum ℂ U, ℝ) :=
    ⟨fun z => (1 - (z : ℂ).re) / 4,
      (continuous_const.sub (Complex.continuous_re.comp continuous_subtype_val)).div_const _⟩
  have he : (fun z : spectrum ℂ U => phase z) = f := by
    funext z
    rcases spectrum_involution hUU z with hz | hz
    · simp [f, phase, hz]
    · simp only [f, ContinuousMap.coe_mk, hz, phase, Complex.arg_neg_one]
      rw [show Real.pi / (2 * Real.pi) = (1/2 : ℝ) by field_simp]
      norm_num [Int.fract_eq_self.mpr (by norm_num : (0:ℝ) ≤ 1/2 ∧ (1/2:ℝ) < 1)]
  have hf : complexify f = (1 / 4 : ℂ) •
      (1 - (ContinuousMap.id ℂ).restrict (spectrum ℂ U)) := by
    ext z
    rcases spectrum_involution hUU z with hz | hz <;>
      simp [complexify, f, hz]; norm_num
  change (∫ z, phase z ∂vectorMeasure U ξ) = _
  rw [he, integral_vectorMeasure, hf, map_smul, map_sub, map_one, cfcHom_id]
  simp [Complex.sub_re, Complex.mul_re]
  ring

end KervaireSpectral

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireSpectral
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
open KervaireTraceCalculus KervaireScalarPhase


theorem solution : type_of% @_root_.OAI.KervaireSpectral.vectorPhase_involution := @_root_.OAI.KervaireSpectral.vectorPhase_involution
