-- Prove2me | solution 1 for OAI.KervaireSpectral.vectorPhase_eq_zero_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:38:08.00066+00:00
-- url     : https://prove2.me/submissions/300c2c52-792d-461b-92da-0832fb63e9dc

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/PhaseFaithfulness.lean:L91-L107
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireSpectral.vectorPhase_eq_zero_of_fixed. The node keeps its source
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

/-- Its calculus is the positive square of `U - I`. -/
theorem distanceSq_calculus (U : Operator H) [hU : IsStarNormal U] :
    cfcHom hU (complexify (distanceSq U)) = star (U - 1) * (U - 1) := by
  let idMap : C(spectrum ℂ U, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩
  have hf : complexify (distanceSq U) = star (idMap - 1) * (idMap - 1) := by
    ext z
    exact Complex.normSq_eq_conj_mul_self
  rw [hf, map_mul, map_star, map_sub, map_one]
  have hid : cfcHom hU idMap = U := cfcHom_id (R := ℂ) hU
  rw [hid]

/-- The scalar spectral measure recovers the norm of the displacement. -/
theorem integral_distanceSq (U : Operator H) [hU : IsStarNormal U] (ξ : H) :
    ∫ z, distanceSq U z ∂vectorMeasure U ξ = ‖U ξ - ξ‖ ^ 2 := by
  rw [integral_vectorMeasure, distanceSq_calculus]
  change (inner ℂ ξ (star (U - 1) ((U - 1) ξ))).re = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ((U - 1) ξ)

end KervaireSpectral

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

end KervaireRegular

namespace KervaireSpectral
open KervaireTraceCalculus
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Fixed vectors carry zero phase, including the atom at the phase cut. -/
theorem vectorPhase_eq_zero_of_fixed (U : Operator H) (hU : U ∈ unitary (Operator H))
    (ξ : H) (hξ : U ξ = ξ) :
    let _ := isStarNormal_of_mem_unitary hU
    vectorPhase U ξ = 0 := by
  let _ := isStarNormal_of_mem_unitary hU
  have hh : ∫ z, distanceSq U z ∂vectorMeasure U ξ = 0 := by
    simp [integral_distanceSq, hξ]
  have hi : Integrable (distanceSq U) (vectorMeasure U ξ) :=
    (distanceSq U).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hd : (fun z => distanceSq U z) =ᵐ[vectorMeasure U ξ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun z => Complex.normSq_nonneg _) hi).mp hh
  have hp : (fun z : spectrum ℂ U => phase z) =ᵐ[vectorMeasure U ξ] 0 := by
    filter_upwards [hd] with z hz
    have hz' : (z : ℂ) = 1 := sub_eq_zero.mp (Complex.normSq_eq_zero.mp hz)
    simp [hz']
  exact (integral_congr_ae hp).trans (integral_zero _ _)

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
open KervaireTraceCalculus


theorem solution : type_of% @_root_.OAI.KervaireSpectral.vectorPhase_eq_zero_of_fixed := @_root_.OAI.KervaireSpectral.vectorPhase_eq_zero_of_fixed
