-- Prove2me | solution 2 for OAI.KervaireFixed.fixedDim_reindex
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:36:43.359068+00:00
-- url     : https://prove2.me/submissions/f0640c5d-bf4f-4a4a-99bd-a03e6fb0e683

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/FixedSpaces.lean:L46-L63
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireFixed.fixedDim_reindex. The node keeps its source
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
lemma mulVecLin_sub_one (M : Matrix I I ℂ) :
    (M-1).mulVecLin = M.mulVecLin - LinearMap.id := by
  ext v i
  simp

lemma fixedDim_reindex (e : I ≃ J) (M : Matrix I I ℂ) :
    fixedDim (Matrix.reindex e e M) = fixedDim M := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (M - 1).mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker ((Matrix.reindex e e M) - 1).mulVecLin
  have hm : (Matrix.reindex e e M) - 1 = Matrix.reindex e e (M - 1) := by
    change (Matrix.reindexAlgEquiv ℂ ℂ e) M - 1 = (Matrix.reindexAlgEquiv ℂ ℂ e) (M-1)
    rw [map_sub,map_one]
  have hr := Matrix.rank_reindex e e (M-1)
  change Module.finrank ℂ (LinearMap.range ((Matrix.reindex e e (M-1)).mulVecLin)) =
    Module.finrank ℂ (LinearMap.range (M-1).mulVecLin) at hr
  rw [← hm] at hr
  rw [mulVecLin_sub_one] at h1 h2 hr
  rw [mulVecLin_sub_one] at hr
  rw [hr] at h2
  have hc := Fintype.card_congr e
  simp only [Module.finrank_fintype_fun_eq_card] at h1 h2
  unfold fixedDim
  omega
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

end KervaireMatrix

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireFixed
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


theorem solution : type_of% @_root_.OAI.KervaireFixed.fixedDim_reindex := @_root_.OAI.KervaireFixed.fixedDim_reindex
