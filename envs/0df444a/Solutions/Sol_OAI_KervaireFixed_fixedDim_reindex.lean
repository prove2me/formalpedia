-- Prove2me | solution 1 for OAI.KervaireFixed.fixedDim_reindex
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:39:53.289451+00:00
-- url     : https://prove2.me/submissions/5ab30948-3f14-486e-8c13-12fd3895cc9f

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
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]


theorem solution (e : I ≃ J) (M : Matrix I I ℂ) :
    fixedDim (Matrix.reindex e e M) = fixedDim M := by
  unfold fixedDim
  let L : (I → ℂ) ≃ₗ[ℂ] (J → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ e.symm
  have hL : ∀ v : I → ℂ, L v = fun j => v (e.symm j) := fun v => rfl
  have key : LinearMap.ker ((Matrix.reindex e e M).mulVecLin - LinearMap.id) =
      (LinearMap.ker (M.mulVecLin - LinearMap.id)).map (L : (I → ℂ) →ₗ[ℂ] (J → ℂ)) := by
    ext w
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, Matrix.mulVecLin_apply, LinearMap.id_apply,
      sub_eq_zero, Submodule.mem_map, LinearEquiv.coe_coe]
    constructor
    · intro hw
      refine ⟨fun i => w (e i), ?_, ?_⟩
      · funext i
        have := congrFun hw (e i)
        simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
          Equiv.symm_apply_apply] at this
        rw [← this, Matrix.mulVec, dotProduct]
        exact (Equiv.sum_comp e.symm _).symm.trans (by simp)
      · funext j; rw [hL]; simp
    · rintro ⟨v, hv, rfl⟩
      funext j
      rw [hL]
      simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply]
      have := congrFun hv (e.symm j)
      rw [← this, Matrix.mulVec, dotProduct]
      exact Equiv.sum_comp e.symm (fun x => M (e.symm j) x * v x)
  rw [key, LinearEquiv.finrank_map_eq]

