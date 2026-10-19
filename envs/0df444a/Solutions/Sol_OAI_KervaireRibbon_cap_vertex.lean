-- Prove2me | solution 1 for OAI.KervaireRibbon.cap_vertex
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:33:10.581581+00:00
-- url     : https://prove2.me/submissions/5521af2a-80c6-4677-a4fb-ac0b89193781

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
import Definitions.Def_OAI_GroupTheory_Kervaire_Traversal
import Definitions.Def_OAI_GroupTheory_Kervaire_BoundaryFlow
import Definitions.Def_OAI_GroupTheory_Kervaire_RelatorRigidity

open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {D A : Type*} [Fintype D] [DecidableEq D] [Group A]


omit [Fintype D] in
theorem solution (σ : Perm D) {x y : D} (hxy : x ≠ y) (hs : σ x = y) (hz : σ y ≠ x) :
    erase (erase σ x) y = swap x y * (swap x (σ y) * σ) := by
  have hyy : σ y ≠ y := fun h => hxy (σ.injective (by rw [hs, h]))
  have h1 : erase σ x = swap x y * σ := by simp [erase, hs]
  have h2 : (swap x y * σ) y = σ y := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hz hyy]
  rw [h1, erase, h2]
  ext d
  simp only [Perm.mul_apply]
  generalize σ d = e
  generalize hc : σ y = c at hz hyy
  by_cases e1 : e = x
  · subst e1; rw [swap_apply_left, swap_apply_left, swap_apply_left, swap_apply_of_ne_of_ne hz hyy]
  by_cases e2 : e = y
  · subst e2; rw [swap_apply_right, swap_apply_of_ne_of_ne hxy (Ne.symm hz), swap_apply_of_ne_of_ne (Ne.symm hxy) (Ne.symm hyy), swap_apply_right]
  by_cases e3 : e = c
  · subst e3; rw [swap_apply_of_ne_of_ne hz hyy, swap_apply_right, swap_apply_right, swap_apply_left]
  rw [swap_apply_of_ne_of_ne e1 e2, swap_apply_of_ne_of_ne e2 e3, swap_apply_of_ne_of_ne e1 e3, swap_apply_of_ne_of_ne e1 e2]

