-- Prove2me | solution 1 for OAI.KervaireRibbon.circle_formPerm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:36:53.45476+00:00
-- url     : https://prove2.me/submissions/baf0505d-9330-4d40-994f-e8ffe2bf002a

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
import Definitions.Def_OAI_GroupTheory_Kervaire_VertexJoin
import Definitions.Def_OAI_GroupTheory_Kervaire_Circles
import Definitions.Def_OAI_GroupTheory_Kervaire_Splicing
import Definitions.Def_OAI_GroupTheory_Kervaire_Capping
import Definitions.Def_OAI_GroupTheory_Kervaire_OuterRibbon
import Definitions.Def_OAI_GroupTheory_Kervaire_RibbonProducts
import Definitions.Def_OAI_GroupTheory_Kervaire_Conjugation
import Definitions.Def_OAI_GroupTheory_Kervaire_Inversion
import Definitions.Def_OAI_GroupTheory_Kervaire_Realization
import Definitions.Def_OAI_GroupTheory_Kervaire_Annulus
import Definitions.Def_OAI_GroupTheory_Kervaire_WordNormalization

open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {I : Type*} [DecidableEq I]


theorem solution (i : I) (l : List I) (hn : (i::l).Nodup) :
    Circle (i::l).formPerm i l := by
  unfold KervaireRibbon.Circle
  rw [List.isChain_iff_forall_rel_of_append_cons_cons]
  intro a b l₁ l₂ hL
  have hc : i :: (l ++ [i]) = (i :: l) ++ [i] := rfl
  rw [hc] at hL
  have ha : ((i :: l) ++ [i])[l₁.length]? = some a := by rw [hL]; simp
  have hb : ((i :: l) ++ [i])[l₁.length + 1]? = some b := by
    rw [hL]; simp [List.getElem?_append_right]
  have hlen : l₁.length + 1 < (i::l).length + 1 := by
    have := congrArg List.length hL; simp at this ⊢; omega
  by_cases hk : l₁.length + 1 < (i::l).length
  · rw [List.getElem?_append_left (by omega)] at ha
    rw [List.getElem?_append_left hk] at hb
    obtain ⟨h1, rfl⟩ := List.getElem?_eq_some_iff.mp ha
    obtain ⟨h2, rfl⟩ := List.getElem?_eq_some_iff.mp hb
    exact List.formPerm_apply_lt_getElem _ hn _ hk
  · have hk' : l₁.length = l.length := by simp at hk hlen ⊢; omega
    rw [List.getElem?_append_left (by simp; omega)] at ha
    rw [List.getElem?_append_right (by simp; omega)] at hb
    simp only [hk', List.length_cons] at ha hb
    simp at hb
    obtain ⟨h1, rfl⟩ := List.getElem?_eq_some_iff.mp ha
    subst hb
    exact List.formPerm_apply_getElem_length _ _

