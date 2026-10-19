-- Prove2me | solution 2 for OAI.KervaireRibbon.circle_formPerm
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:36:24.257621+00:00
-- url     : https://prove2.me/submissions/fff197b9-9d2e-4805-9f09-65c30bc0133d

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/WordNormalization.lean:L85-L99
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.circle_formPerm. The node keeps its source
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

-- ---- from OAI.GroupTheory.Kervaire.WordNormalization ----
namespace OAI

namespace KervaireRibbon

section
open Monoid Multiplicative
variable {A : Type*} [Group A]

end

open Equiv Equiv.Perm
open scoped Classical
variable {I : Type*} [DecidableEq I]

lemma circle_formPerm (i : I) (l : List I) (hn : (i::l).Nodup) :
    Circle (i::l).formPerm i l := by
  change ((i::l)++[i]).IsChain (fun x y ↦ (i::l).formPerm x=y)
  rw [List.isChain_iff_getElem]
  intro n hn'
  have hh : n < (i::l).length := by simp only [List.length_append,List.length_singleton] at hn'; omega
  rw [List.getElem_append_left hh]
  by_cases hs : n+1 < (i::l).length
  · rw [List.getElem_append_left hs]
    exact List.formPerm_apply_lt_getElem _ hn n hs
  · have he : n = l.length := by simp only [List.length_cons] at hh hs; omega
    subst n
    simp only [List.getElem_append_right (by simp : (i::l).length ≤ l.length+1),
      List.length_cons,Nat.sub_self,List.getElem_cons_zero]
    exact List.formPerm_apply_getElem_length i l

end KervaireRibbon

end OAI

-- ---- platform node ----
open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical


theorem solution : type_of% @_root_.OAI.KervaireRibbon.circle_formPerm := @_root_.OAI.KervaireRibbon.circle_formPerm
