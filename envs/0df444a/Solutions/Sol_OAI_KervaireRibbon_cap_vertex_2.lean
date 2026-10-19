-- Prove2me | solution 2 for OAI.KervaireRibbon.cap_vertex
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:01:55.26027+00:00
-- url     : https://prove2.me/submissions/f5c30aa8-444b-40ce-8226-536713c5809c

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/RelatorRigidity.lean:L53-L75
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.cap_vertex. The node keeps its source
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

-- ---- from OAI.GroupTheory.Kervaire.RelatorRigidity ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D A : Type*} [Fintype D] [DecidableEq D] [Group A]

omit [Fintype D] in
lemma cap_vertex (σ : Perm D) {x y : D} (hxy : x ≠ y) (hs : σ x = y) (hz : σ y ≠ x) :
    erase (erase σ x) y = swap x y * (swap x (σ y) * σ) := by
  have hzy : σ y ≠ y := fun h ↦ hxy (σ.injective (hs.trans h.symm))
  unfold erase
  rw [hs]
  change swap y (swap x y (σ y)) * (swap x y * σ) = _
  rw [swap_apply_of_ne_of_ne hz hzy]
  have hg : swap y (σ y) * swap x y = swap x y * swap x (σ y) := by
    ext d
    by_cases hd : d = x
    · subst d
      simp only [mul_apply,swap_apply_left,swap_apply_of_ne_of_ne hz hzy]
    by_cases hd' : d = y
    · subst d
      simp only [mul_apply,swap_apply_right,swap_apply_of_ne_of_ne hxy hz.symm,
        swap_apply_of_ne_of_ne hxy.symm hzy.symm]
    by_cases hd'' : d = σ y
    · subst d
      simp only [mul_apply,swap_apply_of_ne_of_ne hz hzy,swap_apply_right,swap_apply_left]
    · simp only [mul_apply,swap_apply_of_ne_of_ne hd hd',swap_apply_of_ne_of_ne hd' hd'',
        swap_apply_of_ne_of_ne hd hd'']
  rw [← mul_assoc,hg,mul_assoc]

end

section
open Equiv Equiv.Perm
open scoped Classical
variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]

end

section
open Equiv Equiv.Perm
open scoped Classical
variable {V I D : Type*} [Fintype V] [Fintype I] [Fintype D]

end

open Equiv Equiv.Perm
open scoped Classical
variable {V I D A : Type*} [Fintype V] [Fintype I] [Fintype D] [DecidableEq D] [Group A]

end KervaireRibbon

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical


theorem solution : type_of% @_root_.OAI.KervaireRibbon.cap_vertex := @_root_.OAI.KervaireRibbon.cap_vertex
