-- Prove2me | solution 2 for OAI.KervaireRibbon.suppress_involutive_all
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:20:19.001093+00:00
-- url     : https://prove2.me/submissions/85d72a3d-3b89-4a81-b072-6cbc550a523e

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/Capping.lean:L24-L39
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.suppress_involutive_all. The node keeps its source
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
import Theorems.Thm_OAI_KervaireRibbon_suppress_involutive

-- ---- from OAI.GroupTheory.Kervaire.Capping ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D A : Type*} [Fintype D] [DecidableEq D] [Group A]

omit [Fintype D] in
lemma suppress_paired (θ : Perm D) {x y : D} (ht : θ x = y) :
    suppress θ x y = swap x y * θ := by
  simp only [suppress,ht,swap_self]
  change swap x y * (1 * θ * 1) = _
  simp only [one_mul,mul_one]

omit [Fintype D] in
lemma suppress_involutive_all (θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    {x y : D} (hxy : x ≠ y) (hx : θ x ≠ x) (hy : θ y ≠ y) :
    ∀ d, suppress θ x y (suppress θ x y d) = d := by
  by_cases ht : θ x = y
  · rw [suppress_paired θ ht]
    have hty : θ y = x := by simpa only [hθ] using (congrArg θ ht).symm
    intro d
    by_cases hd : d = x
    · subst d; simp only [mul_apply,ht,swap_apply_right]
    by_cases hd' : d = y
    · subst d; simp only [mul_apply,hty,swap_apply_left]
    have hdx : θ d ≠ x := fun h ↦ hd' (by simpa only [hθ,ht] using congrArg θ h)
    have hdy : θ d ≠ y := fun h ↦ hd (by simpa only [hθ,hty] using congrArg θ h)
    simp only [mul_apply,swap_apply_of_ne_of_ne hdx hdy,hθ,swap_apply_of_ne_of_ne hd hd']
  · exact suppress_involutive θ hθ hxy hx ht hy

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


theorem solution : type_of% @_root_.OAI.KervaireRibbon.suppress_involutive_all := @_root_.OAI.KervaireRibbon.suppress_involutive_all
