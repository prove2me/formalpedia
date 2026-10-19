-- Prove2me | solution 2 for OAI.KervaireRibbon.planar_cap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:03:33.526866+00:00
-- url     : https://prove2.me/submissions/5daf9eef-763d-4072-acad-42c32e497205

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/RelatorRigidity.lean:L91-L112
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.planar_cap. The node keeps its source
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
import Theorems.Thm_OAI_KervaireRibbon_cap_vertex
import Theorems.Thm_OAI_KervaireRibbon_planar_suppress

-- ---- from OAI.GroupTheory.Kervaire.RelatorRigidity ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D A : Type*} [Fintype D] [DecidableEq D] [Group A]

omit [DecidableEq D] in
lemma planar_symm (σ θ : Perm D) : planar σ θ ↔ planar θ σ := by
  have hn : numCycles (σ*θ) = numCycles (θ*σ) := by
    have hh := numCycles_conj (σ*θ) σ⁻¹
    simpa only [inv_inv,mul_assoc,inv_mul_cancel_left] using hh.symm
  have hc : components σ θ = components θ σ := sup_comm _ _
  unfold planar
  rw [hn,hc]
  omega

lemma planar_cap (σ θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    {x y : D} (hxy : x ≠ y) (hs : σ x = y) (hz : σ y ≠ x)
    (hx : θ x ≠ x) (hy : θ y ≠ y) (hp : planar σ θ) :
    planar (erase (erase σ x) y) (suppress θ x y) := by
  let τ := swap x (σ y) * σ
  have hzy : σ y ≠ y := fun h ↦ hxy (σ.injective (hs.trans h.symm))
  have hτx : τ x = y := by simp only [τ,mul_apply,hs,swap_apply_of_ne_of_ne hxy.symm hzy.symm]
  have hτy : τ y = x := by simp [τ]
  have hcy : σ.SameCycle x (σ y) := (hs ▸ SameCycle.rfl.apply_right).apply_right
  have hτp := planar_vertex_split σ θ hz.symm hcy hp
  rw [cap_vertex σ hxy hs hz]
  by_cases ht : θ x = y
  · have ht' : suppress θ x y = swap x y * θ := by
      simp only [suppress,ht,swap_self]
      change swap x y * (1 * θ * 1) = _
      simp only [one_mul,mul_one]
    rw [ht']
    have htp := planar_vertex_split θ τ hxy (ht ▸ SameCycle.rfl.apply_right)
      ((planar_symm _ _).mp hτp)
    exact planar_vertex_split τ (swap x y*θ) hxy (hτx ▸ SameCycle.rfl.apply_right)
      ((planar_symm _ _).mp htp)
  · exact planar_suppress τ θ hθ hxy hτx hτy hx ht hy hτp

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


theorem solution : type_of% @_root_.OAI.KervaireRibbon.planar_cap := @_root_.OAI.KervaireRibbon.planar_cap
