-- Prove2me | solution 2 for OAI.KervaireRibbon.chain_cap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:16:58.149395+00:00
-- url     : https://prove2.me/submissions/a9a1e441-2a8e-4e33-902d-26c374a65e17

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/Circles.lean:L74-L103
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.chain_cap. The node keeps its source
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

-- ---- from OAI.GroupTheory.Kervaire.RelatorRigidity ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D A : Type*} [Fintype D] [DecidableEq D] [Group A]

omit [Fintype D] in
lemma cap_vertex_other (σ : Perm D) {x y d : D} (hxy : x ≠ y) (hs : σ x = y)
    (hdx : d ≠ x) (hdy : d ≠ y) :
    erase (erase σ x) y d = if σ d = x then σ y else σ d := by
  have hsy : σ d ≠ y := fun h ↦ hdx (σ.injective (h.trans hs.symm))
  rw [erase_apply _ _ _ hdy,erase_apply _ _ _ hdx]
  by_cases hdx' : σ d = x
  · rw [ite_eq_left hdx',hs,ite_eq_left rfl,erase_apply _ _ _ hxy.symm]
    by_cases hyx : σ y = x
    · rw [ite_eq_left hyx,hs,hyx]
      exact (hdy (σ.injective (hdx'.trans hyx.symm))).elim
    · rw [ite_eq_right hyx,ite_eq_left hdx']
  · rw [ite_eq_right hdx',ite_eq_right hsy,ite_eq_right hdx']

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

-- ---- from OAI.GroupTheory.Kervaire.Circles ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [DecidableEq D] [Finite D]

omit [Finite D] in
lemma chain_cap (σ : Perm D) (pre post : List D) {d x y : D}
    (hc : (pre ++ d::x::y::post).IsChain (fun x y ↦ σ x = y))
    (hxy : x ≠ y) (hno : ∀ z ∈ pre ++ d::post, z ≠ x ∧ z ≠ y) :
    (pre ++ d::post).IsChain (fun a b ↦ erase (erase σ x) y a = b) := by
  obtain ⟨hpre,hd,hxy',hpost⟩ := by
    simpa only [List.isChain_append_cons_cons,List.isChain_cons_cons] using hc
  apply List.isChain_split.mpr
  constructor
  · apply hpre.imp_of_mem_imp
    intro a b ha hb hab
    have hma : a ∈ pre ++ d::post := by
      simpa only [List.mem_append,List.mem_singleton,List.mem_cons] using
        (List.mem_append.mp ha).imp_right (fun h ↦ Or.inl (List.mem_singleton.mp h))
    have hmb : b ∈ pre ++ d::post := by
      simpa only [List.mem_append,List.mem_singleton,List.mem_cons] using
        (List.mem_append.mp hb).imp_right (fun h ↦ Or.inl (List.mem_singleton.mp h))
    rw [cap_vertex_other σ hxy hxy' (hno a hma).1 (hno a hma).2,hab,ite_eq_right (hno b hmb).1]
  · cases post with
    | nil => exact List.IsChain.singleton _
    | cons z post =>
      obtain ⟨hyz,htail⟩ := List.isChain_cons_cons.mp hpost
      apply List.isChain_cons_cons.mpr
      constructor
      · rw [cap_vertex_other σ hxy hxy' (hno d (by simp)).1 (hno d (by simp)).2,hd,ite_eq_left rfl,hyz]
      · apply htail.imp_of_mem_imp
        intro a b ha hb hab
        have hma : a ∈ pre ++ d::z::post := by simp only [List.mem_append,List.mem_cons]; exact Or.inr (Or.inr (List.mem_cons.mp ha))
        have hmb : b ∈ pre ++ d::z::post := by simp only [List.mem_append,List.mem_cons]; exact Or.inr (Or.inr (List.mem_cons.mp hb))
        rw [cap_vertex_other σ hxy hxy' (hno a hma).1 (hno a hma).2,hab,ite_eq_right (hno b hmb).1]
end
open Monoid Multiplicative
open scoped Classical
variable {D A : Type*} [Group A]
end KervaireRibbon

end

end OAI

-- ---- platform node ----
open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical


theorem solution : type_of% @_root_.OAI.KervaireRibbon.chain_cap := @_root_.OAI.KervaireRibbon.chain_cap
