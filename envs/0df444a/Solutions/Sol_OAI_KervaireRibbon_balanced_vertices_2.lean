-- Prove2me | solution 2 for OAI.KervaireRibbon.balanced_vertices
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:05:11.398374+00:00
-- url     : https://prove2.me/submissions/64193afe-4792-413c-8a5f-cec06a0a68eb

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/RelatorRigidity.lean:L231-L259
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.balanced_vertices. The node keeps its source
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

/-- Exact positive/negative disk coordinates, derived from the sign conservation
 of the bands rather than postulated as a balancing hypothesis. -/
lemma balanced_vertices (ε : V → ℤ) (hε : ∀ v, ε v = 1 ∨ ε v = -1)
    (hzero : (∑ v, ε v) = 0) :
    ∃ q : ({v // ε v = 1} ⊕ {v // ε v = 1}) ≃ V,
      (∀ k, ε (q (Sum.inl k)) = 1) ∧ (∀ k, ε (q (Sum.inr k)) = -1) := by
  let P := {v // ε v = 1}
  let N := {v // ¬ ε v = 1}
  let e : P ⊕ N ≃ V := Equiv.sumCompl (fun v ↦ ε v = 1)
  have hn (v : N) : ε v.val = -1 := (hε v.val).resolve_left v.property
  have hh := e.sum_comp ε
  rw [hzero] at hh
  simp only [Fintype.sum_sum_type] at hh
  have hP : ∑ p : P, ε (e (Sum.inl p)) = (Fintype.card P : ℤ) := by
    change (∑ p : P, ε p.val) = _
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using
      Finset.sum_congr rfl (fun (p : P) (_ : p ∈ Finset.univ) ↦ p.property)
  have hN : ∑ n : N, ε (e (Sum.inr n)) = -(Fintype.card N : ℤ) := by
    change (∑ n : N, ε n.val) = _
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_neg,one_mul,mul_one] using
      Finset.sum_congr rfl (fun (n : N) (_ : n ∈ Finset.univ) ↦ hn n)
  rw [hP,hN] at hh
  have hcard : Fintype.card P = Fintype.card N := by omega
  let f : P ≃ N := Fintype.equivOfCardEq hcard
  refine ⟨(Equiv.sumCongr (Equiv.refl P) f).trans e,?_,?_⟩
  · intro p
    exact p.property
  · intro p
    exact hn (f p)
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


theorem solution : type_of% @_root_.OAI.KervaireRibbon.balanced_vertices := @_root_.OAI.KervaireRibbon.balanced_vertices
