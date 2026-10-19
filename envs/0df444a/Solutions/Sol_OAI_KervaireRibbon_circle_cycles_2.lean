-- Prove2me | solution 2 for OAI.KervaireRibbon.circle_cycles
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:14:24.639437+00:00
-- url     : https://prove2.me/submissions/1cfe2454-d4b6-4000-b836-068d634c1ab3

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/Circles.lean:L36-L57
-- (upload_full_project.md Phase 4): solution for node OAI.KervaireRibbon.circle_cycles. The node keeps its source
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

-- ---- from OAI.GroupTheory.Kervaire.Circles ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [DecidableEq D] [Finite D]

omit [Finite D] [DecidableEq D] in
lemma chain_mem_next (σ : Perm D) (o x : D) (l : List D)
    (hc : (x :: (l ++ [o])).IsChain (fun x y ↦ σ x = y)) {d : D} (hd : d ∈ x::l) :
    σ d ∈ l ++ [o] := by
  induction l generalizing x with
  | nil =>
    have hd' : d = x := by simpa using hd
    have hh : σ x = o := by simpa using hc
    simp [hd',hh]
  | cons y l ih =>
    have hh := List.isChain_cons_cons.mp hc
    rcases List.mem_cons.mp hd with rfl | hd
    · simp only [hh.1,List.cons_append,List.mem_cons,true_or]
    · exact List.mem_cons_of_mem _ (ih y hh.2 hd)

omit [DecidableEq D] in
lemma circle_cycles (σ : Perm D) (o : D) (l : List D) (hc : Circle σ o l) (d : D) :
    σ.SameCycle o d ↔ d ∈ o::l := by
  have hm : ∀ d ∈ o::l, σ d ∈ o::l := by
    intro d hd
    have hh := chain_mem_next σ o o l hc hd
    simpa [or_comm] using hh
  constructor
  · intro hd
    obtain ⟨n,hn⟩ := hd.exists_nat_pow_eq
    have hi : ∀ n : ℕ, (σ^n) o ∈ o::l := by
      intro n; induction n with
      | zero => exact List.mem_cons_self
      | succ n ih => rw [pow_succ',mul_apply]; exact hm _ ih
    exact hn ▸ hi n
  · intro hd
    let : Trans σ.SameCycle σ.SameCycle σ.SameCycle := ⟨fun h₁ h₂ ↦ h₁.trans h₂⟩
    have hcc : (o :: (l++[o])).IsChain σ.SameCycle :=
      List.IsChain.imp (R := fun x y ↦ σ x = y) (fun x y h ↦ h ▸ SameCycle.rfl.apply_right) hc
    rcases List.mem_cons.mp hd with rfl | hd
    · exact SameCycle.rfl
    · exact hcc.rel_cons (List.mem_append.mpr (Or.inl hd))

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


theorem solution : type_of% @_root_.OAI.KervaireRibbon.circle_cycles := @_root_.OAI.KervaireRibbon.circle_cycles
