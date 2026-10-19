-- Prove2me | solution 1 for OAI.KervaireRibbon.circle_cycles
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:35:23.101474+00:00
-- url     : https://prove2.me/submissions/1d21f3d6-3343-4d2e-8449-1a2ec5c91239

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

open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [DecidableEq D] [Finite D]
theorem kr_circle_closed {D : Type*} (σ : Perm D) (o : D) (l : List D) (hc : Circle σ o l) :
    ∀ z ∈ o::l, σ z ∈ o::l := by
  intro z hz
  obtain ⟨l₁, m, hm⟩ := List.append_of_mem hz
  have hL : o :: (l ++ [o]) = l₁ ++ z :: (m ++ [o]) := by
    rw [← List.cons_append, hm]; simp
  obtain ⟨b, l₂, hb⟩ : ∃ b l₂, m ++ [o] = b :: l₂ := by
    cases m with
    | nil => exact ⟨o, [], rfl⟩
    | cons c m' => exact ⟨c, m' ++ [o], rfl⟩
  rw [hb] at hL
  have hr := List.isChain_iff_forall_rel_of_append_cons_cons.mp hc hL
  rw [hr]
  have : b ∈ m ++ [o] := by rw [hb]; simp
  rcases List.mem_append.mp this with h | h
  · rw [hm]; simp [h]
  · simp at h; simp [h]

omit [DecidableEq D] in
theorem solution (σ : Perm D) (o : D) (l : List D) (hc : Circle σ o l) (d : D) :
    σ.SameCycle o d ↔ d ∈ o::l := by
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Perm.mul_apply]; exact kr_circle_closed σ o l hc _ (ih ⟨n, rfl⟩)
  · intro hd
    have := List.IsChain.induction (fun z => σ.SameCycle o z) _ hc
      (fun x y hxy hx => by rw [← hxy]; exact hx.trans (SameCycle.refl σ x).apply_right ) (fun _ => SameCycle.refl σ o) d
      (by simp at hd ⊢; tauto)
    exact this

