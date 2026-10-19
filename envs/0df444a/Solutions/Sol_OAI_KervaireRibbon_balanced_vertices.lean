-- Prove2me | solution 1 for OAI.KervaireRibbon.balanced_vertices
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:38:58.976795+00:00
-- url     : https://prove2.me/submissions/6bbf29db-9015-43ae-93f8-1c40d5e263c1

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
variable {V I D : Type*} [Fintype V] [Fintype I] [Fintype D]


theorem solution (ε : V → ℤ) (hε : ∀ v, ε v = 1 ∨ ε v = -1)
    (hzero : (∑ v, ε v) = 0) :
    ∃ q : ({v // ε v = 1} ⊕ {v // ε v = 1}) ≃ V,
      (∀ k, ε (q (Sum.inl k)) = 1) ∧ (∀ k, ε (q (Sum.inr k)) = -1) := by
  classical
  have hsum : ∑ v, ε v = ((Finset.univ.filter (fun v => ε v = 1)).card : ℤ)
      - (Finset.univ.filter (fun v => ¬ ε v = 1)).card := by
    calc ∑ v, ε v = ∑ v, (if ε v = 1 then (1:ℤ) else -1) :=
          Finset.sum_congr rfl (by intro v _; rcases hε v with h|h <;> simp [h])
      _ = _ := by rw [Finset.sum_ite]; simp; ring
  have hcard : Fintype.card {v // ε v = 1} = Fintype.card {v // ¬ ε v = 1} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]; omega
  let e' : {v // ε v = 1} ≃ {v // ¬ ε v = 1} := Fintype.equivOfCardEq hcard
  refine ⟨(Equiv.sumCongr (Equiv.refl _) e').trans (Equiv.sumCompl (fun v => ε v = 1)), ?_, ?_⟩
  · intro k; simp [k.2]
  · intro k
    have := (e' k).2
    simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    rcases hε (e' k) with h | h
    · exact absurd h this
    · exact h

