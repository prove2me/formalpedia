-- Prove2me | solution 1 for NegativeDP.OptEq.theorem52f
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T13:55:45.826743+00:00
-- url     : https://prove2.me/submissions/60b63de4-2eae-41cd-a037-62265f09115f

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_OptEq_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan stationary IsGenerated IsGeneratedPlan)

open NegativeDP.OptEq in
theorem solution {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) (f : {g : S → A // Measurable g})
    (hf : IsGenerated π f) (u : S → EReal) (hu : NegativeDP.Stationary.IsNegM u) :
    ∀ s, NegativeDP.Stationary.T P f u s ≤ U P π u s := by
  intro s
  obtain ⟨pieces, -, -, hU, hfp⟩ := hf
  have hs : s ∈ ⋃ n, pieces n := hU ▸ Set.mem_univ s
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hs
  have heq : NegativeDP.Stationary.T P f u s = NegativeDP.Stationary.T P (π n) u s := by
    unfold NegativeDP.Stationary.T
    rw [hfp n s hn]
  rw [heq]
  exact le_iSup (fun n => NegativeDP.Stationary.T P (π n) u s) n
