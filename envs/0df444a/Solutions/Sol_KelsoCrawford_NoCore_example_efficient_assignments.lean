-- Prove2me | solution 1 for KelsoCrawford.NoCore.example_efficient_assignments
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:11:20.723082+00:00
-- url     : https://prove2.me/submissions/604cd8e1-72c7-4e9a-a9f9-a58448723965

import Mathlib
import Definitions.Def_KelsoCrawford_NoCore_Notions
import Definitions.Def_KelsoCrawford_NoCore_Example
open KelsoCrawford.NoCore
set_option maxRecDepth 4096
set_option maxHeartbeats 0
theorem solution :
    (∀ g : Fin 3 → Fin 2, noCoreMarket.totalProduct g ≤ 23 / 2) ∧
    (∀ g : Fin 3 → Fin 2, noCoreMarket.totalProduct g = 23 / 2 ↔
      (assignedTo g 0 = {0} ∧ assignedTo g 1 = {1, 2}) ∨
      (assignedTo g 0 = {0, 1} ∧ assignedTo g 1 = {2})) := by
  have hu3 : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  have hu2 : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  constructor <;> intro g <;>
    generalize h0 : g 0 = a0 <;> generalize h1 : g 1 = a1 <;>
    generalize h2 : g 2 = a2 <;> fin_cases a0 <;> fin_cases a1 <;> fin_cases a2 <;>
    simp +decide [Market.totalProduct, assignedTo, noCoreMarket, techJ, techK,
      hu3, hu2, h0, h1, h2, Finset.filter_insert, Finset.filter_singleton] <;> norm_num
#print axioms solution
