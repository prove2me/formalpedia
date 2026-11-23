-- Prove2me | solution 1 for GlobalTheory.UnitaryChart.unitary_list_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:26.379348+00:00
-- url     : https://prove2.me/submissions/9d51a142-3ee2-43b7-a1a4-7e3b3b271484

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupSecondKindCoordinatesNearOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.UnitaryChart
open Topology Filter
namespace GlobalTheory.UnitaryChart
theorem _root_.solution {E : Type} [Ring E] (σ : E → E) (hm : ∀ a b, σ (a * b) = σ b * σ a)
    (h1 : σ 1 = 1) (l : List E) (hl : ∀ u ∈ l, σ u * u = 1 ∧ u * σ u = 1) :
    σ l.prod * l.prod = 1 ∧ l.prod * σ l.prod = 1 := by
  induction l with
  | nil => simp [h1]
  | cons a l ih =>
    obtain ⟨i1, i2⟩ := ih (fun u hu => hl u (List.mem_cons_of_mem _ hu))
    obtain ⟨a1, a2⟩ := hl a List.mem_cons_self
    rw [List.prod_cons, hm]
    constructor
    · calc σ l.prod * σ a * (a * l.prod) = σ l.prod * (σ a * a) * l.prod := by noncomm_ring
        _ = 1 := by rw [a1, mul_one, i1]
    · calc a * l.prod * (σ l.prod * σ a) = a * (l.prod * σ l.prod) * σ a := by noncomm_ring
        _ = 1 := by rw [i2, mul_one, a2]
end GlobalTheory.UnitaryChart
