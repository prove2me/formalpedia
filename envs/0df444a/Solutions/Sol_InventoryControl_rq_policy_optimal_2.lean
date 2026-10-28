-- Prove2me | solution 2 for InventoryControl.rq_policy_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T08:26:44.803644+00:00
-- url     : https://prove2.me/submissions/4ae0ca5e-95a2-4527-8f40-c070b727d366

import Mathlib
import Definitions.Def_InventoryControl_rqPolicy
import Theorems.Thm_InventoryControl_rq_policy_cost
import Theorems.Thm_InventoryControl_rq_policy_lower_bound

-- carved verbatim out of submission 378aa269-b08e-4ac7-bd99-bdd7df9e6840, lines 1846-1858

section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology InventoryControl in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : CompoundPoissonDemand P) (D : DiscreteDemand)
    (h b1 L : ℝ) (hh : 0 < h) (hb : 0 < b1) (hL : 0 ≤ L)
    (hD : ∀ j : ℕ, D.p j = P.real {ω | X.cumDemand (X.count L ω) ω = j})
    (Q : ℕ) (hQ : 0 < Q) (R : ℤ)
    (hR : ∀ y : ℤ, windowCost D h b1 Q R ≤ windowCost D h b1 Q y) (y0 : ℤ) :
    (∀ m : ℕ → Ω → ℕ, ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
        ∀ᶠ T in Filter.atTop, windowCost D h b1 Q R / Q - ε ≤ avgCost X D h b1 L Q y0 m T ω)
      ∧ (∀ᵐ ω ∂P, Filter.Tendsto (fun T => avgCost X D h b1 L Q y0 (rqOrders X R Q y0) T ω)
            Filter.atTop (nhds (windowCost D h b1 Q R / Q))) := by
  exact ⟨fun m => InventoryControl.rq_policy_lower_bound X D h b1 L hh hb hL hD Q hQ R hR y0 m,
    InventoryControl.rq_policy_cost X D h b1 L hh hb hL hD Q hQ R y0⟩

end
