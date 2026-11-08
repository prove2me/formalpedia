-- Prove2me | solution 1 for MonoIncExtrap.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:43:25.438907+00:00
-- url     : https://prove2.me/submissions/a18575ec-b2a6-4752-9fb2-0c6c77234328

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MonoIncExtrap_Setting
import Definitions.Def_MonoIncExtrap_Algorithm1

open InnerProductSpace ThreeOpSplitting.Convergence

namespace Aux_MIE

open MonoIncExtrap

theorem lip_ball {n : ℕ} (B : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hloc : IsLocallyLipschitzOn F (closure (dom B))) (c : EuclideanSpace ℝ (Fin n)) (R : ℝ) :
    ∃ L : ℝ, 0 < L ∧ IsLipschitzOn F (ballIn B c R) L := by
  obtain ⟨L, hL, hLip⟩ := hloc (closure (dom B) ∩ Metric.closedBall c R) Set.inter_subset_left
    ((isCompact_closedBall c R).inter_left isClosed_closure)
  have sub : ∀ x, x ∈ ballIn B c R → x ∈ closure (dom B) ∩ Metric.closedBall c R := by
    intro x hx
    exact ⟨subset_closure hx.1, by rw [Metric.mem_closedBall, dist_eq_norm]; exact hx.2⟩
  exact ⟨L, hL, fun x hx y hy => hLip x (sub x hx) y (sub y hy)⟩

end Aux_MIE

open MonoIncExtrap Aux_MIE in
theorem solution {n : ℕ}
    {B : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n))}
    {I : Alg1.Input (EuclideanSpace ℝ (Fin n))} {xstar : EuclideanSpace ℝ (Fin n)}
    (hI : Alg1.Standing B I xstar) :
    ∃ LS LShat : ℝ, Alg1.ValidS B I xstar LS LShat := by
  have hloc := hI.assumption.locally_lipschitz
  obtain ⟨L1, hL1, h1⟩ := lip_ball B I.F hloc xstar
    (I.r0 xstar / Real.sqrt (1 - 2 * I.ν ^ 2))
  obtain ⟨L2, hL2, h2⟩ := lip_ball B I.F hloc xstar
    ((5 + 9 * I.γ0 * L1) * I.r0 xstar / (3 * Real.sqrt (1 - 2 * I.ν ^ 2)))
  exact ⟨L1, L2, hL1, hL2, h1, h2⟩
