-- Prove2me | solution 1 for NieYangPareto.epigraph_eq_add_orthant
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-07T13:49:17.477139+00:00
-- url     : https://prove2.me/submissions/cd892813-139a-4021-99ed-902f86b8837b

import Definitions.Def_NieYangPareto_MOP_U
import Mathlib.Analysis.Convex.Combination

open Pointwise NieYangPareto

theorem solution {n m : ℕ} {E I : Type*} [Finite E] [Finite I]
    (P : MOP n m E I) :
    P.U = (P.obj '' P.K) + {q : Fin m → ℝ | 0 ≤ q} ∧
      convexHull ℝ P.U = convexHull ℝ (P.obj '' P.K) + {q : Fin m → ℝ | 0 ≤ q} := by
  have hU : P.U = (P.obj '' P.K) + {q : Fin m → ℝ | 0 ≤ q} := by
    ext u
    constructor
    · rintro ⟨x, hx, hu⟩
      refine Set.mem_add.mpr ⟨P.obj x, ⟨x, hx, rfl⟩, u - P.obj x, ?_, ?_⟩
      · exact fun i => sub_nonneg.mpr (hu i)
      · rw [add_comm, sub_add_cancel]
    · intro hu
      rcases Set.mem_add.mp hu with ⟨v, ⟨x, hx, rfl⟩, q, hq, rfl⟩
      exact ⟨x, hx, fun i => le_add_of_nonneg_right (hq i)⟩
  have hconv : Convex ℝ {q : Fin m → ℝ | 0 ≤ q} := by
    intro q hq r hr a b ha hb _
    intro i
    exact add_nonneg (mul_nonneg ha (hq i)) (mul_nonneg hb (hr i))
  exact ⟨hU, by rw [hU, convexHull_add, hconv.convexHull_eq]⟩

#print axioms solution
