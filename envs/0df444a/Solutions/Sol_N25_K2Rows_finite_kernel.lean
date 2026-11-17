-- Prove2me | solution 1 for N25.K2Rows.finite_kernel
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:27:18.058367+00:00
-- url     : https://prove2.me/submissions/6733665d-2332-48d2-8a56-363824122240

import Definitions.Def_N25_LocalKummerKernel

set_option autoImplicit false

noncomputable section

namespace N25

/-- The two finite character lines in the exact sequence make the literal
selected kernel finite. -/
theorem _root_.solution (hK2 : K2Rows) : Finite ↥V := by
  classical
  let lift : ZMod 71 → ↥V := fun b => (hK2.q_surjective b).choose
  have hlift (b : ZMod 71) : hK2.q (lift b) = b :=
    (hK2.q_surjective b).choose_spec
  apply Finite.of_surjective (fun ab : ZMod 71 × ZMod 71 => hK2.i ab.1 + lift ab.2)
  intro v
  have hker : v - lift (hK2.q v) ∈ hK2.q.ker := by
    change hK2.q (v - lift (hK2.q v)) = 0
    rw [map_sub, hlift, sub_self]
  rw [hK2.exact_at_V] at hker
  obtain ⟨a, ha⟩ := hker
  refine ⟨(a, hK2.q v), ?_⟩
  dsimp only
  rw [ha]
  exact sub_add_cancel _ _

end N25
