-- Prove2me | solution 1 for OAI.PiExponent.FiniteMinorAnalysis.period_matrix_collision_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T19:11:32.498223+00:00
-- url     : https://prove2.me/submissions/f45f1463-7975-40a1-8f7f-82a7ae4f1404

import Definitions.Def_PiExponent_FiniteTranslationData
import Theorems.Thm_OAI_PiExponent_FiniteMinorAnalysis_690acb6f_period_matrix_collision_bound
open OAI.PiExponent
open OAI.PiExponent.FiniteMinorAnalysis
open Filter Topology
open scoped BigOperators
theorem solution
    {m : ℕ} (K : ℕ) (w0 v theta wmin H : ℝ) (q : Fin m → ℕ)
    (hK : 0 < K) (hw0 : 0 < w0) (hv : 0 < v) (htheta : 0 < theta)
    (hmin : 0 < wmin) (hH : 0 < H)
    (hwmin : ∀ i, wmin ≤ MatrixArithmetic.logWeights q i)
    (selection : Rows K v theta q H → Columns w0 q H)
    (f : Choices K v theta q H) :
    ‖(periodMatrix selection f).det‖ ≤ Real.exp
      (-(Real.log 2 / 4) *
          (∑ a : Transverse q H, (multiplicity (fun r => (f r).1) a : ℝ) ^ 2) +
        (rowCount K v theta q H : ℝ) * H *
          (holomorphicError K w0 v wmin +
            collisionRemainder (rowCount K v theta q H) H)) :=
  OAI.PiExponent.FiniteMinorAnalysis_690acb6f.period_matrix_collision_bound K w0 v theta wmin H q
    hK hw0 hv htheta hmin hH hwmin selection f
