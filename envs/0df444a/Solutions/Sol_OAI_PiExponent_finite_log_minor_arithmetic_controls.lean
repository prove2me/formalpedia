-- Prove2me | solution 1 for OAI.PiExponent.finite_log_minor_arithmetic_controls
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:26:08.985572+00:00
-- url     : https://prove2.me/submissions/6df1d84c-cc2d-4e72-bfda-75fffc9af7e3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_PiExponent_FiniteMinorComparison
import Theorems.Thm_OAI_PiExponent_finite_log_minor_mean_bounds
import Theorems.Thm_OAI_PiExponent_finite_log_minor_determinant_bound

open OAI.PiExponent
open Filter Topology
open scoped BigOperators

theorem solution
    (m K : ℕ) (w0 v0 theta F wmin H : ℝ)
    (p : Fin m → ℤ) (q : Fin m → ℕ)
    (hK : 0 < K) (hw0 : 0 < w0) (hv0 : 0 < v0)
    (htheta : 0 < theta) (hF : 0 ≤ F) (hmin : 0 < wmin)
    (hH : 0 < H) (hq : ∀ i, 2 ≤ q i)
    (hwmin : ∀ i, wmin ≤ OAI.PiExponent.MatrixArithmetic.logWeights q i)
    (selection :
      OAI.PiExponent.InterpolationMatrix.Row K v0 theta
        (OAI.PiExponent.MatrixArithmetic.logWeights q) H →
      OAI.PiExponent.InterpolationMatrix.Column w0
        (OAI.PiExponent.MatrixArithmetic.logWeights q) H)
    (hdet : (OAI.PiExponent.MatrixArithmetic.selectedMinor K
      w0 v0 theta F H p q selection).det ≠ 0) :
    0 ≤ OAI.PiExponent.MatrixArithmetic.meanRowWeight K v0 theta q H ∧
    OAI.PiExponent.MatrixArithmetic.meanRowWeight K v0 theta q H ≤ theta ∧
    -(1 - OAI.PiExponent.MatrixArithmetic.meanRowWeight K v0 theta q H) -
      OAI.PiExponent.FiniteMinorComparison.arithmeticError m v0 theta F wmin ≤
      Real.log ‖(OAI.PiExponent.MatrixArithmetic.selectedMinor K
        w0 v0 theta F H p q selection).det‖ /
        ((Fintype.card (OAI.PiExponent.InterpolationMatrix.Row K v0 theta
          (OAI.PiExponent.MatrixArithmetic.logWeights q) H) : ℝ) * H) := by
  have hmean := OAI.PiExponent.finite_log_minor_mean_bounds
    m K v0 theta H q hK hv0 htheta hH hq
  have hminor := OAI.PiExponent.finite_log_minor_determinant_bound
    m K w0 v0 theta F wmin H p q hK hw0 hv0 htheta hF hmin hH hq hwmin
    selection hdet
  exact ⟨hmean.1, hmean.2, hminor⟩