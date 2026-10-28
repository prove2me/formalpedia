-- Prove2me | solution 1 for OAI.PiExponent.FiniteMinorAnalysis_690acb6f.period_matrix_collision_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T14:48:47.681126+00:00
-- url     : https://prove2.me/submissions/791affdf-cf2d-43a1-92be-72e5364f0b87

import Definitions.Def_PiExponent_FiniteTranslationData_690acb6f
import Theorems.Thm_OAI_PiExponent_FiniteMinorAnalysis_690acb6f_formal_period_collision_bound

open OAI.PiExponent
open OAI.PiExponent.FiniteMinorAnalysis_690acb6f
open Filter Topology
open scoped BigOperators

theorem solution
    {m : Nat} (K : Nat) (w0 v theta wmin H : Real) (q : Fin m -> Nat)
    (hK : 0 < K) (hw0 : 0 < w0) (hv : 0 < v) (htheta : 0 < theta)
    (hmin : 0 < wmin) (hH : 0 < H)
    (hwmin : forall i, wmin <= MatrixArithmetic.logWeights q i)
    (selection : Rows K v theta q H -> Columns w0 q H)
    (f : Choices K v theta q H) :
    ‖(periodMatrix selection f).det‖ <= Real.exp
      (-(Real.log 2 / 4) *
          (∑ a : Transverse q H,
            (OAI.PiExponent.FiniteMinorAnalysis_690acb6f.multiplicity (fun r => (f r).1) a : Real) ^ 2) +
        (rowCount K v theta q H : Real) * H *
          (holomorphicError K w0 v wmin +
            collisionRemainder (rowCount K v theta q H) H)) := by
  classical
  let ell : Rows K v theta q H -> Nat := fun r => r.2.1 0 - (f r).2.2
  have hell : ((∑ r : Rows K v theta q H, ell r : Nat) : Real) <=
      (Fintype.card (Rows K v theta q H) : Real) * H / v := by
    rw [Nat.cast_sum]
    calc
      (∑ r : Rows K v theta q H, (ell r : Real)) <=
          ∑ _r : Rows K v theta q H, H / v := by
        apply Finset.sum_le_sum
        intro r hr
        have hmem : r.2.1 ∈
            (realWeightedSimplex (InterpolationMatrix.rowWeights v theta
              (MatrixArithmetic.logWeights q)) H).filter
              (fun a => ∑ i,
                InterpolationMatrix.rowWeights v theta (MatrixArithmetic.logWeights q) i *
                  (a i : Real) < H) := by
          simpa [strictWeightedSimplex] using r.2.2
        have hstrict := (Finset.mem_filter.mp hmem).2
        have htail : 0 <=
            ∑ i : Fin m,
              (MatrixArithmetic.logWeights q i / theta) * (r.2.1 i.succ : Real) := by
          apply Finset.sum_nonneg
          intro i hi
          exact mul_nonneg
            (div_nonneg (le_of_lt (lt_of_lt_of_le hmin (hwmin i))) (le_of_lt htheta))
            (Nat.cast_nonneg _)
        have hsum : v * (r.2.1 0 : Real) +
              (∑ i : Fin m,
                (MatrixArithmetic.logWeights q i / theta) * (r.2.1 i.succ : Real)) < H := by
          simpa [InterpolationMatrix.rowWeights, Fin.sum_univ_succ] using hstrict
        have hrow : (r.2.1 0 : Real) <= H / v := by
          apply (le_div_iff₀ hv).2
          nlinarith
        have hsub : r.2.1 0 - (f r).2.2 <= r.2.1 0 := Nat.sub_le _ _
        dsimp [ell]
        exact (Nat.cast_le.mpr hsub).trans hrow
      _ = _ := by simp; ring
  have hbound :=
    OAI.PiExponent.FiniteMinorAnalysis_690acb6f.formal_period_collision_bound
      (group := fun r : Rows K v theta q H => (f r).1)
      (transverse := fun a : Transverse q H => a.1)
      (j := fun r => r.1.val)
      (ell := ell)
      (h := fun c : Rows K v theta q H => (selection c).1 0)
      (a := fun c i => (selection c).1 i.succ)
      (w := MatrixArithmetic.logWeights q)
      (K := K) (H := H) (w0 := w0) (v0 := v) (wmin := wmin)
      hK hH hw0 hmin hwmin
      (fun r => r.1.isLt)
      (fun c => by
        have hmem : (selection c).1 ∈
            realWeightedSimplex
              (InterpolationMatrix.columnWeights w0 (MatrixArithmetic.logWeights q)) H :=
          (selection c).property
        have hle : ∑ i : Fin (m + 1),
            InterpolationMatrix.columnWeights w0 (MatrixArithmetic.logWeights q) i *
              (((selection c).1 i : Nat) : Real) ≤ H := by
          exact (Finset.mem_filter.mp hmem).2
        simpa [InterpolationMatrix.columnWeights, Fin.sum_univ_succ] using hle)
      hell
  change ‖Matrix.det (fun r c : Rows K v theta q H =>
    PowerSeries.coeff (r.2.1 0 - ((f r).2.2 : Nat))
      ((periodMonomial r.1.val ((selection c).1 0)
        (fun i => (selection c).1 i.succ)).coeff (f r).1.1))‖ ≤ _
  simpa [rowCount, ell, Fintype.card_prod] using hbound