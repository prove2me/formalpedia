-- Prove2me | solution 1 for KLTNuclear.Oracle.eq_2_12
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T16:21:07.858743+00:00
-- url     : https://prove2.me/submissions/39277998-6553-4c26-86c9-b518e12268bb

import Mathlib
import Definitions.Def_KLTNuclear_Oracle_Model
namespace PriorIdem

open MatrixCompletion
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator

namespace MatrixCompletion

variable {n1 n2 r : Nat} {M : RealMatrix n1 n2}

/-- The column singular kernel collapses: `∑_a K_U(i,a) K_U(a,a') = K_U(i,a')`,
    where `K_U(i,a) = ∑_k u_k i * u_k a`. This is `P_U² = P_U` at kernel level. -/
private lemma KU_collapse (S : SVD M r) (i a' : Fin n1) :
    (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) *
        (∑ k' : Fin r, S.u k' a * S.u k' a'))
      = ∑ k : Fin r, S.u k i * S.u k a' := by
  calc ∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) *
          (∑ k' : Fin r, S.u k' a * S.u k' a')
      = ∑ a : Fin n1, ∑ k : Fin r, ∑ k' : Fin r,
          (S.u k i * S.u k a) * (S.u k' a * S.u k' a') := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.sum_mul_sum]
    _ = ∑ k : Fin r, ∑ k' : Fin r, ∑ a : Fin n1,
          (S.u k i * S.u k a) * (S.u k' a * S.u k' a') := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.sum_comm]
    _ = ∑ k : Fin r, ∑ k' : Fin r,
          (S.u k i * S.u k' a') * (∑ a : Fin n1, S.u k a * S.u k' a) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        refine Finset.sum_congr rfl (fun k' _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        ring
    _ = ∑ k : Fin r, ∑ k' : Fin r,
          (S.u k i * S.u k' a') * (if k = k' then 1 else 0) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        refine Finset.sum_congr rfl (fun k' _ => ?_)
        rw [S.u_orthonormal k k']
    _ = ∑ k : Fin r, S.u k i * S.u k a' := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [show (∑ k' : Fin r, S.u k i * S.u k' a' * if k = k' then 1 else 0)
            = ∑ k' : Fin r, if k = k' then S.u k i * S.u k' a' else 0 from by
          refine Finset.sum_congr rfl (fun k' _ => ?_)
          by_cases h : k = k' <;> simp [h]]
        rw [Finset.sum_ite_eq Finset.univ k (fun k' => S.u k i * S.u k' a')]
        simp

/-- The row singular kernel collapses: `∑_b K_V(b',b) K_V(b,j) = K_V(b',j)`. -/
private lemma KV_collapse (S : SVD M r) (b' j : Fin n2) :
    (∑ b : Fin n2, (∑ k : Fin r, S.v k b' * S.v k b) *
        (∑ k' : Fin r, S.v k' b * S.v k' j))
      = ∑ k : Fin r, S.v k b' * S.v k j := by
  calc ∑ b : Fin n2, (∑ k : Fin r, S.v k b' * S.v k b) *
          (∑ k' : Fin r, S.v k' b * S.v k' j)
      = ∑ b : Fin n2, ∑ k : Fin r, ∑ k' : Fin r,
          (S.v k b' * S.v k b) * (S.v k' b * S.v k' j) := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [Finset.sum_mul_sum]
    _ = ∑ k : Fin r, ∑ k' : Fin r, ∑ b : Fin n2,
          (S.v k b' * S.v k b) * (S.v k' b * S.v k' j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.sum_comm]
    _ = ∑ k : Fin r, ∑ k' : Fin r,
          (S.v k b' * S.v k' j) * (∑ b : Fin n2, S.v k b * S.v k' b) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        refine Finset.sum_congr rfl (fun k' _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        ring
    _ = ∑ k : Fin r, ∑ k' : Fin r,
          (S.v k b' * S.v k' j) * (if k = k' then 1 else 0) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        refine Finset.sum_congr rfl (fun k' _ => ?_)
        rw [S.v_orthonormal k k']
    _ = ∑ k : Fin r, S.v k b' * S.v k j := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [show (∑ k' : Fin r, S.v k b' * S.v k' j * if k = k' then 1 else 0)
            = ∑ k' : Fin r, if k = k' then S.v k b' * S.v k' j else 0 from by
          refine Finset.sum_congr rfl (fun k' _ => ?_)
          by_cases h : k = k' <;> simp [h]]
        rw [Finset.sum_ite_eq Finset.univ k (fun k' => S.v k b' * S.v k' j)]
        simp

/-- `P_U` is idempotent. -/
private lemma left_idem (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (leftSingularProjection S X)
      = leftSingularProjection S X := by
  funext i j
  simp only [leftSingularProjection]
  rw [show (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) *
        ∑ a' : Fin n1, (∑ k' : Fin r, S.u k' a * S.u k' a') * X a' j)
      = ∑ a : Fin n1, ∑ a' : Fin n1,
          ((∑ k : Fin r, S.u k i * S.u k a) *
            (∑ k' : Fin r, S.u k' a * S.u k' a')) * X a' j from by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a' _ => ?_)
    ring]
  rw [Finset.sum_comm]
  rw [show (∑ a' : Fin n1, ∑ a : Fin n1,
        ((∑ k : Fin r, S.u k i * S.u k a) *
          (∑ k' : Fin r, S.u k' a * S.u k' a')) * X a' j)
      = ∑ a' : Fin n1, (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) *
          (∑ k' : Fin r, S.u k' a * S.u k' a')) * X a' j from by
    refine Finset.sum_congr rfl (fun a' _ => ?_)
    rw [Finset.sum_mul]]
  refine Finset.sum_congr rfl (fun a' _ => ?_)
  rw [KU_collapse S i a']

/-- `P_V` is idempotent. -/
private lemma right_idem (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (rightSingularProjection S X)
      = rightSingularProjection S X := by
  funext i j
  simp only [rightSingularProjection]
  rw [show (∑ b : Fin n2, (∑ b' : Fin n2, X i b' * (∑ k : Fin r, S.v k b' * S.v k b)) *
        (∑ k' : Fin r, S.v k' b * S.v k' j))
      = ∑ b' : Fin n2, X i b' * (∑ b : Fin n2,
          (∑ k : Fin r, S.v k b' * S.v k b) * (∑ k' : Fin r, S.v k' b * S.v k' j))
        from by
    rw [show (∑ b : Fin n2, (∑ b' : Fin n2, X i b' * (∑ k : Fin r, S.v k b' * S.v k b)) *
          (∑ k' : Fin r, S.v k' b * S.v k' j))
        = ∑ b : Fin n2, ∑ b' : Fin n2,
            X i b' * ((∑ k : Fin r, S.v k b' * S.v k b) *
              (∑ k' : Fin r, S.v k' b * S.v k' j)) from by
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun b' _ => ?_)
      ring]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b' _ => ?_)
    rw [Finset.mul_sum]]
  refine Finset.sum_congr rfl (fun b' _ => ?_)
  rw [KV_collapse S b' j]

/-- `P_U` and `P_V` commute, and the composite is `twoSided`:
    `P_U (P_V X) = twoSided X`. -/
private lemma left_right_eq_two (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (rightSingularProjection S X)
      = twoSidedSingularProjection S X := by
  funext i j
  simp only [leftSingularProjection, rightSingularProjection,
    twoSidedSingularProjection]
  -- LHS: ∑ a, KU(i,a) * (∑ b, X a b * KV(b,j))
  -- RHS: ∑ a, ∑ b, KU(i,a) * X a b * KV(b,j)
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- `P_V (P_U X) = twoSided X` (the other composition order). -/
private lemma right_left_eq_two (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (leftSingularProjection S X)
      = twoSidedSingularProjection S X := by
  funext i j
  simp only [leftSingularProjection, rightSingularProjection,
    twoSidedSingularProjection]
  -- LHS: ∑ b, (∑ a, KU(i,a) * X a b) * KV(b,j)
  -- RHS: ∑ a, ∑ b, KU(i,a) * X a b * KV(b,j)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_mul]

/-- `P_U (twoSided X) = twoSided X`: applying `P_U` again is idempotent. -/
private lemma left_two_eq_two (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (twoSidedSingularProjection S X)
      = twoSidedSingularProjection S X := by
  funext i j
  simp only [leftSingularProjection, twoSidedSingularProjection]
  -- LHS: ∑ a', KU(i,a') * (∑ a ∑ b, KU(a',a) X a b KV(b,j))
  -- RHS: ∑ a ∑ b, KU(i,a) X a b KV(b,j)
  -- collapse over a': coefficient of (X a b * KV(b,j)) is ∑ a' KU(i,a') KU(a',a) = KU(i,a)
  rw [show (∑ a' : Fin n1, (∑ k : Fin r, S.u k i * S.u k a') *
        ∑ a : Fin n1, ∑ b : Fin n2,
          (∑ k' : Fin r, S.u k' a' * S.u k' a) * X a b *
            (∑ l : Fin r, S.v l b * S.v l j))
      = ∑ a : Fin n1, ∑ b : Fin n2,
          (∑ a' : Fin n1, (∑ k : Fin r, S.u k i * S.u k a') *
            (∑ k' : Fin r, S.u k' a' * S.u k' a)) *
            (X a b * (∑ l : Fin r, S.v l b * S.v l j)) from by
    -- First: distribute KU(i,a') over the inner ∑a ∑b and turn LHS into a
    -- fully expanded triple sum over a', a, b.
    rw [show (∑ a' : Fin n1, (∑ k : Fin r, S.u k i * S.u k a') *
          ∑ a : Fin n1, ∑ b : Fin n2,
            (∑ k' : Fin r, S.u k' a' * S.u k' a) * X a b *
              (∑ l : Fin r, S.v l b * S.v l j))
        = ∑ a' : Fin n1, ∑ a : Fin n1, ∑ b : Fin n2,
            ((∑ k : Fin r, S.u k i * S.u k a') *
              (∑ k' : Fin r, S.u k' a' * S.u k' a)) *
              (X a b * (∑ l : Fin r, S.v l b * S.v l j)) from by
      refine Finset.sum_congr rfl (fun a' _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      ring]
    -- Move ∑ a' innermost: swap a' with a, then a' with b.
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.sum_mul]]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [KU_collapse S i a]
  ring

/-- `P_V (twoSided X) = twoSided X`. -/
private lemma right_two_eq_two (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (twoSidedSingularProjection S X)
      = twoSidedSingularProjection S X := by
  funext i j
  simp only [rightSingularProjection, twoSidedSingularProjection]
  -- LHS: ∑ b', (∑ a ∑ b, KU(i,a) X a b KV(b,b')) * KV(b',j)
  -- RHS: ∑ a ∑ b, KU(i,a) X a b KV(b,j)
  rw [show (∑ b' : Fin n2, (∑ a : Fin n1, ∑ b : Fin n2,
          (∑ k : Fin r, S.u k i * S.u k a) * X a b *
            (∑ l : Fin r, S.v l b * S.v l b')) *
        (∑ l' : Fin r, S.v l' b' * S.v l' j))
      = ∑ a : Fin n1, ∑ b : Fin n2,
          ((∑ k : Fin r, S.u k i * S.u k a) * X a b) *
            (∑ b' : Fin n2, (∑ l : Fin r, S.v l b * S.v l b') *
              (∑ l' : Fin r, S.v l' b' * S.v l' j)) from by
    -- First: distribute KV(b',j) over the inner ∑a ∑b and expand to a triple sum.
    rw [show (∑ b' : Fin n2, (∑ a : Fin n1, ∑ b : Fin n2,
            (∑ k : Fin r, S.u k i * S.u k a) * X a b *
              (∑ l : Fin r, S.v l b * S.v l b')) *
          (∑ l' : Fin r, S.v l' b' * S.v l' j))
        = ∑ b' : Fin n2, ∑ a : Fin n1, ∑ b : Fin n2,
            ((∑ k : Fin r, S.u k i * S.u k a) * X a b) *
              ((∑ l : Fin r, S.v l b * S.v l b') *
                (∑ l' : Fin r, S.v l' b' * S.v l' j)) from by
      refine Finset.sum_congr rfl (fun b' _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      ring]
    -- Move ∑ b' innermost: swap b' with a, then b' with b.
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.mul_sum]]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [KV_collapse S b j]

/-- `twoSided = P_U ∘ P_V`. -/
private lemma two_eq_left_right (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S X
      = leftSingularProjection S (rightSingularProjection S X) :=
  (left_right_eq_two S X).symm

/-- `twoSided (P_U X) = twoSided X`. -/
private lemma two_left_eq_two (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (leftSingularProjection S X)
      = twoSidedSingularProjection S X := by
  rw [two_eq_left_right, right_left_eq_two, left_two_eq_two]

/-- `twoSided (P_V X) = twoSided X`. -/
private lemma two_right_eq_two (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (rightSingularProjection S X)
      = twoSidedSingularProjection S X := by
  rw [two_eq_left_right, right_idem, left_right_eq_two]

/-- `twoSided (twoSided X) = twoSided X`. -/
private lemma two_two_eq_two (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (twoSidedSingularProjection S X)
      = twoSidedSingularProjection S X := by
  rw [two_eq_left_right, right_two_eq_two, left_two_eq_two]

/-- `P_U` is additive. -/
private lemma left_add (S : SVD M r) (A B : RealMatrix n1 n2) :
    leftSingularProjection S (A + B)
      = leftSingularProjection S A + leftSingularProjection S B := by
  funext i j
  simp only [leftSingularProjection, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  ring

/-- `P_V` is additive. -/
private lemma right_add (S : SVD M r) (A B : RealMatrix n1 n2) :
    rightSingularProjection S (A + B)
      = rightSingularProjection S A + rightSingularProjection S B := by
  funext i j
  simp only [rightSingularProjection, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- `twoSided` is additive. -/
private lemma two_add (S : SVD M r) (A B : RealMatrix n1 n2) :
    twoSidedSingularProjection S (A + B)
      = twoSidedSingularProjection S A + twoSidedSingularProjection S B := by
  funext i j
  simp only [twoSidedSingularProjection, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- `P_U` respects subtraction. -/
private lemma left_sub (S : SVD M r) (A B : RealMatrix n1 n2) :
    leftSingularProjection S (A - B)
      = leftSingularProjection S A - leftSingularProjection S B := by
  funext i j
  simp only [leftSingularProjection, Matrix.sub_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  ring

/-- `P_V` respects subtraction. -/
private lemma right_sub (S : SVD M r) (A B : RealMatrix n1 n2) :
    rightSingularProjection S (A - B)
      = rightSingularProjection S A - rightSingularProjection S B := by
  funext i j
  simp only [rightSingularProjection, Matrix.sub_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- `twoSided` respects subtraction. -/
private lemma two_sub (S : SVD M r) (A B : RealMatrix n1 n2) :
    twoSidedSingularProjection S (A - B)
      = twoSidedSingularProjection S A - twoSidedSingularProjection S B := by
  funext i j
  simp only [twoSidedSingularProjection, Matrix.sub_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

end MatrixCompletion

open MatrixCompletion
theorem solution
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (X : RealMatrix n1 n2) :
    tangentProjection S (tangentProjection S X) = tangentProjection S X := by
  -- tangentProjection S Y = P_U Y + P_V Y - twoSided Y, and P_U, P_V, twoSided are
  -- additive.  Expand the outer projection over the inner +/-, then substitute the
  -- nine composition identities; the result telescopes by `abel`.
  simp only [tangentProjection]
  rw [left_sub, left_add, right_sub, right_add, two_sub, two_add,
    left_idem, right_idem, left_right_eq_two, right_left_eq_two,
    left_two_eq_two, right_two_eq_two,
    two_left_eq_two, two_right_eq_two, two_two_eq_two]
  abel

end PriorIdem
#print axioms PriorIdem.solution

namespace PriorAdj
open MatrixCompletion
open scoped BigOperators Matrix

set_option maxHeartbeats 1000000

/-
Self-adjointness (symmetry under the Frobenius inner product) of the tangent
projection `P_T = leftSingularProjection + rightSingularProjection -
twoSidedSingularProjection`:

    ⟨P_T A, B⟩_F = ⟨A, P_T B⟩_F  for all real matrices A, B.

This is the basic orthogonal-projection property the Candès–Recht tangent-space
analysis (arXiv:0805.4471 §3–§4) uses repeatedly: it underlies the
resolution-of-identity `X = ∑_{ab} ⟨P_T(e_ab), X⟩ P_T(e_ab)` for `X ∈ T`, and
the rank-one frame representation of the sampling fluctuation `P_T P_Ω P_T - p P_T`
used in the Rudelson selection lemma (Rudelson 1999, J. Funct. Anal. 164, Thm 1).

Proof: each of the three constituent projections is self-adjoint because its
kernel is symmetric (`∑_k u_k i u_k a` and `∑_l v_l b v_l j`).  The two-sided
projection equals `left ∘ right = right ∘ left`, so its self-adjointness follows
from composing the two self-adjoint factors.  matrixInner is bilinear, so
self-adjointness distributes over the `+`/`-`.  Uses only the SVD orthonormality
data implicitly (in fact only symmetry of the kernels, not orthonormality).
-/
theorem solution
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    matrixInner (tangentProjection S A) B
      = matrixInner A (tangentProjection S B) := by
  -- inline helpers ----------------------------------------------------------
  -- kernel symmetry
  have PuK_symm_inline : ∀ (i a : Fin n1),
      (∑ k, S.u k i * S.u k a) = (∑ k, S.u k a * S.u k i) := by
    intro i a; apply Finset.sum_congr rfl; intro k _; ring
  have PvK_symm_inline : ∀ (b j : Fin n2),
      (∑ l, S.v l b * S.v l j) = (∑ l, S.v l j * S.v l b) := by
    intro b j; apply Finset.sum_congr rfl; intro l _; ring
  -- matrixInner bilinearity
  have matrixInner_add_left : ∀ (P Q C : RealMatrix n1 n2),
      matrixInner (P + Q) C = matrixInner P C + matrixInner Q C := by
    intro P Q C; unfold matrixInner
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; simp [add_mul]
  have matrixInner_sub_left : ∀ (P Q C : RealMatrix n1 n2),
      matrixInner (P - Q) C = matrixInner P C - matrixInner Q C := by
    intro P Q C; unfold matrixInner
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; simp [sub_mul]
  have matrixInner_add_right : ∀ (P Q C : RealMatrix n1 n2),
      matrixInner P (Q + C) = matrixInner P Q + matrixInner P C := by
    intro P Q C; unfold matrixInner
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; simp [mul_add]
  have matrixInner_sub_right : ∀ (P Q C : RealMatrix n1 n2),
      matrixInner P (Q - C) = matrixInner P Q - matrixInner P C := by
    intro P Q C; unfold matrixInner
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; simp [mul_sub]
  -- left self-adjoint
  have left_sa : ∀ (P Q : RealMatrix n1 n2),
      matrixInner (leftSingularProjection S P) Q
        = matrixInner P (leftSingularProjection S Q) := by
    intro P Q; unfold matrixInner leftSingularProjection
    rw [show (∑ i, ∑ j, (∑ a, (∑ k, S.u k i * S.u k a) * P a j) * Q i j)
          = ∑ i, ∑ j, ∑ a, (∑ k, S.u k i * S.u k a) * P a j * Q i j by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.sum_mul]]
    rw [show (∑ i, ∑ j, P i j * (∑ a, (∑ k, S.u k i * S.u k a) * Q a j))
          = ∑ i, ∑ j, ∑ a, (∑ k, S.u k i * S.u k a) * Q a j * P i j by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro a _; ring]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro i _
    rw [PuK_symm_inline i a]; ring
  -- right self-adjoint
  have right_sa : ∀ (P Q : RealMatrix n1 n2),
      matrixInner (rightSingularProjection S P) Q
        = matrixInner P (rightSingularProjection S Q) := by
    intro P Q; unfold matrixInner rightSingularProjection
    rw [show (∑ i, ∑ j, (∑ b, P i b * (∑ l, S.v l b * S.v l j)) * Q i j)
          = ∑ i, ∑ j, ∑ b, P i b * (∑ l, S.v l b * S.v l j) * Q i j by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.sum_mul]]
    rw [show (∑ i, ∑ j, P i j * (∑ b, Q i b * (∑ l, S.v l b * S.v l j)))
          = ∑ i, ∑ j, ∑ b, Q i b * (∑ l, S.v l b * S.v l j) * P i j by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro b _; ring]
    apply Finset.sum_congr rfl; intro i _
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro b _
    rw [PvK_symm_inline b j]; ring
  -- twoSided = left ∘ right and = right ∘ left
  have ts_lr : ∀ (X : RealMatrix n1 n2),
      twoSidedSingularProjection S X
        = leftSingularProjection S (rightSingularProjection S X) := by
    intro X; unfold twoSidedSingularProjection leftSingularProjection rightSingularProjection
    funext i j
    rw [show (∑ a, (∑ k, S.u k i * S.u k a) * (∑ b, X a b * (∑ l, S.v l b * S.v l j)))
          = ∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j) by
          apply Finset.sum_congr rfl; intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro b _; ring]
  have ts_rl : ∀ (X : RealMatrix n1 n2),
      twoSidedSingularProjection S X
        = rightSingularProjection S (leftSingularProjection S X) := by
    intro X; unfold twoSidedSingularProjection leftSingularProjection rightSingularProjection
    funext i j
    rw [show (∑ b, (∑ a, (∑ k, S.u k i * S.u k a) * X a b) * (∑ l, S.v l b * S.v l j))
          = ∑ a, ∑ b, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j) by
          rw [show (∑ b, (∑ a, (∑ k, S.u k i * S.u k a) * X a b) * (∑ l, S.v l b * S.v l j))
                = ∑ b, ∑ a, (∑ k, S.u k i * S.u k a) * X a b * (∑ l, S.v l b * S.v l j) by
                apply Finset.sum_congr rfl; intro b _
                rw [Finset.sum_mul]]
          rw [Finset.sum_comm]]
  -- twoSided self-adjoint via composition
  have ts_sa : ∀ (P Q : RealMatrix n1 n2),
      matrixInner (twoSidedSingularProjection S P) Q
        = matrixInner P (twoSidedSingularProjection S Q) := by
    intro P Q
    rw [ts_lr, left_sa, right_sa, ← ts_rl]
  -- assemble
  unfold tangentProjection
  rw [matrixInner_sub_left, matrixInner_add_left, left_sa, right_sa, ts_sa,
      matrixInner_sub_right, matrixInner_add_right]

end PriorAdj
#print axioms PriorAdj.solution


/-!
C1 — von Neumann / matrix trace-duality inequality:
  `matrixInner A B ≤ spectralNorm A * nuclearNorm B`.

Source: Candès–Recht 2009 (arXiv:0805.4471), §3 Lemma 3.2 first inequality
(von Neumann's trace inequality, 1937; see also Mirsky 1975).

Proof outline (built from Mathlib's self-adjoint spectral theorem; the SVD
reconstruction `B = Σ σ_k u_k v_k^T` is NOT available ready-made in this env's
Mathlib, so it is constructed here):
  * `T := toEuclideanLin B`, `G := Tᵀ∘T` symmetric and PSD.
  * `v_k := eigenvectorBasis G` orthonormal, eigenvalues `μ_k ≥ 0`,
    `σ_k = √μ_k = singularValues T k`.
  * `⟪T v_i, T v_j⟫ = ⟪G v_i, v_j⟫ = μ_i δ_ij`, so `‖T v_k‖ = σ_k`.
  * Frobenius inner product = Hilbert–Schmidt inner `∑_j ⟪S e_j, T e_j⟫`,
    which is `trace(Sᵀ∘T)` — basis-independent — hence `= ∑_k ⟪S v_k, T v_k⟫`.
  * `⟪S v_k, T v_k⟫ ≤ ‖S v_k‖·‖T v_k‖ ≤ ‖S‖·1·σ_k`; sum gives `‖S‖·Σσ_k`.
  * `Σ σ_k = nuclearNorm B`, `‖S‖ = spectralNorm A`.
-/

open Module InnerProductSpace LinearMap Matrix
open scoped BigOperators

/-! ### Operator-level SVD reconstruction & von Neumann inequality. -/

namespace SVDProbe

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

noncomputable abbrev gram (T : E →ₗ[ℝ] F) : E →ₗ[ℝ] E := adjoint T ∘ₗ T

theorem gram_symm (T : E →ₗ[ℝ] F) : (gram T).IsSymmetric :=
  T.isSymmetric_adjoint_comp_self

theorem gram_pos (T : E →ₗ[ℝ] F) : (gram T).IsPositive :=
  T.isPositive_adjoint_comp_self

noncomputable def rsv (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) :
    OrthonormalBasis (Fin n) ℝ E :=
  (gram_symm T).eigenvectorBasis hn

noncomputable def evals (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) : Fin n → ℝ :=
  (gram_symm T).eigenvalues hn

theorem evals_nonneg (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    0 ≤ evals T hn k :=
  (gram_pos T).nonneg_eigenvalues hn k

theorem inner_Tv (T : E →ₗ[ℝ] F) (a b : E) :
    inner ℝ (T a) (T b) = inner ℝ (gram T a) b := by
  unfold gram
  rw [LinearMap.comp_apply, ← LinearMap.adjoint_inner_left]

theorem inner_Tv_eig (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (i j : Fin n) :
    inner ℝ (T (rsv T hn i)) (T (rsv T hn j))
      = if i = j then evals T hn i else 0 := by
  rw [inner_Tv]
  unfold gram rsv evals
  rw [show (adjoint T ∘ₗ T) ((gram_symm T).eigenvectorBasis hn i)
        = (gram T) ((gram_symm T).eigenvectorBasis hn i) from rfl]
  rw [(gram_symm T).apply_eigenvectorBasis hn i]
  rw [inner_smul_left]
  rw [orthonormal_iff_ite.mp ((gram_symm T).eigenvectorBasis hn).orthonormal i j]
  simp only [conj_trivial]
  by_cases h : i = j
  · subst h; rw [if_pos rfl, if_pos rfl, mul_one, RCLike.ofReal_real_eq_id]; rfl
  · rw [if_neg h, if_neg h, mul_zero]

noncomputable def sval (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) : ℝ :=
  T.singularValues k

theorem sval_nonneg (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    0 ≤ sval T hn k := T.singularValues_nonneg k

theorem sval_sq (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    sval T hn k ^ 2 = evals T hn k := by
  unfold sval evals
  rw [T.sq_singularValues_fin hn k]

theorem norm_Tv (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (k : Fin n) :
    ‖T (rsv T hn k)‖ = sval T hn k := by
  have heig : inner ℝ (T (rsv T hn k)) (T (rsv T hn k)) = evals T hn k := by
    have h := inner_Tv_eig T hn k k
    rw [if_pos rfl] at h
    exact h
  have h2 : ‖T (rsv T hn k)‖ ^ 2 = sval T hn k ^ 2 := by
    rw [@norm_sq_eq_re_inner ℝ, heig, sval_sq, RCLike.re_to_real]
  have hnn := sval_nonneg T hn k
  nlinarith [norm_nonneg (T (rsv T hn k)), h2, hnn]

theorem hsInner_eq_trace {ι : Type*} [Fintype ι] (S T : E →ₗ[ℝ] F) (b : OrthonormalBasis ι ℝ E) :
    (∑ j, inner ℝ (S (b j)) (T (b j))) = (adjoint S ∘ₗ T).trace ℝ E := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro j _
  rw [LinearMap.comp_apply, ← LinearMap.adjoint_inner_right S (b j) (T (b j))]

theorem hsInner_basis_indep {ι : Type*} [Fintype ι] (S T : E →ₗ[ℝ] F)
    (b : OrthonormalBasis ι ℝ E) {n : ℕ} (hn : finrank ℝ E = n) :
    (∑ j, inner ℝ (S (b j)) (T (b j)))
      = ∑ k, inner ℝ (S (rsv T hn k)) (T (rsv T hn k)) := by
  rw [hsInner_eq_trace S T b, hsInner_eq_trace S T (rsv T hn)]

theorem vonNeumann_op {ι : Type*} [Fintype ι] (S : E →L[ℝ] F) (T : E →ₗ[ℝ] F)
    (b : OrthonormalBasis ι ℝ E) {n : ℕ} (hn : finrank ℝ E = n) :
    (∑ j, inner ℝ ((S : E →ₗ[ℝ] F) (b j)) (T (b j))) ≤ ‖S‖ * ∑ k, sval T hn k := by
  rw [hsInner_basis_indep (S : E →ₗ[ℝ] F) T b hn]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  have hSle : ‖(S : E →ₗ[ℝ] F) (rsv T hn k)‖ ≤ ‖S‖ * ‖(rsv T hn k : E)‖ := S.le_opNorm _
  calc inner ℝ ((S : E →ₗ[ℝ] F) (rsv T hn k)) (T (rsv T hn k))
      ≤ ‖(S : E →ₗ[ℝ] F) (rsv T hn k)‖ * ‖T (rsv T hn k)‖ := real_inner_le_norm _ _
    _ ≤ (‖S‖ * ‖(rsv T hn k : E)‖) * ‖T (rsv T hn k)‖ := by
          apply mul_le_mul_of_nonneg_right hSle (norm_nonneg _)
    _ = ‖S‖ * sval T hn k := by
          rw [(rsv T hn).orthonormal.1 k, norm_Tv]; ring

end SVDProbe

/-! ### Matrix specialization to the platform statement. -/

namespace MatrixCompletion

open SVDProbe

variable {n1 n2 : ℕ}

theorem matrixInner_eq_hsInner (A B : RealMatrix n1 n2) :
    matrixInner A B
      = ∑ j, inner ℝ ((toEuclideanLin A) (EuclideanSpace.basisFun (Fin n2) ℝ j))
                      ((toEuclideanLin B) (EuclideanSpace.basisFun (Fin n2) ℝ j)) := by
  unfold matrixInner
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.basisFun_apply]
  simp only [toEuclideanLin_apply]
  have hcol : ∀ (C : RealMatrix n1 n2),
      (C *ᵥ (EuclideanSpace.single j (1:ℝ)).ofLp) i = C i j := by
    intro C
    simp only [Matrix.mulVec, EuclideanSpace.ofLp_single, dotProduct_single, mul_one]
  rw [hcol A, hcol B]
  rw [show (⟪A i j, B i j⟫_ℝ : ℝ) = B i j * (starRingEnd ℝ) (A i j) from RCLike.inner_apply _ _,
      conj_trivial]; ring

theorem nuclearNorm_eq_sum_sval (B : RealMatrix n1 n2)
    (hn : finrank ℝ (EuclideanSpace ℝ (Fin n2)) = n2) :
    nuclearNorm B = ∑ k, sval (toEuclideanLin B) hn k := by
  unfold nuclearNorm sval
  set T := toEuclideanLin B
  rw [Finsupp.sum_of_support_subset T.singularValues
      (s := Finset.range n2) ?_ (fun _ x => x) (by intro _ _; rfl)]
  · rw [Finset.sum_range fun k => T.singularValues k]
  · intro k hk
    rw [Finset.mem_range]
    by_contra hge
    push_neg at hge
    have hz : T.singularValues k = 0 := by
      apply T.singularValues_of_finrank_le
      rw [hn]; exact hge
    rw [Finsupp.mem_support_iff] at hk
    exact hk hz

theorem trace_duality_C1 (A B : RealMatrix n1 n2) :
    matrixInner A B ≤ spectralNorm A * nuclearNorm B := by
  have hn : finrank ℝ (EuclideanSpace ℝ (Fin n2)) = n2 := finrank_euclideanSpace_fin
  rw [matrixInner_eq_hsInner A B, nuclearNorm_eq_sum_sval B hn]
  show (∑ j, inner ℝ ((toEuclideanLin A) (EuclideanSpace.basisFun (Fin n2) ℝ j))
                     ((toEuclideanLin B) (EuclideanSpace.basisFun (Fin n2) ℝ j)))
      ≤ spectralNorm A * ∑ k, sval (toEuclideanLin B) hn k
  unfold spectralNorm
  exact vonNeumann_op (LinearMap.toContinuousLinearMap (toEuclideanLin A))
    (toEuclideanLin B) (EuclideanSpace.basisFun (Fin n2) ℝ) hn

end MatrixCompletion

open MatrixCompletion
open scoped BigOperators

/-- C1 — von Neumann / matrix trace-duality inequality.
Source: Candès–Recht 2009 (arXiv:0805.4471), §3 Lemma 3.2, first inequality
(von Neumann's trace inequality 1937; Mirsky 1975). -/
theorem matrix_trace_duality_inequality {n₁ n₂ : ℕ} (A B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    matrixInner A B ≤ spectralNorm A * nuclearNorm B :=
  MatrixCompletion.trace_duality_C1 A B

open MatrixCompletion Module
namespace RectNuclear
-- Generalized from tianyipeng's LRMNucAux to rectangular matrices.
theorem range_rank {m n : ℕ} (X : RealMatrix m n) :
    finrank ℝ (LinearMap.range (Matrix.toEuclideanLin X)) = X.rank := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, ← Matrix.rank_eq_finrank_range_toLin]
theorem trace_self {m n : ℕ} (X : RealMatrix m n) :
    ((Matrix.toEuclideanLin X).adjoint ∘ₗ Matrix.toEuclideanLin X).trace ℝ _ =
      frobeniusNormSq X := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin n) ℝ)]
  unfold frobeniusNormSq
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq,
    EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem nuclear_le {m n : ℕ} (X : RealMatrix m n) :
    nuclearNorm X ≤ Real.sqrt (X.rank : ℝ) * frobeniusNorm X := by
  set T := Matrix.toEuclideanLin X
  have hfin : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hsupp := T.support_singularValues
  have hk : finrank ℝ (LinearMap.range T) = X.rank := range_rank X
  rw [hk] at hsupp
  have hnuc : nuclearNorm X = ∑ i ∈ Finset.range X.rank, T.singularValues i := by
    unfold nuclearNorm; rw [Finsupp.sum, hsupp]
  have hkp : X.rank ≤ n := Matrix.rank_le_width X
  have hsq : ∑ i ∈ Finset.range X.rank, T.singularValues i ^ 2 = frobeniusNormSq X := by
    have h1 : ∑ i ∈ Finset.range X.rank, T.singularValues i ^ 2 =
        ∑ i ∈ Finset.range n, T.singularValues i ^ 2 := by
      apply Finset.sum_subset (Finset.range_subset_range.2 hkp)
      intro i _ hi
      have : T.singularValues i = 0 := by
        by_contra hne
        have : i ∈ T.singularValues.support := Finsupp.mem_support_iff.2 hne
        rw [hsupp] at this; exact hi this
      simp [this]
    rw [h1, Finset.sum_range (fun i => T.singularValues i ^ 2)]
    have h2 : ∀ i : Fin n, T.singularValues i ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues hfin i :=
      fun i => T.sq_singularValues_fin hfin i
    simp_rw [h2]
    rw [← T.isSymmetric_adjoint_comp_self.re_trace_eq_sum_eigenvalues hfin]
    simp only [RCLike.re_to_real]
    exact trace_self X
  have hCS := sq_sum_le_card_mul_sum_sq (s := Finset.range X.rank) (f := fun i => T.singularValues i)
  rw [Finset.card_range, hsq, ← hnuc] at hCS
  unfold frobeniusNorm
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  exact Real.le_sqrt_of_sq_le hCS
end RectNuclear
#print axioms RectNuclear.nuclear_le

open MatrixCompletion Matrix
open scoped BigOperators
namespace TangentRank
variable {m n r : ℕ} {A : RealMatrix m n}
noncomputable def U (S : SVD A r) : Matrix (Fin m) (Fin r) ℝ := fun i k => S.u k i
noncomputable def V (S : SVD A r) : Matrix (Fin n) (Fin r) ℝ := fun j k => S.v k j
lemma utu (S : SVD A r) : (U S).transpose * U S = 1 := by
  ext k l
  simpa [Matrix.mul_apply,U,Matrix.one_apply] using S.u_orthonormal k l
lemma vtv (S : SVD A r) : (V S).transpose * V S = 1 := by
  ext k l
  simpa [Matrix.mul_apply,V,Matrix.one_apply] using S.v_orthonormal k l
lemma factor (S : SVD A r) : A = U S * Matrix.diagonal S.sigma * (V S).transpose := by
  calc A = ∑ k, S.sigma k • Matrix.vecMulVec (S.u k) (S.v k) := S.decomp
       _ = _ := by
        ext i j
        simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Matrix.vecMulVec_apply]
        change (∑ k, S.sigma k * (S.u k i * S.v k j)) =
          ∑ k, (U S * Matrix.diagonal S.sigma) i k * S.v k j
        simp only [Matrix.mul_diagonal,U]
        apply Finset.sum_congr rfl
        intro k hk
        ring
lemma rank_lower (S : SVD A r) : r ≤ A.rank := by
  classical
  have hd : (U S).transpose * A * V S = Matrix.diagonal S.sigma := by
    calc (U S).transpose * A * V S =
          (U S).transpose * (U S * Matrix.diagonal S.sigma * (V S).transpose) * V S :=
            congrArg (fun X : RealMatrix m n => (U S).transpose * X * V S) (factor S)
         _ = _ := by
          simp only [Matrix.mul_assoc,vtv,Matrix.mul_one]
          rw [← Matrix.mul_assoc,utu,Matrix.one_mul]
  have hr : (Matrix.diagonal S.sigma).rank = r := by
    have hnon : ∀ i, S.sigma i ≠ 0 := fun i => ne_of_gt (S.sigma_pos i)
    simp [Matrix.rank_diagonal,hnon]
  rw [← hr,← hd]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
lemma left_eq (S : SVD A r) (X : RealMatrix m n) :
    leftSingularProjection S X = (U S * (U S).transpose) * X := rfl
lemma right_eq (S : SVD A r) (X : RealMatrix m n) :
    rightSingularProjection S X = X * (V S * (V S).transpose) := rfl
lemma two_eq (S : SVD A r) (X : RealMatrix m n) :
    twoSidedSingularProjection S X = (U S * (U S).transpose) * (X * (V S * (V S).transpose)) := by
  ext i j
  simp only [twoSidedSingularProjection,Matrix.mul_apply,Matrix.transpose_apply,U,V,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring
lemma decomposition (S : SVD A r) (X : RealMatrix m n) :
    tangentProjection S X = ((1 - U S * (U S).transpose) * X * V S) * (V S).transpose +
      U S * ((U S).transpose * X) := by
  rw [tangentProjection,left_eq,right_eq,two_eq]
  simp only [Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc]
  abel
lemma rank_add {a b : ℕ} (X Y : RealMatrix a b) : (X+Y).rank ≤ X.rank + Y.rank := by
  unfold Matrix.rank
  refine le_trans (Submodule.finrank_mono ?_)
    (Submodule.finrank_add_le_finrank_add_finrank _ _)
  rintro y ⟨x,rfl⟩
  rw [Matrix.mulVecLin_apply,Matrix.add_mulVec]
  exact Submodule.add_mem_sup ⟨x,rfl⟩ ⟨x,rfl⟩
lemma tangent_rank (S : SVD A r) (X : RealMatrix m n) :
    (tangentProjection S X).rank ≤ 2*A.rank := by
  rw [decomposition]
  have h1 := Matrix.rank_mul_le_left (((1-U S*(U S).transpose)*X)*V S) (V S).transpose
  have h2 := Matrix.rank_le_width (((1-U S*(U S).transpose)*X)*V S)
  have h3 := Matrix.rank_mul_le_left (U S) ((U S).transpose*X)
  have h4 := Matrix.rank_le_width (U S)
  have h5 := rank_add ((((1-U S*(U S).transpose)*X)*V S)*(V S).transpose) (U S*((U S).transpose*X))
  have h6 := rank_lower S
  omega
end TangentRank
#print axioms TangentRank.tangent_rank

open MatrixCompletion
namespace TangentGeometry
lemma energy {m n r : ℕ} {A : RealMatrix m n} (S : SVD A r) (N : RealMatrix m n) :
    frobeniusNorm (tangentProjection S N)^2 = matrixInner N (tangentProjection S N) := by
  have hnn : 0 ≤ frobeniusNormSq (tangentProjection S N) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [frobeniusNorm,Real.sq_sqrt hnn]
  calc frobeniusNormSq (tangentProjection S N) =
       matrixInner (tangentProjection S N) (tangentProjection S N) := by
        simp [frobeniusNormSq,matrixInner,pow_two]
       _ = matrixInner N (tangentProjection S (tangentProjection S N)) := PriorAdj.solution S N _
       _ = _ := by rw [PriorIdem.solution]
lemma norm_bound {m n r : ℕ} {A : RealMatrix m n} (S : SVD A r) (N : RealMatrix m n) :
    frobeniusNorm (tangentProjection S N) ≤
      Real.sqrt ((tangentProjection S N).rank : ℝ) * spectralNorm N := by
  have hn : 0 ≤ spectralNorm N := norm_nonneg _
  have hf : 0 ≤ frobeniusNorm (tangentProjection S N) := Real.sqrt_nonneg _
  by_cases hz : frobeniusNorm (tangentProjection S N) = 0
  · rw [hz]; exact mul_nonneg (Real.sqrt_nonneg _) hn
  · apply (mul_le_mul_iff_right₀ (lt_of_le_of_ne hf (Ne.symm hz))).mp
    calc frobeniusNorm (tangentProjection S N) * frobeniusNorm (tangentProjection S N)
        = frobeniusNorm (tangentProjection S N)^2 := by ring
      _ = matrixInner N (tangentProjection S N) := energy S N
      _ ≤ spectralNorm N * nuclearNorm (tangentProjection S N) := matrix_trace_duality_inequality _ _
      _ ≤ spectralNorm N * (Real.sqrt ((tangentProjection S N).rank : ℝ) *
            frobeniusNorm (tangentProjection S N)) := mul_le_mul_of_nonneg_left (RectNuclear.nuclear_le _) hn
      _ = _ := by ring
end TangentGeometry
#print axioms TangentGeometry.norm_bound

open MatrixCompletion

/-- (2.15) and the bound on Λ = 2‖𝒫_A(N)‖₂ (p. 9), for an arbitrary matrix N in place of 𝐌:
𝒫_A(N) = P_{S₁⊥} N P_{S₂} + P_{S₁} N, and
Λ ≤ 2√(rank 𝒫_A(N)) ‖N‖∞ ≤ 2√(2 rank A) ‖N‖∞ ≤ √(2 rank A) λ when λ ≥ 2‖N‖∞. -/
theorem prior_lambda {m₁ m₂ r : ℕ} {A : RealMatrix m₁ m₂} (S : SVD A r) (N : RealMatrix m₁ m₂) :
    -- (2.15)
    tangentProjection S N =
        (rightSingularProjection S N - twoSidedSingularProjection S N) + leftSingularProjection S N ∧
      2 * frobeniusNorm (tangentProjection S N) ≤
        2 * Real.sqrt ((tangentProjection S N).rank : ℝ) * spectralNorm N ∧
      2 * Real.sqrt ((tangentProjection S N).rank : ℝ) * spectralNorm N ≤
        2 * Real.sqrt (2 * (A.rank : ℝ)) * spectralNorm N ∧
      ∀ lam : ℝ, 2 * spectralNorm N ≤ lam →
        2 * Real.sqrt (2 * (A.rank : ℝ)) * spectralNorm N ≤ Real.sqrt (2 * (A.rank : ℝ)) * lam := by
  have hn : 0 ≤ spectralNorm N := norm_nonneg _
  constructor
  · unfold tangentProjection; abel
  refine ⟨?_,?_,?_⟩
  · have h := TangentGeometry.norm_bound S N
    linarith
  · have hr : ((tangentProjection S N).rank : ℝ) ≤ 2*(A.rank : ℝ) := by
      exact_mod_cast TangentRank.tangent_rank S N
    have h := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hr) hn
    linarith
  · intro lam hlam
    have h := mul_le_mul_of_nonneg_left hlam (Real.sqrt_nonneg (2*(A.rank : ℝ)))
    nlinarith


#print axioms prior_lambda

namespace NormalHelper
open MatrixCompletion
open scoped Classical BigOperators
open Matrix LinearMap Module InnerProductSpace WithLp
variable {n₁ n₂ r : ℕ} {M : RealMatrix n₁ n₂}
theorem ker_idem {N r : Nat} (u : Fin r → (Fin N → ℝ))
    (horth : ∀ k l, ∑ i, u k i * u l i = if k = l then 1 else 0)
    (i b : Fin N) :
    (∑ a : Fin N, (∑ k : Fin r, u k i * u k a) * (∑ l : Fin r, u l a * u l b))
      = ∑ k : Fin r, u k i * u k b := by
  have e1 : (∑ a : Fin N, (∑ k : Fin r, u k i * u k a) * (∑ l : Fin r, u l a * u l b))
      = ∑ a : Fin N, ∑ k : Fin r, ∑ l : Fin r, (u k i * u k a) * (u l a * u l b) := by
    apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_mul_sum]
  rw [e1, Finset.sum_comm]
  have e2 : (∑ k : Fin r, ∑ a : Fin N, ∑ l : Fin r, (u k i * u k a) * (u l a * u l b))
      = ∑ k : Fin r, ∑ l : Fin r, (u k i * u l b) * (∑ a : Fin N, u k a * u l a) := by
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
  rw [e2]
  have e3 : (∑ k : Fin r, ∑ l : Fin r, (u k i * u l b) * (∑ a : Fin N, u k a * u l a))
      = ∑ k : Fin r, ∑ l : Fin r, (u k i * u l b) * (if k = l then 1 else 0) := by
    apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _; rw [horth k l]
  rw [e3]
  apply Finset.sum_congr rfl; intro k _
  have : (∑ l : Fin r, u k i * u l b * (if k = l then 1 else 0))
      = ∑ l : Fin r, (if k = l then u k i * u l b else 0) := by
    apply Finset.sum_congr rfl; intro l _; by_cases h : k = l <;> simp [h]
  rw [this, Finset.sum_ite_eq]; simp


theorem left_signMatrix (S : SVD M r) :
    leftSingularProjection S (signMatrix S) = signMatrix S := by
  funext i j
  unfold leftSingularProjection signMatrix
  -- signMatrix a j = ∑ l, u l a * v l j
  have hsm : ∀ a : Fin n₁, (∑ k, Matrix.vecMulVec (S.u k) (S.v k)) a j
      = ∑ l : Fin r, S.u l a * S.v l j := by
    intro a
    rw [Matrix.sum_apply]
    apply Finset.sum_congr rfl; intro l _
    rw [Matrix.vecMulVec_apply]
  simp only [hsm]
  -- LHS = ∑ a (∑ k u_k i u_k a)(∑ l u_l a v_l j)
  -- = ∑ k u_k i v_k j  (orthonormality of u)
  have hgoal : (∑ a : Fin n₁, (∑ k : Fin r, S.u k i * S.u k a) * (∑ l : Fin r, S.u l a * S.v l j))
      = ∑ k : Fin r, S.u k i * S.v k j := by
    have e1 : (∑ a : Fin n₁, (∑ k : Fin r, S.u k i * S.u k a) * (∑ l : Fin r, S.u l a * S.v l j))
        = ∑ a : Fin n₁, ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.u k a) * (S.u l a * S.v l j) := by
      apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_mul_sum]
    rw [e1, Finset.sum_comm]
    have e2 : (∑ k : Fin r, ∑ a : Fin n₁, ∑ l : Fin r, (S.u k i * S.u k a) * (S.u l a * S.v l j))
        = ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (∑ a : Fin n₁, S.u k a * S.u l a) := by
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro l _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
    rw [e2]
    have e3 : (∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (∑ a : Fin n₁, S.u k a * S.u l a))
        = ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (if k = l then 1 else 0) := by
      apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _
      rw [S.u_orthonormal k l]
    rw [e3]
    apply Finset.sum_congr rfl; intro k _
    have : (∑ l : Fin r, S.u k i * S.v l j * (if k = l then 1 else 0))
        = ∑ l : Fin r, (if k = l then S.u k i * S.v l j else 0) := by
      apply Finset.sum_congr rfl; intro l _; by_cases h : k = l <;> simp [h]
    rw [this, Finset.sum_ite_eq]; simp
  rw [hgoal]

theorem right_signMatrix (S : SVD M r) :
    rightSingularProjection S (signMatrix S) = signMatrix S := by
  funext i j
  unfold rightSingularProjection signMatrix
  have hsm : ∀ b : Fin n₂, (∑ k, Matrix.vecMulVec (S.u k) (S.v k)) i b
      = ∑ l : Fin r, S.u l i * S.v l b := by
    intro b
    rw [Matrix.sum_apply]
    apply Finset.sum_congr rfl; intro l _; rw [Matrix.vecMulVec_apply]
  simp only [hsm]
  have hgoal : (∑ b : Fin n₂, (∑ l : Fin r, S.u l i * S.v l b) * (∑ k : Fin r, S.v k b * S.v k j))
      = ∑ k : Fin r, S.u k i * S.v k j := by
    have e1 : (∑ b : Fin n₂, (∑ l : Fin r, S.u l i * S.v l b) * (∑ k : Fin r, S.v k b * S.v k j))
        = ∑ b : Fin n₂, ∑ l : Fin r, ∑ k : Fin r, (S.u l i * S.v l b) * (S.v k b * S.v k j) := by
      apply Finset.sum_congr rfl; intro b _; rw [Finset.sum_mul_sum]
    rw [e1, Finset.sum_comm]
    have e2 : (∑ l : Fin r, ∑ b : Fin n₂, ∑ k : Fin r, (S.u l i * S.v l b) * (S.v k b * S.v k j))
        = ∑ l : Fin r, ∑ k : Fin r, (S.u l i * S.v k j) * (∑ b : Fin n₂, S.v l b * S.v k b) := by
      apply Finset.sum_congr rfl; intro l _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
    rw [e2]
    have e3 : (∑ l : Fin r, ∑ k : Fin r, (S.u l i * S.v k j) * (∑ b : Fin n₂, S.v l b * S.v k b))
        = ∑ l : Fin r, ∑ k : Fin r, (S.u l i * S.v k j) * (if l = k then 1 else 0) := by
      apply Finset.sum_congr rfl; intro l _; apply Finset.sum_congr rfl; intro k _
      rw [S.v_orthonormal l k]
    rw [e3]
    apply Finset.sum_congr rfl; intro l _
    have : (∑ k : Fin r, S.u l i * S.v k j * (if l = k then 1 else 0))
        = ∑ k : Fin r, (if l = k then S.u l i * S.v k j else 0) := by
      apply Finset.sum_congr rfl; intro k _; by_cases h : l = k <;> simp [h]
    rw [this, Finset.sum_ite_eq]; simp
  rw [hgoal]

/-! ## Matrix projectors PU (n₁×n₁) and PV (n₂×n₂). -/

/-- Orthogonal projector onto the column singular space. -/
noncomputable def PUmat (S : SVD M r) : Matrix (Fin n₁) (Fin n₁) ℝ :=
  ∑ k, Matrix.vecMulVec (S.u k) (S.u k)

/-- Orthogonal projector onto the row singular space. -/
noncomputable def PVmat (S : SVD M r) : Matrix (Fin n₂) (Fin n₂) ℝ :=
  ∑ k, Matrix.vecMulVec (S.v k) (S.v k)

theorem PUmat_apply (S : SVD M r) (i a : Fin n₁) :
    PUmat S i a = ∑ k, S.u k i * S.u k a := by
  unfold PUmat
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl; intro k _; rw [Matrix.vecMulVec_apply]

theorem PVmat_apply (S : SVD M r) (b j : Fin n₂) :
    PVmat S b j = ∑ k, S.v k b * S.v k j := by
  unfold PVmat
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl; intro k _; rw [Matrix.vecMulVec_apply]

/-! ## Projector forms of the singular projections. -/

theorem left_eq_PU (S : SVD M r) (X : RealMatrix n₁ n₂) :
    leftSingularProjection S X = PUmat S * X := by
  funext i j
  unfold leftSingularProjection
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl; intro a _; rw [PUmat_apply]

theorem right_eq_PV (S : SVD M r) (X : RealMatrix n₁ n₂) :
    rightSingularProjection S X = X * PVmat S := by
  funext i j
  unfold rightSingularProjection
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl; intro b _; rw [PVmat_apply]

theorem two_eq_PU_PV (S : SVD M r) (X : RealMatrix n₁ n₂) :
    twoSidedSingularProjection S X = PUmat S * X * PVmat S := by
  funext i j
  unfold twoSidedSingularProjection
  rw [Matrix.mul_apply]
  -- (PU * X * PV) i j = ∑ b (PU*X) i b * PV b j = ∑ b (∑ a PU i a * X a b) * PV b j
  have hrew : ∀ b : Fin n₂, (PUmat S * X) i b * PVmat S b j
      = (∑ a : Fin n₁, (∑ k : Fin r, S.u k i * S.u k a) * X a b)
          * (∑ l : Fin r, S.v l b * S.v l j) := by
    intro b
    rw [Matrix.mul_apply, PVmat_apply]
    congr 1
    apply Finset.sum_congr rfl; intro a _; rw [PUmat_apply]
  rw [Finset.sum_congr rfl (fun b _ => hrew b)]
  -- target: ∑ a ∑ b (∑k u i a) X a b (∑l v b j) = ∑ b (∑ a (∑k u i a) X a b)(∑l v b j)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.sum_mul]

/-! ## Idempotence and symmetry of PU, PV. -/

theorem PU_idem (S : SVD M r) : PUmat S * PUmat S = PUmat S := by
  funext i j
  rw [Matrix.mul_apply]
  have : (∑ a : Fin n₁, PUmat S i a * PUmat S a j)
      = ∑ a : Fin n₁, (∑ k : Fin r, S.u k i * S.u k a) * (∑ l : Fin r, S.u l a * S.u l j) := by
    apply Finset.sum_congr rfl; intro a _; rw [PUmat_apply, PUmat_apply]
  rw [this, ker_idem S.u S.u_orthonormal i j, PUmat_apply]

theorem PV_idem (S : SVD M r) : PVmat S * PVmat S = PVmat S := by
  funext i j
  rw [Matrix.mul_apply]
  have : (∑ a : Fin n₂, PVmat S i a * PVmat S a j)
      = ∑ a : Fin n₂, (∑ k : Fin r, S.v k i * S.v k a) * (∑ l : Fin r, S.v l a * S.v l j) := by
    apply Finset.sum_congr rfl; intro a _; rw [PVmat_apply, PVmat_apply]
  rw [this, ker_idem S.v S.v_orthonormal i j, PVmat_apply]

theorem PU_symm (S : SVD M r) : (PUmat S)ᵀ = PUmat S := by
  funext i j
  rw [Matrix.transpose_apply, PUmat_apply, PUmat_apply]
  apply Finset.sum_congr rfl; intro k _; ring

theorem PV_symm (S : SVD M r) : (PVmat S)ᵀ = PVmat S := by
  funext i j
  rw [Matrix.transpose_apply, PVmat_apply, PVmat_apply]
  apply Finset.sum_congr rfl; intro k _; ring

/-! ## Factorization of the normal projection: W = (1-PU) Z (1-PV). -/

theorem normalProjection_factor (S : SVD M r) (Z : RealMatrix n₁ n₂) :
    normalProjection S Z = (1 - PUmat S) * Z * (1 - PVmat S) := by
  unfold normalProjection tangentProjection
  rw [left_eq_PU, right_eq_PV, two_eq_PU_PV]
  -- Z - (PU Z + Z PV - PU Z PV) = (1-PU) Z (1-PV)
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
  -- LHS = Z - (PU*Z + Z*PV - PU*Z*PV); RHS = (Z - Z*PV) - (PU*Z - PU*Z*PV)
  abel

/-! ## E = signMatrix S obeys PU E = E, E PV = E. -/

theorem PU_signMatrix (S : SVD M r) : PUmat S * signMatrix S = signMatrix S := by
  rw [← left_eq_PU, left_signMatrix]

theorem signMatrix_PV (S : SVD M r) : signMatrix S * PVmat S = signMatrix S := by
  rw [← right_eq_PV, right_signMatrix]

/-! ## Orthogonality crux: Eᵀ * W = 0  and  W * PV = 0. -/

theorem Etrans_W_eq_zero (S : SVD M r) (Z : RealMatrix n₁ n₂) :
    (signMatrix S)ᵀ * normalProjection S Z = 0 := by
  rw [normalProjection_factor]
  -- Eᵀ * (1-PU) * Z * (1-PV) ; Eᵀ * (1-PU) = Eᵀ - Eᵀ PU = Eᵀ - (PU E)ᵀ = Eᵀ - Eᵀ = 0
  have hEt : (signMatrix S)ᵀ * (1 - PUmat S) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    have : (signMatrix S)ᵀ * PUmat S = (signMatrix S)ᵀ := by
      have h := PU_signMatrix S
      have h2 : (PUmat S * signMatrix S)ᵀ = (signMatrix S)ᵀ := by rw [h]
      rw [Matrix.transpose_mul, PU_symm] at h2
      exact h2
    rw [this, sub_self]
  calc (signMatrix S)ᵀ * ((1 - PUmat S) * Z * (1 - PVmat S))
      = ((signMatrix S)ᵀ * (1 - PUmat S)) * Z * (1 - PVmat S) := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = 0 := by rw [hEt, Matrix.zero_mul, Matrix.zero_mul]

theorem W_PV_eq_zero (S : SVD M r) (Z : RealMatrix n₁ n₂) :
    normalProjection S Z * PVmat S = 0 := by
  rw [normalProjection_factor]
  have hPV : (1 - PVmat S) * PVmat S = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, PV_idem, sub_self]
  calc (1 - PUmat S) * Z * (1 - PVmat S) * PVmat S
      = (1 - PUmat S) * Z * ((1 - PVmat S) * PVmat S) := by rw [Matrix.mul_assoc]
    _ = 0 := by rw [hPV, Matrix.mul_zero]

/-! ## E = E PV (already from right_signMatrix). -/

theorem signMatrix_eq_signMatrix_PV (S : SVD M r) :
    signMatrix S = signMatrix S * PVmat S := (signMatrix_PV S).symm

/-! ## Analytic part. -/

/-- ofLp of the Euclidean image is the matrix-vector product. -/
theorem ofLp_image (A : RealMatrix n₁ n₂) (x : EuclideanSpace ℝ (Fin n₂)) :
    ofLp ((toEuclideanLin A) x) = A *ᵥ ofLp x :=
  Matrix.ofLp_toEuclideanLin_apply A x

/-- Euclidean inner product as coordinate sum (for ℝ). -/
theorem eucl_inner_eq_sum {N : ℕ} (a b : EuclideanSpace ℝ (Fin N)) :
    (inner ℝ a b : ℝ) = ∑ i, (ofLp a) i * (ofLp b) i := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl; intro i _
  rw [show (⟪a i, b i⟫_ℝ : ℝ) = b i * (starRingEnd ℝ) (a i) from RCLike.inner_apply _ _,
      conj_trivial]; ring

/-- Inner product of two Euclidean images as a coordinate sum of matrix-vector products. -/
theorem inner_image_eq_sum (B C : RealMatrix n₁ n₂) (x : EuclideanSpace ℝ (Fin n₂)) :
    (inner ℝ ((toEuclideanLin B) x) ((toEuclideanLin C) x) : ℝ)
      = ∑ i, (B *ᵥ ofLp x) i * (C *ᵥ ofLp x) i := by
  rw [eucl_inner_eq_sum, ofLp_image, ofLp_image]

/-- A bilinear quadratic form `∑ᵢ (B x)ᵢ (C x)ᵢ` expands as `∑_{p,q} (Bᵀ C)_{pq} xₚ x_q`. -/
theorem mulVec_dot_eq_transpose_mul (B C : RealMatrix n₁ n₂) (x : Fin n₂ → ℝ) :
    (∑ i, (B *ᵥ x) i * (C *ᵥ x) i)
      = ∑ p, ∑ q, (Bᵀ * C) p q * x p * x q := by
  have e1 : (∑ i, (B *ᵥ x) i * (C *ᵥ x) i)
      = ∑ i, (∑ p, B i p * x p) * (∑ q, C i q * x q) := by
    apply Finset.sum_congr rfl; intro i _
    rw [Matrix.mulVec, Matrix.mulVec]; rfl
  rw [e1]
  -- expand each product, swap sums to pull i innermost
  have e2 : (∑ i, (∑ p, B i p * x p) * (∑ q, C i q * x q))
      = ∑ i, ∑ p, ∑ q, (B i p * C i q) * (x p * x q) := by
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro p _
    apply Finset.sum_congr rfl; intro q _; ring
  rw [e2, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro q _
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  rw [Matrix.transpose_apply]; ring

/-- If `Bᵀ C = 0` then `∑ᵢ (B x)ᵢ (C x)ᵢ = 0`. -/
theorem mulVec_dot_eq_zero_of_transpose_mul_zero (B C : RealMatrix n₁ n₂)
    (h : Bᵀ * C = 0) (x : Fin n₂ → ℝ) :
    (∑ i, (B *ᵥ x) i * (C *ᵥ x) i) = 0 := by
  rw [mulVec_dot_eq_transpose_mul, h]
  simp

/-! ## Euclidean norm-squared as a quadratic form. -/

/-- `‖a‖² = ∑ᵢ (ofLp a)ᵢ²`. -/
theorem normSq_eq_sum {N : ℕ} (a : EuclideanSpace ℝ (Fin N)) :
    ‖a‖ ^ 2 = ∑ i, (ofLp a) i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, eucl_inner_eq_sum]
  apply Finset.sum_congr rfl; intro i _; ring

/-- `‖B y‖² = ∑_{p,q} (Bᵀ B)_{pq} yₚ y_q` for the Euclidean image. -/
theorem normSq_image_eq_quad (B : RealMatrix n₁ n₂) (y : EuclideanSpace ℝ (Fin n₂)) :
    ‖(toEuclideanLin B) y‖ ^ 2
      = ∑ p, ∑ q, (Bᵀ * B) p q * (ofLp y) p * (ofLp y) q := by
  rw [normSq_eq_sum]
  have : (∑ i, (ofLp ((toEuclideanLin B) y)) i ^ 2)
      = ∑ i, (B *ᵥ ofLp y) i * (B *ᵥ ofLp y) i := by
    apply Finset.sum_congr rfl; intro i _; rw [ofLp_image]; ring
  rw [this, mulVec_dot_eq_transpose_mul]

/-- `‖y‖² = ∑_{p,q} (1)_{pq} yₚ y_q`. -/
theorem normSq_eq_one_quad {N : ℕ} (y : EuclideanSpace ℝ (Fin N)) :
    ‖y‖ ^ 2 = ∑ p, ∑ q, (1 : Matrix (Fin N) (Fin N) ℝ) p q * (ofLp y) p * (ofLp y) q := by
  rw [normSq_eq_sum]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.sum_eq_single p]
  · rw [Matrix.one_apply_eq]; ring
  · intro q _ hq; rw [Matrix.one_apply_ne (Ne.symm hq)]; ring
  · intro h; exact absurd (Finset.mem_univ p) h

/-- Pythagorean split for a symmetric idempotent square matrix `P`. -/
theorem pythagoras_split {N : ℕ} (P : Matrix (Fin N) (Fin N) ℝ)
    (hsymm : Pᵀ = P) (hidem : P * P = P) (y : EuclideanSpace ℝ (Fin N)) :
    ‖(toEuclideanLin P) y‖ ^ 2 + ‖(toEuclideanLin (1 - P)) y‖ ^ 2 = ‖y‖ ^ 2 := by
  have hPtP : Pᵀ * P = P := by rw [hsymm, hidem]
  have hQtQ : (1 - P)ᵀ * (1 - P) = 1 - P := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, hsymm]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hidem]
    abel
  rw [normSq_image_eq_quad, hPtP, normSq_image_eq_quad, hQtQ, normSq_eq_one_quad]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro p _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro q _
  rw [Matrix.sub_apply, Matrix.one_apply]
  by_cases h : p = q
  · simp only [if_pos h]; ring
  · simp only [if_neg h]; ring

/-! ## Operator-norm bound transport. -/

/-- `‖B y‖ ≤ spectralNorm B · ‖y‖`. -/
theorem norm_image_le (B : RealMatrix n₁ n₂) (y : EuclideanSpace ℝ (Fin n₂)) :
    ‖(toEuclideanLin B) y‖ ≤ spectralNorm B * ‖y‖ := by
  unfold MatrixCompletion.spectralNorm
  have h := (LinearMap.toContinuousLinearMap (toEuclideanLin B)).le_opNorm y
  simpa using h

/-- Orthogonal projection `1-P` (symmetric idempotent `P`) is a contraction. -/
theorem norm_compl_le {N : ℕ} (P : Matrix (Fin N) (Fin N) ℝ)
    (hsymm : Pᵀ = P) (hidem : P * P = P) (y : EuclideanSpace ℝ (Fin N)) :
    ‖(toEuclideanLin (1 - P)) y‖ ≤ ‖y‖ := by
  have hsplit := pythagoras_split P hsymm hidem y
  have hle : ‖(toEuclideanLin (1 - P)) y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg ‖(toEuclideanLin P) y‖]
  have h1 := norm_nonneg ((toEuclideanLin (1 - P)) y)
  have h2 := norm_nonneg y
  nlinarith [hle, h1, h2]

/-! ## `toEuclideanLin` is multiplicative / additive (transported through `ofLp`). -/

theorem toEuclideanLin_mul_apply {n₀ : ℕ} (A : RealMatrix n₀ n₁) (B : RealMatrix n₁ n₂)
    (x : EuclideanSpace ℝ (Fin n₂)) :
    (toEuclideanLin (A * B)) x = (toEuclideanLin A) ((toEuclideanLin B) x) := by
  apply ofLp_injective
  rw [ofLp_image, ofLp_image, ofLp_image, Matrix.mulVec_mulVec]

theorem toEuclideanLin_add_apply (A B : RealMatrix n₁ n₂) (x : EuclideanSpace ℝ (Fin n₂)) :
    (toEuclideanLin (A + B)) x = (toEuclideanLin A) x + (toEuclideanLin B) x := by
  apply ofLp_injective
  rw [ofLp_image]
  rw [show ofLp ((toEuclideanLin A) x + (toEuclideanLin B) x)
        = ofLp ((toEuclideanLin A) x) + ofLp ((toEuclideanLin B) x) from rfl]
  rw [ofLp_image, ofLp_image, Matrix.add_mulVec]


theorem normal_contraction (S : SVD M r) (N : RealMatrix n₁ n₂) :
    MatrixCompletion.spectralNorm (normalProjection S N) ≤ MatrixCompletion.spectralNorm N := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖(toEuclideanLin (normalProjection S N)) x‖ ≤ MatrixCompletion.spectralNorm N * ‖x‖
  rw [normalProjection_factor,toEuclideanLin_mul_apply,toEuclideanLin_mul_apply]
  calc ‖(toEuclideanLin (1-PUmat S)) ((toEuclideanLin N) ((toEuclideanLin (1-PVmat S)) x))‖
      ≤ ‖(toEuclideanLin N) ((toEuclideanLin (1-PVmat S)) x)‖ :=
        norm_compl_le _ (PU_symm S) (PU_idem S) _
    _ ≤ MatrixCompletion.spectralNorm N * ‖(toEuclideanLin (1-PVmat S)) x‖ := norm_image_le N _
    _ ≤ MatrixCompletion.spectralNorm N * ‖x‖ := mul_le_mul_of_nonneg_left
      (norm_compl_le _ (PV_symm S) (PV_idem S) x) (norm_nonneg _)
end NormalHelper
#print axioms NormalHelper.normal_contraction

open MatrixCompletion
open scoped BigOperators
namespace NoiseBase
lemma inner_self (m n : ℕ) (A : RealMatrix m n) : matrixInner A A = frobeniusNorm A ^ 2 := by
  rw [frobeniusNorm,Real.sq_sqrt]
  · simp [matrixInner,frobeniusNormSq,pow_two]
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
lemma cauchy {m n : ℕ} (A B : RealMatrix m n) :
    |matrixInner A B| ≤ frobeniusNorm A * frobeniusNorm B := by
  have hp := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin m × Fin n))
    (fun p => A p.1 p.2) (fun p => B p.1 p.2)
  have hm := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin m × Fin n))
    (fun p => -(A p.1 p.2)) (fun p => B p.1 p.2)
  simp only [Fintype.sum_prod_type,neg_mul,neg_sq,Finset.sum_neg_distrib] at hp hm
  exact abs_le.mpr ⟨by simpa [matrixInner,frobeniusNorm,frobeniusNormSq] using neg_le_neg hm,
    by simpa [matrixInner,frobeniusNorm,frobeniusNormSq] using hp⟩
lemma tangent_contraction {m n r : ℕ} {A : RealMatrix m n} (S : SVD A r) (X : RealMatrix m n) :
    frobeniusNorm (tangentProjection S X) ≤ frobeniusNorm X := by
  have h := (le_abs_self (matrixInner X (tangentProjection S X))).trans (cauchy X (tangentProjection S X))
  rw [← TangentGeometry.energy] at h
  have hx := Real.sqrt_nonneg (frobeniusNormSq X)
  have hp := Real.sqrt_nonneg (frobeniusNormSq (tangentProjection S X))
  change 0 ≤ frobeniusNorm X at hx
  change 0 ≤ frobeniusNorm (tangentProjection S X) at hp
  nlinarith
lemma normal_zero {m n r : ℕ} {A : RealMatrix m n} (S : SVD A r) : normalProjection S A = 0 := by
  have hl : leftSingularProjection S A = A := by
    rw [TangentRank.left_eq]
    calc (TangentRank.U S * (TangentRank.U S).transpose) * A =
        (TangentRank.U S * (TangentRank.U S).transpose) *
          (TangentRank.U S * Matrix.diagonal S.sigma * (TangentRank.V S).transpose) :=
            congrArg (fun X : RealMatrix m n => (TangentRank.U S * (TangentRank.U S).transpose)*X) (TangentRank.factor S)
      _ = TangentRank.U S * (((TangentRank.U S).transpose * TangentRank.U S) *
            (Matrix.diagonal S.sigma * (TangentRank.V S).transpose)) := by
              simp only [Matrix.mul_assoc]
      _ = TangentRank.U S * Matrix.diagonal S.sigma * (TangentRank.V S).transpose := by
        rw [TangentRank.utu,Matrix.one_mul,Matrix.mul_assoc]
      _ = A := (TangentRank.factor S).symm
  have ht : twoSidedSingularProjection S A = rightSingularProjection S A := by
    rw [TangentRank.two_eq,← Matrix.mul_assoc,← TangentRank.left_eq,hl,← TangentRank.right_eq]
  simp [normalProjection,tangentProjection,hl,ht]
end NoiseBase
#print axioms NoiseBase.cauchy
#print axioms NoiseBase.tangent_contraction
#print axioms NoiseBase.normal_zero

open MatrixCompletion
open scoped BigOperators

namespace NoiseDecomposition
lemma inner_sub_left {m n : ℕ} (X Y Z : RealMatrix m n) :
    matrixInner (X-Y) Z = matrixInner X Z - matrixInner Y Z := by
  simp [matrixInner, sub_mul, Finset.sum_sub_distrib]
lemma inner_sub_right {m n : ℕ} (X Y Z : RealMatrix m n) :
    matrixInner X (Y-Z) = matrixInner X Y - matrixInner X Z := by
  simp [matrixInner, mul_sub, Finset.sum_sub_distrib]

lemma decomposition {m n r : ℕ} {A : RealMatrix m n} (S : SVD A r)
    (X Y : RealMatrix m n) :
    matrixInner X Y = matrixInner (tangentProjection S X) (tangentProjection S Y) +
      matrixInner (normalProjection S X) (normalProjection S Y) := by
  have hxy := PriorAdj.solution S X Y
  have hpp := PriorAdj.solution S X (tangentProjection S Y)
  rw [PriorIdem.solution] at hpp
  simp only [normalProjection, inner_sub_left, inner_sub_right]
  linarith

lemma normal_sub {m n r : ℕ} {A : RealMatrix m n} (S : SVD A r)
    (X Y : RealMatrix m n) :
    normalProjection S (X-Y) = normalProjection S X - normalProjection S Y := by
  simp only [NormalHelper.normalProjection_factor, Matrix.mul_sub, Matrix.sub_mul]
  abel

lemma abs_duality {m n : ℕ} (X Y : RealMatrix m n) :
    |matrixInner X Y| ≤ spectralNorm X * nuclearNorm Y := by
  have hp := matrix_trace_duality_inequality X Y
  have hm := matrix_trace_duality_inequality (-X) Y
  have hn : spectralNorm (-X) = spectralNorm X := by simp [MatrixCompletion.spectralNorm]
  have hi : matrixInner (-X) Y = -matrixInner X Y := by
    simp [matrixInner, Finset.sum_neg_distrib]
  rw [hn,hi] at hm
  exact abs_le.mpr ⟨by linarith, hp⟩
end NoiseDecomposition

theorem solution {m₁ m₂ r : ℕ} {A : RealMatrix m₁ m₂}
    (S : SVD A r) (N B : RealMatrix m₁ m₂) :
    2 * |matrixInner N (B - A)| ≤
        2 * frobeniusNorm (tangentProjection S N) * frobeniusNorm (tangentProjection S (B - A)) +
          2 * spectralNorm (normalProjection S N) * nuclearNorm (normalProjection S B) ∧
      2 * frobeniusNorm (tangentProjection S N) * frobeniusNorm (tangentProjection S (B - A)) +
          2 * spectralNorm (normalProjection S N) * nuclearNorm (normalProjection S B) ≤
        2 * frobeniusNorm (tangentProjection S N) * frobeniusNorm (B - A) +
          2 * spectralNorm (normalProjection S N) * nuclearNorm (normalProjection S B) ∧
      2 * spectralNorm (normalProjection S N) ≤ 2 * spectralNorm N := by
  have hn : normalProjection S (B-A) = normalProjection S B := by
    rw [NoiseDecomposition.normal_sub, NoiseBase.normal_zero, sub_zero]
  have hd := NoiseDecomposition.decomposition S N (B-A)
  rw [hn] at hd
  have ht := NoiseBase.cauchy (tangentProjection S N) (tangentProjection S (B-A))
  have hq := NoiseDecomposition.abs_duality (normalProjection S N) (normalProjection S B)
  have ha := abs_add_le (matrixInner (tangentProjection S N) (tangentProjection S (B-A)))
    (matrixInner (normalProjection S N) (normalProjection S B))
  rw [← hd] at ha
  refine ⟨by nlinarith, ?_, ?_⟩
  · have hf : 0 ≤ frobeniusNorm (tangentProjection S N) := Real.sqrt_nonneg _
    have hc := NoiseBase.tangent_contraction S (B-A)
    nlinarith
  · exact mul_le_mul_of_nonneg_left (NormalHelper.normal_contraction S N) (by norm_num)

#print axioms solution
