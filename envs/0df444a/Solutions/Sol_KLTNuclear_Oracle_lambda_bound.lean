-- Prove2me | solution 1 for KLTNuclear.Oracle.lambda_bound
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T15:06:36.360325+00:00
-- url     : https://prove2.me/submissions/ed9bb1e4-3339-470d-ab81-a23455f7d3e7

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
theorem solution {m₁ m₂ r : ℕ} {A : RealMatrix m₁ m₂} (S : SVD A r) (N : RealMatrix m₁ m₂) :
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


#print axioms solution
