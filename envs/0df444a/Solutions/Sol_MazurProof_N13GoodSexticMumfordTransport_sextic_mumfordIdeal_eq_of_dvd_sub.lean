-- Prove2me | solution 1 for MazurProof.N13GoodSexticMumfordTransport.sextic_mumfordIdeal_eq_of_dvd_sub
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T03:46:07.752871+00:00
-- url     : https://prove2.me/submissions/b5726104-92c4-48bb-82b3-e0024b002642

import Mathlib
import Definitions.Def_MazurN13_L1

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv

-- ===== FLT.Assumptions.MazurProof.N13GoodSexticMumfordTransport =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodSexticMumfordTransport =====
section
/-!
# Transporting N13 Mumford graph ideals through completion of the square

The rational change of coordinates

`Y = 2y + (X³ + X + 1)`

does more than identify the two affine coordinate rings.  It sends the
generalized graph ideal `(u, y - v)` exactly to the sextic graph ideal
`(u, Y - (2v + X³ + X + 1))`.  The factor `1 / 2` appearing on the second
generator is a unit in the base field, so it does not change the generated
ideal.
-/
open Polynomial
namespace MazurProof.N13GoodSexticMumfordTransport
noncomputable section
open N13GoodSexticCoordinateEquiv
universe u
variable {K : Type u} [Field K] [CharZero K]
/-- Congruent graph polynomials define the same sextic graph ideal. -/
theorem sextic_mumfordIdeal_eq_of_dvd_sub
    (u v w : K[X]) (hvw : u ∣ v - w) :
    SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u v =
      SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u w := by
  obtain ⟨q, hq⟩ := hvw
  have hxsub :
      SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) (v - w) =
        SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) v -
          SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) w := by
    change (N13GoodSexticCoordinateEquiv.sexticXHom (K := K)) (v - w) =
      (N13GoodSexticCoordinateEquiv.sexticXHom (K := K)) v - (N13GoodSexticCoordinateEquiv.sexticXHom (K := K)) w
    exact map_sub (N13GoodSexticCoordinateEquiv.sexticXHom (K := K)) v w
  have hxmul :
      SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) (u * q) =
        SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) u *
          SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) q := by
    change (N13GoodSexticCoordinateEquiv.sexticXHom (K := K)) (u * q) =
      (N13GoodSexticCoordinateEquiv.sexticXHom (K := K)) u * (N13GoodSexticCoordinateEquiv.sexticXHom (K := K)) q
    exact map_mul (N13GoodSexticCoordinateEquiv.sexticXHom (K := K)) u q
  have hyw :
      SexticMumford.ySubClass (N13GoodSexticCoordinateEquiv.M (K := K)) w =
        SexticMumford.ySubClass (N13GoodSexticCoordinateEquiv.M (K := K)) v +
          SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) u *
            SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) q := by
    unfold SexticMumford.ySubClass
    rw [← hxmul, ← hq, hxsub]
    ring
  have hyv :
      SexticMumford.ySubClass (N13GoodSexticCoordinateEquiv.M (K := K)) v =
        SexticMumford.ySubClass (N13GoodSexticCoordinateEquiv.M (K := K)) w -
          SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) u *
            SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) q := by
    rw [hyw]
    ring
  have hxv :
      SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) u ∈
        SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u v :=
    SexticMumford.xClass_mem_mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u v
  have hxw :
      SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) u ∈
        SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u w :=
    SexticMumford.xClass_mem_mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u w
  have hyvmem :
      SexticMumford.ySubClass (N13GoodSexticCoordinateEquiv.M (K := K)) v ∈
        SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u v := by
    unfold SexticMumford.mumfordIdeal
    exact Ideal.subset_span (by simp)
  have hywmem :
      SexticMumford.ySubClass (N13GoodSexticCoordinateEquiv.M (K := K)) w ∈
        SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u w := by
    unfold SexticMumford.mumfordIdeal
    exact Ideal.subset_span (by simp)
  have hmulv :
      SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) u *
          SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) q ∈
        SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u v := by
    simpa only [mul_comm] using
      Ideal.mul_mem_left
        (SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u v)
        (SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) q) hxv
  have hmulw :
      SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) u *
          SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) q ∈
        SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u w := by
    simpa only [mul_comm] using
      Ideal.mul_mem_left
        (SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u w)
        (SexticMumford.xClass (N13GoodSexticCoordinateEquiv.M (K := K)) q) hxw
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact hxw
    · rw [hz, hyv]
      exact Ideal.sub_mem
        (SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u w)
        hywmem
        hmulw
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact hxv
    · rw [hz, hyw]
      exact Ideal.add_mem
        (SexticMumford.mumfordIdeal (N13GoodSexticCoordinateEquiv.M (K := K)) u v)
        hyvmem
        hmulv
end
end MazurProof.N13GoodSexticMumfordTransport
end

end

theorem solution : type_of% @MazurProof.N13GoodSexticMumfordTransport.sextic_mumfordIdeal_eq_of_dvd_sub := @MazurProof.N13GoodSexticMumfordTransport.sextic_mumfordIdeal_eq_of_dvd_sub
