-- Prove2me | solution 1 for ModularCurve.R2geoDet.coordDet_eq_algebraMap_of_similitude
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/6fb207c7-397b-508e-bb51-96cb9d022f6b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_R2geoDet_coordDet_eq_algebraMap_of_similitude

set_option autoImplicit false

noncomputable section

theorem solution
    (K : Type) [Field K] [CharZero K]
    (A : Type) [CommRing A] [Algebra K A]
    (V : Type) [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V]
    (b : Module.Basis (Fin 2) A V)
    (B : V →ₗ[K] V →ₗ[K] K)
    (hbal : ∀ (a : A) (v w : V), B (a • v) w = B v (a • w))
    (halt : ∀ v : V, B v v = 0)
    (hnd : ∀ v : V, (∀ w : V, B v w = 0) → v = 0)
    (f : V →ₗ[K] V) (hfA : ∀ (a : A) (v : V), f (a • v) = a • f v)
    (c : K) (hsim : ∀ v w : V, B (f v) (f w) = c • B v w) :
    (b.repr (f (b 0))) 0 * (b.repr (f (b 1))) 1
      - (b.repr (f (b 1))) 0 * (b.repr (f (b 0))) 1
    = algebraMap K A c := by
  have h2K : (2 : K) ≠ 0 := by norm_num

  have hanti : ∀ v w : V, B v w = - B w v := by
    intro v w
    have h := halt (v + w)
    simp only [map_add, LinearMap.add_apply, halt v, halt w, zero_add, add_zero] at h
    linear_combination h

  have key : ∀ (a : A) (v : V), B v (a • v) = 0 := by
    intro a v
    have h1 : B (a • v) v = - B v (a • v) := hanti (a • v) v
    rw [hbal a v v] at h1
    have h2 : (2 : K) * B v (a • v) = 0 := by
      rw [two_mul]
      nth_rewrite 1 [h1]
      exact neg_add_cancel _
    exact (mul_eq_zero.mp h2).resolve_left h2K

  have flip : ∀ e : A, B (b 1) (e • b 0) = - B (b 0) (e • b 1) := by
    intro e
    rw [← hbal e (b 1) (b 0)]
    exact hanti (e • b 1) (b 0)

  have hf0 : f (b 0) = (b.repr (f (b 0))) 0 • b 0 + (b.repr (f (b 0))) 1 • b 1 := by
    conv_lhs => rw [← b.sum_repr (f (b 0))]
    rw [Fin.sum_univ_two]
  have hf1 : f (b 1) = (b.repr (f (b 1))) 0 • b 0 + (b.repr (f (b 1))) 1 • b 1 := by
    conv_lhs => rw [← b.sum_repr (f (b 1))]
    rw [Fin.sum_univ_two]

  have main : ∀ a : A,
      B (b 0) ((a * ((b.repr (f (b 0))) 0 * (b.repr (f (b 1))) 1
          - (b.repr (f (b 1))) 0 * (b.repr (f (b 0))) 1 - algebraMap K A c)) • b 1) = 0 := by
    intro a
    have hs := hsim (a • b 0) (b 1)
    rw [hfA a (b 0), hbal a (f (b 0)) (f (b 1)), hf0, hf1, smul_add, smul_smul, smul_smul] at hs
    simp only [map_add, LinearMap.add_apply] at hs

    rw [hbal ((b.repr (f (b 0))) 0) (b 0) ((a * (b.repr (f (b 1))) 0) • b 0), smul_smul,
        key ((b.repr (f (b 0))) 0 * (a * (b.repr (f (b 1))) 0)) (b 0)] at hs
    rw [hbal ((b.repr (f (b 0))) 0) (b 0) ((a * (b.repr (f (b 1))) 1) • b 1), smul_smul] at hs
    rw [hbal ((b.repr (f (b 0))) 1) (b 1) ((a * (b.repr (f (b 1))) 0) • b 0), smul_smul,
        flip ((b.repr (f (b 0))) 1 * (a * (b.repr (f (b 1))) 0))] at hs
    rw [hbal ((b.repr (f (b 0))) 1) (b 1) ((a * (b.repr (f (b 1))) 1) • b 1), smul_smul,
        key ((b.repr (f (b 0))) 1 * (a * (b.repr (f (b 1))) 1)) (b 1)] at hs

    rw [hbal a (b 0) (b 1), ← map_smul (B (b 0)) c (a • b 1),
        ← algebraMap_smul A c (a • b 1), smul_smul] at hs

    have hcol :
        B (b 0) (((b.repr (f (b 0))) 0 * (a * (b.repr (f (b 1))) 1)) • b 1)
          - B (b 0) (((b.repr (f (b 0))) 1 * (a * (b.repr (f (b 1))) 0)) • b 1)
          - B (b 0) ((algebraMap K A c * a) • b 1) = 0 := by
      linear_combination hs
    rw [← map_sub, ← sub_smul, ← map_sub, ← sub_smul] at hcol
    have harr : a * ((b.repr (f (b 0))) 0 * (b.repr (f (b 1))) 1
          - (b.repr (f (b 1))) 0 * (b.repr (f (b 0))) 1 - algebraMap K A c)
        = (b.repr (f (b 0))) 0 * (a * (b.repr (f (b 1))) 1)
          - (b.repr (f (b 0))) 1 * (a * (b.repr (f (b 1))) 0)
          - algebraMap K A c * a := by ring
    rw [harr]
    exact hcol

  have main0 : ∀ a : A, B (a • b 0) (((b.repr (f (b 0))) 0 * (b.repr (f (b 1))) 1
      - (b.repr (f (b 1))) 0 * (b.repr (f (b 0))) 1 - algebraMap K A c) • b 1) = 0 := by
    intro a
    rw [hbal, smul_smul]
    exact main a
  have main1 : ∀ a : A, B (a • b 1) (((b.repr (f (b 0))) 0 * (b.repr (f (b 1))) 1
      - (b.repr (f (b 1))) 0 * (b.repr (f (b 0))) 1 - algebraMap K A c) • b 1) = 0 := by
    intro a
    rw [hbal, smul_smul]
    exact key _ _
  have hz : ∀ v : V, B v (((b.repr (f (b 0))) 0 * (b.repr (f (b 1))) 1
      - (b.repr (f (b 1))) 0 * (b.repr (f (b 0))) 1 - algebraMap K A c) • b 1) = 0 := by
    intro v
    conv_lhs => rw [← b.sum_repr v, Fin.sum_univ_two]
    rw [map_add, LinearMap.add_apply, main0, main1, add_zero]
  have hzz : ((b.repr (f (b 0))) 0 * (b.repr (f (b 1))) 1
      - (b.repr (f (b 1))) 0 * (b.repr (f (b 0))) 1 - algebraMap K A c) • b 1 = 0 := by
    refine hnd _ fun w => ?_
    rw [hanti, hz w, neg_zero]

  have h5 : (b.repr (f (b 0))) 0 * (b.repr (f (b 1))) 1
      - (b.repr (f (b 1))) 0 * (b.repr (f (b 0))) 1 - algebraMap K A c = 0 := by
    have h6 := congrArg (fun x => (b.repr x) 1) hzz
    simpa [map_smul, Finsupp.smul_apply, b.repr_self, smul_eq_mul] using h6
  linear_combination (exp := 1) h5

end

end S_ModularCurve_R2geoDet_coordDet_eq_algebraMap_of_similitude
end P2MW
export P2MW.S_ModularCurve_R2geoDet_coordDet_eq_algebraMap_of_similitude (solution)
