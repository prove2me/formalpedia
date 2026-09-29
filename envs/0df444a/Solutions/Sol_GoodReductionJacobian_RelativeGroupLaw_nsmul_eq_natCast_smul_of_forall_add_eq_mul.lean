-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.nsmul_eq_natCast_smul_of_forall_add_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/cf30fa7a-a2dd-5b8b-b2e9-26fedd57b36e

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_natCast_smul_of_forall_add_eq_mul

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem solution
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
    (k : Type) [Field k] (sk : B →+* k)
    (W : Type) [AddCommGroup W] [Module k W]
    (τ : W → SchemeHomOver (tangentBase k sk) f)
    (hadd : ∀ v w : W, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w))
    (n : ℕ) (w : W) :
    L.nsmul (tangentBase k sk) n (τ w) = τ ((n : k) • w) ∧
      ((n : k) = 0 → L.nsmul (tangentBase k sk) n (τ w) = L.one (tangentBase k sk)) := by
  letI := L.pointGroup (tangentBase k sk)
  have h0 : τ 0 = L.one (tangentBase k sk) := by
    have h := hadd 0 0
    rw [add_zero] at h

    exact (mul_left_cancel (a := τ 0) (h.symm.trans (mul_one (τ 0)).symm : τ 0 * τ 0 = τ 0 * 1)).symm ▸ rfl
  have main : ∀ m : ℕ, L.nsmul (tangentBase k sk) m (τ w) = τ ((m : k) • w) := by
    intro m
    induction m with
    | zero => rw [RelativeGroupLaw.nsmul_zero, Nat.cast_zero, zero_smul, h0]
    | succ m ih =>
      show L.mul (tangentBase k sk) (L.nsmul (tangentBase k sk) m (τ w)) (τ w) = _
      rw [ih, ← hadd, Nat.cast_succ, add_smul, one_smul]
  refine ⟨main n, fun hn => ?_⟩
  rw [main n, hn, zero_smul, h0]

end S_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_natCast_smul_of_forall_add_eq_mul
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_natCast_smul_of_forall_add_eq_mul (solution)
