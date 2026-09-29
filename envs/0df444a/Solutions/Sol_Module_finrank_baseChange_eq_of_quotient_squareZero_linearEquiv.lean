-- Prove2me | solution 1 for Module.finrank_baseChange_eq_of_quotient_squareZero_linearEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/8724b36d-95d9-5dec-8040-bc81b13f2b69

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_finrank_baseChange_eq_of_quotient_squareZero_linearEquiv

universe u

open TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 8000000

theorem solution
    {R : Type u} [CommRing R] (J : Ideal R) (hJ : J ^ 2 = ⊥)
    {S : Type u} [CommRing S] (φ : R ⧸ J ≃+* S)
    (P : Type u) [AddCommGroup P] [Module S P]
    (P' : Type u) [AddCommGroup P'] [Module R P'] {n : ℕ}
    (hrk : ∀ (K : Type u) [Field K] [Algebra S K], Module.finrank K (K ⊗[S] P) = n) :
    letI : Module (R ⧸ J) P := Module.compHom P φ.toRingHom
    ((R ⧸ J) ⊗[R] P' ≃ₗ[R ⧸ J] P) →
    ∀ (K : Type u) [Field K] [Algebra R K], Module.finrank K (K ⊗[R] P') = n := by
  letI : Module (R ⧸ J) P := Module.compHom P φ.toRingHom
  intro iso K _ _
  have hJK : ∀ x ∈ J, (algebraMap R K) x = 0 := fun x hx => by
    have h2 : (algebraMap R K x) ^ 2 = 0 := by
      rw [← map_pow]
      have : x ^ 2 = 0 := by
        have h := Ideal.pow_mem_pow hx 2; rw [hJ] at h; exact Ideal.mem_bot.mp h
      rw [this, map_zero]
    exact (pow_eq_zero_iff two_ne_zero).mp h2
  letI : Algebra (R ⧸ J) K := (Ideal.Quotient.lift J (algebraMap R K) hJK).toAlgebra
  haveI : IsScalarTower R (R ⧸ J) K := IsScalarTower.of_algebraMap_eq'
    (RingHom.ext fun a => (Ideal.Quotient.lift_mk J (algebraMap R K) hJK).symm)

  have e1 : K ⊗[R] P' ≃ₗ[K] K ⊗[R ⧸ J] P :=
    (AlgebraTensorModule.cancelBaseChange R (R ⧸ J) K K P').symm.trans
      (LinearEquiv.baseChange (R ⧸ J) K ((R ⧸ J) ⊗[R] P') P iso)
  rw [e1.finrank_eq]

  letI : Algebra S K := ((algebraMap (R ⧸ J) K).comp φ.symm.toRingHom).toAlgebra
  have keyeq : ∀ r : R ⧸ J, (algebraMap S K (φ r) : K) = algebraMap (R ⧸ J) K r := fun r => by
    show algebraMap (R ⧸ J) K (φ.symm (φ r)) = _; rw [φ.symm_apply_apply]

  let fwdAH : K ⊗[R ⧸ J] P →+ K ⊗[S] P := TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun k => AddMonoidHom.mk' (fun p => k ⊗ₜ[S] p)
        (fun _ _ => tmul_add k _ _))
      (fun _ _ => AddMonoidHom.ext fun _ => add_tmul _ _ _))
    (fun r k p => by

      show (algebraMap (R ⧸ J) K r * k) ⊗ₜ[S] p = k ⊗ₜ[S] ((φ r : S) • p)
      rw [← keyeq r]
      rw [show algebraMap S K (φ r) * k = (φ r : S) • k from (Algebra.smul_def (φ r) k).symm]
      exact smul_tmul (φ r) k p)
  let bwdAH : K ⊗[S] P →+ K ⊗[R ⧸ J] P := TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun k => AddMonoidHom.mk' (fun p => k ⊗ₜ[R ⧸ J] p)
        (fun _ _ => tmul_add k _ _))
      (fun _ _ => AddMonoidHom.ext fun _ => add_tmul _ _ _))
    (fun s k p => by

      show (algebraMap S K s * k) ⊗ₜ[R ⧸ J] p = k ⊗ₜ[R ⧸ J] (s • p)
      have hk : algebraMap S K s * k = (φ.symm s : R ⧸ J) • k := by
        rw [Algebra.smul_def]; rfl
      have hp : (s • p : P) = (φ.symm s : R ⧸ J) • p := by
        show s • p = (φ (φ.symm s) : S) • p; rw [φ.apply_symm_apply]
      rw [hk, hp]; exact smul_tmul (φ.symm s) k p)

  let e2AE : K ⊗[R ⧸ J] P ≃+ K ⊗[S] P :=
    { toFun := fwdAH
      invFun := bwdAH
      left_inv := fun x => by
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul k p => simp [fwdAH, bwdAH, liftAddHom_tmul]
        | add x y hx hy => simp only [map_add, hx, hy]
      right_inv := fun x => by
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul k p => simp [fwdAH, bwdAH, liftAddHom_tmul]
        | add x y hx hy => simp only [map_add, hx, hy]
      map_add' := map_add fwdAH }

  have e2 : K ⊗[R ⧸ J] P ≃ₗ[K] K ⊗[S] P := by
    refine AddEquiv.toLinearEquiv e2AE ?_
    intro c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul k p =>
        simp only [e2AE, fwdAH, AddEquiv.coe_mk, Equiv.coe_fn_mk, smul_tmul', liftAddHom_tmul,
          AddMonoidHom.mk'_apply]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  rw [e2.finrank_eq]
  exact hrk K

end S_Module_finrank_baseChange_eq_of_quotient_squareZero_linearEquiv
end P2MW
export P2MW.S_Module_finrank_baseChange_eq_of_quotient_squareZero_linearEquiv (solution)
