-- Prove2me | solution 1 for MazurTransfer.PolynomialPowerSubstitutionPresentation.backward_forward
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T06:04:43.317542+00:00
-- url     : https://prove2.me/submissions/11e464ab-17a6-41a1-8405-4a416194a74c

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the two literal maps for Y^n-T are inverse on the root algebra.
Named downstream consumer: the original power-substitution algebra isomorphism and basis used to raise actual FiniteMapData degrees. -/
import Mathlib
import Definitions.Def_MazurTransfer_PolynomialPowerSubstitutionMaps
noncomputable section
universe u
open Polynomial
open MazurTransfer.PolynomialPowerSubstitutionPresentation
namespace PowerSubstitutionInversePublicProof20261017
variable (R : Type u) [CommRing R] (n : ℕ)
theorem root_power : AdjoinRoot.root (relation R n)^n =
    AdjoinRoot.of (relation R n) (sourceX R n) := by
  have h := AdjoinRoot.eval₂_root (relation R n)
  change eval₂ (AdjoinRoot.of (relation R n)) (AdjoinRoot.root (relation R n))
    (X^n - C (sourceX R n)) = 0 at h
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  exact sub_eq_zero.mp h

theorem backward_powerMap : (backward R n).comp (powerMap R n) =
    AdjoinRoot.of (relation R n) := by
  apply Polynomial.ringHom_ext
  · intro r
    change backward R n (aeval ((X : Polynomial R)^n) (C r)) =
      AdjoinRoot.of (relation R n) (C r)
    rw [aeval_C]
    change eval₂ _ _ (C r) = _
    rw [eval₂_C]
    rfl
  · change backward R n (aeval ((X : Polynomial R)^n) X) = AdjoinRoot.of (relation R n) X
    rw [aeval_X, map_pow]
    simpa only [backward, coe_eval₂RingHom, eval₂_X, sourceX] using root_power R n

end PowerSubstitutionInversePublicProof20261017
open PowerSubstitutionInversePublicProof20261017
theorem solution (R : Type u) [CommRing R] (n : ℕ) : (backward R n).comp (forward R n) = RingHom.id _ := by
  have h : ((backward R n).comp (forward R n)).comp (AdjoinRoot.mk (relation R n)) =
      AdjoinRoot.mk (relation R n) := by
    apply Polynomial.ringHom_ext
    · intro p
      change backward R n (forward R n (AdjoinRoot.of (relation R n) p)) =
        AdjoinRoot.of (relation R n) p
      simpa only [forward, AdjoinRoot.lift_of, RingHom.comp_apply] using
        RingHom.congr_fun (backward_powerMap R n) p
    · simp [forward, backward, AdjoinRoot.mk_X]
  apply RingHom.ext
  intro x
  induction x using AdjoinRoot.induction_on with
  | ih p => exact RingHom.congr_fun h p
#print axioms solution
