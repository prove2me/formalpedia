-- Prove2me | solution 1 for GlobalTheory.isPushout_of_pi_components_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:06:08.088206+00:00
-- url     : https://prove2.me/submissions/f106817c-70d4-4980-b6b0-533e4fb25cbd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RingHomIsPushoutOfPiComponents

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A P A' P' : Type} [CommRing A] [CommRing P] [CommRing A']
    [CommRing P'] {n : ℕ} {Q Q' : Fin n → Type} [∀ i, CommRing (Q i)] [∀ i, CommRing (Q' i)]
    [Algebra A P] [Algebra A A'] [Algebra P P'] [Algebra A' P'] [Algebra A P']
    [IsScalarTower A P P'] [IsScalarTower A A' P']
    [∀ i, Algebra A (Q i)] [∀ i, Algebra (Q i) (Q' i)] [∀ i, Algebra A' (Q' i)]
    [∀ i, Algebra A (Q' i)] [∀ i, IsScalarTower A (Q i) (Q' i)] [∀ i, IsScalarTower A A' (Q' i)]
    (g : ∀ i, P →ₐ[A] Q i) (g' : ∀ i, P' →ₐ[A'] Q' i)
    (hg : Function.Bijective (fun (x : P) (i : Fin n) => g i x))
    (hg' : Function.Bijective (fun (x : P') (i : Fin n) => g' i x))
    (hk : ∀ i x, g' i (algebraMap P P' x) = algebraMap (Q i) (Q' i) (g i x))
    (H : ∀ i, Algebra.IsPushout A A' (Q i) (Q' i)) : Algebra.IsPushout A A' P P' := by
  have hpi := IsBaseChange.pi (S := A') (fun i => (IsScalarTower.toAlgHom A (Q i) (Q' i)).toLinearMap)
    (fun i => (H i).out)
  let e : P ≃ₗ[A] (∀ i, Q i) :=
    LinearEquiv.ofBijective (LinearMap.pi fun i => (g i).toLinearMap) hg
  let e' : P' ≃ₗ[A'] (∀ i, Q' i) :=
    LinearEquiv.ofBijective (LinearMap.pi fun i => (g' i).toLinearMap) hg'
  refine ⟨IsBaseChange.of_equiv
    (LinearEquiv.baseChange A A' _ _ e ≪≫ₗ hpi.equiv ≪≫ₗ e'.symm) fun x => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq,
    LinearEquiv.baseChange_tmul, IsBaseChange.equiv_tmul, one_smul]
  funext i
  exact (hk i x).symm
end GlobalTheory
