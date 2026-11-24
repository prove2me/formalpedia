-- Prove2me | solution 1 for GlobalTheory.DetMod.det_baseChange_of_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:23:44.026878+00:00
-- url     : https://prove2.me/submissions/5f2319e0-ffe1-4cab-89f5-2dc5914e41e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOneReductionOfDetOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.DetMod
namespace GlobalTheory.DetMod
theorem _root_.solution {R S L : Type} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup L] [Module R L]
    {r : ℕ} (x : Fin r → L) (b : Module.Basis (Fin r) S (S ⊗[R] L)) (hb : ∀ j, b j = 1 ⊗ₜ x j)
    (γ : L →ₗ[R] L) (s : R) (a : Matrix (Fin r) (Fin r) R) (ha : ∀ j, s • γ (x j) = ∑ i, a i j • x i) :
    algebraMap R S s ^ r * LinearMap.det (LinearMap.baseChange S γ) = algebraMap R S a.det := by
  have h : LinearMap.toMatrix b b (algebraMap R S s • LinearMap.baseChange S γ) = (algebraMap R S).mapMatrix a := by
    ext i j
    have h1 : (algebraMap R S s • LinearMap.baseChange S γ) (b j) = ∑ i, algebraMap R S (a i j) • b i := by
      rw [LinearMap.smul_apply, hb, LinearMap.baseChange_tmul, algebraMap_smul, ← TensorProduct.tmul_smul, ha,
        TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hb, algebraMap_smul, TensorProduct.tmul_smul]
    rw [LinearMap.toMatrix_apply, h1, b.repr_sum_self]
    rfl
  rw [RingHom.map_det, ← h, map_smul, Matrix.det_smul, LinearMap.det_toMatrix, Fintype.card_fin]
end GlobalTheory.DetMod
