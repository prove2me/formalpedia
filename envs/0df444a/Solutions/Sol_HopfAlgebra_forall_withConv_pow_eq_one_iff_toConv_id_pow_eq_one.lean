-- Prove2me | solution 1 for HopfAlgebra.forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/0eb555ec-c941-51f7-b5c2-b0632f31e517

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one

set_option autoImplicit false

universe u v w

namespace HopfAlgebra
namespace UniversalPoint
p2m_open "HopfAlgebra"

variable {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]

theorem lmul'_comp_map_comp {T : Type w} [CommRing T] [Algebra R T]
    (g : H →ₐ[R] T) (a b : H →ₐ[R] H) :
    (Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map (g.comp a) (g.comp b)) =
      g.comp ((Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map a b)) := by
  apply AlgHom.toLinearMap_injective
  apply TensorProduct.ext'
  intro x y
  simp [Algebra.TensorProduct.lmul'_apply_tmul]

theorem toConv_comp_pow {T : Type w} [CommRing T] [Algebra R T]
    (g : H →ₐ[R] T) (u : WithConv (H →ₐ[R] H)) (k : ℕ) :
    (WithConv.toConv (g.comp u.ofConv)) ^ k = WithConv.toConv (g.comp (u ^ k).ofConv) := by
  induction k with
  | zero =>
      rw [pow_zero, pow_zero, AlgHom.convOne_def, AlgHom.convOne_def]
      congr 1
      change (Algebra.ofId R T).comp (Bialgebra.counitAlgHom R H) =
        g.comp ((Algebra.ofId R H).comp (Bialgebra.counitAlgHom R H))
      rw [← AlgHom.comp_assoc]
      congr 1
      exact (AlgHom.ext fun r => (g.commutes r).symm)
  | succ k ih =>
      rw [pow_succ, pow_succ, ih, AlgHom.convMul_def, AlgHom.convMul_def]
      congr 1
      change (Algebra.TensorProduct.lmul' R).comp
          ((Algebra.TensorProduct.map (g.comp (u ^ k).ofConv) (g.comp u.ofConv)).comp
            (Bialgebra.comulAlgHom R H)) =
        g.comp ((Algebra.TensorProduct.lmul' R).comp
          ((Algebra.TensorProduct.map (u ^ k).ofConv u.ofConv).comp (Bialgebra.comulAlgHom R H)))
      rw [← AlgHom.comp_assoc, lmul'_comp_map_comp, AlgHom.comp_assoc, AlgHom.comp_assoc]

end HopfAlgebra.UniversalPoint

open HopfAlgebra.UniversalPoint in
theorem solution
    {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H] (m : ℕ) :
    (∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)), f ^ m = 1) ↔
      (WithConv.toConv (AlgHom.id R H)) ^ m = 1 := by
  constructor
  · intro h
    exact h H (WithConv.toConv (AlgHom.id R H))
  · intro hid T _ _ f
    have hf : f = WithConv.toConv (f.ofConv.comp (WithConv.toConv (AlgHom.id R H)).ofConv) := by
      change f = WithConv.toConv (f.ofConv.comp (AlgHom.id R H))
      rw [AlgHom.comp_id]
    rw [hf, toConv_comp_pow, hid]

    have h0 := toConv_comp_pow f.ofConv (WithConv.toConv (AlgHom.id R H)) 0
    rw [pow_zero, pow_zero] at h0
    exact h0.symm

end S_HopfAlgebra_forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one
end P2MW
export P2MW.S_HopfAlgebra_forall_withConv_pow_eq_one_iff_toConv_id_pow_eq_one (solution)
