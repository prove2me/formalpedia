-- Prove2me | solution 1 for HopfAlgebra.toConv_id_pow_eq_one_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/3f0f06b8-c312-568f-b29a-84eefd0417a1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_toConv_id_pow_eq_one_baseChange

set_option autoImplicit false

universe u v w

namespace HopfAlgebra
namespace UniversalPointBC
p2m_open "HopfAlgebra"

open scoped TensorProduct

variable {R : Type u} [CommRing R] (R' : Type w) [CommRing R'] [Algebra R R']
variable {H : Type v} [CommRing H] [HopfAlgebra R H]

noncomputable abbrev bc (u : H →ₐ[R] H) : R' ⊗[R] H →ₐ[R'] R' ⊗[R] H :=
  Algebra.TensorProduct.map (AlgHom.id R' R') u

theorem convMul_bc_tmul (u v : WithConv (H →ₐ[R] H)) (s : R') (h : H) :
    (WithConv.toConv (bc R' u.ofConv) * WithConv.toConv (bc R' v.ofConv)).ofConv (s ⊗ₜ[R] h) =
      s ⊗ₜ[R] (u * v).ofConv h := by
  classical
  rw [AlgHom.convMul_apply, AlgHom.convMul_apply, TensorProduct.comul_tmul]
  let ρ := Coalgebra.Repr.arbitrary R h
  rw [← ρ.eq]
  change (Algebra.TensorProduct.lift (bc R' u.ofConv) (bc R' v.ofConv) _)
      ((TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R' R R' R' R' H H)
        ((1 ⊗ₜ[R'] s) ⊗ₜ[R] ∑ i ∈ ρ.index, ρ.left i ⊗ₜ[R] ρ.right i)) =
    s ⊗ₜ[R] (Algebra.TensorProduct.lift u.ofConv v.ofConv _) (∑ i ∈ ρ.index, ρ.left i ⊗ₜ[R] ρ.right i)
  rw [TensorProduct.tmul_sum, map_sum, map_sum, map_sum, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, Algebra.TensorProduct.lift_tmul,
    Algebra.TensorProduct.lift_tmul]
  simp [bc, Algebra.TensorProduct.tmul_mul_tmul]

theorem convMul_bc (u v : WithConv (H →ₐ[R] H)) :
    WithConv.toConv (bc R' u.ofConv) * WithConv.toConv (bc R' v.ofConv) =
      WithConv.toConv (bc R' (u * v).ofConv) := by
  apply WithConv.ext
  apply AlgHom.toLinearMap_injective
  apply TensorProduct.AlgebraTensorModule.ext
  intro s h
  change (WithConv.toConv (bc R' u.ofConv) * WithConv.toConv (bc R' v.ofConv)).ofConv (s ⊗ₜ[R] h) =
    (bc R' (u * v).ofConv) (s ⊗ₜ[R] h)
  rw [convMul_bc_tmul]
  simp [bc]

theorem convOne_bc :
    (1 : WithConv (R' ⊗[R] H →ₐ[R'] R' ⊗[R] H)) =
      WithConv.toConv (bc R' (1 : WithConv (H →ₐ[R] H)).ofConv) := by
  apply WithConv.ext
  apply AlgHom.toLinearMap_injective
  apply TensorProduct.AlgebraTensorModule.ext
  intro s h
  rw [AlgHom.convOne_def, AlgHom.convOne_def]
  change algebraMap R' (R' ⊗[R] H) (Coalgebra.counit (s ⊗ₜ[R] h)) =
    s ⊗ₜ[R] algebraMap R H (Coalgebra.counit h)
  rw [TensorProduct.counit_tmul]
  change algebraMap R' (R' ⊗[R] H) (Coalgebra.counit (R := R) h • s) = _
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

theorem pow_bc (u : WithConv (H →ₐ[R] H)) (k : ℕ) :
    (WithConv.toConv (bc R' u.ofConv)) ^ k = WithConv.toConv (bc R' (u ^ k).ofConv) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, convOne_bc]
  | succ k ih => rw [pow_succ, pow_succ, ih, convMul_bc]

end HopfAlgebra.UniversalPointBC

open scoped TensorProduct in
open HopfAlgebra.UniversalPointBC in
theorem solution
    {R : Type u} [CommRing R] (R' : Type w) [CommRing R'] [Algebra R R']
    {H : Type v} [CommRing H] [HopfAlgebra R H] (m : ℕ)
    (h : (WithConv.toConv (AlgHom.id R H)) ^ m = 1) :
    (WithConv.toConv (AlgHom.id R' (TensorProduct R R' H))) ^ m = 1 := by
  have hid : AlgHom.id R' (R' ⊗[R] H) = bc R' (WithConv.toConv (AlgHom.id R H)).ofConv := by
    change AlgHom.id R' (R' ⊗[R] H) = Algebra.TensorProduct.map (AlgHom.id R' R') (AlgHom.id R H)
    exact Algebra.TensorProduct.map_id.symm
  rw [hid]
  change (WithConv.toConv (bc R' (WithConv.toConv (AlgHom.id R H)).ofConv)) ^ m = 1
  rw [pow_bc, h, ← convOne_bc]

end S_HopfAlgebra_toConv_id_pow_eq_one_baseChange
end P2MW
export P2MW.S_HopfAlgebra_toConv_id_pow_eq_one_baseChange (solution)
