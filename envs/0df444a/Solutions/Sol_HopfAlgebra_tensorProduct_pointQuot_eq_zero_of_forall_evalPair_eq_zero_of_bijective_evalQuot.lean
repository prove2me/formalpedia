-- Prove2me | solution 1 for HopfAlgebra.tensorProduct_pointQuot_eq_zero_of_forall_evalPair_eq_zero_of_bijective_evalQuot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/99795bff-308b-5724-b4d4-039724aaa3c7

import Mathlib
import Definitions.Def_HopfAlgebra_CharacterClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_tensorProduct_pointQuot_eq_zero_of_forall_evalPair_eq_zero_of_bijective_evalQuot

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace DK2CORE

variable {F L : Type*} [Field F] [Field L] [Algebra F L]
  {Q : Type*} [CommRing Q] [Algebra F Q]
  {ι : Type*} [Finite ι] (pt : ι → (Q →ₐ[F] L))

def ev : L ⊗[F] Q →ₐ[L] (ι → L) :=
  Algebra.TensorProduct.lift (Algebra.ofId L (ι → L)) (Pi.algHom F _ fun i : ι => pt i) (fun _ _ => Commute.all _ _)

omit [Finite ι] in
@[scoped simp] theorem ev_tmul (c : L) (q : Q) (i : ι) : ev pt (c ⊗ₜ[F] q) i = c * pt i q := by
  simp [ev, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Pi.algHom_apply, Algebra.algebraMap_eq_smul_one]

private def _root_.DK2CORE.evalPair (i j : ι) : Q ⊗[F] Q →ₐ[F] L :=
  (Algebra.TensorProduct.lmul' F (S := L)).comp (Algebra.TensorProduct.map (pt i) (pt j))

p2m_export "DK2CORE" "evalPair"
omit [Finite ι] in
@[scoped simp] theorem evalPair_tmul (i j : ι) (q q' : Q) : evalPair pt i j (q ⊗ₜ[F] q') = pt i q * pt j q' := by
  simp [evalPair]

theorem eq_zero_of_forall_evalPair_eq_zero (hev : Function.Injective (ev pt))
    (x : Q ⊗[F] Q) (hx : ∀ i j, evalPair pt i j x = 0) : x = 0 := by
  classical
  cases nonempty_fintype ι

  let U : Q →ₗ[F] (ι → L) := LinearMap.pi fun i => (pt i).toLinearMap
  have hU_apply : ∀ (q : Q) (i : ι), U q i = pt i q := fun _ _ => rfl

  have hU : Function.Injective U := by
    intro q q' h
    have h1 : ev pt ((1 : L) ⊗ₜ[F] q) = ev pt ((1 : L) ⊗ₜ[F] q') := by
      funext i
      rw [ev_tmul, ev_tmul, ← hU_apply, ← hU_apply, h]
    have h2 := hev h1
    haveI : Module.Flat F Q := inferInstance
    exact Algebra.TensorProduct.includeRight_injective (algebraMap F L).injective h2

  have key : ∀ (y : Q ⊗[F] Q) (i j : ι),
      ev pt (TensorProduct.piLeft F Q (fun _ : ι => L) (U.rTensor Q y) i) j = evalPair pt i j y := by
    intro y i j
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul q q' =>
        rw [LinearMap.rTensor_tmul, evalPair_tmul]
        have : TensorProduct.piLeft F Q (fun _ : ι => L) (U q ⊗ₜ[F] q') i = U q i ⊗ₜ[F] q' := by
          simp [TensorProduct.piLeft, TensorProduct.piRight, TensorProduct.piRightHom, TensorProduct.piRightHomBil]
        rw [this, hU_apply, ev_tmul]
    | add y z hy hz => simp only [map_add, Pi.add_apply, hy, hz]
  have h1 : ∀ i, ev pt (TensorProduct.piLeft F Q (fun _ : ι => L) (U.rTensor Q x) i) = 0 := by
    intro i; funext j; rw [key, hx]; rfl
  have h2 : ∀ i, TensorProduct.piLeft F Q (fun _ : ι => L) (U.rTensor Q x) i = 0 := fun i =>
    hev (by rw [h1, map_zero])
  have h3 : U.rTensor Q x = 0 := by
    apply (TensorProduct.piLeft F Q (fun _ : ι => L)).injective
    rw [map_zero]
    funext i
    exact h2 i
  haveI : Module.Flat F Q := inferInstance
  exact Module.Flat.rTensor_preserves_injective_linearMap U hU (by rw [h3, map_zero])

end DK2CORE
p2m_reactivate "P2MW.S_HopfAlgebra_tensorProduct_pointQuot_eq_zero_of_forall_evalPair_eq_zero_of_bijective_evalQuot.DK2CORE"

end
p2m_reactivate "P2MW.S_HopfAlgebra_tensorProduct_pointQuot_eq_zero_of_forall_evalPair_eq_zero_of_bijective_evalQuot.DK2CORE"

open scoped TensorProduct

theorem solution
    {F : Type*} [Field F] {A : Type*} [CommRing A] [Bialgebra F A]
    {L : Type*} [Field L] [Algebra F L]
    (S : Submonoid (WithConv (A →ₐ[F] L))) [Finite ↥S]
    (hev : Function.Bijective (HopfAlgebra.evalQuot S))
    (x : HopfAlgebra.pointQuot S ⊗[F] HopfAlgebra.pointQuot S)
    (hx : ∀ (ν ν' : A →ₐ[F] L) (hν : ν ∈ HopfAlgebra.ptSet S) (hν' : ν' ∈ HopfAlgebra.ptSet S),
      HopfAlgebra.evalPair (HopfAlgebra.ptSet S) ν ν' hν hν' x = 0) :
    x = 0 :=
  DK2CORE.eq_zero_of_forall_evalPair_eq_zero
    (fun ν : ↥S => HopfAlgebra.liftPoint (HopfAlgebra.ptSet S) (WithConv.ofConv ν.1) (HopfAlgebra.ofConv_mem_ptSet ν))
    hev.1 x (fun i j => hx _ _ _ _)

end S_HopfAlgebra_tensorProduct_pointQuot_eq_zero_of_forall_evalPair_eq_zero_of_bijective_evalQuot
end P2MW
export P2MW.S_HopfAlgebra_tensorProduct_pointQuot_eq_zero_of_forall_evalPair_eq_zero_of_bijective_evalQuot (solution)
