-- Prove2me | solution 1 for HopfAlgebra.exists_withConv_tensorProduct_equiv_prod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/70815ae4-77d7-556e-bd0e-448e2fce8d02

import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_withConv_tensorProduct_equiv_prod

open scoped TensorProduct
open WithConv

namespace SolB5

section points

variable {R L G H : Type} [CommRing R] [CommRing L] [Algebra R L]
  [CommRing G] [CommRing H] [Bialgebra R G] [Bialgebra R H]

private theorem convMul_apply_tmul_one (F₁ F₂ : WithConv ((G ⊗[R] H) →ₐ[R] L)) (x : G) :
    (F₁ * F₂) (x ⊗ₜ[R] (1 : H)) =
      (toConv (F₁.ofConv.comp (Algebra.TensorProduct.includeLeft : G →ₐ[R] G ⊗[R] H)) *
        toConv (F₂.ofConv.comp (Algebra.TensorProduct.includeLeft : G →ₐ[R] G ⊗[R] H))) x := by
  rw [AlgHom.convMul_apply, AlgHom.convMul_apply, TensorProduct.comul_tmul, Bialgebra.comul_one,
    Algebra.TensorProduct.one_def]
  generalize Coalgebra.comul (R := R) x = c
  induction c using TensorProduct.induction_on with
  | zero => rw [TensorProduct.zero_tmul, LinearEquiv.map_zero, map_zero, map_zero]
  | tmul x₁ x₂ =>
    rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
      Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
    rfl
  | add a b ha hb => rw [TensorProduct.add_tmul, LinearEquiv.map_add, map_add, map_add, ha, hb]

private theorem convMul_apply_one_tmul (F₁ F₂ : WithConv ((G ⊗[R] H) →ₐ[R] L)) (y : H) :
    (F₁ * F₂) ((1 : G) ⊗ₜ[R] y) =
      (toConv (F₁.ofConv.comp (Algebra.TensorProduct.includeRight : H →ₐ[R] G ⊗[R] H)) *
        toConv (F₂.ofConv.comp (Algebra.TensorProduct.includeRight : H →ₐ[R] G ⊗[R] H))) y := by
  rw [AlgHom.convMul_apply, AlgHom.convMul_apply, TensorProduct.comul_tmul, Bialgebra.comul_one,
    Algebra.TensorProduct.one_def]
  generalize Coalgebra.comul (R := R) y = c
  induction c using TensorProduct.induction_on with
  | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, map_zero, map_zero]
  | tmul y₁ y₂ =>
    rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
      Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
    rfl
  | add a b ha hb => rw [TensorProduct.tmul_add, LinearEquiv.map_add, map_add, map_add, ha, hb]

private noncomputable def tensorPointsEquiv :
    WithConv ((G ⊗[R] H) →ₐ[R] L) ≃ WithConv (G →ₐ[R] L) × WithConv (H →ₐ[R] L) where
  toFun F := (toConv (F.ofConv.comp Algebra.TensorProduct.includeLeft),
    toConv (F.ofConv.comp Algebra.TensorProduct.includeRight))
  invFun fg := toConv (Algebra.TensorProduct.lift fg.1.ofConv fg.2.ofConv fun _ _ => .all _ _)
  left_inv F := by
    apply WithConv.ext
    ext <;> simp
  right_inv fg := by
    ext <;> simp

private theorem tensorPointsEquiv_fst (F : WithConv ((G ⊗[R] H) →ₐ[R] L)) (x : G) :
    (tensorPointsEquiv F).1 x = F (x ⊗ₜ[R] (1 : H)) := rfl

private theorem tensorPointsEquiv_snd (F : WithConv ((G ⊗[R] H) →ₐ[R] L)) (y : H) :
    (tensorPointsEquiv F).2 y = F ((1 : G) ⊗ₜ[R] y) := rfl

private theorem tensorPointsEquiv_mul (F₁ F₂ : WithConv ((G ⊗[R] H) →ₐ[R] L)) :
    tensorPointsEquiv (F₁ * F₂) = tensorPointsEquiv F₁ * tensorPointsEquiv F₂ := by
  refine Prod.ext (WithConv.ext (AlgHom.ext fun x => ?_)) (WithConv.ext (AlgHom.ext fun y => ?_))
  · exact convMul_apply_tmul_one F₁ F₂ x
  · exact convMul_apply_one_tmul F₁ F₂ y

end points

end SolB5

theorem solution
    {R : Type} [CommRing R] {Γ : Type} [Group Γ]
    (H₁ H₂ : Type) [CommRing H₁] [CommRing H₂] [HopfAlgebra R H₁] [HopfAlgebra R H₂]
    {L : Type} [CommRing L] [Algebra R L] [MulSemiringAction Γ L] [SMulCommClass Γ R L] :
    ∃ e : WithConv ((H₁ ⊗[R] H₂) →ₐ[R] L) ≃ WithConv (H₁ →ₐ[R] L) × WithConv (H₂ →ₐ[R] L),
      (∀ f g, e (f * g) = e f * e g) ∧
      ∀ (σ : Γ) (f g : WithConv ((H₁ ⊗[R] H₂) →ₐ[R] L)),
        (∀ x : H₁ ⊗[R] H₂, g x = σ • (f x)) →
          (∀ y : H₁, (e g).1 y = σ • ((e f).1 y)) ∧ (∀ z : H₂, (e g).2 z = σ • ((e f).2 z)) := by
  refine ⟨SolB5.tensorPointsEquiv, SolB5.tensorPointsEquiv_mul, fun σ f g hfg => ⟨fun y => ?_, fun z => ?_⟩⟩
  · rw [SolB5.tensorPointsEquiv_fst, SolB5.tensorPointsEquiv_fst]
    exact hfg (y ⊗ₜ[R] (1 : H₂))
  · rw [SolB5.tensorPointsEquiv_snd, SolB5.tensorPointsEquiv_snd]
    exact hfg ((1 : H₁) ⊗ₜ[R] z)

#print axioms solution

end S_HopfAlgebra_exists_withConv_tensorProduct_equiv_prod
end P2MW
export P2MW.S_HopfAlgebra_exists_withConv_tensorProduct_equiv_prod (solution)
