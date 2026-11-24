-- Prove2me | solution 1 for GlobalTheory.FiniteFlatKilled.point_pow_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:28:26.805234+00:00
-- url     : https://prove2.me/submissions/753895ef-1483-4af4-b46d-d0e278ae8484

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsIdPowEqOneOfIsFiniteOfFlat
import Theorems.Thm_GlobalTheory_FiniteFlatKilled_postcomp_apply
import Theorems.Thm_GlobalTheory_FiniteFlatKilled_pow_card_eq_one
import Theorems.Thm_GlobalTheory_FiniteFlatKilled_mul_comp_antipode
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FiniteFlatKilled.postcomp_apply

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FiniteFlatKilled
open TensorProduct WithConv Coalgebra
variable {R B C F : Type*} [CommRing R] [CommRing C] [CommRing F] [Algebra R C] [Algebra R F]
variable [CommRing B] [HopfAlgebra R B]
variable [IsCocomm R B]
namespace GlobalTheory.FiniteFlatKilled
theorem _root_.solution {ι : Type*} [Fintype ι] (b : Module.Basis ι C (C ⊗[R] B))
    (u : B →ₐ[R] C) : toConv u ^ Fintype.card ι = 1 := by
  let x : WithConv (B →ₐ[R] C ⊗[R] B) := toConv Algebra.TensorProduct.includeRight
  let T : (B →ₐ[R] C) → (C ⊗[R] B →ₐ[C] C ⊗[R] B) := fun v =>
    Algebra.TensorProduct.lift (Algebra.ofId C _)
      (x * toConv ((IsScalarTower.toAlgHom R C (C ⊗[R] B)).comp v)).ofConv
      fun _ _ => Commute.all _ _
  have hTx : ∀ v, ((T v).restrictScalars R).comp x.ofConv =
      (x * toConv ((IsScalarTower.toAlgHom R C (C ⊗[R] B)).comp v)).ofConv := fun v => by
    ext c
    simp [T, x]
  have hTy : ∀ v w : B →ₐ[R] C, ((T v).restrictScalars R).comp
      ((IsScalarTower.toAlgHom R C (C ⊗[R] B)).comp w) =
      (IsScalarTower.toAlgHom R C (C ⊗[R] B)).comp w := fun v w => by
    ext c
    exact (T v).commutes (w c)
  have hTT : ∀ v w : B →ₐ[R] C, toConv v * toConv w = 1 → (T v).comp (T w) = AlgHom.id _ _ := by
    intro v w hvw
    refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_
    change ((T v).restrictScalars R).comp (((T w).restrictScalars R).comp x.ofConv) = x.ofConv
    have h3 := AlgHom.comp_convMul_distrib (IsScalarTower.toAlgHom R C (C ⊗[R] B))
      (toConv v) (toConv w)
    have h4 : (IsScalarTower.toAlgHom R C (C ⊗[R] B)).comp
        (1 : WithConv (B →ₐ[R] C)).ofConv = (1 : WithConv (B →ₐ[R] C ⊗[R] B)).ofConv := by
      ext c
      simp
    rw [hvw, h4] at h3
    rw [hTx, AlgHom.comp_convMul_distrib, hTx, ofConv_toConv, hTy, toConv_ofConv, mul_assoc,
      ← ofConv_injective h3, mul_one]
  let τ : C ⊗[R] B ≃ₐ[C] C ⊗[R] B :=
    AlgEquiv.ofAlgHom (T u) (T (u.comp (HopfAlgebra.antipodeAlgHom R B)))
      (hTT _ _ (mul_comp_antipode u)) (hTT _ _ (by rw [mul_comm]; exact mul_comp_antipode u))
  have hx : IsUnit (toConv x.ofConv.toLinearMap) := by
    refine IsUnit.of_mul_eq_one
      (toConv (x.ofConv.comp (HopfAlgebra.antipodeAlgHom R B)).toLinearMap) ?_
    exact congrArg (fun f : WithConv (B →ₐ[R] C ⊗[R] B) => toConv f.ofConv.toLinearMap)
      (mul_comp_antipode x.ofConv)
  have key := pow_card_eq_one b τ _ hx (toConv u.toLinearMap)
    (congrArg (fun f : B →ₐ[R] C ⊗[R] B => toConv f.toLinearMap) (hTx u))
  apply ofConv_injective
  apply AlgHom.toLinearMap_injective
  apply toConv_injective
  rw [AlgHom.toLinearMap_convPow, AlgHom.toLinearMap_convOne]
  exact key
end GlobalTheory.FiniteFlatKilled
