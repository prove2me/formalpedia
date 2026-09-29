-- Prove2me | solution 1 for HopfOrder.exists_equiv_algHom_apply_eq_and_toConv_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/eb07a8e0-b446-537a-b3ad-87b459fb4f4b

import Mathlib
import Definitions.Def_HopfAlgebra_HopfOrderData
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfOrder_exists_equiv_algHom_apply_eq_and_toConv_mul
set_option autoImplicit false

open scoped TensorProduct

namespace HopfOrder
p2m_export "HopfOrder" "tensorSqHom tensorSqHom_tmul baseChangeEquiv baseChangeEquiv_tmul counitS algebraMap_counitS comulS tensorSqHom_comulS moduleFlat_of_finite hopfAlgebraOfFinite"
p2m_open "HopfOrder"
namespace Points

set_option linter.unusedSectionVars false

open WithConv

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
  (S : Subalgebra R A) [Module.Finite R ↥S]
  {L : Type*} [CommRing L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  (P : Subalgebra R L) (hP : ∀ x : L, IsIntegral R x → x ∈ P)

noncomputable def res (f : A →ₐ[K] L) : ↥S →ₐ[R] ↥P :=
  ((f.restrictScalars R).comp S.val).codRestrict P
    (fun x => hP _ ((Algebra.IsIntegral.isIntegral (R := R) x).map ((f.restrictScalars R).comp S.val)))

@[scoped simp] theorem coe_res_apply (f : A →ₐ[K] L) (x : ↥S) : ((res S P hP f x : ↥P) : L) = f (x : A) := rfl

private noncomputable def _root_.HopfOrder.Points.ext (hspan : Submodule.span K (S : Set A) = ⊤) (g : ↥S →ₐ[R] ↥P) : A →ₐ[K] L :=
  haveI := moduleFlat_of_finite (K := K) S
  (AlgHom.liftEquiv R K ↥S L (P.val.comp g)).comp
    ((baseChangeEquiv S hspan).symm : A →ₐ[K] K ⊗[R] ↥S)

p2m_export "HopfOrder.Points" "ext"
theorem ext_baseChangeEquiv_tmul (hspan : Submodule.span K (S : Set A) = ⊤) (g : ↥S →ₐ[R] ↥P)
    (k : K) (s : ↥S) :
    haveI := moduleFlat_of_finite (K := K) S
    ext S P hspan g (baseChangeEquiv S hspan (k ⊗ₜ[R] s)) = k • ((g s : ↥P) : L) := by
  haveI := moduleFlat_of_finite (K := K) S
  simp only [ext, AlgHom.comp_apply, AlgEquiv.coe_algHom, AlgEquiv.symm_apply_apply,
    AlgHom.liftEquiv_tmul, Subalgebra.coe_val]

theorem ext_coe (hspan : Submodule.span K (S : Set A) = ⊤) (g : ↥S →ₐ[R] ↥P) (s : ↥S) :
    ext S P hspan g (s : A) = ((g s : ↥P) : L) := by
  haveI := moduleFlat_of_finite (K := K) S
  have h := ext_baseChangeEquiv_tmul S P hspan g 1 s
  rwa [baseChangeEquiv_tmul, one_smul, one_smul] at h

theorem res_ext (hspan : Submodule.span K (S : Set A) = ⊤) (g : ↥S →ₐ[R] ↥P) :
    res S P hP (ext S P hspan g) = g := by
  apply AlgHom.ext
  intro s
  apply Subtype.ext
  rw [coe_res_apply, ext_coe]

theorem ext_res (hspan : Submodule.span K (S : Set A) = ⊤) (f : A →ₐ[K] L) :
    ext S P hspan (res S P hP f) = f := by
  haveI := moduleFlat_of_finite (K := K) S
  apply AlgHom.ext
  intro a
  obtain ⟨z, rfl⟩ := (baseChangeEquiv S hspan).surjective a
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul k s =>
    rw [ext_baseChangeEquiv_tmul, coe_res_apply, baseChangeEquiv_tmul, map_smul]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

noncomputable def equiv (hspan : Submodule.span K (S : Set A) = ⊤) : (A →ₐ[K] L) ≃ (↥S →ₐ[R] ↥P) where
  toFun := res S P hP
  invFun := ext S P hspan
  left_inv := ext_res S P hP hspan
  right_inv := res_ext S P hP hspan

theorem val_lift_res_res (f g : A →ₐ[K] L) (z : ↥S ⊗[R] ↥S) :
    ((Algebra.TensorProduct.lift (res S P hP f) (res S P hP g) (fun _ _ => Commute.all _ _) z : ↥P) : L)
      = Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) (tensorSqHom S z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s t =>
    rw [Algebra.TensorProduct.lift_tmul, tensorSqHom_tmul, Algebra.TensorProduct.lift_tmul,
      Subalgebra.coe_mul, coe_res_apply, coe_res_apply]
  | add x y hx hy => rw [map_add, map_add, Subalgebra.coe_add, map_add, hx, hy]

variable (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)

theorem res_mul (f g : A →ₐ[K] L) :
    letI := HopfOrder.hopfAlgebraOfFinite S hcomul hcounit hanti
    toConv (res S P hP (ofConv (toConv f * toConv g))) = toConv (res S P hP f) * toConv (res S P hP g) := by
  haveI := moduleFlat_of_finite (K := K) S
  letI := HopfOrder.hopfAlgebraOfFinite S hcomul hcounit hanti
  apply WithConv.ext
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  change ((toConv f * toConv g) : WithConv (A →ₐ[K] L)) (x : A)
    = (((toConv (res S P hP f) * toConv (res S P hP g) : WithConv (↥S →ₐ[R] ↥P)) x : ↥P) : L)
  rw [AlgHom.convMul_apply, AlgHom.convMul_apply]
  change _ = ((Algebra.TensorProduct.lift (res S P hP f) (res S P hP g) _ (comulS hcomul x) : ↥P) : L)
  rw [val_lift_res_res, tensorSqHom_comulS]

theorem res_one :
    letI := HopfOrder.hopfAlgebraOfFinite S hcomul hcounit hanti
    toConv (res S P hP (ofConv (1 : WithConv (A →ₐ[K] L)))) = 1 := by
  haveI := moduleFlat_of_finite (K := K) S
  letI := HopfOrder.hopfAlgebraOfFinite S hcomul hcounit hanti
  apply WithConv.ext
  apply AlgHom.ext
  intro x
  apply Subtype.ext
  change ((1 : WithConv (A →ₐ[K] L))) (x : A) = (((1 : WithConv (↥S →ₐ[R] ↥P)) x : ↥P) : L)
  rw [AlgHom.convOne_apply, AlgHom.convOne_apply]
  change _ = ((algebraMap R ↥P (counitS hcounit x) : ↥P) : L)
  rw [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply R K L, algebraMap_counitS]

end Points
p2m_reactivate "P2MW.S_HopfOrder_exists_equiv_algHom_apply_eq_and_toConv_mul.HopfOrder.Points"
end HopfOrder
p2m_reactivate "P2MW.S_HopfOrder_exists_equiv_algHom_apply_eq_and_toConv_mul.HopfOrder.Points P2MW.S_HopfOrder_exists_equiv_algHom_apply_eq_and_toConv_mul.HopfOrder"

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    (S : Subalgebra R A) [Module.Finite R ↥S]
    (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    {L : Type*} [CommRing L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    (P : Subalgebra R L) (hP : ∀ x : L, IsIntegral R x → x ∈ P) :
    letI := HopfOrder.hopfAlgebraOfFinite S hcomul hcounit hanti
    ∃ e : (A →ₐ[K] L) ≃ (↥S →ₐ[R] ↥P),
      (∀ (f : A →ₐ[K] L) (x : ↥S), ((e f x : ↥P) : L) = f (x : A)) ∧
      (∀ f g : A →ₐ[K] L,
          WithConv.toConv (e (WithConv.ofConv (WithConv.toConv f * WithConv.toConv g)))
            = WithConv.toConv (e f) * WithConv.toConv (e g)) ∧
      WithConv.toConv (e (WithConv.ofConv (1 : WithConv (A →ₐ[K] L)))) = 1 :=
  ⟨HopfOrder.Points.equiv S P hP hspan, fun _ _ => rfl,
    HopfOrder.Points.res_mul S P hP hcomul hanti hcounit, HopfOrder.Points.res_one S P hP hcomul hanti hcounit⟩

end S_HopfOrder_exists_equiv_algHom_apply_eq_and_toConv_mul
end P2MW
export P2MW.S_HopfOrder_exists_equiv_algHom_apply_eq_and_toConv_mul (solution)
