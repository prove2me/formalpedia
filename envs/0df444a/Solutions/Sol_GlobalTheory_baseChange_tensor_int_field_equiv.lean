-- Prove2me | solution 1 for GlobalTheory.baseChange_tensor_int_field_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:23:22.588363+00:00
-- url     : https://prove2.me/submissions/75d1af66-04bb-4795-86a1-b4a46bc7efbe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BaseChangeTensorModuleCompat

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
set_option maxHeartbeats 1000000
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K L O : Type) [Field K] [Field L] [Algebra K L] [CommRing O] (M : Type) [AddCommGroup M]
    [Module K M] [Module O M] [SMulCommClass K O M] (N : Type) [AddCommGroup N] [Module L N] [Module O N]
    [SMulCommClass L O N] (e : L ⊗[K] M ≃ₗ[L] N), (∀ (a : O) (m : M), e (1 ⊗ₜ (a • m)) = a • e (1 ⊗ₜ m)) →
    letI : Module (K ⊗[ℤ] O) M := TensorProduct.Algebra.module
    letI : Module (L ⊗[ℤ] O) N := TensorProduct.Algebra.module
    ∃ _ : Algebra (K ⊗[ℤ] O) (L ⊗[ℤ] O), Module.FaithfullyFlat (K ⊗[ℤ] O) (L ⊗[ℤ] O) ∧
      Nonempty ((L ⊗[ℤ] O) ⊗[K ⊗[ℤ] O] M ≃ₗ[L ⊗[ℤ] O] N) := by
  intro R R' O _ _ _ _ M _ _ _ _ N _ _ _ _ e he
  letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module
  letI : Module (R' ⊗[ℤ] O) N := TensorProduct.Algebra.module
  let f : R ⊗[ℤ] O →ₐ[ℤ] R' ⊗[ℤ] O :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℤ R R') (AlgHom.id ℤ O)
  letI : Algebra (R ⊗[ℤ] O) (R' ⊗[ℤ] O) := f.toRingHom.toAlgebra
  letI : Module (R ⊗[ℤ] O) N := Module.compHom N f.toRingHom
  haveI : IsScalarTower (R ⊗[ℤ] O) (R' ⊗[ℤ] O) N := ⟨fun a x n => mul_smul (f a) x n⟩
  have hf : ∀ (r : R) (o : O), f (r ⊗ₜ o) = algebraMap R R' r ⊗ₜ o := fun r o => rfl

  haveI : Module.FaithfullyFlat R R' := inferInstance
  haveI : IsScalarTower R (R ⊗[ℤ] O) (R' ⊗[ℤ] O) := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  let l : R' →ₗ[R] R' ⊗[ℤ] O :=
    { toFun := fun r' => r' ⊗ₜ 1
      map_add' := fun x y => add_tmul x y 1
      map_smul' := fun r r' => rfl }
  let u : (R ⊗[ℤ] O) ⊗[R] R' →ₗ[R ⊗[ℤ] O] R' ⊗[ℤ] O := LinearMap.liftBaseChange _ l
  have hu : ∀ (r : R) (o : O) (r' : R'), u ((r ⊗ₜ o) ⊗ₜ r') = (algebraMap R R' r * r') ⊗ₜ o := by
    intro r o r'
    change f (r ⊗ₜ o) * (r' ⊗ₜ 1) = _
    rw [hf, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
  let w : R' →ₗ[ℤ] O →ₗ[ℤ] (R ⊗[ℤ] O) ⊗[R] R' :=
    LinearMap.mk₂ ℤ (fun r' o => ((1 : R) ⊗ₜ[ℤ] o) ⊗ₜ[R] r')
      (fun x y o => by simp [tmul_add])
      (fun n x o => map_zsmul (TensorProduct.mk R (R ⊗[ℤ] O) R' ((1 : R) ⊗ₜ[ℤ] o)) n x)
      (fun x o o' => by simp [tmul_add, add_tmul])
      (fun n x o => by
        change (TensorProduct.mk R (R ⊗[ℤ] O) R').flip x (TensorProduct.mk ℤ R O 1 (n • o)) =
          n • (TensorProduct.mk R (R ⊗[ℤ] O) R').flip x (TensorProduct.mk ℤ R O 1 o)
        rw [map_zsmul, map_zsmul])
  let v : R' ⊗[ℤ] O →ₗ[ℤ] (R ⊗[ℤ] O) ⊗[R] R' := TensorProduct.lift w
  have hv : ∀ (r' : R') (o : O), v (r' ⊗ₜ o) = ((1 : R) ⊗ₜ[ℤ] o) ⊗ₜ[R] r' := fun r' o => rfl
  have huv : ∀ y, u (v y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r' o =>
      rw [hv, hu, map_one, _root_.one_mul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hvu : ∀ x, v (u x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a r' =>
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul r o =>
        rw [hu, ← Algebra.smul_def, hv, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul,
          _root_.mul_one]
      | add a b ha hb => rw [add_tmul, map_add, map_add, ha, hb]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hubij : Function.Bijective u :=
    ⟨fun a b hab => by rw [← hvu a, ← hvu b, hab], fun y => ⟨v y, huv y⟩⟩
  have hFF : Module.FaithfullyFlat (R ⊗[ℤ] O) (R' ⊗[ℤ] O) :=
    Module.FaithfullyFlat.of_linearEquiv (R ⊗[ℤ] O) ((R ⊗[ℤ] O) ⊗[R] R')
      (LinearEquiv.ofBijective u hubij).symm

  have hj : ∀ (a : R ⊗[ℤ] O) (m : M), e (1 ⊗ₜ (a • m)) = f a • e (1 ⊗ₜ m) := by
    intro a m
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul r o =>
      rw [hf, TensorProduct.Algebra.smul_def, TensorProduct.Algebra.smul_def, ← he,
        TensorProduct.tmul_smul, ← algebraMap_smul R', map_smul]
    | add a b ha hb => rw [add_smul, tmul_add, map_add, ha, hb, map_add, add_smul]
  let j : M →ₗ[R ⊗[ℤ] O] N :=
    { toFun := fun m => e (1 ⊗ₜ m)
      map_add' := fun x y => by simp [tmul_add]
      map_smul' := fun a m => hj a m }
  let Φ : (R' ⊗[ℤ] O) ⊗[R ⊗[ℤ] O] M →ₗ[R' ⊗[ℤ] O] N := LinearMap.liftBaseChange _ j
  let g : R' →+ M →+ (R' ⊗[ℤ] O) ⊗[R ⊗[ℤ] O] M :=
    AddMonoidHom.mk' (fun r' => (TensorProduct.mk (R ⊗[ℤ] O) (R' ⊗[ℤ] O) M
      (r' ⊗ₜ[ℤ] (1 : O))).toAddMonoidHom) (by intro a b; ext m; simp [add_tmul])
  let ψ : R' ⊗[R] M →+ (R' ⊗[ℤ] O) ⊗[R ⊗[ℤ] O] M := TensorProduct.liftAddHom g (by
    intro r r' m
    have hr : r • m = ((r ⊗ₜ[ℤ] (1 : O)) : R ⊗[ℤ] O) • m := by
      rw [TensorProduct.Algebra.smul_def, one_smul]
    simp only [g, AddMonoidHom.mk'_apply, LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply]
    rw [hr, ← TensorProduct.smul_tmul, Algebra.smul_def]
    congr 1
    change _ = f (r ⊗ₜ 1) * _
    simp only [hf, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, Algebra.smul_def])
  have h1 : ∀ y, Φ (ψ y) = e y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r' m =>
      simp only [ψ, TensorProduct.liftAddHom_tmul, g, AddMonoidHom.mk'_apply,
        LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply, Φ, LinearMap.liftBaseChange_tmul]
      change (r' ⊗ₜ[ℤ] (1 : O)) • e (1 ⊗ₜ m) = _
      rw [TensorProduct.Algebra.smul_def, one_smul, ← map_smul, TensorProduct.smul_tmul',
        smul_eq_mul, _root_.mul_one]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  have h2 : ∀ z, ψ (e.symm (Φ z)) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x m =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r' o =>
        have hΦ : Φ ((r' ⊗ₜ[ℤ] o) ⊗ₜ m) = e (r' ⊗ₜ (o • m)) := by
          simp only [Φ, LinearMap.liftBaseChange_tmul]
          change (r' ⊗ₜ[ℤ] o) • e (1 ⊗ₜ m) = _
          rw [TensorProduct.Algebra.smul_def, ← he, ← map_smul, TensorProduct.smul_tmul',
            smul_eq_mul, _root_.mul_one]
        rw [hΦ, LinearEquiv.symm_apply_apply]
        simp only [ψ, TensorProduct.liftAddHom_tmul, g, AddMonoidHom.mk'_apply,
          LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply]
        have ho : o • m = (((1 : R) ⊗ₜ[ℤ] o) : R ⊗[ℤ] O) • m := by
          rw [TensorProduct.Algebra.smul_def, one_smul]
        rw [ho, ← TensorProduct.smul_tmul, Algebra.smul_def]
        congr 1
        change f (1 ⊗ₜ o) * _ = _
        rw [hf, map_one, Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, _root_.mul_one]
      | add x y hx hy => rw [add_tmul, map_add, map_add, map_add, hx, hy]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  have hinj : Function.Injective Φ := fun a b hab => by rw [← h2 a, ← h2 b, hab]
  have hsurj : Function.Surjective Φ := fun n =>
    ⟨ψ (e.symm n), by rw [h1, LinearEquiv.apply_symm_apply]⟩
  exact ⟨f.toRingHom.toAlgebra, hFF, ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩⟩⟩
end GlobalTheory
