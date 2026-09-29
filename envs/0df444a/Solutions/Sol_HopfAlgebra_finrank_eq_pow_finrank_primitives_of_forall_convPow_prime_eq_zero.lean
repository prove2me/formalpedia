-- Prove2me | solution 1 for HopfAlgebra.finrank_eq_pow_finrank_primitives_of_forall_convPow_prime_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/7de6dd1c-df9a-5839-b581-9b6b2edbcbe6

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_ModpRealization
import Theorems.Thm_HopfAlgebra_finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_finrank_eq_pow_finrank_primitives_of_forall_convPow_prime_eq_zero

set_option autoImplicit false

open scoped TensorProduct

noncomputable section

universe u v

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero"
namespace PrimitivesDual
p2m_open "HopfAlgebra"

variable {k : Type u} [Field k] {A : Type v} [CommRing A] [Bialgebra k A]
variable [Module.Finite k A] [Coalgebra.IsCocomm k A]

local notation "D" => CartierDual k A

abbrev augIdeal (k : Type u) [Field k] (A : Type v) [CommRing A] [Bialgebra k A]
    [Module.Finite k A] [Coalgebra.IsCocomm k A] : Ideal (CartierDual k A) :=
  RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k A))

local notation "J" => augIdeal k A

theorem mem_augIdeal_iff (φ : D) : φ ∈ J ↔ φ 1 = 0 := by
  rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply]
  show CartierDual.dualCounit k A (CartierDual.toDual k A φ) = 0 ↔ _
  rw [CartierDual.dualCounit_apply]
  rfl

def IsPrim (k : Type u) [Field k] {A : Type v} [CommRing A] [Bialgebra k A] (x : A) : Prop :=
  Coalgebra.comul (R := k) x = x ⊗ₜ[k] 1 + 1 ⊗ₜ[k] x

def prim (k : Type u) [Field k] (A : Type v) [CommRing A] [Bialgebra k A] : Submodule k A :=
  LinearMap.ker (Coalgebra.comul (R := k) (A := A)
    - (TensorProduct.mk k A A).flip 1 - TensorProduct.mk k A A 1)

omit [Module.Finite k A] [Coalgebra.IsCocomm k A] in
theorem mem_prim_iff (x : A) : x ∈ prim k A ↔ IsPrim k x := by
  unfold prim IsPrim
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sub_apply, sub_sub, sub_eq_zero]
  rfl

omit [Module.Finite k A] in

theorem mul_apply_of_isPrim {x : A} (hx : IsPrim k x) (φ ψ : D) :
    (φ * ψ) x = φ x * ψ 1 + φ 1 * ψ x := by
  rw [CartierDual.mul_apply, hx, map_add, TensorProduct.dualDistrib_apply,
    TensorProduct.dualDistrib_apply]
  rfl

omit [Module.Finite k A] in
theorem mul_apply_one (φ ψ : D) : (φ * ψ) 1 = φ 1 * ψ 1 := by
  rw [CartierDual.mul_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
    TensorProduct.dualDistrib_apply]
  rfl

omit [Module.Finite k A] [Coalgebra.IsCocomm k A] in

theorem counit_eq_zero_of_isPrim {x : A} (hx : IsPrim k x) : Coalgebra.counit (R := k) x = 0 := by
  have h := Coalgebra.rTensor_counit_comul (R := k) x
  rw [hx, map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, Bialgebra.counit_one,
    add_eq_right] at h
  have h2 := congrArg (fun z => Coalgebra.counit (R := k) (TensorProduct.lid k A z)) h
  simp only [TensorProduct.lid_tmul, map_zero, map_smul, Bialgebra.counit_one, smul_eq_mul,
    mul_one] at h2
  exact h2

omit [Module.Finite k A] [Coalgebra.IsCocomm k A] in

theorem apply_eq_sub_apply_of_isPrim {x : A} (hx : IsPrim k x) (φ : D) :
    φ x = (φ - φ 1 • (1 : D)) x := by
  show φ x = φ x - φ 1 • (1 : D) x
  rw [CartierDual.one_apply, counit_eq_zero_of_isPrim hx, smul_zero, sub_zero]

omit [Module.Finite k A] [Coalgebra.IsCocomm k A] in
theorem sub_smul_one_apply_one (φ : D) : (φ - φ 1 • (1 : D)) 1 = 0 := by
  show φ 1 - φ 1 • (1 : D) 1 = 0
  rw [CartierDual.one_apply, Bialgebra.counit_one, smul_eq_mul, mul_one, sub_self]

def evJ (x : A) : ↥J →ₗ[k] k where
  toFun φ := (φ : D) x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem evJ_apply (x : A) (φ : ↥J) : evJ x φ = (φ : D) x := rfl

theorem evJ_mul {x : A} (hx : IsPrim k x) (φ ψ : ↥J) : evJ x (φ * ψ) = 0 := by
  rw [evJ_apply, MulMemClass.coe_mul, mul_apply_of_isPrim hx,
    (mem_augIdeal_iff _).1 φ.2, (mem_augIdeal_iff _).1 ψ.2, mul_zero, zero_mul, add_zero]

noncomputable def θ₀ {x : A} (hx : IsPrim k x) : (augIdeal k A).Cotangent →ₗ[k] k :=
  Ideal.Cotangent.lift (evJ x) (evJ_mul hx)

theorem θ₀_toCotangent {x : A} (hx : IsPrim k x) (φ : ↥J) :
    θ₀ hx ((augIdeal k A).toCotangent φ) = (φ : D) x := rfl

noncomputable def θ : ↥(prim k A) →ₗ[k] Module.Dual k (augIdeal k A).Cotangent where
  toFun x := θ₀ ((mem_prim_iff _).1 x.2)
  map_add' x y := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨φ, rfl⟩ := (augIdeal k A).toCotangent_surjective v
    show (φ : D) ((x : A) + y) = (φ : D) (x : A) + (φ : D) (y : A)
    exact map_add _ _ _
  map_smul' c x := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨φ, rfl⟩ := (augIdeal k A).toCotangent_surjective v
    show (φ : D) (c • (x : A)) = c • (φ : D) (x : A)
    exact map_smul _ _ _

theorem θ_apply_toCotangent (x : ↥(prim k A)) (φ : ↥J) :
    θ x ((augIdeal k A).toCotangent φ) = (φ : D) (x : A) := rfl

theorem θ_injective : Function.Injective (θ (k := k) (A := A)) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have hprim : IsPrim k (x : A) := (mem_prim_iff _).1 x.2
  refine Subtype.ext ((Module.forall_dual_apply_eq_zero_iff k (x : A)).1 fun f => ?_)

  let φ : D := CartierDual.ofDual k A f
  have hφ' : φ - φ 1 • (1 : D) ∈ J := (mem_augIdeal_iff _).2 (sub_smul_one_apply_one φ)
  have h := θ_apply_toCotangent x ⟨_, hφ'⟩
  rw [hx, LinearMap.zero_apply] at h
  show φ (x : A) = 0
  rw [apply_eq_sub_apply_of_isPrim hprim]
  exact h.symm

noncomputable def projJ : D →ₗ[k] ↥J where
  toFun φ := ⟨φ - φ 1 • (1 : D), (mem_augIdeal_iff _).2 (sub_smul_one_apply_one φ)⟩
  map_add' φ ψ := by
    refine Subtype.ext ?_
    show φ + ψ - (φ 1 + ψ 1) • (1 : D) = (φ - φ 1 • (1 : D)) + (ψ - ψ 1 • (1 : D))
    rw [add_smul]; abel
  map_smul' c φ := by
    refine Subtype.ext ?_
    show c • φ - (c * φ 1) • (1 : D) = c • (φ - φ 1 • (1 : D))
    rw [smul_sub, mul_smul]

theorem coe_projJ (φ : D) : (projJ φ : D) = φ - φ 1 • (1 : D) := rfl

theorem projJ_of_mem {φ : D} (hφ : φ ∈ J) : projJ φ = ⟨φ, hφ⟩ := by
  refine Subtype.ext ?_
  rw [coe_projJ, (mem_augIdeal_iff φ).1 hφ, zero_smul, sub_zero]

theorem projJ_mul (φ ψ : D) :
    projJ (φ * ψ) = φ 1 • projJ ψ + ψ 1 • projJ φ + projJ φ * projJ ψ := by
  refine Subtype.ext ?_
  simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, MulMemClass.coe_mul, coe_projJ,
    mul_apply_one]
  simp only [Algebra.smul_def, mul_one, map_mul]
  ring

noncomputable def der (t : Module.Dual k (augIdeal k A).Cotangent) : D →ₗ[k] k :=
  t ∘ₗ ((augIdeal k A).toCotangent.restrictScalars k) ∘ₗ projJ

theorem der_apply (t : Module.Dual k (augIdeal k A).Cotangent) (φ : D) :
    der t φ = t ((augIdeal k A).toCotangent (projJ φ)) := rfl

theorem der_mul (t : Module.Dual k (augIdeal k A).Cotangent) (φ ψ : D) :
    der t (φ * ψ) = φ 1 * der t ψ + ψ 1 * der t φ := by
  have h0 : (augIdeal k A).toCotangent (projJ φ * projJ ψ) = 0 := by
    rw [Ideal.toCotangent_eq_zero, MulMemClass.coe_mul, pow_two]
    exact Ideal.mul_mem_mul (projJ φ).2 (projJ ψ).2
  rw [der_apply, der_apply, der_apply, projJ_mul]
  simp only [map_add, LinearMap.map_smul_of_tower, h0, add_zero, map_smul, smul_eq_mul]

private noncomputable def _root_.HopfAlgebra.PrimitivesDual.lift (t : Module.Dual k (augIdeal k A).Cotangent) : A :=
  (Module.evalEquiv k A).symm (der t ∘ₗ (CartierDual.ofDual k A).toLinearMap)

p2m_export "HopfAlgebra.PrimitivesDual" "lift"
theorem apply_lift (t : Module.Dual k (augIdeal k A).Cotangent) (φ : D) :
    φ (lift t) = der t φ := by
  show (CartierDual.toDual k A φ) ((Module.evalEquiv k A).symm _) = _
  rw [Module.apply_evalEquiv_symm_apply]
  rfl

omit [Coalgebra.IsCocomm k A] in

theorem tmul_ext {z z' : A ⊗[k] A}
    (h : ∀ f g : Module.Dual k A,
      TensorProduct.dualDistrib k A A (f ⊗ₜ[k] g) z = TensorProduct.dualDistrib k A A (f ⊗ₜ[k] g) z') :
    z = z' := by
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff k (z - z')).1 fun F => ?_
  obtain ⟨w, rfl⟩ := (TensorProduct.dualDistribEquiv k A A).surjective F
  rw [CartierDual.dualDistribEquiv_apply_eq, map_sub, sub_eq_zero]
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul f g => exact h f g
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

theorem isPrim_lift (t : Module.Dual k (augIdeal k A).Cotangent) : IsPrim k (lift t) := by
  unfold IsPrim
  refine tmul_ext fun f g => ?_

  have hL : TensorProduct.dualDistrib k A A (f ⊗ₜ[k] g) (Coalgebra.comul (R := k) (lift t)) =
      (CartierDual.ofDual k A f * CartierDual.ofDual k A g) (lift t) :=
    (CartierDual.mul_apply _ _ _).symm
  rw [hL, apply_lift, der_mul, ← apply_lift, ← apply_lift, map_add,
    TensorProduct.dualDistrib_apply, TensorProduct.dualDistrib_apply]
  show f 1 * g (lift t) + g 1 * f (lift t) = f (lift t) * g 1 + f 1 * g (lift t)
  ring

theorem θ_surjective : Function.Surjective (θ (k := k) (A := A)) := by
  intro t
  refine ⟨⟨lift t, (mem_prim_iff _).2 (isPrim_lift t)⟩, LinearMap.ext fun v => ?_⟩
  obtain ⟨φ, rfl⟩ := (augIdeal k A).toCotangent_surjective v
  rw [θ_apply_toCotangent]
  show (φ : D) (lift t) = _
  rw [apply_lift, der_apply, projJ_of_mem φ.2]

noncomputable def θEquiv : ↥(prim k A) ≃ₗ[k] Module.Dual k (augIdeal k A).Cotangent :=
  LinearEquiv.ofBijective θ ⟨θ_injective, θ_surjective⟩

scoped instance : Module.Finite k ↥J :=
  Module.IsNoetherian.finite k ↥((augIdeal k A).restrictScalars k)

scoped instance : Module.Finite k (augIdeal k A).Cotangent :=
  Module.Finite.of_surjective ((augIdeal k A).toCotangent.restrictScalars k)
    (augIdeal k A).toCotangent_surjective

theorem finrank_prim_eq :
    Module.finrank k ↥(prim k A) = Module.finrank k (augIdeal k A).Cotangent := by
  rw [θEquiv.finrank_eq, Subspace.dual_finrank_eq]

omit [Module.Finite k A] in
theorem toDual_pow (φ : D) (n : ℕ) :
    CartierDual.toDual k A (φ ^ n) = (WithConv.toConv (CartierDual.toDual k A φ) ^ n).ofConv := by
  induction n with
  | zero =>
    refine LinearMap.ext fun a => ?_
    rw [pow_zero, pow_zero, LinearMap.convOne_apply, Algebra.algebraMap_self_apply]
    exact CartierDual.one_apply a
  | succ n ih =>
    rw [pow_succ, CartierDual.toDual_mul, ih, WithConv.toConv_ofConv, ← pow_succ]

theorem pow_eq_zero_of_counit_eq_zero {p : ℕ}
    (hV : ∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → β ^ p = 0)
    (φ : D) (hφ : Coalgebra.counit (R := k) φ = 0) : φ ^ p = 0 := by
  rw [CartierDual.counit_apply] at hφ
  have h := hV (WithConv.toConv (CartierDual.toDual k A φ)) hφ
  have h2 : CartierDual.toDual k A (φ ^ p) = 0 := by
    rw [toDual_pow, h, WithConv.ofConv_zero]
  exact CartierDual.ext fun a => congrArg (fun ψ : Module.Dual k A => ψ a) h2

theorem finrank_eq_pow_finrank_prim (p : ℕ) [Fact p.Prime] [CharP k p]
    (hV : ∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → β ^ p = 0) :
    Module.finrank k A = p ^ Module.finrank k ↥(prim k A) := by
  rw [finrank_prim_eq, ← CartierDual.finrank_eq k A]
  exact HopfAlgebra.finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero k p (CartierDual k A)
    (pow_eq_zero_of_counit_eq_zero hV)

end HopfAlgebra.PrimitivesDual
p2m_reactivate "P2MW.S_HopfAlgebra_finrank_eq_pow_finrank_primitives_of_forall_convPow_prime_eq_zero.HopfAlgebra P2MW.S_HopfAlgebra_finrank_eq_pow_finrank_primitives_of_forall_convPow_prime_eq_zero.HopfAlgebra.PrimitivesDual"
p2m_reactivate "P2MW.S_HopfAlgebra_finrank_eq_pow_finrank_primitives_of_forall_convPow_prime_eq_zero.HopfAlgebra"

theorem solution
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]
    (hV : ∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → β ^ p = 0) :
    Module.finrank k A = p ^ Module.finrank k ↥(primitives k A) :=
  HopfAlgebra.PrimitivesDual.finrank_eq_pow_finrank_prim p hV

end
end S_HopfAlgebra_finrank_eq_pow_finrank_primitives_of_forall_convPow_prime_eq_zero
end P2MW
export P2MW.S_HopfAlgebra_finrank_eq_pow_finrank_primitives_of_forall_convPow_prime_eq_zero (solution)
