-- Prove2me | solution 1 for HopfAlgebra.exists_mem_primitives_map_eq_of_surjective_of_forall_convPow_prime_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/f566073a-edcf-5b11-b7a0-8f3bd0f6490f

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_ModpRealization
import Theorems.Thm_HopfAlgebra_finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero
import Theorems.Thm_HopfAlgebra_finrank_eq_pow_finrank_primitives_of_forall_convPow_prime_eq_zero
import Theorems.Thm_HopfAlgebra_mem_ker_counit_sq_of_map_mem_sq_of_injective_of_forall_pow_prime_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_mem_primitives_map_eq_of_surjective_of_forall_convPow_prime_eq_zero
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul"

set_option autoImplicit false

open scoped TensorProduct

noncomputable section

universe u v w

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero finrank_eq_pow_finrank_primitives_of_forall_convPow_prime_eq_zero mem_ker_counit_sq_of_map_mem_sq_of_injective_of_forall_pow_prime_eq_zero"
namespace PrimitivesOnto
p2m_open "HopfAlgebra"

section Engine

variable {k : Type u} [Field k] {X : Type v} [CommRing X] [Bialgebra k X]
variable [Module.Finite k X] [Coalgebra.IsCocomm k X]

abbrev augIdeal (k : Type u) [Field k] (X : Type v) [CommRing X] [Bialgebra k X]
    [Module.Finite k X] [Coalgebra.IsCocomm k X] : Ideal (CartierDual k X) :=
  RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k X))

theorem mem_augIdeal_iff (φ : CartierDual k X) : φ ∈ augIdeal k X ↔ φ 1 = 0 := by
  rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply]
  show CartierDual.dualCounit k X (CartierDual.toDual k X φ) = 0 ↔ _
  rw [CartierDual.dualCounit_apply]
  rfl

def IsPrim (k : Type u) [Field k] {X : Type v} [CommRing X] [Bialgebra k X] (x : X) : Prop :=
  Coalgebra.comul (R := k) x = x ⊗ₜ[k] 1 + 1 ⊗ₜ[k] x

def prim (k : Type u) [Field k] (X : Type v) [CommRing X] [Bialgebra k X] : Submodule k X :=
  LinearMap.ker (Coalgebra.comul (R := k) (A := X)
    - (TensorProduct.mk k X X).flip 1 - TensorProduct.mk k X X 1)

omit [Module.Finite k X] [Coalgebra.IsCocomm k X] in
theorem mem_prim_iff (x : X) : x ∈ prim k X ↔ IsPrim k x := by
  unfold prim IsPrim
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sub_apply, sub_sub, sub_eq_zero]
  rfl

omit [Module.Finite k X] in
theorem mul_apply_of_isPrim {x : X} (hx : IsPrim k x) (φ ψ : CartierDual k X) :
    (φ * ψ) x = φ x * ψ 1 + φ 1 * ψ x := by
  rw [CartierDual.mul_apply, hx, map_add, TensorProduct.dualDistrib_apply,
    TensorProduct.dualDistrib_apply]
  rfl

omit [Module.Finite k X] [Coalgebra.IsCocomm k X] in
theorem counit_eq_zero_of_isPrim {x : X} (hx : IsPrim k x) : Coalgebra.counit (R := k) x = 0 := by
  have h := Coalgebra.rTensor_counit_comul (R := k) x
  rw [hx, map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, Bialgebra.counit_one,
    add_eq_right] at h
  have h2 := congrArg (fun z => Coalgebra.counit (R := k) (TensorProduct.lid k X z)) h
  simp only [TensorProduct.lid_tmul, map_zero, map_smul, Bialgebra.counit_one, smul_eq_mul,
    mul_one] at h2
  exact h2

def evJ (x : X) : ↥(augIdeal k X) →ₗ[k] k where
  toFun φ := (φ : CartierDual k X) x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evJ_mul {x : X} (hx : IsPrim k x) (φ ψ : ↥(augIdeal k X)) : evJ x (φ * ψ) = 0 := by
  show ((φ : CartierDual k X) * ψ) x = 0
  rw [mul_apply_of_isPrim hx, (mem_augIdeal_iff _).1 φ.2, (mem_augIdeal_iff _).1 ψ.2, mul_zero,
    zero_mul, add_zero]

def θ₀ {x : X} (hx : IsPrim k x) : (augIdeal k X).Cotangent →ₗ[k] k :=
  Ideal.Cotangent.lift (evJ x) (evJ_mul hx)

def θ : ↥(prim k X) →ₗ[k] Module.Dual k (augIdeal k X).Cotangent where
  toFun x := θ₀ ((mem_prim_iff _).1 x.2)
  map_add' x y := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨φ, rfl⟩ := (augIdeal k X).toCotangent_surjective v
    show (φ : CartierDual k X) ((x : X) + y) =
      (φ : CartierDual k X) (x : X) + (φ : CartierDual k X) (y : X)
    exact map_add _ _ _
  map_smul' c x := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨φ, rfl⟩ := (augIdeal k X).toCotangent_surjective v
    show (φ : CartierDual k X) (c • (x : X)) = c • (φ : CartierDual k X) (x : X)
    exact map_smul _ _ _

theorem θ_apply_toCotangent (x : ↥(prim k X)) (φ : ↥(augIdeal k X)) :
    θ x ((augIdeal k X).toCotangent φ) = (φ : CartierDual k X) (x : X) := rfl

theorem θ_injective : Function.Injective (θ (k := k) (X := X)) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have hprim : IsPrim k (x : X) := (mem_prim_iff _).1 x.2
  refine Subtype.ext ((Module.forall_dual_apply_eq_zero_iff k (x : X)).1 fun f => ?_)
  let φ : CartierDual k X := CartierDual.ofDual k X f
  have hφ1 : (φ - φ 1 • (1 : CartierDual k X)) 1 = 0 := by
    show φ 1 - φ 1 • (1 : CartierDual k X) 1 = 0
    rw [CartierDual.one_apply, Bialgebra.counit_one, smul_eq_mul, mul_one, sub_self]
  have h := θ_apply_toCotangent x ⟨_, (mem_augIdeal_iff _).2 hφ1⟩
  rw [hx, LinearMap.zero_apply] at h
  show φ (x : X) = 0
  have e : φ (x : X) = (φ - φ 1 • (1 : CartierDual k X)) (x : X) := by
    show φ (x : X) = φ (x : X) - φ 1 • (1 : CartierDual k X) (x : X)
    rw [CartierDual.one_apply, counit_eq_zero_of_isPrim hprim, smul_zero, sub_zero]
  rw [e]
  exact h.symm

scoped instance : Module.Finite k ↥(augIdeal k X) :=
  inferInstanceAs (Module.Finite k ↥((augIdeal k X).restrictScalars k))

scoped instance : Module.Finite k (augIdeal k X).Cotangent :=
  Module.Finite.of_surjective ((augIdeal k X).toCotangent.restrictScalars k)
    (augIdeal k X).toCotangent_surjective

omit [Module.Finite k X] in
theorem toDual_pow (φ : CartierDual k X) (n : ℕ) :
    CartierDual.toDual k X (φ ^ n) = (WithConv.toConv (CartierDual.toDual k X φ) ^ n).ofConv := by
  induction n with
  | zero =>
    refine LinearMap.ext fun a => ?_
    rw [pow_zero, pow_zero, LinearMap.convOne_apply, Algebra.algebraMap_self_apply]
    exact CartierDual.one_apply a
  | succ n ih =>
    rw [pow_succ, CartierDual.toDual_mul, ih, WithConv.toConv_ofConv, ← pow_succ]

theorem pow_eq_zero_of_counit_eq_zero {p : ℕ}
    (hV : ∀ β : WithConv (X →ₗ[k] k), β.ofConv 1 = 0 → β ^ p = 0)
    (φ : CartierDual k X) (hφ : Coalgebra.counit (R := k) φ = 0) : φ ^ p = 0 := by
  rw [CartierDual.counit_apply] at hφ
  have h := hV (WithConv.toConv (CartierDual.toDual k X φ)) hφ
  have h2 : CartierDual.toDual k X (φ ^ p) = 0 := by
    rw [toDual_pow, h, WithConv.ofConv_zero]
  exact CartierDual.ext fun a => congrArg (fun ψ : Module.Dual k X => ψ a) h2

end Engine

section Quotient

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Bialgebra k A]
variable {B : Type w} [CommRing B] [Bialgebra k B]
variable (π : A →ₐc[k] B)

theorem comul_map (a : A) :
    Coalgebra.comul (R := k) (π a) =
      TensorProduct.map (π : A →ₗ[k] B) (π : A →ₗ[k] B) (Coalgebra.comul (R := k) a) :=
  (CoalgHomClass.map_comp_comul_apply π a).symm

theorem comm_map (z : A ⊗[k] A) :
    TensorProduct.comm k B B (TensorProduct.map (π : A →ₗ[k] B) (π : A →ₗ[k] B) z) =
      TensorProduct.map (π : A →ₗ[k] B) (π : A →ₗ[k] B) (TensorProduct.comm k A A z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem isCocomm_of_surjective [Coalgebra.IsCocomm k A] (hπ : Function.Surjective π) :
    Coalgebra.IsCocomm k B := by
  refine ⟨LinearMap.ext fun b => ?_⟩
  obtain ⟨a, rfl⟩ := hπ b
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, comul_map, comm_map]
  congr 1
  exact LinearMap.congr_fun (Coalgebra.IsCocomm.comm_comp_comul (R := k) (A := A)) a

theorem isPrim_map {a : A} (ha : IsPrim k a) : IsPrim k (π a) := by
  unfold IsPrim at ha ⊢
  rw [comul_map, ha, map_add, TensorProduct.map_tmul, TensorProduct.map_tmul]
  show π a ⊗ₜ[k] π 1 + π 1 ⊗ₜ[k] π a = _
  rw [map_one]

variable [Module.Finite k A] [Module.Finite k B]

theorem map_injective (hπ : Function.Surjective π) : Function.Injective (CartierDual.map π) := by
  intro φ ψ h
  refine CartierDual.ext fun b => ?_
  obtain ⟨a, rfl⟩ := hπ b
  exact congrArg (fun χ : CartierDual k A => χ a) h

end Quotient

section Main

variable {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
variable {A : Type v} [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]
variable {B : Type w} [CommRing B] [Bialgebra k B]

omit [Module.Finite k A] [Coalgebra.IsCocomm k A] in
theorem primitives_eq : primitives k A = prim k A := rfl

theorem θ_surjective (hV : ∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → β ^ p = 0) :
    Function.Surjective (θ (k := k) (X := A)) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have h1 := HopfAlgebra.finrank_eq_pow_finrank_primitives_of_forall_convPow_prime_eq_zero k p A hV
  have h2 := HopfAlgebra.finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero k p
    (CartierDual k A) (pow_eq_zero_of_counit_eq_zero hV)
  rw [CartierDual.finrank_eq k A, h1, primitives_eq] at h2
  have h3 : Module.finrank k ↥(prim k A) = Module.finrank k (augIdeal k A).Cotangent :=
    Nat.pow_right_injective hp h2
  have h4 : Module.finrank k ↥(prim k A) =
      Module.finrank k (Module.Dual k (augIdeal k A).Cotangent) := by
    rw [h3, Subspace.dual_finrank_eq]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h4).1 θ_injective

theorem exists_mem_prim_map_eq (π : A →ₐc[k] B) (hπ : Function.Surjective π)
    (hV : ∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → β ^ p = 0)
    (b : B) (hb : IsPrim k b) : ∃ a ∈ prim k A, π a = b := by
  haveI : Module.Finite k B := Module.Finite.of_surjective (π : A →ₗ[k] B) hπ
  haveI : Coalgebra.IsCocomm k B := isCocomm_of_surjective π hπ

  let ι : CartierDual k B →ₐc[k] CartierDual k A := CartierDual.map π
  have hι : Function.Injective ι := map_injective π hπ
  have hD : ∀ x : CartierDual k A, Coalgebra.counit (R := k) x = 0 → x ^ p = 0 :=
    pow_eq_zero_of_counit_eq_zero hV

  have hle : augIdeal k B ≤ (augIdeal k A).comap (ι : CartierDual k B →ₐ[k] CartierDual k A) := by
    intro ψ hψ
    show Coalgebra.counit (R := k) (ι ψ) = 0
    rw [CoalgHomClass.counit_comp_apply]
    exact hψ
  let m : (augIdeal k B).Cotangent →ₗ[k] (augIdeal k A).Cotangent :=
    Ideal.mapCotangent _ _ (ι : CartierDual k B →ₐ[k] CartierDual k A) hle
  have hm : Function.Injective m := by
    refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
    obtain ⟨ψ, rfl⟩ := (augIdeal k B).toCotangent_surjective v
    have hv' : ι ψ ∈ augIdeal k A ^ 2 := by
      have : m ((augIdeal k B).toCotangent ψ) = (augIdeal k A).toCotangent ⟨ι ψ, hle ψ.2⟩ := rfl
      rw [this, Ideal.toCotangent_eq_zero] at hv
      exact hv
    rw [Ideal.toCotangent_eq_zero]
    exact HopfAlgebra.mem_ker_counit_sq_of_map_mem_sq_of_injective_of_forall_pow_prime_eq_zero k p
      (CartierDual k A) hD (CartierDual k B) ι hι ψ ψ.2 hv'

  have hnat : ∀ a : ↥(prim k A),
      θ ⟨π a, (mem_prim_iff _).2 (isPrim_map π ((mem_prim_iff _).1 a.2))⟩ = m.dualMap (θ a) := by
    intro a
    refine LinearMap.ext fun v => ?_
    obtain ⟨ψ, rfl⟩ := (augIdeal k B).toCotangent_surjective v
    rfl

  obtain ⟨f, hf⟩ := LinearMap.dualMap_surjective_of_injective hm (θ ⟨b, (mem_prim_iff _).2 hb⟩)
  obtain ⟨a, rfl⟩ := θ_surjective p hV f
  refine ⟨a, a.2, ?_⟩
  have h := (hnat a).trans hf
  exact congrArg (fun y : ↥(prim k B) => (y : B)) (θ_injective h)

end Main

end HopfAlgebra.PrimitivesOnto
p2m_reactivate "P2MW.S_HopfAlgebra_exists_mem_primitives_map_eq_of_surjective_of_forall_convPow_prime_eq_zero.HopfAlgebra P2MW.S_HopfAlgebra_exists_mem_primitives_map_eq_of_surjective_of_forall_convPow_prime_eq_zero.HopfAlgebra.PrimitivesOnto"
p2m_reactivate "P2MW.S_HopfAlgebra_exists_mem_primitives_map_eq_of_surjective_of_forall_convPow_prime_eq_zero.HopfAlgebra"

theorem solution
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]
    (B : Type w) [CommRing B] [Bialgebra k B]
    (π : A →ₐc[k] B) (hπ : Function.Surjective π)
    (hV : ∀ β : WithConv (A →ₗ[k] k), β.ofConv 1 = 0 → β ^ p = 0)
    (b : B) (hb : Coalgebra.comul (R := k) b = b ⊗ₜ[k] 1 + 1 ⊗ₜ[k] b) :
    ∃ a ∈ primitives k A, π a = b :=
  HopfAlgebra.PrimitivesOnto.exists_mem_prim_map_eq p π hπ hV b hb

end
end S_HopfAlgebra_exists_mem_primitives_map_eq_of_surjective_of_forall_convPow_prime_eq_zero
end P2MW
export P2MW.S_HopfAlgebra_exists_mem_primitives_map_eq_of_surjective_of_forall_convPow_prime_eq_zero (solution)
