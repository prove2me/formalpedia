-- Prove2me | solution 1 for HopfAlgebra.exists_mem_primitives_forall_apply_pow_eq_convPow_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/0233d7f1-476b-5d6b-a5ea-816ab46ed374

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_mem_primitives_forall_apply_pow_eq_convPow_apply

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct
open Function CartierDual

universe u v

namespace HopfAlgebra
namespace FrobeniusUntwist
p2m_open "HopfAlgebra"

variable {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]
variable {A : Type v} [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]

theorem toDual_pow (φ : CartierDual k A) (m : ℕ) :
    CartierDual.toDual k A (φ ^ m) = (WithConv.toConv (CartierDual.toDual k A φ) ^ m).ofConv := by
  induction m with
  | zero =>
    refine LinearMap.ext fun a => ?_
    rw [pow_zero, pow_zero, LinearMap.convOne_apply, Algebra.algebraMap_self_apply]
    exact CartierDual.one_apply a
  | succ m ih =>
    rw [pow_succ, CartierDual.toDual_mul, ih, WithConv.toConv_ofConv, ← pow_succ]

theorem convPow_apply (β : WithConv (A →ₗ[k] k)) (m : ℕ) (x : A) :
    (β ^ m).ofConv x = ((CartierDual.ofDual k A β.ofConv) ^ m) x := by
  have : (β ^ m).ofConv = CartierDual.toDual k A ((CartierDual.ofDual k A β.ofConv) ^ m) := by
    rw [toDual_pow, CartierDual.toDual_ofDual, WithConv.toConv_ofConv]
  rw [this]; rfl

theorem convPow_mul_convPow_apply (β γ : WithConv (A →ₗ[k] k)) (m : ℕ) (x : A) :
    (β ^ m * γ ^ m).ofConv x =
      ((CartierDual.ofDual k A β.ofConv) ^ m * (CartierDual.ofDual k A γ.ofConv) ^ m) x := by
  have : β ^ m * γ ^ m = WithConv.toConv (CartierDual.toDual k A
      ((CartierDual.ofDual k A β.ofConv) ^ m * (CartierDual.ofDual k A γ.ofConv) ^ m)) := by
    rw [CartierDual.toDual_mul, toDual_pow, toDual_pow, CartierDual.toDual_ofDual,
      CartierDual.toDual_ofDual, WithConv.toConv_ofConv, WithConv.toConv_ofConv,
      WithConv.toConv_ofConv]
  rw [this]; rfl

theorem mul_apply_one (φ ψ : CartierDual k A) : (φ * ψ) 1 = φ 1 * ψ 1 := by
  rw [CartierDual.mul_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
    TensorProduct.dualDistrib_apply]
  rfl

theorem pow_apply_one (φ : CartierDual k A) (m : ℕ) : (φ ^ m) 1 = (φ 1) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, CartierDual.one_apply, Bialgebra.counit_one]
  | succ m ih => rw [pow_succ, mul_apply_one, ih, pow_succ]

theorem smul_apply' (c : k) (φ : CartierDual k A) (x : A) : (c • φ) x = c * φ x := rfl

theorem add_apply' (φ ψ : CartierDual k A) (x : A) : (φ + ψ) x = φ x + ψ x := rfl

theorem algebraMap_injective : Injective (algebraMap k (CartierDual k A)) := by
  intro r s h
  have := congrArg (fun φ : CartierDual k A => φ 1) h
  simpa only [CartierDual.algebraMap_apply, Bialgebra.counit_one, one_mul] using this

scoped instance instCharP : CharP (CartierDual k A) p :=
  charP_of_injective_algebraMap algebraMap_injective p

theorem tmul_ext {z : A ⊗[k] A}
    (h : ∀ φ ψ : Module.Dual k A, TensorProduct.dualDistrib k A A (φ ⊗ₜ[k] ψ) z = 0) : z = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff k]
  intro F
  obtain ⟨w, rfl⟩ := (TensorProduct.dualDistribEquiv k A A).surjective F
  change TensorProduct.dualDistrib k A A w z = 0
  induction w with
  | zero => simp
  | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
  | tmul φ ψ => exact h φ ψ

section Main

variable [PerfectField k] (n : ℕ) (a : A)
variable (ha : ∀ φ ψ : CartierDual k A,
  (φ ^ p ^ n * ψ ^ p ^ n) a = (φ ^ p ^ n) a * (ψ ^ p ^ n) 1 + (φ ^ p ^ n) 1 * (ψ ^ p ^ n) a)

abbrev Fr : k ≃+* k := iterateFrobeniusEquiv k p n

theorem Fr_apply (c : k) : Fr (k := k) (p := p) n c = c ^ p ^ n :=
  iterateFrobeniusEquiv_def k p n c

def L : CartierDual k A →ₗ[k] k where
  toFun φ := (Fr (k := k) (p := p) n).symm ((φ ^ p ^ n) a)
  map_add' φ ψ := by
    rw [← map_add]
    congr 1
    rw [add_pow_char_pow, add_apply']
  map_smul' c φ := by
    rw [RingHom.id_apply, smul_eq_mul, smul_pow, smul_apply']
    apply (Fr (k := k) (p := p) n).injective
    rw [RingEquiv.apply_symm_apply, map_mul, RingEquiv.apply_symm_apply, Fr_apply]

theorem L_apply (φ : CartierDual k A) :
    L (k := k) (p := p) n a φ = (Fr (k := k) (p := p) n).symm ((φ ^ p ^ n) a) :=
  rfl

def xx : A :=
  (Module.evalEquiv k A).symm (L (k := k) (p := p) n a ∘ₗ (CartierDual.ofDual k A).toLinearMap)

theorem apply_xx (φ : CartierDual k A) :
    φ (xx (k := k) (p := p) n a) = (Fr (k := k) (p := p) n).symm ((φ ^ p ^ n) a) := by
  have := Module.apply_evalEquiv_symm_apply k A (CartierDual.toDual k A φ)
    (L (k := k) (p := p) n a ∘ₗ (CartierDual.ofDual k A).toLinearMap)
  exact this

theorem apply_xx_pow (φ : CartierDual k A) :
    (φ (xx (k := k) (p := p) n a)) ^ p ^ n = (φ ^ p ^ n) a := by
  rw [apply_xx, ← Fr_apply (k := k) (p := p) n, RingEquiv.apply_symm_apply]

include ha in

theorem mul_apply_xx (φ ψ : CartierDual k A) :
    (φ * ψ) (xx (k := k) (p := p) n a) =
      φ (xx (k := k) (p := p) n a) * ψ 1 + φ 1 * ψ (xx (k := k) (p := p) n a) := by
  apply (Fr (k := k) (p := p) n).injective
  rw [Fr_apply, map_add, map_mul, map_mul, Fr_apply, Fr_apply, Fr_apply, Fr_apply, apply_xx_pow,
    apply_xx_pow, apply_xx_pow, ← pow_apply_one, ← pow_apply_one, mul_pow]
  exact ha φ ψ

include ha in
theorem xx_mem_primitives : xx (k := k) (p := p) n a ∈ primitives k A := by
  change Coalgebra.comul (R := k) (xx (k := k) (p := p) n a) - (xx (k := k) (p := p) n a) ⊗ₜ[k] 1
    - 1 ⊗ₜ[k] (xx (k := k) (p := p) n a) = 0
  refine tmul_ext fun φ ψ => ?_
  rw [map_sub, map_sub, TensorProduct.dualDistrib_apply, TensorProduct.dualDistrib_apply]
  have := CartierDual.mul_apply (CartierDual.ofDual k A φ) (CartierDual.ofDual k A ψ)
    (xx (k := k) (p := p) n a)
  rw [CartierDual.toDual_ofDual, CartierDual.toDual_ofDual] at this
  rw [← this, mul_apply_xx n a ha]
  change φ _ * ψ 1 + φ 1 * ψ _ - φ _ * ψ 1 - φ 1 * ψ _ = 0
  ring

include ha in
theorem main : ∃ x ∈ primitives k A, ∀ β : WithConv (A →ₗ[k] k),
    (β.ofConv x) ^ p ^ n = (β ^ p ^ n).ofConv a :=
  ⟨xx (k := k) (p := p) n a, xx_mem_primitives n a ha, fun β => by
    rw [convPow_apply]
    exact apply_xx_pow n a (CartierDual.ofDual k A β.ofConv)⟩

end Main

end HopfAlgebra.FrobeniusUntwist
p2m_reactivate "P2MW.S_HopfAlgebra_exists_mem_primitives_forall_apply_pow_eq_convPow_apply.HopfAlgebra P2MW.S_HopfAlgebra_exists_mem_primitives_forall_apply_pow_eq_convPow_apply.HopfAlgebra.FrobeniusUntwist"
p2m_reactivate "P2MW.S_HopfAlgebra_exists_mem_primitives_forall_apply_pow_eq_convPow_apply.HopfAlgebra"

theorem solution
    (k : Type u) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p] (n : ℕ)
    (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]
    (a : A)
    (ha : ∀ β γ : WithConv (A →ₗ[k] k),
      (β ^ p ^ n * γ ^ p ^ n).ofConv a =
        (β ^ p ^ n).ofConv a * (γ ^ p ^ n).ofConv 1 +
          (β ^ p ^ n).ofConv 1 * (γ ^ p ^ n).ofConv a) :
    ∃ x ∈ primitives k A, ∀ β : WithConv (A →ₗ[k] k),
      (β.ofConv x) ^ p ^ n = (β ^ p ^ n).ofConv a := by
  refine HopfAlgebra.FrobeniusUntwist.main n a fun φ ψ => ?_
  have h := ha (WithConv.toConv (CartierDual.toDual k A φ))
    (WithConv.toConv (CartierDual.toDual k A ψ))
  rw [HopfAlgebra.FrobeniusUntwist.convPow_mul_convPow_apply,
    HopfAlgebra.FrobeniusUntwist.convPow_apply, HopfAlgebra.FrobeniusUntwist.convPow_apply,
    HopfAlgebra.FrobeniusUntwist.convPow_apply, HopfAlgebra.FrobeniusUntwist.convPow_apply] at h
  simpa only [WithConv.ofConv_toConv, CartierDual.ofDual_toDual] using h

end
end S_HopfAlgebra_exists_mem_primitives_forall_apply_pow_eq_convPow_apply
end P2MW
export P2MW.S_HopfAlgebra_exists_mem_primitives_forall_apply_pow_eq_convPow_apply (solution)
