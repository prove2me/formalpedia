-- Prove2me | solution 1 for HopfAlgebra.exists_primitives_linearEquiv_dual_cotangent_cartierDual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/2362849e-8a47-5461-912e-813056fbc055

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_Dieudonne_ModpRealization
import Theorems.Thm_HopfAlgebra_finrank_primitives_cartierDual_eq_finrank_cotangentSpace
import Theorems.Thm_CartierDual_exists_bialgEquiv_bidual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_primitives_linearEquiv_dual_cotangent_cartierDual

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk finrank_primitives_cartierDual_eq_finrank_cotangentSpace"
namespace PrimCotAux
p2m_open "HopfAlgebra"

section general
variable (k : Type u) [Field k] {A : Type v} [CommRing A] [HopfAlgebra k A]

theorem mem_primitives_iff (x : A) :
    x ∈ primitives k A ↔ Coalgebra.comul (R := k) x = x ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] x := by
  simp only [primitives, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.flip_apply,
    TensorProduct.mk_apply, sub_sub, sub_eq_zero]

theorem counit_eq_zero_of_mem [Nontrivial A] {x : A} (hx : x ∈ primitives k A) : Coalgebra.counit (R := k) x = 0 := by
  have h := Coalgebra.rTensor_counit_comul (R := k) x
  rw [(mem_primitives_iff k x).mp hx, map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
    Bialgebra.counit_one] at h
  have h2 : Coalgebra.counit (R := k) x ⊗ₜ[k] (1 : A) = 0 :=
    add_right_cancel (h.trans (zero_add _).symm)
  have h3 := congrArg (TensorProduct.lid k A) h2
  rw [TensorProduct.lid_tmul, map_zero, smul_eq_zero] at h3
  exact h3.resolve_right one_ne_zero
end general

variable (k : Type u) [Field k] (H : Type v) [CommRing H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H] [Module.Finite k H]

local notation "D" => CartierDual k H
local notation "I" => RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k H))

omit H in
theorem nontrivial_of_bialgebra (A : Type v) [CommRing A] [Bialgebra k A] : Nontrivial A :=
  ⟨⟨0, 1, fun h => by
    have := congrArg (Coalgebra.counit (R := k) (A := A)) h
    rw [map_zero, Bialgebra.counit_one] at this
    exact zero_ne_one this⟩⟩

theorem mem_I_iff (φ : D) : φ ∈ I ↔ φ 1 = 0 := by
  rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply]
  exact Eq.congr_left (CartierDual.counit_apply φ)

theorem mul_apply_eq_zero {x : H} (hx : x ∈ primitives k H) {ψ φ : D} (hψ : ψ ∈ I) (hφ : φ ∈ I) : (ψ * φ) x = 0 := by
  rw [mem_I_iff] at hψ hφ
  rw [CartierDual.mul_apply, (mem_primitives_iff k x).mp hx, map_add, TensorProduct.dualDistrib_apply,
    TensorProduct.dualDistrib_apply, CartierDual.toDual_apply, CartierDual.toDual_apply, CartierDual.toDual_apply,
    CartierDual.toDual_apply, hψ, hφ, mul_zero, zero_mul, add_zero]

noncomputable def pair : H →ₗ[k] (↥I →ₗ[k] k) :=
  LinearMap.mk₂ k (fun x φ => (φ : D) x)
    (fun x y φ => map_add _ _ _)
    (fun c x φ => map_smul _ _ _)
    (fun x φ ψ => by
      show CartierDual.toDual k H ((φ + ψ : ↥I) : D) x = CartierDual.toDual k H (φ : D) x + CartierDual.toDual k H (ψ : D) x
      rw [Submodule.coe_add, map_add, LinearMap.add_apply])
    (fun c x φ => by
      show CartierDual.toDual k H ((c • φ : ↥I) : D) x = c • CartierDual.toDual k H (φ : D) x
      rw [Submodule.coe_smul_of_tower, map_smul, LinearMap.smul_apply])

theorem pair_apply (x : H) (φ : ↥I) : pair k H x φ = (φ : D) x := rfl

theorem le_ker_pair {x : H} (hx : x ∈ primitives k H) :
    ((I : Ideal D) • (⊤ : Submodule D ↥I)).restrictScalars k ≤ LinearMap.ker (pair k H x) := by
  intro y hy
  rw [Submodule.restrictScalars_mem] at hy
  rw [LinearMap.mem_ker, pair_apply]
  refine Submodule.smul_induction_on hy (fun r hr n _ => ?_) (fun a b ha hb => ?_)
  · show (r * (n : D)) x = 0
    exact mul_apply_eq_zero k H hx hr n.2
  · show CartierDual.toDual k H ((a + b : ↥I) : D) x = 0
    rw [Submodule.coe_add, map_add, LinearMap.add_apply]
    exact (congrArg₂ (· + ·) ha hb).trans (add_zero 0)

noncomputable def desc (x : ↥(primitives k H)) : (I).Cotangent →ₗ[k] k :=
  ((((I : Ideal D) • (⊤ : Submodule D ↥I)).restrictScalars k).liftQ (pair k H x.1) (le_ker_pair k H x.2)).comp
    (Submodule.Quotient.restrictScalarsEquiv k ((I : Ideal D) • (⊤ : Submodule D ↥I))).symm.toLinearMap

theorem desc_toCotangent (x : ↥(primitives k H)) (φ : ↥I) : desc k H x ((I).toCotangent φ) = (φ : D) (x : H) := by
  show (((((I : Ideal D) • (⊤ : Submodule D ↥I)).restrictScalars k).liftQ (pair k H x.1) (le_ker_pair k H x.2))
    ((Submodule.Quotient.restrictScalarsEquiv k ((I : Ideal D) • (⊤ : Submodule D ↥I))).symm (Submodule.Quotient.mk φ))) = _
  rw [Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.liftQ_apply, pair_apply]

noncomputable def L : ↥(primitives k H) →ₗ[k] Module.Dual k (I).Cotangent where
  toFun := desc k H
  map_add' x y := by
    apply LinearMap.ext
    intro q
    obtain ⟨φ, rfl⟩ := (I).toCotangent_surjective q
    rw [LinearMap.add_apply, desc_toCotangent, desc_toCotangent, desc_toCotangent, Submodule.coe_add, map_add]
  map_smul' c x := by
    apply LinearMap.ext
    intro q
    obtain ⟨φ, rfl⟩ := (I).toCotangent_surjective q
    rw [LinearMap.smul_apply, desc_toCotangent, desc_toCotangent, Submodule.coe_smul, map_smul, RingHom.id_apply]

theorem L_apply (x : ↥(primitives k H)) (φ : ↥I) : L k H x ((I).toCotangent φ) = (φ : D) (x : H) := desc_toCotangent k H x φ

theorem L_injective : Function.Injective (L k H) := by
  haveI : Nontrivial H := nontrivial_of_bialgebra k H
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hall : ∀ ψ : Module.Dual k H, ψ (x : H) = 0 := by
    intro ψ
    let φ : D := CartierDual.ofDual k H ψ - algebraMap k D (ψ 1)
    have hφ : φ ∈ I := by
      rw [mem_I_iff]
      show CartierDual.ofDual k H ψ 1 - algebraMap k D (ψ 1) 1 = 0
      rw [CartierDual.ofDual_apply, CartierDual.algebraMap_apply, Bialgebra.counit_one, one_mul, sub_self]
    have := L_apply k H x ⟨φ, hφ⟩
    rw [hx, LinearMap.zero_apply] at this
    have h2 : φ (x : H) = ψ (x : H) := by
      show CartierDual.ofDual k H ψ x - algebraMap k D (ψ 1) x = ψ x
      rw [CartierDual.ofDual_apply, CartierDual.algebraMap_apply, counit_eq_zero_of_mem k x.2, zero_mul, sub_zero]
    rw [← h2, ← this]
  exact Subtype.ext ((Module.forall_dual_apply_eq_zero_iff k (x : H)).mp hall)

theorem map_primitives_le {A : Type*} {B : Type*} [CommRing A] [HopfAlgebra k A] [CommRing B] [HopfAlgebra k B]
    (e : A ≃ₐc[k] B) : (primitives k A).map (e : A →ₗ[k] B) ≤ primitives k B := by
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_primitives_iff] at hx
  show e x ∈ primitives k B
  rw [mem_primitives_iff, ← CoalgHomClass.map_comp_comul_apply, hx, map_add, TensorProduct.map_tmul,
    TensorProduct.map_tmul]
  show e x ⊗ₜ[k] e 1 + e 1 ⊗ₜ[k] e x = _
  rw [map_one]

theorem map_primitives_eq {A : Type*} {B : Type*} [CommRing A] [HopfAlgebra k A] [CommRing B] [HopfAlgebra k B]
    (e : A ≃ₐc[k] B) : (primitives k A).map (e : A →ₗ[k] B) = primitives k B := by
  refine le_antisymm (map_primitives_le k e) fun y hy => ?_
  refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
  have := map_primitives_le k e.symm ⟨y, hy, rfl⟩
  exact this

theorem finrank_primitives_eq : Module.finrank k ↥(primitives k H) = Module.finrank k (I).Cotangent := by
  obtain ⟨e, -⟩ := CartierDual.exists_bialgEquiv_bidual k H
  have h1 : Module.finrank k ↥(primitives k (CartierDual k D)) = Module.finrank k ↥(primitives k H) := by
    rw [← map_primitives_eq k e]
    exact LinearEquiv.finrank_map_eq e.toLinearEquiv (primitives k H)
  rw [← h1]
  exact HopfAlgebra.finrank_primitives_cartierDual_eq_finrank_cotangentSpace k D

end HopfAlgebra.PrimCotAux

open HopfAlgebra.PrimCotAux in
theorem solution
    (k : Type u) [Field k] (H : Type v) [CommRing H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]
    [Module.Finite k H] :
    ∃ e : ↥(primitives k H) ≃ₗ[k]
        Module.Dual k (RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k H))).Cotangent,
      ∀ (x : ↥(primitives k H)) (φ : CartierDual k H)
        (hφ : φ ∈ RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k H))),
        e x ((RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k H))).toCotangent ⟨φ, hφ⟩) = φ (x : H) := by
  haveI : Module.Finite k ↥(RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k H))) := by
    show Module.Finite k ↥((RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k H))).restrictScalars k)
    infer_instance
  haveI : Module.Finite k (RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k H))).Cotangent :=
    Module.Finite.of_surjective
      ((RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k H))).toCotangent.restrictScalars k)
      (RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k H))).toCotangent_surjective
  have hdim : Module.finrank k ↥(primitives k H) =
      Module.finrank k (Module.Dual k (RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k H))).Cotangent) := by
    rw [Subspace.dual_finrank_eq]; exact finrank_primitives_eq k H
  refine ⟨LinearMap.linearEquivOfInjective (L k H) (L_injective k H) hdim, fun x φ hφ => ?_⟩
  rw [LinearMap.linearEquivOfInjective_apply]
  exact L_apply k H x ⟨φ, hφ⟩

end S_HopfAlgebra_exists_primitives_linearEquiv_dual_cotangent_cartierDual
end P2MW
export P2MW.S_HopfAlgebra_exists_primitives_linearEquiv_dual_cotangent_cartierDual (solution)
