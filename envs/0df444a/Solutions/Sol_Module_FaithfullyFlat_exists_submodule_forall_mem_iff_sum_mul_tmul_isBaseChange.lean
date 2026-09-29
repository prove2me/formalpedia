-- Prove2me | solution 1 for Module.FaithfullyFlat.exists_submodule_forall_mem_iff_sum_mul_tmul_isBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/0cf4f449-07ca-573e-9a0c-7a4471547c78

import Mathlib
import Definitions.Def_Algebra_DescentCofaces
import Theorems.Thm_Module_FaithfullyFlat_isBaseChange_eqLocus_of_descentDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_FaithfullyFlat_exists_submodule_forall_mem_iff_sum_mul_tmul_isBaseChange

set_option autoImplicit false

open Algebra.DescentCofaces
open scoped TensorProduct

universe u v

namespace Module
p2m_export "Module" "mk FaithfullyFlat restrictScalars FaithfullyFlat.isBaseChange_eqLocus_of_descentDatum"
namespace FaithfullyFlat
p2m_export "Module.FaithfullyFlat" "mk isBaseChange_eqLocus_of_descentDatum"
p2m_open "Module.FaithfullyFlat Module"

namespace TwistDescent

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {G : Type v} [AddCommGroup G] [Fintype G] [DecidableEq G]

def transl {S : Type*} [CommRing S] (u : G → S) : (G → S) →ₗ[S] (G → S) where
  toFun F k := ∑ m, u m * F (k - m)
  map_add' F F' := by ext k; simp [mul_add, Finset.sum_add_distrib]
  map_smul' s F := by ext k; simp [Finset.mul_sum, mul_left_comm]

theorem transl_apply {S : Type*} [CommRing S] (u F : G → S) (k : G) :
    transl u F k = ∑ m, u m * F (k - m) := rfl

theorem transl_transl {S : Type*} [CommRing S] (u v F : G → S) :
    transl u (transl v F) = transl (fun k => ∑ i, u i * v (k - i)) F := by
  ext k
  simp only [transl_apply, Finset.mul_sum, Finset.sum_mul]
  calc ∑ m, ∑ i, u m * (v i * F (k - m - i))
      = ∑ m, ∑ K, u m * (v (K - m) * F (k - K)) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        exact Fintype.sum_equiv (Equiv.addLeft m) _ _ (fun i => by simp [add_sub_cancel_left, sub_sub])
    _ = ∑ K, ∑ m, u m * v (K - m) * F (k - K) := by
        rw [Finset.sum_comm]; simp only [mul_assoc]

theorem transl_single_zero_left {S : Type*} [CommRing S] (F : G → S) :
    transl (Pi.single (0 : G) (1 : S)) F = F := by
  ext k
  rw [transl_apply, Finset.sum_eq_single 0]
  · simp
  · intro m _ hm; simp [hm]
  · simp

theorem transl_transl_neg {S : Type*} [CommRing S] (u : G → S) (hu : CompleteOrthogonalIdempotents u)
    (F : G → S) : transl u (transl (fun k => u (-k)) F) = F := by
  rw [transl_transl]
  have : (fun k => ∑ i, u i * u (-(k - i))) = Pi.single (0 : G) (1 : S) := by
    funext K
    by_cases hK : K = 0
    · subst hK
      simp only [zero_sub, neg_neg, Pi.single_eq_same]
      rw [← hu.complete]
      exact Finset.sum_congr rfl fun i _ => (hu.idem i).eq
    · rw [Pi.single_eq_of_ne hK]
      refine Finset.sum_eq_zero fun i _ => hu.ortho ?_
      intro h; exact hK (by rw [neg_sub] at h; simpa [sub_eq_self] using h.symm)
  rw [this, transl_single_zero_left]

theorem transl_neg_transl {S : Type*} [CommRing S] (u : G → S) (hu : CompleteOrthogonalIdempotents u)
    (F : G → S) : transl (fun k => u (-k)) (transl u F) = F := by
  rw [transl_transl]
  have : (fun k => ∑ i, u (-i) * u (k - i)) = Pi.single (0 : G) (1 : S) := by
    funext K
    by_cases hK : K = 0
    · subst hK
      simp only [zero_sub, Pi.single_eq_same]
      rw [← hu.complete]
      refine (Fintype.sum_equiv (Equiv.neg G) _ _ (fun i => ?_))
      simp [(hu.idem (-i)).eq]
    · rw [Pi.single_eq_of_ne hK]
      refine Finset.sum_eq_zero fun i _ => hu.ortho ?_
      intro h; exact hK (by have := congrArg (· + i) h; simpa using this.symm)
  rw [this, transl_single_zero_left]

theorem map_transl {S T : Type*} [CommRing S] [CommRing T] {Fn : Type*} [FunLike Fn S T]
    [RingHomClass Fn S T] (ρ : Fn) (u F : G → S) (k : G) :
    ρ (transl u F k) = transl (⇑ρ ∘ u) (⇑ρ ∘ F) k := by
  simp [transl_apply, map_sum, map_mul]

variable (R A G) in

def κ₁ : (G → A) ⊗[R] A ≃ₗ[R] (G → A ⊗[R] A) := TensorProduct.piLeft R A (fun _ : G => A)

variable (R A G) in

def κ₂ : A ⊗[R] (G → A) ≃ₗ[R] (G → A ⊗[R] A) := TensorProduct.piRight R R A (fun _ : G => A)

@[scoped simp] theorem κ₁_tmul (f : G → A) (a : A) (k : G) : κ₁ R A G (f ⊗ₜ a) k = f k ⊗ₜ a := by
  simp [κ₁]

@[scoped simp] theorem κ₂_tmul (a : A) (f : G → A) (k : G) : κ₂ R A G (a ⊗ₜ f) k = a ⊗ₜ f k := by
  simp [κ₂]

def φ (e : G → A ⊗[R] A) (he : CompleteOrthogonalIdempotents e) :
    (G → A) ⊗[R] A ≃ₗ[R] A ⊗[R] (G → A) :=
  κ₁ R A G ≪≫ₗ
    (LinearEquiv.ofLinear ((transl e).restrictScalars R) ((transl fun k => e (-k)).restrictScalars R)
      (LinearMap.ext fun F => transl_transl_neg e he F) (LinearMap.ext fun F => transl_neg_transl e he F)) ≪≫ₗ
    (κ₂ R A G).symm

theorem κ₂_φ (e : G → A ⊗[R] A) (he : CompleteOrthogonalIdempotents e) (x : (G → A) ⊗[R] A) :
    κ₂ R A G (φ e he x) = transl e (κ₁ R A G x) := by
  simp [φ]

variable [Module.FaithfullyFlat R A]

omit [Module.FaithfullyFlat R A] in
theorem κ₁_smul (b : A) (x : (G → A) ⊗[R] A) : κ₁ R A G (b • x) = (b ⊗ₜ[R] (1 : A)) • κ₁ R A G x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul f a =>
    funext k
    simp only [TensorProduct.smul_tmul', κ₁_tmul, Pi.smul_apply, smul_eq_mul]
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

omit [Module.FaithfullyFlat R A] in
theorem κ₂_smul (b : A) (y : A ⊗[R] (G → A)) : κ₂ R A G (b • y) = (b ⊗ₜ[R] (1 : A)) • κ₂ R A G y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul a f =>
    funext k
    rw [TensorProduct.smul_tmul', κ₂_tmul, Pi.smul_apply, κ₂_tmul, smul_eq_mul, smul_eq_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]

omit [Module.FaithfullyFlat R A] in
theorem κ₁_lTensor_mulLeft (b : A) (x : (G → A) ⊗[R] A) :
    κ₁ R A G ((LinearMap.mulLeft R b).lTensor (G → A) x) = ((1 : A) ⊗ₜ[R] b) • κ₁ R A G x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul f a =>
    funext k
    rw [LinearMap.lTensor_tmul, LinearMap.mulLeft_apply, κ₁_tmul, Pi.smul_apply, κ₁_tmul, smul_eq_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]

omit [Module.FaithfullyFlat R A] in
theorem κ₂_lTensor_smul (b : A) (y : A ⊗[R] (G → A)) :
    κ₂ R A G ((DistribSMul.toLinearMap R (G → A) b).lTensor A y) = ((1 : A) ⊗ₜ[R] b) • κ₂ R A G y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul a f =>
    funext k
    simp only [LinearMap.lTensor_tmul, DistribSMul.toLinearMap_apply, κ₂_tmul, Pi.smul_apply, smul_eq_mul]
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

omit [Module.FaithfullyFlat R A] in
theorem hφ₁ (e : G → A ⊗[R] A) (he : CompleteOrthogonalIdempotents e)
    (b : A) (x : (G → A) ⊗[R] A) : φ e he (b • x) = b • φ e he x := by
  apply (κ₂ R A G).injective
  rw [κ₂_φ, κ₁_smul, LinearMap.map_smul, κ₂_smul, κ₂_φ]

omit [Module.FaithfullyFlat R A] in
theorem hφ₂ (e : G → A ⊗[R] A) (he : CompleteOrthogonalIdempotents e)
    (b : A) (x : (G → A) ⊗[R] A) :
    φ e he ((LinearMap.mulLeft R b).lTensor (G → A) x) =
      (DistribSMul.toLinearMap R (G → A) b).lTensor A (φ e he x) := by
  apply (κ₂ R A G).injective
  rw [κ₂_φ, κ₁_lTensor_mulLeft, LinearMap.map_smul, κ₂_lTensor_smul, κ₂_φ]

section coords
omit [Module.FaithfullyFlat R A]

abbrev R3 (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] : Type u := A ⊗[R] (A ⊗[R] A)

variable (R A G) in

def cY : (G → A) ⊗[R] (A ⊗[R] A) ≃ₗ[R] (G → R3 R A) := TensorProduct.piLeft R (A ⊗[R] A) (fun _ : G => A)

variable (R A G) in

def c₀ : ((G → A) ⊗[R] A) ⊗[R] A ≃ₗ[R] (G → R3 R A) :=
  TensorProduct.assoc R (G → A) A A ≪≫ₗ cY R A G

variable (R A G) in

def c₂ : A ⊗[R] ((G → A) ⊗[R] A) ≃ₗ[R] (G → R3 R A) :=
  TensorProduct.congr (LinearEquiv.refl R A) (κ₁ R A G) ≪≫ₗ TensorProduct.piRight R R A (fun _ : G => A ⊗[R] A)

variable (R A G) in

def c₁ : (A ⊗[R] (G → A)) ⊗[R] A ≃ₗ[R] (G → R3 R A) :=
  TensorProduct.assoc R A (G → A) A ≪≫ₗ c₂ R A G

variable (R A G) in

def c₃ : A ⊗[R] (A ⊗[R] (G → A)) ≃ₗ[R] (G → R3 R A) :=
  TensorProduct.congr (LinearEquiv.refl R A) (κ₂ R A G) ≪≫ₗ TensorProduct.piRight R R A (fun _ : G => A ⊗[R] A)

@[scoped simp] theorem cY_tmul (f : G → A) (z : A ⊗[R] A) (k : G) : cY R A G (f ⊗ₜ z) k = f k ⊗ₜ z := by
  simp [cY]
@[scoped simp] theorem c₀_tmul (f : G → A) (a a' : A) (k : G) : c₀ R A G ((f ⊗ₜ a) ⊗ₜ a') k = f k ⊗ₜ (a ⊗ₜ a') := by
  simp [c₀]
@[scoped simp] theorem c₂_tmul (a : A) (f : G → A) (a' : A) (k : G) : c₂ R A G (a ⊗ₜ (f ⊗ₜ a')) k = a ⊗ₜ (f k ⊗ₜ a') := by
  simp [c₂]
@[scoped simp] theorem c₁_tmul (a : A) (f : G → A) (a' : A) (k : G) : c₁ R A G ((a ⊗ₜ f) ⊗ₜ a') k = a ⊗ₜ (f k ⊗ₜ a') := by
  simp [c₁]
@[scoped simp] theorem c₃_tmul (a a' : A) (f : G → A) (k : G) : c₃ R A G (a ⊗ₜ (a' ⊗ₜ f)) k = a ⊗ₜ (a' ⊗ₜ f k) := by
  simp [c₃]

theorem c₀_tmul_eq (x : (G → A) ⊗[R] A) (a' : A) (k : G) :
    c₀ R A G (x ⊗ₜ a') k = (c₁₂ R A).hom (κ₁ R A G x k) * ((1 : A) ⊗ₜ ((1 : A) ⊗ₜ a')) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [TensorProduct.zero_tmul, LinearEquiv.map_zero, LinearEquiv.map_zero, Pi.zero_apply,
      Pi.zero_apply, map_zero, zero_mul]
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, Pi.add_apply, hx, hy, add_mul]
  | tmul f a =>
    rw [c₀_tmul, κ₁_tmul, c₁₂_tmul]
    change _ = (f k ⊗ₜ[R] (a ⊗ₜ[R] (1 : A))) * ((1 : A) ⊗ₜ[R] ((1 : A) ⊗ₜ[R] a'))
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one, one_mul]

theorem c₁_tmul_eq (y : A ⊗[R] (G → A)) (a' : A) (k : G) :
    c₁ R A G (y ⊗ₜ a') k = (c₁₂ R A).hom (κ₂ R A G y k) * ((1 : A) ⊗ₜ ((1 : A) ⊗ₜ a')) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [TensorProduct.zero_tmul, LinearEquiv.map_zero, LinearEquiv.map_zero, Pi.zero_apply,
      Pi.zero_apply, map_zero, zero_mul]
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, Pi.add_apply, hx, hy, add_mul]
  | tmul a f =>
    rw [c₁_tmul, κ₂_tmul, c₁₂_tmul]
    change _ = (a ⊗ₜ[R] (f k ⊗ₜ[R] (1 : A))) * ((1 : A) ⊗ₜ[R] ((1 : A) ⊗ₜ[R] a'))
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one, one_mul]

theorem c₂_tmul_eq (a : A) (x : (G → A) ⊗[R] A) (k : G) :
    c₂ R A G (a ⊗ₜ x) k = (a ⊗ₜ ((1 : A) ⊗ₜ (1 : A))) * (c₂₃ R A).hom (κ₁ R A G x k) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, LinearEquiv.map_zero, Pi.zero_apply,
      Pi.zero_apply, map_zero, mul_zero]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, Pi.add_apply, hx, hy, mul_add]
  | tmul f a' =>
    rw [c₂_tmul, κ₁_tmul, c₂₃_tmul]
    change _ = (a ⊗ₜ[R] ((1 : A) ⊗ₜ[R] (1 : A))) * ((1 : A) ⊗ₜ[R] (f k ⊗ₜ[R] a'))
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, one_mul]

theorem c₃_tmul_eq (a : A) (y : A ⊗[R] (G → A)) (k : G) :
    c₃ R A G (a ⊗ₜ y) k = (a ⊗ₜ ((1 : A) ⊗ₜ (1 : A))) * (c₂₃ R A).hom (κ₂ R A G y k) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, LinearEquiv.map_zero, Pi.zero_apply,
      Pi.zero_apply, map_zero, mul_zero]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, Pi.add_apply, hx, hy, mul_add]
  | tmul a'' f =>
    rw [c₃_tmul, κ₂_tmul, c₂₃_tmul]
    change _ = (a ⊗ₜ[R] ((1 : A) ⊗ₜ[R] (1 : A))) * ((1 : A) ⊗ₜ[R] (a'' ⊗ₜ[R] f k))
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, one_mul]

theorem c₁_rTensor_φ (e : G → A ⊗[R] A) (he : CompleteOrthogonalIdempotents e)
    (z : ((G → A) ⊗[R] A) ⊗[R] A) :
    c₁ R A G ((φ e he : (G → A) ⊗[R] A →ₗ[R] A ⊗[R] (G → A)).rTensor A z) =
      transl ((c₁₂ R A).hom ∘ e) (c₀ R A G z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, LinearEquiv.map_zero, LinearEquiv.map_zero, LinearMap.map_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | tmul x a' =>
    funext k
    rw [LinearMap.rTensor_tmul, LinearEquiv.coe_coe, c₁_tmul_eq, κ₂_φ, map_transl, transl_apply,
      transl_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Function.comp_apply, Function.comp_apply, c₀_tmul_eq, mul_assoc]

theorem c₃_lTensor_φ (e : G → A ⊗[R] A) (he : CompleteOrthogonalIdempotents e)
    (w : A ⊗[R] ((G → A) ⊗[R] A)) :
    c₃ R A G ((φ e he : (G → A) ⊗[R] A →ₗ[R] A ⊗[R] (G → A)).lTensor A w) =
      transl ((c₂₃ R A).hom ∘ e) (c₂ R A G w) := by
  induction w using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, LinearEquiv.map_zero, LinearEquiv.map_zero, LinearMap.map_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | tmul a x =>
    funext k
    rw [LinearMap.lTensor_tmul, LinearEquiv.coe_coe, c₃_tmul_eq, κ₂_φ, map_transl, transl_apply,
      transl_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Function.comp_apply, Function.comp_apply, c₂_tmul_eq]
    exact mul_left_comm (a ⊗ₜ[R] ((1 : A) ⊗ₜ[R] (1 : A)) : R3 R A) _ _

variable (R A) in

def σ : R3 R A →ₐ[R] R3 R A :=
  Algebra.TensorProduct.map (AlgHom.id R A) (Algebra.TensorProduct.comm R A A : A ⊗[R] A →ₐ[R] A ⊗[R] A)

@[scoped simp] theorem σ_tmul (a b c : A) : σ R A (a ⊗ₜ (b ⊗ₜ c)) = a ⊗ₜ (c ⊗ₜ b) := by
  simp [σ]

theorem σ_σ (x : R3 R A) : σ R A (σ R A x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a z =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
    | tmul b c => rw [σ_tmul, σ_tmul]

theorem σ_c₁₂ (x : A ⊗[R] A) : σ R A ((c₁₂ R A).hom x) = (c₁₃ R A).hom x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | tmul a b => rw [c₁₂_tmul, c₁₃_tmul]; exact σ_tmul a b 1

theorem c₃_lTensor_comm (w : A ⊗[R] ((G → A) ⊗[R] A)) (k : G) :
    c₃ R A G ((TensorProduct.comm R (G → A) A).toLinearMap.lTensor A w) k = σ R A (c₂ R A G w k) := by
  induction w using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, LinearEquiv.map_zero, Pi.zero_apply, LinearEquiv.map_zero, Pi.zero_apply, map_zero]
  | add x y hx hy => rw [map_add, map_add, Pi.add_apply, hx, hy, map_add, Pi.add_apply, map_add]
  | tmul a x =>
    induction x using TensorProduct.induction_on with
    | zero => rw [TensorProduct.tmul_zero, LinearMap.map_zero, LinearEquiv.map_zero, Pi.zero_apply,
        LinearEquiv.map_zero, Pi.zero_apply, map_zero]
    | add x y hx hy =>
      rw [TensorProduct.tmul_add, map_add, map_add, Pi.add_apply, hx, hy, map_add, Pi.add_apply, map_add]
    | tmul f a' =>
      rw [LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.comm_tmul, c₃_tmul, c₂_tmul, σ_tmul]

theorem cY_lTensor_comm (t : (G → A) ⊗[R] (A ⊗[R] A)) (k : G) :
    cY R A G ((TensorProduct.comm R A A).toLinearMap.lTensor (G → A) t) k = σ R A (cY R A G t k) := by
  induction t using TensorProduct.induction_on with
  | zero =>
    simp only [LinearMap.map_zero, LinearEquiv.map_zero, Pi.zero_apply]
    exact (map_zero (σ R A)).symm
  | add x y hx hy => rw [map_add, map_add, Pi.add_apply, hx, hy, map_add, Pi.add_apply, map_add]
  | tmul f z =>
    induction z using TensorProduct.induction_on with
    | zero =>
      simp only [TensorProduct.tmul_zero, LinearMap.map_zero, LinearEquiv.map_zero, Pi.zero_apply]
      exact (map_zero (σ R A)).symm
    | add x y hx hy =>
      rw [TensorProduct.tmul_add, map_add, map_add, Pi.add_apply, hx, hy, map_add, Pi.add_apply, map_add]
    | tmul a a' =>
      rw [LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.comm_tmul, cY_tmul, cY_tmul, σ_tmul]

end coords

theorem hcocycle (e : G → A ⊗[R] A) (he : CompleteOrthogonalIdempotents e)
    (hcoc : ∀ k, ∑ i, (c₁₂ R A).hom (e i) * (c₂₃ R A).hom (e (k - i)) = (c₁₃ R A).hom (e k)) :
    (φ e he : (G → A) ⊗[R] A →ₗ[R] A ⊗[R] (G → A)).lTensor A ∘ₗ
        (TensorProduct.assoc R A (G → A) A).toLinearMap ∘ₗ
        (φ e he : (G → A) ⊗[R] A →ₗ[R] A ⊗[R] (G → A)).rTensor A =
      (TensorProduct.comm R (G → A) A).toLinearMap.lTensor A ∘ₗ
        (TensorProduct.assoc R A (G → A) A).toLinearMap ∘ₗ
        (φ e he : (G → A) ⊗[R] A →ₗ[R] A ⊗[R] (G → A)).rTensor A ∘ₗ
        (TensorProduct.assoc R (G → A) A A).symm.toLinearMap ∘ₗ
        (TensorProduct.comm R A A).toLinearMap.lTensor (G → A) ∘ₗ
        (TensorProduct.assoc R (G → A) A A).toLinearMap := by

  have hconv : (fun K => ∑ i, ((c₂₃ R A).hom ∘ e) i * ((c₁₂ R A).hom ∘ e) (K - i)) = (c₁₃ R A).hom ∘ e := by
    funext K
    rw [Function.comp_apply, ← hcoc K]
    refine Fintype.sum_equiv (Equiv.subLeft K) _ _ (fun i => ?_)
    simp only [Function.comp_apply, Equiv.subLeft_apply, sub_sub_cancel]
    exact mul_comm ((c₂₃ R A).hom (e i)) _
  refine LinearMap.ext fun z => (c₃ R A G).injective ?_
  funext k

  have hL : c₃ R A G (((φ e he : (G → A) ⊗[R] A →ₗ[R] A ⊗[R] (G → A)).lTensor A)
      ((TensorProduct.assoc R A (G → A) A) (((φ e he : _ →ₗ[R] _).rTensor A) z))) =
      transl ((c₁₃ R A).hom ∘ e) (c₀ R A G z) := by
    rw [c₃_lTensor_φ]
    have : c₂ R A G ((TensorProduct.assoc R A (G → A) A) (((φ e he : _ →ₗ[R] _).rTensor A) z)) =
        c₁ R A G (((φ e he : _ →ₗ[R] _).rTensor A) z) := by
      simp [c₁]
    rw [this, c₁_rTensor_φ, transl_transl, hconv]

  have hR : ∀ k, c₃ R A G (((TensorProduct.comm R (G → A) A).toLinearMap.lTensor A)
      ((TensorProduct.assoc R A (G → A) A) (((φ e he : _ →ₗ[R] _).rTensor A)
        ((TensorProduct.assoc R (G → A) A A).symm (((TensorProduct.comm R A A).toLinearMap.lTensor (G → A))
          ((TensorProduct.assoc R (G → A) A A) z)))))) k =
      transl ((c₁₃ R A).hom ∘ e) (c₀ R A G z) k := by
    intro k
    rw [c₃_lTensor_comm]
    have h1 : ∀ w, c₂ R A G ((TensorProduct.assoc R A (G → A) A) w) = c₁ R A G w := fun w => by simp [c₁]
    rw [h1, c₁_rTensor_φ]
    have h2 : ∀ t, c₀ R A G ((TensorProduct.assoc R (G → A) A A).symm t) = cY R A G t := fun t => by
      simp [c₀]
    rw [h2, map_transl]
    have h3 : ⇑(σ R A) ∘ (cY R A G (((TensorProduct.comm R A A).toLinearMap.lTensor (G → A))
        ((TensorProduct.assoc R (G → A) A A) z))) = c₀ R A G z := by
      funext j
      rw [Function.comp_apply, cY_lTensor_comm, σ_σ]
      simp [c₀]
    have h4 : ⇑(σ R A) ∘ (⇑(c₁₂ R A).hom ∘ e) = ⇑(c₁₃ R A).hom ∘ e := by
      funext j; exact σ_c₁₂ (e j)
    rw [h3, h4]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hL, hR]

theorem mem_eqLocus_iff (e : G → A ⊗[R] A) (he : CompleteOrthogonalIdempotents e) (f : G → A) :
    f ∈ LinearMap.eqLocus ((φ e he : (G → A) ⊗[R] A →ₗ[R] A ⊗[R] (G → A)) ∘ₗ
        (TensorProduct.mk R (G → A) A).flip 1) (TensorProduct.mk R A (G → A) 1) ↔
      ∀ k, ∑ m, e m * (f (k - m) ⊗ₜ[R] 1) = 1 ⊗ₜ[R] f k := by
  rw [LinearMap.mem_eqLocus]
  change φ e he (f ⊗ₜ 1) = 1 ⊗ₜ f ↔ _
  rw [← (κ₂ R A G).injective.eq_iff, κ₂_φ, funext_iff]
  refine forall_congr' fun k => ?_
  rw [transl_apply, κ₂_tmul]
  simp only [κ₁_tmul]

end TwistDescent
p2m_reactivate "P2MW.S_Module_FaithfullyFlat_exists_submodule_forall_mem_iff_sum_mul_tmul_isBaseChange.Module.FaithfullyFlat.TwistDescent"

end Module.FaithfullyFlat
p2m_reactivate "P2MW.S_Module_FaithfullyFlat_exists_submodule_forall_mem_iff_sum_mul_tmul_isBaseChange.Module.FaithfullyFlat.TwistDescent P2MW.S_Module_FaithfullyFlat_exists_submodule_forall_mem_iff_sum_mul_tmul_isBaseChange.Module P2MW.S_Module_FaithfullyFlat_exists_submodule_forall_mem_iff_sum_mul_tmul_isBaseChange.Module.FaithfullyFlat"
p2m_reactivate "P2MW.S_Module_FaithfullyFlat_exists_submodule_forall_mem_iff_sum_mul_tmul_isBaseChange.Module.FaithfullyFlat.TwistDescent P2MW.S_Module_FaithfullyFlat_exists_submodule_forall_mem_iff_sum_mul_tmul_isBaseChange.Module"

open _root_.Module.FaithfullyFlat _root_.P2MW.S_Module_FaithfullyFlat_exists_submodule_forall_mem_iff_sum_mul_tmul_isBaseChange.Module.FaithfullyFlat Module.FaithfullyFlat.TwistDescent in

theorem solution
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.FaithfullyFlat R A]
    {G : Type v} [AddCommGroup G] [Fintype G]
    (e : G → A ⊗[R] A) (he : CompleteOrthogonalIdempotents e)
    (hcoc : ∀ k, ∑ i, (c₁₂ R A).hom (e i) * (c₂₃ R A).hom (e (k - i)) = (c₁₃ R A).hom (e k)) :
    ∃ M : Submodule R (G → A),
      (∀ f : G → A, f ∈ M ↔ ∀ k, ∑ m, e m * (f (k - m) ⊗ₜ[R] 1) = 1 ⊗ₜ[R] f k) ∧
      IsBaseChange A M.subtype := by
  classical
  obtain ⟨hbc, -⟩ := Module.FaithfullyFlat.isBaseChange_eqLocus_of_descentDatum A (φ e he)
    (hφ₁ e he) (hφ₂ e he) (hcocycle e he hcoc)
  exact ⟨_, mem_eqLocus_iff e he, hbc⟩

end S_Module_FaithfullyFlat_exists_submodule_forall_mem_iff_sum_mul_tmul_isBaseChange
end P2MW
export P2MW.S_Module_FaithfullyFlat_exists_submodule_forall_mem_iff_sum_mul_tmul_isBaseChange (solution)
