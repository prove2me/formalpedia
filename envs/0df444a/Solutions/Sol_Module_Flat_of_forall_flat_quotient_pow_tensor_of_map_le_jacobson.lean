-- Prove2me | solution 1 for Module.Flat.of_forall_flat_quotient_pow_tensor_of_map_le_jacobson
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/0b798b81-285b-5a89-9439-6b32b4a508aa

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Flat_of_forall_flat_quotient_pow_tensor_of_map_le_jacobson

set_option autoImplicit false

open scoped TensorProduct
open TensorProduct

namespace LocCritSol

variable {A : Type*} [CommRing A] (B : Type*) [CommRing B] [Algebra A B]

theorem range_rTensor_subtype_smul_top_le (I : Ideal A) (P : Type*) [AddCommGroup P] [Module A P] :
    LinearMap.range (LinearMap.rTensor B (I • (⊤ : Submodule A P)).subtype) ≤ I • (⊤ : Submodule A (P ⊗[A] B)) := by
  rintro _ ⟨t, rfl⟩
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul x b =>
    rw [LinearMap.rTensor_tmul, Submodule.subtype_apply]
    obtain ⟨x, hx⟩ := x
    induction hx using Submodule.smul_induction_on' with
    | smul r hr n _ =>
      show (r • n) ⊗ₜ[A] b ∈ _
      rw [← smul_tmul']
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    | add x _ y _ hx hy =>
      show (x + y) ⊗ₜ[A] b ∈ _
      rw [add_tmul]; exact Submodule.add_mem _ hx hy
  | add s t hs ht => rw [map_add]; exact Submodule.add_mem _ hs ht

end LocCritSol

open LocCritSol in
theorem solution
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A] [IsNoetherianRing B]
    (I : Ideal A) (hI : I.map (algebraMap A B) ≤ (⊥ : Ideal B).jacobson)
    (h : ∀ n : ℕ, Module.Flat (A ⧸ I ^ n) ((A ⧸ I ^ n) ⊗[A] B)) :
    Module.Flat A B := by
  classical
  rw [Module.Flat.iff_rTensor_injective']
  intro 𝔞
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro k hk
  rw [LinearMap.mem_ker] at hk
  rw [Submodule.mem_bot]

  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I (𝔞 : Submodule A A)

  suffices hmem : ∀ n : ℕ, k ∈ I ^ n • (⊤ : Submodule A (↥𝔞 ⊗[A] B)) by
    let e : ↥𝔞 ⊗[A] B ≃ₗ[A] B ⊗[A] ↥𝔞 := TensorProduct.comm A (↥𝔞) B
    have hkr : ∀ n : ℕ, e k ∈ ((I.map (algebraMap A B)) ^ n • (⊤ : Submodule B (B ⊗[A] ↥𝔞))).restrictScalars A := by
      intro n
      rw [← Ideal.map_pow, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
      have h1 := Submodule.mem_map_of_mem (f := (e : ↥𝔞 ⊗[A] B →ₗ[A] B ⊗[A] ↥𝔞)) (hmem n)
      rwa [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range] at h1
    have hbot := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := B ⊗[A] ↥𝔞) (I.map (algebraMap A B)) hI
    have : e k ∈ (⨅ i : ℕ, (I.map (algebraMap A B)) ^ i • (⊤ : Submodule B (B ⊗[A] ↥𝔞))) :=
      (Submodule.mem_iInf _).mpr fun n => hkr n
    rw [hbot, Submodule.mem_bot] at this
    exact e.injective (by rw [this, map_zero])
  intro n

  obtain ⟨m, hmn, hmc⟩ : ∃ m : ℕ, m = n + c ∧ c ≤ m := ⟨n + c, rfl, by omega⟩
  haveI : Module.Flat (A ⧸ I ^ m) ((A ⧸ I ^ m) ⊗[A] B) := h m

  let 𝔟 : Ideal (A ⧸ I ^ m) := 𝔞.map (Ideal.Quotient.mk (I ^ m))
  let π : ↥𝔞 →ₗ[A] ↥𝔟 :=
    { toFun := fun x => ⟨Ideal.Quotient.mk (I ^ m) (x : A), Ideal.mem_map_of_mem _ x.2⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun a x => Subtype.ext (by simp [Algebra.smul_def]) }
  have hπs : Function.Surjective π := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hy
    exact ⟨⟨x, hx⟩, rfl⟩

  have hker : LinearMap.ker π ≤ I ^ n • (⊤ : Submodule A ↥𝔞) := by
    intro x hx
    rw [LinearMap.mem_ker, Subtype.ext_iff] at hx
    change Ideal.Quotient.mk (I ^ m) (x : A) = 0 at hx
    rw [Ideal.Quotient.eq_zero_iff_mem] at hx
    have hx' : (x : A) ∈ I ^ m • (⊤ : Submodule A A) ⊓ (𝔞 : Submodule A A) := by
      refine ⟨?_, x.2⟩
      rw [Ideal.smul_eq_mul, Ideal.mul_top]; exact hx
    rw [hc m hmc, show m - c = n by omega] at hx'
    have hx'' : (x : A) ∈ I ^ n • (𝔞 : Submodule A A) :=
      smul_mono_right (I ^ n) (inf_le_right : I ^ c • ⊤ ⊓ (𝔞 : Submodule A A) ≤ 𝔞) hx'
    have hmap : Submodule.map (𝔞 : Submodule A A).subtype (I ^ n • (⊤ : Submodule A ↥𝔞)) =
        I ^ n • (𝔞 : Submodule A A) := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
    rw [← hmap] at hx''
    obtain ⟨y, hy, hyx⟩ := hx''
    rwa [show y = x from Subtype.ext hyx] at hy

  have hexact := rTensor_exact B (LinearMap.exact_subtype_ker_map π) hπs
  suffices hπk : LinearMap.rTensor B π k = 0 by
    obtain ⟨t, ht⟩ := (hexact k).mp hπk
    rw [← ht]
    have : LinearMap.rTensor B (LinearMap.ker π).subtype =
        LinearMap.rTensor B (I ^ n • (⊤ : Submodule A ↥𝔞)).subtype ∘ₗ LinearMap.rTensor B (Submodule.inclusion hker) := by
      rw [← LinearMap.rTensor_comp]; rfl
    rw [this, LinearMap.comp_apply]
    exact range_rTensor_subtype_smul_top_le B (I ^ n) ↥𝔞 ⟨_, rfl⟩

  have hinj : Function.Injective (LinearMap.rTensor ((A ⧸ I ^ m) ⊗[A] B) (𝔟.subtype)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective

  set Am : Type _ := A ⧸ I ^ m with hAm

  have hone : ∀ (a : A) (b : B), ((1 : A ⧸ I ^ m) ⊗ₜ[A] (a • b)) = (algebraMap A (A ⧸ I ^ m) a) ⊗ₜ[A] b := by
    intro a b
    rw [tmul_smul, smul_tmul', Algebra.smul_def, mul_one]
  have hq : ∀ (s : A ⧸ I ^ m) (b : B), s • ((1 : A ⧸ I ^ m) ⊗ₜ[A] b) = s ⊗ₜ[A] b := by
    intro s b
    rw [smul_tmul', smul_eq_mul, mul_one]
  have hsm : ∀ (a : A) (y : ↥𝔟) (b : B),
      (a • y) ⊗ₜ[A ⧸ I ^ m] ((1 : A ⧸ I ^ m) ⊗ₜ[A] b) = y ⊗ₜ[A ⧸ I ^ m] ((1 : A ⧸ I ^ m) ⊗ₜ[A] (a • b)) := by
    intro a y b
    rw [← algebraMap_smul (A ⧸ I ^ m) a y,
      TensorProduct.smul_tmul (R := A ⧸ I ^ m) (algebraMap A (A ⧸ I ^ m) a) y ((1 : A ⧸ I ^ m) ⊗ₜ[A] b),
      hq, hone]
  let θ : ↥𝔟 ⊗[A] B →+ ↥𝔟 ⊗[A ⧸ I ^ m] ((A ⧸ I ^ m) ⊗[A] B) :=
    TensorProduct.liftAddHom
      { toFun := fun y => { toFun := fun b => y ⊗ₜ[A ⧸ I ^ m] ((1 : A ⧸ I ^ m) ⊗ₜ[A] b)
                            map_zero' := by simp only [tmul_zero]
                            map_add' := fun b b' => by simp only [tmul_add] }
        map_zero' := by ext b; simp only [zero_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.zero_apply]
        map_add' := fun y y' => by ext b; simp only [add_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.add_apply] }
      (fun a y b => hsm a y b)
  have hθ : ∀ (y : ↥𝔟) (b : B), θ (y ⊗ₜ[A] b) = y ⊗ₜ[A ⧸ I ^ m] ((1 : A ⧸ I ^ m) ⊗ₜ[A] b) := fun y b =>
    TensorProduct.liftAddHom_tmul _ _ y b

  have hsm' : ∀ (y : ↥𝔟) (a : A) (s : A ⧸ I ^ m) (b : B),
      ((a • s) • y) ⊗ₜ[A] b = (s • y) ⊗ₜ[A] (a • b) := by
    intro y a s b
    rw [smul_assoc, smul_tmul, tmul_smul]
  let G : ↥𝔟 → ((A ⧸ I ^ m) ⊗[A] B →+ ↥𝔟 ⊗[A] B) := fun y =>
    TensorProduct.liftAddHom
      { toFun := fun s => { toFun := fun b => (s • y) ⊗ₜ[A] b
                            map_zero' := by simp only [tmul_zero]
                            map_add' := fun b b' => by simp only [tmul_add] }
        map_zero' := by ext b; simp only [zero_smul, zero_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.zero_apply]
        map_add' := fun s s' => by ext b; simp only [add_smul, add_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.add_apply] }
      (fun a s b => hsm' y a s b)
  have hG : ∀ (y : ↥𝔟) (s : A ⧸ I ^ m) (b : B), G y (s ⊗ₜ[A] b) = (s • y) ⊗ₜ[A] b := fun y s b =>
    TensorProduct.liftAddHom_tmul _ _ s b
  have hGadd : ∀ (y y' : ↥𝔟) (t : (A ⧸ I ^ m) ⊗[A] B), G (y + y') t = G y t + G y' t := by
    intro y y' t
    induction t using TensorProduct.induction_on with
    | zero => rw [AddMonoidHom.map_zero, AddMonoidHom.map_zero, AddMonoidHom.map_zero, add_zero]
    | tmul s b => rw [hG, hG, hG, smul_add, add_tmul]
    | add t t' ht ht' => rw [AddMonoidHom.map_add, AddMonoidHom.map_add, AddMonoidHom.map_add, ht, ht']; abel
  have hGsm : ∀ (s : A ⧸ I ^ m) (y : ↥𝔟) (t : (A ⧸ I ^ m) ⊗[A] B), G (s • y) t = G y (s • t) := by
    intro s y t
    induction t using TensorProduct.induction_on with
    | zero => rw [smul_zero, AddMonoidHom.map_zero, AddMonoidHom.map_zero]
    | tmul s' b => rw [hG, smul_tmul', hG, smul_smul, smul_eq_mul, mul_comm]
    | add t t' ht ht' => rw [smul_add, AddMonoidHom.map_add, AddMonoidHom.map_add, ht, ht']
  let θ' : ↥𝔟 ⊗[A ⧸ I ^ m] ((A ⧸ I ^ m) ⊗[A] B) →+ ↥𝔟 ⊗[A] B :=
    TensorProduct.liftAddHom
      { toFun := G
        map_zero' := by
          refine AddMonoidHom.ext fun t => ?_
          rw [AddMonoidHom.zero_apply]
          induction t using TensorProduct.induction_on with
          | zero => rw [AddMonoidHom.map_zero]
          | tmul s b => rw [hG, smul_zero, zero_tmul]
          | add t t' ht ht' => rw [AddMonoidHom.map_add, ht, ht', add_zero]
        map_add' := fun y y' => AddMonoidHom.ext fun t => by rw [AddMonoidHom.add_apply]; exact hGadd y y' t }
      (fun s y t => hGsm s y t)
  have hθ'θ : ∀ z, θ' (θ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [AddMonoidHom.map_zero, AddMonoidHom.map_zero]
    | tmul y b => rw [hθ, TensorProduct.liftAddHom_tmul]; show G y ((1 : A ⧸ I ^ m) ⊗ₜ[A] b) = y ⊗ₜ[A] b; rw [hG, one_smul]
    | add z z' hz hz' => rw [AddMonoidHom.map_add, AddMonoidHom.map_add, hz, hz']
  have hθinj : Function.Injective θ := fun z z' hzz => by
    have := congrArg θ' hzz; rwa [hθ'θ, hθ'θ] at this

  have hsmA : ∀ (a a' : A) (b : B),
      (Ideal.Quotient.mk (I ^ m) (a • a')) ⊗ₜ[A ⧸ I ^ m] ((1 : A ⧸ I ^ m) ⊗ₜ[A] b) =
        (Ideal.Quotient.mk (I ^ m) a') ⊗ₜ[A ⧸ I ^ m] ((1 : A ⧸ I ^ m) ⊗ₜ[A] (a • b)) := by
    intro a a' b
    rw [smul_eq_mul, map_mul, ← smul_eq_mul,
      TensorProduct.smul_tmul (R := A ⧸ I ^ m) (Ideal.Quotient.mk (I ^ m) a) (Ideal.Quotient.mk (I ^ m) a') ((1 : A ⧸ I ^ m) ⊗ₜ[A] b),
      hq, hone, Ideal.Quotient.algebraMap_eq]
  let ΨA : A ⊗[A] B →+ (A ⧸ I ^ m) ⊗[A ⧸ I ^ m] ((A ⧸ I ^ m) ⊗[A] B) :=
    TensorProduct.liftAddHom
      { toFun := fun a => { toFun := fun b => (Ideal.Quotient.mk (I ^ m) a) ⊗ₜ[A ⧸ I ^ m] ((1 : A ⧸ I ^ m) ⊗ₜ[A] b)
                            map_zero' := by simp only [tmul_zero]
                            map_add' := fun b b' => by simp only [tmul_add] }
        map_zero' := by ext b; simp only [map_zero, zero_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.zero_apply]
        map_add' := fun a a' => by ext b; simp only [map_add, add_tmul, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.add_apply] }
      (fun a a' b => hsmA a a' b)
  have hΨA : ∀ (a : A) (b : B), ΨA (a ⊗ₜ[A] b) = (Ideal.Quotient.mk (I ^ m) a) ⊗ₜ[A ⧸ I ^ m] ((1 : A ⧸ I ^ m) ⊗ₜ[A] b) :=
    fun a b => TensorProduct.liftAddHom_tmul _ _ a b

  have hsq : ∀ t : ↥𝔞 ⊗[A] B,
      LinearMap.rTensor ((A ⧸ I ^ m) ⊗[A] B) 𝔟.subtype (θ (LinearMap.rTensor B π t)) =
        ΨA (LinearMap.rTensor B 𝔞.subtype t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [LinearMap.map_zero, AddMonoidHom.map_zero, LinearMap.map_zero, LinearMap.map_zero, AddMonoidHom.map_zero]
    | tmul x b =>
      rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, hθ, hΨA, LinearMap.rTensor_tmul]
      rfl
    | add s t hs ht =>
      rw [LinearMap.map_add, AddMonoidHom.map_add, LinearMap.map_add, LinearMap.map_add, AddMonoidHom.map_add, hs, ht]
  have h0 : ΨA (LinearMap.rTensor B 𝔞.subtype k) = 0 := by rw [hk, AddMonoidHom.map_zero]
  rw [← hsq] at h0
  have h1 : θ (LinearMap.rTensor B π k) = 0 := hinj (by rw [h0, LinearMap.map_zero])
  exact hθinj (by rw [h1, AddMonoidHom.map_zero])

end S_Module_Flat_of_forall_flat_quotient_pow_tensor_of_map_le_jacobson
end P2MW
export P2MW.S_Module_Flat_of_forall_flat_quotient_pow_tensor_of_map_le_jacobson (solution)
