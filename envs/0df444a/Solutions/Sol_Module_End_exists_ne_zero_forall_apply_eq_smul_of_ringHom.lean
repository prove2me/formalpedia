-- Prove2me | solution 1 for Module.End.exists_ne_zero_forall_apply_eq_smul_of_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/a51ebe11-6666-5aa6-8af9-e586be9fa60a

import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Artinian.Module
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.NatInt
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Noetherian.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_End_exists_ne_zero_forall_apply_eq_smul_of_ringHom

open Ideal

theorem FrobChareqEngine.engine3
    {K A V : Type*} [Field K] [CommRing A] [Algebra K A] [AddCommGroup V] [Module K V]
    [Module A V] [IsScalarTower K A V] [Module.Finite K V] [FaithfulSMul A V]
    (𝔪 : Ideal A) (h𝔪 : 𝔪.IsMaximal) : ∃ v : V, v ≠ 0 ∧ ∀ a ∈ 𝔪, a • v = 0 := by
  classical

  have hinj : Function.Injective (Algebra.lsmul K K V : A →ₐ[K] Module.End K V) := by
    intro a b hab
    refine FaithfulSMul.eq_of_smul_eq_smul (α := V) fun v => ?_
    have := congrArg (fun f : Module.End K V => f v) hab
    simpa using this
  haveI : Module.Finite K A :=
    Module.Finite.of_injective (Algebra.lsmul K K V : A →ₐ[K] Module.End K V).toLinearMap hinj
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  haveI : IsNoetherianRing A := inferInstance
  haveI : Module.Finite A V := Module.Finite.of_restrictScalars_finite K A V

  have hann : Module.annihilator A V = ⊥ := by
    refine eq_bot_iff.mpr fun a ha => ?_
    rw [Module.mem_annihilator] at ha
    refine (Ideal.mem_bot).mpr (FaithfulSMul.eq_of_smul_eq_smul (α := V) fun v => ?_)
    rw [ha v, zero_smul]

  have hmin : 𝔪 ∈ (Module.annihilator A V).minimalPrimes := by
    rw [hann]
    refine ⟨⟨h𝔪.isPrime, bot_le⟩, ?_⟩
    rintro q ⟨hq, -⟩ hle
    have hqmax : q.IsMaximal := (IsArtinianRing.isPrime_iff_isMaximal q).mp hq
    exact (hqmax.eq_of_le h𝔪.ne_top hle).ge

  have hass := Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes A V hmin
  change (⊥ : Submodule A V).IsAssociatedPrime 𝔪 at hass
  rw [Submodule.isAssociatedPrime_iff] at hass
  obtain ⟨-, x, hx⟩ := hass
  refine ⟨x, ?_, fun a ha => ?_⟩
  · rintro rfl
    apply h𝔪.ne_top
    rw [hx, eq_top_iff]
    intro a _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem _
  · have : a ∈ (⊥ : Submodule A V).colon {x} := hx ▸ ha
    rw [Submodule.mem_colon_singleton] at this
    simpa using this

theorem FrobChareqEngine.engine4
    {K A V : Type*} [Field K] [CommRing A] [Algebra K A] [AddCommGroup V] [Module K V]
    [Module A V] [IsScalarTower K A V] [Module.Finite K V] [FaithfulSMul A V]
    (χ : A →ₐ[K] K) : ∃ v : V, v ≠ 0 ∧ ∀ a : A, a • v = χ a • v := by
  have hsurj : Function.Surjective χ := fun c => ⟨algebraMap K A c, χ.commutes c⟩
  have hmax : (RingHom.ker χ).IsMaximal := RingHom.ker_isMaximal_of_surjective χ hsurj
  obtain ⟨v, hv, hkill⟩ :=
    FrobChareqEngine.engine3 (K := K) (V := V) (RingHom.ker χ) hmax
  refine ⟨v, hv, fun a => ?_⟩
  have hmem : a - algebraMap K A (χ a) ∈ RingHom.ker χ := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have := hkill _ hmem
  rw [sub_smul, sub_eq_zero, algebraMap_smul] at this
  exact this

open scoped TensorProduct in

theorem FrobChareqEngine.engine5a
    {K V T D : Type*} [Field K] [AddCommGroup V] [Module K V] [CommRing T] [CommRing D]
    [Module.Finite ℤ D] [Module.Free ℤ D]
    (ρ : T →+* Module.End K V) (χ : T →+* K) (π : T →+* D)
    (χbar : D →+* K) (hχ : ∀ t, χbar (π t) = χ t)
    (e : D →+ V) (heT : ∀ t d, e (π t * d) = ρ t (e d))
    (hind : ∀ (n : ℕ) (d : Fin n → D), LinearIndependent ℤ d →
      LinearIndependent K (fun i => e (d i))) :
    ∃ v : V, v ≠ 0 ∧ ∀ t : T, ρ t v = χ t • v := by
  classical

  let n := Fintype.card (Module.Free.ChooseBasisIndex ℤ D)
  let b : Module.Basis (Fin n) ℤ D := (Module.Free.chooseBasis ℤ D).reindex (Fintype.equivFin _)

  haveI : Module.Finite K (K ⊗[ℤ] D) := inferInstance
  let χA : K ⊗[ℤ] D →ₐ[K] K :=
    Algebra.TensorProduct.lift (AlgHom.id K K) χbar.toIntAlgHom fun _ _ => Commute.all _ _
  have hχA : ∀ (c : K) (d : D), χA (c ⊗ₜ d) = c * χbar d := fun c d =>
    Algebra.TensorProduct.lift_tmul _ _ _ c d

  obtain ⟨w, hw0, hw⟩ :=
    FrobChareqEngine.engine4 (K := K) (V := K ⊗[ℤ] D) χA

  let eZ : D →ₗ[ℤ] V := e.toIntLinearMap
  let ι : K ⊗[ℤ] D →ₗ[K] V :=
    TensorProduct.AlgebraTensorModule.lift ((LinearMap.id : K →ₗ[K] K).smulRight eZ)
  have hι : ∀ (c : K) (d : D), ι (c ⊗ₜ d) = c • e d := fun c d => rfl

  have hιT : ∀ (t : T) (a : K ⊗[ℤ] D), ρ t (ι a) = ι ((1 : K) ⊗ₜ (π t) * a) := by
    intro t a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul c d =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hι, hι, map_smul, heT]
    | add a₁ a₂ h₁ h₂ => rw [mul_add, map_add, map_add, map_add, h₁, h₂]

  let bA : Module.Basis (Fin n) K (K ⊗[ℤ] D) := Algebra.TensorProduct.basis K b
  have hyK : LinearIndependent K (fun i => e (b i)) := hind n b b.linearIndependent
  have hιb : ∀ i, ι (bA i) = e (b i) := by
    intro i
    rw [Algebra.TensorProduct.basis_apply, hι, one_smul]
  have hιinj : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    rw [← bA.sum_repr a] at ha ⊢
    simp only [map_sum, map_smul, hιb] at ha
    have hc := Fintype.linearIndependent_iff.mp hyK _ ha
    simp [hc]

  refine ⟨ι w, fun h => hw0 (hιinj (by rw [h, map_zero])), fun t => ?_⟩
  have hw' := hw ((1 : K) ⊗ₜ π t)
  rw [smul_eq_mul] at hw'
  rw [hιT, hw', map_smul, hχA, one_mul, hχ]

theorem solution {K V T : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] [CommRing T] (ρ : T →+* Module.End K V) (L : Submodule ℤ V) (hL : L.FG) (hstab : ∀ (t : T), ∀ x ∈ L, ρ t x ∈ L) (hfaith : ∀ t : T, (∀ x ∈ L, ρ t x = 0) → t = 0) (hfree : ∀ (n : ℕ) (y : Fin n → V), (∀ i, y i ∈ L) → LinearIndependent ℤ y → LinearIndependent K y) (χ : T →+* K) : ∃ v : V, v ≠ 0 ∧ ∀ t : T, ρ t v = χ t • v := by
  classical

  letI modTV : Module T V := Module.compHom V ρ
  have hsmulT : ∀ (t : T) (v : V), t • v = ρ t v := fun _ _ => rfl
  let LT : Submodule T V :=
    { carrier := L
      add_mem' := fun ha hb => L.add_mem ha hb
      zero_mem' := L.zero_mem
      smul_mem' := fun t x hx => hstab t x hx }

  haveI hVtf : IsAddTorsionFree V := by
    refine ⟨fun n hn a b hab => ?_⟩
    have h : (n : K) • a = (n : K) • b := by
      simpa only [Nat.cast_smul_eq_nsmul] using hab
    exact smul_right_injective V (Nat.cast_ne_zero.mpr hn) h
  haveI hLTtf : IsAddTorsionFree LT := by
    refine ⟨fun n hn a b hab => ?_⟩
    apply Subtype.ext
    apply IsAddTorsionFree.nsmul_right_injective hn
    have := congrArg Subtype.val hab
    simpa using this

  haveI : Module.Finite ℤ L := Module.Finite.iff_fg.mpr hL
  let eL : L ≃ₗ[ℤ] LT :=
    { toFun := fun x => ⟨x, x.2⟩
      invFun := fun x => ⟨x, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  haveI : Module.Finite ℤ LT := Module.Finite.equiv eL
  haveI : Module.Finite T LT := Module.Finite.of_restrictScalars_finite ℤ T LT

  haveI : Module.Free ℤ LT := inferInstance
  let ψ : T →+* Module.End ℤ LT := Module.toModuleEnd ℤ (S := T) LT
  have hψ : Function.Injective ψ.toAddMonoidHom.toIntLinearMap := by
    intro s t hst
    rw [← sub_eq_zero]
    apply hfaith
    intro x hx
    have h := congrArg (fun f : Module.End ℤ LT => ((f ⟨x, hx⟩ : LT) : V)) hst
    simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_toIntLinearMap,
      AddMonoidHom.coe_coe, ψ, Module.toModuleEnd_apply, DistribSMul.toLinearMap_apply] at h
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero]
    exact h
  haveI : Module.Finite ℤ T := Module.Finite.of_injective _ hψ
  haveI : IsNoetherianRing T := IsNoetherianRing.of_finite ℤ T

  have hann : Module.annihilator T LT = ⊥ := by
    refine eq_bot_iff.mpr fun t ht => ?_
    rw [Module.mem_annihilator] at ht
    refine (Ideal.mem_bot).mpr (hfaith t fun x hx => ?_)
    have := congrArg Subtype.val (ht ⟨x, hx⟩)
    simp at this
    exact this

  haveI : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime χ
  obtain ⟨𝔓, h𝔓min, h𝔓le⟩ :=
    Ideal.exists_minimalPrimes_le (show (⊥ : Ideal T) ≤ RingHom.ker χ from bot_le)
  have hmin : 𝔓 ∈ (Module.annihilator T LT).minimalPrimes := by rw [hann]; exact h𝔓min
  have hass := Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes T LT hmin
  change (⊥ : Submodule T LT).IsAssociatedPrime 𝔓 at hass
  rw [Submodule.isAssociatedPrime_iff] at hass
  obtain ⟨h𝔓prime, x, hx⟩ := hass
  haveI : 𝔓.IsPrime := h𝔓prime
  have hmem𝔓 : ∀ t : T, t ∈ 𝔓 ↔ ρ t (x : V) = 0 := by
    intro t
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot, Subtype.ext_iff]
    exact Iff.rfl
  have hxL : (x : V) ∈ L := x.2

  let e : (T ⧸ 𝔓) →ₗ[T] V :=
    Submodule.liftQ 𝔓 (LinearMap.toSpanSingleton T V (x : V)) (fun t ht => by
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, hsmulT]
      exact (hmem𝔓 t).mp ht)
  have he_mk : ∀ t : T, e (Ideal.Quotient.mk 𝔓 t) = ρ t x := fun t => rfl
  have he_inj : Function.Injective e := by
    rw [injective_iff_map_eq_zero]
    intro d hd
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective d
    rw [he_mk] at hd
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hmem𝔓 t).mpr hd)
  have he_memL : ∀ d, e d ∈ L := by
    intro d
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective d
    rw [he_mk]
    exact hstab t x hxL
  have he_smul : ∀ (t : T) (d : T ⧸ 𝔓), e (Ideal.Quotient.mk 𝔓 t * d) = ρ t (e d) := by
    intro t d
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective d
    rw [← map_mul, he_mk, he_mk, map_mul]
    rfl

  haveI : Module.Finite ℤ (T ⧸ 𝔓) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ 𝔓).toLinearMap
      (Ideal.Quotient.mkₐ_surjective ℤ 𝔓)
  haveI : IsAddTorsionFree (T ⧸ 𝔓) := by
    refine ⟨fun n hn a b hab => he_inj ?_⟩
    apply IsAddTorsionFree.nsmul_right_injective hn
    simp only [← map_nsmul]
    exact congrArg e hab
  haveI : Module.Free ℤ (T ⧸ 𝔓) := inferInstance

  refine FrobChareqEngine.engine5a ρ χ (Ideal.Quotient.mk 𝔓)
    (Ideal.Quotient.lift 𝔓 χ fun t ht => h𝔓le ht) (fun t => Ideal.Quotient.lift_mk 𝔓 χ _)
    e.toAddMonoidHom (fun t d => he_smul t d) ?_
  intro n d hd
  have h1 : LinearIndependent ℤ (fun i => e (d i)) := by
    have hker : LinearMap.ker (e.restrictScalars ℤ) = ⊥ := LinearMap.ker_eq_bot.mpr he_inj
    exact hd.map' (e.restrictScalars ℤ) hker
  exact hfree n _ (fun i => he_memL _) h1

end S_Module_End_exists_ne_zero_forall_apply_eq_smul_of_ringHom
end P2MW
export P2MW.S_Module_End_exists_ne_zero_forall_apply_eq_smul_of_ringHom (solution)
