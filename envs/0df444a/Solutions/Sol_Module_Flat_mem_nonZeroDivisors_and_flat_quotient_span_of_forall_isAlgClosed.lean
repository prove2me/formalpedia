-- Prove2me | solution 1 for Module.Flat.mem_nonZeroDivisors_and_flat_quotient_span_of_forall_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/e2166cfb-455c-5fcb-b45d-527bf201d82e

import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Flat_mem_nonZeroDivisors_and_flat_quotient_span_of_forall_isAlgClosed

set_option autoImplicit false

universe u v w x

open IsLocalRing TensorProduct nonZeroDivisors

namespace ZDFlatCA

variable {R : Type*} [CommRing R]
variable {N M : Type*} [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M]

theorem lTensor_injective_of_isTorsionBySet [IsLocalRing R] (u : N →ₗ[R] M)
    (hu : Function.Injective (u.lTensor (ResidueField R)))
    (V : Type*) [AddCommGroup V] [Module R V]
    (hV : Module.IsTorsionBySet R V (maximalIdeal R)) :
    Function.Injective (u.lTensor V) := by
  letI : Module (ResidueField R) V := hV.module
  haveI : IsScalarTower R (ResidueField R) V := hV.isScalarTower
  have key := AlgebraTensorModule.lTensor_comp_cancelBaseChange R (ResidueField R)
    (ResidueField R) (M := V) u
  have hinner : Function.Injective
      (AlgebraTensorModule.lTensor (ResidueField R) (ResidueField R) u) := by
    rw [AlgebraTensorModule.coe_lTensor]; exact hu
  have h2 : Function.Injective (AlgebraTensorModule.lTensor (ResidueField R) V
      (AlgebraTensorModule.lTensor (ResidueField R) (ResidueField R) u)) := by
    rw [AlgebraTensorModule.coe_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hinner
  have h3 : Function.Injective
      ((AlgebraTensorModule.lTensor (ResidueField R) V u) ∘
        (AlgebraTensorModule.cancelBaseChange R (ResidueField R) (ResidueField R) V N)) := by
    have hfun : ⇑(AlgebraTensorModule.lTensor (ResidueField R) V u) ∘
        ⇑(AlgebraTensorModule.cancelBaseChange R (ResidueField R) (ResidueField R) V N) =
        ⇑(AlgebraTensorModule.cancelBaseChange R (ResidueField R) (ResidueField R) V M) ∘
        ⇑(AlgebraTensorModule.lTensor (ResidueField R) V
          (AlgebraTensorModule.lTensor (ResidueField R) (ResidueField R) u)) :=
      funext fun x => LinearMap.congr_fun key x
    rw [hfun]
    exact (AlgebraTensorModule.cancelBaseChange R _ _ V M).injective.comp h2
  have h4 := h3.of_comp_right (AlgebraTensorModule.cancelBaseChange R _ _ V N).surjective
  rwa [AlgebraTensorModule.coe_lTensor] at h4

theorem lTensor_quotient_injective_of_le [Module.Flat R M] (u : N →ₗ[R] M) {J' J : Ideal R}
    (h : J' ≤ J)
    (hA : Function.Injective (u.lTensor (LinearMap.ker (Submodule.factor h))))
    (hJ : Function.Injective (u.lTensor (R ⧸ J))) :
    Function.Injective (u.lTensor (R ⧸ J')) := by
  set p : (R ⧸ J') →ₗ[R] (R ⧸ J) := Submodule.factor h
  set A := LinearMap.ker p
  have top : Function.Exact (A.subtype.rTensor N) (p.rTensor N) :=
    rTensor_exact N p.exact_subtype_ker_map (Submodule.factor_surjective h)
  have bot_inj : Function.Injective (A.subtype.rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ A.injective_subtype
  have sq1 : ∀ x, (u.lTensor (R ⧸ J')) (A.subtype.rTensor N x) =
      A.subtype.rTensor M (u.lTensor A x) := by
    intro x
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      LinearMap.rTensor_comp_lTensor]
  have sq2 : ∀ y, (u.lTensor (R ⧸ J)) (p.rTensor N y) = p.rTensor M (u.lTensor (R ⧸ J') y) := by
    intro y
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      LinearMap.rTensor_comp_lTensor]
  rw [injective_iff_map_eq_zero]
  intro b hb
  have h1 : (u.lTensor (R ⧸ J)) (p.rTensor N b) = 0 := by rw [sq2, hb, map_zero]
  have h2 : p.rTensor N b = 0 := hJ (by rw [h1, map_zero])
  obtain ⟨a, rfl⟩ := (top b).mp h2
  have h3 : A.subtype.rTensor M (u.lTensor A a) = 0 := by rw [← sq1]; exact hb
  have h4 : u.lTensor A a = 0 := bot_inj (by rw [h3, map_zero])
  have h5 : a = 0 := hA (by rw [h4, map_zero])
  rw [h5, map_zero]

theorem isTorsionBySet_quotient {K s : Ideal R} (h : s ≤ K) :
    Module.IsTorsionBySet R (R ⧸ K) s := by
  rintro x ⟨a, ha⟩
  induction x using Submodule.Quotient.induction_on with
  | H r =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact K.mul_mem_right r (h ha)

theorem isTorsionBySet_ker_factor {J' J : Ideal R} (h : J' ≤ J) {s : Ideal R} (hs : s * J ≤ J') :
    Module.IsTorsionBySet R (LinearMap.ker (Submodule.factor h)) s := by
  rintro ⟨x, hx⟩ ⟨a, ha⟩
  induction x using Submodule.Quotient.induction_on with
  | H r =>
    rw [LinearMap.mem_ker, Submodule.factor, Submodule.mapQ_apply, LinearMap.id_apply,
      Submodule.Quotient.mk_eq_zero] at hx
    apply Subtype.ext
    change (a : R) • Submodule.Quotient.mk r = (0 : R ⧸ J')
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hs (Ideal.mul_mem_mul ha hx)

theorem lTensor_quotient_sup_pow_injective [IsLocalRing R] [Module.Flat R M] (u : N →ₗ[R] M)
    (hu : Function.Injective (u.lTensor (ResidueField R))) (I : Ideal R) (n : ℕ) :
    Function.Injective (u.lTensor (R ⧸ (I ⊔ maximalIdeal R ^ n))) := by
  induction n with
  | zero =>
    apply lTensor_injective_of_isTorsionBySet u hu
    apply isTorsionBySet_quotient
    exact le_sup_of_le_right (by simp)
  | succ n ih =>
    have hle : I ⊔ maximalIdeal R ^ (n + 1) ≤ I ⊔ maximalIdeal R ^ n :=
      sup_le_sup_left (Ideal.pow_le_pow_right n.le_succ) I
    refine lTensor_quotient_injective_of_le u hle ?_ ih
    apply lTensor_injective_of_isTorsionBySet u hu
    apply isTorsionBySet_ker_factor hle
    rw [Ideal.mul_sup, pow_succ']
    exact sup_le_sup_right Ideal.mul_le_right _

theorem lTensor_quotient_injective_iff (u : N →ₗ[R] M) (J : Ideal R) :
    Function.Injective (u.lTensor (R ⧸ J)) ↔
      ∀ x, u x ∈ J • (⊤ : Submodule R M) → x ∈ J • (⊤ : Submodule R N) := by
  constructor
  · intro h x hx
    have h1 : quotTensorEquivQuotSMul M J (u.lTensor (R ⧸ J) ((1 : R ⧸ J) ⊗ₜ[R] x)) = 0 := by
      rw [LinearMap.lTensor_tmul, quotTensorEquivQuotSMul_mk_one_tmul]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hx
    rw [LinearEquiv.map_eq_zero_iff] at h1
    have h3 : (1 : R ⧸ J) ⊗ₜ[R] x = 0 := h (by rw [h1, map_zero])
    have h4 := congrArg (quotTensorEquivQuotSMul N J) h3
    rwa [quotTensorEquivQuotSMul_mk_one_tmul, map_zero, Submodule.Quotient.mk_eq_zero] at h4
  · intro h
    rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective (J • (⊤ : Submodule R N))
      (quotTensorEquivQuotSMul N J t)
    have ht' : t = (1 : R ⧸ J) ⊗ₜ[R] x := by
      rw [← (quotTensorEquivQuotSMul N J).symm_apply_apply t, ← hx,
        quotTensorEquivQuotSMul_symm_mk]
    rw [ht', LinearMap.lTensor_tmul] at ht
    have h1 := congrArg (quotTensorEquivQuotSMul M J) ht
    rw [quotTensorEquivQuotSMul_mk_one_tmul, map_zero, Submodule.Quotient.mk_eq_zero] at h1
    have h2 : Submodule.Quotient.mk (p := J • (⊤ : Submodule R N)) x = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (h x h1)
    rw [ht', ← quotTensorEquivQuotSMul_symm_mk, h2, map_zero]

theorem mem_smul_top_of_forall_mem_sup_pow_smul
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
    [Module S N] [IsScalarTower R S N] [Module.Finite S N] (I : Ideal R) (x : N)
    (hx : ∀ n : ℕ, x ∈ (I ⊔ maximalIdeal R ^ n) • (⊤ : Submodule R N)) :
    x ∈ I • (⊤ : Submodule R N) := by
  set K : Submodule S N := I.map (algebraMap R S) • ⊤ with hKdef
  have hK : K.restrictScalars R = I • ⊤ := by
    rw [hKdef, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
  set mS : Ideal S := (maximalIdeal R).map (algebraMap R S) with hmSdef
  have hmS : mS ≠ ⊤ := fun htop =>
    (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (htop ▸ map_maximalIdeal_le (algebraMap R S)))
  have krull : (⨅ i : ℕ, mS ^ i • ⊤ : Submodule S (N ⧸ K)) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_isLocalRing mS hmS
  let π : N →ₗ[R] N ⧸ K := (K.mkQ).restrictScalars R
  have hπx : ∀ n, π x ∈ (mS ^ n • ⊤ : Submodule S (N ⧸ K)).restrictScalars R := by
    intro n
    rw [hmSdef, ← Ideal.map_pow, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
    have hn := hx n
    rw [Submodule.sup_smul] at hn
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hn
    rw [map_add]
    have hy0 : π y = 0 := by
      rw [← hK] at hy
      exact (Submodule.Quotient.mk_eq_zero K).mpr hy
    rw [hy0, zero_add]
    have hz' : π z ∈ Submodule.map π (maximalIdeal R ^ n • ⊤) := Submodule.mem_map_of_mem hz
    rw [Submodule.map_smul''] at hz'
    exact Submodule.smul_mono le_rfl le_top hz'
  have hπ0 : π x = 0 := by
    have hmem : π x ∈ (⨅ i : ℕ, mS ^ i • ⊤ : Submodule S (N ⧸ K)) :=
      (Submodule.mem_iInf _).mpr fun n => hπx n
    rwa [krull, Submodule.mem_bot] at hmem
  have hxK : x ∈ K := (Submodule.Quotient.mk_eq_zero K).mp hπ0
  rw [← hK]
  exact hxK

theorem lTensor_quotient_injective
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
    [Module S N] [IsScalarTower R S N] [Module.Finite S N] [Module.Flat R M] (u : N →ₗ[R] M)
    (hu : ∀ x, u x ∈ maximalIdeal R • (⊤ : Submodule R M) →
      x ∈ maximalIdeal R • (⊤ : Submodule R N))
    (I : Ideal R) : Function.Injective (u.lTensor (R ⧸ I)) := by
  have hκ : Function.Injective (u.lTensor (ResidueField R)) :=
    (lTensor_quotient_injective_iff u (maximalIdeal R)).mpr hu
  rw [lTensor_quotient_injective_iff]
  intro x hx
  apply mem_smul_top_of_forall_mem_sup_pow_smul S I x
  intro n
  exact (lTensor_quotient_injective_iff u _).mp (lTensor_quotient_sup_pow_injective u hκ I n) x
    (Submodule.smul_mono_left le_sup_left hx)

theorem injective_and_flat_quotient_range
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
    [Module S N] [IsScalarTower R S N] [Module.Finite S N] [Module.Flat R M] (u : N →ₗ[R] M)
    (hu : ∀ x, u x ∈ maximalIdeal R • (⊤ : Submodule R M) →
      x ∈ maximalIdeal R • (⊤ : Submodule R N)) :
    Function.Injective u ∧ Module.Flat R (M ⧸ LinearMap.range u) := by
  have H : ∀ I : Ideal R, Function.Injective (u.lTensor (R ⧸ I)) :=
    lTensor_quotient_injective S u hu
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h := (lTensor_quotient_injective_iff u ⊥).mp (H ⊥) x (by rw [hx]; exact zero_mem _)
    rwa [Submodule.bot_smul, Submodule.mem_bot] at h
  · rw [Module.Flat.iff_lTensor_injective']
    intro I
    exact lTensor_injective_of_exact_of_exact_of_rTensor_injective
      (f₁ := u) (f₂ := (LinearMap.range u).mkQ) (g₁ := Submodule.subtype I) (g₂ := Submodule.mkQ I)
      (LinearMap.exact_map_mkQ_range u) (Submodule.mkQ_surjective _)
      (LinearMap.exact_subtype_mkQ I) (Submodule.mkQ_surjective I)
      ((LinearMap.lTensor_inj_iff_rTensor_inj (R ⧸ I) u).mp (H I))
      (Module.Flat.lTensor_preserves_injective_linearMap _ I.injective_subtype)

end ZDFlatCA

namespace ZDFlatCA

theorem stacks00MF
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [IsNoetherianRing S] [Module.Flat R S] (f : S)
    (hf : Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) f ∈
      nonZeroDivisors (S ⧸ (maximalIdeal R).map (algebraMap R S))) :
    f ∈ nonZeroDivisors S ∧ Module.Flat R (S ⧸ Ideal.span {f}) := by
  let u : S →ₗ[R] S := LinearMap.mulLeft R f
  have hu : ∀ x : S, u x ∈ maximalIdeal R • (⊤ : Submodule R S) →
      x ∈ maximalIdeal R • (⊤ : Submodule R S) := by
    intro x hx
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, ← Ideal.Quotient.eq_zero_iff_mem]
      at hx ⊢
    rw [LinearMap.mulLeft_apply, map_mul] at hx
    exact (mem_nonZeroDivisors_iff_left.mp hf) _ hx
  obtain ⟨hinj, hflat⟩ := injective_and_flat_quotient_range S u hu
  refine ⟨?_, ?_⟩
  · rw [mem_nonZeroDivisors_iff_left]
    intro x hx
    exact hinj (by rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, hx, mul_zero])
  · have hrange : LinearMap.range u = (Ideal.span {f}).restrictScalars R := by
      ext x
      simp only [LinearMap.mem_range, Submodule.restrictScalars_mem, Ideal.mem_span_singleton']
      constructor
      · rintro ⟨y, rfl⟩; exact ⟨y, mul_comm y f⟩
      · rintro ⟨y, rfl⟩; exact ⟨y, mul_comm f y⟩
    exact Module.Flat.of_linearEquiv
      ((Submodule.quotEquivOfEq _ _ hrange).trans
        (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {f}))).symm

section Fiber

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : Ideal A) [p.IsPrime]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open Algebra.TensorProduct in

noncomputable def fiberEquivQuotient :
    letI Rp := Localization p.primeCompl
    letI pRp := IsLocalRing.maximalIdeal Rp
    letI Sp := Localization (Algebra.algebraMapSubmonoid B p.primeCompl)
    letI pSp := pRp.map (algebraMap Rp Sp)
    p.Fiber B ≃ₐ[B] Sp ⧸ pSp :=
  (commRight A B p.ResidueField).symm.trans <| (tensorQuotientEquiv B _ B _).trans <|
    { __ := Ideal.quotientEquiv _ _ (Localization.tensorLeftAlgEquiv p.primeCompl B) (by
        rw [← Ideal.map_coe includeRight, Ideal.map_map]
        congr
        ext
        simp [Localization.tensorLeftAlgEquiv_apply_one_tmul p.primeCompl])
      commutes' := by simp }

theorem exists_smul_mem_of_one_tmul_eq_zero (b : B)
    (h : ((1 : p.ResidueField) ⊗ₜ[A] b : p.Fiber B) = 0) :
    ∃ a ∉ p, a • b ∈ p.map (algebraMap A B) := by
  let Sp := Localization (Algebra.algebraMapSubmonoid B p.primeCompl)
  have h1 : algebraMap B (Sp ⧸ (IsLocalRing.maximalIdeal (Localization p.primeCompl)).map
      (algebraMap (Localization p.primeCompl) Sp)) b = 0 := by
    rw [← (fiberEquivQuotient (B := B) p).commutes b]
    change fiberEquivQuotient (B := B) p ((1 : p.ResidueField) ⊗ₜ[A] b) = 0
    rw [h, map_zero]
  rw [IsScalarTower.algebraMap_apply B Sp (Sp ⧸ _), Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A B Sp, ← Ideal.map_map,
    IsLocalization.algebraMap_mem_map_algebraMap_iff (Algebra.algebraMapSubmonoid B p.primeCompl) Sp]
    at h1
  obtain ⟨m, hm, hmb⟩ := h1
  obtain ⟨a, ha, rfl⟩ := Submonoid.mem_map.mp hm
  exact ⟨a, ha, by rwa [Algebra.smul_def]⟩

end Fiber

theorem exists_smul_mem_of_mul_mem {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (g : B)
    (hg : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra A K],
      (g ⊗ₜ[A] (1 : K)) ∈ nonZeroDivisors (B ⊗[A] K))
    (p : Ideal A) [p.IsPrime] (b : B) (hb : g * b ∈ p.map (algebraMap A B)) :
    ∃ a ∉ p, a • b ∈ p.map (algebraMap A B) := by
  let κ := p.ResidueField
  let K := AlgebraicClosure κ

  have h0 : ∀ x ∈ p.map (algebraMap A B), (x ⊗ₜ[A] (1 : K) : B ⊗[A] K) = 0 := by
    intro x hx
    rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map] at hx
    refine Submodule.smul_induction_on (p := fun x => (x ⊗ₜ[A] (1 : K) : B ⊗[A] K) = 0) hx
      ?_ ?_
    · intro a ha y _
      rw [smul_tmul, Algebra.smul_def, mul_one, IsScalarTower.algebraMap_apply A κ K,
        (Ideal.algebraMap_residueField_eq_zero).mpr ha, map_zero, tmul_zero]
    · intro y z hy hz
      rw [add_tmul, hy, hz, add_zero]
  have h1 : (b ⊗ₜ[A] (1 : K) : B ⊗[A] K) = 0 := by
    apply (mem_nonZeroDivisors_iff_left.mp (hg K)) _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    exact h0 _ hb

  have hinj : Function.Injective (((Algebra.linearMap κ K).restrictScalars A).lTensor B) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (algebraMap κ K).injective
  have h2 : (b ⊗ₜ[A] (1 : κ) : B ⊗[A] κ) = 0 := hinj (by
    rw [LinearMap.lTensor_tmul, map_zero, LinearMap.restrictScalars_apply, Algebra.linearMap_apply,
      map_one]
    exact h1)

  have h3 : ((1 : κ) ⊗ₜ[A] b : p.Fiber B) = 0 := by
    have := congrArg (TensorProduct.comm A B κ) h2
    rwa [TensorProduct.comm_tmul, map_zero] at this
  exact exists_smul_mem_of_one_tmul_eq_zero p b h3

theorem localization_regular_and_flat {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing B] [Module.Flat A B] (g : B)
    (H : ∀ (p : Ideal A) [p.IsPrime] (b : B), g * b ∈ p.map (algebraMap A B) →
      ∃ a ∉ p, a • b ∈ p.map (algebraMap A B))
    (q : Ideal B) [q.IsPrime] :
    algebraMap B (Localization.AtPrime q) g ∈ (Localization.AtPrime q)⁰ ∧
      Module.Flat A (Localization.AtPrime q ⧸
        Ideal.span {algebraMap B (Localization.AtPrime q) g}) := by
  by_cases hgq : g ∈ q
  · let p := q.under A
    letI := Localization.AtPrime.algebraOfLiesOver p q
    haveI : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
      rw [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq (p := p) (P := q)]
      infer_instance
    have hfib : Ideal.Quotient.mk ((maximalIdeal (Localization.AtPrime p)).map
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)))
        (algebraMap B (Localization.AtPrime q) g) ∈
        (Localization.AtPrime q ⧸ (maximalIdeal (Localization.AtPrime p)).map
          (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)))⁰ := by
      have hmS : (maximalIdeal (Localization.AtPrime p)).map
          (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) =
          (p.map (algebraMap A B)).map (algebraMap B (Localization.AtPrime q)) := by
        rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map,
          ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
      rw [mem_nonZeroDivisors_iff_left]
      intro y hy
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, hmS] at hy
      rw [Ideal.Quotient.eq_zero_iff_mem, hmS]
      obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl y
      rw [IsLocalization.mul_mk'_eq_mk'_of_mul] at hy
      obtain ⟨m, hm, hmb⟩ :=
        (IsLocalization.mk'_mem_map_algebraMap_iff q.primeCompl (Localization.AtPrime q) _ _ _).mp hy
      obtain ⟨a, hap, hab⟩ := H p (m * b) (by rw [mul_left_comm]; exact hmb)
      refine (IsLocalization.mk'_mem_map_algebraMap_iff q.primeCompl (Localization.AtPrime q)
        _ _ _).mpr ⟨algebraMap A B a * m, q.primeCompl.mul_mem ?_ hm, ?_⟩
      · exact fun h => hap (Ideal.mem_comap.mpr h)
      · rw [mul_assoc, ← Algebra.smul_def]; exact hab
    obtain ⟨hreg, hflat⟩ := stacks00MF (R := Localization.AtPrime p) (S := Localization.AtPrime q)
      (algebraMap B (Localization.AtPrime q) g) hfib
    refine ⟨hreg, ?_⟩
    haveI : Module.Flat A (Localization.AtPrime p) := IsLocalization.flat _ p.primeCompl
    haveI := hflat
    exact Module.Flat.trans A (Localization.AtPrime p) _
  · have hu : IsUnit (algebraMap B (Localization.AtPrime q) g) := IsLocalization.map_units (Localization.AtPrime q) (⟨g, show g ∈ q.primeCompl from hgq⟩ : q.primeCompl)
    refine ⟨hu.mem_nonZeroDivisors, ?_⟩
    haveI : Subsingleton (Localization.AtPrime q ⧸
        Ideal.span {algebraMap B (Localization.AtPrime q) g}) :=
      Ideal.Quotient.subsingleton_iff.mpr ((Ideal.span_singleton_eq_top).mpr hu)
    infer_instance

theorem mem_nonZeroDivisors_and_flat_quotient {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] [IsNoetherianRing B] [Module.Flat A B] (g : B)
    (hg : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra A K],
      (g ⊗ₜ[A] (1 : K)) ∈ nonZeroDivisors (B ⊗[A] K)) :
    g ∈ nonZeroDivisors B ∧ Module.Flat A (B ⧸ Ideal.span {g}) := by
  have loc := fun (q : Ideal B) (hq : q.IsPrime) =>
    localization_regular_and_flat g (fun p _ b hb => exists_smul_mem_of_mul_mem g hg p b hb) q
  refine ⟨?_, ?_⟩
  · rw [mem_nonZeroDivisors_iff_left]
    intro b hb
    apply eq_zero_of_localization
    intro J hJ
    exact (mem_nonZeroDivisors_iff_left.mp (loc J inferInstance).1) _
      (by rw [← map_mul, hb, map_zero])
  · let I : Ideal B := Ideal.span {g}
    let Mq := fun (J : Ideal B) [J.IsMaximal] =>
      Localization.AtPrime J ⧸ I.map (algebraMap B (Localization.AtPrime J))
    let f := fun (J : Ideal B) [J.IsMaximal] =>
      (IsScalarTower.toAlgHom B (B ⧸ I) (Mq J)).toLinearMap
    haveI : ∀ (J : Ideal B) [J.IsMaximal], IsLocalizedModule.AtPrime J (f J) := fun J _ =>
      isLocalizedModule_iff_isLocalization.mpr inferInstance
    refine Module.flat_of_isLocalized_maximal B (B ⧸ I) Mq f fun J _ => ?_
    have hIJ : I.map (algebraMap B (Localization.AtPrime J)) =
        Ideal.span {algebraMap B (Localization.AtPrime J) g} := by
      rw [Ideal.map_span, Set.image_singleton]
    haveI := (loc J inferInstance).2
    exact Module.Flat.of_linearEquiv
      (Ideal.quotientEquivAlgOfEq A hIJ).toLinearEquiv

end ZDFlatCA

theorem solution
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing B]
    [Module.Flat A B] (g : B)
    (hg : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra A K],
      (g ⊗ₜ[A] (1 : K)) ∈ nonZeroDivisors (B ⊗[A] K)) :
    g ∈ nonZeroDivisors B ∧ Module.Flat A (B ⧸ Ideal.span {g}) := by
  exact ZDFlatCA.mem_nonZeroDivisors_and_flat_quotient g hg

end S_Module_Flat_mem_nonZeroDivisors_and_flat_quotient_span_of_forall_isAlgClosed
end P2MW
export P2MW.S_Module_Flat_mem_nonZeroDivisors_and_flat_quotient_span_of_forall_isAlgClosed (solution)
