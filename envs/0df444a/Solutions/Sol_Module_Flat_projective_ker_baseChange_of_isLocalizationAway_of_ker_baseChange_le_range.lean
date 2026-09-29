-- Prove2me | solution 1 for Module.Flat.projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/2ca8e772-79d4-5c53-b618-c0bfcad5f454

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Theorems.Thm_Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Flat_projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range

set_option autoImplicit false

universe u uR uT uM

open TensorProduct

namespace B2SOL

section Transport

variable {A : Type*} [Semiring A]
  {M₀ M₁ M₂ N₀ N₁ N₂ : Type*}
  [AddCommMonoid M₀] [AddCommMonoid M₁] [AddCommMonoid M₂]
  [AddCommMonoid N₀] [AddCommMonoid N₁] [AddCommMonoid N₂]
  [Module A M₀] [Module A M₁] [Module A M₂] [Module A N₀] [Module A N₁] [Module A N₂]

theorem ker_le_range_transport (e₀ : M₀ ≃ₗ[A] N₀) (e₁ : M₁ ≃ₗ[A] N₁) (e₂ : M₂ ≃ₗ[A] N₂)
    (u : M₀ →ₗ[A] M₁) (v : M₁ →ₗ[A] M₂) (u' : N₀ →ₗ[A] N₁) (v' : N₁ →ₗ[A] N₂)
    (h₀ : ∀ x, e₁ (u x) = u' (e₀ x)) (h₁ : ∀ y, e₂ (v y) = v' (e₁ y))
    (hex : LinearMap.ker v ≤ LinearMap.range u) :
    LinearMap.ker v' ≤ LinearMap.range u' := by
  intro y' hy'
  rw [LinearMap.mem_ker] at hy'
  obtain ⟨y, rfl⟩ := e₁.surjective y'
  have hy : y ∈ LinearMap.ker v := by
    rw [LinearMap.mem_ker, ← e₂.map_eq_zero_iff, h₁, hy']
  obtain ⟨x, hx⟩ := hex hy
  exact ⟨e₀ x, by rw [← h₀, hx]⟩

end Transport

section Cancel

variable (R : Type*) (S : Type*) (B : Type*) [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem cancelBaseChange_baseChange_baseChange (f : M →ₗ[R] N) (x : B ⊗[S] (S ⊗[R] M)) :
    AlgebraTensorModule.cancelBaseChange R S B B N (((f.baseChange S).baseChange B) x) =
      (f.baseChange B) (AlgebraTensorModule.cancelBaseChange R S B B M x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul s m =>
      simp [LinearMap.baseChange_tmul, AlgebraTensorModule.cancelBaseChange_tmul]
    | add y₁ y₂ h₁ h₂ => simp only [tmul_add, map_add, h₁, h₂]
  | add x₁ x₂ h₁ h₂ => simp only [map_add, h₁, h₂]

end Cancel

section FlatKer

variable {R : Type uR} [CommRing R] (T : Type uT) [CommRing T] [Algebra R T] [Module.Flat R T]
  {M N : Type uM} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem baseChange_subtype_injective (f : M →ₗ[R] N) :
    Function.Injective ((LinearMap.ker f).subtype.baseChange T) := by
  intro x y h
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := T)
    (LinearMap.ker f).subtype (LinearMap.ker f).injective_subtype
  exact hinj h

theorem exists_baseChange_subtype_eq (f : M →ₗ[R] N) (y : T ⊗[R] M)
    (hy : f.baseChange T y = 0) :
    ∃ x : T ⊗[R] LinearMap.ker f, (LinearMap.ker f).subtype.baseChange T x = y := by
  have h := Module.Flat.lTensor_exact T (LinearMap.exact_subtype_ker_map f)
  exact (h y).mp hy

theorem kerBaseChangeHom_bijective (f : M →ₗ[R] N) :
    Function.Bijective (TwoChartCech.kerBaseChangeHom f T) := by
  constructor
  · intro x y h
    apply baseChange_subtype_injective T f
    rw [← TwoChartCech.kerBaseChangeHom_apply_coe, ← TwoChartCech.kerBaseChangeHom_apply_coe, h]
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := exists_baseChange_subtype_eq T f y hy
    exact ⟨x, Subtype.ext (by rw [TwoChartCech.kerBaseChangeHom_apply_coe, hx])⟩

noncomputable def kerEquiv (f : M →ₗ[R] N) :
    T ⊗[R] LinearMap.ker f ≃ₗ[T] LinearMap.ker (f.baseChange T) :=
  LinearEquiv.ofBijective _ (kerBaseChangeHom_bijective T f)

@[scoped simp] theorem kerEquiv_apply_coe (f : M →ₗ[R] N) (x : T ⊗[R] LinearMap.ker f) :
    (kerEquiv T f x : T ⊗[R] M) = (LinearMap.ker f).subtype.baseChange T x := by
  simp [kerEquiv, TwoChartCech.kerBaseChangeHom_apply_coe]

end FlatKer

section Key

variable (R : Type uR) (S : Type uR) (B : Type uT) [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B] [Module.Flat R S]
  {M N : Type uM} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem key (f : M →ₗ[R] N) (w : B ⊗[S] (S ⊗[R] LinearMap.ker f)) :
    ((LinearMap.ker f).subtype.baseChange B)
        (AlgebraTensorModule.cancelBaseChange R S B B (LinearMap.ker f) w) =
      AlgebraTensorModule.cancelBaseChange R S B B M
        ↑(TwoChartCech.kerBaseChangeHom (f.baseChange S) B
          (LinearEquiv.baseChange S B _ _ (kerEquiv S f) w)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul b t =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s k =>
      simp [LinearEquiv.baseChange_tmul, TwoChartCech.kerBaseChangeHom_apply_coe,
        LinearMap.baseChange_tmul, AlgebraTensorModule.cancelBaseChange_tmul]
    | add t₁ t₂ h₁ h₂ => simp only [tmul_add, map_add, Submodule.coe_add, h₁, h₂]
  | add w₁ w₂ h₁ h₂ => simp only [map_add, Submodule.coe_add, h₁, h₂]

end Key

theorem subsingleton_tensor {R : Type*} [CommRing R] (T : Type*) [CommRing T] [Algebra R T]
    (M : Type*) [AddCommGroup M] [Module R M] [Subsingleton M] : Subsingleton (T ⊗[R] M) := by
  refine ⟨fun x y => ?_⟩
  have h : ∀ z : T ⊗[R] M, z = 0 := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul t m => rw [Subsingleton.elim m 0, tmul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  rw [h x, h y]

end B2SOL
p2m_reactivate "P2MW.S_Module_Flat_projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range.B2SOL"

open B2SOL in

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (g : R) (S : Type u) [CommRing S] [Algebra R S] [IsLocalization.Away g S]
    (hex : ∀ i : ℕ, LinearMap.ker ((d (i + 1)).baseChange S) ≤ LinearMap.range ((d i).baseChange S))
    (A : Type u) [CommRing A] [Algebra R A] (hA : IsUnit (algebraMap R A g)) :
    Module.Finite A (LinearMap.ker ((d 0).baseChange A)) ∧
      Module.Projective A (LinearMap.ker ((d 0).baseChange A)) ∧
      (∀ i : ℕ, LinearMap.ker ((d (i + 1)).baseChange A) ≤ LinearMap.range ((d i).baseChange A)) ∧
      Function.Bijective (TwoChartCech.kerBaseChangeHom (d 0) A) := by
  classical

  haveI : Module.Flat R S := IsLocalization.flat S (Submonoid.powers g)
  haveI : IsNoetherianRing S :=
    IsLocalization.isNoetherianRing (Submonoid.powers g) S inferInstance
  letI : Algebra S A := (IsLocalization.Away.lift g (g := algebraMap R A) hA).toAlgebra
  haveI : IsScalarTower R S A :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (IsLocalization.Away.lift_eq g (g := algebraMap R A) hA x).symm

  have hdd' : ∀ i, (d (i + 1)).baseChange S ∘ₗ (d i).baseChange S = 0 := fun i => by
    rw [← LinearMap.baseChange_comp, hdd, LinearMap.baseChange_zero]
  have hbd' : ∀ i, n ≤ i → Subsingleton (S ⊗[R] C i) := fun i hi => by
    haveI := hbd i hi
    exact subsingleton_tensor S (C i)
  obtain ⟨hflat', hbij', hex'⟩ :=
    Module.Flat.flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range (R := S)
      (fun i => S ⊗[R] C i) (fun i => (d i).baseChange S) hdd' n hbd' hex

  have hexA : ∀ i : ℕ,
      LinearMap.ker ((d (i + 1)).baseChange A) ≤ LinearMap.range ((d i).baseChange A) :=
    fun i => ker_le_range_transport
      (AlgebraTensorModule.cancelBaseChange R S A A (C i))
      (AlgebraTensorModule.cancelBaseChange R S A A (C (i + 1)))
      (AlgebraTensorModule.cancelBaseChange R S A A (C (i + 1 + 1)))
      (((d i).baseChange S).baseChange A) (((d (i + 1)).baseChange S).baseChange A)
      ((d i).baseChange A) ((d (i + 1)).baseChange A)
      (cancelBaseChange_baseChange_baseChange R S A (d i))
      (cancelBaseChange_baseChange_baseChange R S A (d (i + 1))) (hex' A i)

  have hψ : Function.Bijective (TwoChartCech.kerBaseChangeHom ((d 0).baseChange S) A) := hbij' A
  have hbijA : Function.Bijective (TwoChartCech.kerBaseChangeHom (d 0) A) := by
    constructor
    · intro x y hxy
      obtain ⟨wx, rfl⟩ :=
        (AlgebraTensorModule.cancelBaseChange R S A A (LinearMap.ker (d 0))).surjective x
      obtain ⟨wy, rfl⟩ :=
        (AlgebraTensorModule.cancelBaseChange R S A A (LinearMap.ker (d 0))).surjective y
      have h1 := congrArg Subtype.val hxy
      rw [TwoChartCech.kerBaseChangeHom_apply_coe, TwoChartCech.kerBaseChangeHom_apply_coe,
        key R S A (d 0), key R S A (d 0)] at h1
      have h2 := hψ.1 (Subtype.val_injective
        ((AlgebraTensorModule.cancelBaseChange R S A A (C 0)).injective h1))
      rw [(LinearEquiv.baseChange S A _ _ (kerEquiv S (d 0))).injective h2]
    · rintro ⟨y, hy⟩
      obtain ⟨y₁, rfl⟩ := (AlgebraTensorModule.cancelBaseChange R S A A (C 0)).surjective y
      have hy₁ : ((d 0).baseChange S).baseChange A y₁ = 0 := by
        rw [LinearMap.mem_ker, ← cancelBaseChange_baseChange_baseChange R S A (d 0) y₁,
          LinearEquiv.map_eq_zero_iff] at hy
        exact hy
      obtain ⟨z, hz⟩ := hψ.2 ⟨y₁, hy₁⟩
      obtain ⟨w, rfl⟩ := (LinearEquiv.baseChange S A _ _ (kerEquiv S (d 0))).surjective z
      refine ⟨AlgebraTensorModule.cancelBaseChange R S A A (LinearMap.ker (d 0)) w, Subtype.ext ?_⟩
      rw [TwoChartCech.kerBaseChangeHom_apply_coe, key R S A (d 0), hz]

  have hfinA : Module.Finite A (LinearMap.ker ((d 0).baseChange A)) := by
    haveI := hfin0
    exact Module.Finite.equiv (LinearEquiv.ofBijective (TwoChartCech.kerBaseChangeHom (d 0) A) hbijA)
  have hprojS : Module.Projective S (LinearMap.ker ((d 0).baseChange S)) := by
    haveI : Module.Flat S (LinearMap.ker ((d 0).baseChange S)) := hflat'
    haveI : Module.Finite S (S ⊗[R] LinearMap.ker (d 0)) := by
      haveI := hfin0
      infer_instance
    haveI : Module.Finite S (LinearMap.ker ((d 0).baseChange S)) :=
      Module.Finite.of_surjective (TwoChartCech.kerBaseChangeHom (d 0) S)
        (kerBaseChangeHom_bijective S (d 0)).2
    haveI := Module.finitePresentation_of_finite S (LinearMap.ker ((d 0).baseChange S))
    exact Module.Flat.projective_of_finitePresentation (R := S)
      (M := LinearMap.ker ((d 0).baseChange S))
  have hprojA : Module.Projective A (LinearMap.ker ((d 0).baseChange A)) := by
    haveI := hprojS
    haveI : Module.Projective A (A ⊗[S] LinearMap.ker ((d 0).baseChange S)) :=
      Module.Projective.tensorProduct
    exact Module.Projective.of_equiv
      (((LinearEquiv.baseChange S A _ _ (kerEquiv S (d 0))).symm.trans
        (AlgebraTensorModule.cancelBaseChange R S A A (LinearMap.ker (d 0)))).trans
        (LinearEquiv.ofBijective (TwoChartCech.kerBaseChangeHom (d 0) A) hbijA))
  exact ⟨hfinA, hprojA, hexA, hbijA⟩

end S_Module_Flat_projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range
end P2MW
export P2MW.S_Module_Flat_projective_ker_baseChange_of_isLocalizationAway_of_ker_baseChange_le_range (solution)
