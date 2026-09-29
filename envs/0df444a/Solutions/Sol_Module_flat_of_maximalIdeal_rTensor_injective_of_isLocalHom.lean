-- Prove2me | solution 1 for Module.flat_of_maximalIdeal_rTensor_injective_of_isLocalHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/770117af-4a19-58f3-a8b7-3293e77a856e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_flat_of_maximalIdeal_rTensor_injective_of_isLocalHom

set_option autoImplicit false

open TensorProduct IsLocalRing

universe u

namespace LCF

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable (M : Type u) [AddCommGroup M] [Module A M]

theorem inj_subtype_of_le (h𝔪 : Function.Injective (LinearMap.lTensor M (maximalIdeal A).subtype))
    (J : Ideal A) (hJ : maximalIdeal A ≤ J) : Function.Injective (LinearMap.lTensor M J.subtype) := by
  rcases eq_or_ne J ⊤ with rfl | hne
  ·
    have : (⊤ : Submodule A A).subtype = (Submodule.topEquiv : (⊤ : Submodule A A) ≃ₗ[A] A).toLinearMap := rfl
    rw [this]
    exact (Submodule.topEquiv.lTensor M).injective
  · have : J = maximalIdeal A := le_antisymm (IsLocalRing.le_maximalIdeal hne) hJ
    subst this
    exact h𝔪

theorem inj_of_bijective {P Q : Type u} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    (f : P →ₗ[A] Q) (hf : Function.Bijective f) : Function.Injective (LinearMap.lTensor M f) := by
  have : f = (LinearEquiv.ofBijective f hf).toLinearMap := rfl
  rw [this]
  exact ((LinearEquiv.ofBijective f hf).lTensor M).injective

theorem alpha (h𝔪 : Function.Injective (LinearMap.lTensor M (maximalIdeal A).subtype))
    {P : Type u} [AddCommGroup P] [Module A P] (Q Q'' : Submodule A P) (p : P) (hQ : Q ≤ Q'')
    (hQ'' : Q'' = Q ⊔ Submodule.span A {p}) (hp : ∀ a ∈ maximalIdeal A, a • p ∈ Q) :
    Function.Injective (LinearMap.lTensor M (Submodule.inclusion hQ)) := by
  subst hQ''

  let J : Ideal A := Q.comap (LinearMap.toSpanSingleton A P p)
  have hJmem : ∀ a : A, a ∈ J ↔ a • p ∈ Q := fun a => Iff.rfl
  have h𝔪J : maximalIdeal A ≤ J := fun a ha => (hJmem a).2 (hp a ha)

  have hpmem : ∀ a : A, a • p ∈ Q ⊔ Submodule.span A {p} :=
    fun a => Submodule.mem_sup_right (Submodule.smul_mem _ a (Submodule.mem_span_singleton_self p))
  let Φ : (↥Q × A) →ₗ[A] ↥(Q ⊔ Submodule.span A {p}) :=
    LinearMap.coprod (Submodule.inclusion hQ) (LinearMap.codRestrict (Q ⊔ Submodule.span A {p}) (LinearMap.toSpanSingleton A P p) hpmem)
  let j₁ : ↥J →ₗ[A] ↥Q := -(LinearMap.codRestrict Q ((LinearMap.toSpanSingleton A P p).comp J.subtype) (fun a => a.2))
  let ψ : ↥J →ₗ[A] (↥Q × A) := LinearMap.prod j₁ J.subtype
  have hΦsurj : Function.Surjective Φ := by
    rintro ⟨x, hx⟩
    obtain ⟨q, hq, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    exact ⟨(⟨q, hq⟩, a), Subtype.ext rfl⟩
  have hexact : Function.Exact ψ Φ := by
    intro x
    constructor
    · intro hx
      obtain ⟨q, a⟩ := x
      have hx' : (q : P) + a • p = 0 := congrArg Subtype.val hx
      have hap : a • p = -(q : P) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact hx'
      have haJ : a ∈ J := by
        rw [hJmem, hap]
        exact Q.neg_mem q.2
      refine ⟨⟨a, haJ⟩, ?_⟩
      ext
      · change -((a : A) • p) = (q : P)
        rw [hap, neg_neg]
      · rfl
    · rintro ⟨a, rfl⟩
      apply Subtype.ext
      change -((a : A) • p) + (a : A) • p = 0
      abel
  have hexactT := lTensor_exact M hexact hΦsurj

  have hincl : Submodule.inclusion hQ = Φ.comp (LinearMap.inl A ↥Q A) := by
    ext x
    change (x : P) = (x : P) + (0 : A) • p
    rw [zero_smul, add_zero]
  intro x y hxy
  rw [← sub_eq_zero] at hxy ⊢
  rw [← map_sub] at hxy
  set d := x - y with hd
  rw [hincl, LinearMap.lTensor_comp, LinearMap.comp_apply] at hxy
  obtain ⟨z, hz⟩ := (hexactT _).1 hxy

  have h1 : LinearMap.lTensor M J.subtype z = 0 := by
    have : J.subtype = (LinearMap.snd A ↥Q A).comp ψ := by ext a; rfl
    rw [this, LinearMap.lTensor_comp, LinearMap.comp_apply, hz, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      LinearMap.snd_comp_inl, LinearMap.lTensor_zero, LinearMap.zero_apply]
  have hz0 : z = 0 := inj_subtype_of_le M h𝔪 J h𝔪J (by rw [h1, map_zero])
  have h2 : LinearMap.lTensor M (LinearMap.inl A ↥Q A) d = 0 := by rw [← hz, hz0, map_zero]
  have : d = LinearMap.lTensor M ((LinearMap.fst A ↥Q A).comp (LinearMap.inl A ↥Q A)) d := by
    rw [LinearMap.fst_comp_inl, LinearMap.lTensor_id, LinearMap.id_apply]
  rw [this, LinearMap.lTensor_comp, LinearMap.comp_apply, h2, map_zero]

theorem beta (h𝔪 : Function.Injective (LinearMap.lTensor M (maximalIdeal A).subtype))
    {P' P : Type u} [AddCommGroup P'] [Module A P'] [AddCommGroup P] [Module A P] [Module.Finite A P]
    (u : P' →ₗ[A] P) (hu : Function.Injective u)
    (h𝔪P : ∀ a ∈ maximalIdeal A, ∀ x : P, a • x ∈ LinearMap.range u) :
    Function.Injective (LinearMap.lTensor M u) := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Module.Finite A P).fg_top

  have chain : ∀ t : Finset P, Function.Injective
      (LinearMap.lTensor M (Submodule.inclusion (le_sup_left : LinearMap.range u ≤ LinearMap.range u ⊔ Submodule.span A (t : Set P)))) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      apply inj_of_bijective
      refine ⟨Submodule.inclusion_injective _, ?_⟩
      rintro ⟨x, hx⟩
      rw [Finset.coe_empty, Submodule.span_empty, sup_bot_eq] at hx
      exact ⟨⟨x, hx⟩, rfl⟩
    | insert p t hpt ih =>
      have hle : LinearMap.range u ⊔ Submodule.span A (t : Set P) ≤ LinearMap.range u ⊔ Submodule.span A ((insert p t : Finset P) : Set P) :=
        sup_le_sup_left (Submodule.span_mono (by simp)) _
      have heq : LinearMap.range u ⊔ Submodule.span A ((insert p t : Finset P) : Set P) =
          (LinearMap.range u ⊔ Submodule.span A (t : Set P)) ⊔ Submodule.span A {p} := by
        rw [Finset.coe_insert, Submodule.span_insert, sup_assoc, sup_comm (Submodule.span A {p})]
      have hstep := alpha M h𝔪 _ _ p hle heq (fun a ha => Submodule.mem_sup_left (h𝔪P a ha p))
      have hcomp : Submodule.inclusion (le_sup_left : LinearMap.range u ≤ LinearMap.range u ⊔ Submodule.span A ((insert p t : Finset P) : Set P)) =
          (Submodule.inclusion hle).comp (Submodule.inclusion le_sup_left) := by ext x; rfl
      rw [hcomp, LinearMap.lTensor_comp]
      exact hstep.comp ih

  have htop : LinearMap.range u ⊔ Submodule.span A (s : Set P) = ⊤ := by rw [hs, sup_top_eq]
  have hsub : ∀ X : Submodule A P, X = ⊤ → Function.Injective (LinearMap.lTensor M X.subtype) := by
    intro X hX; subst hX
    exact inj_of_bijective M _ ⟨Subtype.val_injective, fun x => ⟨⟨x, trivial⟩, rfl⟩⟩
  let e : P' →ₗ[A] ↥(LinearMap.range u) := LinearMap.codRestrict (LinearMap.range u) u (LinearMap.mem_range_self u)
  have he : Function.Bijective e := ⟨fun x y hxy => hu (congrArg Subtype.val hxy), fun ⟨y, hy⟩ => by
    obtain ⟨x, rfl⟩ := hy; exact ⟨x, rfl⟩⟩
  have hfac : u = ((LinearMap.range u ⊔ Submodule.span A (s : Set P)).subtype.comp (Submodule.inclusion le_sup_left)).comp e := by
    ext x; rfl
  rw [hfac, LinearMap.lTensor_comp, LinearMap.lTensor_comp]
  exact ((hsub _ htop).comp (chain s)).comp (inj_of_bijective M e he)

theorem gamma [IsNoetherianRing A] (h𝔪 : Function.Injective (LinearMap.lTensor M (maximalIdeal A).subtype)) (n : ℕ) :
    ∀ (N : Type u) [AddCommGroup N] [Module A N] [Module.Finite A N],
      (maximalIdeal A) ^ n • (⊤ : Submodule A N) = ⊥ →
      ∀ (N' : Type u) [AddCommGroup N'] [Module A N'] (u : N' →ₗ[A] N), Function.Injective u →
        Function.Injective (LinearMap.lTensor M u) := by
  induction n with
  | zero =>
    intro N _ _ _ hN N' _ _ u hu
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul] at hN
    have hsub : Subsingleton N := subsingleton_of_forall_eq 0 fun x => by
      have : x ∈ (⊤ : Submodule A N) := trivial
      rw [hN] at this; exact this
    have : Subsingleton N' := ⟨fun a b => hu (Subsingleton.elim _ _)⟩
    haveI : Subsingleton (M ⊗[A] N') := inferInstance
    exact fun a b _ => Subsingleton.elim a b
  | succ n ih =>
    intro N _ _ _ hN N' _ _ u hu

    let N₀ : Submodule A N := maximalIdeal A • ⊤
    let N'₀ : Submodule A N' := N₀.comap u
    haveI : IsNoetherian A N := inferInstance
    haveI : Module.Finite A ↥N₀ := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian N₀)
    have hN₀ : (maximalIdeal A) ^ n • (⊤ : Submodule A ↥N₀) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : (x : N) ∈ Submodule.map N₀.subtype ((maximalIdeal A) ^ n • ⊤) := ⟨x, hx, rfl⟩
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] at hx'
      have hEq : (maximalIdeal A) ^ n • N₀ = (maximalIdeal A) ^ (n + 1) • (⊤ : Submodule A N) := by
        rw [show N₀ = maximalIdeal A • ⊤ from rfl, ← Submodule.smul_assoc, Ideal.smul_eq_mul, ← pow_succ]
      rw [hEq, hN, Submodule.mem_bot] at hx'
      rw [Submodule.mem_bot]
      exact Subtype.ext hx'

    let u₀ : ↥N'₀ →ₗ[A] ↥N₀ := u.restrict fun x hx => hx
    have hu₀ : Function.Injective u₀ := fun x y hxy => Subtype.ext (hu (congrArg Subtype.val hxy))
    let ū : (N' ⧸ N'₀) →ₗ[A] (N ⧸ N₀) := Submodule.mapQ N'₀ N₀ u le_rfl
    have hū : Function.Injective ū := by
      intro x y hxy
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N'₀ x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N'₀ y
      rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at hxy
      rw [Submodule.Quotient.eq]
      change u (x - y) ∈ N₀
      rw [map_sub]; exact hxy

    have i₀ : Function.Injective (LinearMap.lTensor M u₀) := ih (↥N₀) hN₀ (↥N'₀) u₀ hu₀
    have iι : Function.Injective (LinearMap.lTensor M N₀.subtype) :=
      beta M h𝔪 N₀.subtype Subtype.val_injective fun a ha x => by
        rw [Submodule.range_subtype]; exact Submodule.smul_mem_smul ha trivial
    haveI : Module.Finite A (N ⧸ N₀) := inferInstance
    have iū : Function.Injective (LinearMap.lTensor M ū) :=
      beta M h𝔪 ū hū fun a ha x => by
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N₀ x
        rw [← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero N₀).2 (Submodule.smul_mem_smul ha trivial)]
        exact zero_mem _

    have hexT := lTensor_exact M (LinearMap.exact_subtype_mkQ N'₀) (Submodule.mkQ_surjective N'₀)
    intro x y hxy
    rw [← sub_eq_zero] at hxy ⊢
    rw [← map_sub] at hxy
    set d := x - y
    have h1 : LinearMap.lTensor M N'₀.mkQ d = 0 := by
      apply iū
      rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
      have : ū.comp N'₀.mkQ = N₀.mkQ.comp u := by ext; rfl
      rw [this, LinearMap.lTensor_comp, LinearMap.comp_apply, hxy, map_zero]
    obtain ⟨z, hz⟩ := (hexT d).1 h1
    have h2 : LinearMap.lTensor M u₀ z = 0 := by
      apply iι
      rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
      have : N₀.subtype.comp u₀ = u.comp N'₀.subtype := by ext; rfl
      rw [this, LinearMap.lTensor_comp, LinearMap.comp_apply, hz, hxy]
    have hz0 : z = 0 := i₀ (by rw [h2, map_zero])
    rw [← hz, hz0, map_zero]

end LCF

namespace LCF

theorem finite_tensor {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (M : Type u) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M] [Module.Finite B M]
    (I : Type u) [AddCommGroup I] [Module A I] [Module.Finite A I] :
    Module.Finite B (M ⊗[A] I) := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Module.Finite A I).fg_top
  let Ψ : (↥s → M) →ₗ[B] M ⊗[A] I :=
    { toFun := fun m => ∑ y : ↥s, m y ⊗ₜ[A] (y : I)
      map_add' := fun m m' => by
        simp only [Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]
      map_smul' := fun b m => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, TensorProduct.smul_tmul'] }
  refine Module.Finite.of_surjective Ψ ?_
  have key : ∀ z : I, ∀ m : M, ∃ v : ↥s → M, Ψ v = m ⊗ₜ[A] z := by
    intro z
    have hz : z ∈ Submodule.span A (s : Set I) := by rw [hs]; exact Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem y hy =>
      intro m
      refine ⟨fun y' => if y' = ⟨y, hy⟩ then m else 0, ?_⟩
      change ∑ y' : ↥s, (if y' = ⟨y, hy⟩ then m else 0) ⊗ₜ[A] (y' : I) = m ⊗ₜ[A] y
      rw [Finset.sum_eq_single (⟨y, hy⟩ : ↥s)]
      · simp
      · intro y' _ hne; rw [if_neg hne, TensorProduct.zero_tmul]
      · intro h; exact absurd (Finset.mem_univ _) h
    | zero => intro m; exact ⟨0, by rw [map_zero, TensorProduct.tmul_zero]⟩
    | add z₁ z₂ _ _ h₁ h₂ =>
      intro m
      obtain ⟨v₁, hv₁⟩ := h₁ m; obtain ⟨v₂, hv₂⟩ := h₂ m
      exact ⟨v₁ + v₂, by rw [map_add, hv₁, hv₂, TensorProduct.tmul_add]⟩
    | smul a z _ h =>
      intro m
      obtain ⟨v, hv⟩ := h (a • m)
      exact ⟨v, by rw [hv, TensorProduct.smul_tmul, TensorProduct.tmul_smul]⟩
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero Ψ⟩
  | tmul m z => exact key z m
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add Ψ a b⟩

end LCF

open LCF in
theorem solution
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (M : Type u) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M] [Module.Finite B M]
    (h : Function.Injective (LinearMap.rTensor M (maximalIdeal A).subtype)) :
    Module.Flat A M := by
  classical
  have h𝔪 : Function.Injective (LinearMap.lTensor M (maximalIdeal A).subtype) :=
    (LinearMap.lTensor_inj_iff_rTensor_inj M _).2 h
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx

  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul (maximalIdeal A) (M := A) (I : Submodule A A)

  have hδ : ∀ n : ℕ, x ∈ (maximalIdeal A) ^ n • (⊤ : Submodule A (M ⊗[A] ↥I)) := by
    intro n
    set N := n + c with hNdef

    let KI : Submodule A ↥I := Submodule.comap I.subtype ((maximalIdeal A) ^ N)

    let ū : (↥I ⧸ KI) →ₗ[A] (A ⧸ (maximalIdeal A) ^ N) := Submodule.mapQ KI ((maximalIdeal A) ^ N) I.subtype le_rfl
    have hū : Function.Injective ū := by
      intro a b hab
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective KI a
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective KI b
      rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at hab
      rw [Submodule.Quotient.eq]
      change I.subtype (a - b) ∈ (maximalIdeal A) ^ N
      rw [map_sub]; exact hab
    have hkill : (maximalIdeal A) ^ N • (⊤ : Submodule A (A ⧸ (maximalIdeal A) ^ N)) = ⊥ := by
      rw [eq_bot_iff, Submodule.smul_le]
      intro r hr y _
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [← Submodule.Quotient.mk_smul, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      exact Ideal.mul_mem_right y _ hr
    have hγ := gamma M h𝔪 N (A ⧸ (maximalIdeal A) ^ N) hkill (↥I ⧸ KI) ū hū

    have h1 : LinearMap.lTensor M KI.mkQ x = 0 := by
      apply hγ
      rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
      have : ū.comp KI.mkQ = ((maximalIdeal A) ^ N).mkQ.comp I.subtype := by ext; rfl
      rw [this, LinearMap.lTensor_comp, LinearMap.comp_apply, hx, map_zero]
    obtain ⟨z, hz⟩ := ((lTensor_exact M (LinearMap.exact_subtype_mkQ KI) (Submodule.mkQ_surjective KI)) x).1 h1

    have hKI : KI ≤ (maximalIdeal A) ^ n • (⊤ : Submodule A ↥I) := by
      intro k hk
      have hk' : (k : A) ∈ (maximalIdeal A) ^ N • (⊤ : Submodule A A) ⊓ (I : Submodule A A) := by
        refine ⟨?_, k.2⟩
        rw [Ideal.smul_eq_mul, Ideal.mul_top]; exact hk
      rw [hc N (by omega), show N - c = n by omega] at hk'
      have hle : (maximalIdeal A) ^ n • ((maximalIdeal A) ^ c • (⊤ : Submodule A A) ⊓ (I : Submodule A A)) ≤
          Submodule.map I.subtype ((maximalIdeal A) ^ n • ⊤) := by
        rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
        exact Submodule.smul_mono le_rfl inf_le_right
      obtain ⟨k', hk'mem, hk'eq⟩ := hle hk'
      have : k' = k := Subtype.ext hk'eq
      rw [← this]; exact hk'mem

    rw [← hz]
    clear hz
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul m k =>
      rw [LinearMap.lTensor_tmul]
      have hk := hKI k.2

      refine Submodule.smul_induction_on (p := fun y => m ⊗ₜ[A] y ∈ (maximalIdeal A) ^ n • (⊤ : Submodule A (M ⊗[A] ↥I))) hk ?_ ?_
      · intro r hr y _
        rw [TensorProduct.tmul_smul]
        exact Submodule.smul_mem_smul hr trivial
      · intro y₁ y₂ h₁ h₂
        rw [TensorProduct.tmul_add]; exact add_mem h₁ h₂
    | add z₁ z₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂

  haveI : SMulCommClass A B M := IsScalarTower.to_smulCommClass
  haveI : Module.Finite A ↥I := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian I)
  haveI : Module.Finite B (M ⊗[A] ↥I) := finite_tensor M ↥I
  have hKrull := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (maximalIdeal B) (M := M ⊗[A] ↥I)
    (Ideal.IsPrime.ne_top inferInstance)
  have hmap : ∀ a ∈ maximalIdeal A, algebraMap A B a ∈ maximalIdeal B := by
    intro a ha
    by_contra hb
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hb
    exact ha (IsLocalHom.map_nonunit a hb)
  have hpow : ∀ (n : ℕ) (a : A), a ∈ (maximalIdeal A) ^ n → algebraMap A B a ∈ (maximalIdeal B) ^ n := by
    intro n a ha
    have : Ideal.map (algebraMap A B) ((maximalIdeal A) ^ n) ≤ (maximalIdeal B) ^ n := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun a ha => Ideal.mem_comap.2 (hmap a ha)) n
    exact this (Ideal.mem_map_of_mem _ ha)
  have hxB : ∀ n : ℕ, x ∈ ((maximalIdeal B) ^ n • (⊤ : Submodule B (M ⊗[A] ↥I))) := by
    intro n
    have hle : ∀ y : M ⊗[A] ↥I, y ∈ (maximalIdeal A) ^ n • (⊤ : Submodule A (M ⊗[A] ↥I)) →
        y ∈ ((maximalIdeal B) ^ n • (⊤ : Submodule B (M ⊗[A] ↥I))) := by
      intro y hy
      refine Submodule.smul_induction_on (p := fun y => y ∈ ((maximalIdeal B) ^ n • (⊤ : Submodule B (M ⊗[A] ↥I)))) hy ?_ ?_
      · intro r hr w _
        have : r • w = (algebraMap A B r) • w := (algebraMap_smul B r w).symm
        rw [this]
        exact Submodule.smul_mem_smul (hpow n r hr) trivial
      · intro y₁ y₂ h₁ h₂; exact add_mem h₁ h₂
    exact hle x (hδ n)
  have : x ∈ (⨅ i : ℕ, (maximalIdeal B) ^ i • (⊤ : Submodule B (M ⊗[A] ↥I))) := (Submodule.mem_iInf _).2 hxB
  rw [hKrull] at this
  exact this

end S_Module_flat_of_maximalIdeal_rTensor_injective_of_isLocalHom
end P2MW
export P2MW.S_Module_flat_of_maximalIdeal_rTensor_injective_of_isLocalHom (solution)
