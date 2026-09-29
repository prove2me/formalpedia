-- Prove2me | solution 1 for Module.nonempty_linearEquiv_of_forall_exists_quotient_pow_smul_linearEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/77a8a66b-1f3f-57ee-831e-ee221a25517d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_nonempty_linearEquiv_of_forall_exists_quotient_pow_smul_linearEquiv

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace GuralnickLift

variable {A : Type*} [CommRing A]

abbrev W (M : Type*) [AddCommGroup M] [Module A M] (ϖ : A) (k : ℕ) : Submodule A M :=
  LinearMap.range (ϖ ^ k • (LinearMap.id : M →ₗ[A] M))

section Basic

variable {M : Type*} [AddCommGroup M] [Module A M] (ϖ : A)

theorem mem_W {k : ℕ} {v : M} : v ∈ W M ϖ k ↔ ∃ w : M, ϖ ^ k • w = v := by
  simp only [LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply]

theorem pow_smul_mem_W (k : ℕ) (w : M) : ϖ ^ k • w ∈ W M ϖ k := (mem_W ϖ).mpr ⟨w, rfl⟩

theorem W_anti {k k' : ℕ} (h : k ≤ k') : W M ϖ k' ≤ W M ϖ k := by
  intro v hv
  obtain ⟨w, rfl⟩ := (mem_W ϖ).mp hv
  refine (mem_W ϖ).mpr ⟨ϖ ^ (k' - k) • w, ?_⟩
  rw [← mul_smul, ← pow_add, Nat.add_sub_cancel' h]

theorem pow_smul_eq_zero (hM : ∀ m : M, ϖ • m = 0 → m = 0) (k : ℕ) (m : M) (h : ϖ ^ k • m = 0) :
    m = 0 := by
  induction k with
  | zero => rwa [pow_zero, one_smul] at h
  | succ k ih =>
    apply ih
    apply hM
    rwa [← mul_smul, ← pow_succ']

theorem pow_smul_injective (hM : ∀ m : M, ϖ • m = 0 → m = 0) (k : ℕ) :
    Function.Injective (ϖ ^ k • (LinearMap.id : M →ₗ[A] M)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro m hm
  exact pow_smul_eq_zero ϖ hM k m hm

abbrev red {k k' : ℕ} (h : k ≤ k') : (M ⧸ W M ϖ k') →ₗ[A] (M ⧸ W M ϖ k) :=
  (W M ϖ k').mapQ (W M ϖ k) LinearMap.id (W_anti ϖ h)

theorem red_mk {k k' : ℕ} (h : k ≤ k') (v : M) :
    red ϖ h (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := rfl

end Basic

section Lift

variable [IsNoetherianRing A] (ϖ : A)
  {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
  {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]

theorem exists_lift_const (hN : ∀ n : N, ϖ • n = 0 → n = 0) :
    ∃ n₀ : ℕ, ∀ (m k : ℕ) (hmk : m + n₀ ≤ k) (g : M →ₗ[A] N ⧸ W N ϖ k),
      ∃ ψ : M →ₗ[A] N, ∀ v : M,
        (W N ϖ m).mkQ (ψ v) = red ϖ (le_trans (Nat.le_add_right m n₀) hmk) (g v) := by
  classical

  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' A M
  set K : Submodule A (Fin n → A) := LinearMap.ker π with hKdef
  haveI : IsNoetherian A ↥K := inferInstance
  haveI : Module.Finite A ↥K := inferInstance

  let resK : ((Fin n → A) →ₗ[A] N) →ₗ[A] (↥K →ₗ[A] N) := LinearMap.lcomp A N K.subtype
  have resK_apply : ∀ (f : (Fin n → A) →ₗ[A] N) (κ : ↥K), resK f κ = f κ := fun f κ => rfl
  let R₀ : Submodule A (↥K →ₗ[A] N) := LinearMap.range resK

  obtain ⟨j, πK, hπK⟩ := Module.Finite.exists_fin' A ↥K
  haveI : IsNoetherian A ((Fin j → A) →ₗ[A] N) := inferInstance
  haveI : IsNoetherian A (↥K →ₗ[A] N) := by
    refine isNoetherian_of_injective (LinearMap.lcomp A N πK) fun h h' hh => ?_
    apply LinearMap.ext
    intro κ
    obtain ⟨y, rfl⟩ := hπK κ
    exact LinearMap.congr_fun hh y
  haveI : IsNoetherian A ((↥K →ₗ[A] N) ⧸ R₀) := inferInstance

  let c : ℕ →o Submodule A ((↥K →ₗ[A] N) ⧸ R₀) :=
    { toFun := fun i => LinearMap.ker (ϖ ^ i • (LinearMap.id : _ →ₗ[A] _))
      monotone' := fun i i' hii' q hq => by
        rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at hq ⊢
        rw [← Nat.add_sub_cancel' hii', pow_add, mul_comm, mul_smul, hq, smul_zero] }
  obtain ⟨n₀, hn₀⟩ := (monotone_stabilizes_iff_noetherian.mpr inferInstance) c
  have hbdd : ∀ (i : ℕ) (q : (↥K →ₗ[A] N) ⧸ R₀), n₀ ≤ i → ϖ ^ i • q = 0 → ϖ ^ n₀ • q = 0 := by
    intro i q hi hq
    have hmem : q ∈ c i := by
      show q ∈ LinearMap.ker (ϖ ^ i • (LinearMap.id : _ →ₗ[A] _))
      rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, hq]
    rw [← hn₀ i hi] at hmem
    have : q ∈ LinearMap.ker (ϖ ^ n₀ • (LinearMap.id : _ →ₗ[A] _)) := hmem
    rwa [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at this
  refine ⟨n₀, fun m k hmk g => ?_⟩
  have hn₀k : n₀ ≤ k := le_trans (Nat.le_add_left n₀ m) hmk

  obtain ⟨f, hf⟩ := Module.projective_lifting_property (W N ϖ k).mkQ (g ∘ₗ π)
    (Submodule.mkQ_surjective _)
  have hfK : ∀ κ : ↥K, f κ ∈ W N ϖ k := fun κ => by
    have := LinearMap.congr_fun hf κ
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
      show π (κ : Fin n → A) = 0 from LinearMap.mem_ker.mp κ.2, map_zero,
      Submodule.Quotient.mk_eq_zero] at this
    exact this

  let eqv : N ≃ₗ[A] ↥(W N ϖ k) := LinearEquiv.ofInjective _ (pow_smul_injective ϖ hN k)
  have eqv_apply : ∀ w : N, ((eqv w : ↥(W N ϖ k)) : N) = ϖ ^ k • w := fun w => rfl
  let h : ↥K →ₗ[A] N := eqv.symm.toLinearMap ∘ₗ (f ∘ₗ K.subtype).codRestrict (W N ϖ k) hfK
  have hh : ∀ κ : ↥K, ϖ ^ k • h κ = f κ := fun κ => by
    rw [← eqv_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply,
      LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply]

  have hcls : ϖ ^ k • R₀.mkQ h = 0 := by
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine ⟨f, LinearMap.ext fun κ => ?_⟩
    rw [resK_apply, LinearMap.smul_apply, hh]
  have hcls' := hbdd k _ hn₀k hcls
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hcls'
  obtain ⟨f', hf'⟩ := hcls'
  have hf'K : ∀ κ : ↥K, f' κ = ϖ ^ n₀ • h κ := fun κ => by
    have := LinearMap.congr_fun hf' κ
    rw [resK_apply, LinearMap.smul_apply] at this
    exact this

  let f₂ : (Fin n → A) →ₗ[A] N := f - ϖ ^ (k - n₀) • f'
  have hf₂K : K ≤ LinearMap.ker f₂ := fun y hy => by
    rw [LinearMap.mem_ker]
    show f y - ϖ ^ (k - n₀) • f' y = 0
    have h1 := hh ⟨y, hy⟩
    have h2 := hf'K ⟨y, hy⟩
    rw [h2, ← h1, ← mul_smul, ← pow_add, Nat.sub_add_cancel hn₀k, sub_self]
  let ψ : M →ₗ[A] N := (K.liftQ f₂ hf₂K) ∘ₗ (π.quotKerEquivOfSurjective hπ).symm.toLinearMap
  have hψ : ∀ y : Fin n → A, ψ (π y) = f₂ y := fun y => by
    show K.liftQ f₂ hf₂K ((π.quotKerEquivOfSurjective hπ).symm (π y)) = f₂ y
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  refine ⟨ψ, fun v => ?_⟩
  obtain ⟨y, rfl⟩ := hπ v
  have hgy : g (π y) = (W N ϖ k).mkQ (f y) := by
    have := LinearMap.congr_fun hf y
    exact this.symm
  rw [hψ, hgy, Submodule.mkQ_apply, Submodule.mkQ_apply, red_mk]
  show Submodule.Quotient.mk (f y - ϖ ^ (k - n₀) • f' y) = Submodule.Quotient.mk (f y)
  rw [Submodule.Quotient.mk_sub, sub_eq_self, Submodule.Quotient.mk_eq_zero]
  have hmk : m ≤ k - n₀ := by omega
  exact W_anti ϖ hmk (pow_smul_mem_W ϖ _ _)

theorem exists_surjective (hϖ : ϖ ∈ Ideal.jacobson (⊥ : Ideal A))
    (hN : ∀ n : N, ϖ • n = 0 → n = 0)
    (h : ∀ k₀ : ℕ, ∃ k : ℕ, k₀ ≤ k ∧ Nonempty ((M ⧸ W M ϖ k) ≃ₗ[A] (N ⧸ W N ϖ k))) :
    ∃ ψ : M →ₗ[A] N, Function.Surjective ψ := by
  obtain ⟨n₀, hn₀⟩ := exists_lift_const ϖ (M := M) hN
  obtain ⟨k, hk, ⟨e⟩⟩ := h (1 + n₀)
  obtain ⟨ψ, hψ⟩ := hn₀ 1 k hk (e.toLinearMap ∘ₗ (W M ϖ k).mkQ)
  refine ⟨ψ, ?_⟩

  have hle : (⊤ : Submodule A N) ≤ LinearMap.range ψ ⊔ Ideal.span {ϖ} • ⊤ := by
    intro n _
    obtain ⟨q, hq⟩ := e.surjective ((W N ϖ k).mkQ n)
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ q
    have h1 := hψ v
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hq, Submodule.mkQ_apply, Submodule.mkQ_apply, red_mk,
      Submodule.Quotient.eq] at h1
    obtain ⟨w, hw⟩ := (mem_W ϖ).mp h1
    rw [pow_one] at hw
    have : n = ψ v - ϖ • w := by rw [hw, sub_sub_cancel]
    rw [this]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left (LinearMap.mem_range_self ψ v))
      (Submodule.mem_sup_right (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ϖ)
        Submodule.mem_top))
  have hspan : Ideal.span {ϖ} ≤ Ideal.jacobson ⊥ := (Ideal.span_singleton_le_iff_mem _).mpr hϖ
  have htop := Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hspan hle
  rw [← LinearMap.range_eq_top]
  exact top_le_iff.mp htop

end Lift

end GuralnickLift

end

open GuralnickLift in
theorem solution
    {A : Type*} [CommRing A] [IsNoetherianRing A] (ϖ : A) (hϖ : ϖ ∈ Ideal.jacobson (⊥ : Ideal A))
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hM : ∀ m : M, ϖ • m = 0 → m = 0) (hN : ∀ n : N, ϖ • n = 0 → n = 0)
    (h : ∀ k₀ : ℕ, ∃ k : ℕ, k₀ ≤ k ∧
      Nonempty ((M ⧸ LinearMap.range (ϖ ^ k • (LinearMap.id : M →ₗ[A] M))) ≃ₗ[A]
        (N ⧸ LinearMap.range (ϖ ^ k • (LinearMap.id : N →ₗ[A] N))))) :
    Nonempty (M ≃ₗ[A] N) := by

  obtain ⟨ψ, hψ⟩ := exists_surjective ϖ hϖ hN h
  obtain ⟨χ, hχ⟩ := exists_surjective ϖ (M := N) (N := M) hϖ hM fun k₀ => by
    obtain ⟨k, hk, ⟨e⟩⟩ := h k₀
    exact ⟨k, hk, ⟨e.symm⟩⟩

  haveI : IsNoetherian A M := inferInstance
  have hinj : Function.Injective (χ ∘ₗ ψ) :=
    IsNoetherian.injective_of_surjective_endomorphism _ (hχ.comp hψ)
  exact ⟨LinearEquiv.ofBijective ψ ⟨Function.Injective.of_comp hinj, hψ⟩⟩

end S_Module_nonempty_linearEquiv_of_forall_exists_quotient_pow_smul_linearEquiv
end P2MW
export P2MW.S_Module_nonempty_linearEquiv_of_forall_exists_quotient_pow_smul_linearEquiv (solution)
