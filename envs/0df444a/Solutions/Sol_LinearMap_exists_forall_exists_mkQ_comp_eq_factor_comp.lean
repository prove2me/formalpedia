-- Prove2me | solution 1 for LinearMap.exists_forall_exists_mkQ_comp_eq_factor_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/3a7e8b9c-293b-5941-b7f9-838b0b9bd84a

import Mathlib
import Theorems.Thm_LinearMap_exists_forall_mem_pow_smul_top_of_range_le_pow_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearMap_exists_forall_exists_mkQ_comp_eq_factor_comp

set_option autoImplicit false

universe u v w

namespace Z1Alg

theorem finite_hom_ker {B : Type u} [CommRing B] [IsNoetherianRing B] {M : Type v} {N : Type w}
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] [Module.Finite B N]
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M) : Module.Finite B (↥(LinearMap.ker p) →ₗ[B] N) := by
  haveI : Module.Finite B ↥(LinearMap.ker p) := Module.Finite.of_fg (IsNoetherian.noetherian _)
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' B ↥(LinearMap.ker p)
  haveI : Module.Finite B ((Fin n → B) →ₗ[B] N) := Module.Finite.linearMap B B _ _
  refine Module.Finite.of_injective (LinearMap.lcomp B N π) fun f g hfg => ?_
  ext s
  obtain ⟨v, rfl⟩ := hπ s
  exact congrArg (fun φ : (Fin n → B) →ₗ[B] N => φ v) hfg

theorem exists_artinRees_lift {B : Type u} [CommRing B] [IsNoetherianRing B] {P : Type v} {Q : Type w}
    [AddCommGroup P] [Module B P] [AddCommGroup Q] [Module B Q] [Module.Finite B Q]
    (J : Ideal B) (L : P →ₗ[B] Q) :
    ∃ c : ℕ, ∀ (n : ℕ) (x : P), L x ∈ J ^ (n + c) • (⊤ : Submodule B Q) →
      ∃ z : P, z ∈ J ^ n • (⊤ : Submodule B P) ∧ L z = L x := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul J (LinearMap.range L)
  refine ⟨c, fun n x hx => ?_⟩
  have hmem : L x ∈ J ^ (n + c) • (⊤ : Submodule B Q) ⊓ LinearMap.range L := ⟨hx, LinearMap.mem_range_self L x⟩
  rw [hc (n + c) (Nat.le_add_left c n), Nat.add_sub_cancel] at hmem
  have hle : J ^ n • (J ^ c • (⊤ : Submodule B Q) ⊓ LinearMap.range L) ≤ (J ^ n • (⊤ : Submodule B P)).map L := by
    rw [Submodule.map_smul'', Submodule.map_top]
    exact Submodule.smul_mono le_rfl inf_le_right
  obtain ⟨z, hz, hzx⟩ := hle hmem
  exact ⟨z, hz, hzx⟩

theorem apply_mem_smul_top_of_mem {B : Type u} [CommRing B] {X : Type v} {N : Type w}
    [AddCommGroup X] [Module B X] [AddCommGroup N] [Module B N]
    (J : Ideal B) (h : X →ₗ[B] N) (hh : h ∈ J • (⊤ : Submodule B (X →ₗ[B] N))) (x : X) :
    h x ∈ J • (⊤ : Submodule B N) := by
  have : (J • (⊤ : Submodule B (X →ₗ[B] N))).map (LinearMap.applyₗ x) ≤ J • ⊤ := by
    rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
  exact this ⟨h, hh, rfl⟩

end Z1Alg

open Z1Alg in
theorem solution
    {B : Type u} [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    {M : Type v} [AddCommGroup M] [Module B M] [Module.Finite B M]
    {N : Type w} [AddCommGroup N] [Module B N] [Module.Finite B N] :
    ∃ c : ℕ, ∀ (n : ℕ) (f : M →ₗ[B] N ⧸ (I ^ (n + c) • (⊤ : Submodule B N))),
      ∃ g : M →ₗ[B] N,
        (I ^ n • (⊤ : Submodule B N)).mkQ ∘ₗ g =
          Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_right n c))) ∘ₗ f := by
  classical

  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' B M
  haveI : Module.Finite B ↥(LinearMap.ker π) := Module.Finite.of_fg (IsNoetherian.noetherian _)
  haveI := finite_hom_ker (N := N) π

  obtain ⟨c₂, hc₂⟩ := LinearMap.exists_forall_mem_pow_smul_top_of_range_le_pow_smul I (M := ↥(LinearMap.ker π)) (N := N)
  obtain ⟨c₁, hc₁⟩ := exists_artinRees_lift I (LinearMap.lcomp B N (LinearMap.ker π).subtype)
  refine ⟨c₁ + c₂, fun n f => ?_⟩

  obtain ⟨h, hh⟩ := Module.projective_lifting_property (I ^ (n + (c₁ + c₂)) • (⊤ : Submodule B N)).mkQ (f ∘ₗ π)
    (Submodule.mkQ_surjective _)

  have hR : LinearMap.range (h ∘ₗ (LinearMap.ker π).subtype) ≤ I ^ (n + (c₁ + c₂)) • (⊤ : Submodule B N) := by
    rintro _ ⟨s, rfl⟩
    have : (I ^ (n + (c₁ + c₂)) • (⊤ : Submodule B N)).mkQ (h s) = 0 := by
      have := LinearMap.congr_fun hh (s : Fin r → B)
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.mem_ker.mp s.2, map_zero] at this
      exact this
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  rw [← add_assoc] at hR

  have h1 : h ∘ₗ (LinearMap.ker π).subtype ∈ I ^ (n + c₁) • (⊤ : Submodule B (↥(LinearMap.ker π) →ₗ[B] N)) :=
    hc₂ (n + c₁) _ hR
  obtain ⟨h', hh', hres⟩ := hc₁ n h h1

  have hvan : ∀ s : ↥(LinearMap.ker π), (h - h') (s : Fin r → B) = 0 := by
    intro s
    have := LinearMap.congr_fun hres s
    simp only [LinearMap.lcomp_apply, Submodule.subtype_apply] at this
    rw [LinearMap.sub_apply, this, sub_self]
  have hker : LinearMap.ker π ≤ LinearMap.ker (h - h') := fun s hs => hvan ⟨s, hs⟩
  let g : M →ₗ[B] N := ((LinearMap.ker π).liftQ (h - h') hker) ∘ₗ (π.quotKerEquivOfSurjective hπ).symm.toLinearMap
  have hgπ : g ∘ₗ π = h - h' := by
    refine LinearMap.ext fun v => ?_
    show ((LinearMap.ker π).liftQ (h - h') hker) ((π.quotKerEquivOfSurjective hπ).symm (π v)) = (h - h') v
    have : (π.quotKerEquivOfSurjective hπ).symm (π v) = Submodule.Quotient.mk v := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    rw [this]; rfl
  refine ⟨g, ?_⟩

  apply LinearMap.ext
  intro m
  obtain ⟨v, rfl⟩ := hπ m
  have e1 : ((I ^ n • (⊤ : Submodule B N)).mkQ ∘ₗ g) (π v) = (I ^ n • (⊤ : Submodule B N)).mkQ (h v) - (I ^ n • (⊤ : Submodule B N)).mkQ (h' v) := by
    rw [LinearMap.comp_apply, ← LinearMap.comp_apply g π, hgπ, LinearMap.sub_apply, map_sub]
  have e2 : (I ^ n • (⊤ : Submodule B N)).mkQ (h' v) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact apply_mem_smul_top_of_mem (I ^ n) h' hh' v
  have e3 : (Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_right n (c₁ + c₂)))) ∘ₗ f) (π v)
      = (I ^ n • (⊤ : Submodule B N)).mkQ (h v) := by
    rw [LinearMap.comp_apply, ← LinearMap.comp_apply f π, ← hh, LinearMap.comp_apply]
    rfl
  rw [e1, e2, sub_zero, e3]

end S_LinearMap_exists_forall_exists_mkQ_comp_eq_factor_comp
end P2MW
export P2MW.S_LinearMap_exists_forall_exists_mkQ_comp_eq_factor_comp (solution)
