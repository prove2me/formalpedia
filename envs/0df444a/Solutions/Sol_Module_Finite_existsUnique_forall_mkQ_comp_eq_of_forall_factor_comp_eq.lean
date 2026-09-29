-- Prove2me | solution 1 for Module.Finite.existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/0849591f-d034-5a1b-a60d-27d11ac673d8

import Mathlib
import Theorems.Thm_AdicCompletion_exists_linearMap_forall_val_apply_eq_mk_apply
import Theorems.Thm_AdicCompletion_bijective_of_forall_val_apply_eq_mk_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Finite_existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq

set_option autoImplicit false

universe u

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Finite A M] [Module.Finite A N]
    (ψ : ∀ n : ℕ, M →ₗ[A] N ⧸ (I ^ (n + 1) • (⊤ : Submodule A N)))
    (hψ : ∀ n : ℕ,
      Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) ∘ₗ ψ (n + 1) = ψ n) :
    ∃! Φ : ∀ n : ℕ, (M →ₗ[A] N) ⧸ (I ^ (n + 1) • (⊤ : Submodule A (M →ₗ[A] N))),
      (∀ n : ℕ, Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) (Φ (n + 1)) = Φ n) ∧
      (∀ (n : ℕ) (g : M →ₗ[A] N), Submodule.Quotient.mk g = Φ n →
        (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule A N))) ∘ₗ g = ψ n) := by
  classical
  obtain ⟨θ, hθ⟩ := AdicCompletion.exists_linearMap_forall_val_apply_eq_mk_apply I M N
  have hbij := AdicCompletion.bijective_of_forall_val_apply_eq_mk_apply I θ hθ

  have hsubN : ∀ a b : N ⧸ (I ^ 0 • (⊤ : Submodule A N)), a = b := by
    intro a b
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [Submodule.Quotient.eq, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    exact Submodule.mem_top
  have hsubH : ∀ a b : (M →ₗ[A] N) ⧸ (I ^ 0 • (⊤ : Submodule A (M →ₗ[A] N))), a = b := by
    intro a b
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [Submodule.Quotient.eq, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    exact Submodule.mem_top
  have antiN : Antitone fun n : ℕ => (I ^ n • ⊤ : Submodule A N) :=
    fun _ _ h => Submodule.smul_mono_left (Ideal.pow_le_pow_right h)
  have antiH : Antitone fun n : ℕ => (I ^ n • ⊤ : Submodule A (M →ₗ[A] N)) :=
    fun _ _ h => Submodule.smul_mono_left (Ideal.pow_le_pow_right h)

  let ψ' : ∀ n : ℕ, M →ₗ[A] N ⧸ (I ^ n • (⊤ : Submodule A N)) := fun n =>
    match n with
    | 0 => 0
    | n + 1 => ψ n
  have hψ'v : ∀ (v : M) {m n : ℕ} (hle : m ≤ n),
      AdicCompletion.transitionMap I N hle (ψ' n v) = ψ' m v := by
    intro v m n hle
    refine (Submodule.eq_factor_of_eq_factor_succ antiN (fun n => ψ' n v) (fun m => ?_) hle).symm
    cases m with
    | zero => exact hsubN _ _
    | succ m => exact (LinearMap.congr_fun (hψ m) v).symm
  have hψ' : ∀ {m n : ℕ} (hle : m ≤ n), AdicCompletion.transitionMap I N hle ∘ₗ ψ' n = ψ' m :=
    fun hle => LinearMap.ext fun v => hψ'v v hle
  let Ψ : M →ₗ[A] AdicCompletion I N := AdicCompletion.lift I ψ' hψ'
  have hΨ : ∀ (v : M) (n : ℕ), (Ψ v).val (n + 1) = ψ n v := fun v n => rfl
  obtain ⟨x, hx⟩ := hbij.2 Ψ
  refine ⟨fun n => x.val (n + 1), ⟨fun n => x.property (Nat.le_succ (n + 1)), ?_⟩, ?_⟩
  · intro n g hg
    ext v
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, ← hθ x (n + 1) g hg v, hx, hΨ]
  · rintro Φ' ⟨hc', hcl'⟩

    let Φ'' : ∀ n : ℕ, (M →ₗ[A] N) ⧸ (I ^ n • (⊤ : Submodule A (M →ₗ[A] N))) := fun n =>
      match n with
      | 0 => 0
      | n + 1 => Φ' n
    have hΦ'' : ∀ {m n : ℕ} (hle : m ≤ n),
        AdicCompletion.transitionMap I (M →ₗ[A] N) hle (Φ'' n) = Φ'' m := by
      intro m n hle
      refine (Submodule.eq_factor_of_eq_factor_succ antiH Φ'' (fun m => ?_) hle).symm
      cases m with
      | zero => exact hsubH _ _
      | succ m => exact (hc' m).symm
    let x' : AdicCompletion I (M →ₗ[A] N) := ⟨Φ'', fun hle => hΦ'' hle⟩
    have hx' : θ x' = Ψ := by
      refine LinearMap.ext fun v => AdicCompletion.ext fun n => ?_
      cases n with
      | zero => exact hsubN _ _
      | succ n =>
        obtain ⟨g, hg⟩ := Submodule.Quotient.mk_surjective _ (Φ' n)
        rw [hθ x' (n + 1) g hg v, hΨ, ← hcl' n g hg, LinearMap.comp_apply, Submodule.mkQ_apply]
    have hxx : x' = x := hbij.1 (hx'.trans hx.symm)
    funext n
    show x'.val (n + 1) = x.val (n + 1)
    rw [hxx]

end S_Module_Finite_existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq
end P2MW
export P2MW.S_Module_Finite_existsUnique_forall_mkQ_comp_eq_of_forall_factor_comp_eq (solution)
