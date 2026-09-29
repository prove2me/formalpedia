-- Prove2me | solution 1 for Module.existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/93853d4e-511b-5ae2-a0a1-fea28bbdb20a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul

set_option autoImplicit false

universe u

theorem solution
    {R : Type u} [CommRing R] (I : Ideal R)
    (E : ℕ → Type u) [∀ k, AddCommGroup (E k)] [∀ k, Module R (E k)]
    (τ : ∀ k, E (k + 1) →ₗ[R] E k) (hτs : ∀ k, Function.Surjective (τ k))
    (hτk : ∀ k, LinearMap.ker (τ k) = I ^ (k + 1) • (⊤ : Submodule R (E (k + 1))))
    (P : ℕ → Type u) [∀ k, AddCommGroup (P k)] [∀ k, Module R (P k)] (π : ∀ k, P (k + 1) →ₗ[R] P k)
    (C : ℕ → Type u) [∀ k, AddCommGroup (C k)] [∀ k, Module R (C k)] (θ : ∀ k, P k →ₗ[R] C k)
    (u : ∀ k, E k →ₗ[R] P k) (huc : ∀ k, π k ∘ₗ u (k + 1) = u k ∘ₗ τ k)
    (hur : ∀ k, LinearMap.range (u k) = LinearMap.ker (θ k))
    (hui : ∃ c : ℕ, ∀ k : ℕ, LinearMap.ker (u (k + c)) ≤ I ^ (k + 1) • (⊤ : Submodule R (E (k + c))))
    (p : ∀ k, P k) (hp : ∀ k, π k (p (k + 1)) = p k) (hpθ : ∀ k, θ k (p k) = 0) :
    ∃! e : ∀ k, E k, (∀ k, τ k (e (k + 1)) = e k) ∧ ∀ k, u k (e k) = p k := by
  classical
  obtain ⟨c, hc⟩ := hui

  let T : (∀ k, E k) →ₗ[R] (∀ k, E k) := LinearMap.pi fun k => τ k ∘ₗ LinearMap.proj (k + 1)
  let S : (∀ k, P k) →ₗ[R] (∀ k, P k) := LinearMap.pi fun k => π k ∘ₗ LinearMap.proj (k + 1)
  let U : (∀ k, E k) →ₗ[R] (∀ k, P k) := LinearMap.pi fun k => u k ∘ₗ LinearMap.proj k
  have hT : ∀ (x : ∀ k, E k) (k : ℕ), T x k = τ k (x (k + 1)) := fun x k => rfl
  have hS : ∀ (y : ∀ k, P k) (k : ℕ), S y k = π k (y (k + 1)) := fun y k => rfl
  have hU : ∀ (x : ∀ k, E k) (k : ℕ), U x k = u k (x k) := fun x k => rfl

  have hkill : ∀ (k : ℕ) (x : E k), x ∈ (I ^ (k + 1) • ⊤ : Submodule R (E k)) → x = 0 := by
    intro k x hx
    refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun x y hx hy => by rw [hx, hy, add_zero])
    obtain ⟨z, rfl⟩ := hτs k y
    rw [← map_smul]
    have hz : a • z ∈ LinearMap.ker (τ k) := by
      rw [hτk k]; exact Submodule.smul_mem_smul ha Submodule.mem_top
    exact LinearMap.mem_ker.mp hz

  have hinv : ∀ (j : ℕ) (x : ∀ k, E k), (∀ k, x k ∈ (I ^ (k + 1 + j - c) • ⊤ : Submodule R (E k))) →
      ∀ k, T x k ∈ (I ^ (k + 1 + (j + 1) - c) • ⊤ : Submodule R (E k)) := by
    intro j x hx k
    rw [hT]
    have h1 : x (k + 1) ∈ (I ^ (k + 1 + 1 + j - c) • ⊤ : Submodule R (E (k + 1))) := hx (k + 1)
    have h2 : Submodule.map (τ k) (I ^ (k + 1 + 1 + j - c) • ⊤ : Submodule R (E (k + 1))) ≤
        (I ^ (k + 1 + (j + 1) - c) • ⊤ : Submodule R (E k)) := by
      rw [Submodule.map_smul'', show k + 1 + 1 + j - c = k + 1 + (j + 1) - c by omega]
      exact smul_mono_right _ le_top
    exact h2 ⟨_, h1, rfl⟩
  have hiter : ∀ (j : ℕ) (x : ∀ k, E k), (∀ k, x k ∈ (I ^ (k + 1 - c) • ⊤ : Submodule R (E k))) →
      ∀ k, (T ^ j) x k ∈ (I ^ (k + 1 + j - c) • ⊤ : Submodule R (E k)) := by
    intro j
    induction j with
    | zero =>
      intro x hx k
      rw [pow_zero, Module.End.one_apply, show k + 1 + 0 - c = k + 1 - c by omega]
      exact hx k
    | succ j ih =>
      intro x hx k
      rw [pow_succ', Module.End.mul_apply]
      exact hinv j _ (ih x hx) k
  have hvanish : ∀ x : ∀ k, E k, U x = 0 → (T ^ c) x = 0 := by
    intro x hx
    have hx' : ∀ k, x k ∈ (I ^ (k + 1 - c) • ⊤ : Submodule R (E k)) := by
      intro k
      by_cases hk : c ≤ k
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
        have hxk : x (m + c) ∈ LinearMap.ker (u (m + c)) := by
          have := congrFun hx (m + c)
          rw [hU] at this
          exact this
        have := hc m hxk
        rwa [show m + c + 1 - c = m + 1 by omega]
      · rw [show k + 1 - c = 0 by omega, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
        trivial
    funext k
    have := hiter c x hx' k
    rw [show k + 1 + c - c = k + 1 by omega] at this
    exact hkill k _ this

  have hUT : ∀ x, U (T x) = S (U x) := by
    intro x; funext k
    rw [hU, hT, hS, hU]
    exact (LinearMap.congr_fun (huc k) (x (k + 1))).symm
  have hUTi : ∀ (j : ℕ) (x : ∀ k, E k), U ((T ^ j) x) = (S ^ j) (U x) := by
    intro j
    induction j with
    | zero => intro x; rw [pow_zero, pow_zero, Module.End.one_apply, Module.End.one_apply]
    | succ j ih => intro x; rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, hUT, ih]
  have hSp : S p = p := funext fun k => by rw [hS]; exact hp k
  have hSpi : ∀ j : ℕ, (S ^ j) p = p := by
    intro j
    induction j with
    | zero => rw [pow_zero, Module.End.one_apply]
    | succ j ih => rw [pow_succ', Module.End.mul_apply, ih, hSp]
  have hTpow : ∀ (j : ℕ) (x : ∀ k, E k), (T ^ j) (T x) = T ((T ^ j) x) := by
    intro j x
    rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply]

  have hex : ∀ k, ∃ y : E k, u k y = p k := fun k => by
    have : p k ∈ LinearMap.range (u k) := by rw [hur k]; exact hpθ k
    exact this
  choose e' he' using hex
  have hUe' : U e' = p := funext fun k => by rw [hU]; exact he' k
  have hTe : T ((T ^ c) e') = (T ^ c) e' := by
    have h1 : (T ^ c) (T e' - e') = 0 := hvanish _ (by rw [map_sub, hUT, hUe', hSp, sub_self])
    rw [map_sub, sub_eq_zero, hTpow] at h1
    exact h1
  have hUe : U ((T ^ c) e') = p := by rw [hUTi, hUe', hSpi]
  refine ⟨(T ^ c) e', ⟨fun k => ?_, fun k => ?_⟩, ?_⟩
  · have := congrFun hTe k
    rw [hT] at this
    exact this
  · have := congrFun hUe k
    rw [hU] at this
    exact this

  · rintro e₂ ⟨h₂c, h₂u⟩
    have hTd : T (e₂ - (T ^ c) e') = e₂ - (T ^ c) e' := by
      rw [map_sub, hTe]
      congr 1
      funext k; rw [hT]; exact h₂c k
    have hUd : U (e₂ - (T ^ c) e') = 0 := by
      rw [map_sub, hUe, sub_eq_zero]
      funext k; rw [hU]; exact h₂u k
    have hfix : ∀ j : ℕ, (T ^ j) (e₂ - (T ^ c) e') = e₂ - (T ^ c) e' := by
      intro j
      induction j with
      | zero => rw [pow_zero, Module.End.one_apply]
      | succ j ih => rw [pow_succ', Module.End.mul_apply, ih, hTd]
    have := hvanish _ hUd
    rw [hfix] at this
    exact sub_eq_zero.mp this

end S_Module_existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul
end P2MW
export P2MW.S_Module_existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul (solution)
