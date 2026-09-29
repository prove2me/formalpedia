-- Prove2me | solution 1 for ModularCurve.MTorsionNeBot.of_surjective_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/d46c6440-1631-5fde-aafc-14f3dd76fad8

import Definitions.Def_HeckeGalois_EichlerShimura
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Finiteness.Nakayama
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MTorsionNeBot_of_surjective_of_finite

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_MTorsionNeBot_of_surjective_of_finite.ModularCurve"

private theorem exists_ne_zero_smul_eq_zero_of_pow_smul_eq_zero {𝕋 : Type*} [CommRing 𝕋]
    {N : Type*} [AddCommGroup N] [Module 𝕋 N] (𝔪 : Ideal 𝕋) (n : ℕ) :
    ∀ m : N, m ≠ 0 → (∀ t ∈ 𝔪 ^ n, t • m = 0) → ∃ x : N, x ≠ 0 ∧ ∀ t ∈ 𝔪, t • x = 0 := by
  induction n with
  | zero =>
    intro m hm h
    exfalso
    apply hm
    have h1 : (1 : 𝕋) ∈ 𝔪 ^ 0 := by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
    simpa using h 1 h1
  | succ n ih =>
    intro m hm h
    by_cases hn : ∀ t ∈ 𝔪 ^ n, t • m = 0
    · exact ih m hm hn
    · obtain ⟨s, hs, hsm⟩ : ∃ s ∈ 𝔪 ^ n, s • m ≠ 0 := by
        by_contra hc
        exact hn fun t ht => by_contra fun h' => hc ⟨t, ht, h'⟩
      refine ⟨s • m, hsm, fun t ht => ?_⟩
      rw [smul_smul]
      exact h (t * s) (by rw [pow_succ']; exact Ideal.mul_mem_mul ht hs)

private theorem exists_ne_zero_pow_smul_eq_zero_of_surjective {𝕋 : Type*} [CommRing 𝕋]
    {N N'' : Type*} [AddCommGroup N] [Module 𝕋 N] [AddCommGroup N''] [Module 𝕋 N''] (𝔪 : Ideal 𝕋)
    [Finite N] (f : N →ₗ[𝕋] N'') (x₀ : N) (hy0 : f x₀ ≠ 0) (hy : ∀ t ∈ 𝔪, t • f x₀ = 0) :
    ∃ (n : ℕ) (m : N), m ≠ 0 ∧ ∀ t ∈ 𝔪 ^ n, t • m = 0 := by
  haveI : IsArtinian 𝕋 N := isArtinian_of_finite
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes (R := 𝕋) (M := N)
    ⟨fun i => OrderDual.toDual (𝔪 ^ i • (⊤ : Submodule 𝕋 N)),
      fun i j hij => Submodule.smul_mono_left (Ideal.pow_le_pow_right hij)⟩
  have hstab : 𝔪 ^ n • (⊤ : Submodule 𝕋 N) = 𝔪 ^ (n + 1) • (⊤ : Submodule 𝕋 N) :=
    hn (n + 1) (Nat.le_succ n)
  have hle : 𝔪 ^ n • (⊤ : Submodule 𝕋 N) ≤ 𝔪 • (𝔪 ^ n • (⊤ : Submodule 𝕋 N)) := by
    rw [← Submodule.mul_smul, ← pow_succ', ← hstab]
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪
    (𝔪 ^ n • (⊤ : Submodule 𝕋 N)) (IsNoetherian.noetherian _) hle
  refine ⟨n, r • x₀, fun hz => hy0 ?_, fun t ht => ?_⟩
  · have h1 : (r - 1) • f x₀ = 0 := hy (r - 1) hr1
    rw [sub_smul, one_smul, sub_eq_zero] at h1
    rw [← h1, ← map_smul, hz, map_zero]
  · rw [smul_smul, mul_comm, ← smul_smul]
    exact hr (t • x₀) (Submodule.smul_mem_smul ht Submodule.mem_top)

namespace ModularCurve p2m_export "ModularCurve" "MTorsionNeBot" namespace MTorsionNeBot end ModularCurve.MTorsionNeBot
p2m_open_scoped "ModularCurve" in
private theorem ModularCurve.MTorsionNeBot.of_surjective_of_finite_impl {𝕋 : Type*} [CommRing 𝕋]
    {N N'' : Type*} [AddCommGroup N] [Module 𝕋 N] [AddCommGroup N''] [Module 𝕋 N''] (𝔪 : Ideal 𝕋)
    [Finite N] (f : N →ₗ[𝕋] N'') (hf : Function.Surjective f) :
    MTorsionNeBot 𝕋 N'' 𝔪 → MTorsionNeBot 𝕋 N 𝔪 := by
  intro h
  unfold MTorsionNeBot at h ⊢
  rw [Submodule.ne_bot_iff] at h ⊢
  obtain ⟨y, hy, hy0⟩ := h
  rw [Submodule.mem_torsionBySet_iff] at hy
  obtain ⟨x₀, rfl⟩ := hf y
  obtain ⟨n, m, hm0, hm⟩ := exists_ne_zero_pow_smul_eq_zero_of_surjective 𝔪 f x₀ hy0
    (fun t ht => hy ⟨t, ht⟩)
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_smul_eq_zero_of_pow_smul_eq_zero 𝔪 n m hm0 hm
  exact ⟨x, (Submodule.mem_torsionBySet_iff _ _).2 (fun a => hx a.1 a.2), hx0⟩

theorem solution {𝕋 : Type*} [CommRing 𝕋]
    {N N'' : Type*} [AddCommGroup N] [Module 𝕋 N] [AddCommGroup N''] [Module 𝕋 N''] (𝔪 : Ideal 𝕋)
    [Finite N] (f : N →ₗ[𝕋] N'') (hf : Function.Surjective f) :
    MTorsionNeBot 𝕋 N'' 𝔪 → MTorsionNeBot 𝕋 N 𝔪 :=
  ModularCurve.MTorsionNeBot.of_surjective_of_finite_impl 𝔪 f hf

end S_ModularCurve_MTorsionNeBot_of_surjective_of_finite
end P2MW
export P2MW.S_ModularCurve_MTorsionNeBot_of_surjective_of_finite (solution)
