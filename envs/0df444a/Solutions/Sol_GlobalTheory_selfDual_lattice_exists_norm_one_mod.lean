-- Prove2me | solution 1 for GlobalTheory.selfDual_lattice_exists_norm_one_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:42:19.607502+00:00
-- url     : https://prove2.me/submissions/465f8afb-00f6-495a-b76c-960344c88fdd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SelfDualHermitianLatticeExistsNormOneMod
import Theorems.Thm_GlobalTheory_padicNorm_of_sq_add_prime_mul_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) (p d : ℕ) (θ : K) (O : Subring K) (L : AddSubgroup V), p.Prime → d.Prime → θ ^ 2 = -(d : K) → σ θ = -θ → (∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * θ) → (∀ x ∈ O, σ x ∈ O) → (1 + θ) / 2 ∈ O → (∀ r : ℚ, (r : K) ∈ O ↔ padicNorm p r ≤ 1) → (∀ x y : V, h y x = σ (h x y)) → (∀ x : V, h x x = 0 → x = 0) → (∀ a ∈ O, ∀ x ∈ L, a • x ∈ L) → (∀ x ∈ L, ∀ y ∈ L, h x y ∈ O) → (∀ x : V, ∃ m : ℕ, (p : K) ^ m • x ∈ L) → (∀ u v : ℚ, padicNorm p u = 1 → padicNorm p v = 1 → ∃ a b : ℤ, padicNorm p (u * (a : ℚ) ^ 2 + v * (b : ℚ) ^ 2 - 1) < 1) → (∀ W : Submodule K V, (∀ x ∈ W, (∀ y ∈ L, y ∈ W → h x y ∈ O) → x ∈ L) → (∃ x ∈ W, x ≠ 0) → ∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧ padicNorm p u = 1) → ∀ W : Submodule K V, (∀ x ∈ W, (∀ y ∈ L, y ∈ W → h x y ∈ O) → x ∈ L) → (∃ e ∈ W, h e e = 1) → ∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧ padicNorm p (u - 1) < 1 := by
  intro K V _ _ _ _ σ h p d θ O L hp hd hθ hσθ hK hσO hω hO hh hdef hL hLO hbig hab hun W hW
    ⟨e, heW, he⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at he
  obtain ⟨y1, hy1L, hy1W, u1, hu1, hu1n⟩ := hun W hW ⟨e, heW, he0⟩
  have hu10 : u1 ≠ 0 := by
    rintro rfl
    simp at hu1n
  have hu10K : (u1 : K) ≠ 0 := by exact_mod_cast hu10
  have hinv : (u1 : K)⁻¹ ∈ O := by
    have : ((u1⁻¹ : ℚ) : K) ∈ O := by
      rw [hO, ← one_div, padicNorm.div, hu1n]
      simp
    simpa using this
  have hθO : θ ∈ O := by
    have h2 : θ = (1 + θ) / 2 + (1 + θ) / 2 - 1 := by ring
    rw [h2]
    exact O.sub_mem (O.add_mem hω hω) O.one_mem
  have hperp : ∀ y : V, h (y - (h y y1 * (u1 : K)⁻¹) • y1) y1 = 0 := by
    intro y
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hu1]
    field_simp
    ring
  have hnorm : ∀ s t : ℚ, h (((s : K) + (t : K) * θ) • y1) (((s : K) + (t : K) * θ) • y1)
      = (((s ^ 2 + (d : ℚ) * t ^ 2) * u1 : ℚ) : K) := by
    intro s t
    simp only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, hu1, map_add,
      map_mul, map_ratCast, hσθ]
    push_cast
    linear_combination (-(t : K) ^ 2 * (u1 : K)) * hθ
  set W' : Submodule K V := W ⊓ LinearMap.ker (h.flip y1) with hW'
  have hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ h x y1 = 0 := by
    intro x
    simp [hW']
  by_cases hne : ∃ x ∈ W', x ≠ 0
  · have hsd : ∀ x ∈ W', (∀ y ∈ L, y ∈ W' → h x y ∈ O) → x ∈ L := by
      intro x hx hxO
      obtain ⟨hxW, hx1⟩ := (hmem x).1 hx
      refine hW x hxW fun y hyL hyW => ?_
      have := hxO (y - (h y y1 * (u1 : K)⁻¹) • y1)
        (L.sub_mem hyL (hL _ (O.mul_mem (hLO _ hyL _ hy1L) hinv) _ hy1L))
        ((hmem _).2 ⟨W.sub_mem hyW (W.smul_mem _ hy1W), hperp y⟩)
      simpa [map_sub, LinearMap.map_smulₛₗ, hx1] using this
    obtain ⟨y2, hy2L, hy2W', u2, hu2, hu2n⟩ := hun W' hsd hne
    obtain ⟨hy2W, h21⟩ := (hmem y2).1 hy2W'
    have h12 : h y1 y2 = 0 := by rw [hh, h21, map_zero]
    obtain ⟨a, b, hab'⟩ := hab u1 u2 hu1n hu2n
    refine ⟨(a : K) • y1 + (b : K) • y2,
      L.add_mem (hL _ (intCast_mem O a) _ hy1L) (hL _ (intCast_mem O b) _ hy2L),
      W.add_mem (W.smul_mem _ hy1W) (W.smul_mem _ hy2W), _, ?_, hab'⟩
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.map_smulₛₗ, smul_eq_mul, hu1, hu2, h12, h21, map_intCast]
    push_cast
    ring
  · by_cases hpd : p = d
    · subst hpd
      have h0 : e - (h e y1 * (u1 : K)⁻¹) • y1 = 0 := by
        by_contra hc
        exact hne ⟨_, (hmem _).2 ⟨W.sub_mem heW (W.smul_mem _ hy1W), hperp e⟩, hc⟩
      obtain ⟨s, t, hst⟩ := hK (h e y1 * (u1 : K)⁻¹)
      rw [hst, sub_eq_zero] at h0
      have h1 := hnorm s t
      rw [← h0, he] at h1
      have h2 : (s ^ 2 + (p : ℚ) * t ^ 2) * u1 = 1 := by exact_mod_cast h1.symm
      have h3 : padicNorm p (s ^ 2 + (p : ℚ) * t ^ 2) = 1 := by
        have := congrArg (padicNorm p) h2
        rwa [padicNorm.mul, hu1n, mul_one, padicNorm.one] at this
      obtain ⟨hs, ht⟩ := padicNorm_of_sq_add_prime_mul_sq p s t h3
      have h4 := hnorm s 0
      refine ⟨_, hL _ ?_ _ hy1L, W.smul_mem _ hy1W, _, h4, ?_⟩
      · simpa using (hO s).2 hs
      · have : (s ^ 2 + (p : ℚ) * 0 ^ 2) * u1 - 1 = -((p : ℚ) * t ^ 2 * u1) := by
          linear_combination h2
        rw [this, padicNorm.neg, padicNorm.mul, hu1n, mul_one]
        exact ht
    · haveI : Fact d.Prime := ⟨hd⟩
      have hdn : padicNorm p (d : ℚ) = 1 := padicNorm.padicNorm_of_prime_of_ne hpd
      obtain ⟨a, b, hab'⟩ := hab u1 (u1 * d) hu1n (by rw [padicNorm.mul, hu1n, hdn, mul_one])
      have h4 := hnorm a b
      refine ⟨_, hL _ ?_ _ hy1L, W.smul_mem _ hy1W, _, h4, ?_⟩
      · push_cast
        exact O.add_mem (intCast_mem O a) (O.mul_mem (intCast_mem O b) hθO)
      · convert hab' using 2
        ring
end GlobalTheory
