-- Prove2me | solution 1 for GroundTheory.Automorphic.CuspidalSpectrum.exists_ncard_ratGLBox_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:42:51.128802+00:00
-- url     : https://prove2.me/submissions/d2521107-2349-4dcf-af68-4005ccd8df7e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalDiscreteness_Counting
import Theorems.Thm_GroundTheory_Automorphic_CuspidalSpectrum_exists_natCast_mul_integral_of_isCompact
import Theorems.Thm_GroundTheory_Automorphic_CuspidalSpectrum_exists_ncard_integers_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Set
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.CuspidalSpectrum
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace GroundTheory.Automorphic.CuspidalSpectrum
theorem _root_.solution (n : ℕ) {𝒦 : Set (FiniteAdeleRing (𝓞 K) K)} (h𝒦 : IsCompact 𝒦) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ T : ℝ, 0 ≤ T →
      (ratGLBox n 𝒦 T).Finite ∧ ((ratGLBox n 𝒦 T).ncard : ℝ) ≤ C * (1 + T) ^ N := by
  classical
  obtain ⟨m, hm, hmint⟩ := exists_natCast_mul_integral_of_isCompact K h𝒦
  obtain ⟨C₂, hC₂, hcount⟩ := exists_ncard_integers_le K
  set d := Module.finrank ℚ K
  refine ⟨(C₂ * (m : ℝ) ^ d) ^ (n * n), d * (n * n), fun T hT => ?_⟩
  have hmT : 0 ≤ (m : ℝ) * T := by positivity
  obtain ⟨hfinS, hcardS⟩ := hcount (m * T) hmT
  set F := hfinS.toFinset
  set Φ : GL (Fin n) K → Fin n → Fin n → 𝓞 K := fun γ i j =>
    if h : ∃ z : 𝓞 K, (z : K) = m * (γ : Matrix (Fin n) (Fin n) K) i j then h.choose else 0
  set box : Finset (Fin n → Fin n → 𝓞 K) := Fintype.piFinset fun _ => Fintype.piFinset fun _ => F
  have hΦ : ∀ γ ∈ ratGLBox n 𝒦 T, ∀ i j,
      ((Φ γ i j : 𝓞 K) : K) = m * (γ : Matrix (Fin n) (Fin n) K) i j := by
    intro γ hγ i j
    have h := hmint _ (hγ i j).1
    simp only [Φ, dif_pos h]
    exact h.choose_spec
  have hmaps : ∀ γ ∈ ratGLBox n 𝒦 T, Φ γ ∈ (box : Set (Fin n → Fin n → 𝓞 K)) := by
    intro γ hγ
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [Fintype.mem_piFinset]
    intro j
    rw [Set.Finite.mem_toFinset]
    intro w
    rw [hΦ γ hγ i j, map_mul, InfinitePlace.map_natCast]
    exact mul_le_mul_of_nonneg_left ((hγ i j).2 w) (Nat.cast_nonneg m)
  have hinj : InjOn Φ (ratGLBox n 𝒦 T) := by
    intro γ hγ γ' hγ' h
    refine Units.ext (Matrix.ext fun i j => ?_)
    have h1 := hΦ γ hγ i j
    have h2 := hΦ γ' hγ' i j
    rw [show Φ γ i j = Φ γ' i j from congrFun (congrFun h i) j, h2] at h1
    have hm0 : (m : K) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    exact (mul_left_cancel₀ hm0 h1).symm
  have hfin : (box : Set (Fin n → Fin n → 𝓞 K)).Finite := Finset.finite_toSet _
  refine ⟨hfin.of_injOn hmaps hinj, ?_⟩
  have hcard := Set.ncard_le_ncard_of_injOn Φ hmaps hinj hfin
  rw [Set.ncard_coe_finset] at hcard
  simp only [box, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hcard
  have hF : (F.card : ℝ) ≤ C₂ * (m : ℝ) ^ d * (1 + T) ^ d := by
    rw [← Set.ncard_eq_toFinset_card _ hfinS]
    refine hcardS.trans ?_
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have : 1 + (m : ℝ) * T ≤ m * (1 + T) := by nlinarith
    calc C₂ * (1 + (m : ℝ) * T) ^ d ≤ C₂ * ((m : ℝ) * (1 + T)) ^ d := by gcongr
      _ = C₂ * (m : ℝ) ^ d * (1 + T) ^ d := by rw [mul_pow]; ring
  calc ((ratGLBox n 𝒦 T).ncard : ℝ) ≤ (((F.card ^ n) ^ n : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (F.card : ℝ) ^ (n * n) := by push_cast; rw [← pow_mul]
    _ ≤ (C₂ * (m : ℝ) ^ d * (1 + T) ^ d) ^ (n * n) := by gcongr
    _ = (C₂ * (m : ℝ) ^ d) ^ (n * n) * (1 + T) ^ (d * (n * n)) := by rw [mul_pow, ← pow_mul]
end GroundTheory.Automorphic.CuspidalSpectrum
