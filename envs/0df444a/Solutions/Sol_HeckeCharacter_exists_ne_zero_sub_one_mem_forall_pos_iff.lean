-- Prove2me | solution 1 for HeckeCharacter.exists_ne_zero_sub_one_mem_forall_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/c620efeb-5bed-54c3-a44a-e2fd2497b0cd

import Mathlib
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCharacter_exists_ne_zero_sub_one_mem_forall_pos_iff

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors

namespace WAsgnAux

variable (K : Type*) [Field K] [NumberField K]

omit [NumberField K] in

theorem ringEquivRealOfIsReal_algebraMap_infiniteAdeleRing (τ : K →+* ℝ) (x : K) :
    InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_placeOf K τ)
      ((algebraMap K (InfiniteAdeleRing K) x) (placeOf K τ)) = τ x := by
  rw [InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply]
  simp only [placeOf, InfinitePlace.embedding_mk_eq_of_isReal (isReal_compOfRealHom K τ)]
  rfl

theorem exists_forall_abs_sub_lt_one (s : (K →+* ℝ) → ℝ) :
    ∃ x : K, ∀ τ : K →+* ℝ, |τ x - s τ| < 1 := by
  classical
  let t : InfiniteAdeleRing K := fun w =>
    if hw : w.IsReal then (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm (s (InfinitePlace.embedding_of_isReal hw))
    else 0
  obtain ⟨x, hx⟩ := (InfiniteAdeleRing.denseRange_algebraMap K).exists_mem_open
    (isOpen_set_pi Set.finite_univ fun w _ => Metric.isOpen_ball :
      IsOpen (Set.pi Set.univ fun w : InfinitePlace K => Metric.ball (t w) 1))
    ⟨t, fun w _ => Metric.mem_ball_self one_pos⟩
  refine ⟨x, fun τ => ?_⟩
  have hw := isReal_placeOf K τ
  have h := hx (placeOf K τ) (Set.mem_univ _)
  rw [Metric.mem_ball] at h
  have hiso := InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw
  rw [← hiso.dist_eq, ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply, ringEquivRealOfIsReal_algebraMap_infiniteAdeleRing] at h
  simp only [t, dif_pos hw, RingEquiv.apply_symm_apply] at h
  have hτ : InfinitePlace.embedding_of_isReal hw = τ := by
    ext y
    have := ringEquivRealOfIsReal_algebraMap_infiniteAdeleRing K τ y
    rw [InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe] at this
    simpa using this
  rw [hτ, Real.dist_eq] at h
  exact h

end WAsgnAux

open WAsgnAux in
theorem solution
    (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥) (ε : (K →+* ℝ) → Prop) :
    ∃ β : 𝓞 K, β ≠ 0 ∧ β - 1 ∈ 𝔣 ∧ ∀ τ : K →+* ℝ, (0 < τ (β : K) ↔ ε τ) := by
  classical
  rcases isEmpty_or_nonempty (K →+* ℝ) with hE | hE
  · exact ⟨1, one_ne_zero, by simp, fun τ => (IsEmpty.false τ).elim⟩

  obtain ⟨x, hx⟩ := exists_forall_abs_sub_lt_one K fun τ => if ε τ then 2 else -2
  have hxpos : ∀ τ : K →+* ℝ, ε τ → 1 < τ x := by
    intro τ hε; have h := hx τ; rw [if_pos hε] at h; have := (abs_lt.mp h).1; linarith
  have hxneg : ∀ τ : K →+* ℝ, ¬ ε τ → τ x < -1 := by
    intro τ hε; have h := hx τ; rw [if_neg hε] at h; have := (abs_lt.mp h).2; linarith
  have hx0 : ∀ τ : K →+* ℝ, 1 ≤ |τ x| := by
    intro τ
    by_cases hε : ε τ
    · exact le_trans (hxpos τ hε).le (le_abs_self _)
    · have := hxneg τ hε
      rw [abs_of_neg (by linarith)]; linarith

  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hb0 : (b : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : ((b : 𝓞 K) : K) ≠ 0 := fun h => hb0 (by exact_mod_cast h)
  have hg : ((b : 𝓞 K) : K) * ((a : 𝓞 K) : K) = (b : K) ^ 2 * x := by
    rw [← hab]
    change (b : K) * (a : K) = (b : K) ^ 2 * ((a : K) / (b : K))
    field_simp

  have hm : ((Ideal.absNorm 𝔣 : ℕ) : 𝓞 K) ∈ 𝔣 := Ideal.absNorm_mem 𝔣
  have hm0 : (Ideal.absNorm 𝔣 : ℕ) ≠ 0 := fun h => h𝔣 (Ideal.absNorm_eq_zero_iff.mp h)
  have hm1 : (1 : ℝ) ≤ (Ideal.absNorm 𝔣 : ℕ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0

  have hq : ∀ τ : K →+* ℝ, 0 < (τ b) ^ 2 * |τ x| := by
    intro τ
    have hτb : (τ b : ℝ) ≠ 0 := (map_ne_zero τ).mpr hbK
    have : 0 < (τ b) ^ 2 := by positivity
    exact mul_pos this (by linarith [hx0 τ])
  obtain ⟨N, hN⟩ := exists_nat_gt (∑ τ : K →+* ℝ, ((τ b) ^ 2 * |τ x|)⁻¹)
  have hN' : ∀ τ : K →+* ℝ, 1 < (N : ℝ) * ((τ b) ^ 2 * |τ x|) := by
    intro τ
    have h1 : ((τ b) ^ 2 * |τ x|)⁻¹ < N :=
      lt_of_le_of_lt (Finset.single_le_sum (fun τ' _ => (inv_pos.mpr (hq τ')).le) (Finset.mem_univ τ)) hN
    have h2 := mul_lt_mul_of_pos_right h1 (hq τ)
    rwa [inv_mul_cancel₀ (hq τ).ne'] at h2

  set m : ℕ := Ideal.absNorm 𝔣 with hm_def
  refine ⟨1 + (N : 𝓞 K) * (m : 𝓞 K) * (b * a), ?_, ?_, ?_⟩
  rotate_left
  · rw [add_sub_cancel_left]
    exact 𝔣.mul_mem_right _ (𝔣.mul_mem_left _ hm)
  ·
    have hval : ∀ τ : K →+* ℝ, τ (((1 + (N : 𝓞 K) * (m : 𝓞 K) * (b * a) : 𝓞 K)) : K) =
        1 + (N : ℝ) * m * ((τ b) ^ 2 * τ x) := by
      intro τ
      push_cast
      rw [hg]
      simp only [map_add, map_one, map_mul, map_natCast, map_pow]
    intro τ
    rw [hval τ]
    by_cases hε : ε τ
    · refine ⟨fun _ => hε, fun _ => ?_⟩
      have h1 := hxpos τ hε
      have : 0 ≤ (N : ℝ) * m * ((τ b) ^ 2 * τ x) := by positivity
      linarith
    · refine ⟨fun h => absurd h ?_, fun h => absurd h hε⟩
      have h1 := hxneg τ hε
      have habs : |τ x| = -τ x := abs_of_neg (by linarith)
      have h2 := hN' τ
      rw [habs] at h2
      have h3 : (N : ℝ) * ((τ b) ^ 2 * -τ x) ≤ (N : ℝ) * m * ((τ b) ^ 2 * -τ x) := by
        have h4 : 0 ≤ (N : ℝ) * ((τ b) ^ 2 * -τ x) := by linarith
        calc (N : ℝ) * ((τ b) ^ 2 * -τ x) = 1 * ((N : ℝ) * ((τ b) ^ 2 * -τ x)) := by ring
          _ ≤ (m : ℝ) * ((N : ℝ) * ((τ b) ^ 2 * -τ x)) := mul_le_mul_of_nonneg_right hm1 h4
          _ = (N : ℝ) * m * ((τ b) ^ 2 * -τ x) := by ring
      intro hpos
      nlinarith
  ·
    obtain ⟨τ₀⟩ := hE
    intro h0
    have hval0 : τ₀ (((1 + (N : 𝓞 K) * (m : 𝓞 K) * (b * a) : 𝓞 K)) : K) = 0 := by rw [h0]; simp
    have hv : τ₀ (((1 + (N : 𝓞 K) * (m : 𝓞 K) * (b * a) : 𝓞 K)) : K) = 1 + (N : ℝ) * m * ((τ₀ b) ^ 2 * τ₀ x) := by
      push_cast
      rw [hg]
      simp only [map_add, map_one, map_mul, map_natCast, map_pow]
    rw [hv] at hval0
    by_cases hε : ε τ₀
    · have h1 := hxpos τ₀ hε
      have : 0 ≤ (N : ℝ) * m * ((τ₀ b) ^ 2 * τ₀ x) := by positivity
      linarith
    · have h1 := hxneg τ₀ hε
      have habs : |τ₀ x| = -τ₀ x := abs_of_neg (by linarith)
      have h2 := hN' τ₀
      rw [habs] at h2
      have h4 : 0 ≤ (N : ℝ) * ((τ₀ b) ^ 2 * -τ₀ x) := by linarith
      have h3 : (N : ℝ) * ((τ₀ b) ^ 2 * -τ₀ x) ≤ (N : ℝ) * m * ((τ₀ b) ^ 2 * -τ₀ x) := by
        calc (N : ℝ) * ((τ₀ b) ^ 2 * -τ₀ x) = 1 * ((N : ℝ) * ((τ₀ b) ^ 2 * -τ₀ x)) := by ring
          _ ≤ (m : ℝ) * ((N : ℝ) * ((τ₀ b) ^ 2 * -τ₀ x)) := mul_le_mul_of_nonneg_right hm1 h4
          _ = (N : ℝ) * m * ((τ₀ b) ^ 2 * -τ₀ x) := by ring
      nlinarith

end S_HeckeCharacter_exists_ne_zero_sub_one_mem_forall_pos_iff
end P2MW
export P2MW.S_HeckeCharacter_exists_ne_zero_sub_one_mem_forall_pos_iff (solution)
