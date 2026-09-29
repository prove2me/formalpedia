-- Prove2me | solution 1 for NumberField.exists_ne_zero_and_sub_one_mem_and_lt_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d2afd10c-14d2-5268-a200-f038d9432202

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_ne_zero_and_sub_one_mem_and_lt_zero_iff

open NumberField

namespace SignApproxSol

theorem exists_pos_forall_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 < f i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, δ ≤ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
    obtain ⟨δ, hδ, h⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine ⟨min δ (f a), lt_min hδ (hf a (Finset.mem_insert_self a s)), fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h i hi)

variable {K : Type*} [Field K] [NumberField K]

theorem realEmb_eq_of_apply_gen_eq {φ φ' : K →+* ℝ}
    (h : φ (Field.powerBasisOfFiniteOfSeparable ℚ K).gen =
      φ' (Field.powerBasisOfFiniteOfSeparable ℚ K).gen) : φ = φ' := by
  have h' : φ.toRatAlgHom = φ'.toRatAlgHom := by
    apply PowerBasis.algHom_ext (Field.powerBasisOfFiniteOfSeparable ℚ K)
    rw [RingHom.toRatAlgHom_apply, RingHom.toRatAlgHom_apply, h]
  have := congrArg (fun f : K →ₐ[ℚ] ℝ => (f : K →+* ℝ)) h'
  simpa [RingHom.toRatAlgHom_toRingHom] using this

theorem exists_lt_zero_iff_eq (φ₀ : K →+* ℝ) :
    ∃ β : K, ∀ φ : K →+* ℝ, (φ β < 0 ↔ φ = φ₀) ∧ φ β ≠ 0 := by
  classical
  set θ : K := (Field.powerBasisOfFiniteOfSeparable ℚ K).gen with hθ
  set t : (K →+* ℝ) → ℝ := fun φ => φ θ with ht
  have hinj : ∀ φ φ' : K →+* ℝ, t φ = t φ' → φ = φ' := fun φ φ' h => realEmb_eq_of_apply_gen_eq h

  obtain ⟨δ, hδ, hδle⟩ := exists_pos_forall_le (Finset.univ.filter fun φ : K →+* ℝ => φ ≠ φ₀)
    (fun φ => |t φ - t φ₀|) (fun φ hφ => by
      rw [Finset.mem_filter] at hφ
      exact abs_pos.mpr (sub_ne_zero.mpr (fun h => hφ.2 (hinj _ _ h))))
  have hfar : ∀ φ : K →+* ℝ, φ ≠ φ₀ → δ ≤ |t φ - t φ₀| := fun φ hφ =>
    hδle φ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hφ⟩)
  obtain ⟨r₁, hr₁l, hr₁r⟩ := exists_rat_btwn (show t φ₀ - δ < t φ₀ by linarith)
  obtain ⟨r₂, hr₂l, hr₂r⟩ := exists_rat_btwn (show t φ₀ < t φ₀ + δ by linarith)
  refine ⟨(θ - (r₁ : K)) * (θ - (r₂ : K)), fun φ => ?_⟩
  have hval : φ ((θ - (r₁ : K)) * (θ - (r₂ : K))) = (t φ - r₁) * (t φ - r₂) := by
    rw [map_mul, map_sub, map_sub, map_ratCast, map_ratCast]
  rw [hval]
  by_cases hφ : φ = φ₀
  · subst hφ
    refine ⟨⟨fun _ => rfl, fun _ => mul_neg_of_pos_of_neg (by linarith) (by linarith)⟩, ?_⟩
    exact (mul_neg_of_pos_of_neg (by linarith) (by linarith)).ne
  · have hd := hfar φ hφ
    have hpos : 0 < (t φ - r₁) * (t φ - r₂) := by
      rcases le_abs'.mp hd with h | h
      ·
        exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
      · exact mul_pos (by linarith) (by linarith)
    exact ⟨⟨fun h => absurd h (not_lt.mpr hpos.le), fun h => absurd h hφ⟩, hpos.ne'⟩

theorem exists_lt_zero_iff_mem (N : Finset (K →+* ℝ)) :
    ∃ β : K, ∀ φ : K →+* ℝ, (φ β < 0 ↔ φ ∈ N) ∧ φ β ≠ 0 := by
  classical
  choose b hb using fun φ₀ : K →+* ℝ => exists_lt_zero_iff_eq φ₀
  refine ⟨∏ φ₀ ∈ N, b φ₀, ?_⟩
  induction N using Finset.induction_on with
  | empty =>
    intro φ
    simp
  | insert a s ha ih =>
    intro φ
    rw [Finset.prod_insert ha, map_mul]
    obtain ⟨hiff, hne⟩ := ih φ
    obtain ⟨haiff, hane⟩ := hb a φ
    refine ⟨?_, mul_ne_zero hane hne⟩
    by_cases hφ : φ = a
    · have hneg : φ (b a) < 0 := haiff.mpr hφ
      have hns : ¬ φ ∈ s := fun h => ha (hφ ▸ h)
      have hpos : 0 < φ (∏ φ₀ ∈ s, b φ₀) :=
        lt_of_le_of_ne (not_lt.mp (fun h => hns (hiff.mp h))) hne.symm
      exact ⟨fun _ => Finset.mem_insert.mpr (Or.inl hφ), fun _ => mul_neg_of_neg_of_pos hneg hpos⟩
    · have hpos : 0 < φ (b a) := lt_of_le_of_ne (not_lt.mp (fun h => hφ (haiff.mp h))) hane.symm
      rw [Finset.mem_insert]
      constructor
      · intro h
        right
        exact hiff.mp ((pos_iff_neg_of_mul_neg h).mp hpos)
      · rintro (h | h)
        · exact absurd h hφ
        · exact mul_neg_of_pos_of_neg hpos (hiff.mpr h)

theorem exists_integer_lt_zero_iff_mem (N : Finset (K →+* ℝ)) :
    ∃ γ : 𝓞 K, ∀ φ : K →+* ℝ, (φ (algebraMap (𝓞 K) K γ) < 0 ↔ φ ∈ N) ∧
      φ (algebraMap (𝓞 K) K γ) ≠ 0 := by
  obtain ⟨β, hβ⟩ := exists_lt_zero_iff_mem N
  have halg : IsAlgebraic ℤ β :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic β)
  obtain ⟨d, hd0, hint⟩ := halg.exists_integral_multiple
  have hint2 : IsIntegral ℤ ((d * d : ℤ) • β) := by
    rw [mul_smul]
    exact hint.smul d
  refine ⟨⟨(d * d : ℤ) • β, hint2⟩, fun φ => ?_⟩
  have hval : φ (algebraMap (𝓞 K) K ⟨(d * d : ℤ) • β, hint2⟩) = ((d * d : ℤ) : ℝ) * φ β := by
    change φ ((d * d : ℤ) • β) = _
    rw [zsmul_eq_mul, map_mul, map_intCast]
  have hdd : (0 : ℝ) < ((d * d : ℤ) : ℝ) := by
    have : (0 : ℤ) < d * d := mul_self_pos.mpr hd0
    exact_mod_cast this
  rw [hval]
  refine ⟨?_, mul_ne_zero hdd.ne' (hβ φ).2⟩
  rw [mul_neg_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact (hβ φ).1.mp h
    · exact absurd h (not_lt.mpr hdd.le)
  · intro h
    exact Or.inl ⟨hdd, (hβ φ).1.mpr h⟩

theorem main (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥) (N : Finset (K →+* ℝ)) :
    ∃ α : 𝓞 K, α ≠ 0 ∧ α - 1 ∈ 𝔪 ∧
      ∀ φ : K →+* ℝ, φ (algebraMap (𝓞 K) K α) < 0 ↔ φ ∈ N := by
  classical
  rcases isEmpty_or_nonempty (K →+* ℝ) with hK | hK
  · exact ⟨1, one_ne_zero, by simp, fun φ => (IsEmpty.false φ).elim⟩
  obtain ⟨γ, hγ⟩ := exists_integer_lt_zero_iff_mem N

  set n : ℕ := Ideal.absNorm 𝔪 with hn
  have hnmem : (n : 𝓞 K) ∈ 𝔪 := Ideal.absNorm_mem 𝔪
  have hn0 : n ≠ 0 := by
    rw [hn]
    exact Ideal.absNorm_eq_zero_iff.not.mpr h𝔪
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0

  obtain ⟨δ, hδ, hδle⟩ := exists_pos_forall_le (Finset.univ : Finset (K →+* ℝ))
    (fun φ => (n : ℝ) * |φ (algebraMap (𝓞 K) K γ)|)
    (fun φ _ => mul_pos hnpos (abs_pos.mpr (hγ φ).2))
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / δ)
  have hMδ : 1 < (M : ℝ) * δ := by
    have := (div_lt_iff₀ hδ).mp hM
    linarith
  refine ⟨1 + ((M * n : ℕ) : 𝓞 K) * γ, ?_, ?_, ?_⟩
  ·
    obtain ⟨φ⟩ := hK
    intro h0
    have h1 : φ (algebraMap (𝓞 K) K (1 + ((M * n : ℕ) : 𝓞 K) * γ)) = 0 := by
      rw [h0, map_zero, map_zero]
    simp only [map_add, map_one, map_mul, map_natCast] at h1
    have hb : 1 < (M : ℝ) * ((n : ℝ) * |φ (algebraMap (𝓞 K) K γ)|) :=
      hMδ.trans_le (mul_le_mul_of_nonneg_left (hδle φ (Finset.mem_univ _)) (Nat.cast_nonneg M))
    rcases lt_or_gt_of_ne (hγ φ).2 with hneg | hpos
    · rw [abs_of_neg hneg] at hb
      have : ((M * n : ℕ) : ℝ) * φ (algebraMap (𝓞 K) K γ) < -1 := by push_cast; nlinarith
      linarith
    · rw [abs_of_pos hpos] at hb
      have : 1 < ((M * n : ℕ) : ℝ) * φ (algebraMap (𝓞 K) K γ) := by push_cast; nlinarith
      linarith
  ·
    rw [add_sub_cancel_left, Nat.cast_mul, mul_assoc]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hnmem)
  · intro φ
    simp only [map_add, map_one, map_mul, map_natCast]
    have hb : 1 < (M : ℝ) * ((n : ℝ) * |φ (algebraMap (𝓞 K) K γ)|) :=
      hMδ.trans_le (mul_le_mul_of_nonneg_left (hδle φ (Finset.mem_univ _)) (Nat.cast_nonneg M))
    constructor
    · intro h
      apply (hγ φ).1.mp
      by_contra hge
      have hpos : 0 < φ (algebraMap (𝓞 K) K γ) := lt_of_le_of_ne (not_lt.mp hge) (hγ φ).2.symm
      have : 0 ≤ ((M * n : ℕ) : ℝ) * φ (algebraMap (𝓞 K) K γ) := by positivity
      linarith
    · intro h
      have hneg : φ (algebraMap (𝓞 K) K γ) < 0 := (hγ φ).1.mpr h
      rw [abs_of_neg hneg] at hb
      have : ((M * n : ℕ) : ℝ) * φ (algebraMap (𝓞 K) K γ) < -1 := by push_cast; nlinarith
      linarith

end SignApproxSol

theorem solution
    (K : Type*) [Field K] [NumberField K] (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥)
    (N : Set (K →+* ℝ)) :
    ∃ α : 𝓞 K, α ≠ 0 ∧ α - 1 ∈ 𝔪 ∧
      ∀ φ : K →+* ℝ, φ (algebraMap (𝓞 K) K α) < 0 ↔ φ ∈ N := by
  classical
  obtain ⟨α, h0, h1, h⟩ := SignApproxSol.main 𝔪 h𝔪 (Set.toFinset N)
  exact ⟨α, h0, h1, fun φ => by rw [h φ, Set.mem_toFinset]⟩

end S_NumberField_exists_ne_zero_and_sub_one_mem_and_lt_zero_iff
end P2MW
export P2MW.S_NumberField_exists_ne_zero_and_sub_one_mem_and_lt_zero_iff (solution)
