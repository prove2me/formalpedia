-- Prove2me | solution 1 for KashUpgrade.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:26:15.254804+00:00
-- url     : https://prove2.me/submissions/76cb4b2e-cd83-4542-ae84-f95ee002e33a

import Mathlib
import Definitions.Def_KashUpgrade_Assumption2
import Definitions.Def_KashUpgrade_firstOrderThreshold
import Definitions.Def_KashUpgrade_lumpBlock

set_option autoImplicit false

open Classical KashUpgrade

namespace KashUpgrade.Lemma2Proof

def rel (S : Finset ℕ) (a b : ℕ) : Prop :=
  ∀ m, min a b ≤ m → m < max a b → m ∈ S

theorem mem_lumpBlock_iff (j n : ℕ) (S : Finset ℕ) (i ℓ : ℕ) :
    ℓ ∈ lumpBlock j n S i ↔ ℓ ∈ Finset.Icc (j + 1) (j + n) ∧ rel S ℓ i := by
  simp [lumpBlock, rel]

theorem rel_refl (S : Finset ℕ) (a : ℕ) : rel S a a := by
  intro m h1 h2; omega

theorem rel_symm {S : Finset ℕ} {a b : ℕ} (h : rel S a b) : rel S b a := by
  intro m h1 h2; exact h m (by omega) (by omega)

theorem rel_trans {S : Finset ℕ} {a b d : ℕ} (h1 : rel S a b) (h2 : rel S b d) :
    rel S a d := by
  intro m hm1 hm2
  by_cases hmb : m < b
  · by_cases hab : a ≤ m
    · exact h1 m (by omega) (by omega)
    · exact h2 m (by omega) (by omega)
  · by_cases hmd : m < d
    · exact h2 m (by omega) (by omega)
    · exact h1 m (by omega) (by omega)

theorem virtualInverse_ne_top {f : ℝ → ℝ} {ζ : ENNReal} (hf : Assumption2 f ζ) (γ : ℝ) :
    virtualInverse f ζ γ ≠ ⊤ := by
  unfold virtualInverse
  rcases eq_or_ne ζ ⊤ with rfl | hζ
  · rw [min_eq_left le_top]
    set a : ℝ := (1 - typeCdf f 1) / f 1
    set θ : ℝ := max 2 (γ + a + 1)
    have hθ1 : 1 ≤ θ := le_trans (by norm_num) (le_max_left _ _)
    have h1_mem : (1 : ℝ) ∈ typeInterior ⊤ := ⟨one_pos, ENNReal.ofReal_lt_top⟩
    have hθ_mem : θ ∈ typeInterior ⊤ := ⟨lt_of_lt_of_le one_pos hθ1, ENNReal.ofReal_lt_top⟩
    have hanti : (1 - typeCdf f θ) / f θ ≤ a := hf.antitoneOn h1_mem hθ_mem hθ1
    have hv : γ ≤ virtualValue f θ := by
      unfold virtualValue
      have : γ + a + 1 ≤ θ := le_max_right _ _
      linarith
    have hle : (⨅ p ∈ {p : ℝ | 0 < p ∧ ENNReal.ofReal p < ⊤ ∧ γ ≤ virtualValue f p},
        ENNReal.ofReal p) ≤ ENNReal.ofReal θ :=
      biInf_le _ ⟨lt_of_lt_of_le one_pos hθ1, ENNReal.ofReal_lt_top, hv⟩
    exact (lt_of_le_of_lt hle ENNReal.ofReal_lt_top).ne
  · exact (lt_of_le_of_lt (min_le_right _ _) (lt_top_iff_ne_top.mpr hζ)).ne

theorem threshold_mono {f : ℝ → ℝ} {ζ : ENNReal} (hf : Assumption2 f ζ) {γ₁ γ₂ : ℝ}
    (hγ : γ₁ ≤ γ₂) :
    (virtualInverse f ζ γ₁).toReal ≤ (virtualInverse f ζ γ₂).toReal := by
  apply ENNReal.toReal_mono (virtualInverse_ne_top hf γ₂)
  unfold virtualInverse
  apply min_le_min_right
  refine biInf_mono ?_
  rintro θ ⟨h0, hlt, hv⟩
  exact ⟨h0, hlt, hγ.trans hv⟩

end KashUpgrade.Lemma2Proof

open KashUpgrade.Lemma2Proof in
theorem solution {f : ℝ → ℝ} {ζ : ENNReal} (hf : Assumption2 f ζ) {c : ℝ} (hc : 0 < c)
    (s : ℕ → ℕ) (A : ℕ → ℝ) (j n : ℕ)
    (hA : ∀ ℓ ∈ Finset.Icc (j + 1) (j + n), 0 ≤ A ℓ ∧ (0 < A ℓ → s (ℓ - 1) < s ℓ))
    {L L' : Finset ℕ} (hL : L ⊆ L') {i : ℕ} (hi : i ∈ Finset.Icc (j + 1) (j + n))
    (hB : ∀ ι ∈ lumpBlock j n L' i, 0 < ∑ ℓ ∈ lumpBlock j n L ι, A ℓ) :
    ∃ ι₁ ∈ lumpBlock j n L' i, ∃ ι₂ ∈ lumpBlock j n L' i,
      firstOrderThreshold f ζ c s A (lumpBlock j n L ι₁) ≤
        firstOrderThreshold f ζ c s A (lumpBlock j n L' i) ∧
      firstOrderThreshold f ζ c s A (lumpBlock j n L' i) ≤
        firstOrderThreshold f ζ c s A (lumpBlock j n L ι₂) := by
  set B' := lumpBlock j n L' i
  have hi_mem : i ∈ B' := (mem_lumpBlock_iff j n L' i i).mpr ⟨hi, rel_refl L' i⟩
  have hB'_ne : B'.Nonempty := ⟨i, hi_mem⟩
  have hsub_B' : ∀ ι ∈ B', lumpBlock j n L ι ⊆ B' := by
    intro ι hι ℓ hℓ
    obtain ⟨hιI, hιrel⟩ := (mem_lumpBlock_iff j n L' i ι).mp hι
    obtain ⟨hℓI, hℓrel⟩ := (mem_lumpBlock_iff j n L ι ℓ).mp hℓ
    have hℓL' : rel L' ℓ ι := fun m hm1 hm2 => hL (hℓrel m hm1 hm2)
    exact (mem_lumpBlock_iff j n L' i ℓ).mpr ⟨hℓI, rel_trans hℓL' hιrel⟩
  let ℬ : Finset (Finset ℕ) := B'.image (fun ι => lumpBlock j n L ι)
  have hℬ_ne : ℬ.Nonempty := hB'_ne.image _
  have hdisj : (ℬ : Set (Finset ℕ)).PairwiseDisjoint id := by
    intro C₁ hC₁ C₂ hC₂ hne
    obtain ⟨ι₁, hι₁, rfl⟩ := Finset.mem_image.mp hC₁
    obtain ⟨ι₂, hι₂, rfl⟩ := Finset.mem_image.mp hC₂
    change Disjoint (lumpBlock j n L ι₁) (lumpBlock j n L ι₂)
    rw [Finset.disjoint_left]
    intro k hk₁ hk₂
    apply hne
    obtain ⟨-, hkι₁⟩ := (mem_lumpBlock_iff j n L ι₁ k).mp hk₁
    obtain ⟨-, hkι₂⟩ := (mem_lumpBlock_iff j n L ι₂ k).mp hk₂
    have h12 : rel L ι₁ ι₂ := rel_trans (rel_symm hkι₁) hkι₂
    ext x
    rw [mem_lumpBlock_iff, mem_lumpBlock_iff]
    exact ⟨fun ⟨hxI, hx1⟩ => ⟨hxI, rel_trans hx1 h12⟩,
      fun ⟨hxI, hx2⟩ => ⟨hxI, rel_trans hx2 (rel_symm h12)⟩⟩
  have hbiU : ℬ.biUnion id = B' := by
    ext ℓ
    simp only [Finset.mem_biUnion, id_eq, ℬ, Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨ι, hι, rfl⟩, hℓ⟩
      exact hsub_B' ι hι hℓ
    · intro hℓ
      refine ⟨lumpBlock j n L ℓ, ⟨ℓ, hℓ, rfl⟩, ?_⟩
      exact (mem_lumpBlock_iff j n L ℓ ℓ).mpr ⟨((mem_lumpBlock_iff j n L' i ℓ).mp hℓ).1, rel_refl L ℓ⟩
  let den : Finset ℕ → ℝ := fun C => ∑ ℓ ∈ C, A ℓ * ((s ℓ : ℝ) - s (ℓ - 1))
  let num : Finset ℕ → ℝ := fun C => c * ∑ ℓ ∈ C, A ℓ
  have hden_pos : ∀ C ∈ ℬ, 0 < den C := by
    intro C hC
    obtain ⟨ι, hι, rfl⟩ := Finset.mem_image.mp hC
    have hAsum : 0 < ∑ ℓ ∈ lumpBlock j n L ι, A ℓ := hB ι hι
    have hex_pos : ∃ ℓ₀ ∈ lumpBlock j n L ι, 0 < A ℓ₀ := by
      by_contra hall
      push Not at hall
      have : ∑ ℓ ∈ lumpBlock j n L ι, A ℓ ≤ 0 := Finset.sum_nonpos hall
      linarith
    obtain ⟨ℓ₀, hℓ₀, hA₀⟩ := hex_pos
    refine Finset.sum_pos' ?_ ⟨ℓ₀, hℓ₀, ?_⟩
    · intro ℓ hℓ
      have hℓI : ℓ ∈ Finset.Icc (j + 1) (j + n) := ((mem_lumpBlock_iff j n L ι ℓ).mp hℓ).1
      obtain ⟨hA_nn, hA_imp⟩ := hA ℓ hℓI
      by_cases hA_zero : A ℓ = 0
      · rw [hA_zero, zero_mul]
      · have hA_gt : 0 < A ℓ := lt_of_le_of_ne hA_nn (Ne.symm hA_zero)
        have hslt : (s (ℓ - 1) : ℝ) < s ℓ := Nat.cast_lt.mpr (hA_imp hA_gt)
        exact mul_nonneg hA_nn (by linarith)
    · have hℓ₀I : ℓ₀ ∈ Finset.Icc (j + 1) (j + n) := ((mem_lumpBlock_iff j n L ι ℓ₀).mp hℓ₀).1
      have hslt : (s (ℓ₀ - 1) : ℝ) < s ℓ₀ := Nat.cast_lt.mpr ((hA ℓ₀ hℓ₀I).2 hA₀)
      exact mul_pos hA₀ (by linarith)
  have hden_B' : den B' = ∑ C ∈ ℬ, den C := by
    simp only [den]
    rw [← hbiU, Finset.sum_biUnion hdisj]
    rfl
  have hnum_B' : num B' = ∑ C ∈ ℬ, num C := by
    simp only [num]
    rw [← hbiU, Finset.sum_biUnion hdisj, Finset.mul_sum]
    rfl
  have hden_B'_pos : 0 < den B' := by
    rw [hden_B']
    obtain ⟨C₀, hC₀⟩ := hℬ_ne
    exact Finset.sum_pos' (fun C hC => (hden_pos C hC).le) ⟨C₀, hC₀, hden_pos C₀ hC₀⟩
  obtain ⟨C₁, hC₁, hmin⟩ := Finset.exists_min_image ℬ (blockValue c s A) hℬ_ne
  obtain ⟨C₂, hC₂, hmax⟩ := Finset.exists_max_image ℬ (blockValue c s A) hℬ_ne
  obtain ⟨ι₁, hι₁, rfl⟩ := Finset.mem_image.mp hC₁
  obtain ⟨ι₂, hι₂, rfl⟩ := Finset.mem_image.mp hC₂
  have hbv_min : blockValue c s A (lumpBlock j n L ι₁) ≤ blockValue c s A B' := by
    change blockValue c s A (lumpBlock j n L ι₁) ≤ num B' / den B'
    rw [le_div_iff₀ hden_B'_pos, hden_B', hnum_B', Finset.mul_sum]
    apply Finset.sum_le_sum
    intro C hC
    have h1 : blockValue c s A (lumpBlock j n L ι₁) * den C ≤ blockValue c s A C * den C :=
      mul_le_mul_of_nonneg_right (hmin C hC) (hden_pos C hC).le
    have h2 : blockValue c s A C * den C = num C := div_mul_cancel₀ (num C) (hden_pos C hC).ne'
    linarith
  have hbv_max : blockValue c s A B' ≤ blockValue c s A (lumpBlock j n L ι₂) := by
    change num B' / den B' ≤ blockValue c s A (lumpBlock j n L ι₂)
    rw [div_le_iff₀ hden_B'_pos, hden_B', hnum_B', Finset.mul_sum]
    apply Finset.sum_le_sum
    intro C hC
    have h1 : blockValue c s A C * den C ≤ blockValue c s A (lumpBlock j n L ι₂) * den C :=
      mul_le_mul_of_nonneg_right (hmax C hC) (hden_pos C hC).le
    have h2 : blockValue c s A C * den C = num C := div_mul_cancel₀ (num C) (hden_pos C hC).ne'
    linarith
  refine ⟨ι₁, hι₁, ι₂, hι₂, ?_, ?_⟩
  · unfold firstOrderThreshold
    exact threshold_mono hf hbv_min
  · unfold firstOrderThreshold
    exact threshold_mono hf hbv_max
