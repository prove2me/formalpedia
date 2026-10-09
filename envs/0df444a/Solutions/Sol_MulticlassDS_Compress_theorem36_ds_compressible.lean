-- Prove2me | solution 1 for MulticlassDS.Compress.theorem36_ds_compressible
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T16:11:47.003028+00:00
-- url     : https://prove2.me/submissions/1277b13d-0ee5-4e08-a48a-0a9079c6d4a8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Dimensions
import Definitions.Def_MulticlassDS_Compress_Compression
import Theorems.Thm_MulticlassDS_Compress_lemma39_list_compression
import Theorems.Thm_MulticlassDS_Compress_lemma40_menu_compression

set_option autoImplicit false



open MulticlassDS.Compress in
theorem glue2e95_trivial {X Y : Type*} [Nonempty Y] (H : Set (X → Y)) (n : ℕ) :
    ∃ ρ : (Fin n → X × Y) → X → Y, IsCompressionScheme H n n ρ := by
  classical
  refine ⟨fun S' => if h : IsRealizable H S' then Classical.choose h
    else fun _ => Classical.arbitrary Y, ?_⟩
  intro S hS
  refine ⟨S, fun j => ⟨j, rfl⟩, ?_⟩
  intro i
  simp only [dif_pos hS]
  exact (Classical.choose_spec hS).2 i

open MulticlassDS.Compress in
theorem glue2e95_pad {X Y : Type*} (H : Set (X → Y)) (μ : X → Set Y) (n r r' : ℕ) (hn : 0 < n)
    (hrr : r ≤ r') (ρ : (Fin r → X × Y) → X → Y) (hρ : IsMenuCompressionScheme H μ n r ρ) :
    ∃ ρ' : (Fin r' → X × Y) → X → Y, IsMenuCompressionScheme H μ n r' ρ' := by
  classical
  refine ⟨fun z => ρ (fun j => z (Fin.castLE hrr j)), ?_⟩
  intro S hS hM
  obtain ⟨S', hsub, hcor⟩ := hρ S hS hM
  refine ⟨fun k => if h : (k : ℕ) < r then S' ⟨k, h⟩ else S ⟨0, hn⟩, ?_, ?_⟩
  · intro k
    by_cases h : (k : ℕ) < r
    · obtain ⟨i, hi⟩ := hsub ⟨k, h⟩
      exact ⟨i, by simp only [dif_pos h]; exact hi⟩
    · exact ⟨⟨0, hn⟩, by simp only [dif_neg h]⟩
  · intro i
    have : (fun j : Fin r => (fun k : Fin r' => if h : (k : ℕ) < r then S' ⟨k, h⟩
        else S ⟨0, hn⟩) (Fin.castLE hrr j)) = S' := by
      funext j
      simp [Fin.castLE]
    simp only [this]
    exact hcor i

open MulticlassDS.Compress in
theorem glue2e95_combine {X Y : Type*} (H : Set (X → Y)) (n r₁ p R : ℕ)
    (ρ₁ : (Fin r₁ → X × Y) → X → Set Y) (h₁ : IsListCompressionScheme H n r₁ p ρ₁)
    (ρ₂ : (Fin r₁ → X × Y) → (Fin R → X × Y) → X → Y)
    (h₂ : ∀ S' : Fin r₁ → X × Y, IsMenuCompressionScheme H (ρ₁ S') n R (ρ₂ S')) :
    ∃ ρ : (Fin (r₁ + R) → X × Y) → X → Y, IsCompressionScheme H n (r₁ + R) ρ := by
  refine ⟨fun z => ρ₂ (fun i => z (Fin.castAdd R i)) (fun j => z (Fin.natAdd r₁ j)), ?_⟩
  intro S hS
  obtain ⟨S₁, hsub₁, hmem⟩ := h₁.2 S hS
  obtain ⟨S₂, hsub₂, hcor⟩ := h₂ S₁ S hS hmem
  refine ⟨Fin.append S₁ S₂, ?_, ?_⟩
  · intro k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · obtain ⟨m, hm⟩ := hsub₁ i
      exact ⟨m, by simp [Fin.append_left, hm]⟩
    · obtain ⟨m, hm⟩ := hsub₂ j
      exact ⟨m, by simp [Fin.append_right, hm]⟩
  · intro i
    simp only [Fin.append_left, Fin.append_right]
    exact hcor i

open MulticlassDS.Compress in
theorem solution {X Y : Type*} (H : Set (X → Y)) (dDS dN : ℕ)
    (hDS : dsDim H = dDS) (hN : natarajanDim H = dN) (n t : ℕ) (hn : 0 < n) (ht : 0 < t) :
    ∃ r : ℕ, r ≤ n ∧
      (r : ℝ) ≤ (((dDS : ℝ) + t + 1) / (t + 1) * (dDS + t) +
          10 ^ 3 * dN * Real.logb 2 ((Nat.choose (dDS + t + 1) (t + 1) : ℝ) *
            Real.logb 2 (2 * (n : ℝ)))) * Real.logb 2 (2 * (n : ℝ)) ∧
      ∃ ρ : (Fin r → X × Y) → X → Y, IsCompressionScheme H n r ρ := by
  classical
  set L : ℝ := Real.logb 2 (2 * (n : ℝ)) with hL
  set C : ℝ := (Nat.choose (dDS + t + 1) (t + 1) : ℝ) with hC
  set A : ℝ := ((dDS : ℝ) + t + 1) / (t + 1) * (dDS + t) with hA
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
    simp; linarith
  have hC1 : 1 ≤ C := by
    rw [hC]; exact_mod_cast Nat.choose_pos (by omega)
  have hCL : 1 ≤ C * L := by nlinarith
  have hlogCL : 0 ≤ Real.logb 2 (C * L) := Real.logb_nonneg (by norm_num) hCL
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hA1 : (t : ℝ) ≤ A := by
    rw [hA]
    have h1 : (1 : ℝ) ≤ ((dDS : ℝ) + t + 1) / (t + 1) := by
      rw [le_div_iff₀ (by positivity)]; have : (0 : ℝ) ≤ dDS := by positivity
      linarith
    have hd0 : (0 : ℝ) ≤ dDS := by positivity
    have h2 : (t : ℝ) ≤ dDS + t := by linarith
    nlinarith
  have hdN0 : (0 : ℝ) ≤ dN := by positivity
  rcases isEmpty_or_nonempty Y with hY | hY
  · -- empty label type: r = 1, the scheme is vacuous
    refine ⟨1, hn, ?_, ⟨fun S' _ => (S' 0).2, ?_⟩⟩
    · have : 0 ≤ 10 ^ 3 * (dN : ℝ) * Real.logb 2 (C * L) := by positivity
      push_cast
      nlinarith
    · intro S _
      exact isEmptyElim (S ⟨0, hn⟩).2
  · obtain ⟨r₁, p, hr₁, hp, ρ₁, h₁⟩ := lemma39_list_compression H dDS hDS n t hn ht
    set K : ℝ := 10 ^ 3 * dN * Real.logb 2 (C * L) * L with hK
    have hK0 : 0 ≤ K := by rw [hK]; positivity
    have hlogp : Real.logb 2 p ≤ Real.logb 2 (C * L) := by
      rcases Nat.eq_zero_or_pos p with h0 | hpos
      · simp [h0, hlogCL]
      · exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hpos) hp
    have key : ∀ S' : Fin r₁ → X × Y, ∃ ρ' : (Fin ⌊K⌋₊ → X × Y) → X → Y,
        IsMenuCompressionScheme H (ρ₁ S') n ⌊K⌋₊ ρ' := by
      intro S'
      obtain ⟨r₂, hr₂, ρ₂, h₂⟩ := lemma40_menu_compression H dN hN (ρ₁ S') p (fun x => h₁.1 S' x) n hn
      have hr₂K : (r₂ : ℝ) ≤ K := by
        refine hr₂.trans ?_
        rw [hK]
        have hL0 : (0 : ℝ) ≤ L := by linarith
        have := mul_le_mul_of_nonneg_left hlogp (by positivity : (0 : ℝ) ≤ 10 ^ 3 * dN)
        exact mul_le_mul_of_nonneg_right this hL0
      exact glue2e95_pad H (ρ₁ S') n r₂ ⌊K⌋₊ hn (Nat.le_floor hr₂K) ρ₂ h₂
    choose ρ₂ h₂ using key
    have hbound : ((r₁ + ⌊K⌋₊ : ℕ) : ℝ) ≤ (A + 10 ^ 3 * dN * Real.logb 2 (C * L)) * L := by
      push_cast
      have := Nat.floor_le hK0
      have e : (A + 10 ^ 3 * dN * Real.logb 2 (C * L)) * L = A * L + K := by rw [hK]; ring
      rw [e]
      have : (r₁ : ℝ) ≤ A * L := by rw [hA]; exact hr₁
      linarith
    by_cases hle : r₁ + ⌊K⌋₊ ≤ n
    · exact ⟨r₁ + ⌊K⌋₊, hle, hbound, glue2e95_combine H n r₁ p ⌊K⌋₊ ρ₁ h₁ ρ₂ h₂⟩
    · refine ⟨n, le_rfl, ?_, glue2e95_trivial H n⟩
      have : (n : ℝ) ≤ ((r₁ + ⌊K⌋₊ : ℕ) : ℝ) := by exact_mod_cast (by omega : n ≤ r₁ + ⌊K⌋₊)
      linarith
