-- Prove2me | solution 1 for LefebvreVariations.ch2_unif_two_not_gf_representable
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T22:03:19.121842+00:00
-- url     : https://prove2.me/submissions/8860b4f9-3d94-4a5b-8d32-df1a37e8c73c

import Mathlib
import Definitions.Def_TenChallenges_MatroidRepresentability

set_option autoImplicit false

namespace LefebvreVariations
end LefebvreVariations

open LefebvreVariations

theorem solution (p m : ℕ) [Fact p.Prime] (hm : 0 < m)
    {α : Type*} (M : Matroid α)
    (hE : M.E.encard = ((p ^ m + 2 : ℕ) : ℕ∞))
    (hI : ∀ I : Set α, M.Indep I ↔ I ⊆ M.E ∧ I.encard ≤ 2) :
    ¬ IsGFRepresentable p m M := by
  rintro ⟨W, _, _, v, hv⟩
  set F := GaloisField p m
  -- Every pair of ground elements is independent.
  have hpair : ∀ x ∈ M.E, ∀ y ∈ M.E, x ≠ y → LinearIndepOn F v {x, y} := by
    intro x hx y hy hxy
    rw [← hv, hI]
    refine ⟨?_, (Set.encard_pair hxy).le⟩
    intro z hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  -- Two distinct elements `a`, `b`.
  have h1 : 1 < M.E.encard := by
    rw [hE]; exact_mod_cast (by omega : 1 < p ^ m + 2)
  obtain ⟨a, b, ha, hb, hab⟩ := Set.one_lt_encard_iff.mp h1
  -- Every element other than `a` is a multiple of some `r • v a + v b`.
  have hrep : ∀ x ∈ M.E \ {a}, ∃ r d : F, v x = d • (r • v a + v b) := by
    rintro x ⟨hx, hxa⟩
    rw [Set.mem_singleton_iff] at hxa
    by_cases hxb : x = b
    · subst hxb; exact ⟨0, 1, by simp⟩
    have hnot : ¬ LinearIndepOn F v (insert x {a, b}) := by
      rw [← hv, hI]
      rintro ⟨-, h⟩
      have hx' : x ∉ ({a, b} : Set α) := by
        rintro (h' | h') <;> contradiction
      rw [Set.encard_insert_of_notMem hx', Set.encard_pair hab] at h
      exact absurd h (by decide)
    have hx' : x ∉ ({a, b} : Set α) := by
      rintro (h' | h') <;> contradiction
    rw [linearIndepOn_insert hx'] at hnot
    have hmem : v x ∈ Submodule.span F (v '' {a, b}) := by
      by_contra hc; exact hnot ⟨hpair a ha b hb hab, hc⟩
    rw [Set.image_pair, Submodule.mem_span_pair] at hmem
    obtain ⟨c, d, hcd⟩ := hmem
    have hd : d ≠ 0 := by
      rintro rfl
      have := (LinearIndepOn.pair_iff v (Ne.symm hxa)).mp (hpair a ha x hx (Ne.symm hxa)) c (-1)
        (by rw [← hcd]; simp)
      exact one_ne_zero (neg_eq_zero.mp this.2)
    refine ⟨c / d, d, ?_⟩
    rw [← hcd, smul_add, smul_smul, mul_div_cancel₀ c hd]
  choose! r d hrd using hrep
  -- `r` is injective on `M.E \ {a}`.
  have hinj : Set.InjOn r (M.E \ {a}) := by
    intro x hx y hy hxy
    by_contra hne
    have hli := hpair x hx.1 y hy.1 hne
    have key := (LinearIndepOn.pair_iff v hne).mp hli (d y) (-d x)
      (by rw [hrd x hx, hrd y hy, hxy, smul_smul, smul_smul, neg_mul, neg_smul, mul_comm, add_neg_cancel])
    have h0 := (LinearIndepOn.pair_iff v hne).mp hli 1 0
      (by rw [hrd x hx, hrd y hy, key.1, neg_eq_zero.mp key.2]; simp)
    exact one_ne_zero h0.1
  -- Counting.
  have hcardF : ENat.card F = ((p ^ m : ℕ) : ℕ∞) := by
    rw [ENat.card_eq_coe_natCard, GaloisField.card p m (by omega)]
  have hle : (M.E \ {a}).encard ≤ ((p ^ m : ℕ) : ℕ∞) := by
    rw [← hinj.encard_image, ← hcardF]; exact Set.encard_le_card
  have hsize := Set.encard_sdiff_singleton_add_one ha
  rw [hE] at hsize
  have : ((p ^ m + 2 : ℕ) : ℕ∞) ≤ ((p ^ m + 1 : ℕ) : ℕ∞) := by
    rw [← hsize]; push_cast at hle ⊢; gcongr
  have := ENat.natCast_le_natCast.mp this
  omega
