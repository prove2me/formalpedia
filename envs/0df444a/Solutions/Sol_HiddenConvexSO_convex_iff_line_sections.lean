-- Prove2me | solution 1 for HiddenConvexSO.convex_iff_line_sections
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:31:43.436883+00:00
-- url     : https://prove2.me/submissions/cdd5c9b6-dc6c-44e6-8374-545ceceda8af

import Mathlib
namespace HiddenConvexSO

theorem convex_iff_line_sections (S : Set (ℝ × ℝ)) :
    Convex ℝ S ↔
      ∀ ℓ : ℝ × ℝ, ℓ ≠ 0 → ∀ α : ℝ,
        IsPreconnected (S ∩ {z : ℝ × ℝ | ℓ.1 * z.1 + ℓ.2 * z.2 = α}) := by
  constructor
  · intro hS ℓ _ α
    apply Convex.isPreconnected
    apply hS.inter
    intro u hu v hv a b ha hb hab
    simp only [Set.mem_setOf_eq] at hu hv ⊢
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have : ℓ.1 * (a * u.1 + b * v.1) + ℓ.2 * (a * u.2 + b * v.2) =
        a * (ℓ.1 * u.1 + ℓ.2 * u.2) + b * (ℓ.1 * v.1 + ℓ.2 * v.2) := by ring
    rw [this, hu, hv, ← add_mul, hab, one_mul]
  · intro h x hx y hy a b ha hb hab
    by_cases hxy : x = y
    · subst hxy
      rw [← add_smul, hab, one_smul]; exact hx
    set d1 := y.1 - x.1 with hd1
    set d2 := y.2 - x.2 with hd2
    have hD : 0 < d1 ^ 2 + d2 ^ 2 := by
      by_contra hc
      have e1 : d1 = 0 := by nlinarith [sq_nonneg d1, sq_nonneg d2]
      have e2 : d2 = 0 := by nlinarith [sq_nonneg d1, sq_nonneg d2]
      exact hxy (Prod.ext (by linarith) (by linarith))
    set ℓ : ℝ × ℝ := (-d2, d1) with hℓ
    have hℓ0 : ℓ ≠ 0 := by
      intro h0
      have a1 : -d2 = 0 := congrArg Prod.fst h0
      have a2 : d1 = 0 := congrArg Prod.snd h0
      nlinarith
    set α := ℓ.1 * x.1 + ℓ.2 * x.2 with hα
    set L := S ∩ {z : ℝ × ℝ | ℓ.1 * z.1 + ℓ.2 * z.2 = α} with hL
    have hpc := h ℓ hℓ0 α
    let φ : ℝ × ℝ → ℝ := fun z => (z.1 - x.1) * d1 + (z.2 - x.2) * d2
    have hφc : Continuous φ := by fun_prop
    have himg : (φ '' L).OrdConnected := (hpc.image φ hφc.continuousOn).ordConnected
    have hxL : x ∈ L := ⟨hx, rfl⟩
    have hyL : y ∈ L := ⟨hy, by simp only [Set.mem_setOf_eq, hα, hℓ, hd1, hd2]; ring⟩
    have h0 : φ x ∈ φ '' L := ⟨x, hxL, rfl⟩
    have h1 : φ y ∈ φ '' L := ⟨y, hyL, rfl⟩
    have hφx : φ x = 0 := by simp [φ]
    have hφy : φ y = d1 ^ 2 + d2 ^ 2 := by simp only [φ, hd1, hd2]; ring
    have hmem : b * (d1 ^ 2 + d2 ^ 2) ∈ Set.Icc (φ x) (φ y) := by
      rw [hφx, hφy]
      constructor
      · positivity
      · have : b ≤ 1 := by linarith
        nlinarith
    obtain ⟨q, ⟨hqS, hqL⟩, hq⟩ := himg.out h0 h1 hmem
    simp only [Set.mem_setOf_eq, hα, hℓ] at hqL
    simp only [φ] at hq
    have hp : a • x + b • y = q := by
      have ha' : a = 1 - b := by linarith
      set u1 := q.1 - x.1 - b * d1
      set u2 := q.2 - x.2 - b * d2
      have eq1 : -d2 * u1 + d1 * u2 = 0 := by simp only [u1, u2]; linarith
      have eq2 : d1 * u1 + d2 * u2 = 0 := by simp only [u1, u2]; nlinarith
      have k1 : (d1 ^ 2 + d2 ^ 2) * u1 = 0 := by linear_combination d1 * eq2 - d2 * eq1
      have k2 : (d1 ^ 2 + d2 ^ 2) * u2 = 0 := by linear_combination d2 * eq2 + d1 * eq1
      have z1 : u1 = 0 := (mul_eq_zero.mp k1).resolve_left hD.ne'
      have z2 : u2 = 0 := (mul_eq_zero.mp k2).resolve_left hD.ne'
      simp only [u1, u2, hd1, hd2] at z1 z2
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, ha']; linarith
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, ha']; linarith
    rw [hp]; exact hqS

end HiddenConvexSO

theorem solution (S : Set (ℝ × ℝ)) :
    Convex ℝ S ↔
      ∀ ℓ : ℝ × ℝ, ℓ ≠ 0 → ∀ α : ℝ,
        IsPreconnected (S ∩ {z : ℝ × ℝ | ℓ.1 * z.1 + ℓ.2 * z.2 = α}) :=
  HiddenConvexSO.convex_iff_line_sections S
