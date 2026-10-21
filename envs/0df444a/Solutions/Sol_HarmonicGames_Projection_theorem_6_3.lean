-- Prove2me | solution 1 for HarmonicGames.Projection.theorem_6_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:31:52.791791+00:00
-- url     : https://prove2.me/submissions/24437173-6d40-4f4d-bbcc-c1ac127b1f13

import Mathlib
import Definitions.Def_HarmonicGames_Projection_EpsEquilibrium
import Definitions.Def_HarmonicGames_Projection_Closest

set_option autoImplicit false
open HarmonicGames.Projection

lemma hgp_bound {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]
    (u û : ι → (∀ m, E m) → ℝ) (m : ι) (p : ∀ m, E m) :
    |u m p - û m p| ≤ normME E (u - û) / Real.sqrt (Fintype.card (E m)) := by
  have hcard : (0 : ℝ) < Fintype.card (E m) := by exact_mod_cast Fintype.card_pos
  have hsq : 0 < Real.sqrt (Fintype.card (E m)) := Real.sqrt_pos.2 hcard
  rw [le_div_iff₀ hsq]
  have h1 : (Fintype.card (E m) : ℝ) * (u m p - û m p) ^ 2 ≤ innerME E (u - û) (u - û) := by
    unfold innerME
    have h2 : (u m p - û m p) ^ 2 ≤ ∑ q : (∀ k, E k), (u - û) m q * (u - û) m q := by
      have := Finset.single_le_sum (f := fun q : (∀ k, E k) => (u - û) m q * (u - û) m q)
        (fun q _ => mul_self_nonneg _) (Finset.mem_univ p)
      simpa [sq] using this
    have h3 : (Fintype.card (E m) : ℝ) * (u m p - û m p) ^ 2 ≤
        (Fintype.card (E m) : ℝ) * ∑ q : (∀ k, E k), (u - û) m q * (u - û) m q :=
      mul_le_mul_of_nonneg_left h2 hcard.le
    refine h3.trans ?_
    exact Finset.single_le_sum (f := fun m' => (Fintype.card (E m') : ℝ) *
      ∑ q : (∀ k, E k), (u - û) m' q * (u - û) m' q)
      (fun m' _ => mul_nonneg (Nat.cast_nonneg _)
        (Finset.sum_nonneg fun q _ => mul_self_nonneg _)) (Finset.mem_univ m)
  unfold normME
  calc |u m p - û m p| * Real.sqrt (Fintype.card (E m))
      = Real.sqrt ((Fintype.card (E m) : ℝ) * (u m p - û m p) ^ 2) := by
        rw [Real.sqrt_mul hcard.le, Real.sqrt_sq_eq_abs]; ring
    _ ≤ Real.sqrt (innerME E (u - û) (u - û)) := Real.sqrt_le_sqrt h1

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]
    (u û : ι → (∀ m, E m) → ℝ) (hû : IsClosestPotential E u û) :
    (∀ (ϵ₁ : ℝ) (p : ∀ m, E m), IsEpsEquilibrium û ϵ₁ p →
        IsEpsEquilibrium u
          (Finset.univ.sup' Finset.univ_nonempty
            (fun m => 2 * normME E (u - û) / Real.sqrt (Fintype.card (E m))) + ϵ₁) p) ∧
      (∀ (ϵ₁ : ℝ) (p : ∀ m, E m), IsEpsEquilibrium u ϵ₁ p →
        IsEpsEquilibrium û
          (Finset.univ.sup' Finset.univ_nonempty
            (fun m => 2 * normME E (u - û) / Real.sqrt (Fintype.card (E m))) + ϵ₁) p) := by
  have hS : ∀ m, 2 * (normME E (u - û) / Real.sqrt (Fintype.card (E m))) ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun m => 2 * normME E (u - û) / Real.sqrt (Fintype.card (E m))) := fun m => by
    rw [← mul_div_assoc]
    exact Finset.le_sup' (fun m => 2 * normME E (u - û) / Real.sqrt (Fintype.card (E m)))
      (Finset.mem_univ m)
  constructor
  · intro ϵ₁ p hp m q
    have h1 := abs_le.mp (hgp_bound E u û m (Function.update p m q))
    have h2 := abs_le.mp (hgp_bound E u û m p)
    have h3 := hp m q
    have h4 := hS m
    linarith [h1.1, h1.2, h2.1, h2.2]
  · intro ϵ₁ p hp m q
    have h1 := abs_le.mp (hgp_bound E u û m (Function.update p m q))
    have h2 := abs_le.mp (hgp_bound E u û m p)
    have h3 := hp m q
    have h4 := hS m
    linarith [h1.1, h1.2, h2.1, h2.2]
