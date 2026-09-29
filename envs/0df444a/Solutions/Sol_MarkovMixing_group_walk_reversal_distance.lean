-- Prove2me | solution 1 for MarkovMixing.group_walk_reversal_distance
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T03:55:33.869964+00:00
-- url     : https://prove2.me/submissions/1c04497e-312e-46d0-a4a0-11ac7195e5b9

import Definitions.Def_mm_mixing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Group

open scoped BigOperators
open scoped Matrix
open MarkovMixing

theorem solution {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] (μ : G → ℝ) (hμ : IsDist μ) (t : ℕ) :
    tvDist (rowDist (groupWalk μ) t 1) (uniformDist G) =
      tvDist (rowDist (groupWalk (invDist μ)) t 1) (uniformDist G) := by
  classical
  set P : Matrix G G ℝ := groupWalk μ with hPdef
  set Q : Matrix G G ℝ := groupWalk (invDist μ) with hQdef
  -- the inverse-increment walk is the transpose of the original walk
  have hQP : Q = Pᵀ := by
    funext a b
    show invDist μ (b * a⁻¹) = μ (a * b⁻¹)
    show μ (b * a⁻¹)⁻¹ = μ (a * b⁻¹)
    rw [mul_inv_rev, inv_inv]
  -- right translation invariance of the walk
  have hinv : ∀ (n : ℕ) (a b c : G), (P ^ n) (a * c) (b * c) = (P ^ n) a b := by
    intro n
    induction n with
    | zero =>
        intro a b c
        by_cases hab : a = b
        · subst hab; simp [Matrix.one_apply]
        · have hne : a * c ≠ b * c := fun h => hab (mul_right_cancel h)
          simp [Matrix.one_apply, hab, hne]
    | succ m ih =>
        intro a b c
        have hL : (P ^ (m + 1)) (a * c) (b * c)
            = ∑ w, (P ^ m) (a * c) w * μ (b * c * w⁻¹) := by rw [pow_succ]; rfl
        have hR : (P ^ (m + 1)) a b = ∑ w, (P ^ m) a w * μ (b * w⁻¹) := by
          rw [pow_succ]; rfl
        rw [hL, hR, ← Equiv.sum_comp (Equiv.mulRight c)
          (fun w : G => (P ^ m) (a * c) w * μ (b * c * w⁻¹))]
        refine Finset.sum_congr rfl fun w _ => ?_
        simp only [Equiv.coe_mulRight]
        rw [ih a w c]
        congr 2
        group
  -- hence the reversed walk's row at the identity is the original row, inverted
  have hrow : ∀ g : G, rowDist Q t 1 g = rowDist P t 1 g⁻¹ := by
    intro g
    show (Q ^ t) 1 g = (P ^ t) 1 g⁻¹
    rw [hQP, ← Matrix.transpose_pow]
    show (P ^ t) g 1 = (P ^ t) 1 g⁻¹
    have h := hinv t g 1 g⁻¹
    rw [mul_inv_cancel, one_mul] at h
    exact h.symm
  -- transport the supremum along the inversion bijection on subsets
  have hbdd : ∀ ν : G → ℝ,
      BddAbove (Set.range fun A : Finset G =>
        |∑ x ∈ A, ν x - ∑ x ∈ A, uniformDist G x|) :=
    fun ν => Set.Finite.bddAbove
      (Set.range fun A : Finset G => |∑ x ∈ A, ν x - ∑ x ∈ A, uniformDist G x|).toFinite
  have hinj : ∀ A : Finset G, Set.InjOn (fun g : G => g⁻¹) A :=
    fun A x _ y _ h => by simpa using congrArg (fun g : G => g⁻¹) h
  have hsum_img : ∀ (ν : G → ℝ) (A : Finset G),
      ∑ y ∈ A.image (fun g : G => g⁻¹), ν y = ∑ x ∈ A, ν x⁻¹ := by
    intro ν A
    exact Finset.sum_image fun x hx y hy h => by
      simpa using congrArg (fun g : G => g⁻¹) h
  have hcard : ∀ A : Finset G, (A.image (fun g : G => g⁻¹)).card = A.card :=
    fun A => Finset.card_image_of_injective A (fun x y h => by
      simpa using congrArg (fun g : G => g⁻¹) h)
  have hunif : ∀ A : Finset G, ∑ x ∈ A, uniformDist G x
      = (A.card : ℝ) * (Fintype.card G : ℝ)⁻¹ := by
    intro A
    show ∑ _x ∈ A, (Fintype.card G : ℝ)⁻¹ = _
    rw [Finset.sum_const, nsmul_eq_mul]
  have hkey : ∀ A : Finset G,
      |∑ x ∈ A, rowDist Q t 1 x - ∑ x ∈ A, uniformDist G x|
      = |∑ y ∈ A.image (fun g : G => g⁻¹), rowDist P t 1 y
          - ∑ y ∈ A.image (fun g : G => g⁻¹), uniformDist G y| := by
    intro A
    rw [hsum_img (rowDist P t 1) A, hunif, hunif, hcard A]
    congr 2
    exact Finset.sum_congr rfl fun x _ => hrow x
  refine le_antisymm ?_ ?_
  · refine ciSup_le fun A => ?_
    have hA : |∑ x ∈ A, rowDist P t 1 x - ∑ x ∈ A, uniformDist G x|
        = |∑ y ∈ (A.image (fun g : G => g⁻¹)), rowDist Q t 1 y
            - ∑ y ∈ (A.image (fun g : G => g⁻¹)), uniformDist G y| := by
      rw [hkey (A.image (fun g : G => g⁻¹))]
      congr 2
      · rw [Finset.image_image]
        congr 1
        ext x
        simp
      · rw [Finset.image_image]
        congr 1
        ext x
        simp
    rw [hA]
    exact le_ciSup (hbdd (rowDist Q t 1)) _
  · refine ciSup_le fun A => ?_
    rw [hkey A]
    exact le_ciSup (hbdd (rowDist P t 1)) _
