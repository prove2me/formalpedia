-- Prove2me | solution 1 for MongeApprox.Sparsify.eq_4
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T23:55:15.976113+00:00
-- url     : https://prove2.me/submissions/8b76987e-12a3-41f3-b7f8-e92741243b8a

import Mathlib
import Definitions.Def_MongeApprox_Sparsify_Monge

set_option autoImplicit false

open MongeApprox.Sparsify

/-- Double telescoping of the discrete mixed second difference. -/
private lemma telescope2 (f : ℕ → ℕ → ℝ) (I J : ℕ) :
    ∑ a ∈ Finset.range I, ∑ b ∈ Finset.range J,
      (f a (b + 1) + f (a + 1) b - f a b - f (a + 1) (b + 1)) =
      f 0 J + f I 0 - f 0 0 - f I J := by
  have inner : ∀ a, ∑ b ∈ Finset.range J,
      (f a (b + 1) + f (a + 1) b - f a b - f (a + 1) (b + 1)) =
      (f a J - f a 0) - (f (a + 1) J - f (a + 1) 0) := by
    intro a
    have e : ∀ b, f a (b + 1) + f (a + 1) b - f a b - f (a + 1) (b + 1) =
        (f a (b + 1) - f a b) - (f (a + 1) (b + 1) - f (a + 1) b) := fun b => by ring
    rw [Finset.sum_congr rfl (fun b _ => e b), Finset.sum_sub_distrib,
      Finset.sum_range_sub (fun b => f a b), Finset.sum_range_sub (fun b => f (a + 1) b)]
  simp only [inner]
  rw [Finset.sum_range_sub' (fun a => f a J - f a 0)]
  ring

/-- `M` extended by zero to all pairs of naturals. -/
private noncomputable def ext {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) (i j : ℕ) : ℝ :=
  if h : i < p ∧ j < q then M ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

private lemma ext_apply {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) (i j : ℕ) (hi : i < p)
    (hj : j < q) : ext M i j = M ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp [ext, hi, hj]

private lemma density_ext {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) (i j : ℕ) (hi : i + 1 < p)
    (hj : j + 1 < q) :
    density M i j = ext M i (j + 1) + ext M (i + 1) j - ext M i j - ext M (i + 1) (j + 1) := by
  rw [density, dif_pos ⟨hi, hj⟩, ext_apply M i (j + 1) (by omega) hj,
    ext_apply M (i + 1) j hi (by omega), ext_apply M i j (by omega) (by omega),
    ext_apply M (i + 1) (j + 1) hi hj]

theorem solution {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (M : Matrix (Fin p) (Fin q) ℝ) :
    totalCurvature M =
      M ⟨0, hp⟩ ⟨q - 1, by omega⟩ + M ⟨p - 1, by omega⟩ ⟨0, hq⟩
        - M ⟨0, hp⟩ ⟨0, hq⟩ - M ⟨p - 1, by omega⟩ ⟨q - 1, by omega⟩ := by
  have h : totalCurvature M = ∑ a ∈ Finset.range (p - 1), ∑ b ∈ Finset.range (q - 1),
      (ext M a (b + 1) + ext M (a + 1) b - ext M a b - ext M (a + 1) (b + 1)) := by
    unfold totalCurvature
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    rw [Finset.mem_range] at ha hb
    exact density_ext M a b (by omega) (by omega)
  rw [h, telescope2, ext_apply M 0 (q - 1) hp (by omega), ext_apply M (p - 1) 0 (by omega) hq,
    ext_apply M 0 0 hp hq, ext_apply M (p - 1) (q - 1) (by omega) (by omega)]
