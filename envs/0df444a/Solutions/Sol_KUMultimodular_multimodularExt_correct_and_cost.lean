-- Prove2me | solution 1 for KUMultimodular.multimodularExt_correct_and_cost
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T05:38:42.191475+00:00
-- url     : https://prove2.me/submissions/8249168e-b2a3-43c6-a651-660040e13598

import Mathlib
import Definitions.Def_KUMultimodular_Timed
import Definitions.Def_KUMultimodular_lam
import Definitions.Def_KUMultimodular_densePoly
import Definitions.Def_KUMultimodular_multimodularExt

set_option autoImplicit false

namespace KUMultimodularCex

open KUMultimodular

/-- The cost of a `bind` is the sum of the costs. -/
theorem bind_cost {α β : Type} (x : Timed α) (f : α → Timed β) :
    (x >>= f).cost = x.cost + (f x.val).cost := rfl

/-- The first step of `multimodularExt` alone already charges `bits r`. -/
theorem bits_le_cost (t : ℕ) {r : ℕ} (E : Polynomial (ZMod r)) (hE : E.Monic)
    {m d N : ℕ} (coef : (Fin m → Fin d) → AdjoinRoot E) (α : Fin N → Fin m → AdjoinRoot E) :
    bits r ≤ (multimodularExt t E hE coef α).cost := by
  unfold multimodularExt
  rw [bind_cost]
  have h : (tick (bits E.natDegree + bits r)).cost = bits E.natDegree + bits r := rfl
  rw [h]
  omega

theorem bits_two_pow (K : ℕ) : bits (2 ^ K) = K + 2 := by
  unfold bits
  rw [Nat.size_pow]

theorem key (X B : ℝ) (K : ℕ) (h1 : (K : ℝ) + 2 ≤ X) (h2 : X ≤ B) (h3 : B ≤ K) : False := by
  linarith

/-- For `E = 1` the ring has `q = 1` element, so the claimed bound does not depend on `r`,
while the algorithm reads `r` and pays `bits r`. -/
theorem cex : ¬ (∀ (t : ℕ) (ht : 1 ≤ t),
    ∃ (C₁ C₂ : ℝ) (c : ℕ), 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (r : ℕ), 0 < r → ∀ (E : Polynomial (ZMod r)) (hE : E.Monic) (m d N : ℕ)
        (coef : (Fin m → Fin d) → AdjoinRoot E) (α : Fin N → Fin m → AdjoinRoot E), 1 ≤ m →
        (∀ i, (multimodularExt t E hE coef α).val i = MvPolynomial.eval (α i) (densePoly coef)) ∧
        ((multimodularExt t E hE coef α).cost : ℝ) ≤
          C₁ * ((lam t d) ^ m + N) * lam t (Real.logb 2 ((r : ℝ) ^ E.natDegree))
            * (lam t d) ^ (t + 2) * (lam t m) ^ (m + t + 3)
            * (C₂ * ilog (t - 1) (max 1 ((d : ℝ) ^ 2 * (m : ℝ) ^ 2 * lg ((r : ℝ) ^ E.natDegree)
                * lg (lg ((r : ℝ) ^ E.natDegree))))) ^ m
            * (lg (m * d * lg ((r : ℝ) ^ E.natDegree))) ^ c) := by
  intro H
  obtain ⟨C₁, C₂, c, _, _, H⟩ := H 1 le_rfl
  let B : ℝ := C₁ * ((lam 1 ((1 : ℕ) : ℝ)) ^ 1 + ((0 : ℕ) : ℝ)) * lam 1 (Real.logb 2 1)
            * (lam 1 ((1 : ℕ) : ℝ)) ^ (1 + 2) * (lam 1 ((1 : ℕ) : ℝ)) ^ (1 + 1 + 3)
            * (C₂ * ilog (1 - 1) (max 1 (((1 : ℕ) : ℝ) ^ 2 * ((1 : ℕ) : ℝ) ^ 2 * lg 1
                * lg (lg 1)))) ^ 1
            * (lg (((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) * lg 1)) ^ c
  have hr : 0 < 2 ^ ⌈B⌉₊ := Nat.two_pow_pos _
  have h := (H (2 ^ ⌈B⌉₊) hr (1 : Polynomial (ZMod (2 ^ ⌈B⌉₊))) Polynomial.monic_one 1 1 0
    (fun _ => 0) (fun i => Fin.elim0 i) le_rfl).2
  rw [Polynomial.natDegree_one, pow_zero] at h
  have hle := (Nat.cast_le (α := ℝ)).mpr (bits_le_cost 1 (1 : Polynomial (ZMod (2 ^ ⌈B⌉₊)))
    Polynomial.monic_one (m := 1) (d := 1) (N := 0) (fun _ => 0) (fun i => Fin.elim0 i))
  have hbits : ((bits (2 ^ ⌈B⌉₊) : ℕ) : ℝ) = ((⌈B⌉₊ : ℕ) : ℝ) + 2 := by
    rw [bits_two_pow]; push_cast; ring
  exact key _ _ ⌈B⌉₊ (hbits ▸ hle) h (Nat.le_ceil B)

end KUMultimodularCex

theorem solution : ¬ (∀ (t : ℕ) (ht : 1 ≤ t),
    ∃ (C₁ C₂ : ℝ) (c : ℕ), 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (r : ℕ), 0 < r → ∀ (E : Polynomial (ZMod r)) (hE : E.Monic) (m d N : ℕ)
        (coef : (Fin m → Fin d) → AdjoinRoot E) (α : Fin N → Fin m → AdjoinRoot E), 1 ≤ m →
        (∀ i, (KUMultimodular.multimodularExt t E hE coef α).val i =
            MvPolynomial.eval (α i) (KUMultimodular.densePoly coef)) ∧
        ((KUMultimodular.multimodularExt t E hE coef α).cost : ℝ) ≤
          C₁ * ((KUMultimodular.lam t d) ^ m + N)
            * KUMultimodular.lam t (Real.logb 2 ((r : ℝ) ^ E.natDegree))
            * (KUMultimodular.lam t d) ^ (t + 2) * (KUMultimodular.lam t m) ^ (m + t + 3)
            * (C₂ * KUMultimodular.ilog (t - 1) (max 1 ((d : ℝ) ^ 2 * (m : ℝ) ^ 2
                * KUMultimodular.lg ((r : ℝ) ^ E.natDegree)
                * KUMultimodular.lg (KUMultimodular.lg ((r : ℝ) ^ E.natDegree))))) ^ m
            * (KUMultimodular.lg (m * d * KUMultimodular.lg ((r : ℝ) ^ E.natDegree))) ^ c) := by
  exact KUMultimodularCex.cex
