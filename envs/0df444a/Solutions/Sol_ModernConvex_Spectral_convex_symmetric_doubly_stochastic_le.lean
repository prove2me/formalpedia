-- Prove2me | solution 1 for ModernConvex.Spectral.convex_symmetric_doubly_stochastic_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:40:31.886985+00:00
-- url     : https://prove2.me/submissions/112625c3-88e4-4290-a438-9f4e71627ff5

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR

open Matrix
open ModernConvex.Spectral

/-- Ben-Tal–Nemirovski, fact (C), p. 281: let `f : ℝᵐ → ℝ ∪ {+∞}` be a convex symmetric function,
let `x ∈ Dom f` and let `P ∈ 𝒮_m` be double-stochastic. Then `f(Px) ≤ f(x)`. -/
theorem solution {m : ℕ} (f : (Fin m → ℝ) → EReal)
    (hf : IsConvexExt f) (hsym : IsSymmetricFn f) (x : Fin m → ℝ) (hx : f x ≠ ⊤)
    (P : Matrix (Fin m) (Fin m) ℝ) (hP : IsDoublyStochastic P) :
    f (P *ᵥ x) ≤ f x := by
  have hP' : P ∈ doublyStochastic ℝ (Fin m) := by
    rw [mem_doublyStochastic_iff_sum]
    exact ⟨hP.1, hP.2.2, hP.2.1⟩
  obtain ⟨w, hw0, hw1, hwP⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hP'
  have hPx : P *ᵥ x = ∑ σ, w σ • (x ∘ σ) := by
    rw [← hwP, sum_mulVec]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_mulVec, Matrix.permMatrix_mulVec]
  set r := (f x).toReal with hr
  have hfx : f x = (r : EReal) := (EReal.coe_toReal hx (hf.1 x)).symm
  have hmem : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin m))),
      ((x ∘ σ, r) : (Fin m → ℝ) × ℝ) ∈ {p : (Fin m → ℝ) × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    intro σ _
    show f (x ∘ σ) ≤ (r : EReal)
    rw [hsym σ x, hfx]
  have := hf.2.sum_mem (fun σ _ => hw0 σ) hw1 hmem
  simp only [Set.mem_ofPred_eq, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, ← Finset.sum_mul, hw1, one_mul] at this
  rw [hPx, hfx]
  exact this

