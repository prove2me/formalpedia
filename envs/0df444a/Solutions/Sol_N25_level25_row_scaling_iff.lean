-- Prove2me | solution 1 for N25.level25_row_scaling_iff
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:40:59.430441+00:00
-- url     : https://prove2.me/submissions/e5963abc-1b0d-4de3-acf3-adaa1e2ca284

import Mathlib
import Definitions.Def_N25
import Theorems.Thm_N25_level25_row_normalization

set_option autoImplicit false

namespace N25

private theorem level25_code_injective :
    Function.Injective (fun r : Fin 25 × Fin 25 => r.1.val + 25*r.2.val) := by
  intro r s h
  dsimp only at h
  have hr := r.1.isLt
  have hs := s.1.isLt
  apply Prod.ext <;> apply Fin.ext <;> omega

/-- Equality of the canonical codes is exactly equivalence under the level
subgroup's scalar action, including nonprimitive residue rows. -/
theorem _root_.solution :
    let R := Fin 25 × Fin 25
    let scale : ℕ → R → R := fun h r =>
      (⟨h * r.1.val % 25, Nat.mod_lt _ (by decide)⟩,
       ⟨h * r.2.val % 25, Nat.mod_lt _ (by decide)⟩)
    let code : R → ℕ := fun r => r.1.val + 25 * r.2.val
    let labels : Fin 4 → ℕ := ![1,7,18,24]
    let normcode : R → ℕ := fun r =>
      min (min (code r) (code (scale 7 r))) (min (code (scale 18 r)) (code (scale 24 r)))
    ∀ r s : R, normcode r = normcode s ↔
      ∃ i : Fin 4, scale (labels i) r = s := by
  dsimp only
  have facts := level25_row_normalization
  dsimp only at facts
  rcases facts with ⟨hmin, hinv, hmul, hinverse⟩
  intro r s
  constructor
  · intro h
    obtain ⟨i, hi⟩ := hmin r
    obtain ⟨j, hj⟩ := hmin s
    have scaled := @level25_code_injective
      ((⟨(![1,7,18,24] i) * r.1.val % 25, Nat.mod_lt _ (by decide)⟩ : Fin 25),
       (⟨(![1,7,18,24] i) * r.2.val % 25, Nat.mod_lt _ (by decide)⟩ : Fin 25))
      ((⟨(![1,7,18,24] j) * s.1.val % 25, Nat.mod_lt _ (by decide)⟩ : Fin 25),
       (⟨(![1,7,18,24] j) * s.2.val % 25, Nat.mod_lt _ (by decide)⟩ : Fin 25))
      (hi.trans (h.trans hj.symm))
    obtain ⟨k, hk⟩ := hmul i j
    obtain ⟨l, hl⟩ := hinverse j
    refine ⟨k, ?_⟩
    have equ := (hk r).symm.trans scaled
    have invEqu := congrArg (fun t : Fin 25 × Fin 25 =>
      ((⟨(![1,7,18,24] l) * t.1.val % 25, Nat.mod_lt _ (by decide)⟩ : Fin 25),
       (⟨(![1,7,18,24] l) * t.2.val % 25, Nat.mod_lt _ (by decide)⟩ : Fin 25))) equ
    exact (hl _).symm.trans (invEqu.trans (hl _))
  · rintro ⟨i, rfl⟩
    exact (hinv r i).symm

end N25
