-- Prove2me | solution 1 for NonstatNV.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:38:21.065427+00:00
-- url     : https://prove2.me/submissions/e1caffb8-0821-4139-bd78-cda6528e681e

import Definitions.Def_NonstatNV_Model_Standing
import Definitions.Def_NonstatNV_Model_LipschitzCost

open MeasureTheory

open NonstatNV in
theorem solution (M : Model) (ℓ : ℝ) (hM : M.Standing) (hℓ : M.LipschitzCost ℓ)
    (b h : ℝ) (hb : b ∈ Set.Icc 0 M.bmax) (hh : h ∈ Set.Icc 0 M.hmax)
    (μ₁ μ₂ : ℝ) (hμ₁ : μ₁ ∈ Set.Icc M.μmin M.μmax) (hμ₂ : μ₂ ∈ Set.Icc M.μmin M.μmax)
    (q₁ q₂ : ℝ) (hq₁ : q₁ ∈ M.Q) (hq₁min : ∀ q ∈ M.Q, M.cost μ₁ b h q₁ ≤ M.cost μ₁ b h q)
    (hq₂ : q₂ ∈ M.Q) (hq₂min : ∀ q ∈ M.Q, M.cost μ₂ b h q₂ ≤ M.cost μ₂ b h q) :
    M.cost μ₁ b h q₂ - M.cost μ₁ b h q₁ ≤ 2 * ℓ * |μ₁ - μ₂| := by
  have h1 := hℓ.2 b hb h hh q₂ hq₂ μ₁ hμ₁ μ₂ hμ₂
  have h2 := hℓ.2 b hb h hh q₁ hq₁ μ₁ hμ₁ μ₂ hμ₂
  have h3 := hq₂min q₁ hq₁
  have a1 := (abs_le.mp h1).2
  have a2 := (abs_le.mp h2).1
  linarith
