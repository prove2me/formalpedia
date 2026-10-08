-- Prove2me | solution 1 for GrothendieckTeichmuller.brown_free_lie_subalgebra
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T12:54:24.989111+00:00
-- url     : https://prove2.me/submissions/29ff5421-58f6-4c25-8336-e30c116947e9

import Definitions.Def_GT_grt1
import Theorems.Thm_GrothendieckTeichmuller_deligne_drinfeld_ihara
import Mathlib


section
section
namespace GrothendieckTeichmuller

theorem brown_free_lie_subalgebra_oai :
    ∃ sigma : ℕ → Lxy,
      (∀ p, sigma p ∈ grt1 ∧ IsHomogeneousOfDegree (2 * p + 3) (sigma p)) ∧
      Function.Injective
        ⇑(FreeLieAlgebra.lift ℚ (fun p : ℕ => iharaDeriv (sigma p))) := by
  obtain ⟨sigma, h1, h2, -⟩ := deligne_drinfeld_ihara
  exact ⟨sigma, h1, h2⟩

end GrothendieckTeichmuller

end
end

section
open GrothendieckTeichmuller

theorem solution :
    ∃ sigma : ℕ → Lxy,
      (∀ p, sigma p ∈ grt1 ∧ IsHomogeneousOfDegree (2 * p + 3) (sigma p)) ∧
      Function.Injective
        ⇑(FreeLieAlgebra.lift ℚ (fun p : ℕ => iharaDeriv (sigma p))) := by
  apply GrothendieckTeichmuller.brown_free_lie_subalgebra_oai <;> assumption

end
