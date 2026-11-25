-- Prove2me | solution 1 for GlobalTheory.LagSplit.secH_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:58:58.069348+00:00
-- url     : https://prove2.me/submissions/439f416b-376f-4a87-8e33-01640cb95a45

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_BetaEqZeroOfCharacter
import Theorems.Thm_GlobalTheory_LagSplit_perProj_secH
import Theorems.Thm_GlobalTheory_LagSplit_mem_range_secH_iff
import Theorems.Thm_GlobalTheory_LagSplit_eq_secH_of_conj_mem_ker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Key.Chi
open GlobalTheory GlobalTheory.LagSplit
variable {g : ℕ}
namespace GlobalTheory.LagSplit
theorem _root_.solution {τ : Matrix (Fin g) (Fin g) ℂ} (hY : IsUnit (τ.map Complex.im).det)
    (A : (Fin g ⊕ Fin g → ℂ) → (Fin g ⊕ Fin g → ℂ)) (B : (Fin g → ℂ) → (Fin g → ℂ)) (hB : B 0 = 0)
    (hA : ∀ u, A (star u) = star (A u)) (hAB : ∀ u, perProj τ (A u) = B (perProj τ u))
    (z : Fin g → ℂ) : secH τ (B z) = A (secH τ z) := by
  refine (eq_secH_of_conj_mem_ker hY ?_ ?_).symm
  · rw [hAB, perProj_secH hY]
  · rw [← hA, hAB, (mem_range_secH_iff hY _).mp ⟨z, rfl⟩, hB]
end GlobalTheory.LagSplit
