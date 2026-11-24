-- Prove2me | solution 1 for GlobalTheory.LagSplit.eq_secH_of_conj_mem_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:45:08.232797+00:00
-- url     : https://prove2.me/submissions/b175fa79-48e2-4786-bdaa-2999588c4d4d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_BetaEqZeroOfCharacter
import Theorems.Thm_GlobalTheory_LagSplit_perProj_secH
import Theorems.Thm_GlobalTheory_LagSplit_mem_range_secH_iff

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
    {u : Fin g ⊕ Fin g → ℂ} {z : Fin g → ℂ} (hu : perProj τ u = z) (hc : perProj τ (star u) = 0) :
    u = secH τ z := by
  obtain ⟨v, rfl⟩ := (mem_range_secH_iff hY u).mpr hc
  rw [perProj_secH hY] at hu
  rw [hu]
end GlobalTheory.LagSplit
