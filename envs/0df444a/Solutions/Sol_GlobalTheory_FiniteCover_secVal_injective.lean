-- Prove2me | solution 1 for GlobalTheory.FiniteCover.secVal_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:11:04.746921+00:00
-- url     : https://prove2.me/submissions/61fcf026-e212-49d7-bb22-07514407f7fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringDominatingSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecValEqIff
import Theorems.Thm_GlobalTheory_FiniteCover_generic_mem
import Theorems.Thm_GlobalTheory_FiniteCover_toField_injective
import Theorems.Thm_GlobalTheory_FiniteCover_toField_coord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.FiniteCover
variable {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']
variable {M : LB X} {k₀ : M.ι} (h₀ : genericPoint X ∈ M.U k₀)
namespace GlobalTheory.FiniteCover
theorem _root_.solution {V : X.Opens} (hV : genericPoint X ∈ V) :
    Function.Injective (secVal h₀ hV) := fun σ τ h => GlobalTheory.LB.sec_ext fun k => by
  by_cases hk : genericPoint X ∈ M.U k
  · refine toField_injective (U := V ⊓ M.U k) (generic_inf (hV) (hk)) ?_
    rw [toField_coord h₀ hV σ hk, toField_coord h₀ hV τ hk, h]
  · have : V ⊓ M.U k = ⊥ := eq_bot_iff.2 fun x hx => (hk (generic_mem hx.2)).elim
    have : Subsingleton Γ(X, V ⊓ M.U k) := this ▸ inferInstance
    exact Subsingleton.elim _ _
end GlobalTheory.FiniteCover
