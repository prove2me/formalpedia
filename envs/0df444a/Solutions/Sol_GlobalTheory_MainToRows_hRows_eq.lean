-- Prove2me | solution 1 for GlobalTheory.MainToRows.hRows_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:28:30.293986+00:00
-- url     : https://prove2.me/submissions/457357b3-bf1f-458b-a849-4296e037efff

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MainTermImpliesRowHypothesis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds
noncomputable section
open scoped BigOperators
open Classical MvPowerSeries Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
open GlobalTheory GlobalTheory.MainToRows
variable {C : Type} [Field C]
namespace GlobalTheory.MainToRows
theorem _root_.solution (n0 : ℕ) (H : MvPowerSeries (Fin n0 ⊕ Fin n0) C) :
    hRows n0 H = ∑ ρ : Fin n0, rename (rowE ρ) H := by
  unfold hRows
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [rename_eq_subst]
  congr 1
  funext x
  rcases x with x | x <;> rfl
end GlobalTheory.MainToRows
