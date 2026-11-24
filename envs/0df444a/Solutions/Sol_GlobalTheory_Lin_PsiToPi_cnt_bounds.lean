-- Prove2me | solution 1 for GlobalTheory.Lin.PsiToPi.cnt_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:43:54.695639+00:00
-- url     : https://prove2.me/submissions/0116cd7e-04c5-40ca-a762-c7ed3b3b3eef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeCountRelativeErrorOfPsiRelativeError

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.PsiToPi
open Formalism.HermitianLattices.GL2PrimeSums (Li Emain)
namespace GlobalTheory.Lin.PsiToPi
theorem _root_.solution (P : ℕ → Prop) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ cnt P u ∧ cnt P u ≤ u := by
  refine ⟨Nat.cast_nonneg _, le_trans ?_ (Nat.floor_le hu)⟩
  have := Finset.card_filter_le (Finset.Icc 1 ⌊u⌋₊) (fun p => p.Prime ∧ P p)
  rw [Nat.card_Icc, Nat.add_sub_cancel] at this
  unfold cnt
  exact_mod_cast this
end GlobalTheory.Lin.PsiToPi
