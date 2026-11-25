-- Prove2me | solution 1 for GlobalTheory.PullBdd.dmin_lact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:14:16.685289+00:00
-- url     : https://prove2.me/submissions/26dea01a-11f0-426a-803d-84947b8d2d7a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_TwoLevelLogarithm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLevelBlockOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CuspFormPullbackIsBoundedSection
import Theorems.Thm_GlobalTheory_CMLattice_embAll_apply
import Theorems.Thm_GlobalTheory_PerMove_col_mul
import Theorems.Thm_GlobalTheory_PerMove_hermC_unitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMLattice.embAll_apply



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open scoped Matrix
open GlobalTheory GlobalTheory.PullBdd
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.PullBdd
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {β : GL (Fin r) E}
    (hβ : ∀ u v, herm G ((β : Matrix (Fin r) (Fin r) E) *ᵥ u) ((β : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm G u v) (x : Frame Ψ r) (τ : Ψ) (i : Fin (r + 1)) :
    dmin G (lact β x) τ i = dmin G x τ i := by
  have e1 : mat (lact β x) τ = (β : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  have e2 : gram τ.1 G (mat (lact β x) τ) = gram τ.1 G (mat x τ) := by
    ext a b
    simp only [gram, Matrix.of_apply, e1, PerMove.col_mul, PerMove.hermC_unitary _ _ _ hβ]
  unfold dmin
  rw [e2]
end GlobalTheory.PullBdd
