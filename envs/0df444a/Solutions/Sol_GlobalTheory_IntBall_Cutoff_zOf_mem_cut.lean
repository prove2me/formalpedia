-- Prove2me | solution 1 for GlobalTheory.IntBall.Cutoff.zOf_mem_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:18:23.19438+00:00
-- url     : https://prove2.me/submissions/c2d4523e-55aa-4b82-825e-ecebef4eab64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OfRealGramDeterminantBoundLeProdCutoff
import Theorems.Thm_GlobalTheory_IntBall_Cutoff_norm_entry_le_opNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
open GlobalTheory GlobalTheory.IntBall GlobalTheory.IntBall.Cutoff
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.IntBall.Cutoff
theorem _root_.solution (X : Data E r) {z : V (nd X)} (hz : z ∈ Om X) (τ : X.Ψ) :
    zOf X z τ ∈ {w : Low r → ℂ | ∀ p : Low r, (p.1.2 : ℕ) < X.p0 → X.p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1} := by
  intro p hb ha
  have he : zOf X z τ p = zBlock X z τ ⟨p.1.1, ha⟩ ⟨p.1.2, hb⟩ := by
    simp [zBlock, nmat, zOf, p.2]
  rw [he]
  exact ((norm_entry_le_opNorm _ _ _).trans (hz τ).le)
end GlobalTheory.IntBall.Cutoff
