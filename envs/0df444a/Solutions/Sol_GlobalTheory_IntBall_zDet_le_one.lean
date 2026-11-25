-- Prove2me | solution 1 for GlobalTheory.IntBall.zDet_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:48:12.348495+00:00
-- url     : https://prove2.me/submissions/0df33628-caf1-4508-b9aa-5e0afe96a236

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetOneSubOffDiagonalBlockGramLeOneBall
import Theorems.Thm_GlobalTheory_IntBall_DetLe_re_det_one_sub_le_of_unique
import Theorems.Thm_P2M_GlobalTheory_IntBall_DetLe_re_det_one_sub_le_of_unique__1c5d5c652355

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
open GlobalTheory GlobalTheory.IntBall
open GlobalTheory.IntBall.DetLe
namespace GlobalTheory.IntBall
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (X.p0 = 1 ∨ X.p0 + 1 = r) → ∀ z : V (nd X), z ∈ Om X → ∀ τ : X.Ψ, zDet X z τ ≤ 1 := by
  intro E _ _ _ r X h z _ τ
  have hle := X.p0_le
  unfold zDet
  rcases h with h | h
  · letI : Unique {b : Fin r // (b : ℕ) < X.p0} :=
      { default := ⟨⟨0, by omega⟩, by simp [h]⟩
        uniq := fun b => Subtype.ext (Fin.ext (by have := b.2; simp only; omega)) }
    exact re_det_one_sub_le_of_unique _
  · letI : Unique {a : Fin r // X.p0 ≤ (a : ℕ)} :=
      { default := ⟨⟨X.p0, by omega⟩, le_refl _⟩
        uniq := fun a => Subtype.ext (Fin.ext (by have := a.2; have := a.1.2; simp only; omega)) }
    exact re_det_one_sub_le_of_unique' _
end GlobalTheory.IntBall
