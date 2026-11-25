-- Prove2me | solution 1 for GlobalTheory.TateMatrices.val_mul_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:08:47.789223+00:00
-- url     : https://prove2.me/submissions/f8c637a7-ece4-4eb4-92ac-42d43e501567

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_CharR
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsTateMatricesLink
import Theorems.Thm_GlobalTheory_TateMatrices_val_natCast_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2
noncomputable section
open GlobalTheory
open GlobalTheory.TateMatrices
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory.TateMatrices
theorem _root_.solution {Γ : Type} [AddCommGroup Γ] (a b : ZMod p) (x : Γ) (hx : p • x = 0) :
    (a * b).val • x = a.val • b.val • x := by
  rw [← mul_nsmul', ← val_natCast_smul p (a.val * b.val) x hx]
  simp
end GlobalTheory.TateMatrices
