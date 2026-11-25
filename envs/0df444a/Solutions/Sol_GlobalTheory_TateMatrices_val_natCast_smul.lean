-- Prove2me | solution 1 for GlobalTheory.TateMatrices.val_natCast_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:50:16.48496+00:00
-- url     : https://prove2.me/submissions/62b54a0b-5aad-4881-9456-436dd8f3e7b0

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_CharR
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsTateMatricesLink

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
theorem _root_.solution {Γ : Type} [AddCommGroup Γ] (N m : ℕ) (x : Γ) (hx : N • x = 0) :
    (m : ZMod N).val • x = m • x := by
  rw [ZMod.val_natCast]
  conv_rhs => rw [← Nat.mod_add_div m N, add_nsmul, mul_nsmul, hx, smul_zero, add_zero]
end GlobalTheory.TateMatrices
