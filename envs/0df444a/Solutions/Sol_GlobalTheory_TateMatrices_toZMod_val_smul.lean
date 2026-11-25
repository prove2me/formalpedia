-- Prove2me | solution 1 for GlobalTheory.TateMatrices.toZMod_val_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:12:53.157999+00:00
-- url     : https://prove2.me/submissions/6b51220e-051c-4ebe-8131-00cfc72dfb6e

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_CharR
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsTateMatricesLink
import Theorems.Thm_GlobalTheory_TateMatrices_map_eq_val
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
theorem _root_.solution {Γ : Type} [AddCommGroup Γ] (c : ℤ_[p]) (x : Γ) (hx : p • x = 0) :
    (PadicInt.toZMod c).val • x = (PadicInt.toZModPow (0 + 1) c).val • x := by
  rw [map_eq_val (PadicInt.toZMod (p := p)) (0 + 1) (by simp) c, val_natCast_smul p _ x hx]
end GlobalTheory.TateMatrices
