-- Prove2me | solution 1 for GlobalTheory.DirScale.dof_iter_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:12:03.24986+00:00
-- url     : https://prove2.me/submissions/1cc388c7-8852-4ca6-a2a1-c0f605667177

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_DofIterSmulDir
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dof_C_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.DirScale
variable {R : Type} [CommRing R] {d : ℕ}
namespace GlobalTheory.DirScale
theorem _root_.solution (F : Fin d → PS R 2 d) (u : Fin d → R) (n : ℕ) (r : R) (f : PS R 1 d) :
    (Dof F u)^[n] (C r * f) = C r * (Dof F u)^[n] f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, GE.dof_C_mul, ih]
end GlobalTheory.DirScale
