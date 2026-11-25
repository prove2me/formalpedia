-- Prove2me | solution 1 for GlobalTheory.DirScale.dof_iter_smul_dir
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:21:33.35125+00:00
-- url     : https://prove2.me/submissions/b51cfd66-d3b4-4b64-8524-7f23f8dd0784

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_DofIterSmulDir
import Theorems.Thm_GlobalTheory_DirScale_dof_smul_dir
import Theorems.Thm_GlobalTheory_DirScale_dof_iter_C_mul

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
theorem _root_.solution (F : Fin d → PS R 2 d) (c : R) (u : Fin d → R) (n : ℕ) (f : PS R 1 d) :
    (Dof F (c • u))^[n] f = C (c ^ n) * (Dof F u)^[n] f := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, dof_smul_dir, dof_iter_C_mul,
      pow_succ, map_mul, mul_assoc]
end GlobalTheory.DirScale
