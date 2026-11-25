-- Prove2me | solution 1 for GlobalTheory.DirScale.foldr_smul_dir
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:27:10.584373+00:00
-- url     : https://prove2.me/submissions/ea4d432e-cab4-4c26-8dc5-2795ba9e2a80

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_DofIterSmulDir
import Theorems.Thm_GlobalTheory_DirScale_dof_iter_C_mul
import Theorems.Thm_GlobalTheory_DirScale_dof_iter_smul_dir

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
theorem _root_.solution (F : Fin d → PS R 2 d) {ι : Type} (c : ι → R) (u : ι → Fin d → R)
    (m : ι → ℕ) (f : PS R 1 d) (L : List ι) :
    L.foldr (fun l g => (Dof F (c l • u l))^[m l] g) f =
      C (L.map fun l => c l ^ m l).prod * L.foldr (fun l g => (Dof F (u l))^[m l] g) f := by
  induction L with
  | nil => simp
  | cons l L ih =>
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    rw [ih, dof_iter_smul_dir, dof_iter_C_mul, map_mul, mul_assoc]
end GlobalTheory.DirScale
