-- Prove2me | solution 1 for GlobalTheory.EigenCongruence.dof_mem_coeffIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:49:12.573436+00:00
-- url     : https://prove2.me/submissions/b6b8492c-0570-4c1d-bdaf-990446add985

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfSubMem
import Theorems.Thm_GlobalTheory_EigenCongruence_pderiv_mem_coeffIdeal

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
open GlobalTheory GlobalTheory.EigenCongruence
variable {R : Type} [CommRing R] {d : ℕ}
namespace GlobalTheory.EigenCongruence
theorem _root_.solution (F : Fin d → PS R 2 d) (v : Fin d → R) {I : Ideal R} {g : PS R 1 d}
    (hg : g ∈ coeffIdeal I) : Dof F v g ∈ coeffIdeal I :=
  Ideal.sum_mem _ fun _ _ => Ideal.mul_mem_left _ _ (pderiv_mem_coeffIdeal hg _)
end GlobalTheory.EigenCongruence
