-- Prove2me | solution 1 for GlobalTheory.EigenCongruence.dof_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:11:44.381717+00:00
-- url     : https://prove2.me/submissions/f7ef2079-0b5b-4d91-89e5-5df1f137d80e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfSubMem
import Theorems.Thm_GlobalTheory_EigenCongruence_dof_mem_coeffIdeal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dof_C_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dof_add


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
theorem _root_.solution (F : Fin d → PS R 2 d) (v : Fin d → R) (y c : R) {I : Ideal R} {f g : PS R 1 d}
    (hf : Dof F v f - C y * f ∈ coeffIdeal I) (hg : g - C c * f ∈ coeffIdeal I) :
    Dof F v g - C (y * c) * f ∈ coeffIdeal I := by
  have h1 : Dof F v g = Dof F v (g - C c * f) + C c * Dof F v f := by
    rw [← GE.dof_C_mul, ← GE.dof_add, sub_add_cancel]
  have h2 : Dof F v g - C (y * c) * f =
      Dof F v (g - C c * f) + C c * (Dof F v f - C y * f) := by
    rw [h1, map_mul]; ring
  rw [h2]
  exact Ideal.add_mem _ (dof_mem_coeffIdeal F v hg) (Ideal.mul_mem_left _ _ hf)
end GlobalTheory.EigenCongruence
