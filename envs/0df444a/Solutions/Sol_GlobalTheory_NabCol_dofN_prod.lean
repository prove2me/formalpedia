-- Prove2me | solution 1 for GlobalTheory.NabCol.dofN_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:53:01.937612+00:00
-- url     : https://prove2.me/submissions/cc8a17ae-eb85-460f-9c80-9804f81f5f98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumSupportRename
import Theorems.Thm_GlobalTheory_NabCol_dofN_inCol
import Theorems.Thm_GlobalTheory_NabCol_pderiv_prod_out
import Theorems.Thm_GlobalTheory_NabCol_dofN_mul_out

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
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.PowGerm
open GlobalTheory GlobalTheory.NabCol
variable {k : Type} [CommRing k] {d n : ℕ}
namespace GlobalTheory.NabCol
theorem _root_.solution (F : Fin d → PS k 2 d) (c : Fin n) (u : Fin d → k) (g : Fin n → PS k 1 d) :
    DofN F c u (∏ b, inCol b (g b)) = ∏ b, inCol b (colD F c u b (g b)) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ c), ← Finset.mul_prod_erase _ _ (Finset.mem_univ c),
    dofN_mul_out F c u _ _ (fun j => pderiv_prod_out c j g _ (Finset.notMem_erase c _)), dofN_inCol]
  congr 1
  · simp [colD]
  · refine Finset.prod_congr rfl fun b hb => ?_
    rw [colD, if_neg (Finset.ne_of_mem_erase hb).symm]
    rfl
end GlobalTheory.NabCol
