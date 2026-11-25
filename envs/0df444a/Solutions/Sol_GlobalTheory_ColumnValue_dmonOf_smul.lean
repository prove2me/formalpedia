-- Prove2me | solution 1 for GlobalTheory.ColumnValue.dmonOf_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:21:45.009967+00:00
-- url     : https://prove2.me/submissions/95dff8d7-5acb-4730-81cf-43826770b064

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_NabTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvariantDerivAlongEndo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsGroupedOfSublist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfSubMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NabValPullbackMonomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NabValColumnsCongr
import Theorems.Thm_GlobalTheory_DerivEndo_iterate_dof_C_mul


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.ColumnValue
namespace GlobalTheory.ColumnValue
theorem _root_.solution {k : Type} [CommRing k] {d : ℕ} (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι]
    (u : ι → Fin d → k) (mo : ι →₀ ℕ) (c : k) (g : PS k 1 d) :
    DmonOf F u mo (c • g) = C c * DmonOf F u mo g := by
  rw [smul_eq_C_mul]
  unfold DmonOf
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons a L ih => rw [List.foldr_cons, List.foldr_cons, ih, DerivEndo.iterate_dof_C_mul]
end GlobalTheory.ColumnValue
