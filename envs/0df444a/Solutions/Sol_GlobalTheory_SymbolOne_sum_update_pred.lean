-- Prove2me | solution 1 for GlobalTheory.SymbolOne.sum_update_pred
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:23:20.564536+00:00
-- url     : https://prove2.me/submissions/910350b0-d8be-45e0-8a24-a54d5d8f4638

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DerivationMemPowOfMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfProdLinear

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
open GlobalTheory GlobalTheory.SymbolOne
variable {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
variable {ι : Type}
variable [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.SymbolOne
theorem _root_.solution (a : ι → ℕ) (j : ι) (h : a j ≠ 0) :
    ∑ l, Function.update a j (a j - 1) l + 1 = ∑ l, a l := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ j), ← Finset.add_sum_erase _ a (Finset.mem_univ j),
    Finset.sdiff_singleton_eq_erase]
  omega
end GlobalTheory.SymbolOne
