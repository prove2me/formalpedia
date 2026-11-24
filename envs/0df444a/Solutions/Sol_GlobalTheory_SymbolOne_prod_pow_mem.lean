-- Prove2me | solution 1 for GlobalTheory.SymbolOne.prod_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:59:52.170183+00:00
-- url     : https://prove2.me/submissions/f7dc7e6d-3cd1-4bf7-aed4-8841c320f3f2

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
theorem _root_.solution (I : Ideal A) (lam : ι → A) (hlam : ∀ l, lam l ∈ I) (a : ι → ℕ) :
    ∏ l, lam l ^ a l ∈ I ^ (∑ l, a l) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun l _ => Ideal.pow_mem_pow (hlam l) _
end GlobalTheory.SymbolOne
