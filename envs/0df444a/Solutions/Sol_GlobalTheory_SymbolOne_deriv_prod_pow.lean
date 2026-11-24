-- Prove2me | solution 1 for GlobalTheory.SymbolOne.deriv_prod_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:12:29.776033+00:00
-- url     : https://prove2.me/submissions/f245a7bc-d223-47a3-8b62-47894fd18153

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DerivationMemPowOfMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfProdLinear
import Theorems.Thm_GlobalTheory_SymbolOne_deriv_prod

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
theorem _root_.solution (D : Derivation k A A) (lam : ι → A) (a : ι → ℕ) :
    D (∏ l, lam l ^ a l) =
      ∑ j, (a j : A) * (∏ l, lam l ^ Function.update a j (a j - 1) l) * D (lam j) := by
  rw [deriv_prod]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Derivation.leibniz_pow, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Function.update_self]
  have : ∏ l ∈ Finset.univ.erase j, lam l ^ Function.update a j (a j - 1) l =
      ∏ l ∈ Finset.univ.erase j, lam l ^ a l :=
    Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  rw [this]
  simp only [smul_eq_mul, nsmul_eq_mul]
  ring
end GlobalTheory.SymbolOne
