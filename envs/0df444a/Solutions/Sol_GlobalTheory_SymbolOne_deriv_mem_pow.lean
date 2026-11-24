-- Prove2me | solution 1 for GlobalTheory.SymbolOne.deriv_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:59:48.909106+00:00
-- url     : https://prove2.me/submissions/5e365992-700e-46f2-ad0a-b40f7b91ff03

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
namespace GlobalTheory.SymbolOne
theorem _root_.solution (D : Derivation k A A) (I : Ideal A) (n : ℕ) (x : A) (hx : x ∈ I ^ (n + 1)) :
    D x ∈ I ^ n := by
  first
  | exact @_root_.GlobalTheory.DerivationMemPow.derivation_mem_pow_of_mem_pow_succ
  | exact _root_.GlobalTheory.DerivationMemPow.derivation_mem_pow_of_mem_pow_succ
  | (apply _root_.GlobalTheory.DerivationMemPow.derivation_mem_pow_of_mem_pow_succ <;> assumption)
  | (intros; apply _root_.GlobalTheory.DerivationMemPow.derivation_mem_pow_of_mem_pow_succ <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DerivationMemPow.derivation_mem_pow_of_mem_pow_succ <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DerivationMemPow.derivation_mem_pow_of_mem_pow_succ ..)
end GlobalTheory.SymbolOne
