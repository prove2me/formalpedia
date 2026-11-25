-- Prove2me | solution 1 for GlobalTheory.SymbolCols.coeff_mul_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:59:48.202433+00:00
-- url     : https://prove2.me/submissions/7261af3c-7c2a-463c-8d50-c2142622f5e4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfCongrJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfProdLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumProdConstantCoeffDmonOfCols

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.SymbolCols
namespace GlobalTheory.SymbolCols
theorem _root_.solution {k σ : Type} [CommRing k] (N : ℕ) (f g E : MvPowerSeries σ k)
    (h : ∀ mo : σ →₀ ℕ, mo.degree ≤ N → coeff mo f = coeff mo g)
    (mo : σ →₀ ℕ) (hmo : mo.degree ≤ N) : coeff mo (f * E) = coeff mo (g * E) := by
  classical
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = mo := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hd : p.1.degree + p.2.degree = mo.degree := by rw [← hp', map_add]
  rw [h p.1 (by omega)]
end GlobalTheory.SymbolCols
