-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnramDict.exists_value_eq_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:54:51.053577+00:00
-- url     : https://prove2.me/submissions/1786a028-3e7e-45e2-96e0-db3a4a5bf955

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedExtensionIntegralBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Topology Filter
open PositivityTheory.Rg.Tf.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnramDict
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}
namespace GlobalTheory.CompanionTheory.UnramDict
theorem _root_.solution {π : K} (h0 : valuation K π ≠ 0) (h1 : valuation K π < 1)
    (hmax : ∀ x : K, valuation K x < 1 → valuation K x ≤ valuation K π) {x : K} (hx : x ≠ 0) :
    ∃ m : ℤ, valuation K x = valuation K π ^ m := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have hb0 : e (valuation K π) ≠ 0 := by
    intro h
    exact h0 (e.injective (h.trans (map_zero e).symm))
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (e.symm (WithZero.exp (-1 : ℤ)))
  have hey : e (valuation K y) = WithZero.exp (-1 : ℤ) := by rw [hy]; simp
  have hy1 : valuation K y < 1 := by
    rw [← e.strictMono.lt_iff_lt, hey, map_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hle : e (valuation K y) ≤ e (valuation K π) := e.strictMono.monotone (hmax y hy1)
  have hlt : e (valuation K π) < 1 := by simpa using e.strictMono h1
  have hb : e (valuation K π) = WithZero.exp (-1 : ℤ) := by
    obtain ⟨b, hbe⟩ : ∃ b : ℤ, e (valuation K π) = WithZero.exp b := ⟨_, (WithZero.exp_log hb0).symm⟩
    rw [hbe] at hle hlt ⊢
    rw [hey, WithZero.exp_le_exp] at hle
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
    congr 1
    omega
  have hx0 : e (valuation K x) ≠ 0 := by
    intro h
    exact (Valuation.ne_zero_iff _).2 hx (e.injective (h.trans (map_zero e).symm))
  refine ⟨-WithZero.log (e (valuation K x)), e.injective ?_⟩
  have hz : (WithZero.exp (-1 : ℤ)) ^ (-WithZero.log (e (valuation K x))) =
      e (valuation K x) := by
    rw [← WithZero.exp_zsmul]
    simpa using WithZero.exp_log hx0
  show e (valuation K x) = e (valuation K π ^ (-WithZero.log (e (valuation K x))))
  rw [map_zpow₀ e, hb, hz]
end GlobalTheory.CompanionTheory.UnramDict
