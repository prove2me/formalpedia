-- Prove2me | solution 1 for GlobalTheory.NormTower.exists_eventually_dvd_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:14:47.967679+00:00
-- url     : https://prove2.me/submissions/bdfc32ff-d540-46e4-a001-143c5180e957

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHostNormModCoprimeLevelHalfStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsCompatibleNormTowerProfinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.NormTower
namespace GlobalTheory.NormTower
theorem _root_.solution {E : Type} [Field E] [NumberField E] (U : Ultrafilter ℕ) (s : ℕ → 𝓞 E)
    (n : ℕ) (hn : 0 < n) : ∃ t : 𝓞 E, ∀ᶠ j in (U : Filter ℕ), (n : 𝓞 E) ∣ s j - t := by
  have hI : Ideal.span {(n : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn.ne'
  haveI : Finite (𝓞 E ⧸ Ideal.span {(n : 𝓞 E)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  obtain ⟨c, hc⟩ := Ultrafilter.eq_pure_of_finite
    (U.map fun j => Ideal.Quotient.mk (Ideal.span {(n : 𝓞 E)}) (s j))
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨t, ?_⟩
  have h : {Ideal.Quotient.mk (Ideal.span {(n : 𝓞 E)}) t} ∈
      U.map fun j => Ideal.Quotient.mk (Ideal.span {(n : 𝓞 E)}) (s j) := by
    rw [hc]; exact Ultrafilter.mem_pure.2 rfl
  rw [Ultrafilter.mem_map] at h
  filter_upwards [h] with j hj
  exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hj)
end GlobalTheory.NormTower
