-- Prove2me | solution 1 for GlobalTheory.JointModelGuards.localRing_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:55:05.47725+00:00
-- url     : https://prove2.me/submissions/073b2582-efa2-4620-81fb-9682dd6a7afc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_MemOfEqMulInvPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.JointModelGuards
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.JointModelGuards
theorem _root_.solution (l : Level H) (c : Coeff l) (W : ValuationSubring ℂ) {p : ℕ} (hp : p.Prime)
    (hW : (p : ℂ) ∈ W.nonunits) : c.V W ≠ ⊤ := by
  intro h
  have h1 : ((p : c.F))⁻¹ ∈ c.V W := by rw [h]; trivial
  have h2 : ((p : ℂ))⁻¹ ∈ W := by simpa [ValuationSubring.mem_comap] using h1
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  rw [ValuationSubring.mem_nonunits_iff] at hW
  have h3 := (W.valuation_le_one_iff _).mpr h2
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((map_ne_zero _).mpr hp0))] at h3
  exact absurd hW (not_lt.mpr h3)
end GlobalTheory.JointModelGuards
