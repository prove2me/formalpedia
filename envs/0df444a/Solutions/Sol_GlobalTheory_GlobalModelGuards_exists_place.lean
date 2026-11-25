-- Prove2me | solution 1 for GlobalTheory.GlobalModelGuards.exists_place
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:45:49.195646+00:00
-- url     : https://prove2.me/submissions/828de447-60cf-498b-bdac-766ab18a37f7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_ExistsGoodLevel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GlobalModelGuards
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
namespace GlobalTheory.GlobalModelGuards
theorem _root_.solution (p : ℕ) (hp : p.Prime) : ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits := by
  have hne : (Ideal.span {(p : (⊥ : Subring ℂ))}) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    obtain ⟨n, hn⟩ := Subring.mem_bot.1 v.2
    have h1 : ((p : ℤ) * n : ℤ) = 1 := by
      have := congrArg Subtype.val hv
      simp only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_one] at this
      rw [← hn] at this
      exact_mod_cast this
    have := Int.isUnit_iff_natAbs_eq.1 (IsUnit.of_mul_eq_one _ h1)
    simp at this
    exact hp.one_lt.ne' this
  obtain ⟨W, -, hW⟩ := Ideal.image_subset_nonunits_valuationSubring _ hne
  exact ⟨W, hW ⟨p, Ideal.mem_span_singleton_self _, by simp⟩⟩
end GlobalTheory.GlobalModelGuards
