-- Prove2me | solution 1 for GlobalTheory.IwahoriInj.eventually_deep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:55.386397+00:00
-- url     : https://prove2.me/submissions/4cc363da-2297-476a-9df8-c4f387ee24b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.IwahoriInj
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.IwahoriInj
theorem _root_.solution (x : k) : ∀ᶠ m : ℕ in Filter.atTop, Deep (-(m : ℤ)) x := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, valuation k x ≤ (uniformizer k)⁻¹ ^ m := by
    exact MulArchimedean.arch _ ((one_lt_inv₀ unif_pos).2 uniformizer_lt_one)
  filter_upwards [Filter.eventually_ge_atTop m] with m' hm'
  have : Deep (-(m : ℤ)) x := by simpa [Deep] using hm
  exact this.mono (by omega)
end GlobalTheory.IwahoriInj
