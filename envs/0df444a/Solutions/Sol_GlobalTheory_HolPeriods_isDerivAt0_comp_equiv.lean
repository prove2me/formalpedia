-- Prove2me | solution 1 for GlobalTheory.HolPeriods.isDerivAt0_comp_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:37:17.907098+00:00
-- url     : https://prove2.me/submissions/c7368519-9a14-4cde-8a56-d809654902ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDifferentiableOnTransfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HolPeriods
namespace GlobalTheory.HolPeriods
theorem _root_.solution {g : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) :
    IsDerivAt0 (fun z => e (k z)) w v ↔ IsDerivAt0 e (k w) v := by
  have : ∀ (U : X.Opens) (f : Γ(X, U)), fderiv ℂ (fun z => valAt' (e (k z)) U f) 0 w =
      fderiv ℂ (fun z => valAt' (e z) U f) 0 (k w) := by
    intro U f
    have := k.toContinuousLinearEquiv.comp_right_fderiv (f := fun z => valAt' (e z) U f) (x := 0)
    have h2 := congrArg (fun L => L w) this
    simpa [Function.comp_def] using h2
  simp only [IsDerivAt0, map_zero, this]
end GlobalTheory.HolPeriods
