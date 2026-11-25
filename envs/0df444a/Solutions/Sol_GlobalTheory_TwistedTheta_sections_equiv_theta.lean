-- Prove2me | solution 1 for GlobalTheory.TwistedTheta.sections_equiv_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:13:34.193259+00:00
-- url     : https://prove2.me/submissions/42b8bbe4-6c4c-408d-8d12-b75a31a532d9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstOfNormPeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SectionsEquivAnArcTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.TwistedTheta
open CubeValues SymmetricSemicharacter EigenNorm FrameValue FieldBaseChange
namespace GlobalTheory.TwistedTheta
theorem _root_.solution (D : Out.DegPre ℂ) {g : ℕ} (u : HolUnif D.P.A D.P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (χ : u.Λ → ℂ) (h : u.IsAH Hm χ) (j : ℕ) (hj : 1 ≤ j) (hθ : ∀ θ, u.IsThetaFn Hm χ j θ → ∃ s, u.IsFnPow j s θ)
    (α : D.X) (c : Fin g → ℂ) (hc : u.ex c = D.c α) :
    ∃ e : SecSpace D j α ≃ₗ[ℂ] thetaShift u Hm χ j c,
      (∀ (s : D.SecB j α) z, (e s : (Fin g → ℂ) → ℂ) z = secVal u D.P.isLB s (u.ex z).left ![z, z + c, c, 0]) ∧
      ∀ (s : D.SecB j α) z (i : Fin 4 → D.P.L.ι), ⊤ ≤ (u.ex z).left ⁻¹ᵁ D.P.L.wchart (D.famφB α) i →
        valAt' (u.ex z).left (D.P.L.wchart (D.famφB α) i) (s.f i) = (e s : (Fin g → ℂ) → ℂ) z *
          (u.fr (i 0) z ^ ((j : ℤ) - 1) * u.fr (i 1) (z + c) * (u.fr (i 2) c)⁻¹ * u.fr (i 3) 0) :=
  ⟨secEquiv h (Nat.one_le_iff_ne_zero.1 hj) hθ hc, fun _ _ => rfl, valAt'_eq_secFn hc⟩
end GlobalTheory.TwistedTheta
