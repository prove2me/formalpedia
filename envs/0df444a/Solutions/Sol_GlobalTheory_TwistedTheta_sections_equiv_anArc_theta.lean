-- Prove2me | solution 1 for GlobalTheory.TwistedTheta.sections_equiv_anArc_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:26.4678+00:00
-- url     : https://prove2.me/submissions/6753fa5c-435d-402c-ad54-83b131e151ed

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
import Theorems.Thm_GlobalTheory_TwistedTheta_theta_eq_thetaShift
import Theorems.Thm_GlobalTheory_TwistedTheta_sections_equiv_theta

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
theorem _root_.solution {O : Type} [CommRing O] [StarRing O] (A : AnArc O) (D : Out.DegPre ℂ)
    (u : HolUnif D.P.A D.P.L A.gB) (χ : u.Λ → ℂ) (hΛ : u.Λ = A.abelian₂)
    (hχ : ∀ (l : u.Λ) (l' : A.abelian₂), (l : Fin A.gB → ℂ) = l' → χ l = A.chi l') (h : u.IsAH A.Hm χ) (j : ℕ) (hj : 1 ≤ j)
    (hθ : ∀ θ, u.IsThetaFn A.Hm χ j θ → ∃ s, u.IsFnPow j s θ) (α : D.X) (x : A.X) (hc : u.ex (A.ct x) = D.c α) :
    ∃ e : SecSpace D j α ≃ₗ[ℂ] A.Theta j x,
      (∀ (s : D.SecB j α) z, (e s : (Fin A.gB → ℂ) → ℂ) z =
        secVal u D.P.isLB s (u.ex z).left ![z, z + A.ct x, A.ct x, 0]) ∧
      ∀ (s : D.SecB j α) z (i : Fin 4 → D.P.L.ι), ⊤ ≤ (u.ex z).left ⁻¹ᵁ D.P.L.wchart (D.famφB α) i →
        valAt' (u.ex z).left (D.P.L.wchart (D.famφB α) i) (s.f i) = (e s : (Fin A.gB → ℂ) → ℂ) z *
          (u.fr (i 0) z ^ ((j : ℤ) - 1) * u.fr (i 1) (z + A.ct x) * (u.fr (i 2) (A.ct x))⁻¹ * u.fr (i 3) 0) := by
  rw [theta_eq_thetaShift A u χ hΛ hχ]
  exact sections_equiv_theta D u A.Hm χ h j hj hθ α _ hc
end GlobalTheory.TwistedTheta
