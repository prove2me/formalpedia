-- Prove2me | solution 1 for GlobalTheory.ZM.ThIdeal.component_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:31:53.904074+00:00
-- url     : https://prove2.me/submissions/52a9cb66-76e5-4a0e-801e-eea4873dde57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaPointsVanishingIdealRadicalHomogeneous
import Theorems.Thm_GlobalTheory_ZM_ThIdeal_coeff_scale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.ThIdeal
namespace GlobalTheory.ZM.ThIdeal
theorem _root_.solution {R σ : Type} [CommRing R] (β : R →+* ℂ) (w : σ → ℂ)
    (F : MvPolynomial σ R) (e : ℕ)
    (h : ∀ c : ℂ, c ≠ 0 → MvPolynomial.eval₂Hom β (fun i => c * w i) F = 0) :
    MvPolynomial.eval₂Hom β w (MvPolynomial.homogeneousComponent e F) = 0 := by
  rw [← coeff_scale]
  have : MvPolynomial.eval₂Hom ((Polynomial.C : ℂ →+* Polynomial ℂ).comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) F = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (s := {0}ᶜ) (fun c hc => ?_) (Set.finite_singleton (0 : ℂ)).infinite_compl
    have h1 := MvPolynomial.map_eval₂Hom ((Polynomial.C : ℂ →+* Polynomial ℂ).comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) (Polynomial.evalRingHom c) F
    rw [Set.mem_ofPred_eq, Polynomial.IsRoot.def, ← Polynomial.coe_evalRingHom, h1, ← h c hc]
    congr 2
    · ext r; simp
    · ext i; simp [_root_.mul_comm c]
  rw [this, Polynomial.coeff_zero]
end GlobalTheory.ZM.ThIdeal
