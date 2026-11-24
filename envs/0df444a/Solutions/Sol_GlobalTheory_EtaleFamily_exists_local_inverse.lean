-- Prove2me | solution 1 for GlobalTheory.EtaleFamily.exists_local_inverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:27:39.995887+00:00
-- url     : https://prove2.me/submissions/cd040c00-30dc-46e2-9d62-bd1c69ee4d30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolomorphicSections
import Theorems.Thm_GlobalTheory_AnalyticLineDerivative_main


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
open GlobalTheory GlobalTheory.EtaleFamily
namespace GlobalTheory.EtaleFamily
theorem _root_.solution {E S J σ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [CommRing S] [Fintype J] [Fintype σ] [DecidableEq σ]
    (χ : E → (S →+* ℂ)) (rel : σ → MvPolynomial J S) (c : σ → J) (hc : Function.Bijective c)
    (z₀ : E) (u₀ : J → ℂ) (hχ : ∀ a, AnalyticAt ℂ (fun z => χ z a) z₀)
    (hdet : (Matrix.of fun s r : σ =>
      MvPolynomial.eval₂Hom (χ z₀) u₀ (MvPolynomial.pderiv (c s) (rel r))).det ≠ 0) :
    ∃ Φ : OpenPartialHomeomorph (E × (J → ℂ)) (E × (σ → ℂ)),
      (∀ w, Φ w = (w.1, fun r => MvPolynomial.eval₂Hom (χ w.1) w.2 (rel r))) ∧
      (z₀, u₀) ∈ Φ.source ∧ AnalyticOnNhd ℂ Φ.symm Φ.target := by
  first
  | exact @_root_.GlobalTheory.AnalyticLineDerivative.main
  | exact _root_.GlobalTheory.AnalyticLineDerivative.main
  | (apply _root_.GlobalTheory.AnalyticLineDerivative.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AnalyticLineDerivative.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AnalyticLineDerivative.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AnalyticLineDerivative.main ..)
end GlobalTheory.EtaleFamily
