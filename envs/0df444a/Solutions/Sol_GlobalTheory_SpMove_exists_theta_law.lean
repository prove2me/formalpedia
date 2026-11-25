-- Prove2me | solution 1 for GlobalTheory.SpMove.exists_theta_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:03:17.756068+00:00
-- url     : https://prove2.me/submissions/95a69f52-de29-419d-9ea3-959d4e02974e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolUnifReparam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_EntireEqZeroOrEqZeroOfMulEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ThetaLawSymplecticNormalForm
import Theorems.Thm_GlobalTheory_entire_eq_mul_of_sq_eq_mul_sq
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spAct_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SpMove
open Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
namespace GlobalTheory.SpMove
theorem _root_.solution {g : ℕ} {δ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hδ : δ ∈ Matrix.symplecticGroup (Fin g) ℤ) {n n' k k' : Fin g → ℤ}
    (h : KeyPow.ThetaLaw g δ n n' k k') {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g)) :
    ∃ r : ℂ, r ^ 8 = (jAut δ τ).det ^ 4 ∧ ∀ z,
      theta (halfVec k) (halfVec k') (zAct δ τ z) (spAct δ τ) =
        r * Complex.exp (Real.pi * Complex.I * expArg δ τ z) * theta (halfVec n) (halfVec n') z τ := by
  obtain ⟨c, hc, h⟩ := h
  have hz : Differentiable ℂ (zAct δ τ) :=
    (Matrix.mulVecLin ((jAut δ τ)⁻¹)ᵀ).toContinuousLinearMap.differentiable
  have hq : Differentiable ℂ fun z => Real.pi * Complex.I * expArg δ τ z := by
    simp only [expArg, dotProduct, mulVec]
    fun_prop
  obtain ⟨r, hr, H⟩ := entire_eq_mul_of_sq_eq_mul_sq g
    (fun z => theta (halfVec k) (halfVec k') (zAct δ τ z) (spAct δ τ))
    (fun z => theta (halfVec n) (halfVec n') z τ) _ (c * (jAut δ τ).det)
    ((differentiable_theta (spAct_mem hδ hτ) _ _).comp hz) (differentiable_theta hτ _ _) hq
    (fun z => by
      rw [h τ hτ z, eC]
      congr 3
      ring)
  refine ⟨r, ?_, H⟩
  calc r ^ 8 = (r ^ 2) ^ 4 := by ring
    _ = _ := by rw [hr, mul_pow, hc, _root_.one_mul]
end GlobalTheory.SpMove
