-- Prove2me | solution 1 for GlobalTheory.exists_theta_multiplier_of_two_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:27:29.483814+00:00
-- url     : https://prove2.me/submissions/1334f4ab-6d39-466b-8e66-3a1f658453c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FromBlocksMapIntCastMemSymplecticGroup
import Theorems.Thm_GlobalTheory_odd_det_of_mem_symplecticGroup
import Theorems.Thm_GlobalTheory_exists_theta_multiplier_of_odd_det
import Theorems.Thm_GlobalTheory_even_dotProduct_mulVec_of_two_dvd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped Real
noncomputable section
open GlobalTheory
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ} {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
namespace GlobalTheory
theorem _root_.solution (hγ : γ ∈ symplecticGroup (Fin g) ℤ)
    (hb : ∀ i j, 2 ∣ γ.toBlocks₁₂ i j) (hc : ∀ i j, 2 ∣ γ.toBlocks₂₁ i j) :
    ∃ l : Matrix (Fin g) (Fin g) ℂ → ℂ, IsHoloSiegel g l ∧ ∀ τ ∈ SiegelH (Fin g),
      (∀ z, theta 0 0 (zAct γ τ z) (spAct γ τ) * eC (-expArg γ τ z / 2) = l τ * theta 0 0 z τ) ∧
      l τ ^ 2 = (ZMod.χ₄ (γ.toBlocks₂₂.det : ZMod 4) : ℤ) * (jAut γ τ).det :=
  exists_theta_multiplier_of_odd_det hγ
    (odd_det_of_mem_symplecticGroup (by rwa [fromBlocks_toBlocks]) hb)
    (even_dotProduct_mulVec_of_two_dvd hb _) (even_dotProduct_mulVec_of_two_dvd hc _)
end GlobalTheory
