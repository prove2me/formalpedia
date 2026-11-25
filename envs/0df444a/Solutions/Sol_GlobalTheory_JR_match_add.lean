-- Prove2me | solution 1 for GlobalTheory.JR.match_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:16:09.971148+00:00
-- url     : https://prove2.me/submissions/4cffc080-d1b9-4131-bc97-216e91e8ede8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitalIntegrandIsLocallyConstantCoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisMatchingAdd
import Theorems.Thm_GlobalTheory_JR_MatchAdd_integrable_of_isTest
import Theorems.Thm_GlobalTheory_T_jacquetRallis_borderedMatrix_normalForm_invariants
import Theorems.Thm_GlobalTheory_T_jacquetRallis_orbitalIntegrand_isLocallyConstantCompactSupport


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
namespace GlobalTheory.JR
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (f₁' f₂' : Gl r F → ℂ) (f₁ f₂ : Hn r F E → ℂ), IsTest f₁' → IsTest f₂' → IsTest f₁ → IsTest f₂ → Match M f₁' f₁ → Match M f₂' f₂ → Match M (f₁' + f₂') (f₁ + f₂) := by
  intro F E _ _ _ _ _ r M f₁' f₂' f₁ f₂ h₁' h₂' h₁ h₂ m₁ m₂ a ha
  obtain ⟨hG, hU⟩ := GlobalTheory.T.jacquetRallis_orbitalIntegrand_isLocallyConstantCompactSupport F E r M
  obtain ⟨-, hsec, -⟩ := GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants F r
  have ha' : Delta (inv (sec a)) ≠ 0 := by rw [hsec]; exact ha
  have eG : orbG M (f₁' + f₂') (sec a) = orbG M f₁' (sec a) + orbG M f₂' (sec a) := by
    letI := M.mG
    haveI := M.bG
    haveI := M.haarG
    unfold orbG
    simp only [Pi.add_apply, add_mul]
    exact integral_add (MatchAdd.integrable_of_isTest _ (hG _ h₁' _ ha'))
      (MatchAdd.integrable_of_isTest _ (hG _ h₂' _ ha'))
  have eU : ∀ X : Hn r F E, HasInv X a → orbU M (f₁ + f₂) X = orbU M f₁ X + orbU M f₂ X := by
    intro X hX
    letI := M.mU
    haveI := M.bU
    haveI := M.haarU
    unfold orbU
    simp only [Pi.add_apply]
    exact integral_add (MatchAdd.integrable_of_isTest _ (hU _ h₁ a X ha hX))
      (MatchAdd.integrable_of_isTest _ (hU _ h₂ a X ha hX))
  refine ⟨fun X hX => ?_, fun hn => ?_⟩
  · rw [eG, eU X hX, (m₁ a ha).1 X hX, (m₂ a ha).1 X hX]
  · rw [eG, (m₁ a ha).2 hn, (m₂ a ha).2 hn, add_zero]
end GlobalTheory.JR
