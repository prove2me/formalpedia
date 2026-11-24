-- Prove2me | solution 1 for GlobalTheory.T.coset_congruence_refinement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:05:33.163394+00:00
-- url     : https://prove2.me/submissions/ee2a0192-e207-44f2-939a-2b9ae937bda5

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetCongruenceRefinement
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetCongruenceRefinementStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_coset_step


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)), v ∉ S → ∀ (I : Ideal (𝓞 F)), I ≠ ⊥ → ¬ I ≤ v.asIdeal → ∀ (k : ℕ) (x0 : ι → F) (c : ι → Fv F v), ∃ x1 : ι → F, ∀ x : ι → F, (x ∈ cosetOff (insert v S) I x0 ∧ ∀ i, algebraMap F (Fv F v) (x i) - c i ∈ ballV v k) ↔ x ∈ cosetOff S (I * v.asIdeal ^ k) x1 := by
  first | exact @GlobalTheory.CompanionTheory.Equi.CosetStep.coset_step | exact GlobalTheory.CompanionTheory.Equi.CosetStep.coset_step | (intros; apply GlobalTheory.CompanionTheory.Equi.CosetStep.coset_step <;> assumption)
end _root_.GlobalTheory.T
