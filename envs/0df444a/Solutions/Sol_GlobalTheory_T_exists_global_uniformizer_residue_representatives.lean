-- Prove2me | solution 1 for GlobalTheory.T.exists_global_uniformizer_residue_representatives
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:32:20.525678+00:00
-- url     : https://prove2.me/submissions/8f396f20-b317-4870-9bb2-029a7040dae1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsGlobalUniformizerResidueRepresentatives
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsGlobalUniformizerResidueRepresentativesStatement
import Theorems.Thm_GlobalTheory_QNorm_exists_uniformizer_and_residue_representatives


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), (∃ π : F, v.valuation F π = WithZero.exp (-1) ∧ Valued.v (algebraMap F (v.adicCompletion F) π) = WithZero.exp (-1)) ∧ (∀ x : F, Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x) ∧ (∀ x : v.adicCompletion F, Valued.v x ≤ 1 → ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (a : F)) < 1) ∧ ∃ R : Finset (v.adicCompletion F), R.card ≤ Ideal.absNorm v.asIdeal ∧ (∀ r ∈ R, Valued.v r ≤ 1) ∧ ∀ x : v.adicCompletion F, Valued.v x ≤ 1 → ∃ r ∈ R, Valued.v (x - r) < 1 := by
  first | exact @GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives | exact GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives | (intros; apply GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives <;> assumption)
end _root_.GlobalTheory.T
