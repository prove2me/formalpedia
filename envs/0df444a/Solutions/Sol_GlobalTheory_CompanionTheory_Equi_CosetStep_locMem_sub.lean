-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.CosetStep.locMem_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:45:23.20671+00:00
-- url     : https://prove2.me/submissions/035c46eb-db6b-442c-aaa6-fb821e91b7c7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetCongruenceRefinement
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_locMem_add
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_locMem_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Equi GlobalTheory.CompanionTheory.Equi.CosetStep
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.Equi.CosetStep
theorem _root_.solution {I : Ideal (𝓞 F)} {w : HeightOneSpectrum (𝓞 F)} {a b : F}
    (ha : LocMem I w a) (hb : LocMem I w b) : LocMem I w (a - b) := by
  rw [sub_eq_add_neg]; exact locMem_add ha (locMem_neg hb)
end GlobalTheory.CompanionTheory.Equi.CosetStep
