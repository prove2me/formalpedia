-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.CosetTop.cosetOff_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:00:08.216888+00:00
-- url     : https://prove2.me/submissions/99f9f2f9-23d0-4f22-9bac-009ed3481f20

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetUnitIdealIntegral
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetTop_algebraMap_mem_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetTop_locMem_top_iff

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Equi GlobalTheory.CompanionTheory.Equi.CosetTop
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.Equi.CosetTop
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))), cosetOff S (⊤ : Ideal (𝓞 F)) (0 : ι → F) = {x : ι → F | ∀ v, v ∉ S → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} := by
  intro F _ _ ι S
  ext x
  simp only [cosetOff, Set.mem_setOf_eq, Pi.zero_apply, sub_zero, locMem_top_iff, algebraMap_mem_iff]
end GlobalTheory.CompanionTheory.Equi.CosetTop
