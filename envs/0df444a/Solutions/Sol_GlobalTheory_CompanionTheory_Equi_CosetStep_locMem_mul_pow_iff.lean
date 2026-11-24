-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.CosetStep.locMem_mul_pow_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:26:28.688639+00:00
-- url     : https://prove2.me/submissions/3d1a63c1-ffa7-4537-bc3c-ec418443a98c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetCongruenceRefinement
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_exists_mem_pow_not_mem

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
theorem _root_.solution {I : Ideal (𝓞 F)} {v w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) (k : ℕ)
    {t : F} : LocMem (I * v.asIdeal ^ k) w t ↔ LocMem I w t := by
  constructor
  · rintro ⟨s, hs, y, hy, h⟩
    exact ⟨s, hs, y, (Ideal.mul_le_left : I * v.asIdeal ^ k ≤ I) hy, h⟩
  · rintro ⟨s, hs, y, hy, h⟩
    obtain ⟨e, he, hew⟩ := exists_mem_pow_not_mem hw k
    refine ⟨e * s, fun hm => (w.isPrime.mem_or_mem hm).elim hew hs, y * e, Ideal.mul_mem_mul hy he, ?_⟩
    push_cast
    rw [mul_assoc, h]
    ring
end GlobalTheory.CompanionTheory.Equi.CosetStep
