-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Equi.CosetStep.coset_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:03:23.045836+00:00
-- url     : https://prove2.me/submissions/59375647-d766-486c-9943-c355d1b05681

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetCongruenceRefinement
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_locMem_add
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_locMem_sub
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_locMem_mul_pow_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_mem_ballV_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_ballV_add
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_ballV_sub
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_locMem_v_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_exists_approx

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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)), v ∉ S → ∀ (I : Ideal (𝓞 F)), I ≠ ⊥ → ¬ I ≤ v.asIdeal → ∀ (k : ℕ) (x0 : ι → F) (c : ι → Fv F v), ∃ x1 : ι → F, ∀ x : ι → F, (x ∈ cosetOff (insert v S) I x0 ∧ ∀ i, algebraMap F (Fv F v) (x i) - c i ∈ ballV v k) ↔ x ∈ cosetOff S (I * v.asIdeal ^ k) x1 := by
  intro F _ _ ι S v hvS I hI hIv k x0 c
  choose x1 hx1w hx1v using fun i => exists_approx hI v k (x0 i) (c i)
  refine ⟨x1, fun x => ?_⟩
  simp only [cosetOff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hball⟩ w hwS i
    by_cases hwv : w = v
    · subst hwv
      rw [locMem_v_iff hIv, ← mem_ballV_iff, map_sub]
      have h3 := ballV_sub (hball i) (hx1v i)
      convert h3 using 1
      abel
    · have h1 : LocMem I w (x i - x0 i) := hx w (by simp [hwv, hwS]) i
      have h2 := locMem_sub h1 (hx1w i w hwv)
      rw [locMem_mul_pow_iff hwv]
      convert h2 using 1
      ring
  · intro hx
    refine ⟨fun w hw i => ?_, fun i => ?_⟩
    · have hwv : w ≠ v := fun h => hw (by simp [h])
      have hwS : w ∉ S := fun h => hw (by simp [h])
      have h1 := (locMem_mul_pow_iff hwv k).mp (hx w hwS i)
      have h2 := locMem_add h1 (hx1w i w hwv)
      convert h2 using 1
      ring
    · have h1 := (locMem_v_iff hIv k (x i - x1 i)).mp (hx v hvS i)
      rw [← mem_ballV_iff, map_sub] at h1
      have h3 := ballV_add h1 (hx1v i)
      convert h3 using 1
      abel
end GlobalTheory.CompanionTheory.Equi.CosetStep
