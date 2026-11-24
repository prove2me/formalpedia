-- Prove2me | solution 1 for GlobalTheory.DI.PhiLead.alt_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:26:32.540545+00:00
-- url     : https://prove2.me/submissions/da9ac33f-fc6c-48f9-9d4d-013a18f02d9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechAntisymmetrizedCupProductLeadingTerm
import Theorems.Thm_GlobalTheory_DI_PhiLead_prodL_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI GlobalTheory.DI.PhiLead
variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι]
namespace GlobalTheory.DI.PhiLead
theorem _root_.solution (f : ι → V →+ V) (h : ι → ι → V →+ K) (a : ℕ) (v : Fin a → V) (j : ι) :
    alt f h a v {j} = ((-1 : ℤ) ^ a * (a.factorial : ℤ)) • ExteriorAlgebra.ιMulti K a (fun k => f j (v k)) := by
  have key : ∀ σ : Equiv.Perm (Fin a), prodL f h (List.ofFn (v ∘ σ)) {j} =
      ((-1 : ℤ) ^ a * ((Equiv.Perm.sign σ : ℤˣ) : ℤ)) • ExteriorAlgebra.ιMulti K a (fun k => f j (v k)) := by
    intro σ
    rw [prodL_single, List.length_ofFn, List.map_ofFn]
    have h1 : (List.ofFn ((fun v => ExteriorAlgebra.ι K (f j v)) ∘ v ∘ σ)).prod =
        ExteriorAlgebra.ιMulti K a ((fun k => f j (v k)) ∘ σ) := by
      rw [ExteriorAlgebra.ιMulti_apply]; rfl
    rw [h1, AlternatingMap.map_perm, mul_smul]
    simp [Units.smul_def]
  simp only [alt, Finset.sum_apply, Pi.smul_apply, key, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  have hs : ∀ σ : Equiv.Perm (Fin a), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) * ((-1 : ℤ) ^ a * ((Equiv.Perm.sign σ : ℤˣ) : ℤ)) = (-1 : ℤ) ^ a := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ <;> simp [hσ]
  simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  push_cast; ring
end GlobalTheory.DI.PhiLead
