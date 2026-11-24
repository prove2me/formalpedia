-- Prove2me | solution 1 for GlobalTheory.FixedRoots.mem_of_forall_ringEquiv_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:41:18.614981+00:00
-- url     : https://prove2.me/submissions/ecff2b6e-1ef9-463a-8873-4262e8aca42c

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FixedByAutomorphismInField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsRingEquivAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemOfForallRingEquivFixed
import Theorems.Thm_GlobalTheory_FixedRoots_exists_ringEquiv_add_one
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_exists_algEquiv_extending
import Theorems.Thm_GlobalTheory_ShiftVariables_exists_ringEquiv_add_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.FixedRoots
namespace GlobalTheory.FixedRoots
theorem _root_.solution {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    (k : Subfield Ω) (c : Ω) (hfix : ∀ σ : Ω ≃+* Ω, (∀ a ∈ k, σ a = a) → σ c = c) : c ∈ k := by
  by_cases hc : Transcendental k c
  · exfalso
    obtain ⟨σ, hσk, hσc⟩ := exists_ringEquiv_add_one k c hc
    have := hfix σ hσk
    rw [hσc] at this
    simp at this
  · have hcA : IsAlgebraic k c := by simpa [Transcendental] using hc
    have hzA : c ∈ algebraicClosure k Ω := (mem_algebraicClosure_iff).2 hcA
    have : IsGalois k (algebraicClosure k Ω) := inferInstance
    obtain ⟨r, hr⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed
      (k := k) (K := algebraicClosure k Ω) ⟨c, hzA⟩).2 (by
        intro σ₀
        obtain ⟨σ, hσ⟩ := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.exists_algEquiv_extending σ₀
        apply Subtype.ext
        rw [← hσ]
        exact hfix σ.toRingEquiv (fun a ha => σ.commutes ⟨a, ha⟩))
    have : ((r : k) : Ω) = c := congrArg Subtype.val hr
    rw [← this]
    exact r.2
end GlobalTheory.FixedRoots
