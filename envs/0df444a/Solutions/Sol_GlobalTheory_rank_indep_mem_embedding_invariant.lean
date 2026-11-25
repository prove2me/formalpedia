-- Prove2me | solution 1 for GlobalTheory.rank_indep_mem_embedding_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:56:09.07696+00:00
-- url     : https://prove2.me/submissions/8c598b47-448e-4016-8d9c-0c0f11c03ca3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LinearIndependentRingHomCompIff
import Theorems.Thm_GlobalTheory_linearIndependent_ringHom_comp_iff
import Theorems.Thm_GlobalTheory_finrank_span_ringHom_comp_eq
import Theorems.Thm_GlobalTheory_mem_span_iff_finrank_option_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (A F F' : Type) [CommRing A] [Field F] [Field F'] (φ : A →+* F) (ψ : A →+* F'), Function.Injective φ → Function.Injective ψ → ∀ (ι μ : Type) [Fintype ι] [Fintype μ] (c : ι → μ → A), (LinearIndependent F (fun i m => φ (c i m)) ↔ LinearIndependent F' (fun i m => ψ (c i m))) ∧ (∀ q : μ → A, (fun m => φ (q m)) ∈ Submodule.span F (Set.range fun i m => φ (c i m)) ↔ (fun m => ψ (q m)) ∈ Submodule.span F' (Set.range fun i m => ψ (c i m))) ∧ Module.finrank F (Submodule.span F (Set.range fun i m => φ (c i m))) = Module.finrank F' (Submodule.span F' (Set.range fun i m => ψ (c i m))) := by
  intro A F F' _ _ _ φ ψ hφ hψ ι μ _ _ c
  refine ⟨?_, fun q => ?_, finrank_span_ringHom_comp_eq φ ψ hφ hψ c⟩
  · rw [linearIndependent_ringHom_comp_iff φ hφ, linearIndependent_ringHom_comp_iff ψ hψ]
  · let d : Option ι → μ → A := fun o => o.elim q c
    have h1 := mem_span_iff_finrank_option_eq (F := F) (fun o m => φ (d o m))
    have h2 := mem_span_iff_finrank_option_eq (F := F') (fun o m => ψ (d o m))
    have e1 := finrank_span_ringHom_comp_eq φ ψ hφ hψ c
    have e2 := finrank_span_ringHom_comp_eq φ ψ hφ hψ d
    refine h1.trans (Iff.trans ?_ h2.symm)
    rw [e2]
    exact e1 ▸ Iff.rfl
end GlobalTheory
