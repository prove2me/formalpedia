-- Prove2me | solution 1 for GlobalTheory.CuspCharCheck.isCuspChar_of_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:22:08.406328+00:00
-- url     : https://prove2.me/submissions/bd14f582-444c-44cf-a96e-fb65be8e1fd3

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CuspEllipticValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralIdempotentIrreducibleCharacterProps
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_SubgroupCharacterSums_SumSubgroupEqZeroIff
import Theorems.Thm_GlobalTheory_CuspCharCheck_isIrrChar_of_hom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CuspElliptic
open GlobalTheory GlobalTheory.CuspCharCheck
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
namespace GlobalTheory.CuspCharCheck
theorem _root_.solution {d : ℕ} (c : GL (Fin d) F →* ℂˣ)
    (hc : ∀ a, 0 < a → a < d → ∃ t ∈ (unipBlock d a : Set (GL (Fin d) F)), (c t : ℂ) ≠ 1) :
    IsCuspChar (fun x => (c x : ℂ)) := by
  classical
  refine ⟨isIrrChar_of_hom _, fun a h0 h1 => ?_⟩
  obtain ⟨t, ht, hs⟩ := hc a h0 h1
  let U : Subgroup (GL (Fin d) F) := unipSubgroup d a
  let f : U →* ℂ := ((Units.coeHom ℂ).comp c).comp U.subtype
  have h := sum_hom_units_eq_zero f (fun h => hs (by
    have h2 := DFunLike.congr_fun h (⟨t, ht⟩ : U)
    exact h2))
  rw [← Finset.sum_filter]
  refine Eq.trans ?_ h
  exact Finset.sum_subtype (p := (· ∈ U)) _ (fun x => by rw [Finset.mem_filter]; exact and_iff_right (Finset.mem_univ _))
    (fun g => ((c g : ℂˣ) : ℂ))
end GlobalTheory.CuspCharCheck
