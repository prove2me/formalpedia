-- Prove2me | solution 1 for GlobalTheory.ValConjClosure.exists_conj_over_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:35:34.351826+00:00
-- url     : https://prove2.me/submissions/631c032f-d640-45b1-ab7a-4210773e88c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ApplyEqOfMemAdjoin
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsTopWTopWOfExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsGaloisConjValuationSubringSameTrace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsConjOverPrime
import Theorems.Thm_GlobalTheory_ValConjClosure_ratCast_mem_iff
import Theorems.Thm_GlobalTheory_ValConjClosure_exists_conj_of_isGalois

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
open GlobalTheory GlobalTheory.ValConjClosure
namespace GlobalTheory.ValConjClosure
theorem _root_.solution : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (A B : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits → ((p : ℕ) : Ω) ∈ B.nonunits → ∃ σ : Ω ≃ₐ[ℚ] Ω, ∀ x, σ x ∈ B ↔ x ∈ A := by
  intro Ω _ _ _ p _ A B hA hB
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hp : p.Prime := Fact.out
  have hA' := (A.mem_nonunits_iff).mp hA
  have hB' := (B.mem_nonunits_iff).mp hB
  apply exists_conj_of_isGalois A B
  intro a
  rw [eq_ratCast, ratCast_mem_iff hp A hA', ratCast_mem_iff hp B hB']
end GlobalTheory.ValConjClosure
