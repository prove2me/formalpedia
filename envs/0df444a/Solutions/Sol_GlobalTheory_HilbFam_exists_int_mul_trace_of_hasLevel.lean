-- Prove2me | solution 1 for GlobalTheory.HilbFam.exists_int_mul_trace_of_hasLevel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:30:49.420616+00:00
-- url     : https://prove2.me/submissions/4184a856-5ba6-46c3-bdd6-a1b8663fdba1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitLatticeLevelTraceDenominator
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_latM_eq_dual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam
namespace GlobalTheory.HilbFam
theorem _root_.solution {F : Type} [Field F] [NumberField F] {N : ℕ} {𝔞 𝔟 : Frac F} {x : F}
    (h : HasLevel N (split 𝔞 𝔟 x)) {ν c : F} (hν : ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F))
    (hc : c ∈ (1 : Submodule (𝓞 F) F)) : ∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F (ν * c) = n := by
  have h1 : (![0, c] : Fin 2 → F) ∈ stdLat F := by
    intro i _
    fin_cases i
    · exact Submodule.zero_mem _
    · exact hc
  have h2 := (h.1 _ h1).2
  have h3 : ((N : 𝓞 F) • (![0, c] : Fin 2 → F)) 1 - ((N : 𝓞 F) • (![0, c] : Fin 2 → F)) 0 * x = (N : F) * c := by
    simp [Algebra.smul_def]
  rw [h3, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual, FractionalIdeal.mem_dual 𝔞.ne_zero] at h2
  obtain ⟨n, hn⟩ := h2 ν hν
  refine ⟨n, ?_⟩
  have h4 : (N : F) * c * ν = (N : ℚ) • (ν * c) := by
    rw [Algebra.smul_def, map_natCast]; ring
  rw [Algebra.traceForm_apply, h4, map_smul, smul_eq_mul] at hn
  simpa using hn.symm
end GlobalTheory.HilbFam
