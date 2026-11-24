-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GaussRec.sum_traceChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:16:57.178484+00:00
-- url     : https://prove2.me/submissions/efa280d7-b3ac-4a2e-8833-5bbc57523835

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussSumHermitianNormLevelShift
import Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_traceChar_mk
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_trace_nondeg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GaussRec
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.GaussRec
theorem _root_.solution {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε)
    [Fintype (R ⧸ lev ϖ 1)] {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ) (c : R)
    [Decidable (c ∈ lev ϖ 1)] :
    ∑ t, traceChar σ ϖ hR.fix_ϖ ψ c t
      = if c ∈ lev ϖ 1 then (Fintype.card (R ⧸ lev ϖ 1) : ℂ) else 0 := by
  split_ifs with hc
  · have h1 : ∀ t, traceChar σ ϖ hR.fix_ϖ ψ c t = 1 := by
      intro t
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective t
      rw [traceChar_mk]
      have : Ideal.Quotient.mk (lev ϖ 1) (c * y + σ (c * y)) = 0 := by
        have h0 : Ideal.Quotient.mk (lev ϖ 1) c = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hc
        rw [map_add, ← barσ_mk σ ϖ hR.fix_ϖ, map_mul, h0]
        simp
      rw [this, AddChar.map_zero_eq_one]
    simp [h1]
  · have hne : traceChar σ ϖ hR.fix_ϖ ψ c ≠ 1 := by
      intro h0
      apply hc
      refine trace_nondeg hR hψ 1 c (fun t => ?_)
      have h1 := traceChar_mk σ ϖ hR.fix_ϖ ψ c t
      rw [h0, AddChar.one_apply] at h1
      rw [mul_comm t c]
      exact h1.symm
    exact AddChar.sum_eq_zero_of_ne_one hne
end GlobalTheory.CompanionTheory.GaussRec
