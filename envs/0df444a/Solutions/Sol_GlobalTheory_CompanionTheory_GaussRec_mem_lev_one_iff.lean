-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GaussRec.mem_lev_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:35:59.589565+00:00
-- url     : https://prove2.me/submissions/83e20961-771b-44d5-b14f-c9547d4a58bb

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussSumHermitianNormLevelShift
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_mem_lev_iff


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
theorem _root_.solution {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε) {a : R}
    (ha : σ a = a) (ha1 : a ∉ lev ϖ 1) (x : R) : a * σ x ∈ lev ϖ 1 ↔ x ∈ lev ϖ 1 := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := (hR.fixLocal a ha ha1).exists_left_inv
    have h1 : σ x ∈ lev ϖ 1 := by
      have : σ x = v * (a * σ x) := by rw [← mul_assoc, hv, one_mul]
      rw [this]
      exact Ideal.mul_mem_left _ _ h
    obtain ⟨c, hc⟩ := mem_lev_iff.1 h1
    refine mem_lev_iff.2 ⟨σ c, ?_⟩
    have := congrArg σ hc
    simpa [hR.inv, hR.fix_ϖ] using this
  · intro h
    obtain ⟨c, rfl⟩ := mem_lev_iff.1 h
    refine mem_lev_iff.2 ⟨a * σ c, ?_⟩
    simp only [map_mul, map_pow, hR.fix_ϖ]
    ring
end GlobalTheory.CompanionTheory.GaussRec
