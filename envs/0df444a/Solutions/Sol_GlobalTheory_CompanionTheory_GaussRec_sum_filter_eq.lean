-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GaussRec.sum_filter_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:52:38.442975+00:00
-- url     : https://prove2.me/submissions/c57c0815-b7e9-423c-887e-f8928d6163fb

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussSumHermitianNormLevelShift
import Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_mem_lev_one_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_mk_lft
import Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_mk_mul_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_mk_of_mul_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_gaussTerm_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_mem_lev_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.GaussRec.mk_lft

set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GaussRec
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.GaussRec
theorem _root_.solution {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε)
    [∀ k, Fintype (R ⧸ lev ϖ k)] {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ)
    (j : ℕ) {a : R} (ha : σ a = a) (ha1 : a ∉ lev ϖ 1) [DecidablePred fun c => c ∈ lev ϖ 1] :
    (∑ w, if a * σ (lft ϖ (j + 2) w) ∈ lev ϖ 1 then gaussTerm σ ϖ hR.fix_ϖ ψ a (j + 2) w else 0)
      = ∑ w' : R ⧸ lev ϖ (j + 1), gaussTerm σ ϖ hR.fix_ϖ ψ a j
          (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ (Nat.le_succ j))) w') := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_nbij (fun w' => Ideal.Quotient.mk (lev ϖ (j + 2)) (ϖ * lft ϖ (j + 1) w'))
    ?_ ?_ ?_ ?_
  · intro w' _
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, (mem_lev_one_iff hR ha ha1 _).2 ?_⟩
    have h := mk_lft ϖ (j + 2) (Ideal.Quotient.mk (lev ϖ (j + 2)) (ϖ * lft ϖ (j + 1) w'))
    rw [Ideal.Quotient.eq] at h
    obtain ⟨c, hc⟩ := mem_lev_iff.1 h
    rw [sub_eq_iff_eq_add] at hc
    rw [hc]
    refine mem_lev_iff.2 ⟨ϖ ^ (j + 1) * c + lft ϖ (j + 1) w', ?_⟩
    ring
  · intro x _ y _ h
    have := mk_of_mul_eq hR.reg j h
    simpa using this
  · intro w hw
    have hw' := (mem_lev_one_iff hR ha ha1 _).1 (Finset.mem_filter.1 hw).2
    obtain ⟨c, hc⟩ := mem_lev_iff.1 hw'
    refine ⟨Ideal.Quotient.mk _ c, by simp, ?_⟩
    have h1 := mk_mul_eq ϖ j (mk_lft ϖ (j + 1) (Ideal.Quotient.mk _ c))
    simp only
    rw [h1, ← mk_lft ϖ (j + 2) w, hc, pow_one]
  · intro w' _
    conv_lhs => rw [← mk_lft ϖ (j + 1) w']
    rw [Ideal.Quotient.factor_mk, gaussTerm_mul hR.fix_ϖ hψ]
end GlobalTheory.CompanionTheory.GaussRec
