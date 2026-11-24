-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GaussRec.sum_stationary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:38:29.99836+00:00
-- url     : https://prove2.me/submissions/fbf46c15-9c0c-4b58-8e52-2038b59863e9

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussSumHermitianNormLevelShift
import Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_sum_traceChar
import Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_gaussTerm_shift
import Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_mk_lft
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
    (j : ℕ) {a : R} (ha : σ a = a) [DecidablePred fun c => c ∈ lev ϖ 1] :
    ∑ w, gaussTerm σ ϖ hR.fix_ϖ ψ a (j + 2) w
      = ∑ w, if a * σ (lft ϖ (j + 2) w) ∈ lev ϖ 1 then gaussTerm σ ϖ hR.fix_ϖ ψ a (j + 2) w else 0 := by
  have shift : ∀ t : R ⧸ lev ϖ 1, ∑ w, gaussTerm σ ϖ hR.fix_ϖ ψ a (j + 2) w
      = ∑ w, gaussTerm σ ϖ hR.fix_ϖ ψ a (j + 2) w
          * traceChar σ ϖ hR.fix_ϖ ψ (a * σ (lft ϖ (j + 2) w)) t := by
    intro t
    rw [← Equiv.sum_comp (Equiv.addRight (Ideal.Quotient.mk (lev ϖ (j + 2)) (ϖ ^ (j + 1) * lft ϖ 1 t)))]
    refine Finset.sum_congr rfl fun w _ => ?_
    have h := gaussTerm_shift hR.inv hR.fix_ϖ hψ j ha (lft ϖ (j + 2) w) (lft ϖ 1 t)
    rw [mk_lft, mk_lft] at h
    exact h
  have hcard : (Fintype.card (R ⧸ lev ϖ 1) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  apply mul_left_cancel₀ hcard
  calc (Fintype.card (R ⧸ lev ϖ 1) : ℂ) * ∑ w, gaussTerm σ ϖ hR.fix_ϖ ψ a (j + 2) w
      = ∑ t : R ⧸ lev ϖ 1, ∑ w, gaussTerm σ ϖ hR.fix_ϖ ψ a (j + 2) w := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ∑ t : R ⧸ lev ϖ 1, ∑ w, gaussTerm σ ϖ hR.fix_ϖ ψ a (j + 2) w
          * traceChar σ ϖ hR.fix_ϖ ψ (a * σ (lft ϖ (j + 2) w)) t :=
        Finset.sum_congr rfl fun t _ => shift t
    _ = ∑ w, gaussTerm σ ϖ hR.fix_ϖ ψ a (j + 2) w
          * ∑ t, traceChar σ ϖ hR.fix_ϖ ψ (a * σ (lft ϖ (j + 2) w)) t := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun w _ => (Finset.mul_sum _ _ _).symm
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [sum_traceChar hR hψ]
        split_ifs <;> ring
end GlobalTheory.CompanionTheory.GaussRec
