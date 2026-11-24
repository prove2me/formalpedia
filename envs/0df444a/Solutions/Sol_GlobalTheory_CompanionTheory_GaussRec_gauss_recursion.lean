-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GaussRec.gauss_recursion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:00:41.838841+00:00
-- url     : https://prove2.me/submissions/11c81e3f-fe1e-4437-a82b-58e894de5c6a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussSumHermitianNormLevelShift
import Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_sum_comp_surj
import Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_mk_lft
import Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_sum_stationary
import Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_sum_filter_eq
import Theorems.Thm_GlobalTheory_T_unramified_quotient_card

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
open GlobalTheory.CompanionTheory.GaussRec
namespace GlobalTheory.CompanionTheory.GaussRec
theorem _root_.solution : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ) (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ), IsLevelChars σ ϖ ψ → ∀ (j : ℕ) (a : R), σ a = a → a ∉ lev ϖ 1 → (∑ w : R ⧸ lev ϖ (j + 2), ψ (j + 2) (Ideal.Quotient.mk (lev ϖ (j + 2)) a * (barσ σ ϖ hR.fix_ϖ (j + 2) w * w))) = (q : ℂ) ^ 2 * ∑ w : R ⧸ lev ϖ j, ψ j (Ideal.Quotient.mk (lev ϖ j) a * (barσ σ ϖ hR.fix_ϖ j w * w)) := by
  intro R _ σ ϖ q ε hR _ ψ hψ j a ha ha1
  classical
  have hle : lev ϖ (j + 1) ≤ lev ϖ j :=
    Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ (Nat.le_succ j))
  have h1 := sum_stationary hR hψ j ha
  rw [sum_filter_eq hR hψ j ha ha1] at h1
  have hc : Fintype.card (R ⧸ lev ϖ (j + 1)) = q ^ 2 * Fintype.card (R ⧸ lev ϖ j) := by
    have e1 := GlobalTheory.T.unramified_quotient_card R σ ϖ q ε hR (j + 1)
    have e2 := GlobalTheory.T.unramified_quotient_card R σ ϖ q ε hR j
    rw [Nat.card_eq_fintype_card] at e1 e2
    rw [e1, e2, ← pow_add]
    congr 1
    ring
  have h2 := sum_comp_surj (Ideal.Quotient.factor hle).toAddMonoidHom
    (Ideal.Quotient.factor_surjective hle) (q ^ 2) hc (gaussTerm σ ϖ hR.fix_ϖ ψ a j)
  have h3 : (∑ w, gaussTerm σ ϖ hR.fix_ϖ ψ a (j + 2) w) = ((q ^ 2 : ℕ) : ℂ) * ∑ w, gaussTerm σ ϖ hR.fix_ϖ ψ a j w :=
    h1.trans h2
  simpa [gaussTerm] using h3
end GlobalTheory.CompanionTheory.GaussRec
