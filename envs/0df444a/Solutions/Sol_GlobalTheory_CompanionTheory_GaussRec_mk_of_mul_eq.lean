-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GaussRec.mk_of_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:36:01.58153+00:00
-- url     : https://prove2.me/submissions/54dbc247-0c68-4b31-ae54-f7a8b802d478

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussSumHermitianNormLevelShift
import Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_mk_lft
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
theorem _root_.solution {ϖ : R} (hreg : IsSMulRegular R ϖ) (j : ℕ) {x y : R}
    (h : Ideal.Quotient.mk (lev ϖ (j + 2)) (ϖ * x) = Ideal.Quotient.mk (lev ϖ (j + 2)) (ϖ * y)) :
    Ideal.Quotient.mk (lev ϖ (j + 1)) x = Ideal.Quotient.mk (lev ϖ (j + 1)) y := by
  rw [Ideal.Quotient.eq] at h ⊢
  obtain ⟨c, hc⟩ := mem_lev_iff.1 h
  refine mem_lev_iff.2 ⟨c, hreg ?_⟩
  simp only [smul_eq_mul]
  rw [mul_sub, hc]
  ring
end GlobalTheory.CompanionTheory.GaussRec
