-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegLoc.Scaled.mul_mem_lev_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:38:50.6378+00:00
-- url     : https://prove2.me/submissions/9ec675b4-7de6-420f-83c0-c403a2276788

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SumCompSurj
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardRangeMulQuotientBoundedLevel
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc GlobalTheory.CompanionTheory.SiegLoc.Scaled
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.SiegLoc.Scaled
theorem _root_.solution {ϖ c : R} (hreg : IsSMulRegular R ϖ) (hc : IsUnit c) (e a₀ : ℕ) (y : R) :
    ϖ ^ a₀ * c * y ∈ lev ϖ (e + a₀) ↔ y ∈ lev ϖ e := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := mem_lev_iff.1 h
    have h1 : c * y = ϖ ^ e * t := by
      apply hreg.pow a₀
      simp only [smul_eq_mul]
      rw [← mul_assoc, ht, pow_add]
      ring
    obtain ⟨v, hv⟩ := hc.exists_left_inv
    refine mem_lev_iff.2 ⟨v * t, ?_⟩
    calc y = v * (c * y) := by rw [← mul_assoc, hv, one_mul]
      _ = ϖ ^ e * (v * t) := by rw [h1]; ring
  · intro h
    obtain ⟨t, rfl⟩ := mem_lev_iff.1 h
    exact mem_lev_iff.2 ⟨c * t, by rw [pow_add]; ring⟩
end GlobalTheory.CompanionTheory.SiegLoc.Scaled
