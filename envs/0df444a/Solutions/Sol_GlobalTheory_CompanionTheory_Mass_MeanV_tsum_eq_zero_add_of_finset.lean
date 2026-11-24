-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Mass.MeanV.tsum_eq_zero_add_of_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:23:24.337517+00:00
-- url     : https://prove2.me/submissions/58f69f3e-e0b3-4da9-b525-87a6f5cb6cf7

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TsumNeZeroEqSum
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TruncatedSumLimit
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_CompanionTheory_Mass_MeanV_tsum_ne_zero_eq_sum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Mass GlobalTheory.CompanionTheory.Mass.MeanV
namespace GlobalTheory.CompanionTheory.Mass.MeanV
theorem _root_.solution {F : Type} [Field F] (h : F → ℝ) (B : Finset F) (hB : ∀ x ∈ B, x ≠ 0)
    (hh : ∀ x, x ≠ 0 → x ∉ B → h x = 0) :
    ∑' x : F, h x = h 0 + ∑' β : {β : F // β ≠ 0}, h β.1 := by
  rw [tsum_ne_zero_eq_sum h B hB hh, tsum_eq_sum (s := insert 0 B) ?_, Finset.sum_insert (fun h0 => hB 0 h0 rfl)]
  intro x hx
  simp only [Finset.mem_insert, not_or] at hx
  exact hh x hx.1 hx.2
end GlobalTheory.CompanionTheory.Mass.MeanV
