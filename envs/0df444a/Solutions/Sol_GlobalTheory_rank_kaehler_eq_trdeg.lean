-- Prove2me | solution 1 for GlobalTheory.rank_kaehler_eq_trdeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:58:38.168843+00:00
-- url     : https://prove2.me/submissions/78504814-d31b-47a9-9e0e-98a4cba5beea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_P2M_GlobalTheory_formMap__Multi_014b852379ac
import Theorems.Thm_GlobalTheory_dlogWedge_empty
import Theorems.Thm_GlobalTheory_ordTop_vw_zero
import Theorems.Thm_GlobalTheory_fracKaehlerBasis_apply
import Theorems.Thm_GlobalTheory_topFormCoeff_topFormGen
import Theorems.Thm_GlobalTheory_exists_basis_kaehler_of_algebraicIndependent
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15


attribute [local simp] GlobalTheory.formMap_ιMulti
attribute [local simp] GlobalTheory.dlogWedge_empty
attribute [local simp] GlobalTheory.ordTop_vw_zero
attribute [local simp] GlobalTheory.fracKaehlerBasis_apply
attribute [local simp] GlobalTheory.topFormCoeff_topFormGen

set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
namespace GlobalTheory
theorem _root_.solution (K F : Type*) [Field K] [Field F] [Algebra K F] [PerfectField K]
    [Algebra.EssFiniteType K F] : Module.rank F Ω[F⁄K] = Algebra.trdeg K F := by
  obtain ⟨s, hs, H⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K F
  have : Algebra.IsSeparable (IntermediateField.adjoin K (Set.range ((↑) : s → F))) F := by
    convert! H <;> simp
  obtain ⟨b, -⟩ := exists_basis_kaehler_of_algebraicIndependent hs.1
  rw [← hs.cardinalMk_eq_trdeg, ← b.mk_eq_rank'']
end GlobalTheory
