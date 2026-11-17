-- Prove2me | solution 1 for Kyprianou.Ch01.chapterOneV4_last33_part_b
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:34:16.35498+00:00
-- url     : https://prove2.me/submissions/b67446f6-c34e-49d5-a0e4-86a6ce7fbfbc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch01_All67CertificatesZeroBoundaryV4
import Theorems.Thm_Kyprianou_Ch01_chapterOneV4_last33_part_b1
import Theorems.Thm_Kyprianou_Ch01_chapterOneV4_last33_part_b2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
universe u v

theorem solution :
    Kyprianou.Ch01.certificate_riskEmbeddedRandomWalkTails ∧
    Kyprianou.Ch01.certificate_exponentialAscendingLadderRenewal ∧
    Kyprianou.Ch01.certificate_brownianPassageHalfStableLevyProcessZeroBoundaryV2.{u} ∧
    Kyprianou.Ch01.certificate_stableLevyExponentFormAwayFromOne ∧
    Kyprianou.Ch01.certificate_stableLevyExponentFormIndexOne ∧
    Kyprianou.Ch01.certificate_branchingOneAncestorGeneratorFromRates ∧
    Kyprianou.Ch01.certificate_levyTripletExponentSignBridgeReviewed ∧
    Kyprianou.Ch01.certificate_continuousRepresentativeForAlmostSurePaths.{u} ∧
    Kyprianou.Ch01.certificate_reuse_ProbabilityTheory_IsLevyProcess_isInfinitelyDivisible_marginal.{u, v} ∧
    Kyprianou.Ch01.certificate_reuse_ProbabilityTheory_IsLevyProcess_charFun_eq_exp_mul.{u, v} ∧
    Kyprianou.Ch01.certificate_reuse_ProbabilityTheory_IsPoissonProcess_isLevyProcess.{u} := by
  have hb1 := @Kyprianou.Ch01.chapterOneV4_last33_part_b1
  have hb2 := @Kyprianou.Ch01.chapterOneV4_last33_part_b2
  simpa only [and_assoc] using And.intro hb1 hb2
