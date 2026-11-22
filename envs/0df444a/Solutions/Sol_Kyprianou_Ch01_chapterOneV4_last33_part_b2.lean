-- Prove2me | solution 1 for Kyprianou.Ch01.chapterOneV4_last33_part_b2
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-11-21T15:29:07.32529+00:00
-- url     : https://prove2.me/submissions/8ac978ae-a2bf-4f66-9eed-af4980279b78

import Definitions.Def_Kyprianou_Ch01_All67CertificatesZeroBoundaryV4
import Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorGeneratorFromRates
import Theorems.Thm_Kyprianou_Ch01_levyTripletExponentSignBridgeTargetedV2
import Theorems.Thm_Kyprianou_Ch01_continuousRepresentativeForAlmostSurePaths
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_isInfinitelyDivisible_marginal
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_charFun_eq_exp_mul
import Theorems.Thm_ProbabilityTheory_IsPoissonProcess_isLevyProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01
set_option autoImplicit false
universe u v

theorem solution :
    Kyprianou.Ch01.certificate_branchingOneAncestorGeneratorFromRates ∧
    Kyprianou.Ch01.certificate_levyTripletExponentSignBridgeReviewed ∧
    Kyprianou.Ch01.certificate_continuousRepresentativeForAlmostSurePaths.{u} ∧
    Kyprianou.Ch01.certificate_reuse_ProbabilityTheory_IsLevyProcess_isInfinitelyDivisible_marginal.{u, v} ∧
    Kyprianou.Ch01.certificate_reuse_ProbabilityTheory_IsLevyProcess_charFun_eq_exp_mul.{u, v} ∧
    Kyprianou.Ch01.certificate_reuse_ProbabilityTheory_IsPoissonProcess_isLevyProcess.{u} := by
  exact ⟨@branchingOneAncestorGeneratorFromRates,
    @levyTripletExponentSignBridgeTargetedV2,
    @continuousRepresentativeForAlmostSurePaths,
    @ProbabilityTheory.IsLevyProcess.isInfinitelyDivisible_marginal,
    @ProbabilityTheory.IsLevyProcess.charFun_eq_exp_mul,
    @ProbabilityTheory.IsPoissonProcess.isLevyProcess⟩
