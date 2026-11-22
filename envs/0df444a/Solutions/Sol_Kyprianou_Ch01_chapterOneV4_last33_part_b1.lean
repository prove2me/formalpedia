-- Prove2me | solution 1 for Kyprianou.Ch01.chapterOneV4_last33_part_b1
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-11-21T15:29:07.954032+00:00
-- url     : https://prove2.me/submissions/69e43a9d-8dc9-406d-ad26-bb25ae79e7c4

import Definitions.Def_Kyprianou_Ch01_All67CertificatesZeroBoundaryV4
import Theorems.Thm_Kyprianou_Ch01_riskEmbeddedRandomWalkTails
import Theorems.Thm_Kyprianou_Ch01_exponentialAscendingLadderRenewal
import Theorems.Thm_Kyprianou_Ch01_brownianPassageHalfStableLevyProcessZeroBoundaryV2
import Theorems.Thm_Kyprianou_Ch01_stableLevyExponentFormAwayFromOneTargetedV2
import Theorems.Thm_Kyprianou_Ch01_stableLevyExponentFormIndexOneTargetedV2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01
set_option autoImplicit false
universe u v

theorem solution :
    Kyprianou.Ch01.certificate_riskEmbeddedRandomWalkTails ∧
    Kyprianou.Ch01.certificate_exponentialAscendingLadderRenewal ∧
    Kyprianou.Ch01.certificate_brownianPassageHalfStableLevyProcessZeroBoundaryV2.{u} ∧
    Kyprianou.Ch01.certificate_stableLevyExponentFormAwayFromOne ∧
    Kyprianou.Ch01.certificate_stableLevyExponentFormIndexOne := by
  exact ⟨@riskEmbeddedRandomWalkTails,
    @exponentialAscendingLadderRenewal,
    @brownianPassageHalfStableLevyProcessZeroBoundaryV2,
    @stableLevyExponentFormAwayFromOneTargetedV2,
    @stableLevyExponentFormIndexOneTargetedV2⟩
