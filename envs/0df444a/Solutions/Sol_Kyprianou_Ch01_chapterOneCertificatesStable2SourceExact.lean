-- Prove2me | solution 1 for Kyprianou.Ch01.chapterOneCertificatesStable2SourceExact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T20:15:53.884084+00:00
-- url     : https://prove2.me/submissions/f498c3b8-356c-479d-8f2b-a71ea072bd5c

import Definitions.Def_Kyprianou_Ch01_All67CertificatesTargetedV3
import Theorems.Thm_Kyprianou_Ch01_stableLevyExponentFormAwayFromOneTargetedV2
import Theorems.Thm_Kyprianou_Ch01_stableLevyExponentFormIndexOneTargetedV2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option maxRecDepth 4000
open Kyprianou.Ch01
set_option autoImplicit false
universe u v

theorem solution :
    certificate_stableLevyExponentFormAwayFromOne ∧
    certificate_stableLevyExponentFormIndexOne := by
  exact ⟨
    @stableLevyExponentFormAwayFromOneTargetedV2,
    @stableLevyExponentFormIndexOneTargetedV2
  ⟩
