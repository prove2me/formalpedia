-- Prove2me | solution 1 for N25.unitRelationNumeratorResidue25_first
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:06.614617+00:00
-- url     : https://prove2.me/submissions/67405cf7-cd23-44a1-b3d6-6cd8bfb560d5

import Definitions.Def_N25_UnitRelationCertificate

namespace N25

/-- The finite numerator evaluation vanishes modulo the first base power. -/
theorem _root_.solution :
    unitRelationNumeratorResidue25 (unitRelationCertificateBase25 0) 4951 = 0 := by
  decide +kernel

end N25
