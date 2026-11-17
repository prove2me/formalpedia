-- Prove2me | solution 1 for N25.unitRelationNumeratorResidue25_second
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:07.965975+00:00
-- url     : https://prove2.me/submissions/21c86d24-f84e-4e8e-a8ab-8885de83c7b0

import Definitions.Def_N25_UnitRelationCertificate

namespace N25

/-- The finite numerator evaluation vanishes modulo the second base power. -/
theorem _root_.solution :
    unitRelationNumeratorResidue25 (unitRelationCertificateBase25 1) 4951 = 0 := by
  decide +kernel

end N25
