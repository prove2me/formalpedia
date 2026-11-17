-- Prove2me | solution 1 for N25.unitRelationNumeratorResidue25_third
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:08.790745+00:00
-- url     : https://prove2.me/submissions/ac485e57-b6bc-4e9d-b302-0aa3c16865cd

import Definitions.Def_N25_UnitRelationCertificate

namespace N25

/-- The finite numerator evaluation vanishes modulo the third base power. -/
theorem _root_.solution :
    unitRelationNumeratorResidue25 (unitRelationCertificateBase25 2) 4951 = 0 := by
  decide +kernel

end N25
