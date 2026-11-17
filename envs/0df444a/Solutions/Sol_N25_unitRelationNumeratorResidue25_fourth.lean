-- Prove2me | solution 1 for N25.unitRelationNumeratorResidue25_fourth
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:07.319204+00:00
-- url     : https://prove2.me/submissions/96ce20b2-c26a-4139-8e85-e8257b1c1d73

import Definitions.Def_N25_UnitRelationCertificate

namespace N25

/-- The finite numerator evaluation vanishes modulo the fourth base power. -/
theorem _root_.solution :
    unitRelationNumeratorResidue25 (unitRelationCertificateBase25 3) 4951 = 0 := by
  decide +kernel

end N25
