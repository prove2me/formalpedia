-- Prove2me | solution 1 for N25.canonicalOpenChartRing25C_isDomain
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:47.129606+00:00
-- url     : https://prove2.me/submissions/938fb7f9-a385-4111-8f66-9549b3ead7bc

import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField
import Definitions.Def_N25_CanonicalOpenChart
import Definitions.Def_N25_UnitPlaneAlgebraOverRing
import Definitions.Def_N25_BirationalIdentities
import Definitions.Def_N25_CanonicalOpenAlgebraOverRing

/-! The literal canonical principal open is a domain, through its birational equivalence with the plane principal open. -/
noncomputable section

namespace N25

open Polynomial

variable {K : Type*} [Field K]

/-- The literal canonical principal open is a domain over every coefficient field. -/
theorem _root_.solution : IsDomain (CanonicalOpenChartRing25 K) := by
  letI := unitPlaneOpenRing25C_isDomain (K := K)
  exact MulEquiv.isDomain (UnitPlaneOpenRing25C K)
    (canonicalUnitPlaneOpenAlgEquiv25C K).toMulEquiv

end N25
