-- Prove2me | solution 1 for N25.canonicalOpenChartRing_isDomain_good25
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:47.719144+00:00
-- url     : https://prove2.me/submissions/8a1f59ac-2158-40e1-91d0-1af119e78e99

import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField
import Definitions.Def_N25_CanonicalOpenChart
import Definitions.Def_N25_UnitPlaneAlgebraOverRing
import Definitions.Def_N25_BirationalIdentities
import Definitions.Def_N25_CanonicalOpenAlgebraOverRing
import Theorems.Thm_N25_canonicalOpenChartRing25C_isDomain

/-! The literal canonical principal open is a domain, through its birational equivalence with the plane principal open. -/
noncomputable section

namespace N25

open Polynomial

variable {K : Type*} [Field K]

/-- The signed good-prime canonical principal open is a domain. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type*) [Field K] [CharP K p] :
    IsDomain (CanonicalOpenChartRing25 K) := by
  cases hp <;> exact canonicalOpenChartRing25C_isDomain

end N25
