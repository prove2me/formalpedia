-- Prove2me | solution 1 for N25.canonicalConeFractionPiece25_injective
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:44.958682+00:00
-- url     : https://prove2.me/submissions/a0f88a4f-da6a-4584-bb29-a3f601c9dfc6

import Definitions.Def_N25_CanonicalProjectiveCharts
import Definitions.Def_N25_CanonicalChartDehomogenization
import Definitions.Def_N25_CanonicalProjectivePrincipalOpen
import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField
import Definitions.Def_N25_CanonicalOpenChart
import Definitions.Def_N25_UnitPlaneAlgebraOverRing
import Definitions.Def_N25_BirationalIdentities
import Definitions.Def_N25_CanonicalOpenAlgebraOverRing
import Definitions.Def_N25_CanonicalPrincipalOpenChart
import Definitions.Def_N25_CanonicalConePolynomial
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

/-! A graded polynomial representation of the canonical cone, normalized by A. -/

noncomputable section

universe u

namespace N25

open HomogeneousLocalization DirectSum

variable (K : Type u) [Field K]

/-- Regularity of A prevents any homogeneous coefficient from disappearing on the A-chart. -/
theorem _root_.solution (ha : IsRegular (canonicalConeA25 K)) (n : ℕ) :
    Function.Injective (canonicalConeFractionPiece25 K n) := by
  have hi : Function.Injective (algebraMap (CanonicalConeRing25 K) (Localization.Away (canonicalConeA25 K))) := by
    apply IsLocalization.injective (M := Submonoid.powers (canonicalConeA25 K))
    rintro x ⟨m, rfl⟩
    exact (ha.pow m).mem_nonZeroDivisors
  intro x y hxy
  apply Subtype.ext
  apply hi
  have hh := congrArg HomogeneousLocalization.val hxy
  change Localization.mk x.val _ = Localization.mk y.val _ at hh
  simp only [Localization.mk_eq_mk'] at hh
  have hx := IsLocalization.mk'_spec (Localization.Away (canonicalConeA25 K)) x.val
    (⟨canonicalConeA25 K ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (canonicalConeA25 K))
  have hy := IsLocalization.mk'_spec (Localization.Away (canonicalConeA25 K)) y.val
    (⟨canonicalConeA25 K ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (canonicalConeA25 K))
  exact hx.symm.trans ((congrArg (fun z => z * algebraMap (CanonicalConeRing25 K)
    (Localization.Away (canonicalConeA25 K)) (canonicalConeA25 K ^ n)) hh).trans hy)

end N25
