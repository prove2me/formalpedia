-- Prove2me | solution 1 for GlobalTheory.JR.OKCompact.coeff_charpoly_lmul_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:27:17.519681+00:00
-- url     : https://prove2.me/submissions/79e6daa3-56e0-419e-93bb-eb76e2a8917d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCompactFiniteEtaleHermitianPairOK
import Theorems.Thm_GlobalTheory_JR_OKCompact_charpoly_smul_eq_scaleRoots

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.OKCompact
variable {F : Type} [NontriviallyNormedField F] {K : Type} [CommRing K] [Algebra F K] [Module.Finite F K]
namespace GlobalTheory.JR.OKCompact
theorem _root_.solution [Infinite F] (z : K) {c : F} (hc : c ≠ 0) (k : ℕ) :
    (LinearMap.charpoly (Algebra.lmul F K (c • z))).coeff k =
      (LinearMap.charpoly (Algebra.lmul F K z)).coeff k * c ^ (Module.finrank F K - k) := by
  let b := Module.finBasis F K
  rw [← LinearMap.charpoly_toMatrix (Algebra.lmul F K (c • z)) b,
    ← LinearMap.charpoly_toMatrix (Algebra.lmul F K z) b, map_smul, map_smul,
    charpoly_smul_eq_scaleRoots _ hc, Polynomial.coeff_scaleRoots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
end GlobalTheory.JR.OKCompact
