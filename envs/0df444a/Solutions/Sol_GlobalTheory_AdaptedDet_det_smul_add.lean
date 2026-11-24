-- Prove2me | solution 1 for GlobalTheory.AdaptedDet.det_smul_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:54:13.915129+00:00
-- url     : https://prove2.me/submissions/38dc4924-0f2e-4184-93b8-4c19896363d7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralDetSubOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmUnitPowFourIdempotentModEight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AdaptedDet
namespace GlobalTheory.AdaptedDet
theorem _root_.solution {K : Type} [Field K] [IsAlgClosed K] {r : ℕ} (A : Matrix (Fin r) (Fin r) K)
    (c a : K) (hc : c ≠ 0) :
    (c • A + a • (1 : Matrix (Fin r) (Fin r) K)).det =
      (A.charpoly.roots.map fun μ => c * μ + a).prod := by
  have h1 : c • A + a • (1 : Matrix (Fin r) (Fin r) K) =
      (-c) • (Matrix.scalar (Fin r) (-a / c) - A) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp
      field_simp
      ring
    · simp [h]
  have hs : A.charpoly.Splits := IsAlgClosed.splits _
  have hcard : A.charpoly.roots.card = r := by
    rw [← hs.natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  rw [h1, Matrix.det_smul, ← Matrix.eval_charpoly, hs.eval_eq_prod_roots_of_monic A.charpoly_monic,
    Fintype.card_fin]
  have h2 : (fun μ => c * μ + a) = fun μ => (-c) * (-a / c - μ) := by
    funext μ
    field_simp
    ring
  rw [h2, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard]
end GlobalTheory.AdaptedDet
