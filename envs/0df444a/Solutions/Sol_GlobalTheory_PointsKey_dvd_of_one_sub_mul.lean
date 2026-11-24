-- Prove2me | solution 1 for GlobalTheory.PointsKey.dvd_of_one_sub_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:27:05.454984+00:00
-- url     : https://prove2.me/submissions/b363d43e-fb61-496b-8647-ea16c410b7cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FrobeniusPowEquationDvdAllPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowDvdOfVanishingAtPerfectValuationPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdAllPowOfFrobeniusEqKilledByPerfectPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory GlobalTheory.PointsKey
namespace GlobalTheory.PointsKey
theorem _root_.solution {R : Type} [CommRing R] (u r D a : R) (m : ℕ)
    (h : (1 - u * r) * D = u ^ m * a) : u ^ m ∣ D := by
  have hg : (1 - u * r) * (∑ i ∈ Finset.range m, (u * r) ^ i) = 1 - (u * r) ^ m := by
    rw [mul_comm, geom_sum_mul_neg]
  refine ⟨a * ∑ i ∈ Finset.range m, (u * r) ^ i + r ^ m * D, ?_⟩
  calc D = (1 - (u * r) ^ m) * D + (u * r) ^ m * D := by ring
    _ = (∑ i ∈ Finset.range m, (u * r) ^ i) * ((1 - u * r) * D) + (u * r) ^ m * D := by
        rw [← hg]; ring
    _ = _ := by rw [h]; ring
end GlobalTheory.PointsKey
